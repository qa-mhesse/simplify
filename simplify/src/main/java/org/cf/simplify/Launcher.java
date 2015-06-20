package org.cf.simplify;

import ch.qos.logback.classic.Level;
import org.apache.commons.io.FileUtils;
import org.cf.smalivm.ClassManager;
import org.cf.smalivm.VirtualMachine;
import org.cf.smalivm.context.ExecutionGraph;
import org.cf.smalivm.exception.MaxAddressVisitsExceeded;
import org.cf.smalivm.exception.MaxCallDepthExceeded;
import org.cf.smalivm.exception.MaxMethodVisitsExceeded;
import org.cf.smalivm.exception.UnhandledVirtualException;
import org.jf.dexlib2.writer.builder.BuilderMethod;
import org.jf.dexlib2.writer.builder.DexBuilder;
import org.jf.dexlib2.writer.io.FileDataStore;
import org.kohsuke.args4j.CmdLineException;
import org.kohsuke.args4j.CmdLineParser;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.nio.file.*;
import java.util.*;
import java.util.regex.Pattern;

public class Launcher {

    private static final Logger log = LoggerFactory.getLogger(Main.class.getSimpleName());

    private static final Pattern SUPPORT_LIBRARY_PATTERN = Pattern.compile("Landroid/support/(annotation|v\\d{1,2})/");

    private static Options getOptions(String[] args) {
        Options opts = new Options();
        CmdLineParser parser = new CmdLineParser(opts);
        try {
            parser.parseArgument(args);
        } catch (CmdLineException e) {
            System.err.println(e);
            parser.printUsage(System.out);
            System.exit(0);
        }
        if (opts.isHelp()) {
            parser.printUsage(System.out);
            System.exit(0);
        }

        return opts;
    }

    private static ClassManager getClassManager(File inFile, boolean disassemble, DexBuilder dexBuilder)
            throws IOException {
        ClassManager classManager;
        if (disassemble) {
            String outPath = disassemble(inFile);
            classManager = new ClassManager(outPath, dexBuilder);
        } else {
            classManager = new ClassManager(inFile, dexBuilder);
        }

        return classManager;
    }

    private static String disassemble(File file) throws IOException {
        // No, no, I'll do it since you're too lazy to do this yourself.
        // All these options are just for funsies. Could help with debugging.
        Path tempDir = Files.createTempDirectory("simplify");
        String[] args = new String[]{
                "--use-locals", "--sequential-labels", "--code-offsets", file.getAbsolutePath(), "--output",
                tempDir.toString(),};
        org.jf.baksmali.main.main(args);

        return tempDir.toString();
    }

    private static void updateZip(File zip, File entry, String entryName) throws IOException {
        Map<String, String> env = new HashMap<>();
        String uriPath = "jar:file:" + zip.getAbsolutePath();
        URI uri = URI.create(uriPath);
        try (FileSystem fs = FileSystems.newFileSystem(uri, env)) {
            fs.provider().checkAccess(fs.getPath(entryName), AccessMode.READ);
            Path target = fs.getPath(entryName);
            Path source = entry.toPath();
            Files.copy(source, target, StandardCopyOption.REPLACE_EXISTING);
        }
    }

    private static void filterMethods(Collection<String> methodDescriptors, Pattern positive, Pattern negative) {
        for (Iterator<String> it = methodDescriptors.iterator(); it.hasNext(); ) {
            String name = it.next();
            if ((positive != null) && !positive.matcher(name).find()) {
                it.remove();
            }

            if ((negative != null) && negative.matcher(name).find()) {
                it.remove();
            }
        }
    }

    private static void filterSupportLibrary(Collection<String> methodDescriptors) {
        for (Iterator<String> it = methodDescriptors.iterator(); it.hasNext(); ) {
            String name = it.next();
            if (SUPPORT_LIBRARY_PATTERN.matcher(name).find()) {
                it.remove();
            }
        }
    }

    private static void setLogLevel(Options bean) {
        if (bean.isQuiet()) {
            ch.qos.logback.classic.Logger rootLogger = (ch.qos.logback.classic.Logger) LoggerFactory
                    .getLogger(ch.qos.logback.classic.Logger.ROOT_LOGGER_NAME);
            rootLogger.setLevel(Level.OFF);
            return;
        }

        if (bean.isVerbose()) {
            ch.qos.logback.classic.Logger rootLogger = (ch.qos.logback.classic.Logger) LoggerFactory
                    .getLogger(ch.qos.logback.classic.Logger.ROOT_LOGGER_NAME);
            rootLogger.setLevel(Level.INFO);
        } else if (bean.isVverbose()) {
            ch.qos.logback.classic.Logger rootLogger = (ch.qos.logback.classic.Logger) LoggerFactory
                    .getLogger(ch.qos.logback.classic.Logger.ROOT_LOGGER_NAME);
            rootLogger.setLevel(Level.DEBUG);
        } else if (bean.isVvverbose()) {
            ch.qos.logback.classic.Logger rootLogger = (ch.qos.logback.classic.Logger) LoggerFactory
                    .getLogger(ch.qos.logback.classic.Logger.ROOT_LOGGER_NAME);
            rootLogger.setLevel(Level.TRACE);
        }
    }

    public void run(String[] args) throws IOException, UnhandledVirtualException {
        Options opts = getOptions(args);

        setLogLevel(opts);
        if (log.isInfoEnabled()) {
            log.info("Options:\n{}", opts.toString());
        }

        long startTime = System.currentTimeMillis();
        DexBuilder dexBuilder = DexBuilder.makeDexBuilder(opts.getOutputAPILevel());
        ClassManager classManager = getClassManager(opts.getInFile(), opts.isApk() | opts.isDex(), dexBuilder);
        VirtualMachine vm = new VirtualMachine(classManager, opts.getMaxAddressVisits(), opts.getMaxCallDepth(),
                opts.getMaxMethodVisits());

        Set<String> classNames = classManager.getNonFrameworkClassNames();
        for (String className : classNames) {
            Set<String> methodDescriptors = classManager.getMethodDescriptors(className);
            filterMethods(methodDescriptors, opts.getIncludeFilter(), opts.getExcludeFilter());
            if (!opts.includeSupportLibrary()) {
                filterSupportLibrary(methodDescriptors);
            }

            for (String methodDescriptor : methodDescriptors) {
                if (opts.isStaticOnly() && !methodDescriptor.endsWith("<clinit>()V")) {
                    System.out.println("Skipping " + methodDescriptor);
                    continue;
                }

                boolean shouldExecuteAgain;
                do {
                    System.out.println("Executing: " + methodDescriptor);
                    ExecutionGraph graph = null;
                    try {
                        graph = vm.execute(methodDescriptor);
                    } catch (MaxAddressVisitsExceeded | MaxCallDepthExceeded | MaxMethodVisitsExceeded e) {
                        System.err.println("Max visitation exception: " + e);
                    }

                    if (null == graph) {
                        System.out.println("Skipping " + methodDescriptor);
                        break;
                    }

                    BuilderMethod method = classManager.getMethod(methodDescriptor);
                    Optimizer optimizer = new Optimizer(graph, method, vm, dexBuilder);
                    optimizer.simplify(opts.getMaxOptimizationPasses());
                    if (optimizer.madeChanges()) {
                        // Optimizer changed the implementation. Re-build graph to include changes.
                        vm.updateInstructionGraph(methodDescriptor);
                    }
                    System.out.println(optimizer.getOptimizationCounts());

                    shouldExecuteAgain = optimizer.getShouldExecuteAgain();
                } while (shouldExecuteAgain);
            }
        }

        long totalTime = System.currentTimeMillis() - startTime;
        System.out.println("Simplified " + classNames.size() + " classes in " + totalTime + " ms.");
        System.out.println(Optimizer.getTotalOptimizationCounts());

        System.out.println("Writing output to " + opts.getOutFile());
        dexBuilder.writeTo(new FileDataStore(opts.getOutDexFile()));
        if (opts.isApk()) {
            FileUtils.copyFile(opts.getInFile(), opts.getOutFile());
            updateZip(opts.getOutFile(), opts.getOutDexFile(), "classes.dex");
        }
    }

}
