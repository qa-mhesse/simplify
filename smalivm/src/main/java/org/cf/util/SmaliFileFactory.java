package org.cf.util;

import org.apache.commons.io.FileUtils;
import org.cf.smalivm.SmaliFile;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.IOException;
import java.util.*;

public class SmaliFileFactory {

    private static final Logger log = LoggerFactory.getLogger(SmaliFileFactory.class.getSimpleName());

    private static Map<String, SmaliFile> frameworkCache;

    private Map<String, SmaliFile> frameworkClassNameToSmaliFile;

    private static List<File> getFilesWithSmaliExtension(File file) {
        List<File> files = new LinkedList<>();
        if (file.isDirectory()) {
            files = (List<File>) FileUtils.listFiles(file, new String[]{"smali"}, true);
        } else if (file.getAbsolutePath().toLowerCase().endsWith(".smali")) {
            files.add(file);
        }

        return files;
    }

    public Set<SmaliFile> getSmaliFiles(String path) throws IOException {
        return getSmaliFiles(new String[]{path});
    }

    public Set<SmaliFile> getSmaliFiles(String[] paths) throws IOException {
        File[] files = new File[paths.length];
        for (int i = 0; i < paths.length; i++) {
            files[i] = new File(paths[i]);
        }

        return getSmaliFiles(files);
    }

    public Set<SmaliFile> getSmaliFiles(File file) throws IOException {
        return getSmaliFiles(new File[]{file});
    }

    public boolean isFrameworkClass(String className) {
        return frameworkClassNameToSmaliFile.containsKey(className);
    }

    public boolean isSafeFrameworkClass(String className) {
        SmaliFile smaliFile = frameworkClassNameToSmaliFile.get(className);
        return null != smaliFile && smaliFile.isSafeFrameworkClass();
    }

    private synchronized void cacheFramework() throws IOException {
        if (frameworkCache != null) {
            return;
        }

        frameworkCache = new HashMap<>();

        long startTime = System.currentTimeMillis();
        List<String> frameworkClassesCfg = ConfigLoader.loadConfig("framework_classes.cfg");
        Set<String> safeFrameworkClasses = new HashSet<>(ConfigLoader.loadConfig("safe_framework_classes.cfg"));
        for (String line : frameworkClassesCfg) {
            String[] parts = line.split(":");
            String className = parts[0];
            String path = parts[1];
            SmaliFile smaliFile = new SmaliFile(path, className);
            smaliFile.setIsResource(true);
            smaliFile.setIsSafeFramework(safeFrameworkClasses.contains(className));
            frameworkCache.put(smaliFile.getClassName(), smaliFile);
        }

        if (log.isDebugEnabled()) {
            long endTime = System.currentTimeMillis();
            long totalTime = endTime - startTime; // assuming time has not gone backwards
            log.debug("Cached " + frameworkCache.size() + " framework classes in " + totalTime + " ms.");
        }
    }

    public Set<SmaliFile> getSmaliFiles(File[] files) throws IOException {
        Set<SmaliFile> smaliFiles = new HashSet<>();
        Set<String> inputClasses = new HashSet<>();
        for (File file : files) {
            List<File> matches = getFilesWithSmaliExtension(file);
            for (File match : matches) {
                SmaliFile smaliFile = new SmaliFile(match);
                smaliFiles.add(smaliFile);
                inputClasses.add(smaliFile.getClassName());
            }
        }

        cacheFramework();

        // Override framework classes with input classes of the same name
        frameworkClassNameToSmaliFile = new HashMap<>(frameworkCache);
        List<Map.Entry<String, SmaliFile>> entriesToRemove = new LinkedList<Map.Entry<String, SmaliFile>>();
        for (Map.Entry<String, SmaliFile> entry : frameworkClassNameToSmaliFile.entrySet()) {
            if (inputClasses.contains(entry.getKey())) {
                entriesToRemove.add(entry);
            } else {
                smaliFiles.add(entry.getValue());
            }
        }
        frameworkClassNameToSmaliFile.entrySet().removeAll(entriesToRemove);

        return smaliFiles;
    }

}
