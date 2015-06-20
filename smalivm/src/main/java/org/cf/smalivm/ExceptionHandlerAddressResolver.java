package org.cf.smalivm;

import org.cf.util.SmaliClassUtils;
import org.jf.dexlib2.builder.BuilderTryBlock;
import org.jf.dexlib2.iface.ExceptionHandler;
import org.jf.dexlib2.iface.TryBlock;

import java.util.*;

public class ExceptionHandlerAddressResolver {

    private final ClassManager classManager;
    private final List<BuilderTryBlock> tryBlocks;

    ExceptionHandlerAddressResolver(ClassManager classManager, String methodDescriptor) {
        this.classManager = classManager;
        tryBlocks = classManager.getTryBlocks(methodDescriptor);
    }

    @Deprecated
    int resolve(Exception ex, int address) {
        String exceptionClass = SmaliClassUtils.javaClassToSmali(ex.getClass().getName());
        return resolve(exceptionClass, address);
    }

    int resolve(VirtualException vex, int address) {
        return resolve(vex.getExceptionClass(), address);
    }

    private int resolve(String exceptionClass, int address) {
        Deque<String> classAncestors = new ArrayDeque<String>();
        classAncestors.add(exceptionClass);
        Set<String> visited = new HashSet<String>();

        String currentExceptionClass;
        while ((currentExceptionClass = classAncestors.poll()) != null) {
            for (TryBlock<? extends ExceptionHandler> tryBlock : tryBlocks) {
                if ((address < tryBlock.getStartCodeAddress()) || (address > (tryBlock.getStartCodeAddress() + tryBlock
                        .getCodeUnitCount()))) {
                    // address is not inside of this try/catch
                    continue;
                }

                List<? extends ExceptionHandler> handlers = tryBlock.getExceptionHandlers();
                for (ExceptionHandler handler : handlers) {
                    String handlerType = handler.getExceptionType();
                    if (currentExceptionClass.equals(handlerType)) {
                        int handlerAddress = handler.getHandlerCodeAddress();

                        return handlerAddress;
                    }
                }
            }

            visited.add(currentExceptionClass);
            Set<String> ancestors = classManager.getClassAncestors(currentExceptionClass);
            ancestors.removeAll(visited);
            classAncestors.addAll(ancestors);
        }

        // Not caught by anything. Look for a catch-all / finally.
        for (TryBlock<? extends ExceptionHandler> tryBlock : tryBlocks) {
            if ((address < tryBlock.getStartCodeAddress()) || (address > (tryBlock.getStartCodeAddress() + tryBlock
                    .getCodeUnitCount()))) {
                // address is not inside of this try/catch
                continue;
            }

            List<? extends ExceptionHandler> handlers = tryBlock.getExceptionHandlers();
            ExceptionHandler handler = handlers.get(handlers.size() - 1);
            if (null == handler.getExceptionType()) {
                // catch-all
                int handlerAddress = handler.getHandlerCodeAddress();

                return handlerAddress;
            }

        }

        return -1;
    }

}
