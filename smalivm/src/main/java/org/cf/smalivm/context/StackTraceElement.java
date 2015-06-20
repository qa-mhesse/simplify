package org.cf.smalivm.context;

import org.cf.util.SmaliClassUtils;

public class StackTraceElement {

    private String definingClass;
    private String methodName;
    private String fileName;
    private int lineNumber;

    public StackTraceElement(String methodDescriptor, String fileName, int lineNumber) {
        String[] parts = methodDescriptor.split("->");
        definingClass = SmaliClassUtils.smaliClassToJava(parts[0]);
        methodName = parts[1].split("\\(")[0];
        this.fileName = fileName;
        this.lineNumber = lineNumber;
    }

    public String getDeclaringClass() {
        return definingClass;
    }

    public String getMethodName() {
        return methodName;
    }

    public String getFileName() {
        return fileName;
    }

    public int getLineNumber() {
        return lineNumber;
    }

    @Override
    public String toString() {
        // E.g. java.lang.Thread.getStackTrace(Thread.java:1589)
        return getDeclaringClass() + '.' + getMethodName() + '(' + getFileName() + ':' + getLineNumber() + ')';
    }

}
