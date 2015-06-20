package org.cf.simplify;

import org.cf.smalivm.exception.UnhandledVirtualException;

import java.io.IOException;

public class Main {

    private static Launcher launcher = new Launcher();

    public static void main(String[] args) throws IOException, UnhandledVirtualException {
        launcher.run(args);
    }

    static void setLauncher(Launcher launcher) {
        Main.launcher = launcher;
    }

}
