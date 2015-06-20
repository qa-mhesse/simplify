package org.cf.smalivm.emulate;

import org.cf.smalivm.SideEffect.Level;
import org.cf.smalivm.VirtualException;

import java.util.Set;

public interface EmulatedMethod {

    Level getSideEffectLevel();

    Set<VirtualException> getExceptions();

}
