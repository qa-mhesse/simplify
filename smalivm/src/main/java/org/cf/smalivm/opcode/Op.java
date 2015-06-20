package org.cf.smalivm.opcode;

import org.cf.smalivm.SideEffect;
import org.cf.smalivm.VirtualException;

import java.util.HashSet;
import java.util.Set;

public abstract class Op {

    private final String opName;
    private final Set<VirtualException> exceptions;
    // These should be final, but when graphs are modified, these values need to change.
    private int address;
    private int[] childAddresses;

    Op(int address, String opName, int childAddress) {
        this(address, opName, new int[]{childAddress});
    }

    Op(int address, String opName, int[] childAddresses) {
        this.address = address;
        this.opName = opName;
        this.childAddresses = childAddresses;
        exceptions = new HashSet<>();
    }

    public final int getAddress() {
        return address;
    }

    public void setAddress(int address) {
        this.address = address;
    }

    public final String getName() {
        return opName;
    }

    public final int[] getChildren() {
        return childAddresses;
    }

    public void setChildren(int... childAddresses) {
        this.childAddresses = childAddresses;
    }

    public SideEffect.Level sideEffectLevel() {
        return SideEffect.Level.NONE;
    }

    void addException(VirtualException exception) {
        exceptions.add(exception);
    }

    public Set<VirtualException> getExceptions() {
        return exceptions;
    }

    @Override
    public abstract String toString();

}
