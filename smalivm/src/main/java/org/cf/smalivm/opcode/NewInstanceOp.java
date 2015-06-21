package org.cf.smalivm.opcode;

import org.cf.smalivm.MethodReflector;
import org.cf.smalivm.SideEffect;
import org.cf.smalivm.VirtualMachine;
import org.cf.smalivm.context.ExecutionContext;
import org.cf.smalivm.context.ExecutionNode;
import org.cf.smalivm.context.HeapItem;
import org.cf.smalivm.context.MethodState;
import org.cf.smalivm.type.LocalInstance;
import org.cf.smalivm.type.UninitializedInstance;
import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.instruction.formats.Instruction21c;
import org.jf.dexlib2.iface.reference.TypeReference;

public class NewInstanceOp extends ExecutionContextOp {

    static NewInstanceOp create(Instruction instruction, int address, VirtualMachine vm) {
        String opName = instruction.getOpcode().name;
        int childAddress = address + instruction.getCodeUnits();

        Instruction21c instr = (Instruction21c) instruction;
        int destRegister = instr.getRegisterA();
        TypeReference typeRef = (TypeReference) instr.getReference();
        String className = typeRef.getType();

        return new NewInstanceOp(address, opName, childAddress, destRegister, className, vm);
    }

    private final String className;
    private final int destRegister;
    private SideEffect.Level sideEffectLevel;
    private final VirtualMachine vm;

    NewInstanceOp(int address, String opName, int childAddress, int destRegister, String className, VirtualMachine vm) {
        super(address, opName, childAddress);

        this.destRegister = destRegister;
        this.className = className;
        this.vm = vm;
        sideEffectLevel = SideEffect.Level.STRONG;
    }

    @Override
    public void execute(ExecutionNode node, ExecutionContext ectx) {
        Object instance = null;
        if (vm.isLocalClass(className)) {
            // New-instance causes static initialization (but not new-array!)
            ectx.readClassState(className); // access will initialize if necessary
            sideEffectLevel = ectx.getClassSideEffectLevel(className);
            instance = new LocalInstance(className);
        } else {
            if (MethodReflector.isSafe(className)) {
                sideEffectLevel = SideEffect.Level.NONE;
            }
            instance = new UninitializedInstance(className);
        }

        MethodState mState = ectx.getMethodState();
        HeapItem instanceItem = new HeapItem(instance, className);
        mState.assignRegister(destRegister, instanceItem);
    }

    @Override
    public SideEffect.Level sideEffectLevel() {
        return sideEffectLevel;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder(getName());
        sb.append(" r").append(destRegister).append(", ").append(className);

        return sb.toString();
    }

    @Override
    public boolean modifiesRegister(int register) {
        return register == destRegister;
    }
}
