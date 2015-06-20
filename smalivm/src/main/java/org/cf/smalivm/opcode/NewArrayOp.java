package org.cf.smalivm.opcode;

import org.cf.smalivm.ClassManager;
import org.cf.smalivm.VirtualMachine;
import org.cf.smalivm.context.ExecutionNode;
import org.cf.smalivm.context.HeapItem;
import org.cf.smalivm.context.MethodState;
import org.cf.util.SmaliClassUtils;
import org.cf.util.Utils;
import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.instruction.formats.Instruction22c;
import org.jf.dexlib2.util.ReferenceUtil;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class NewArrayOp extends MethodStateOp {

    private static final Logger log = LoggerFactory.getLogger(NewArrayOp.class.getSimpleName());
    private final int destRegister;
    private final int lengthRegister;
    private final boolean useLocalClass;
    private final String arrayType;

    private NewArrayOp(int address, String opName, int childAddress, int destRegister, int lengthRegister,
                       String arrayType, boolean useLocalClass) {
        super(address, opName, childAddress);

        this.destRegister = destRegister;
        this.lengthRegister = lengthRegister;
        this.arrayType = arrayType;
        this.useLocalClass = useLocalClass;
    }

    static NewArrayOp create(Instruction instruction, int address, VirtualMachine vm) {
        String opName = instruction.getOpcode().name;
        int childAddress = address + instruction.getCodeUnits();

        Instruction22c instr = (Instruction22c) instruction;
        int destRegister = instr.getRegisterA();
        int sizeRegister = instr.getRegisterB();

        // [[Lsome_class;
        String arrayType = ReferenceUtil.getReferenceString(instr.getReference());
        String baseClassName = SmaliClassUtils.getBaseClass(arrayType);
        ClassManager classManager = vm.getClassManager();
        boolean useLocalClass;
        if (classManager.isFramework(baseClassName)) {
            useLocalClass = classManager.isSafeFramework(baseClassName);
        } else {
            useLocalClass = classManager.isLocalClass(baseClassName);
        }

        return new NewArrayOp(address, opName, childAddress, destRegister, sizeRegister, arrayType, useLocalClass);
    }

    @Override
    public void execute(ExecutionNode node, MethodState mState) {
        HeapItem lengthItem = mState.readRegister(lengthRegister);
        HeapItem instanceItem;
        if (lengthItem.isUnknown()) {
            instanceItem = HeapItem.newUnknown(arrayType);
        } else {
            int length = lengthItem.getIntegerValue();
            try {
                // Dalvik does not statically initialize classes with new-array
                Object instance = Utils.buildArray(arrayType, length, useLocalClass);
                instanceItem = new HeapItem(instance, arrayType);
            } catch (ClassNotFoundException e) {
                if (log.isErrorEnabled()) {
                    log.error("Couldn't find class: " + arrayType + " @" + toString(), e);
                }
                instanceItem = HeapItem.newUnknown(arrayType);
            }
        }
        mState.assignRegister(destRegister, instanceItem);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder(getName());
        sb.append(" r").append(destRegister).append(", r").append(lengthRegister).append(", ").append(arrayType);

        return sb.toString();
    }

}
