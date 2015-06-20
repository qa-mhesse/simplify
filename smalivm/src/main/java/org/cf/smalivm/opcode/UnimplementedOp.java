package org.cf.smalivm.opcode;

import org.cf.smalivm.context.ExecutionNode;
import org.cf.smalivm.context.HeapItem;
import org.cf.smalivm.context.MethodState;
import org.jf.dexlib2.Opcode;
import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.instruction.OneRegisterInstruction;

class UnimplementedOp extends MethodStateOp {

    private static final String UNKNOWN_TYPE = "?";
    private final boolean canContinue;
    private final boolean canThrow;
    private final int registerA;
    private final boolean setsRegister;
    private final boolean setsResult;

    UnimplementedOp(int address, String opName, int childAddress, boolean canContinue, boolean canThrow,
                    boolean setsResult) {
        this(address, opName, childAddress, canContinue, canThrow, setsResult, false, -1);
    }

    UnimplementedOp(int address, String opName, int childAddress, boolean canContinue, boolean canThrow,
                    boolean setsResult, boolean setsRegister, int registerA) {
        super(address, opName, canContinue ? childAddress : 0);

        this.canContinue = canContinue;
        this.canThrow = canThrow;
        this.setsResult = setsResult;
        this.setsRegister = setsRegister;
        this.registerA = registerA;
    }

    static UnimplementedOp create(Instruction instruction, int address) {
        UnimplementedOp result;

        int childAddress = address + instruction.getCodeUnits();
        Opcode op = instruction.getOpcode();

        if (instruction instanceof OneRegisterInstruction) {
            OneRegisterInstruction instr = (OneRegisterInstruction) instruction;
            int registerA = instr.getRegisterA();

            result = new UnimplementedOp(address, op.name, childAddress, op.canContinue(), op.canThrow(),
                    op.setsResult(), op.setsRegister(), registerA);
        } else {
            result = new UnimplementedOp(address, op.name, childAddress, op.canContinue(), op.canThrow(),
                    op.setsResult());
        }

        return result;
    }

    @Override
    public void execute(ExecutionNode node, MethodState mState) {
        if (setsResult) {
            mState.assignResultRegister(HeapItem.newUnknown(UNKNOWN_TYPE));
        }

        if (registerA >= 0) {
            if (setsRegister) {
                mState.assignRegister(registerA, HeapItem.newUnknown(UNKNOWN_TYPE));
            } else {
                mState.readRegister(registerA);
            }
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder(getName());
        if (registerA >= 0) {
            sb.append(" r").append(registerA);
        }
        sb.append(" (unimplmented)");

        return sb.toString();
    }

}
