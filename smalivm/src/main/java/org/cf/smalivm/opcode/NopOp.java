package org.cf.smalivm.opcode;

import org.cf.smalivm.context.ExecutionNode;
import org.cf.smalivm.context.MethodState;
import org.jf.dexlib2.iface.instruction.Instruction;

public class NopOp extends MethodStateOp {

    static NopOp create(Instruction instruction, int address) {
        String opName = instruction.getOpcode().name;
        int childAddress = address + instruction.getCodeUnits();

        return new NopOp(address, opName, childAddress);
    }

    private NopOp(int address, String opName, int childAddress) {
        super(address, opName, childAddress);
    }

    @Override
    public void execute(ExecutionNode node, MethodState mState) {
        // Yesterday, upon the stair,
        // I met an op who wasn't there.
        // It wasn't there again today,
        // I wish, I wish it'd go away...
        //
        // Last night I saw upon the stair,
        // A little op who wasn't there,
        // It wasn't there again today
        // Oh, how I wish it'd go away...
    }

    @Override
    public String toString() {
        return getName();
    }

    @Override
    public boolean modifiesRegister(int register) {
        return false;
    }

}
