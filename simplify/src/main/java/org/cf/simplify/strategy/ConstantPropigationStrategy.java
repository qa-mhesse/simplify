package org.cf.simplify.strategy;

import org.cf.simplify.ConstantBuilder;
import org.cf.simplify.Dependancy;
import org.cf.simplify.MethodBackedGraph;
import org.cf.smalivm.context.HeapItem;
import org.cf.smalivm.opcode.Op;
import org.jf.dexlib2.builder.BuilderInstruction;
import org.jf.dexlib2.iface.instruction.OneRegisterInstruction;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.HashMap;
import java.util.Map;

public class ConstantPropigationStrategy implements OptimizationStrategy {

    @SuppressWarnings("unused")
    private static final Logger log = LoggerFactory.getLogger(ConstantPropigationStrategy.class.getSimpleName());

    private final MethodBackedGraph mbgraph;
    protected ConstantBuilder constantBuilder;
    private int constantCount;
    private boolean madeChanges;

    public ConstantPropigationStrategy(MethodBackedGraph mbgraph) {
        getDependancies();
        this.mbgraph = mbgraph;
        constantCount = 0;
    }

    @Override
    public Map<String, Integer> getOptimizationCounts() {
        Map<String, Integer> result = new HashMap<String, Integer>();
        result.put("constants", constantCount);

        return result;
    }

    @Override
    public boolean perform() {
        madeChanges = false;

        for (int address : mbgraph.getAddresses()) {
            BuilderInstruction original = mbgraph.getInstruction(address);
            if (canConstantizeAddress(address)) {
                madeChanges = true;

                BuilderInstruction constInstruction = ConstantBuilder.buildConstant(address, mbgraph);
                if (original.getOpcode().name().startsWith("RETURN")) {
                    mbgraph.insertInstruction(address, constInstruction);
                } else {
                    mbgraph.replaceInstruction(address, constInstruction);
                }
                constantCount++;
            }
        }

        return madeChanges;
    }

    private boolean canConstantizeAddress(int address) {
        if (!mbgraph.wasAddressReached(address)) {
            return false;
        }

        Op op = mbgraph.getOp(address);
        if (!constantBuilder.canConstantizeOp(op)) {
            return false;
        }

        OneRegisterInstruction instruction = (OneRegisterInstruction) mbgraph.getInstruction(address);
        int register = instruction.getRegisterA();
        HeapItem consensus = mbgraph.getRegisterConsensus(address, register);
        // Consensus may be null if we have correct syntax without legitimate values (fake code)
        if ((consensus == null) || consensus.isUnknown()) {
            return false;
        }

        String unboxedValueType = consensus.getUnboxedValueType();
        if (!constantBuilder.canConstantizeType(unboxedValueType)) {
            return false;
        }

        return true;
    }

    protected void getDependancies() {
        if (constantBuilder == null) {
            constantBuilder = new ConstantBuilder();
        }
    }

    protected void setDependancies(Dependancy dependancy) {
        constantBuilder = (ConstantBuilder) dependancy;
    }

}
