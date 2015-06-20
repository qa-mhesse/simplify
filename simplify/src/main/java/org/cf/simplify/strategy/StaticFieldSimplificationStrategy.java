package org.cf.simplify.strategy;

import org.cf.simplify.ConstantBuilder;
import org.cf.simplify.MethodBackedGraph;
import org.cf.smalivm.context.ClassState;
import org.cf.smalivm.context.ExecutionContext;
import org.cf.smalivm.context.ExecutionNode;
import org.cf.smalivm.context.HeapItem;
import org.cf.smalivm.type.UninitializedInstance;
import org.cf.smalivm.type.UnknownValue;
import org.jf.dexlib2.Opcode;
import org.jf.dexlib2.builder.BuilderInstruction;
import org.jf.dexlib2.builder.instruction.BuilderInstruction21c;
import org.jf.dexlib2.builder.instruction.BuilderInstruction23x;
import org.jf.dexlib2.writer.builder.BuilderFieldReference;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class StaticFieldSimplificationStrategy implements OptimizationStrategy {
    private static final Logger log = LoggerFactory.getLogger(StaticFieldSimplificationStrategy.class.getSimpleName());
    private final MethodBackedGraph mbgraph;
    private int decryptCount;
    private int insertedInstructionsCount;

    public StaticFieldSimplificationStrategy(MethodBackedGraph mbgraph) {
        this.mbgraph = mbgraph;
        decryptCount = 0;
        insertedInstructionsCount = 0;
    }

    public Map<String, Integer> getOptimizationCounts() {
        Map<String, Integer> result = new HashMap<>();
        result.put("staticDecrypts", decryptCount);

        return result;
    }

    public boolean perform() {
        if (!mbgraph.getMethodDescriptor().endsWith("<clinit>()V")) return false;

        boolean changes = false;

        // obtain last instruction
        ExecutionNode last = mbgraph.getRoot();
        while (last.getChildren().size() > 0) {
            last = last.getChildren().get(0);
        }
        ExecutionNode node = last.getParent();


        ExecutionContext c = node.getContext();
        Set<String> initClasses = node.getContext().getInitializedClasses();

        for (String className : initClasses) {
            ClassState classState = c.peekClassState(className);

            for (String fieldName : classState.getFieldNames()) {
                HeapItem field = classState.peekField(fieldName);
                Object fieldValue = field.getValue();

                if (!(fieldValue instanceof UnknownValue || fieldValue instanceof UninitializedInstance)) {
                    if (isPrimitive(fieldValue)) {
                        changes |= substitutePrimitiveField(last.getAddress(), className, fieldName, field);
                    } else if (fieldValue.getClass().isArray()) {
                        changes |= substituteArrayField(last.getAddress(), className, fieldName, field);
                    } else {
                        System.out.println(fieldName + ": object (" + fieldValue.getClass() + ") = " + fieldValue);
                        changes = substituteObjectField(last.getAddress(), className, fieldName, field);
                    }
                }
            }
        }

        System.out.println(mbgraph.toSmali());
        return changes;
    }

    private boolean isPrimitive(Object o) {
        return o.getClass().isPrimitive() || o.getClass().equals(String.class);
    }

    private boolean isWide(Object o) {
        return o.getClass().equals(Long.class) || o.getClass().equals(Double.class);
    }

    private boolean substitutePrimitiveField(int lastAddress, String className, String fieldName, HeapItem field) {
        Object fieldValue = field.getValue();

        BuilderInstruction createStatic = ConstantBuilder.buildConstant(fieldValue, field.getType(), 0, mbgraph.getDexBuilder());
        String realFieldName = fieldName.substring(0, fieldName.length() - field.getType().length() - 1);
        BuilderFieldReference bfr = mbgraph.getDexBuilder().internFieldReference(mbgraph.getVM().getClassManager().getField(className, realFieldName));
        BuilderInstruction assignStatic = new BuilderInstruction21c((isWide(fieldValue) ? Opcode.SPUT_WIDE : Opcode.SPUT), 0, bfr);

        mbgraph.insertInstruction(lastAddress, createStatic);
        mbgraph.insertInstruction(lastAddress, assignStatic);

        decryptCount++;
        insertedInstructionsCount += 2;
        if (log.isInfoEnabled()) {
            log.info("Directly set primitive static field " + fieldName + " to \"" + fieldValue + "\"");
        }

        return true;
    }

    private boolean substituteArrayField(int lastAddress, String className, String fieldName, HeapItem field) {
        int i = 0;
        boolean changes = false;

        String realFieldName = fieldName.substring(0, fieldName.length() - field.getType().length() - 1);
        BuilderFieldReference bfr = mbgraph.getDexBuilder().internFieldReference(mbgraph.getVM().getClassManager().getField(className, realFieldName));
        BuilderInstruction getArray = new BuilderInstruction21c(Opcode.SGET_OBJECT, 0, bfr);
        mbgraph.insertInstruction(lastAddress, getArray);

        for (Object o : (Object[]) field.getValue()) {
            if (o instanceof UnknownValue) continue;
            else if (o.getClass().isPrimitive() || o.getClass().equals(String.class)) {
                BuilderInstruction arrayIndex = ConstantBuilder.buildConstant(i, "I", 1, mbgraph.getDexBuilder());
                BuilderInstruction createStatic = ConstantBuilder.buildConstant(o, field.getType().substring(1), 2, mbgraph.getDexBuilder());
                BuilderInstruction assignStatic = new BuilderInstruction23x((isWide(o) ? Opcode.APUT_WIDE : Opcode.APUT), 2, 0, 1);

                mbgraph.insertInstruction(lastAddress, arrayIndex);
                mbgraph.insertInstruction(lastAddress, createStatic);
                mbgraph.insertInstruction(lastAddress, assignStatic);

                decryptCount++;
                insertedInstructionsCount += 3;
                changes = true;
                if (log.isInfoEnabled()) {
                    log.info("Directly set primitive entry #" + i + " of array field " + fieldName + " to \"" + o + "\"");
                }
            } else {
                // TODO: set field to value
                System.out.println("  [" + i + "]: object (" + o.getClass() + ") = " + o);
            }
            i++;
        }

        if (changes) {
            BuilderInstruction putArray = new BuilderInstruction21c(Opcode.SPUT_OBJECT, 0, bfr);
            mbgraph.insertInstruction(lastAddress, putArray);
            insertedInstructionsCount += 2;
        } else {
            mbgraph.removeInstruction(lastAddress);
        }

        return changes;
    }

    private boolean substituteObjectField(int last, String className, String fieldName, HeapItem field) {
        // TODO: set field to value
        return false;
    }

    private void traceBackToPrimitves(int address, int last, String field, boolean fr) {
        // TODO; trace object back to primitive values
    }
}