package org.cf.simplify.strategy;

import gnu.trove.list.TIntList;
import gnu.trove.list.array.TIntArrayList;
import org.cf.simplify.ConstantBuilder;
import org.cf.simplify.MethodBackedGraph;
import org.cf.smalivm.context.ClassState;
import org.cf.smalivm.context.ExecutionContext;
import org.cf.smalivm.context.ExecutionNode;
import org.cf.smalivm.context.HeapItem;
import org.cf.smalivm.opcode.*;
import org.cf.smalivm.type.UninitializedInstance;
import org.cf.smalivm.type.UnknownValue;
import org.cf.util.SmaliClassUtils;
import org.jf.dexlib2.Opcode;
import org.jf.dexlib2.builder.BuilderInstruction;
import org.jf.dexlib2.builder.instruction.*;
import org.jf.dexlib2.iface.instruction.TwoRegisterInstruction;
import org.jf.dexlib2.iface.reference.FieldReference;
import org.jf.dexlib2.writer.builder.BuilderFieldReference;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.reflect.Array;
import java.util.*;

public class StaticFieldSimplificationStrategy implements OptimizationStrategy {
    private static final Logger log = LoggerFactory.getLogger(StaticFieldSimplificationStrategy.class.getSimpleName());
    private final MethodBackedGraph graph;
    private int simplificationCount;
    private int addrDiff;
    private int insertedInstructions;

    public StaticFieldSimplificationStrategy(MethodBackedGraph graph) {
        this.graph = graph;
        simplificationCount = 0;
        addrDiff = 0;
        insertedInstructions = 0;
    }

    public Map<String, Integer> getOptimizationCounts() {
        Map<String, Integer> result = new HashMap<>();
        result.put("staticDecrypts", simplificationCount);

        return result;
    }

    public boolean perform() {
        if (!graph.getMethodDescriptor().endsWith("<clinit>()V")) return false;

        // obtain last instruction
        ExecutionNode last = graph.getRoot();
        while (last.getChildren().size() > 0) {
            last = last.getChildren().get(0);
        }
        ExecutionNode node = last.getParent();

        ExecutionContext c = node.getContext();
        Set<String> initClasses = node.getContext().getInitializedClasses();

        boolean substitutedAll = true;
        for (String className : initClasses) {
            if (!graph.getMethodDescriptor().startsWith(className)) continue;
            ClassState classState = c.peekClassState(className);

            for (String fieldName : classState.getFieldNames()) {
                HeapItem field = classState.peekField(fieldName);
                Object fieldValue = field.getValue();

                if (!(fieldValue instanceof UnknownValue || fieldValue instanceof UninitializedInstance)) {
                    if (canMakeSimpleConstant(field.getType())) {
                        if (substitutePrimitiveField(last, className, fieldName, field)) simplificationCount++;
                        else {
                            substitutedAll = false;
                            if (log.isInfoEnabled()) {
                                log.info("Couldn't substitute field " + fieldName);
                            }
                        }
                    } else if (canMakeArraySimpleConstant(field.getType())) {
                        if (substitutePrimitiveArrayField(last, className, fieldName, field)) simplificationCount++;
                        else {
                            substitutedAll = false;
                            if (log.isInfoEnabled()) {
                                log.info("Couldn't substitute field " + fieldName);
                            }
                        }
                    } else {
                        if (substituteNonPrimitiveField(last, className, fieldName, field)) simplificationCount++;
                        else {
                            substitutedAll = false;
                            if (log.isInfoEnabled()) {
                                log.info("Couldn't substitute field " + fieldName);
                            }
                        }
                    }
                }
            }
        }

        if (substitutedAll) {
            removeUnnecessaryInstructions(last);
        }

        return addrDiff > 0;
    }

    private void removeUnnecessaryInstructions(ExecutionNode last) {
        // remove all switch / switch-payload instructions first
        while (true) {
            TIntList addresses = new TIntArrayList(graph.getAddresses());
            addresses.sort();
            int[] addrs = addresses.toArray();

            boolean removedInstruction = false;
            for (int i = 0; i < addrs.length && !removedInstruction; i++) {
                Op o = graph.getTemplateNode(addrs[i]).getOp();
                if (o instanceof SwitchOp || o instanceof SwitchPayloadOp) {
                    try {
                        graph.removeInstruction(addrs[i]);
                        removedInstruction = true;

                        if (log.isInfoEnabled()) {
                            log.info("removed " + o.toString() + " @" + addrs[i]);
                        }
                    } catch (IndexOutOfBoundsException | NullPointerException | IllegalStateException e) {
                        log.warn("tried to remove switch instruction which isn't there: " + o.toString() + " @" + addrs[i]);
                    }
                }
            }
            if (!removedInstruction) break;
        }

        // then remove all goto instructions
        while (true) {
            TIntList addresses = new TIntArrayList(graph.getAddresses());
            addresses.sort();
            int[] addrs = addresses.toArray();

            boolean removedInstruction = false;
            for (int i = 0; i < addrs.length && !removedInstruction; i++) {
                Op o = graph.getTemplateNode(addrs[i]).getOp();
                if (o instanceof GotoOp) {
                    try {
                        graph.removeInstruction(addrs[i]);
                        removedInstruction = true;

                        if (log.isInfoEnabled()) {
                            log.info("removed " + o.toString() + " @" + addrs[i]);
                        }
                    } catch (IndexOutOfBoundsException | NullPointerException | IllegalStateException e) {
                        log.warn("tried to remove goto instruction which isn't there: " + o.toString() + " @" + addrs[i]);
                    }
                }
            }
            if (!removedInstruction) break;
        }

        // thirdly remove all if instructions
        while (true) {
            TIntList addresses = new TIntArrayList(graph.getAddresses());
            addresses.sort();
            int[] addrs = addresses.toArray();

            boolean removedInstruction = false;
            for (int i = 0; i < addrs.length && !removedInstruction; i++) {
                Op o = graph.getTemplateNode(addrs[i]).getOp();
                if (o instanceof IfOp) {
                    try {
                        graph.removeInstruction(addrs[i]);
                        removedInstruction = true;

                        if (log.isInfoEnabled()) {
                            log.info("removed " + o.toString() + " @" + addrs[i]);
                        }
                    } catch (IndexOutOfBoundsException | NullPointerException | IllegalStateException e) {
                        log.warn("tried to remove if instruction which isn't there: " + o.toString() + " @" + addrs[i]);
                    }
                }
            }
            if (!removedInstruction) break;
        }

        // remove all other instructions that we don't need
        while (true) {
            TIntList addresses = new TIntArrayList(graph.getAddresses());
            addresses.sort();
            int[] addrs = addresses.toArray();

            boolean removedInstruction = false;

            // recalculate addresses we don't want to remove
            ExecutionNode first = last;
            int[] protect = new int[insertedInstructions + 1];
            for (int i = 0; i <= insertedInstructions; i++) {
                protect[i] = first.getAddress();
                first = first.getParent();
            }

            for (int i = 0; i < addrs.length && !removedInstruction; i++) {
                boolean canBeRemoved = true;
                for (int j = 0; j <= insertedInstructions; j++) {
                    if (addrs[i] == protect[j]) canBeRemoved = false;
                }

                if (canBeRemoved) {
                    try {
                        String op = graph.getTemplateNode(addrs[i]).getOp().toString();
                        graph.removeInstruction(addrs[i]);
                        removedInstruction = true;

                        if (log.isInfoEnabled()) {
                            log.info("removed " + op + " @" + addrs[i]);
                        }
                    } catch (IndexOutOfBoundsException | NullPointerException | IllegalStateException e) {
                        log.warn("tried to remove instruction which isn't there: @" + addrs[i]);
                    }
                }
            }
            if (!removedInstruction) break;
        }

        System.out.println(graph.toSmali());
    }

    private boolean substitutePrimitiveField(ExecutionNode last, String className, String fieldName, HeapItem field) {
        Object fieldValue = field.getValue();

        BuilderInstruction createStatic = ConstantBuilder.buildConstant(fieldValue, field.getType(), 0, graph.getDexBuilder());
        if (createStatic == null) return false;

        String realFieldName = fieldName.substring(0, fieldName.length() - field.getType().length() - 1);
        BuilderFieldReference bfr = graph.getDexBuilder().internFieldReference(graph.getVM().getClassManager().getField(className, realFieldName));
        BuilderInstruction assignStatic = new BuilderInstruction21c(getOpCodeVariant("SPUT", SmaliClassUtils.getBaseClass(field.getType())), 0, bfr);

        insert(last.getAddress(), createStatic);
        insert(last.getAddress(), assignStatic);

        simplificationCount++;
        if (log.isInfoEnabled()) {
            log.info("Directly set primitive static field " + fieldName + " to \"" + fieldValue + "\"");
        }

        return true;
    }

    private boolean substitutePrimitiveArrayField(ExecutionNode last, String className, String fieldName, HeapItem field) {
        boolean success = substitutePrimitiveArrayRegister(last, 0, field);

        String realFieldName = fieldName.substring(0, fieldName.length() - field.getType().length() - 1);
        BuilderFieldReference bfr = graph.getDexBuilder().internFieldReference(graph.getVM().getClassManager().getField(className, realFieldName));
        BuilderInstruction putArray = new BuilderInstruction21c(Opcode.SPUT_OBJECT, 0, bfr);
        insert(last.getAddress(), putArray);

        return success;
    }

    private boolean substitutePrimitiveArrayRegister(ExecutionNode last, int register, HeapItem field) {
        log.info(field.getValue().toString() + field.getValue().getClass().isArray());
        BuilderInstruction arraySize = ConstantBuilder.buildConstant(Array.getLength(field.getValue()), "I", 1, graph.getDexBuilder());
        BuilderInstruction newArray = new BuilderInstruction22c(Opcode.NEW_ARRAY, register, 1, graph.getDexBuilder().internTypeReference(field.getType()));
        insert(last.getAddress(), arraySize);
        insert(last.getAddress(), newArray);
        boolean success = true;

        for (int i = 0; i < Array.getLength(field.getValue()); i++) {
            Object arrayEntry = Array.get(field.getValue(), i);
            if (!(arrayEntry instanceof UnknownValue || arrayEntry instanceof UninitializedInstance)) {
                if (canMakeArraySimpleConstant(field.getType())) {
                    if (!substitutePrimitiveArrayEntry(last, register, i, arrayEntry, field.getType().substring(1))) {
                        success = false;
                        break;
                    }
                } else {
                    if (!traceBackNonPrimitiveArrayEntry(last, last, register, i, field.getType().substring(1))) {
                        success = false;
                        break;
                    }
                }
            }
        }

        return success;
    }

    private boolean substituteNonPrimitiveField(ExecutionNode last, String className, String fieldName, HeapItem field) {
        boolean success = traceBackNonPrimitiveField(last, last, className, fieldName, field.getType());

        if (log.isInfoEnabled()) {
            log.info("Directly set non primitive static field " + fieldName + " to " + field.getValue() + "\"");
        }

        return success;
    }

    private boolean substitutePrimitiveArrayEntry(ExecutionNode last, int arrayRegister, int index, Object primitiveValue, String smaliType) {
        int indexRegister = arrayRegister == 0 ? 1 : 0;
        int constantRegister = arrayRegister == 0 || arrayRegister == 1 ? 2 : 1;
        BuilderInstruction arrayIndex = ConstantBuilder.buildConstant(index, "I", indexRegister, graph.getDexBuilder());
        BuilderInstruction createStatic = ConstantBuilder.buildConstant(primitiveValue, smaliType, constantRegister, graph.getDexBuilder());

        if (createStatic == null) return false;
        BuilderInstruction assignStatic = new BuilderInstruction23x(getOpCodeVariant("APUT", smaliType), constantRegister, arrayRegister, indexRegister);

        insert(last.getAddress(), arrayIndex);
        insert(last.getAddress(), createStatic);
        insert(last.getAddress(), assignStatic);

        return true;
    }

    /*private boolean traceBackPrimitiveArray(ExecutionNode last, ExecutionNode address, int arrayRegister, String smaliType) {
        ExecutionNode current = address.getParent();

        while (!(current.getOp().modifiesRegister(arrayRegister) || registerInParameterList(current.getOp(), arrayRegister))) {
            current = current.getParent();
        }

        boolean success = true;
        BuilderInstruction instr = graph.getInstruction(current.getAddress());
        log.info(current.getOp().toString());
        switch (current.getOp().getClass().getSimpleName()) {
            case "InvokeOp":
                InvokeOp inv = (InvokeOp) current.getOp();
                String md = inv.getMethodDescriptor();
                List<String> types = graph.getVM().getClassManager().getParameterTypes(md);

                int i = 0;
                for (int r : inv.getParameterRegisters()) {
                    if (canMakeSimpleConstant(types.get(i))) {
                        BuilderInstruction buildConstant = ConstantBuilder.buildConstant(current.getContext().getMethodState().peekRegister(r).getValue(), types.get(i), r, graph.getDexBuilder());
                        if (buildConstant == null) return false;
                        insert(last.getAddress(), buildConstant);
                    } else if (canMakeArraySimpleConstant(types.get(i))) {
                        success = traceBackPrimitiveArray(last, current, r, types.get(i));
                    } else {
                        success = traceBackNonPrimitiveRegister(last, current, r, types.get(i));
                    }

                    if (!success) return false;
                    i++;
                }

            case "MoveOp":
                MoveOp.MoveType mt = ((MoveOp) current.getOp()).getMoveType();

                if (mt == MoveOp.MoveType.RESULT) {
                    current = current.getParent();
                    BuilderInstruction instr2 = graph.getInstruction(current.getAddress());

                    int[] parameterRegisters;

                    if (instr2 instanceof BuilderInstruction3rc) {
                        BuilderInstruction3rc bi3rc = (BuilderInstruction3rc) instr2;
                        parameterRegisters = new int[bi3rc.getRegisterCount()];
                        for (i = 0; i < parameterRegisters.length; i++) {
                            parameterRegisters[i] = bi3rc.getStartRegister() + i;
                        }
                    } else if (instr2 instanceof BuilderInstruction35c) {
                        BuilderInstruction35c bi35cc = (BuilderInstruction35c) instr2;
                        int regCount = bi35cc.getRegisterCount();
                        parameterRegisters = new int[regCount];
                        if (regCount > 0) parameterRegisters[0] = bi35cc.getRegisterC();
                        if (regCount > 1) parameterRegisters[1] = bi35cc.getRegisterD();
                        if (regCount > 2) parameterRegisters[2] = bi35cc.getRegisterE();
                        if (regCount > 3) parameterRegisters[3] = bi35cc.getRegisterF();
                        if (regCount > 4) parameterRegisters[4] = bi35cc.getRegisterG();
                    } else {
                        throw new UnsupportedOperationException("This operation is not yet supported for simplification: " + current.getOp().toString());
                    }

                    if (current.getOp().getClass().equals(InvokeOp.class)) {
                        types = graph.getVM().getClassManager().getParameterTypes(((InvokeOp) current.getOp()).getMethodDescriptor());
                    } else {
                        types = new ArrayList<>();
                        for (i = 0; i < parameterRegisters.length; i++) {
                            types.add(smaliType.substring(1));
                        }
                    }

                    i = 0;
                    for (int r : parameterRegisters) {
                        if (canMakeSimpleConstant(types.get(i))) {
                            BuilderInstruction buildConstant = ConstantBuilder.buildConstant(current.getContext().getMethodState().peekRegister(r).getValue(), types.get(i), r, graph.getDexBuilder());
                            insert(last.getAddress(), buildConstant);
                        } else if (canMakeArraySimpleConstant(types.get(i))) {
                            success = traceBackPrimitiveArray(last, current, r, types.get(i));
                        } else {
                            success = traceBackNonPrimitiveRegister(last, current, r, types.get(i));
                        }

                        if (!success) return false;
                        i++;
                    }

                    insert(last.getAddress(), instr2);
                } else if (mt == MoveOp.MoveType.REGISTER) {
                    if (!traceBackPrimitiveArray(last, current, ((TwoRegisterInstruction) instr).getRegisterB(), smaliType)) return false;
                } else throw new IllegalStateException("Cannot move exception into register where an object is expected.");
                break;

            case "IGetOp":
                BuilderInstruction22c bi = (BuilderInstruction22c) graph.getInstruction(current.getAddress());
                if (!traceBackNonPrimitiveRegister(last, current, bi.getRegisterB(), ((BuilderFieldReference) bi.getReference()).getType())) return false;
            case "SGetOp":
            case "NewInstanceOp":
            case "NewArrayOp":
                break;

            default:
                throw new UnsupportedOperationException("This operation is not yet supported for simplification: " + current.getOp().toString());
        }

        insert(last.getAddress(), instr);
        return true;
    }*/

    private boolean traceBackNonPrimitiveArrayEntry(ExecutionNode last, ExecutionNode address, int arrayRegister, int index, String smaliType) {
        ExecutionNode current = address.getParent();

        while (!(current.getOp() instanceof APutOp && current.getContext().getMethodState().peekRegister(((APutOp) current.getOp()).getIndex()).getValue() == index)) {
            current = current.getParent();
        }

        BuilderInstruction23x bi23x = (BuilderInstruction23x) graph.getInstruction(current.getAddress());
        boolean success = traceBackNonPrimitiveRegister(last, current, bi23x.getRegisterC(), smaliType);

        if (success) {
            int indexRegister = arrayRegister == 0 ? 1 : 0;
            BuilderInstruction arrayIndex = ConstantBuilder.buildConstant(index, "I", indexRegister, graph.getDexBuilder());

            insert(last.getAddress(), arrayIndex);
            insert(last.getAddress(), bi23x);
        }

        return success;
    }

    private boolean traceBackNonPrimitiveField(ExecutionNode last, ExecutionNode address, String className, String fieldName, String smaliType) {
        ExecutionNode current = address.getParent();
        String realFieldName = fieldName.substring(0, fieldName.length() - smaliType.length() - 1);

        FieldReference dst = graph.getVM().getClassManager().getField(className, realFieldName);
        while (!(current.getOp() instanceof SPutOp && dst.equals(((BuilderInstruction21c) graph.getInstruction(current.getAddress())).getReference()))) {
            current = current.getParent();
        }

        BuilderInstruction21c bi21c = (BuilderInstruction21c) graph.getInstruction(current.getAddress());

        if (!traceBackNonPrimitiveRegister(last, current, bi21c.getRegisterA(), smaliType)) return false;

        BuilderFieldReference bfr = graph.getDexBuilder().internFieldReference(graph.getVM().getClassManager().getField(className, realFieldName));
        BuilderInstruction putObject = new BuilderInstruction21c(Opcode.SPUT_OBJECT, bi21c.getRegisterA(), bfr);
        insert(last.getAddress(), putObject);
        return true;
    }

    private boolean traceBackNonPrimitiveRegister(ExecutionNode last, ExecutionNode address, int register, String smaliType) {
        ExecutionNode current = address.getParent();

        while (!(current.getOp().modifiesRegister(register) || registerInParameterList(current.getOp(), register))) {
            current = current.getParent();
        }

        boolean success = true;
        BuilderInstruction instr = graph.getInstruction(current.getAddress());
        switch (current.getOp().getClass().getSimpleName()) {
            case "InvokeOp":
                InvokeOp inv = (InvokeOp) current.getOp();
                String md = inv.getMethodDescriptor();
                List<String> types = graph.getVM().getClassManager().getParameterTypes(md);

                int i = 0;
                for (int r : inv.getParameterRegisters()) {
                    if (canMakeSimpleConstant(types.get(i))) {
                        BuilderInstruction buildConstant = ConstantBuilder.buildConstant(current.getContext().getMethodState().peekRegister(r).getValue(), types.get(i), r, graph.getDexBuilder());
                        if (buildConstant == null) return false;
                        insert(last.getAddress(), buildConstant);
                    } else if (canMakeArraySimpleConstant(types.get(i))) {
                        //success = traceBackPrimitiveArray(last, current, r, types.get(i));
                        log.info("parameter[" + i + "] " + r + " type " + types.get(i) + " directly as array");
                        log.info(current.getContext().getMethodState().toString());
                        success = substitutePrimitiveArrayRegister(last, r, current.getContext().getMethodState().peekRegister(r));
                    } else {
                        success = traceBackNonPrimitiveRegister(last, current, r, types.get(i));
                    }

                    if (!success) return false;
                    i++;
                }
                break;

            case "MoveOp":
                MoveOp.MoveType mt = ((MoveOp) current.getOp()).getMoveType();
                if (mt == MoveOp.MoveType.RESULT) {
                    current = current.getParent();
                    BuilderInstruction instr2 = graph.getInstruction(current.getAddress());

                    int[] parameterRegisters;

                    if (instr2 instanceof BuilderInstruction3rc) {
                        BuilderInstruction3rc bi3rc = (BuilderInstruction3rc) instr2;
                        parameterRegisters = new int[bi3rc.getRegisterCount()];
                        for (i = 0; i < parameterRegisters.length; i++) {
                            parameterRegisters[i] = bi3rc.getStartRegister() + i;
                        }
                    } else if (instr2 instanceof BuilderInstruction35c) {
                        BuilderInstruction35c bi35cc = (BuilderInstruction35c) instr2;
                        int regCount = bi35cc.getRegisterCount();
                        parameterRegisters = new int[regCount];
                        if (regCount > 0) parameterRegisters[0] = bi35cc.getRegisterC();
                        if (regCount > 1) parameterRegisters[1] = bi35cc.getRegisterD();
                        if (regCount > 2) parameterRegisters[2] = bi35cc.getRegisterE();
                        if (regCount > 3) parameterRegisters[3] = bi35cc.getRegisterF();
                        if (regCount > 4) parameterRegisters[4] = bi35cc.getRegisterG();
                    } else {
                        throw new UnsupportedOperationException("This operation is not yet supported for simplification: " + current.getOp().toString());
                    }

                    if (current.getOp().getClass().equals(InvokeOp.class)) {
                        types = graph.getVM().getClassManager().getParameterTypes(((InvokeOp) current.getOp()).getMethodDescriptor());
                    } else {
                        types = new ArrayList<>();
                        for (i = 0; i < parameterRegisters.length; i++) {
                            types.add(smaliType.substring(1));
                        }
                    }

                    i = 0;
                    for (int r : parameterRegisters) {
                        if (canMakeSimpleConstant(types.get(i))) {
                            BuilderInstruction buildConstant = ConstantBuilder.buildConstant(current.getContext().getMethodState().peekRegister(r).getValue(), types.get(i), r, graph.getDexBuilder());
                            if (buildConstant == null) return false;
                            insert(last.getAddress(), buildConstant);
                        } else if (canMakeArraySimpleConstant(types.get(i))) {
                            //success = traceBackPrimitiveArray(last, current, r, types.get(i));
                            success = substitutePrimitiveArrayRegister(last, r, current.getContext().getMethodState().peekRegister(r));
                        } else {
                            success = traceBackNonPrimitiveRegister(last, current, r, types.get(i));
                        }

                        if (!success) return false;
                        i++;
                    }

                    insert(last.getAddress(), instr2);
                } else if (mt == MoveOp.MoveType.REGISTER) {
                    if (!traceBackNonPrimitiveRegister(last, current, ((TwoRegisterInstruction) instr).getRegisterB(), smaliType))
                        return false;
                } else
                    throw new IllegalStateException("Cannot move exception into register where an object is expected.");
                break;

            case "AGetOp":
                BuilderInstruction23x bi23x = (BuilderInstruction23x) instr;
                traceBackNonPrimitiveArrayEntry(last, current, bi23x.getRegisterB(), bi23x.getRegisterC(), smaliType);
                break;


            case "IGetOp":
                BuilderInstruction22c bi22c = (BuilderInstruction22c) instr;
                if (!traceBackNonPrimitiveRegister(last, current, bi22c.getRegisterB(), ((BuilderFieldReference) bi22c.getReference()).getType()))
                    return false;

            case "SGetOp":
            case "NewInstanceOp":
                break;

            default:
                throw new UnsupportedOperationException("This operation is not yet supported for simplification: " + current.getOp().toString());
        }

        insert(last.getAddress(), instr);
        return true;
    }

    private boolean registerInParameterList(Op op, int register) {
        if (!(op instanceof InvokeOp)) return false;

        for (int p : ((InvokeOp) op).getParameterRegisters()) {
            if (register == p) return true;
        }

        return false;
    }

    private void insert(int addr, BuilderInstruction bi) {
        graph.insertInstruction(addr, bi);
        insertedInstructions++;
        addrDiff += bi.getCodeUnits();
    }

    public static boolean canMakeSimpleConstant(String smaliType) {
        return SmaliClassUtils.getBaseClass(smaliType).equals(smaliType)
                && (SmaliClassUtils.isPrimitiveType(smaliType)
                || "Ljava/lang/String;".equals(smaliType)
                || "Ljava/lang/Class;".equals(smaliType));
    }

    public static boolean canMakeArraySimpleConstant(String smaliType) {
        return smaliType.charAt(0) == '[' && canMakeSimpleConstant(smaliType.substring(1));
    }

    private Opcode getOpCodeVariant(String baseOp, String smaliType) {
        baseOp = baseOp.toUpperCase();

        if ("I".equals(smaliType) || "F".equals(smaliType)) return Enum.valueOf(Opcode.class, baseOp);
        if ("J".equals(smaliType) || "D".equals(smaliType)) return Enum.valueOf(Opcode.class, baseOp + "_WIDE");
        if ("S".equals(smaliType)) return Enum.valueOf(Opcode.class, baseOp + "_SHORT");
        if ("B".equals(smaliType)) return Enum.valueOf(Opcode.class, baseOp + "_BYTE");
        if ("C".equals(smaliType)) return Enum.valueOf(Opcode.class, baseOp + "_CHAR");
        if ("Z".equals(smaliType)) return Enum.valueOf(Opcode.class, baseOp + "_BOOLEAN");
        return Enum.valueOf(Opcode.class, baseOp + "_OBJECT");
    }
}