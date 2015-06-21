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
import org.jf.dexlib2.Opcode;
import org.jf.dexlib2.builder.BuilderInstruction;
import org.jf.dexlib2.builder.instruction.*;
import org.jf.dexlib2.iface.reference.MethodReference;
import org.jf.dexlib2.writer.builder.BuilderFieldReference;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class StaticFieldSimplificationStrategy implements OptimizationStrategy {
    private static final Logger log = LoggerFactory.getLogger(StaticFieldSimplificationStrategy.class.getSimpleName());
    private final MethodBackedGraph mbgraph;
    private int simplificationCount;
    private int addrDiff;
    private int insertedInstructions;

    public StaticFieldSimplificationStrategy(MethodBackedGraph mbgraph) {
        this.mbgraph = mbgraph;
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
        if (!mbgraph.getMethodDescriptor().endsWith("<clinit>()V")) return false;

        // obtain last instruction
        ExecutionNode last = mbgraph.getRoot();
        while (last.getChildren().size() > 0) {
            last = last.getChildren().get(0);
        }
        ExecutionNode node = last.getParent();

        ExecutionContext c = node.getContext();
        Set<String> initClasses = node.getContext().getInitializedClasses();

        int nrFields = 0;
        for (String className : initClasses) {
            if (!mbgraph.getMethodDescriptor().startsWith(className)) continue;
            ClassState classState = c.peekClassState(className);
            nrFields = classState.getFieldNames().size();

            for (String fieldName : classState.getFieldNames()) {
                HeapItem field = classState.peekField(fieldName);
                Object fieldValue = field.getValue();

                if (!(fieldValue instanceof UnknownValue || fieldValue instanceof UninitializedInstance)) {
                    if (isPrimitive(fieldValue)) {
                        simplificationCount += substitutePrimitiveField(last, className, fieldName, field);
                    } else if (fieldValue.getClass().isArray()) {
                        simplificationCount += substituteArrayField(last, className, fieldName, field);
                    } else {
                        simplificationCount += substituteNonPrimitiveField(last, className, fieldName, field);
                    }
                } else {
                    simplificationCount++;
                }
            }
        }

        if (simplificationCount == nrFields) {
            removeUnnecessaryInstructions(last);
        }

        return addrDiff > 0;
    }

    private void removeUnnecessaryInstructions(ExecutionNode last) {
        // remove all switch / switch-payload instructions first
        while (true) {
            TIntList addresses = new TIntArrayList(mbgraph.getAddresses());
            addresses.sort();
            int[] addrs = addresses.toArray();

            boolean removedInstruction = false;
            for (int i = 0; i < addrs.length && !removedInstruction; i++) {
                Op o = mbgraph.getTemplateNode(addrs[i]).getOp();
                if (o instanceof SwitchOp || o instanceof SwitchPayloadOp) {
                    try {
                        mbgraph.removeInstruction(addrs[i]);
                        removedInstruction = true;

                        if (log.isInfoEnabled()) {
                            log.info("removed " + o.toString() + " @" + addrs[i]);
                        }
                    } catch (IndexOutOfBoundsException e) {
                        log.warn("tried to remove switch instruction which isn't there: " + o.toString() + " @" + addrs[i]);
                    }
                }
            }
            if (!removedInstruction) break;
        }

        // then remove all goto instructions
        /*while (true) {
            TIntList addresses = new TIntArrayList(mbgraph.getAddresses());
            addresses.sort();
            int[] addrs = addresses.toArray();

            boolean removedInstruction = false;
            for (int i = 0; i < addrs.length && !removedInstruction; i++) {
                Op o = mbgraph.getTemplateNode(addrs[i]).getOp();
                if (o instanceof GotoOp) {
                    try {
                        mbgraph.removeInstruction(addrs[i]);
                        removedInstruction = true;

                        if (log.isInfoEnabled()) {
                            log.info("removed " + o.toString() + " @" + addrs[i]);
                        }
                    } catch (IndexOutOfBoundsException e) {
                        log.warn("tried to remove goto instruction which isn't there: " + o.toString() + " @" + addrs[i]);
                    }
                }
            }
            if (!removedInstruction) break;
        }

        // thirdly remove all if instructions
        while (true) {
            TIntList addresses = new TIntArrayList(mbgraph.getAddresses());
            addresses.sort();
            int[] addrs = addresses.toArray();

            boolean removedInstruction = false;
            for (int i = 0; i < addrs.length && !removedInstruction; i++) {
                Op o = mbgraph.getTemplateNode(addrs[i]).getOp();
                if (o instanceof IfOp) {
                    try {
                        mbgraph.removeInstruction(addrs[i]);
                        removedInstruction = true;

                        if (log.isInfoEnabled()) {
                            log.info("removed " + o.toString() + " @" + addrs[i]);
                        }
                    } catch (IndexOutOfBoundsException e) {
                        log.warn("tried to remove if instruction which isn't there: " + o.toString() + " @" + addrs[i]);
                    }
                }
            }
            if (!removedInstruction) break;
        }*/

        // remove all other instructions that we don't need
        while (true) {
            TIntList addresses = new TIntArrayList(mbgraph.getAddresses());
            addresses.sort();
            int[] addrs = addresses.toArray();

            boolean removedInstruction = false;

            // recalculate addresses we don't want to remove
            ExecutionNode first = last;
            int[] protect = new int[insertedInstructions];
            for (int i = 0; i < insertedInstructions; i++) {
                protect[i] = first.getAddress();
                first = first.getParent();
            }

            for (int i = 0; i < addrs.length && !removedInstruction; i++) {
                boolean canBeRemoved = true;
                for (int j = 0; j < insertedInstructions; j++) {
                    if (addrs[i] == protect[j]) canBeRemoved = false;
                }

                if (canBeRemoved) {
                    try {
                        String op = mbgraph.getTemplateNode(addrs[i]).getOp().toString();
                        mbgraph.removeInstruction(addrs[i]);
                        removedInstruction = true;

                        if (log.isInfoEnabled()) {
                            log.info("removed " + op + " @" + addrs[i]);
                        }
                    } catch (IndexOutOfBoundsException | NullPointerException e) {
                        log.warn("tried to remove instruction which isn't there: @" + addrs[i]);
                    }
                }
            }
            if (!removedInstruction) break;
        }

        System.out.println(mbgraph.toSmali());
    }

    private int substitutePrimitiveField(ExecutionNode last, String className, String fieldName, HeapItem field) {
        Object fieldValue = field.getValue();

        BuilderInstruction createStatic = ConstantBuilder.buildConstant(fieldValue, field.getType(), 0, mbgraph.getDexBuilder());
        String realFieldName = fieldName.substring(0, fieldName.length() - field.getType().length() - 1);
        BuilderFieldReference bfr = mbgraph.getDexBuilder().internFieldReference(mbgraph.getVM().getClassManager().getField(className, realFieldName));
        BuilderInstruction assignStatic = new BuilderInstruction21c((isWide(fieldValue) ? Opcode.SPUT_WIDE : Opcode.SPUT), 0, bfr);

        insert(last.getAddress(), createStatic);
        insert(last.getAddress(), assignStatic);

        simplificationCount++;
        if (log.isInfoEnabled()) {
            log.info("Directly set primitive static field " + fieldName + " to \"" + fieldValue + "\"");
        }

        return 1;
    }

    private int substituteArrayField(ExecutionNode lastAddress, String className, String fieldName, HeapItem field) {
        int i = 0;

        String realFieldName = fieldName.substring(0, fieldName.length() - field.getType().length() - 1);
        BuilderFieldReference bfr = mbgraph.getDexBuilder().internFieldReference(mbgraph.getVM().getClassManager().getField(className, realFieldName));
        BuilderInstruction arraySize = ConstantBuilder.buildConstant(((Object[]) field.getValue()).length, "I", 1, mbgraph.getDexBuilder());
        BuilderInstruction newArray = new BuilderInstruction22c(Opcode.NEW_ARRAY, 0, 1, mbgraph.getDexBuilder().internTypeReference(field.getType()));
        insert(lastAddress.getAddress(), arraySize);
        insert(lastAddress.getAddress(), newArray);

        int changes = 0;

        for (Object o : (Object[]) field.getValue()) {
            if (o instanceof UnknownValue) continue;
            else if (o.getClass().isPrimitive() || o.getClass().equals(String.class)) {
                BuilderInstruction arrayIndex = ConstantBuilder.buildConstant(i, "I", 1, mbgraph.getDexBuilder());
                BuilderInstruction createStatic = ConstantBuilder.buildConstant(o, field.getType().substring(1), 2, mbgraph.getDexBuilder());
                BuilderInstruction assignStatic = new BuilderInstruction23x((isWide(o) ? Opcode.APUT_WIDE : Opcode.APUT), 2, 0, 1);

                insert(lastAddress.getAddress(), arrayIndex);
                insert(lastAddress.getAddress(), createStatic);
                insert(lastAddress.getAddress(), assignStatic);

                changes++;
                if (log.isInfoEnabled()) {
                    log.info("Directly set primitive entry #" + i + " of array field " + fieldName + " to \"" + o + "\"");
                }
            } else {
                // TODO: set field to value
                System.out.println("  [" + i + "]: object (" + o.getClass() + ") = " + o);
            }
            i++;
        }

        if (changes > 0) {
            BuilderInstruction putArray = new BuilderInstruction21c(Opcode.SPUT_OBJECT, 0, bfr);
            insert(lastAddress.getAddress(), putArray);
        } else {
            mbgraph.removeInstruction(lastAddress.getAddress());
            mbgraph.removeInstruction(lastAddress.getAddress());
            insertedInstructions -= 2;
        }

        return changes > 1 ? 1 : 0;
    }

    private int substituteNonPrimitiveField(ExecutionNode last, String className, String fieldName, HeapItem field) {
        traceBackNonPrimitiveField(last, last, className, fieldName, field.getType());
        return 1;
    }

    private void traceBackNonPrimitiveField(ExecutionNode last, ExecutionNode address, String className, String fieldName, String fieldType) {
        ExecutionNode parent = address.getParent();

        while (!(parent.getOp() instanceof SPutOp && parent.getOp().toString().endsWith(className + "->" + fieldName))) {
            parent = parent.getParent();
        }

        int offset = parent.getOp().toString().length() - className.length() - fieldName.length() - 5;
        int register = Integer.parseInt(parent.getOp().toString().substring(offset, offset + 1));

        traceBackNonPrimitiveRegister(last, parent, register, fieldType);

        String realFieldName = fieldName.substring(0, fieldName.length() - fieldType.length() - 1);
        BuilderFieldReference bfr = mbgraph.getDexBuilder().internFieldReference(mbgraph.getVM().getClassManager().getField(className, realFieldName));
        BuilderInstruction putObject = new BuilderInstruction21c(Opcode.SPUT_OBJECT, register, bfr);
        insert(last.getAddress(), putObject);
    }

    private void traceBackNonPrimitiveRegister(ExecutionNode last, ExecutionNode address, int register, String type) {
        ExecutionNode parent = address.getParent();

        while (!(parent.getOp().modifiesRegister(register) || registerInParameterList(parent.getOp(), register))) {
            parent = parent.getParent();
        }

        switch (parent.getOp().getClass().getSimpleName()) {
            case "InvokeOp":
                InvokeOp inv = (InvokeOp) parent.getOp();
                String md = inv.getMethodDescriptor();
                List<String> types = mbgraph.getVM().getClassManager().getParameterTypes(md);

                int i = 0;
                for (int r : inv.getParameterRegisters()) {
                    BuilderInstruction buildConstant = ConstantBuilder.buildConstant(parent.getContext().getMethodState().peekRegister(r).getValue(), types.get(i), r, mbgraph.getDexBuilder());
                    if (buildConstant == null) {
                        traceBackNonPrimitiveRegister(last, parent, r, types.get(i));
                    } else insert(last.getAddress(), buildConstant);
                    i++;
                }

                BuilderInstruction invoke;
                MethodReference mr = mbgraph.getDexBuilder().internMethodReference(mbgraph.getVM().getClassManager().getMethod(md));
                if (parent.getOp().toString().split(" ")[0].contains("/range")) {
                    invoke = new BuilderInstruction3rc(getInvokeOpCode(inv.toString()), inv.getParameterRegisters()[0], inv.getParameterRegisters().length, mr);
                } else {
                    int[] regs = new int[5];
                    System.arraycopy(inv.getParameterRegisters(), 0, regs, 0, i);
                    invoke = new BuilderInstruction35c(getInvokeOpCode(inv.toString()), i, regs[0], regs[1], regs[2], regs[3], regs[4], mr);
                }
                insert(last.getAddress(), invoke);
                break;

            case "MoveOp":
                // TODO: implement support
                throw new UnsupportedOperationException("Simplification of moving objects not supported.");
                /*MoveOp m = (MoveOp) parent.getOp();
                if (m.toString().startsWith("move-result-object")) {

                } else {

                }
                break;*/

            case "AGetOp":
                // TODO: implement support
                throw new UnsupportedOperationException("Simplification of fetching objects from arrays not supported.");
                //break;

            case "IGetOp":
                IGetOp iop = (IGetOp) parent.getOp();
                String[] fd = iop.getFieldDescriptor().split("->");
                if (fd.length > 2)
                    throw new UnsupportedOperationException("Field or class name contains \"->\": " + iop.getFieldDescriptor());
                if (fd[1].split(":").length > 2)
                    throw new UnsupportedOperationException("Field name contains ':'" + iop.getFieldDescriptor());
                String[] field = fd[1].split(":");

                traceBackNonPrimitiveRegister(last, parent, ((IGetOp) parent.getOp()).getInstanceRegister(), field[1]);

                BuilderFieldReference bfr = mbgraph.getDexBuilder().internFieldReference(mbgraph.getVM().getClassManager().getField(fd[0], field[0]));
                BuilderInstruction getObject = new BuilderInstruction21c(Opcode.IGET_OBJECT, register, bfr);
                insert(last.getAddress(), getObject);
                break;

            case "SGetOp":
                SGetOp sop = (SGetOp) parent.getOp();
                fd = sop.getFieldDescriptor().split("->");
                if (fd.length > 2)
                    throw new UnsupportedOperationException("Field or class name contains \"->\"" + sop.getFieldDescriptor());
                if (fd[1].split(":").length > 2)
                    throw new UnsupportedOperationException("Field name contains ':'" + sop.getFieldDescriptor());
                fd[1] = fd[1].split(":")[0];

                bfr = mbgraph.getDexBuilder().internFieldReference(mbgraph.getVM().getClassManager().getField(fd[0], fd[1]));
                getObject = new BuilderInstruction21c(Opcode.SGET_OBJECT, register, bfr);
                insert(last.getAddress(), getObject);
                break;

            case "NewInstanceOp":
                insert(last.getAddress(), new BuilderInstruction21c(Opcode.NEW_INSTANCE, register, mbgraph.getDexBuilder().internTypeReference(type)));
                break;
        }
    }

    private boolean isPrimitive(Object o) {
        return o.getClass().isPrimitive() || o.getClass().equals(String.class);
    }

    private boolean isWide(Object o) {
        return o.getClass().equals(Long.class) || o.getClass().equals(Double.class);
    }

    private boolean registerInParameterList(Op op, int register) {
        if (!(op instanceof InvokeOp)) return false;

        for (int p : ((InvokeOp) op).getParameterRegisters()) {
            if (register == p) return true;
        }

        return false;
    }

    private Opcode getInvokeOpCode(String op) {
        String s = op.split(" ")[0];
        if (s.endsWith("/range")) {
            if (s.contains("virtual")) return Opcode.INVOKE_VIRTUAL_RANGE;
            if (s.contains("super")) return Opcode.INVOKE_SUPER_RANGE;
            if (s.contains("direct")) return Opcode.INVOKE_DIRECT_RANGE;
            if (s.contains("static")) return Opcode.INVOKE_STATIC_RANGE;
            if (s.contains("interface")) return Opcode.INVOKE_INTERFACE_RANGE;
        } else {
            if (s.endsWith("virtual")) return Opcode.INVOKE_VIRTUAL;
            if (s.endsWith("super")) return Opcode.INVOKE_SUPER;
            if (s.endsWith("direct")) return Opcode.INVOKE_DIRECT;
            if (s.endsWith("static")) return Opcode.INVOKE_STATIC;
            if (s.endsWith("interface")) return Opcode.INVOKE_INTERFACE;
        }
        throw new UnsupportedOperationException("Illegal invoke operation " + op);
    }

    private void insert(int addr, BuilderInstruction bi) {
        mbgraph.insertInstruction(addr, bi);
        insertedInstructions++;
        addrDiff += bi.getCodeUnits();
    }
}