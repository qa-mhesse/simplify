package org.cf.smalivm.context;

import gnu.trove.list.TIntList;
import gnu.trove.list.array.TIntArrayList;
import gnu.trove.map.TIntObjectMap;
import gnu.trove.map.hash.TIntObjectHashMap;
import org.cf.smalivm.SideEffect;
import org.cf.smalivm.VirtualMachine;
import org.cf.smalivm.opcode.Op;
import org.cf.smalivm.opcode.OpFactory;
import org.jf.dexlib2.Opcode;
import org.jf.dexlib2.builder.BuilderInstruction;
import org.jf.dexlib2.builder.MutableMethodImplementation;
import org.jf.dexlib2.util.ReferenceUtil;
import org.jf.dexlib2.writer.builder.BuilderMethod;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;

public class ExecutionGraph implements Iterable<ExecutionNode> {

    protected static final int TEMPLATE_NODE_INDEX = 0;
    protected static final int METHOD_ROOT_ADDRESS = 0;
    private static final Logger log = LoggerFactory.getLogger(ExecutionGraph.class.getSimpleName());
    protected final TIntObjectMap<List<ExecutionNode>> addressToNodePile;
    private final String methodDescriptor;
    private final TIntList terminatingAddresses;

    public ExecutionGraph(ExecutionGraph other) {
        methodDescriptor = other.methodDescriptor;
        addressToNodePile = new TIntObjectHashMap<List<ExecutionNode>>();
        for (int address : other.addressToNodePile.keys()) {
            List<ExecutionNode> otherNodePile = other.addressToNodePile.get(address);
            List<ExecutionNode> nodePile = new ArrayList<ExecutionNode>(otherNodePile.size());
            for (ExecutionNode otherNode : otherNodePile) {
                nodePile.add(new ExecutionNode(otherNode));
            }
            addressToNodePile.put(address, nodePile);
        }
        terminatingAddresses = other.terminatingAddresses;
    }

    public ExecutionGraph(ExecutionGraph other, boolean wrap) {
        this.addressToNodePile = other.addressToNodePile;
        this.methodDescriptor = other.methodDescriptor;
        this.terminatingAddresses = other.terminatingAddresses;
    }

    public ExecutionGraph(VirtualMachine vm, BuilderMethod method) {
        methodDescriptor = ReferenceUtil.getMethodDescriptor(method);
        MutableMethodImplementation implementation = (MutableMethodImplementation) method.getImplementation();
        List<BuilderInstruction> instructions = implementation.getInstructions();
        addressToNodePile = buildAddressToNodePile(vm, instructions);
        terminatingAddresses = buildTerminatingAddresses(instructions);
    }

    private static TIntObjectMap<List<ExecutionNode>> buildAddressToNodePile(VirtualMachine vm,
                                                                             List<BuilderInstruction> instructions) {
        OpFactory opFactory = new OpFactory(vm);
        TIntObjectMap<List<ExecutionNode>> result = new TIntObjectHashMap<List<ExecutionNode>>();
        for (BuilderInstruction instruction : instructions) {
            int address = instruction.getLocation().getCodeAddress();
            Op op = opFactory.create(instruction, address);
            ExecutionNode node = new ExecutionNode(op);

            // Most node piles will be a template node and one or more ContextNodes.
            List<ExecutionNode> nodePile = new ArrayList<ExecutionNode>(2);
            nodePile.add(node);
            result.put(address, nodePile);
        }

        return result;
    }

    private static TIntList buildTerminatingAddresses(List<BuilderInstruction> instructions) {
        TIntList result = new TIntArrayList();
        for (BuilderInstruction instruction : instructions) {
            int address = instruction.getLocation().getCodeAddress();
            /*
             * Array payload is a weird pseudo instruction. We treat it like a normal one but perhaps a better way would
             * be to make it easier for operations to execute other operations, perhaps looking up by address. This
             * would eliminate the need for MethodState.pseudoInstructionReturnAddress.
             */
            Opcode op = instruction.getOpcode();
            if (op.canContinue() || (op == Opcode.ARRAY_PAYLOAD) || op.name.startsWith("goto")) {
                continue;
            }
            result.add(address);
        }

        return result;
    }

    public void addNode(ExecutionNode node) {
        addressToNodePile.get(node.getAddress()).add(node);
    }

    public int[] getAddresses() {
        return addressToNodePile.keys();
    }

    public TIntList getConnectedTerminatingAddresses() {
        TIntList result = new TIntArrayList(1);
        for (int i = 0; i < terminatingAddresses.size(); i++) {
            int address = terminatingAddresses.get(i);
            if (wasAddressReached(address)) {
                result.add(address);
            }
        }

        return result;
    }

    public HeapItem getFieldConsensus(TIntList addressList, String fieldDescriptor) {
        String[] parts = fieldDescriptor.split("->");
        String className = parts[0];
        String fieldNameAndType = parts[1];

        return getFieldConsensus(addressList, className, fieldNameAndType);
    }

    public HeapItem getFieldConsensus(TIntList addressList, String className, String fieldNameAndType) {
        String[] parts = fieldNameAndType.split(":");
        String type = parts[1];
        Set<HeapItem> items = new HashSet<HeapItem>();
        for (int address : addressList.toArray()) {
            // If the class wasn't initialized in one path, it's unknown
            for (ExecutionNode node : getNodePile(address)) {
                if (!node.getContext().isClassInitialized(className)) {
                    return HeapItem.newUnknown(type);
                }
            }

            items.addAll(getFieldItems(address, className, fieldNameAndType));
            if (1 != items.size()) {
                // since set, size == 1 -> consensus
                if (log.isTraceEnabled()) {
                    log.trace("No conensus for " + className + "->" + fieldNameAndType + ", returning unknown");
                }

                return HeapItem.newUnknown(type);
            }
        }

        return items.toArray(new HeapItem[items.size()])[0];
    }

    public Set<String> getAllPossiblyInitializedClasses(TIntList addressList) {
        Set<String> allClasses = new HashSet<String>();
        for (int address : addressList.toArray()) {
            List<ExecutionNode> pile = getNodePile(address);
            for (ExecutionNode node : pile) {
                allClasses.addAll(node.getContext().getInitializedClasses());
            }
        }

        return allClasses;
    }

    public Set<HeapItem> getFieldItems(int address, String className, String fieldNameAndType) {
        List<ExecutionNode> nodePile = getNodePile(address);
        Set<HeapItem> items = new HashSet<HeapItem>(nodePile.size());
        for (ExecutionNode node : nodePile) {
            ClassState cState = node.getContext().peekClassState(className);
            HeapItem item = cState.peekField(fieldNameAndType);
            items.add(item);
        }

        return items;
    }

    public String getMethodDescriptor() {
        return methodDescriptor;
    }

    public int getNodeCount() {
        int totalSize = addressToNodePile.size();
        int templateCount = addressToNodePile.keys().length;

        return totalSize - templateCount;
    }

    public List<ExecutionNode> getNodePile(int address) {
        List<ExecutionNode> result = addressToNodePile.get(address);
        result = result.subList(1, result.size());

        return result;
    }

    public Op getOp(int address) {
        List<ExecutionNode> pile = addressToNodePile.get(address);
        // same pile implies same op
        ExecutionNode bottomNode = pile.get(TEMPLATE_NODE_INDEX);

        return bottomNode.getOp();
    }

    public HeapItem getRegisterConsensus(int address, int register) {
        TIntList addresses = new TIntArrayList(new int[]{address});

        return getRegisterConsensus(addresses, register);
    }

    public Object getRegisterConsensusValue(int address, int register) {
        HeapItem item = getRegisterConsensus(address, register);
        if (null == item) {
            return null;
        }

        return item.getValue();
    }

    public SideEffect.Level getHighestClassSideEffectLevel(String className) {
        TIntList addressList = getConnectedTerminatingAddresses();
        SideEffect.Level result = SideEffect.Level.NONE;
        for (int address : addressList.toArray()) {
            List<ExecutionNode> pile = getNodePile(address);
            for (ExecutionNode node : pile) {
                SideEffect.Level level = node.getContext().getClassSideEffectLevel(className);
                if (level == null) {
                    // Maybe the class wasn't initialized.
                    continue;
                }
                switch (level) {
                    case STRONG:
                        return level;
                    case WEAK:
                        result = level;
                        break;
                    case NONE:
                        break;
                }
            }
        }

        return result;
    }

    public Object getRegisterConsensusValue(TIntList addressList, int register) {
        HeapItem item = getRegisterConsensus(addressList, register);
        if (null == item) {
            return null;
        }

        return item.getValue();
    }

    public HeapItem getRegisterConsensus(TIntList addressList, int register) {
        Set<HeapItem> items = new HashSet<HeapItem>();
        for (int address : addressList.toArray()) {
            items.addAll(getRegisterItems(address, register));
            if (items.size() != 1) {
                if (log.isTraceEnabled()) {
                    log.trace("No conensus for register #" + register + ", returning unknown");
                }
                HeapItem item = items.toArray(new HeapItem[items.size()])[0];

                return HeapItem.newUnknown(item.getType());
            }
        }
        assert items.size() == 1;

        return items.toArray(new HeapItem[1])[0];
    }

    public Set<HeapItem> getRegisterItems(int address, int register) {
        List<ExecutionNode> nodePile = getNodePile(address);
        Set<HeapItem> items = new HashSet<HeapItem>(nodePile.size());
        for (ExecutionNode node : nodePile) {
            MethodState mState = node.getContext().getMethodState();
            HeapItem item = mState.peekRegister(register);
            items.add(item);
        }

        return items;
    }

    public ExecutionNode getRoot() {
        List<ExecutionNode> pile = addressToNodePile.get(METHOD_ROOT_ADDRESS);
        // Return node with initialized context if available.
        if (pile.size() > 1) {
            return pile.get(1);
        } else {
            return pile.get(TEMPLATE_NODE_INDEX);
        }
    }

    public SideEffect.Level getHighestSideEffectLevel() {
        SideEffect.Level result = getHighestMethodSideEffectLevel();
        if (result == SideEffect.Level.STRONG) {
            return result;
        }

        TIntList addressList = getConnectedTerminatingAddresses();
        Set<String> allClasses = getAllPossiblyInitializedClasses(addressList);
        for (String className : allClasses) {
            SideEffect.Level level = getHighestClassSideEffectLevel(className);
            switch (level) {
                case STRONG:
                    return level;
                case WEAK:
                    result = level;
                    break;
                case NONE:
                    break;
            }
        }

        return result;
    }

    public SideEffect.Level getHighestMethodSideEffectLevel() {
        SideEffect.Level result = SideEffect.Level.NONE;
        for (ExecutionNode node : this) {
            Op op = node.getOp();
            SideEffect.Level level = op.sideEffectLevel();
            switch (level) {
                case STRONG:
                    return level;
                case WEAK:
                    result = level;
                    break;
                case NONE:
                    break;
            }
        }

        return result;
    }

    public ExecutionNode getTemplateNode(int address) {
        return addressToNodePile.get(address).get(TEMPLATE_NODE_INDEX);
    }

    public HeapItem getTerminatingFieldConsensus(String fieldDescriptor) {
        Map<String, HeapItem> items = getTerminatingFieldConsensus(new String[]{fieldDescriptor});

        return items.get(fieldDescriptor);
    }

    public Map<String, HeapItem> getTerminatingFieldConsensus(String[] fieldDescriptors) {
        TIntList addresses = getConnectedTerminatingAddresses();
        Map<String, HeapItem> result = new HashMap<String, HeapItem>(fieldDescriptors.length);
        for (String fieldDescriptor : fieldDescriptors) {
            HeapItem item = getFieldConsensus(addresses, fieldDescriptor);
            result.put(fieldDescriptor, item);
        }

        return result;
    }

    public HeapItem getTerminatingRegisterConsensus(int register) {
        Map<Integer, HeapItem> items = getTerminatingRegisterConsensus(new int[]{register});

        return items.get(register);
    }

    public Map<Integer, HeapItem> getTerminatingRegisterConsensus(int[] registers) {
        TIntList addresses = getConnectedTerminatingAddresses();
        Map<Integer, HeapItem> result = new HashMap<Integer, HeapItem>(registers.length);
        for (int register : registers) {
            HeapItem item = getRegisterConsensus(addresses, register);
            result.put(register, item);
        }

        return result;
    }

    @Override
    public Iterator<ExecutionNode> iterator() {
        return new ExecutionGraphIterator(this);
    }

    public String toGraph() {
        return getRoot().toGraph();
    }

    public boolean wasAddressReached(int address) {
        if (METHOD_ROOT_ADDRESS == address) {
            // Root is always reachable
            return true;
        }

        // If this address was reached during execution there will be clones in the pile.
        List<ExecutionNode> nodePile = addressToNodePile.get(address);
        if ((nodePile == null) || (1 > nodePile.size())) {
            log.warn("Node pile @" + address + " has no template node.");
            return false;
        }

        return nodePile.size() > 1;
    }

}
