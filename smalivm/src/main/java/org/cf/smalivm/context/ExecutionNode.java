package org.cf.smalivm.context;

import org.cf.smalivm.VirtualException;
import org.cf.smalivm.opcode.ExecutionContextOp;
import org.cf.smalivm.opcode.MethodStateOp;
import org.cf.smalivm.opcode.Op;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class ExecutionNode {

    private final static String DOT = "[^a-zA-Z\200-\377_0-9\\s\\p{Punct}]";

    private static Logger log = LoggerFactory.getLogger(ExecutionNode.class.getSimpleName());

    private final List<ExecutionNode> children;
    private final Op op;
    private ExecutionContext ectx;
    private ExecutionNode parent;
    private int[] childAddresses;
    private Set<VirtualException> exceptions;

    public ExecutionNode(ExecutionNode other) {
        op = other.op;
        children = new ArrayList<>(other.getChildren());
    }

    public ExecutionNode(Op op) {
        this.op = op;
        children = new ArrayList<>(op.getChildren().length);
    }

    public void clearChildAddresses() {
        setChildAddresses();
    }

    public void clearExceptions() {
        exceptions = new HashSet<>();
    }

    public void execute() {
        ExecutionContext ectx = getContext();
        if (log.isDebugEnabled()) {
            log.debug("HANDLING @" + op.getAddress() + ": " + op + "\nContext before:\n" + ectx);
        }

        if (op instanceof MethodStateOp) {
            MethodState mState = ectx.getMethodState();
            ((MethodStateOp) op).execute(this, mState);
        } else if (op instanceof ExecutionContextOp) {
            ((ExecutionContextOp) op).execute(this, ectx);
        }

        if (log.isDebugEnabled()) {
            log.debug("Context after:\n" + ectx);
        }

        // If op didn't set children or exceptions specifically, pull in template values.
        if (childAddresses == null) {
            setChildAddresses(op.getChildren());
        }

        if (exceptions == null) {
            setExceptions(op.getExceptions());
        }
    }

    public int getAddress() {
        return op.getAddress();
    }

    public int getCallDepth() {
        return ectx.getCallDepth();
    }

    public int[] getChildAddresses() {
        return childAddresses;
    }

    public void setChildAddresses(int... childAddresses) {
        this.childAddresses = childAddresses;
    }

    public List<ExecutionNode> getChildren() {
        return children;
    }

    public ExecutionContext getContext() {
        return ectx;
    }

    public void setContext(ExecutionContext ectx) {
        this.ectx = ectx;
    }

    public Set<VirtualException> getExceptions() {
        return exceptions;
    }

    public void setExceptions(Set<VirtualException> exceptions) {
        this.exceptions = exceptions;
    }

    public Op getOp() {
        return op;
    }

    public ExecutionNode getParent() {
        return parent;
    }

    public void setParent(ExecutionNode parent) {
        // All nodes will have [0,1] parents since a node represents both an instruction and a context, or vm state.
        // Each execution of an instruction will have a new state.
        this.parent = parent;
        if (parent != null) {
            parent.addChild(this);
        }
    }

    public boolean mayThrowException() {
        return exceptions != null && exceptions.size() > 0;
    }

    public void removeChild(ExecutionNode child) {
        children.remove(child);
    }

    public void replaceChild(ExecutionNode oldChild, ExecutionNode newChild) {
        int index = children.indexOf(oldChild);
        // http://stream1.gifsoup.com/view/773318/not-the-father-dance-o.gif
        assert index >= 0;
        children.remove(index);
        newChild.setParent(this);
    }

    public void setException(VirtualException exception) {
        exceptions = new HashSet<VirtualException>();
        exceptions.add(exception);
    }

    public void setMethodState(MethodState mState) {
        ectx.setMethodState(mState);
    }

    public ExecutionNode spawnChild(Op childOp) {
        ExecutionNode child = new ExecutionNode(childOp);
        child.setContext(ectx.spawnChild());
        child.setParent(this);

        return child;
    }

    public String toGraph() {
        List<ExecutionNode> visitedNodes = new ArrayList<ExecutionNode>();
        StringBuilder sb = new StringBuilder("digraph {\n");
        getGraph(sb, visitedNodes);
        sb.append("}");

        return sb.toString();
    }

    @Override
    public String toString() {
        return op.toString();
    }

    private void addChild(ExecutionNode child) {
        children.add(child);
    }

    private void getGraph(StringBuilder sb, List<ExecutionNode> visitedNodes) {
        if (visitedNodes.contains(this)) {
            return;
        }
        visitedNodes.add(this);

        ExecutionContext parentExecutionContext = getContext();
        MethodState parentMethodState = parentExecutionContext.getMethodState();
        for (ExecutionNode child : getChildren()) {
            String op = toString().replaceAll(DOT, "?").replace("\"", "\\\"");
            String ctx = parentMethodState.toString().replaceAll(DOT, "?").replace("\"", "\\\"").trim();
            sb.append('"').append(getAddress()).append('\n').append(op).append('\n').append(ctx).append('"');

            sb.append(" -> ");

            ExecutionContext childExecutionContext = child.getContext();
            MethodState childMethodState = childExecutionContext.getMethodState();
            op = toString().replaceAll(DOT, "?").replace("\"", "\\\"");
            ctx = childMethodState.toString().replaceAll(DOT, "?").replace("\"", "\\\"").trim();
            sb.append('"').append(getAddress()).append('\n').append(op).append('\n').append(ctx).append('"');
            sb.append('\n');

            child.getGraph(sb, visitedNodes);
        }
    }

}
