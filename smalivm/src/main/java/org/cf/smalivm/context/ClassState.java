package org.cf.smalivm.context;

import gnu.trove.set.hash.THashSet;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ClassState extends BaseState {

    private static Logger log = LoggerFactory.getLogger(ClassState.class.getSimpleName());

    private final String className;
    private final THashSet<String> fieldNameAndTypes;

    public ClassState(ExecutionContext ectx, String className, int fieldCount) {
        super(ectx, fieldCount);

        fieldNameAndTypes = new THashSet<>();
        this.className = className;
    }

    private ClassState(ClassState parent, ExecutionContext childContext, THashSet<String> fieldNameAndTypes) {
        super(childContext, fieldNameAndTypes.size());

        this.fieldNameAndTypes = fieldNameAndTypes;
        this.className = parent.className;
    }

    public ClassState(ClassState other, ExecutionContext ectx) {
        super(other, ectx);

        fieldNameAndTypes = new THashSet<>(other.fieldNameAndTypes);
        className = other.className;
    }

    public void assignField(String fieldNameAndType, Object value) {
        int register = 0;
        String heapKey = getKey(fieldNameAndType);
        String type = fieldNameAndType.split(":")[1];
        assignRegister(register, new HeapItem(value, type), heapKey);
    }

    public void assignField(String fieldNameAndType, HeapItem item) {
        int register = 0;
        String heapKey = getKey(fieldNameAndType);
        assignRegister(register, item, heapKey);
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        } else if (obj == this) {
            return true;
        } else if (obj.getClass() != getClass()) {
            return false;
        }
        ClassState other = (ClassState) obj;

        return this.toString().equals(other.toString());
    }

    public HeapItem peekField(String fieldNameAndType) {
        int register = 0;
        String heapKey = getKey(fieldNameAndType);

        HeapItem fieldItem = peekRegister(register, heapKey);
        if (fieldItem == null) {
            log.error("Undefined field: " + className + ";->" + fieldNameAndType + ". Returning unknown.");
            fieldItem = HeapItem.newUnknown(fieldNameAndType.split(":")[1]);
        }

        return fieldItem;
    }

    public THashSet<String> getFieldNames() {
        return fieldNameAndTypes;
    }

    public void pokeField(String fieldNameAndType, Object value) {
        int register = 0;
        String heapKey = getKey(fieldNameAndType);
        String type = fieldNameAndType.split(":")[1];
        pokeRegister(register, new HeapItem(value, type), heapKey);
    }

    public void pokeField(String fieldNameAndType, HeapItem item) {
        int register = 0;
        String heapKey = getKey(fieldNameAndType);
        pokeRegister(register, item, heapKey);
    }

    private String getKey(String fieldNameAndType) {
        fieldNameAndTypes.add(fieldNameAndType);
        return className + "->" + fieldNameAndType;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("Fields:\n");
        for (String fieldNameAndType : fieldNameAndTypes) {
            sb.append(fieldNameAndType).append(" = ").append(peekField(fieldNameAndType)).append('\n');
        }
        sb.setLength(sb.length() - 1);
        sb.append('\n');

        return sb.toString();
    }

    ClassState getChild(ExecutionContext childContext) {
        return new ClassState(this, childContext, fieldNameAndTypes);
    }

}
