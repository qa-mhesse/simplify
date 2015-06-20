package org.cf.smalivm.context;

import com.rits.cloning.Cloner;
import org.apache.commons.lang3.builder.EqualsBuilder;
import org.apache.commons.lang3.builder.HashCodeBuilder;
import org.cf.smalivm.type.UnknownValue;
import org.cf.util.ImmutableUtils;
import org.cf.util.SmaliClassUtils;
import org.cf.util.Utils;

import java.lang.reflect.Array;
import java.util.Arrays;

public class HeapItem {

    private static final Cloner cloner = new Cloner();

    private Object value;
    private String type;

    public HeapItem(Object value, String type) {
        this.value = value;
        this.type = type;
    }

    HeapItem(HeapItem other) {
        value = cloner.deepClone(other.getValue());
        type = other.getType();
    }

    public static HeapItem newUnknown(String type) {
        return new HeapItem(new UnknownValue(), type);
    }

    public Object getValue() {
        return value;
    }

    public double getDoubleValue() {
        return Utils.getDoubleValue(getValue());
    }

    public int getIntegerValue() {
        return Utils.getIntegerValue(getValue());
    }

    public long getLongValue() {
        return Utils.getLongValue(getValue());
    }

    public float getFloatValue() {
        return Utils.getFloatValue(getValue());
    }

    public String getType() {
        return type;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (obj == this) {
            return true;
        }
        if (obj.getClass() != getClass()) {
            return false;
        }
        HeapItem rhs = (HeapItem) obj;

        return new EqualsBuilder().append(getType(), rhs.getType()).append(getValue(), rhs.getValue()).isEquals();
    }

    @Override
    public int hashCode() {
        return new HashCodeBuilder(113, 21).append(getType()).append(getValue()).hashCode();
    }

    public boolean valueIdentity(HeapItem other) {
        return getValue() == other.getValue();
    }

    public boolean isPrimitive() {
        return SmaliClassUtils.isPrimitiveType(getType());
    }

    public boolean isPrimitiveOrWrapper() {
        return SmaliClassUtils.isPrimitiveOrWrapperType(getType());
    }

    public boolean isPrimitiveWrapper() {
        return SmaliClassUtils.isWrapperType(getType());
    }

    public boolean isUnknown() {
        return getValue() instanceof UnknownValue;
    }

    public boolean isImmutable() {
        return ImmutableUtils.isImmutableClass(getType());
    }

    public String getUnboxedValueType() {
        String unboxedType = SmaliClassUtils.smaliWrapperToSmaliPrimitive(getType());
        if (null == unboxedType) {
            unboxedType = type;
        }

        return unboxedType;
    }

    @Override
    public String toString() {
        Object value = getValue();
        StringBuilder sb = new StringBuilder("type=");
        sb.append(getType()).append(", value=");
        if (value == null) {
            sb.append("null");
        } else {
            if (value.getClass().isArray()) {
                Object[] objArray;
                if (value.getClass().getComponentType().isPrimitive()) {
                    int arrayLen = Array.getLength(value);
                    objArray = new Object[arrayLen];
                    for (int i = 0; i < arrayLen; i++) {
                        objArray[i] = Array.get(value, i);
                    }
                } else {
                    objArray = (Object[]) value;
                }
                String arrayString = Arrays.deepToString(objArray);
                sb.append(arrayString);
            } else {
                sb.append(value);
            }
        }

        return sb.toString();
    }

}
