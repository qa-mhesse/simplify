package org.cf.util;

import gnu.trove.list.TIntList;
import gnu.trove.list.array.TIntArrayList;
import gnu.trove.map.TIntObjectMap;
import org.apache.commons.lang3.ClassUtils;
import org.cf.smalivm.context.HeapItem;
import org.cf.smalivm.type.*;
import org.jf.dexlib2.builder.BuilderInstruction;
import org.jf.dexlib2.builder.BuilderOffsetInstruction;
import org.jf.dexlib2.builder.instruction.*;
import org.jf.dexlib2.iface.instruction.NarrowLiteralInstruction;
import org.jf.dexlib2.iface.instruction.OneRegisterInstruction;
import org.jf.dexlib2.iface.instruction.ReferenceInstruction;
import org.jf.dexlib2.iface.instruction.TwoRegisterInstruction;
import org.jf.dexlib2.writer.builder.BuilderTypeList;
import org.jf.dexlib2.writer.builder.BuilderTypeReference;

import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Utils {

    private static final Pattern ParameterIndividuator = Pattern.compile("(\\[*(?:[BCDFIJSZ]|L[^;]+;))");
    private static final Pattern ParameterIsolator = Pattern.compile("\\([^\\)]+\\)");

    public static String getArrayDimensionString(Object array) {
        if (!array.getClass().isArray()) {
            return "";
        }

        StringBuilder sb = new StringBuilder();
        Object current = array;
        int len = Array.getLength(current);
        sb.append('[').append(len).append(']');

        while (len > 0) {
            current = Array.get(current, 0);
            if ((current == null) || !current.getClass().isArray()) {
                break;
            }
            len = Array.getLength(current);
            sb.append('[').append(len).append(']');
        }

        return sb.toString();
    }

    public static Object buildArray(String typeReference, int length, boolean useLocalClass)
            throws ClassNotFoundException {
        String baseClassName = SmaliClassUtils.getBaseClass(typeReference);
        String javaClassName;
        if (useLocalClass) {
            javaClassName = LocalInstance.class.getName();
        } else {
            javaClassName = SmaliClassUtils.smaliClassToJava(baseClassName);
        }

        int dimensionCount = getDimensionCount(typeReference) - 1;
        String classNameWithDimensions = addDimensionsToClassName(javaClassName, dimensionCount);
        Class<?> klazz = ClassUtils.getClass(classNameWithDimensions);

        return Array.newInstance(klazz, length);
    }

    public static int getDimensionCount(String typeReference) {
        // A fancy word for "number of dimensions" is "rank".
        // But getRank() only makes sense if you're a total nerd.
        String baseClassName = typeReference.replace("[", "");

        return typeReference.length() - baseClassName.length();
    }

    public static List<String> getParameterTypes(String methodDescriptor) {
        // Only use this for non-local methods.
        // For local methods, there's VirtualMachine#getParameterTypes.
        Matcher m = ParameterIsolator.matcher(methodDescriptor);
        List<String> result = new ArrayList<>();
        if (m.find()) {
            String params = m.group();
            m = ParameterIndividuator.matcher(params);
            while (m.find()) {
                result.add(m.group());
            }
        }

        return result;
    }

    public static <E> Collection<E> makeCollection(Iterable<E> iter) {
        Collection<E> list = new ArrayList<>();
        for (E item : iter) {
            list.add(item);
        }
        return list;
    }

    public static <T> void shiftIntegerMapKeys(int startKey, int shift, TIntObjectMap<T> intToObject) {
        if (shift == 0) {
            return;
        }

        TIntList keysToShift = new TIntArrayList(intToObject.keys());
        // Exclude anything before and including startKey
        for (int currentKey : keysToShift.toArray()) {
            if (currentKey <= startKey) {
                keysToShift.remove(currentKey);
            }
        }

        if (keysToShift.size() == 0) {
            intToObject.remove(startKey);
        }

        keysToShift.sort();
        if (shift > 0) {
            // Shifting keys up, so start at the end to avoid overwriting keys.
            keysToShift.reverse();
        }

        for (int currentKey : keysToShift.toArray()) {
            T obj = intToObject.get(currentKey);
            intToObject.remove(currentKey);
            intToObject.put(currentKey + shift, obj);
        }
    }

    private static String addDimensionsToClassName(String className, int dimensionCount) {
        // Apache's ClassUtils.forName expects someArray[] instead of [someArray
        StringBuilder sb = new StringBuilder(className);
        for (int i = 0; i < dimensionCount; i++) {
            sb.append("[]");
        }

        return sb.toString();
    }

    public static int getRegisterSize(List<String> typeNames) {
        int size = 0;
        for (String typeName : typeNames) {
            size += getRegisterSize(typeName);
        }

        return size;
    }

    public static int getRegisterSize(String typeName) {
        return "J".equals(typeName) || "D".equals(typeName) ? 2 : 1;
    }

    public static int getRegisterSize(Class<?>[] parameterTypes) {
        return getRegisterSize(SmaliClassUtils.javaClassToSmali(parameterTypes));
    }

    public static List<String> builderTypeListToStringList(BuilderTypeList typeList) {
        List<String> typeNames = new LinkedList<>();
        for (BuilderTypeReference type : typeList) {
            typeNames.add(type.getType());
        }

        return typeNames;
    }

    public static int getRegisterSize(BuilderTypeList typeList) {
        return getRegisterSize(builderTypeListToStringList(typeList));
    }

    public static Integer getIntegerValue(Object obj) {
        return (Integer) castToPrimitiveWrapper(obj, "Ljava/lang/Integer;");
    }

    public static Float getFloatValue(Object obj) {
        return (Float) castToPrimitiveWrapper(obj, "Ljava/lang/Float;");
    }

    public static Double getDoubleValue(Object obj) {
        return (Double) castToPrimitiveWrapper(obj, "Ljava/lang/Double;");
    }

    public static Long getLongValue(Object obj) {
        return (Long) castToPrimitiveWrapper(obj, "Ljava/lang/Long;");
    }

    public static Object castToPrimitiveWrapper(Object value, String targetType) {
        // TODO: add tests for this + confirm dalvik works this way

        // Type information is not always available beyond "const" because Dalvik handles multiple types like integers.
        // This is to make easier the casting of that number to the correct type.
        if (value instanceof Number) {
            Number castValue = (Number) value;
            if ("B".equals(targetType) || "Ljava/lang/Byte;".equals(targetType)) {
                return castValue.byteValue();
            } else if ("D".equals(targetType) || "Ljava/lang/Double;".equals(targetType)) {
                return castValue.doubleValue();
            } else if ("F".equals(targetType) || "Ljava/lang/Float;".equals(targetType)) {
                return castValue.floatValue();
            } else if ("I".equals(targetType) || "Ljava/lang/Integer;".equals(targetType)) {
                return castValue.intValue();
            } else if ("L".equals(targetType) || "Ljava/lang/Long;".equals(targetType)) {
                return castValue.longValue();
            } else if ("S".equals(targetType) || "Ljava/lang/Short;".equals(targetType)) {
                return castValue.shortValue();
            } else if ("C".equals(targetType) || "Ljava/lang/Character;".equals(targetType)) {
                return (char) castValue.intValue();
            } else if ("Z".equals(targetType) || "Ljava/lang/Boolean;".equals(targetType)) {
                return castValue.intValue() != 0;
            }
        } else if (value instanceof Boolean) {
            Boolean castValue = (Boolean) value;
            if ("Z".equals(targetType) || "Ljava/lang/Boolean;".equals(targetType)) {
                return castValue;
            } else if ("B".equals(targetType) || "Ljava/lang/Byte;".equals(targetType)) {
                return castValue ? 1 : 0;
            } else if ("I".equals(targetType) || "Ljava/lang/Integer;".equals(targetType)) {
                return castValue ? 1 : 0;
            } else if ("S".equals(targetType) || "Ljava/lang/Short;".equals(targetType)) {
                return castValue ? 1 : 0;
            }
        } else if (value instanceof Character) {
            Character castValue = (Character) value;
            Integer intValue = (int) castValue;
            if ("Z".equals(targetType) || "Ljava/lang/Boolean;".equals(targetType)) {
                return (int) castValue != 0;
            } else if ("B".equals(targetType) || "Ljava/lang/Byte;".equals(targetType)) {
                return intValue.byteValue();
            } else if ("I".equals(targetType) || "Ljava/lang/Integer;".equals(targetType)) {
                return intValue;
            } else if ("S".equals(targetType) || "Ljava/lang/Short;".equals(targetType)) {
                return intValue.shortValue();
            }
        }

        return value;
    }

    public static Set<String> getTypes(HeapItem item) {
        Set<String> types = new HashSet<>();

        String declaredType = item.getType();
        types.add(declaredType);

        Object value = item.getValue();
        if (value instanceof UnknownValue) {
            // Can't imply type from value
        } else if (value instanceof LocalClass) {
            types.add(SmaliClassUtils.javaClassToSmali(Class.class));
        } else if (value instanceof LocalField) {
            types.add(SmaliClassUtils.javaClassToSmali(Field.class));
        } else if (value instanceof LocalMethod) {
            types.add(SmaliClassUtils.javaClassToSmali(Method.class));
        } else if (value != null) {
            // All other value classes should be the actual classes
            types.add(SmaliClassUtils.javaClassToSmali(value.getClass()));
        }

        return types;
    }

    public static BuilderInstruction cloneInstruction(BuilderInstruction instr) {
        try {
            switch (instr.getClass().getSimpleName()) {
                case "BuilderInstruction3rc":
                    BuilderInstruction3rc bi3rc = (BuilderInstruction3rc) instr;
                    return new BuilderInstruction3rc(bi3rc.getOpcode(), bi3rc.getStartRegister(), bi3rc.getRegisterCount(), bi3rc.getReference());

                case "BuilderInstruction10t":
                case "BuilderInstruction20t":
                case "BuilderInstruction30t":
                    BuilderOffsetInstruction boi = (BuilderOffsetInstruction) instr;
                    return (BuilderInstruction) instr.getClass().getDeclaredConstructors()[0].newInstance(boi.getOpcode(), boi.getTarget());

                case "BuilderInstruction10x":
                    return new BuilderInstruction10x(instr.getOpcode());

                case "BuilderInstruction11n":
                case "BuilderInstruction21s":
                case "BuilderInstruction21ih":
                case "BuilderInstruction31i":
                    NarrowLiteralInstruction nli = (NarrowLiteralInstruction) instr;
                    OneRegisterInstruction ori = (OneRegisterInstruction) instr;
                    return (BuilderInstruction) instr.getClass().getDeclaredConstructors()[0].newInstance(nli.getOpcode(), ori.getRegisterA(), nli.getNarrowLiteral());

                case "BuilderInstruction11x":
                    BuilderInstruction11x bi11x = (BuilderInstruction11x) instr;
                    return new BuilderInstruction11x(bi11x.getOpcode(), bi11x.getRegisterA());

                case "BuilderInstruction12x":
                case "BuilderInstruction22x":
                case "BuilderInstruction32x":
                    TwoRegisterInstruction bi12x = (TwoRegisterInstruction) instr;
                    return (BuilderInstruction) instr.getClass().getDeclaredConstructors()[0].newInstance(bi12x.getOpcode(), bi12x.getRegisterA(), bi12x.getRegisterB());

                case "BuilderInstruction20bc":
                    BuilderInstruction20bc bi20bc = (BuilderInstruction20bc) instr;
                    return new BuilderInstruction20bc(bi20bc.getOpcode(), bi20bc.getVerificationError(), bi20bc.getReference());

                case "BuilderInstruction21c":
                case "BuilderInstruction31c":
                    ori = (OneRegisterInstruction) instr;
                    ReferenceInstruction ri = (ReferenceInstruction) instr;
                    return (BuilderInstruction) instr.getClass().getDeclaredConstructors()[0].newInstance(ori.getOpcode(), ori.getRegisterA(), ri.getReference());

                case "BuilderInstruction21lh":
                    BuilderInstruction21lh bi21lh = (BuilderInstruction21lh) instr;
                    return (BuilderInstruction) instr.getClass().getDeclaredConstructors()[0].newInstance(bi21lh.getOpcode(), bi21lh.getRegisterA(), bi21lh.getWideLiteral());

                case "BuilderInstruction21t":
                case "BuilderInstruction31t":
                    boi = (BuilderOffsetInstruction) instr;
                    ori = (OneRegisterInstruction) instr;
                    return (BuilderInstruction) instr.getClass().getDeclaredConstructors()[0].newInstance(boi.getOpcode(), ori.getRegisterA(), boi.getTarget());

                case "BuilderInstruction22b":
                case "BuilderInstruction22s":
                    nli = (NarrowLiteralInstruction) instr;
                    TwoRegisterInstruction tri = (TwoRegisterInstruction) instr;
                    return new BuilderInstruction22b(nli.getOpcode(), tri.getRegisterA(), tri.getRegisterB(), nli.getNarrowLiteral());

                case "BuilderInstruction22c":
                    BuilderInstruction22c bi22c = (BuilderInstruction22c) instr;
                    return new BuilderInstruction22c(bi22c.getOpcode(), bi22c.getRegisterA(), bi22c.getRegisterB(), bi22c.getReference());

                case "BuilderInstruction22t":
                    BuilderInstruction22t bi22t = (BuilderInstruction22t) instr;
                    return new BuilderInstruction22t(bi22t.getOpcode(), bi22t.getRegisterA(), bi22t.getRegisterB(), bi22t.getTarget());

                case "BuilderInstruction23x":
                    BuilderInstruction23x bi23x = (BuilderInstruction23x) instr;
                    return new BuilderInstruction23x(bi23x.getOpcode(), bi23x.getRegisterA(), bi23x.getRegisterB(), bi23x.getRegisterC());

                case "BuilderInstruction25x":
                    BuilderInstruction25x bi25x = (BuilderInstruction25x) instr;
                    return new BuilderInstruction25x(bi25x.getOpcode(), bi25x.getParameterRegisterCount(), bi25x.getRegisterFixedC(), bi25x.getRegisterParameterD(), bi25x.getRegisterParameterE(), bi25x.getRegisterParameterF(), bi25x.getRegisterParameterG());

                case "BuilderInstruction35c":
                    BuilderInstruction35c bi35c = (BuilderInstruction35c) instr;
                    return new BuilderInstruction35c(bi35c.getOpcode(), bi35c.getRegisterCount(), bi35c.getRegisterC(), bi35c.getRegisterD(), bi35c.getRegisterE(), bi35c.getRegisterF(), bi35c.getRegisterG(), bi35c.getReference());

                case "BuilderInstruction51l":
                    BuilderInstruction51l bi51l = (BuilderInstruction51l) instr;
                    return new BuilderInstruction51l(bi51l.getOpcode(), bi51l.getRegisterA(), bi51l.getWideLiteral());

                case "ArrayPayload":
                    BuilderArrayPayload bap = (BuilderArrayPayload) instr;
                    return new BuilderArrayPayload(bap.getElementWidth(), bap.getArrayElements());

                default:
                    throw new UnsupportedOperationException("Cannot clone unknown instruction " + instr.getOpcode().toString());
            }
        } catch (InvocationTargetException | InstantiationException | IllegalAccessException e) {
            throw new UnsupportedOperationException("Something went wrong here.. horribly wrong o.O", e);
        }
    }
}
