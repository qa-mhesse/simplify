package org.cf.smalivm.emulate;

import org.cf.smalivm.ClassManager;
import org.cf.smalivm.SideEffect;
import org.cf.smalivm.VirtualException;
import org.cf.smalivm.VirtualMachine;
import org.cf.smalivm.context.HeapItem;
import org.cf.smalivm.context.MethodState;
import org.cf.smalivm.type.LocalClass;
import org.cf.smalivm.type.LocalField;
import org.cf.smalivm.type.UnknownValue;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.reflect.Field;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class java_lang_Class_getField implements MethodStateMethod {

    private static final Logger log = LoggerFactory.getLogger(java_lang_Class_getField.class.getSimpleName());

    private static final String RETURN_TYPE = "Ljava/lang/reflect/Field;";

    private final Set<VirtualException> exceptions;
    private SideEffect.Level level;

    java_lang_Class_getField() {
        exceptions = new HashSet<>();
        level = SideEffect.Level.NONE;
    }

    private static Field getNonLocalField(Class<?> klazz, String fieldName) throws NoSuchFieldException,
            SecurityException {
        return klazz.getField(fieldName);
    }

    @Override
    public Set<VirtualException> getExceptions() {
        return exceptions;
    }

    private void setException(VirtualException exception) {
        exceptions.add(exception);
    }

    @Override
    public void execute(VirtualMachine vm, MethodState mState) throws Exception {
        // TODO: getDeclared for fields and methods should be handled differently
        // can look at method descriptor to figure out which one we are
        HeapItem classItem = mState.peekParameter(0);
        Object classValue = classItem.getValue();
        String fieldName = (String) mState.peekParameter(1).getValue();

        Object fieldValue;
        if (classValue instanceof Class<?>) {
            // It's a real class. Try and return a real field.
            try {
                fieldValue = getNonLocalField((Class<?>) classValue, fieldName);
            } catch (NoSuchFieldException | SecurityException e) {
                setException(new VirtualException(e));
                return;
            }
        } else if (classValue instanceof LocalClass) {
            LocalClass localClass = (LocalClass) classValue;
            fieldValue = getLocalField(vm.getClassManager(), localClass, fieldName);
            if (fieldValue == null) {
                setException(new VirtualException(NoSuchFieldException.class, fieldName));
                return;
            }
        } else {
            if (log.isErrorEnabled()) {
                log.error("Class.getField with {} has unexpected type and confuses me.", classItem);
            }
            fieldValue = new UnknownValue();
        }

        mState.assignReturnRegister(fieldValue, RETURN_TYPE);
    }

    private Object getLocalField(ClassManager classManager, LocalClass localClass, String fieldName) {
        String className = localClass.getName();
        if (!classManager.isLocalClass(className)) {
            return null;
        }

        List<String> fieldNameAndTypes = classManager.getFieldNameAndTypes(className);
        for (String fieldNameAndType : fieldNameAndTypes) {
            if (fieldNameAndType.startsWith(fieldName)) {
                return new LocalField(className + "->" + fieldNameAndType);
            }
        }

        return null;
    }

    @Override
    public SideEffect.Level getSideEffectLevel() {
        return level;
    }

}
