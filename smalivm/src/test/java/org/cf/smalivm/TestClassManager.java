package org.cf.smalivm;

import org.cf.smalivm.exception.UnknownAncestors;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.IOException;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.*;

public class TestClassManager {

    private static final String TEST_DIRECTORY = "resources/test";
    private static final String CHILD_CLASS = "Lchild_class;";
    private static final String PARENT_CLASS = "Lparent_class;";
    private static final String GRANDPARENT_CLASS = "Lgrandparent_class;";
    private static final String NON_EXISTENT_CLASS = "Lthis_certainly_wont_exists;";

    private static ClassManager manager;

    @BeforeClass
    public static void getClassManager() throws IOException {
        manager = new ClassManager(TEST_DIRECTORY);
    }

    @Test
    public void testChildIsInstanceOfParent() throws UnknownAncestors {
        boolean isInstance = manager.isInstance(CHILD_CLASS, PARENT_CLASS);

        assertTrue(isInstance);
    }

    @Test
    public void testCanUnderstandNativeMethods() throws UnknownAncestors {
        boolean isNative = manager.isNativeMethod("Lnative_method_class;->nativeMethod()V");

        assertTrue(isNative);
    }

    @Test
    public void testChildIsInstanceOfGrandParent() throws UnknownAncestors {
        boolean isInstance = manager.isInstance(CHILD_CLASS, GRANDPARENT_CLASS);

        assertTrue(isInstance);
    }

    @Test
    public void testParentIsNotInstanceOfChild() throws UnknownAncestors {
        boolean isInstance = manager.isInstance(PARENT_CLASS, CHILD_CLASS);

        assertFalse(isInstance);
    }

    @Test
    public void testStringIsInstanceOfObject() throws UnknownAncestors {
        boolean isInstance = manager.isInstance(String.class, Object.class);

        assertTrue(isInstance);
    }

    @Test
    public void testStringArrayIsInstanceOfObjectArray() throws UnknownAncestors {
        boolean isInstance = manager.isInstance(String[].class, Object[].class);

        assertTrue(isInstance);
    }

    @Test
    public void testStringArrayIsInstanceOf2DObjectArray() throws UnknownAncestors {
        boolean isInstance = manager.isInstance(String[].class, Object[][].class);

        assertFalse(isInstance);
    }

    @Test
    public void testIntPrimitiveIsInstanceOfInteger() throws UnknownAncestors {
        boolean isInstance = manager.isInstance(int.class, Integer.class);

        assertTrue(isInstance);
    }

    @Test
    public void testIntPrimitiveIsInstanceOfNumber() throws UnknownAncestors {
        boolean isInstance = manager.isInstance(int.class, Number.class);

        assertTrue(isInstance);
    }

    @Test
    public void testIntPrimitiveIsInstanceIntPrimitive() throws UnknownAncestors {
        boolean isInstance = manager.isInstance(int.class, int.class);

        assertTrue(isInstance);
    }

    @Test
    public void testIntPrimitiveIsNotInstanceOfLong() throws UnknownAncestors {
        boolean isInstance = manager.isInstance(int.class, Long.class);

        assertFalse(isInstance);
    }

    @Test
    public void testIntPrimitiveIsNotInstanceOfIntArray() throws UnknownAncestors {
        boolean isInstance = manager.isInstance(int.class, int[].class);

        assertFalse(isInstance);
    }

    @Test(expected = UnknownAncestors.class)
    public void testUnknownChildThrowsUnknownAncestors() throws UnknownAncestors {
        manager.isInstance(NON_EXISTENT_CLASS, PARENT_CLASS);
    }

    @Test
    public void testUnknownParentDoesNotThrowUnknownAncestors() throws UnknownAncestors {
        manager.isInstance(CHILD_CLASS, NON_EXISTENT_CLASS);
    }

    @Test
    public void testGetFieldsAndTypesReturnsFieldsFromSuperClasses() {
        List<String> fieldNameAndTypes = manager.getFieldNameAndTypes("Lchild_class;");
        String[] actual = fieldNameAndTypes.toArray(new String[fieldNameAndTypes.size()]);
        String[] expected = new String[]{"childField:I", "parentField:I", "grandparentField:I"};
        Arrays.sort(actual);
        Arrays.sort(expected);

        assertArrayEquals(expected, actual);
    }

}
