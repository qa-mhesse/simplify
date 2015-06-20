package org.cf.util;

import org.junit.Test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class TestImmutableUtils {

    @Test
    public void testStringIsImmutable() {
        assertTrue(ImmutableUtils.isImmutableClass("Ljava/lang/String;"));
    }

    @Test
    public void testStringArrayIsImmutable() {
        assertFalse(ImmutableUtils.isImmutableClass("[Ljava/lang/String;"));
    }

    @Test
    public void testStringBuilderIsImmutable() {
        assertFalse(ImmutableUtils.isImmutableClass("Ljava/lang/StringBuilder;"));
    }

}
