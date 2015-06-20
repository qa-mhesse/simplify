package org.cf.smalivm.opcode;

import gnu.trove.map.TIntObjectMap;
import org.cf.smalivm.VMTester;
import org.cf.smalivm.VirtualException;
import org.cf.smalivm.VirtualMachine;
import org.cf.smalivm.context.ExecutionNode;
import org.cf.smalivm.context.HeapItem;
import org.cf.smalivm.context.MethodState;
import org.cf.smalivm.type.UnknownValue;
import org.jf.dexlib2.Opcode;
import org.jf.dexlib2.builder.BuilderInstruction;
import org.jf.dexlib2.iface.instruction.TwoRegisterInstruction;
import org.jf.dexlib2.iface.instruction.formats.Instruction12x;
import org.junit.Before;
import org.junit.Test;
import org.junit.experimental.runners.Enclosed;
import org.junit.runner.RunWith;

import java.util.HashSet;
import java.util.Set;

import static org.mockito.Mockito.*;

@RunWith(Enclosed.class)
public class TestArrayLengthOp {

    private static final String CLASS_NAME = "Larray_length_test;";

    public static class TestObjectArrays {

        @Test
        public void testArrayLengthForEmptyIntegerArray() {
            TIntObjectMap<HeapItem> initial = VMTester.buildRegisterState(0, new Integer[]{}, "[I");
            TIntObjectMap<HeapItem> expected = VMTester.buildRegisterState(0, 0, "I");

            VMTester.testMethodState(CLASS_NAME, "ArrayLength()V", initial, expected);
        }

        @Test
        public void testArrayLengthForIntegerArray() {
            TIntObjectMap<HeapItem> initial = VMTester.buildRegisterState(0, new Integer[]{1, 2, 3}, "[I");
            TIntObjectMap<HeapItem> expected = VMTester.buildRegisterState(0, 3, "I");

            VMTester.testMethodState(CLASS_NAME, "ArrayLength()V", initial, expected);
        }

        @Test
        public void testArrayLengthForStringArray() {
            TIntObjectMap<HeapItem> initial = VMTester.buildRegisterState(0, new String[]{"isn't", "this", "where"},
                    "[I");
            TIntObjectMap<HeapItem> expected = VMTester.buildRegisterState(0, 3, "I");

            VMTester.testMethodState(CLASS_NAME, "ArrayLength()V", initial, expected);
        }

        @Test
        public void testArrayLengthForUnknownValueOfIntegerType() {
            TIntObjectMap<HeapItem> initial = VMTester
                    .buildRegisterState(0, new UnknownValue(), "[Ljava/lang/Integer;");
            TIntObjectMap<HeapItem> expected = VMTester.buildRegisterState(0, new UnknownValue(), "I");

            VMTester.testMethodState(CLASS_NAME, "ArrayLength()V", initial, expected);
        }

        @Test
        public void testArrayLengthForUnknownValueOfPrimitiveType() {
            TIntObjectMap<HeapItem> initial = VMTester.buildRegisterState(0, new UnknownValue(), "[I");
            TIntObjectMap<HeapItem> expected = VMTester.buildRegisterState(0, new UnknownValue(), "I");

            VMTester.testMethodState(CLASS_NAME, "ArrayLength()V", initial, expected);
        }
    }

    public static class TestPrimitiveArrays {

        @Test
        public void testArrayLengthForEmptyIntArray() {
            TIntObjectMap<HeapItem> initial = VMTester.buildRegisterState(0, new int[]{}, "[I");
            TIntObjectMap<HeapItem> expected = VMTester.buildRegisterState(0, 0, "I");

            VMTester.testMethodState(CLASS_NAME, "ArrayLength()V", initial, expected);
        }

        @Test
        public void testArrayLengthForIntArray() {
            TIntObjectMap<HeapItem> initial = VMTester.buildRegisterState(0, new int[]{1, 2, 3}, "[I");
            TIntObjectMap<HeapItem> expected = VMTester.buildRegisterState(0, 3, "I");

            VMTester.testMethodState(CLASS_NAME, "ArrayLength()V", initial, expected);
        }

        @Test
        public void testArrayLengthForLongArray() {
            TIntObjectMap<HeapItem> initial = VMTester.buildRegisterState(0, new long[]{1, 2, 3, 4}, "[J");
            TIntObjectMap<HeapItem> expected = VMTester.buildRegisterState(0, 4, "I");

            VMTester.testMethodState(CLASS_NAME, "ArrayLength()V", initial, expected);
        }

        @Test
        public void testArrayLengthForShortArray() {
            TIntObjectMap<HeapItem> initial = VMTester.buildRegisterState(0, new short[]{1, 2}, "[S");
            TIntObjectMap<HeapItem> expected = VMTester.buildRegisterState(0, 2, "I");

            VMTester.testMethodState(CLASS_NAME, "ArrayLength()V", initial, expected);
        }
    }

    public static class UnitTest {

        private static final int ADDRESS = 0;
        private static final int DEST_REGISTER = 0;
        private static final int ARG1_REGISTER = 2;

        private BuilderInstruction instruction;
        private OpFactory opFactory;
        private MethodState mState;
        private ExecutionNode node;
        private ArrayLengthOp op;

        @Before
        public void setUp() {
            VirtualMachine vm = mock(VirtualMachine.class);
            opFactory = new OpFactory(vm);
            mState = mock(MethodState.class);
            node = mock(ExecutionNode.class);
            instruction = mock(BuilderInstruction.class,
                    withSettings().extraInterfaces(TwoRegisterInstruction.class, Instruction12x.class));
            when(instruction.getOpcode()).thenReturn(Opcode.ARRAY_LENGTH);
            when(((Instruction12x) instruction).getRegisterA()).thenReturn(DEST_REGISTER);
            when(((Instruction12x) instruction).getRegisterB()).thenReturn(ARG1_REGISTER);
        }

        @Test
        public void nullArrayThrowsExpectedException() {
            VMTester.addHeapItem(mState, ARG1_REGISTER, null, "[I");

            op = (ArrayLengthOp) opFactory.create(instruction, ADDRESS);
            op.execute(node, mState);

            VirtualException expectedException = new VirtualException(NullPointerException.class,
                    "Attempt to get length of null array");
            Set<VirtualException> expectedExceptions = new HashSet<>();
            expectedExceptions.add(expectedException);
            VMTester.verifyExceptionHandling(expectedExceptions, node, mState);
        }
    }

}
