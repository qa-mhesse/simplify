package org.cf.smalivm.opcode;

import gnu.trove.map.TIntObjectMap;
import org.cf.smalivm.VMTester;
import org.cf.smalivm.VirtualMachine;
import org.cf.smalivm.context.ExecutionNode;
import org.cf.smalivm.context.HeapItem;
import org.cf.smalivm.context.MethodState;
import org.cf.smalivm.type.UnknownValue;
import org.jf.dexlib2.Opcode;
import org.jf.dexlib2.builder.BuilderInstruction;
import org.jf.dexlib2.iface.instruction.ReferenceInstruction;
import org.jf.dexlib2.iface.instruction.RegisterRangeInstruction;
import org.jf.dexlib2.iface.instruction.VariableRegisterInstruction;
import org.jf.dexlib2.iface.instruction.formats.Instruction35c;
import org.jf.dexlib2.iface.instruction.formats.Instruction3rc;
import org.jf.dexlib2.iface.reference.Reference;
import org.jf.dexlib2.immutable.reference.ImmutableTypeReference;
import org.junit.Before;
import org.junit.Test;
import org.junit.experimental.runners.Enclosed;
import org.junit.runner.RunWith;
import org.mockito.ArgumentCaptor;
import org.mockito.runners.MockitoJUnitRunner;

import static org.junit.Assert.assertEquals;
import static org.mockito.Matchers.eq;
import static org.mockito.Mockito.*;

@RunWith(Enclosed.class)
public class TestFilledNewArray {

    @RunWith(MockitoJUnitRunner.class)
    public static class UnitTestFilledNewArray {

        private static final int ADDRESS = 0;
        private static final int REGISTER_C = 0;
        private static final int REGISTER_D = 1;
        private static final int REGISTER_E = 2;
        private static final int REGISTER_F = 3;
        private static final int REGISTER_G = 4;

        private BuilderInstruction instruction;
        private OpFactory opFactory;
        private MethodState mState;
        private ExecutionNode node;
        private HeapItem itemC;
        private HeapItem itemD;
        private HeapItem itemE;
        private HeapItem itemF;
        private HeapItem itemG;
        private FilledNewArrayOp op;

        @Before
        public void setUp() {
            VirtualMachine vm = mock(VirtualMachine.class);
            opFactory = new OpFactory(vm);
            instruction = mock(
                    BuilderInstruction.class,
                    withSettings().extraInterfaces(Instruction35c.class, VariableRegisterInstruction.class,
                            ReferenceInstruction.class));
            when(((Instruction35c) instruction).getRegisterC()).thenReturn(REGISTER_C);
            when(((Instruction35c) instruction).getRegisterD()).thenReturn(REGISTER_D);
            when(((Instruction35c) instruction).getRegisterE()).thenReturn(REGISTER_E);
            when(((Instruction35c) instruction).getRegisterF()).thenReturn(REGISTER_F);
            when(((Instruction35c) instruction).getRegisterG()).thenReturn(REGISTER_G);

            Reference ref = new ImmutableTypeReference("[I");
            when(((ReferenceInstruction) instruction).getReference()).thenReturn(ref);

            mState = mock(MethodState.class);
            node = mock(ExecutionNode.class);
            itemC = mock(HeapItem.class);
            itemD = mock(HeapItem.class);
            itemE = mock(HeapItem.class);
            itemF = mock(HeapItem.class);
            itemG = mock(HeapItem.class);
            when(mState.readRegister(REGISTER_C)).thenReturn(itemC);
            when(mState.readRegister(REGISTER_D)).thenReturn(itemD);
            when(mState.readRegister(REGISTER_E)).thenReturn(itemE);
            when(mState.readRegister(REGISTER_F)).thenReturn(itemF);
            when(mState.readRegister(REGISTER_G)).thenReturn(itemG);

            when(itemC.isUnknown()).thenReturn(false);
            when(itemD.isUnknown()).thenReturn(false);
            when(itemE.isUnknown()).thenReturn(false);
            when(itemF.isUnknown()).thenReturn(false);
            when(itemG.isUnknown()).thenReturn(false);
        }

        private void doTest(Number... values) {
            when(instruction.getOpcode()).thenReturn(Opcode.FILLED_NEW_ARRAY);
            when(((VariableRegisterInstruction) instruction).getRegisterCount()).thenReturn(values.length);
            switch (values.length) {
                case 5:
                    when(itemG.getValue()).thenReturn(values[4]);
                case 4:
                    when(itemF.getValue()).thenReturn(values[3]);
                case 3:
                    when(itemE.getValue()).thenReturn(values[2]);
                case 2:
                    when(itemD.getValue()).thenReturn(values[1]);
                case 1:
                    when(itemC.getValue()).thenReturn(values[0]);
            }

            op = (FilledNewArrayOp) opFactory.create(instruction, ADDRESS);
            op.execute(node, mState);

            switch (values.length) {
                case 5:
                    verify(mState, times(1)).readRegister(eq(REGISTER_G));
                case 4:
                    verify(mState, times(1)).readRegister(eq(REGISTER_F));
                case 3:
                    verify(mState, times(1)).readRegister(eq(REGISTER_E));
                case 2:
                    verify(mState, times(1)).readRegister(eq(REGISTER_D));
                case 1:
                    verify(mState, times(1)).readRegister(eq(REGISTER_C));
            }

            int[] expected = new int[values.length];
            for (int i = 0; i < expected.length; i++) {
                expected[i] = values[i].intValue();
            }

            verify(mState, times(1)).assignResultRegister(eq(expected), eq("[I"));
        }

        @Test
        public void testOneIntegerGivesExpectedArray() {
            doTest(1);
        }

        @Test
        public void testTwoIntegersGivesExpectedArray() {
            doTest(1, 2);
        }

        @Test
        public void testThreeIntegersGivesExpectedArray() {
            doTest(1, 2, 3);
        }

        @Test
        public void testFourIntegersGivesExpectedArray() {
            doTest(3, 5, 7, 11);
        }

        @Test
        public void testFiveIntegersGivesExpectedArray() {
            doTest(42, -42, 42, -42, 42);
        }

        @Test
        public void testThreeNumbersGivesExpectedArray() {
            Short number1 = 42;
            Byte number2 = 35;
            Integer number3 = 10;
            doTest(number1, number2, number3);
        }

        @Test
        public void testUnknownValueGivesUnknownArray() {
            when(instruction.getOpcode()).thenReturn(Opcode.FILLED_NEW_ARRAY);
            when(((VariableRegisterInstruction) instruction).getRegisterCount()).thenReturn(2);
            when(itemD.getValue()).thenReturn(new UnknownValue());
            when(itemD.isUnknown()).thenReturn(true);
            when(itemC.getValue()).thenReturn(3);

            op = (FilledNewArrayOp) opFactory.create(instruction, ADDRESS);
            op.execute(node, mState);

            verify(mState, times(1)).readRegister(eq(REGISTER_D));
            verify(mState, times(1)).readRegister(eq(REGISTER_C));

            ArgumentCaptor<HeapItem> setItem = ArgumentCaptor.forClass(HeapItem.class);
            verify(mState, times(1)).assignResultRegister(setItem.capture());
            assertEquals(UnknownValue.class, setItem.getValue().getValue().getClass());
            assertEquals("[I", setItem.getValue().getType());
            assertEquals("filled-new-array {r0, r1}, [I", op.toString());
        }
    }

    @RunWith(MockitoJUnitRunner.class)
    public static class UnitTestFilledNewArrayRange {

        private static final int ADDRESS = 0;

        private BuilderInstruction instruction;
        private OpFactory opFactory;
        private MethodState mState;
        private ExecutionNode node;
        private FilledNewArrayOp op;

        @Before
        public void setUp() {
            VirtualMachine vm = mock(VirtualMachine.class);
            opFactory = new OpFactory(vm);
            instruction = mock(
                    BuilderInstruction.class,
                    withSettings().extraInterfaces(Instruction3rc.class, VariableRegisterInstruction.class,
                            ReferenceInstruction.class, RegisterRangeInstruction.class));

            Reference ref = new ImmutableTypeReference("[I");
            when(((ReferenceInstruction) instruction).getReference()).thenReturn(ref);
            node = mock(ExecutionNode.class);
            mState = mock(MethodState.class);
        }

        private void doTest(Number... values) {
            when(instruction.getOpcode()).thenReturn(Opcode.FILLED_NEW_ARRAY_RANGE);
            when(((VariableRegisterInstruction) instruction).getRegisterCount()).thenReturn(values.length);
            when(((RegisterRangeInstruction) instruction).getStartRegister()).thenReturn(0);

            int[] expected = new int[values.length];
            for (int i = 0; i < expected.length; i++) {
                expected[i] = values[i].intValue();
                HeapItem item = mock(HeapItem.class);
                when(item.getValue()).thenReturn(expected[i]);
                when(item.getType()).thenReturn("I");
                when(mState.readRegister(i)).thenReturn(item);
            }

            op = (FilledNewArrayOp) opFactory.create(instruction, ADDRESS);
            op.execute(node, mState);

            for (int i = 0; i < expected.length; i++) {
                verify(mState, times(1)).readRegister(eq(i));
            }
            verify(mState, times(1)).assignResultRegister(eq(expected), eq("[I"));
        }

        @Test
        public void testSixIntegersGivesExpectedArray() {
            doTest(42, -42, 42, -42, 42, -42);
        }

        @Test
        public void testUnknownValueGivesUnknownArray() {
            when(instruction.getOpcode()).thenReturn(Opcode.FILLED_NEW_ARRAY_RANGE);
            when(((VariableRegisterInstruction) instruction).getRegisterCount()).thenReturn(6);
            when(((RegisterRangeInstruction) instruction).getStartRegister()).thenReturn(0);

            for (int i = 0; i < 6; i++) {
                HeapItem item = mock(HeapItem.class);
                when(item.getValue()).thenReturn(i == 3 ? new UnknownValue() : i);
                when(item.getType()).thenReturn("I");
                when(mState.readRegister(i)).thenReturn(item);
            }

            op = (FilledNewArrayOp) opFactory.create(instruction, ADDRESS);
            op.execute(node, mState);

            for (int i = 0; i < 6; i++) {
                verify(mState, times(1)).readRegister(eq(i));
            }
            ArgumentCaptor<HeapItem> setItem = ArgumentCaptor.forClass(HeapItem.class);
            verify(mState, times(1)).assignResultRegister(setItem.capture());
            assertEquals(UnknownValue.class, setItem.getValue().getValue().getClass());
            assertEquals("[I", setItem.getValue().getType());
            assertEquals("filled-new-array/range {r0 .. r5}, [I", op.toString());
        }
    }

    public static class IntegrationTest {

        private static final String CLASS_NAME = "Lfilled_new_array_test;";
        private static final String METHOD_NAME = "TestFilledNewArray()V";

        @Test
        public void testIntegerParametersCreatesArrayWithExpectedContents() {
            int[] elements = new int[]{2, 3, 5};
            TIntObjectMap<HeapItem> initial = VMTester.buildRegisterState(0, elements[0], "I", 1, elements[1], "I", 2,
                    elements[2], "I");
            TIntObjectMap<HeapItem> expected = VMTester.buildRegisterState(MethodState.ResultRegister, elements, "[I");

            VMTester.testMethodState(CLASS_NAME, METHOD_NAME, initial, expected);
        }

        @Test
        public void testNewArrayRangeWithIntegerParametersCreatesArrayWithExpectedContents() {
            int[] elements = new int[]{2, 3, 5, 7, 11, 13};
            TIntObjectMap<HeapItem> initial = VMTester.buildRegisterState(0, elements[0], "I", 1, elements[1], "I", 2,
                    elements[2], "I", 3, elements[3], "I", 4, elements[4], "I", 5, elements[5], "I");
            TIntObjectMap<HeapItem> expected = VMTester.buildRegisterState(MethodState.ResultRegister, elements, "[I");

            VMTester.testMethodState(CLASS_NAME, "TestFilledNewArrayRange()V", initial, expected);
        }

        @Test
        public void testShortParametersCreatesArrayWithExpectedContents() {
            Short[] elements = new Short[]{2, 3, 5};
            int[] intElements = new int[]{2, 3, 5};
            TIntObjectMap<HeapItem> initial = VMTester.buildRegisterState(0, elements[0], "S", 1, elements[1], "S", 2,
                    elements[2], "S");
            TIntObjectMap<HeapItem> expected = VMTester.buildRegisterState(MethodState.ResultRegister, intElements,
                    "[I");

            VMTester.testMethodState(CLASS_NAME, METHOD_NAME, initial, expected);
        }

        @Test
        public void testUnknownElementParameterReturnsUnknownValueOfIntegerArrayType() {
            TIntObjectMap<HeapItem> initial = VMTester.buildRegisterState(0, 2, "I", 1, 3, "I", 2, new UnknownValue(),
                    "I");
            TIntObjectMap<HeapItem> expected = VMTester.buildRegisterState(MethodState.ResultRegister,
                    new UnknownValue(), "[I");

            VMTester.testMethodState(CLASS_NAME, METHOD_NAME, initial, expected);
        }
    }

}
