package org.cf.smalivm;

import org.cf.smalivm.context.ExecutionGraph;
import org.cf.smalivm.context.HeapItem;
import org.cf.smalivm.context.MethodState;
import org.cf.smalivm.exception.MaxAddressVisitsExceeded;
import org.cf.smalivm.exception.MaxCallDepthExceeded;
import org.cf.smalivm.exception.MaxMethodVisitsExceeded;
import org.cf.smalivm.exception.UnhandledVirtualException;
import org.junit.Before;
import org.junit.Test;
import org.junit.experimental.runners.Enclosed;
import org.junit.runner.RunWith;

import static org.junit.Assert.assertEquals;

@RunWith(Enclosed.class)
public class TestMethodInheritence {

    public static class ChildClass {

        private static final String CLASS_NAME = "Lchild_class;";
        private static final String EXPECTED_VALUE = "abstract?";
        private VirtualMachine vm;

        @Before
        public void setupVM() {
            vm = VMTester.getTestVM();
        }

        @Test
        public void testInvokingAbstractMethodThroughParentReferenceWorks() throws MaxAddressVisitsExceeded,
                MaxCallDepthExceeded, MaxMethodVisitsExceeded, UnhandledVirtualException {
            String methodName = "callsAbstractMethod()Ljava/lang/String;";
            ExecutionGraph graph = vm.execute(CLASS_NAME + "->" + methodName);
            HeapItem item = graph.getTerminatingRegisterConsensus(MethodState.ReturnRegister);
            String value = (String) item.getValue();

            assertEquals(EXPECTED_VALUE, value);
        }

        @Test
        public void testInvokingImplemenetedAbstractMethodWorks() throws MaxAddressVisitsExceeded,
                MaxCallDepthExceeded, MaxMethodVisitsExceeded, UnhandledVirtualException {
            String methodName = "abstractMethod()Ljava/lang/String;";
            ExecutionGraph graph = vm.execute(CLASS_NAME + "->" + methodName);
            HeapItem item = graph.getTerminatingRegisterConsensus(MethodState.ReturnRegister);
            String value = (String) item.getValue();

            assertEquals(EXPECTED_VALUE, value);
        }

        @Test
        public void testInvokingParentMethodWorks() throws MaxAddressVisitsExceeded, MaxCallDepthExceeded,
                MaxMethodVisitsExceeded, UnhandledVirtualException {
            String methodName = "callsParentMethod()Ljava/lang/String;";
            ExecutionGraph graph = vm.execute(CLASS_NAME + "->" + methodName);
            HeapItem item = graph.getTerminatingRegisterConsensus(MethodState.ReturnRegister);
            String value = (String) item.getValue();

            assertEquals("parentMethod", value);
        }
    }

    public static class ParentClass {

        private static final String CLASS_NAME = "Lparent_class;";

        private VirtualMachine vm;

        @Before
        public void setupVM() {
            vm = VMTester.getTestVM();
        }

        @Test
        public void testExecutingAbstractMethodReturnsNull() throws MaxAddressVisitsExceeded, MaxCallDepthExceeded,
                MaxMethodVisitsExceeded, UnhandledVirtualException {
            String methodName = "abstractMethod()Ljava/lang/String;";
            ExecutionGraph graph = vm.execute(CLASS_NAME + "->" + methodName);

            assertEquals(null, graph);
        }
    }

}
