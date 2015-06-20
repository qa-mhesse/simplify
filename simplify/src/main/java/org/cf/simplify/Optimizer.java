package org.cf.simplify;

import org.cf.simplify.strategy.*;
import org.cf.smalivm.VirtualMachine;
import org.cf.smalivm.context.ExecutionGraph;
import org.jf.dexlib2.util.ReferenceUtil;
import org.jf.dexlib2.writer.builder.BuilderMethod;
import org.jf.dexlib2.writer.builder.DexBuilder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;

public class Optimizer {

    @SuppressWarnings("unused")
    private static final Logger log = LoggerFactory.getLogger(Optimizer.class.getSimpleName());

    private static final Map<String, Integer> totalOptimizationCounts = new HashMap<>();

    private final List<OptimizationStrategy> allStrategies;
    private final MethodBackedGraph mbgraph;
    private final String methodDescriptor;
    private final List<OptimizationStrategy> performOnceStrategies;
    private final List<OptimizationStrategy> performRepeatedlyStrategies;
    private final List<OptimizationStrategy> methodReexecuteStrategies;

    private boolean madeChanges;
    private boolean shouldExecuteAgain;
    private Map<String, Integer> optimizationCounts;

    public Optimizer(ExecutionGraph graph, BuilderMethod method, VirtualMachine vm, DexBuilder dexBuilder) {
        methodDescriptor = ReferenceUtil.getMethodDescriptor(method);
        mbgraph = new MethodBackedGraph(graph, method, vm, dexBuilder);
        performOnceStrategies = new LinkedList<>();
        performOnceStrategies.add(new StaticFieldSimplificationStrategy(mbgraph));
        performOnceStrategies.add(new ConstantPropigationStrategy(mbgraph));
        performOnceStrategies.add(new PeepholeStrategy(mbgraph));

        performRepeatedlyStrategies = new LinkedList<>();
        performRepeatedlyStrategies.add(new DeadRemovalStrategy(mbgraph));

        methodReexecuteStrategies = new LinkedList<>();
        methodReexecuteStrategies.add(new ReflectionRemovalStrategy(mbgraph));

        allStrategies = new LinkedList<>();
        allStrategies.addAll(performOnceStrategies);
        allStrategies.addAll(performRepeatedlyStrategies);
        allStrategies.addAll(methodReexecuteStrategies);

        optimizationCounts = new HashMap<>();
    }

    public static String getTotalOptimizationCounts() {
        StringBuilder sb = new StringBuilder("Total optimizations: ");
        Set<String> keySet = totalOptimizationCounts.keySet();
        String[] keys = keySet.toArray(new String[keySet.size()]);
        Arrays.sort(keys);
        for (String key : keys) {
            sb.append(key).append('=').append(totalOptimizationCounts.get(key)).append(", ");
        }
        if (sb.length() > "Total optimizations: ".length()) {
            sb.setLength(sb.length() - 2);
        }

        return sb.toString();
    }

    public void simplify(int maxSweeps) {
        System.out.println("Simplifying: " + methodDescriptor);

        for (OptimizationStrategy strategy : performOnceStrategies) {
            strategy.perform();
        }

        shouldExecuteAgain = false;
        for (OptimizationStrategy strategy : methodReexecuteStrategies) {
            shouldExecuteAgain |= strategy.perform();
        }

        int sweep = 0;
        do {
            madeChanges = false;
            for (OptimizationStrategy strategy : performRepeatedlyStrategies) {
                madeChanges |= strategy.perform();
            }
            sweep++;
        } while ((sweep < maxSweeps) && madeChanges);

        madeChanges = updateOptimizationCounts() > 0;
    }

    public boolean madeChanges() {
        return madeChanges;
    }

    public boolean getShouldExecuteAgain() {
        return shouldExecuteAgain;
    }

    private int updateOptimizationCounts() {
        int sweepCount = 0;
        for (OptimizationStrategy strategy : allStrategies) {
            Map<String, Integer> optimizations = strategy.getOptimizationCounts();
            for (String key : optimizations.keySet()) {
                Integer currentCount = optimizationCounts.get(key);
                if (null == currentCount) {
                    currentCount = 0;
                }
                Integer totalCount = totalOptimizationCounts.get(key);
                if (null == totalCount) {
                    totalCount = 0;
                }

                int count = optimizations.get(key);
                currentCount += count;
                optimizationCounts.put(key, currentCount);
                totalCount += count;
                totalOptimizationCounts.put(key, totalCount);

                sweepCount += count;
            }
        }

        return sweepCount;
    }

    public String getOptimizationCounts() {
        StringBuilder sb = new StringBuilder("Optimizations: ");
        Set<String> keySet = optimizationCounts.keySet();
        String[] keys = keySet.toArray(new String[keySet.size()]);
        Arrays.sort(keys);
        for (String key : keys) {
            sb.append(key).append('=').append(optimizationCounts.get(key)).append(", ");
        }
        if (sb.length() > "Optimizations: ".length()) {
            sb.setLength(sb.length() - 2);
        }

        return sb.toString();
    }

}
