package analysis.exercise3;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import analysis.exercise1.CHAAlgorithm;
import org.graphstream.algorithm.TarjanStronglyConnectedComponents;
import org.graphstream.graph.Edge;
import org.graphstream.graph.Graph;
import org.graphstream.graph.Node;
import org.graphstream.graph.implementations.MultiGraph;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.*;
import soot.jimple.FieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.internal.*;

import java.util.*;
import java.util.stream.Collectors;

public class VTAAlgorithm extends CallGraphAlgorithm {

    private final Logger log = LoggerFactory.getLogger("VTA");

    @Override
    protected String getAlgorithm() {
        return "VTA";
    }

    // As VTA is a variable type analysis, we need a variable and it's corresponding type to be stored in order to perform VTA
    // So we declare a map to store this data
    // One variable can be of various class types(because of typecast), so declaring the value as a set
    HashMap<String, Set<SootClass>> variableTypes = new HashMap<>();

    @Override
    protected void populateCallGraph(Scene scene, CallGraph callGraph) {
        // Form Initial conservative Call Graph, as VTA requires already constructed callgraph
        CallGraph chaCallGraph = new CHAAlgorithm().constructCallGraph(scene);

        this.getEntryPoints(scene).forEach(entryPoint -> this.constructVTAAlgorithm(callGraph, entryPoint, scene));

        // Your implementation goes here, also feel free to add methods as needed
        // To get your entry points we prepared getEntryPoints(scene) in the superclass for you

    }

    private void constructVTAAlgorithm(CallGraph callGraph, SootMethod method, Scene scene) {
        if (method.hasActiveBody()) {
            // This is a method. So add it to the call graph and make sure it is not added before
            callGraph.addNode(method);
            // If we identify a method we need to flow through all the units of the method to find
            // any other possible calls
            flowThroughMethod(method, callGraph, scene);

        } else { // This is not a method call and out of our scope
        }
    }

    private void flowThroughMethod(SootMethod entryPoint, CallGraph callGraph, Scene scene) {
        entryPoint.getActiveBody().getUnits().forEach(unit -> {
            Stmt stmt = (Stmt) unit;
            // For a variable to be assigned an object, the unit should be a JAssignStmt
            // In our running example, SomeInterface leaf = new LeafClass();
            if (stmt instanceof JAssignStmt) {
                processStmtAsJAssignStmt(stmt);
            }
            // As of the running example, this is one of the call leaf.doSomething(); (Which is a interface call)
            // So need to handle it for the interface as well
            else if (stmt instanceof JInvokeStmt) {
                processStmtAsJInvokeStmt(stmt, entryPoint, callGraph);
            }
        });
    }

    private void processStmtAsJInvokeStmt(Stmt stmt, SootMethod entryPoint, CallGraph callGraph) {
        JInvokeStmt jInvokeStmt = (JInvokeStmt) stmt;
        InvokeExpr invokeExpr = jInvokeStmt.getInvokeExpr();
        String methodType = null;
        SootMethod invokedMethod = null;
        // The invoke expression is of two types, invoking expression in interface(leaf.doSomething(); in SimpleScenario.class)
        // or in normal method (aliasLeaf.doSomething(); in SimpleScenario.class)
        if (invokeExpr instanceof JInterfaceInvokeExpr) {
            JInterfaceInvokeExpr jInterfaceInvokeExpr = (JInterfaceInvokeExpr) invokeExpr;
            // The type of the interface method and the method it invocated needs to be stored
            methodType = jInterfaceInvokeExpr.getBase().toString();
            invokedMethod = jInterfaceInvokeExpr.getMethod();
        } else if (invokeExpr instanceof JVirtualInvokeExpr) {
            JVirtualInvokeExpr jVirtualInvokeExpr = (JVirtualInvokeExpr) invokeExpr;
            methodType = jVirtualInvokeExpr.getBase().toString();
            invokedMethod = jVirtualInvokeExpr.getMethod();
        }

        if (methodType != null && invokedMethod != null) {
            Set<SootClass> values = variableTypes.get(methodType);
//            if (values != null && !values.isEmpty()) {
                for (SootClass targetClass : values) {
                    List<SootMethod> targetClsMthds = targetClass.getMethods();
                    for (SootMethod sootMethod : targetClsMthds) {
                        if (sootMethod.getSubSignature().equals(invokedMethod.getSubSignature())) {
                            addNodeToCallGraph(sootMethod, callGraph);
                            addEdgeToCallGraph(sootMethod, entryPoint, callGraph);
                        }
                    }
                }
//            }
        }
    }

    private void processStmtAsJAssignStmt(Stmt stmt) {
        // The various types a variable can be assigned object is
        // A a (variable) = new A() (class) ---> JNewExpr
        // A b (variable) = a (class) --> JCastExpr
        // So as of the example above, leftop is a variable and the rightop is a classType
        String variable = ((JAssignStmt) stmt).getLeftOp().toString();
        Value classType = ((JAssignStmt) stmt).getRightOp();
        // Variable to store the classType of the variable
        SootClass sootClass = null;


        // Here there comes two cases, A class can either be created already and new object is created.
        // A a = new A() --> So we already have class A in our HashMap
        // A b = new A() --> This is the creation of new object for already existing class in our hashmap, in this case just add the variable
        // The classType can be either a new class invocation or typecast or alias (So classType can be either in key or value in our hashmap)
        if (variableTypes.containsKey(classType.toString())) {
            variableTypes.put(variable, variableTypes.get(classType.toString()));
        } else if (classType instanceof JNewExpr || classType instanceof JCastExpr) {
            // A class that models Java's reference types. RefTypes are parametrized by a class name. Two RefType are equal iff they are
            // parametrized by the same class name as a String.
            sootClass = ((RefType) classType.getType()).getSootClass();
        } else if (classType instanceof JStaticInvokeExpr) {
            // This is a call that invokes method from other class, so the variable will have the return type of that method
            // a = SomeClass.getThis(); -> SomeClass.getThis() return a String
            // So 'a' will have the soot-class of type String
            JStaticInvokeExpr invExpr = (JStaticInvokeExpr) classType;
            // The soot-class is the type of the return statement (What the method is returning)
            sootClass = getRefType(invExpr);
        }

        if (sootClass != null) {
            if(!variableTypes.containsKey(variable)){
                // We need to add this to the value of the hashmap
                // So create a set, because our param in hashmap is string
                Set<SootClass> sootClasses = new HashSet<>();
                sootClasses.add(sootClass);
                variableTypes.put(variable, sootClasses);
            }
        }

    }

    private SootClass getRefType(JStaticInvokeExpr invExpr) {
        SootClass sootClass;
        List<Unit> collect = invExpr.getMethod().getActiveBody().getUnits().stream().filter(unit -> unit instanceof JReturnStmt).collect(Collectors.toList());
        JReturnStmt returnStmt = (JReturnStmt) collect.get(0);
        sootClass = ((RefType) returnStmt.getOpBox().getValue().getType()).getSootClass();
        return sootClass;
    }

    private void addNodeToCallGraph(SootMethod method, CallGraph callGraph) {
        // Check whether the method already exists
        if (!callGraph.hasNode(method)) {
            callGraph.addNode(method);
        }
    }


    private void addEdgeToCallGraph(SootMethod sourceMethod, SootMethod targetMethod, CallGraph callGraph) {
        if (!callGraph.hasNode(sourceMethod) || !callGraph.hasNode(targetMethod))
            throw new RuntimeException("Method is not found in the nodes list");
        // Check if the edge already exists
        if (!callGraph.hasEdge(targetMethod, sourceMethod))
            callGraph.addEdge(targetMethod, sourceMethod);
    }


    /**
     * You can use this class to represent your type assignment graph.
     * We do not use this data structure in tests, so you are free to use something else.
     * However, we use this data structure in our solution and it instantly supports collapsing strong-connected components.
     */
    private class TypeAssignmentGraph {
        private final Graph graph;
        private TarjanStronglyConnectedComponents tscc = new TarjanStronglyConnectedComponents();

        public TypeAssignmentGraph() {
            this.graph = new MultiGraph("tag");
        }

        private boolean containsNode(Value value) {
            return graph.getNode(createId(value)) != null;
        }

        private boolean containsEdge(Value source, Value target) {
            return graph.getEdge(createId(source) + "-" + createId(target)) != null;
        }

        private String createId(Value value) {
            if (value instanceof FieldRef) return value.toString();
            return Integer.toHexString(System.identityHashCode(value));
        }

        public void addNode(Value value) {
            if (!containsNode(value)) {
                Node node = graph.addNode(createId(value));
                node.setAttribute("value", value);
                node.setAttribute("ui.label", value);
                node.setAttribute("tags", new HashSet<SootClass>());
            }
        }

        public void tagNode(Value value, SootClass classTag) {
            if (containsNode(value))
                getNodeTags(value).add(classTag);
        }

        public Set<Pair<Value, Set<SootClass>>> getTaggedNodes() {
            return graph.getNodeSet().stream()
                    .map(n -> new Pair<Value, Set<SootClass>>(n.getAttribute("value"), (Set<SootClass>) n.getAttribute("tags")))
                    .filter(p -> p.second.size() > 0)
                    .collect(Collectors.toSet());
        }

        public Set<SootClass> getNodeTags(Value val) {
            return ((Set<SootClass>) graph.getNode(createId(val)).getAttribute("tags"));
        }

        public void addEdge(Value source, Value target) {
            if (!containsEdge(source, target)) {
                Node sourceNode = graph.getNode(createId(source));
                Node targetNode = graph.getNode(createId(target));
                if (sourceNode == null || targetNode == null)
                    log.error("Could not find one of the nodes. Source: " + sourceNode + " - Target: " + targetNode);
                graph.addEdge(createId(source) + "-" + createId(target),
                        sourceNode,
                        targetNode, true);
            }

        }

        public Set<Value> getTargetsFor(Value initialNode) {
            if (!containsNode(initialNode)) return Collections.emptySet();
            Node source = graph.getNode(createId(initialNode));
            Collection<Edge> edges = source.getLeavingEdgeSet();
            return edges.stream()
                    .map(e -> (Value) e.getTargetNode().getAttribute("value"))
                    .collect(Collectors.toSet());
        }

        /**
         * Use this method to start the SCC computation.
         */
        public void annotateScc() {
            tscc.init(graph);
            tscc.compute();
        }

        /**
         * Retrieve the index assigned by the SCC algorithm
         *
         * @param value
         * @return
         */
        public Object getSccIndex(Value value) {
            if (!containsNode(value)) return null;
            return graph.getNode(createId(value)).getAttribute(tscc.getSCCIndexAttribute());
        }

        /**
         * Use this method to inspect your type assignment graph
         */
        public void draw() {
            graph.display();
        }
    }

    private class Pair<A, B> {
        final A first;
        final B second;

        public Pair(A first, B second) {
            this.first = first;
            this.second = second;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Pair<?, ?> pair = (Pair<?, ?>) o;

            if (first != null ? !first.equals(pair.first) : pair.first != null) return false;
            return second != null ? second.equals(pair.second) : pair.second == null;
        }

        @Override
        public int hashCode() {
            int result = first != null ? first.hashCode() : 0;
            result = 31 * result + (second != null ? second.hashCode() : 0);
            return result;
        }

        @Override
        public String toString() {
            return "(" + first +
                    ", " + second +
                    ')';
        }
    }

}
