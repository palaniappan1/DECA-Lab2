package analysis.exercise2;


import analysis.CallGraph;
import analysis.exercise1.CHAAlgorithm;
import soot.Hierarchy;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInterfaceInvokeExpr;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JSpecialInvokeExpr;

import java.util.HashSet;
import java.util.List;

public class RTAAlgorithm extends CHAAlgorithm  {

    @Override
    protected String getAlgorithm() {
        return "RTA";
    }

    // Only the initialized Classes should be added in the callGraph
    // So Creating one set for storing all the initialized Classes
    HashSet<SootClass> intializedClasses = new HashSet<>();

    @Override
    protected void populateCallGraph(Scene scene, CallGraph callGraph) {
        // Your implementation goes here, also feel free to add methods as needed
        // To get your entry points we prepared getEntryPoints(scene) in the superclass for you
        //RTA only takes into account that the program ACTUALLY INSTANTIATES. (Instantiation is creating an object)
        // Writing new method, as a usability for recursive calls.
        this.getEntryPoints(scene).forEach(
                entryPoint -> constructRTAAlgorithm(callGraph, entryPoint, scene));

    }

    private void constructRTAAlgorithm(CallGraph callGraph, SootMethod method, Scene scene){
        if (method.hasActiveBody()) {
            // This is a method. So add it to the call graph and mae sure it is not added before
            addNodeToCallGraph(method, callGraph);
            // If we identify a method we need to flow through all the units of the method to find
            // any other possible calls
            flowThroughMethod(method, callGraph, scene);

        } else { // This is not a method call and out of our scope
        }
    }

    private void flowThroughMethod(SootMethod entryPoint, CallGraph callGraph, Scene scene) {
        entryPoint.getActiveBody().getUnits().forEach(unit -> {
            Stmt stmt = (Stmt) unit;
            // According to our use-case, check whether any method call is made when analyzing the unit.
            // Method call can be found by containsInvokeExpr() returning true.
            if (stmt.containsInvokeExpr()) {
                InvokeExpr invokeExpr = stmt.getInvokeExpr();
                // Get the name of the invoked method
                SootMethod method = invokeExpr.getMethod();
                // Add the new method to the call graph and construct an edge from the current method to new method
                addNodeToCallGraph(method, callGraph);
                addEdgeToCallGraph(entryPoint, method, callGraph);
                //According to our usecase, we need to store all the classes initiliazed.
                // For the class to be initialized it should have the new() Operator. So check all the statements for that
                if(invokeExpr instanceof JSpecialInvokeExpr){
                    intializedClasses.add(method.getDeclaringClass());
                }
                // One interesting call site is the method can either be abstract class or interface
                // , which needs to be handled differently.
                else if(invokeExpr instanceof JInterfaceInvokeExpr){
                    // https://stackoverflow.com/questions/42570651/how-to-get-the-subclass-of-a-class-by-soot
                    // To find the methods inside the interface, we need to get the hierarchy of the Scene class
                    Hierarchy activeHierarchy = scene.getActiveHierarchy();
//                    FastHierarchy fastHierarchy = scene.getFastHierarchy();
                    // resolveAbstractDispatch gives a list of possible receiver methods
                    List<SootMethod> sootMethods = activeHierarchy.resolveAbstractDispatch(method.getDeclaringClass(), method);
//                    Set<SootMethod> sootMethods = fastHierarchy.resolveAbstractDispatch(method.getDeclaringClass(), method);
                    for (SootMethod sootMethod : sootMethods) {
                        // Only initialized classes should be added to the call graph
                        if(intializedClasses.contains(sootMethod.getDeclaringClass())) {
                            addNodeToCallGraph(sootMethod, callGraph);
                            addEdgeToCallGraph(entryPoint, sootMethod, callGraph);
                        }
                    }
                }
                else{
                    // Once the new method is added and edge created, it is now time to construct CHAAlgorithm for
                    // new (Target) Method
                    constructRTAAlgorithm(callGraph, method, scene);
                }

            }
        });
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
        if (!callGraph.hasEdge(sourceMethod, targetMethod))
            callGraph.addEdge(sourceMethod, targetMethod);
    }

}
