package analysis.exercise1;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import soot.*;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;

import java.util.List;
import java.util.Set;

public class CHAAlgorithm extends CallGraphAlgorithm {

    @Override
    protected String getAlgorithm() {
        return "CHA";
    }

    @Override
    protected void populateCallGraph(Scene scene, CallGraph callGraph) {
        // Your implementation goes here, also feel free to add methods as needed
        // To get your entry points we prepared getEntryPoints(scene) in the superclass for you

        // Writing new method, as a usability for recursive calls.
        this.getEntryPoints(scene).forEach(
                entryPoint -> constructCHAAlgorithm(callGraph, entryPoint, scene));
    }

    private void constructCHAAlgorithm(CallGraph callGraph, SootMethod method, Scene scene) {
        // To identify method calls, have a look at the body of a method where hasActiveBody() re-
        //turns true
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
                // One interesting call site is the method can either be abstract class or interface
                // , which needs to be handled differently.
                if (invokeExpr instanceof InterfaceInvokeExpr) {
                    // https://stackoverflow.com/questions/42570651/how-to-get-the-subclass-of-a-class-by-soot
                    // To find the methods inside the interface, we need to get the hierarchy of the Scene class
                    Hierarchy activeHierarchy = scene.getActiveHierarchy();
//                    FastHierarchy fastHierarchy = scene.getFastHierarchy();
                    // resolveAbstractDispatch gives a list of possible receiver methods
                    List<SootMethod> sootMethods = activeHierarchy.resolveAbstractDispatch(method.getDeclaringClass(), method);
//                    Set<SootMethod> sootMethods = fastHierarchy.resolveAbstractDispatch(method.getDeclaringClass(), method);
                    for (SootMethod sootMethod : sootMethods) {
                        addNodeToCallGraph(sootMethod,callGraph);
                        addEdgeToCallGraph(entryPoint,sootMethod,callGraph);
                    }

                }
                else {
                    // Once the new method is added and edge created, it is now time to construct CHAAlgorithm for
                    // new (Target) Method
                    constructCHAAlgorithm(callGraph, method, scene);
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
