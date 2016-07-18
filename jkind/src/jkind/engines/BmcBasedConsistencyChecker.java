package jkind.engines; 
import java.util.ArrayList; 
import java.util.HashSet; 
import java.util.List; 
import java.util.Set;

import jkind.JKind; 
import jkind.JKindSettings;
import jkind.Output;
import jkind.engines.messages.BaseStepMessage;
import jkind.engines.messages.EngineType;
import jkind.engines.messages.InductiveCounterexampleMessage;
import jkind.engines.messages.InvalidMessage;
import jkind.engines.messages.InvariantMessage;
import jkind.engines.messages.Itinerary;
import jkind.engines.messages.UnknownMessage;
import jkind.engines.messages.ValidMessage;  
import jkind.lustre.Equation;
import jkind.lustre.Expr; 
import jkind.lustre.LustreUtil;
import jkind.lustre.NamedType;
import jkind.lustre.Node; 
import jkind.lustre.VarDecl;
import jkind.lustre.builders.NodeBuilder;
import jkind.sexp.Cons;
import jkind.sexp.Sexp;
import jkind.sexp.Symbol;
import jkind.slicing.Dependency; 
import jkind.solvers.Result; 
import jkind.solvers.UnsatResult;
import jkind.solvers.z3.Z3Solver;
import jkind.translation.Lustre2Sexp;
import jkind.translation.Specification;
import jkind.util.LinkedBiMap;
import jkind.util.StreamIndex;
import jkind.util.Util;

public class BmcBasedConsistencyChecker  extends SolverBasedEngine {
	public static final String NAME = "bmc-consistency-checker";
	private Specification localSpec;   
	private Z3Solver z3Solver;
	private LinkedBiMap<String, Symbol> ivcMap;
	
	public BmcBasedConsistencyChecker(Specification spec, JKindSettings settings, Director director) {
		super(NAME, spec, settings, director); 
	}
	
	@Override
	protected void initializeSolver() {
		solver = getSolver();
		solver.initialize(); 
		z3Solver = (Z3Solver) solver;
	}

	@Override
	public void main() {
		processMessagesAndWaitUntil(() -> properties.isEmpty());
	}

	private void check(ValidMessage vm) {
		for (String property : vm.valid) {
			if (properties.remove(property)) {
				comment("Checking consistency for: " + property);
				solver.push();
				// create an over-approx of the model with IVCs
				// define a new property which is the same as boolean expressions in the transition system
				// we need this over-approx node because we might have several IVCs
				// if proof goes through ==> no inconsistency
				// otherwise ==> it will find an example to show the inconsistency
				Node main = overApproximateWithIvc(property, spec.node, vm.ivc, vm.invariants);
				main = setIvcArgs(main, getAllAssigned(main));   
				localSpec = new Specification(main, settings.noSlicing);  
				ivcMap = Lustre2Sexp.createIvcMap(localSpec.node.ivc); 
				
				for (Symbol e : ivcMap.values()) {
					solver.define(new VarDecl(e.str, NamedType.BOOL));
				}
				
				solver.define(localSpec.getIvcTransitionRelation());
				solver.define(new VarDecl(INIT.str, NamedType.BOOL));  
				checkConsistency(property, vm);
				solver.pop();
			}
		}
	}
 
	private Node overApproximateWithIvc(String prop, Node node, Set<String> ivc, List<Expr> invariants) { 
		List<Expr> assertions = removeAssertions(node.assertions, ivc);
		List<Equation> equations = removeEquations(node.equations, ivc); 
		List<VarDecl> locals = removeVariable(node.locals, equations);
		List<VarDecl> outputs = removeVariable(node.outputs, equations);
		NodeBuilder builder = new NodeBuilder(node);  
		builder.clearProperties().addProperty(prop);
		builder.clearLocals().addLocals(locals);
		builder.clearOutputs().addOutputs(outputs);
		builder.clearEquations().addEquations(equations);
		builder.clearAssertions().addAssertions(assertions); 
		return builder.build();
	}

	private List<Expr> removeAssertions(List<Expr> assertions, Set<String> ivc) {
		List<Expr> ret = new ArrayList<>(); 
		for(Expr asr : assertions){
			if(ivc.contains(asr.toString())){
				ret.add(asr);
			}
		} 
		return ret;
	}

	private List<Equation> removeEquations(List<Equation> equations, Set<String> ivc) {
		List<Equation> ret = new ArrayList<>();
		Set<Dependency> map = new HashSet<>();
		Set<String> depName = new HashSet<>();
		for(String core : ivc){ 
			try{
				map.addAll(spec.dependencyMap.get(core).getSet());
			}catch(NullPointerException e){}
		} 
		for(Dependency d : map){
			depName.add(d.name);
		}
		for(Equation eq : equations){
			if(ivc.contains(eq.lhs.get(0).id)){
				ret.add(eq);
			}else if(depName.contains(eq.lhs.get(0).id)){
				ret.add(eq);
			}
		} 
		return ret; 
	}

	private List<VarDecl> removeVariable(List<VarDecl> vars, List<Equation> equations) {
		List<VarDecl> ret = new ArrayList<>();
		List<String> left = new ArrayList<>();
		for(Equation eq : equations){
			left.add(eq.lhs.get(0).id);
		}
		for(VarDecl var : vars){
			if(left.contains(var.id)){
				ret.add(var);
			}
		}
		return ret; 
	}
	
	private void assertProperty(String prop, int k) {
		solver.assertSexp(new StreamIndex(prop, k).getEncoded());
	}

	private void checkConsistency(String property, ValidMessage vm) {
		createVariables(-1);
		for (int k = 0; k < settings.n; k++) {
			comment("K = " + (k + 1));  
			createVariables(k);
			assertBaseTransition(k);
			Result result  = z3Solver.quickCheckSat(ivcMap.valueList());
			if (result instanceof UnsatResult){
				Output.println("------------------------------------------------------------------");
				Output.println("  Model is inconsistent with property \n         "
									+ property + ", at K = " + k  + " with:"); 
				List<Symbol> unsatCore = ((UnsatResult) result).getUnsatCore();
				for(Symbol s : unsatCore){
					Output.println("    - "+ findRightSide(ivcMap.getKey(s)));
				}
				Output.println("-------------------------------------------------------------------");
				sendValid(property, vm);
				return;
			} 
			assertProperty(property, k);
		}
		
		Output.println("---------------------------------------------------------------------------");
		Output.println("  No inconsistency was found for \n"+
						  "        property " + property + " to the depth of K = " +  settings.n);
		Output.println("----------------------------------------------------------------------------");
		sendValid(property, vm);
	}
	
	private String findRightSide(String ivc) {
		for (Equation eq : localSpec.node.equations){
			if(ivc.equals(eq.lhs.get(0).id)){
				if(ivc.contains(MiniJKind.EQUATION_NAME ) || ivc.contains(JKind.EQUATION_NAME)){
					return "assert (" + eq.expr.toString() +")";
				}else{
					return ivc ;
				}
			}
		}
		return null;
	}
 
	private static List<String> getAllAssigned(Node node) {
		List<String> result = new ArrayList<>();
		result.addAll(Util.getIds(node.locals));
		result.addAll(Util.getIds(node.outputs));
		return result;
	}
	
	private static Node setIvcArgs(Node node, List<String> newSupport) {
		return new NodeBuilder(node).clearIvc().addIvcs(newSupport).build();
	}

	private void sendValid(String valid, ValidMessage vm) {
		Itinerary itinerary = vm.getNextItinerary();
		director.broadcast(new ValidMessage(vm.source, valid, vm.k, vm.invariants, vm.ivc , itinerary, null)); 
	}

	@Override
	protected void handleMessage(BaseStepMessage bsm) {
		// TODO Auto-generated method stub
		
	}

	@Override
	protected void handleMessage(InductiveCounterexampleMessage icm) {
		// TODO Auto-generated method stub
		
	}

	@Override
	protected void handleMessage(InvalidMessage im) {
		// TODO Auto-generated method stub
		
	}

	@Override
	protected void handleMessage(InvariantMessage im) {
		// TODO Auto-generated method stub
		
	}

	@Override
	protected void handleMessage(UnknownMessage um) {
		// TODO Auto-generated method stub
		
	}

	@Override
	protected void handleMessage(ValidMessage vm) {
		if (vm.getNextDestination() == EngineType.BMC_BASED_CONSISTENCY_CHECKER) { 
			check(vm);
		}
		
	}
	
	@Override
	protected void createVariables(int k) {
		for (VarDecl vd : getOffsetVarDecls(k)) {
			solver.define(vd);
		}

		for (VarDecl vd : Util.getVarDecls(localSpec.node)) {
			Expr constraint = LustreUtil.typeConstraint(vd.id, vd.type);
			if (constraint != null) {
				solver.assertSexp(constraint.accept(new Lustre2Sexp(k)));
			}
		}
	}

	@Override
	protected List<VarDecl> getOffsetVarDecls(int k) {
		List<VarDecl> result = new ArrayList<>();
		for (VarDecl vd : Util.getVarDecls(localSpec.node)) {
			StreamIndex si = new StreamIndex(vd.id, k);
			result.add(new VarDecl(si.getEncoded().str, vd.type));
		}
		return result;
	}

	@Override
	protected Sexp getTransition(int k, Sexp init) {
		List<Sexp> args = new ArrayList<>();
		args.add(init);
		args.addAll(getSymbols(getOffsetVarDecls(k - 1)));
		args.addAll(getSymbols(getOffsetVarDecls(k)));
		return new Cons(localSpec.getTransitionRelation().getName(), args);
	}

}
