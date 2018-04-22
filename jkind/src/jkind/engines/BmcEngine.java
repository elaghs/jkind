package jkind.engines;

import java.io.File;
import java.io.FileOutputStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import jkind.ExitCodes;
import jkind.JKindSettings;
import jkind.engines.ivcs.IvcUtil;
import jkind.engines.messages.BaseStepMessage;
import jkind.engines.messages.InductiveCounterexampleMessage;
import jkind.engines.messages.InvalidMessage;
import jkind.engines.messages.InvariantMessage;
import jkind.engines.messages.Itinerary;
import jkind.engines.messages.UnknownMessage;
import jkind.engines.messages.ValidMessage;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.NamedType;
import jkind.lustre.VarDecl;
import jkind.sexp.Cons;
import jkind.sexp.Sexp;
import jkind.sexp.Symbol;
import jkind.solvers.Model;
import jkind.solvers.Result;
import jkind.solvers.SatResult;
import jkind.solvers.UnknownResult;
import jkind.solvers.UnsatResult;
import jkind.translation.Lustre2Sexp;
import jkind.translation.Specification;
import jkind.util.LinkedBiMap;
import jkind.util.SexpUtil;
import jkind.util.StreamIndex;

public class BmcEngine extends SolverBasedEngine {
	public static final String NAME = "bmc";
	private List<String> validProperties = new ArrayList<>();
	private List<Expr> validPropsExpr = new ArrayList<>();;
	private List<Expr> propertiesExpr = string2Expr(properties);
	private final LinkedBiMap<String, Symbol> ivcMap;
	
	public BmcEngine(Specification spec, JKindSettings settings, Director director) {
		super(NAME, spec, settings, director);
		ivcMap = Lustre2Sexp.createIvcMap(spec.node.ivc);  
	}
	
	@Override
	protected void initializeSolver() {
		solver = getSolver();
		solver.initialize(); 
		for (Symbol e : ivcMap.values()) {
			solver.define(new VarDecl(e.str, NamedType.BOOL)); 
		} 
		solver.define(spec.getTransitionRelation());
		solver.define(new VarDecl(INIT.str, NamedType.BOOL));
	}

	@Override
	public void main() {
		createVariables(-1);
		//solver.assertSexp(SexpUtil.conjoin(ivcMap.valueList()));
		for (int k = 0; k < settings.n; k++) {
			comment("K = " + (k + 1));
			processMessages();
			if (properties.isEmpty()) {
				return;
			}
			createVariables(k);
			assertBaseTransition(k);

			checkProperties(k);
			assertProperties(k);
		}
		sendUnknown(properties);
	}
	

	private void checkProperties(int k) {
		Result result;
		do {
			//result = solver.query(StreamIndex.conjoinEncodings(properties, k));
			//Sexp query = SexpUtil.conjoinInvariants(propertiesExpr, k - 1);
			//result = solver.unsatQuery(ivcMap.valueList(), getBaseIvcQuery(prop, k)); 
			result = solver.unsatQuery(ivcMap.valueList(), StreamIndex.conjoinEncodings(properties, k));
			if (result instanceof SatResult || result instanceof UnknownResult) {
				Model model = getModel(result);
				if (model == null) {
					sendUnknown(properties);
					properties.clear();
					break;
				}
				
				List<String> bad = getFalseProperties(properties, k, model);
				properties.removeAll(bad);
				
				if (result instanceof SatResult) {
					sendInvalid(bad, k, model);
				} else {
					sendUnknown(bad);
				} 
			} else if (result instanceof UnsatResult){  
				List<Symbol> unsatCore = ((UnsatResult) result).getUnsatCore();
				writeToXmlAllIvcs(IvcUtil.getIvcNames(ivcMap, unsatCore), k); 
			}
		} while (!properties.isEmpty() && result instanceof SatResult);

		sendBaseStep(k);
	}

	private void sendInvalid(List<String> invalid, int k, Model model) {
		Itinerary itinerary = director.getInvalidMessageItinerary();
		director.broadcast(new InvalidMessage(getName(), invalid, k + 1, model, itinerary));
	}

	private void sendBaseStep(int k) {
		director.broadcast(new BaseStepMessage(k + 1, properties));
	}

	private void sendUnknown(List<String> unknown) {
		director.receiveMessage(new UnknownMessage(getName(), unknown));
	}

	private void assertProperties(int k) {
		assertProperties(propertiesExpr, k);
		//assertProperties(validPropsExpr, k);
	}

	private void assertProperties(List<Expr> properties, int k) {
		for (Expr prop : properties) {
			//solver.assertSexp(new StreamIndex(prop, k).getEncoded());
			solver.assertSexp(prop.accept(new Lustre2Sexp(k))); 
		}
		
		/*for (Entry<String, Symbol> entry : ivcMap.entrySet()) {
			solver.assertSexp(createConditional(entry, k));
		}*/
	}
	
	private Sexp createConditional(Entry<String, Symbol> entry, int k) { 
		Symbol actLit = entry.getValue();
		Sexp ivc = new IdExpr(entry.getKey()).accept(new Lustre2Sexp(k));
		return new Cons("=>", actLit, ivc);
	}

	@Override
	protected void handleMessage(BaseStepMessage bsm) {
	}

	@Override
	protected void handleMessage(InductiveCounterexampleMessage icm) {
	}

	@Override
	protected void handleMessage(InvalidMessage im) {
		properties.removeAll(im.invalid);
	}

	@Override
	protected void handleMessage(InvariantMessage im) {
	}

	@Override
	protected void handleMessage(UnknownMessage um) {
	}

	@Override
	protected void handleMessage(ValidMessage vm) {
		properties.removeAll(vm.valid);
		validProperties.addAll(vm.valid);
		validPropsExpr.addAll(string2Expr(vm.valid));
	}
	
	private List<Expr> string2Expr(List<String> p){
		List<Expr> prop = new ArrayList<>();
		for (String s : p){
			prop.add(new IdExpr(s));
		}
		return prop;
	}
	
	 
	private void writeToXmlAllIvcs(Set<String> cores, int k) {
 		String xmlFilename = settings.filename + "_bvc.xml";  

		try (PrintWriter out = new PrintWriter(new FileOutputStream(new File(xmlFilename), true))) { 
			out.println("<Results>");

			//out.println("   <Time unit=\"sec\">" + d + "</Time>");
			out.println("   <Depth>" + k + "</Depth>");   
			for (String s : cores) {
				out.println("   <BVC>" + s + "</BVC>");
			}
			out.println("</Results>");
			out.flush(); 
			out.close(); 
		} catch (Throwable t) { 
			t.printStackTrace();
			System.exit(ExitCodes.UNCAUGHT_EXCEPTION);
		}
		
} 
}
