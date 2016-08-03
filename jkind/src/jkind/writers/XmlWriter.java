package jkind.writers;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintWriter;
import java.util.List;
import java.util.Map;
import java.util.Set;

import jkind.engines.ivcs.messages.ConsistencyMessage;
import jkind.interval.BoolInterval;
import jkind.interval.NumericInterval;
import jkind.lustre.Expr;
import jkind.lustre.Type;
import jkind.lustre.values.BooleanValue;
import jkind.lustre.values.Value;
import jkind.results.Counterexample;
import jkind.results.Signal;
import jkind.util.Tuple;
import jkind.util.Util;

public class XmlWriter extends Writer {
	private final PrintWriter out;
	private final Map<String, Type> types;

	public XmlWriter(String filename, Map<String, Type> types, boolean useStdout)
			throws FileNotFoundException {
		if (useStdout) {
			this.out = new PrintWriter(System.out, true);
		} else {
			this.out = new PrintWriter(new FileOutputStream(filename));
		}
		this.types = types;
	}

	@Override
	public void begin() {
		out.println("<?xml version=\"1.0\"?>");
		out.println("<Results xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\">");
	}

	@Override
	public void end() {
		out.println("</Results>");
		out.close();
	}

	@Override
	public void writeValid(List<String> props, String source, int k, double runtime,
			List<Expr> invariants, Set<String> ivc, List<Tuple<Set<String>, List<String>>> allIvcs) {
		for (String prop : props) {
			writeValid(prop, source, k, runtime, invariants, ivc, allIvcs);
		}
	}

	public void writeValid(String prop, String source, int k, double runtime,
			List<Expr> invariants, Set<String> ivc, List<Tuple<Set<String>, List<String>>> allIvcs) {
		out.println("  <Property name=\"" + prop + "\">");
		out.println("    <Runtime unit=\"sec\">" + runtime + "</Runtime>");
		out.println("    <Answer source=\"" + source + "\">valid</Answer>");
		out.println("    <K>" + k + "</K>");
		
		if(allIvcs.isEmpty()){
			for (Expr invariant : invariants) {
				out.println("    <Invariant>" + escape(invariant) + "</Invariant>");
			}
			for (String supp : ivc) {
				out.println("    <Ivc>" + supp + "</Ivc>");
			}
		}else{
			out.println("    <NumberOfIVCs>" + allIvcs.size() + "</NumberOfIVCs>");
			int count = 1;
			 
			for (String supp : ivc) {
				out.println("    <MustElem>" + supp + "</MustElem>");
			}
			
			for(Tuple<Set<String>, List<String>> ivcSet : allIvcs){
				out.println("    <IvcSet number=\"" + count + "\">");
				for (String invariant : ivcSet.secondElement()) {
					out.println("    <Invariant>" + invariant + "</Invariant>");
				}
				for (String supp : ivcSet.firstElement()) {
					out.println("    <Ivc>" + supp + "</Ivc>");
				}
				out.println("    </IvcSet>");
				count++;
			}
		}
		
		out.println("  </Property>");
		out.flush();
	}

	private String escape(Expr invariant) {
		return invariant.toString().replace("<", "&lt;").replace(">", "&gt;");
	}

	@Override
	public void writeInvalid(String prop, String source, Counterexample cex,
			List<String> conflicts, double runtime) {
		out.println("  <Property name=\"" + prop + "\">");
		out.println("    <Runtime unit=\"sec\">" + runtime + "</Runtime>");
		out.println("    <Answer source=\"" + source + "\">falsifiable</Answer>");
		out.println("    <K>" + cex.getLength() + "</K>");
		writeCounterexample(cex);
		writeConflicts(conflicts);
		out.println("  </Property>");
		out.flush();
	}

	private void writeConflicts(List<String> conflicts) {
		if (conflicts.isEmpty()) {
			return;
		}

		out.println("    <Conflicts>");
		for (String conflict : conflicts) {
			out.println("      <Conflict>" + conflict + "</Conflict>");
		}
		out.println("    </Conflicts>");
	}

	private void writeUnknown(String prop, int trueFor, Counterexample cex, double runtime) {
		out.println("  <Property name=\"" + prop + "\">");
		out.println("    <Runtime unit=\"sec\">" + runtime + "</Runtime>");
		out.println("    <Answer>unknown</Answer>");
		out.println("    <TrueFor>" + trueFor + "</TrueFor>");
		if (cex != null) {
			out.println("    <K>" + cex.getLength() + "</K>");
			writeCounterexample(cex);
		}
		out.println("  </Property>");
		out.flush();
	}

	private void writeCounterexample(Counterexample cex) {
		out.println("    <Counterexample>");
		for (Signal<Value> signal : cex.getSignals()) {
			writeSignal(cex.getLength(), signal);
		}
		out.println("    </Counterexample>");
	}

	private void writeSignal(int k, Signal<Value> signal) {
		String name = signal.getName();
		Type type = types.get(name);
		out.println("      <Signal name=\"" + name + "\" type=\"" + type + "\">");
		for (int i = 0; i < k; i++) {
			Value value = signal.getValue(i);
			if (!Util.isArbitrary(value)) {
				out.println("        <Value time=\"" + i + "\">" + formatValue(value) + "</Value>");
			}
		}
		out.println("      </Signal>");
	}

	/**
	 * pkind prints booleans as 0/1. We do the same for compatibility, but we
	 * should eventually switch to true/false
	 */
	private String formatValue(Value value) {
		if (value instanceof BooleanValue) {
			BooleanValue bv = (BooleanValue) value;
			return bv.value ? "1" : "0";
		}
		if (value instanceof NumericInterval) {
			NumericInterval ni = (NumericInterval) value;
			return "<Interval low=\"" + ni.getLow() + "\" high=\"" + ni.getHigh() + "\"/>";
		}
		if (value instanceof BoolInterval) {
			BoolInterval bi = (BoolInterval) value;
			return bi.isTrue() ? "1" : "0";
		} else {
			return value.toString();
		}
	}

	@Override
	public void writeUnknown(List<String> props, int trueFor,
			Map<String, Counterexample> inductiveCounterexamples, double runtime) {
		for (String prop : props) {
			writeUnknown(prop, trueFor, inductiveCounterexamples.get(prop), runtime);
		}
	}

	@Override
	public void writeBaseStep(List<String> props, int k) {
		out.println("  <Progress source=\"bmc\" trueFor=\"" + k + "\">");
		for (String prop : props) {
			out.println("    <PropertyProgress name=\"" + prop + "\"/>");
		}
		out.println("  </Progress>");
		out.flush();
	}

	@Override
	public void writeInconsistent(String prop, String source, int k, double runtime) {
		out.println("  <Property name=\"" + prop + "\">");
		out.println("    <Runtime unit=\"sec\">" + runtime + "</Runtime>");
		out.println("    <Answer source=\"" + source + "\">inconsistent</Answer>");
		out.println("    <K>" + k + "</K>");
		out.println("  </Property>");
		out.flush();
	}

	@SuppressWarnings({ "incomplete-switch", "unchecked" })
	@Override
	public void writeConsistencyCheckerResults(ConsistencyMessage cm) {
		switch(cm.getStatus()){
			case CONSISTENT: 
				return;
				
			case UC: 
				out.println("    <Inconsistencies>");  
				for(String c : (Set<String>)cm.getConsistencyMsg()){
					out.println("      <Inconsistency>" + c + "</Inconsistency>"); 
				} 
				out.println("    </Inconsistencies>");  
				break;
				
			case CEX:
				out.println("    <InconsistencyWithCounterexample>"); 
				Counterexample cex = ((List<Counterexample>)cm.getConsistencyMsg()).get(0);
				for (Signal<Value> signal : cex.getSignals()) {
					writeSignal(cex.getLength(), signal);
				}
				out.println("    </InonsistencyCounterexample>");
				break;
		}
		out.flush();
	}
 
}
