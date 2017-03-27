package jkind;

import jkind.analysis.LinearChecker;
import jkind.analysis.StaticAnalyzer;
import jkind.engines.Director;
import jkind.engines.ivcs.IvcUtil; 
import jkind.lustre.Node; 
import jkind.lustre.Program;
import jkind.lustre.builders.ProgramBuilder; 
import jkind.translation.InlineSimpleEquations;
import jkind.translation.Specification;
import jkind.translation.Translate; 

public class JKind {
	public static final String EQUATION_NAME = "__addedEQforAsrInconsis_by_JKind__"; 
	public static void main(String[] args) {
		try {
			JKindSettings settings = JKindArgumentParser.parse(args);
			Program program = Main.parseLustre(settings.filename);
			program = setMainNode(program, settings.main);

			StaticAnalyzer.check(program, settings.solver);
			if (!LinearChecker.isLinear(program)) {
				if (settings.pdrMax > 0) {
					StdErr.warning("disabling PDR due to non-linearities");
					settings.pdrMax = 0;
				}
			}

			Node main = Translate.translate(program); 
			if(settings.allAssigned){
				
				//to compare with the results of our first paper, comment the next line
				// the next line is necessary for consistency_checker
				//main = IvcUtil.normalizeAssertions(main);
				
				main = IvcUtil.setIvcArgs(main, IvcUtil.getAllAssigned(main));
			} 
			Specification userSpec = new Specification(main, settings.slicing); 
			Specification analysisSpec = getAnalysisSpec(userSpec, settings);

			new Director(settings, userSpec, analysisSpec).run();
			System.exit(0); // Kills all threads
		} catch (Throwable t) {
			t.printStackTrace();
			System.exit(ExitCodes.UNCAUGHT_EXCEPTION);
		}
	}

	private static Program setMainNode(Program program, String main) {
		if (main == null) {
			return program;
		}

		boolean hasMainNode = program.nodes.stream().anyMatch(n -> n.id.equals(main));
		if (!hasMainNode) {
			StdErr.fatal(ExitCodes.INVALID_OPTIONS, "Unable to find main node '" + main + "'");
		}

		return new ProgramBuilder(program).setMain(main).build();
	}

	private static Specification getAnalysisSpec(Specification userSpec, JKindSettings settings) {
		if (settings.inlining) {
			Node inlined = InlineSimpleEquations.node(userSpec.node);
			return new Specification(inlined, settings.slicing);
		} else {
			return userSpec;
		}
	}
}
