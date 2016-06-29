package jkind;


public class JKindSettings extends Settings {
	public int n = Integer.MAX_VALUE;
	public int timeout = Integer.MAX_VALUE;
	
	public boolean miniJkind = false;
	public boolean excel = false;
	public boolean xml = false;
	public boolean xmlToStdout = false;
	
	public boolean boundedModelChecking = true;
	public boolean kInduction = true;
	public boolean invariantGeneration = true;
    public int pdrMax = 1;
	public boolean inductiveCounterexamples = false;
	public boolean reduceIvc = false;
	public boolean allIvcs = false;
	public boolean smoothCounterexamples = false;
    public boolean intervalGeneralization = false;
    public boolean inline = true;
	
	public SolverOption solver = SolverOption.SMTINTERPOL;
	public boolean scratch = false;

	public String writeAdvice = null;
	public String readAdvice = null;
	public boolean allIvcs2 = false;
	public boolean noSlicing = false;
	public boolean allAssigned = false;
}
