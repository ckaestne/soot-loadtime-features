/* Soot - a J*va Optimization Framework
 * Copyright (C) 2008 Eric Bodden
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import soot.Body;
import soot.BodyTransformer;
import soot.G;
import soot.Local;
import soot.PackManager;
import soot.PrimType;
import soot.RefLikeType;
import soot.Transform;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.internal.JCastExpr;
import soot.jimple.internal.JEqExpr;
import soot.jimple.internal.JIfStmt;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.scalar.ForwardBranchedFlowAnalysis;

public class MyMain {

	public static void main(String[] args) {
		PackManager.v().getPack("jtp")
				.add(new Transform("jtp.myTransform", new BodyTransformer() {

					protected void internalTransform(Body body, String phase,
							Map options) {
						new MyAnalysis(new ExceptionalUnitGraph(body));
						// use G.v().out instead of System.out so that Soot can
						// redirect this output to the Eclipse console
						G.v().out.println(body.getMethod());
					}

				}));

		soot.Main.main(args);
	}

	public static class FeatureState {
		private String name;

		FeatureState(String name) {
			this.name = name;
		}

		public String toString() {
			return name;
		}
	}

	public static final FeatureState FEATURE = new FeatureState("A");
	public static final FeatureState NOT_FEATURE = new FeatureState("!A");
	public static final FeatureState TRUE = new FeatureState("1");
	public static final FeatureState FALSE = new FeatureState("0");
	public static final FeatureState EXTERNAL_CALL = new FeatureState("E");
	public static final FeatureState TOP = new FeatureState("?");
	public static final FeatureState UNKNOWN = TOP;// alias
	public static final FeatureState BOTTOM = new FeatureState("_");

	public static class AnalysisState {
		Map<Value, FeatureState> variables = new HashMap<Value, MyMain.FeatureState>();
		FeatureState pathCondition = BOTTOM;

		public AnalysisState() {
		}

		public AnalysisState(FeatureState init) {
			this.pathCondition = init;
		}

		@Override
		public boolean equals(Object that) {
			if (that instanceof AnalysisState)
				return ((AnalysisState) that).pathCondition == this.pathCondition
						&& ((AnalysisState) that).variables
								.equals(this.variables);
			return super.equals(that);
		}

		@Override
		public int hashCode() {
			return variables.hashCode() + pathCondition.hashCode();
		}

		@Override
		public String toString() {
			return pathCondition + " -- " + variables;
		}

		public AnalysisState createClone() {
			AnalysisState r = new AnalysisState(pathCondition);
			r.variables.putAll(this.variables);
			return r;
		}

		public AnalysisState merge(AnalysisState that) {
			AnalysisState r = createClone();
			// ideally: new condition = this.condition OR that.condition
			if (this.pathCondition != that.pathCondition)
				r.pathCondition = UNKNOWN;

			for (Entry<Value, FeatureState> var : that.variables.entrySet()) {
				if (!r.variables.containsKey(var.getKey()))
					r.variables.put(var.getKey(), var.getValue());
				else {
					FeatureState stateA = r.variables.get(var.getKey());
					FeatureState stateB = var.getValue();
					FeatureState newState = UNKNOWN;
					if (stateA == stateB)
						newState = stateA;
					// TODO need more generic mechanism, potentially creating
					// choices
					if (stateA == TRUE && stateB == FALSE)
						if (this.pathCondition == FEATURE
								&& that.pathCondition == NOT_FEATURE)
							newState = FEATURE;
						else if (this.pathCondition == NOT_FEATURE
								&& that.pathCondition == FEATURE)
							newState = NOT_FEATURE;
					if (stateA == FALSE && stateB == TRUE)
						if (this.pathCondition == FEATURE
								&& that.pathCondition == NOT_FEATURE)
							newState = NOT_FEATURE;
						else if (this.pathCondition == NOT_FEATURE
								&& that.pathCondition == FEATURE)
							newState = FEATURE;
					r.variables.put(var.getKey(), newState);
				}

			}

			return r;
		}
	}

	public static class MyAnalysis extends
			ForwardBranchedFlowAnalysis<AnalysisState> {

		public MyAnalysis(ExceptionalUnitGraph exceptionalUnitGraph) {
			super(exceptionalUnitGraph);
			doAnalysis();
		}

		@Override
		protected void flowThrough(AnalysisState in, Unit unit,
				List<AnalysisState> fallOut, List<AnalysisState> branchOuts) {
			AnalysisState out = in.createClone();
			AnalysisState outBranch = in.createClone();
			Stmt s = (Stmt) unit;

			if (s.containsInvokeExpr()) {
				InvokeExpr inv = s.getInvokeExpr();
				if (inv.getMethodRef().name().equals("makeFeature")) {
					out.variables.put(inv.getArg(0), FEATURE);
				}
			}
			if (s instanceof JIfStmt) {
				JIfStmt ifStmt = (JIfStmt) s;
				handleIfStmt(ifStmt, in, out, outBranch);
			}
			// if we have a definition (assignment) statement to a ref-like
			// type, handle it,
			// i.e. assign it TOP, except in the following special cases:
			// x=null, assign NULL
			// x=@this or x= new... assign NON_NULL
			// x=y, copy the info for y (for locals x,y)
			if (s instanceof DefinitionStmt) {
				DefinitionStmt defStmt = (DefinitionStmt) s;
				if (defStmt.getLeftOp().getType() instanceof PrimType) {
					handlePrimTypeAssignment(defStmt, out);
				}
			}

			// now copy the computed info to all successors
			for (Iterator<AnalysisState> it = fallOut.iterator(); it.hasNext();) {
				copy(out, it.next());
			}
			for (Iterator<AnalysisState> it = branchOuts.iterator(); it
					.hasNext();) {
				copy(outBranch, it.next());
			}
		}

		private void handlePrimTypeAssignment(DefinitionStmt assignStmt,
				AnalysisState out) {
			Value left = assignStmt.getLeftOp();
			Value right = assignStmt.getRightOp();

			// unbox casted value
			if (right instanceof JCastExpr) {
				JCastExpr castExpr = (JCastExpr) right;
				right = castExpr.getOp();
			}

			FeatureState valueFeature = evalCondition(right, out);
			out.variables.put(left, valueFeature);
		}

		private void handleIfStmt(JIfStmt ifStmt, AnalysisState in,
				AnalysisState out, AnalysisState outBranch) {
			Value condition = ifStmt.getCondition();
			// TODO reduce complex conditions
			FeatureState conditionPath = evalCondition(condition, in);
			// in.variables.get(condition);

			if (conditionPath == FEATURE) {
				out.pathCondition = FEATURE;
				outBranch.pathCondition = NOT_FEATURE;
			}
			if (conditionPath == NOT_FEATURE) {
				out.pathCondition = NOT_FEATURE;
				outBranch.pathCondition = FEATURE;
			}
		}

		private FeatureState evalCondition(Value condition, AnalysisState in) {
			if (condition instanceof JEqExpr) {
				return evalEqCondition((JEqExpr) condition, in);
			}
			if (condition instanceof IntConstant) {
				return ((IntConstant) condition).value == 0 ? FALSE : TRUE;
			}
			if (condition instanceof Local) {
				if (in.variables.containsKey(condition))
					return in.variables.get(condition);
			}

			return UNKNOWN;
		}

		private FeatureState evalEqCondition(JEqExpr eqExpr, AnalysisState in) {
			Value left = eqExpr.getOp1();
			Value right = eqExpr.getOp2();

			Value val = null;
			if (left instanceof IntConstant && ((IntConstant) left).value == 0) {
				val = right;
			} else if (right instanceof IntConstant
					&& ((IntConstant) right).value == 0) {
				val = left;
			}

			// if we compare a local with numeric constant then process
			// further...
			if (val != null && val instanceof Local) {
				FeatureState valFeature = in.variables.get(val);
				if (valFeature == FEATURE)
					return NOT_FEATURE;
				else if (valFeature == NOT_FEATURE)
					return FEATURE;
			}

			return UNKNOWN;
		}

		@Override
		protected AnalysisState newInitialFlow() {
			return new AnalysisState();
		}

		@Override
		protected AnalysisState entryInitialFlow() {
			return new AnalysisState(EXTERNAL_CALL);
		}

		@Override
		protected void merge(AnalysisState in1, AnalysisState in2,
				AnalysisState out) {
			copy(in1.merge(in2), out);
		}

		@Override
		protected void copy(AnalysisState source, AnalysisState dest) {
			dest.pathCondition = source.pathCondition;
			dest.variables = new HashMap<>(source.variables);
		}

	}

}