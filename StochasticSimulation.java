package hu.bme.mit.inf.dslreasoner.viatrasolver.reasoner;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.function.Consumer;

import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.viatra.query.runtime.api.IPatternMatch;
import org.eclipse.viatra.query.runtime.api.ViatraQueryEngine;
import org.eclipse.viatra.query.runtime.api.ViatraQueryMatcher;
import org.eclipse.viatra.query.runtime.emf.EMFScope;
import org.eclipse.viatra.transformation.runtime.emf.rules.batch.BatchTransformationRule;
import org.eclipse.xtend2.lib.StringConcatenation;

import hu.bme.mit.inf.dslreasoner.logic.model.builder.DocumentationLevel;
import hu.bme.mit.inf.dslreasoner.logic.model.builder.LogicModelInterpretation;
import hu.bme.mit.inf.dslreasoner.logic.model.builder.LogicReasoner;
import hu.bme.mit.inf.dslreasoner.logic.model.builder.LogicReasonerException;
import hu.bme.mit.inf.dslreasoner.logic.model.builder.LogicSolverConfiguration;
import hu.bme.mit.inf.dslreasoner.logic.model.logiclanguage.DefinedElement;
import hu.bme.mit.inf.dslreasoner.logic.model.logicproblem.LogicProblem;
import hu.bme.mit.inf.dslreasoner.logic.model.logicresult.LogicResult;
import hu.bme.mit.inf.dslreasoner.logic.model.logicresult.LogicresultFactory;
import hu.bme.mit.inf.dslreasoner.logic.model.logicresult.ModelResult;
import hu.bme.mit.inf.dslreasoner.logic.model.logicresult.Statistics;
import hu.bme.mit.inf.dslreasoner.viatrasolver.logic2viatra.ModelGenerationStatistics;
import hu.bme.mit.inf.dslreasoner.viatrasolver.logic2viatra.cardinality.ScopePropagator;
import hu.bme.mit.inf.dslreasoner.viatrasolver.partialinterpretationlanguage.PartialInterpretationInitialiser;
import hu.bme.mit.inf.dslreasoner.viatrasolver.partialinterpretationlanguage.partialinterpretation.PartialComplexTypeInterpretation;
import hu.bme.mit.inf.dslreasoner.viatrasolver.partialinterpretationlanguage.partialinterpretation.PartialInterpretation;
import hu.bme.mit.inf.dslreasoner.viatrasolver.partialinterpretationlanguage.partialinterpretation.PartialRelationInterpretation;
import hu.bme.mit.inf.dslreasoner.viatrasolver.partialinterpretationlanguage.partialinterpretation.PartialTypeInterpratation;
import hu.bme.mit.inf.dslreasoner.viatrasolver.partialinterpretationlanguage.visualisation.PartialInterpretationVisualisation;
import hu.bme.mit.inf.dslreasoner.viatrasolver.partialinterpretationlanguage.visualisation.PartialInterpretationVisualiser;
import hu.bme.mit.inf.dslreasoner.viatrasolver.reasoner.dse.PartialModelAsLogicInterpretation;
import hu.bme.mit.inf.dslreasoner.viatrasolver.reasoner.dse.SolutionCopier;
import hu.bme.mit.inf.dslreasoner.workspace.ReasonerWorkspace;

public class StochasticSimulation extends LogicReasoner{
	private final PartialInterpretationInitialiser initialiser = new PartialInterpretationInitialiser();
	private final ModelGenerationMethodProvider modelGenerationMethodProvider = new ModelGenerationMethodProvider();

	@Override
	public LogicResult solve(LogicProblem problem, LogicSolverConfiguration configuration, ReasonerWorkspace workspace)
			throws LogicReasonerException {

		long start = System.nanoTime();
		
		final ViatraReasonerConfiguration viatraConfig = this.asConfig(configuration);
		final PartialInterpretation currentSolution = this.initialiser.initialisePartialInterpretation(problem, viatraConfig.typeScopes).getOutput();
		currentSolution.setProblemConainer(problem);
		currentSolution.getPartialtypeinterpratation();
		ModelGenerationStatistics statistics = new ModelGenerationStatistics();
		final ScopePropagator scopePropagator = new ScopePropagator(currentSolution, statistics);
		final ModelGenerationMethod method = this.modelGenerationMethodProvider.createModelGenerationMethod(problem, currentSolution, workspace, viatraConfig);
		
		ViatraQueryEngine engine = ViatraQueryEngine.on(new EMFScope(currentSolution));
		double edgeNodeRatio = viatraConfig.edgeNodeRatio;
		double corrigatedEdgeNodeR = (edgeNodeRatio - 1.5) / 2;
		int maxSteps = viatraConfig.maxSteps;
		ArrayList<Boolean> isVertexMatcher = new ArrayList<>();
		ArrayList<ViatraQueryMatcher<?>> matcherList = new ArrayList<>();
		Map<ViatraQueryMatcher,Consumer> matcher2Action = new HashMap<>();
		for (BatchTransformationRule<?, ?> objectRefinementRule : method.getObjectRefinementRules()) {
			ViatraQueryMatcher<?> matcher = engine.getMatcher(objectRefinementRule.getPrecondition());
			Consumer<?> action = objectRefinementRule.getAction();
			matcher2Action.put(matcher,action);
			matcherList.add(matcher);
			isVertexMatcher.add(true);
		}
		for (BatchTransformationRule<?, ?> relationRefinementRule : method.getRelationRefinementRules()) {
			ViatraQueryMatcher<?> matcher = engine.getMatcher(relationRefinementRule.getPrecondition());
			Consumer<?> action = relationRefinementRule.getAction();
			matcher2Action.put(matcher,action);
			matcherList.add(matcher);
			isVertexMatcher.add(false);
		}
		ArrayList<Boolean> isVertexMatch = new ArrayList<>();
		ArrayList<IPatternMatch> currentMatches = new ArrayList<>();
		Map<IPatternMatch,ViatraQueryMatcher<?>> match2Matcher = new HashMap<>();
		if(maxSteps < 1) maxSteps = 100;
		for(int i = 0; i < maxSteps; ++i)
		{
			if(currentSolution.getMinNewElements() == 0) break;
			isVertexMatch.clear();
			currentMatches.clear();
			ArrayList<IPatternMatch> tempMatches = new ArrayList<>();
			for(int j = 0; j < matcherList.size(); ++j)
			{
				ViatraQueryMatcher<?> tempMatcher = matcherList.get(j);
				tempMatches.clear();
				tempMatches.addAll(tempMatcher.getAllMatches());
				currentMatches.addAll(tempMatches);
				Boolean isVertex = isVertexMatcher.get(j);
				for(int k = 0; k < tempMatches.size(); ++k)
				{
					isVertexMatch.add(isVertex);
					match2Matcher.put(tempMatches.get(k), tempMatcher);
				}
			}
			int allEdgeCnt = 0;
			int allVertexCnt = 0;
			EList<DefinedElement> newElements = currentSolution.getNewElements();
			allVertexCnt = newElements.size();
			if((System.nanoTime()-start) / 1000000 > 1200000)
			{
				System.out.println("The final size of the model is " + allVertexCnt);
				break;
			}
			
			for(PartialRelationInterpretation r2 : currentSolution.getPartialrelationinterpretation()) {
				allEdgeCnt += r2.getRelationlinks().size();
			}
			//System.out.println("Vertices: " + allVertexCnt + " edges: " + allEdgeCnt);
			Random rand = new Random();
			if(currentMatches.size() > 0)
			{
				int vertexCnt = 0;
				int edgeCnt = 0;
				for(int q = 0; q < currentMatches.size(); ++q)
				{
					if(!isVertexMatch.get(q))
					{
						vertexCnt = q;
						edgeCnt = currentMatches.size() - vertexCnt;
						break;
					}
					if(q+1 == currentMatches.size())vertexCnt = q+1;
				}
				double vertexWeightSum = 0;
				double edgeWeightSum = 0;
				double vertexWeight = 0;
				double edgeWeight = 0;
				if(vertexCnt > 0)
				{
					vertexWeightSum = vertexCnt;
					vertexWeight = 1;
					if(edgeCnt > 0 && corrigatedEdgeNodeR > 0) {
						if(allEdgeCnt > 0 && allVertexCnt > 0) {
							double currentEdgeNodeRatio = (double)allEdgeCnt / allVertexCnt;
							edgeWeightSum = vertexCnt * (corrigatedEdgeNodeR + 1) * Math.pow(edgeNodeRatio / currentEdgeNodeRatio,4)- vertexCnt;
							if(edgeWeightSum < 0) edgeWeightSum = 0;
							//System.out.println("Current edge-node ratio: " + currentEdgeNodeRatio + "      edge chance: " + edgeWeightSum/(edgeWeightSum+vertexWeightSum));
						}
						else{
							edgeWeightSum =vertexCnt * corrigatedEdgeNodeR;
						}
						edgeWeight = edgeWeightSum / edgeCnt;
					}
				}else {
					edgeWeightSum = edgeCnt;
					edgeWeight = 1;
				}
				int index = 0;
				double border = rand.nextDouble() * (vertexWeightSum + edgeWeightSum);
				for(int q = 0; q < currentMatches.size(); ++q)
				{
					if(isVertexMatch.get(q)) border -= vertexWeight;
					else border -= edgeWeight;
					if(border <= 0)
					{
						index = q;
						break;
					}
				}
				if(index == 0) index = currentMatches.size() - 1;
				IPatternMatch selectedMatch = currentMatches.get(index);
				ViatraQueryMatcher<?> selectedMatcher = match2Matcher.get(selectedMatch);
				matcher2Action.get(selectedMatcher).accept(selectedMatch);
			}
			else break;
			//visualiseCurrentState(viatraConfig, workspace, emptySolution, i+1);
		}
		LogicresultFactory factory = LogicresultFactory.eINSTANCE;
		Statistics statistics2 = factory.createStatistics();
		statistics2.setSolverTime((int) ((System.nanoTime()-start) / 1000000));
		ModelResult res = factory.createModelResult();
		res.setProblem(problem);
		res.setTrace(null);
		res.getRepresentation().add(currentSolution);
		res.setStatistics(statistics2);
		return res;
	}
	
	public void visualiseCurrentState(ViatraReasonerConfiguration configuration, ReasonerWorkspace workspace,
			PartialInterpretation partial, int cnt) {
		PartialInterpretationVisualiser partialInterpretatioVisualiser = configuration.debugConfiguration.partialInterpretatioVisualiser;
		if(partialInterpretatioVisualiser != null && workspace != null) {
			PartialInterpretationVisualisation visualisation = partialInterpretatioVisualiser.visualiseConcretization(partial);
			String name = String.format("state%09d", cnt);
			visualisation.writeToFile(workspace, name + ".png");
			workspace.writeModel((EObject) partial, name + ".xmi");
		}
	}
	
	private ViatraReasonerConfiguration asConfig(final LogicSolverConfiguration configuration) {
	    if ((configuration instanceof ViatraReasonerConfiguration)) {
	      return ((ViatraReasonerConfiguration)configuration);
	    } else {
	      StringConcatenation _builder = new StringConcatenation();
	      _builder.append("Wrong configuration. Expected: ");
	      String _name = ViatraReasonerConfiguration.class.getName();
	      _builder.append(_name);
	      _builder.append(", but got: ");
	      String _name_1 = configuration.getClass().getName();
	      _builder.append(_name_1);
	      _builder.append("\"");
	      throw new IllegalArgumentException(_builder.toString());
	    }
	  }

	@Override
	public List<? extends LogicModelInterpretation> getInterpretations(ModelResult modelResult) {
		List<PartialModelAsLogicInterpretation> result = new LinkedList<PartialModelAsLogicInterpretation>();
		for(int index=0; index<modelResult.getRepresentation().size();index++) {
			Map<EObject,EObject> forwardMap = new HashMap<>();
			PartialInterpretation x = (PartialInterpretation) modelResult.getRepresentation().get(index);
			TreeIterator<EObject> i = x.eAllContents();
			while(i.hasNext())
			{
				EObject a = i.next();
				forwardMap.put(a, a);
			}
			forwardMap.put(x, x);
			PartialModelAsLogicInterpretation model = new PartialModelAsLogicInterpretation(x, forwardMap);
			result.add(model);
		}
		return result;
	}

}
