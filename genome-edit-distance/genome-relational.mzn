include "circuit.mzn";

%------------Parameters------------
int: planLength; %The number of steps we're looking for here. Left in for backwards compat, ignored
int: genomeLength;
int: costCap;
int: inversionPenalty;
int: transpositionPenalty = 2;
int: transversionPenalty = 2;

set of int: geneValues = 1..genomeLength;
set of int: stepIndices = 1..(genomeLength);
set of int: stateIndices = 1..(genomeLength+1);
set of int: sign = {1} union {-1};
set of int: cost = {0, inversionPenalty,transpositionPenalty, transversionPenalty};

array[geneValues] of int: initialGenome;
array[geneValues] of int: goalGenome;

%------------Variables------------
%--States--
array[stateIndices, geneValues] of var sign: geneSign; %geneSign[t,i] = sign of gene with value i at step t.
array[stateIndices, geneValues] of var geneValues: leftNeighbour; %The relational encoding array. i is left of leftNeighbour[i]
array[stateIndices, geneValues] of var geneValues: rightNeighbour; %The other relational encoding array. i is right of rightNeighbour[i]

%------------Operations------------
array[stepIndices] of var bool: inversionTookPlace; %Whether we flipped on this step
array[stepIndices] of var geneValues: operationStart;
array[stepIndices] of var geneValues: operationEnd;
array[stepIndices] of var geneValues: operationTarget; %the block goes before the target

%------------Action costs------------
array[stepIndices] of var cost: actionCost;


%------------Predicates------------

%isLeftNeighbour(t,g1,g2): true if g1 is the left neighbour of g2 at time step t
predicate isLeftNeighbour(var int: t, var int: g1, var int: g2) =  leftNeighbour[t,abs(g2)] = abs(g1);
predicate isLeftNeighbourConstant(int: t, int: g1, int: g2) =  leftNeighbour[t,abs(g2)] = abs(g1);

%whether the left neighbour changes from t -> t+1
predicate leftNeighbourChanges(var int: t, var int: g) = (leftNeighbour[t,g] != leftNeighbour[t+1,g]);
predicate rightNeighbourChanges(var int: t, var int: g) = (rightNeighbour[t,g] != rightNeighbour[t+1,g]);
predicate neighbourChanges(var int: t, var int: g) = leftNeighbourChanges(t,g) \/ rightNeighbourChanges(t,g);

%for transposition operations, whether the transposition operation is actually displacing anything
predicate operationIsMoving(var int: t) = not isLeftNeighbour(t, operationEnd[t], operationTarget[t]);

%Whether the gene's neighbour is allowed to change at this step.
%We allow inverted gene segments left and right neighbours to change - but only to swap. This is done later.
predicate leftNeighbourChangeAllowed(var int: t, var int: g) = (g=operationTarget[t]) \/ (g=operationStart[t]) \/ (g=rightNeighbour[t,operationEnd[t]]) \/ partOfInversion(t,g);
predicate rightNeighbourChangeAllowed(var int: t, var int: g) = (g=leftNeighbour[t,operationTarget[t]]) \/ (g=leftNeighbour[t,operationStart[t]]) \/ (g=operationEnd[t])  \/ partOfInversion(t,g);

%Inversion operation sign inference
predicate partOfInversion(var int: t, var int: g) = geneSign[t,g] != geneSign[t+1,g];
predicate widthOneOperation(var int: t) = operationStart[t] = operationEnd[t];

%Action predicates
%Based on the plan, come up with the actions
predicate inversionAction(var int: t) = ((not operationIsMoving(t)) /\ inversionTookPlace[t]);	%Vanilla inversion (no moving)
predicate transpositionAction(var int: t) = (operationIsMoving(t) /\ (not inversionTookPlace[t])); %Vanilla transposition (no inverting)
predicate transversionAction(var int: t) = (operationIsMoving(t) /\ inversionTookPlace[t]);	%Transversion (moving and inverting)
predicate noAction(var int: t) = ((not operationIsMoving(t)) /\ (not inversionTookPlace[t]));	%No action (not moving, not inverting)

%================Constraints================
%---------INITIAL AND GOAL GENOME---------
%initialGenome must be reflected in leftNeighbour array
constraint forall(g in geneValues) (
    isLeftNeighbourConstant(1,initialGenome[g],initialGenome[g+1])
) /\ (
    isLeftNeighbourConstant(1,initialGenome[genomeLength],initialGenome[1])
);

%goalGenome must be reflected in leftNeighbour array
constraint
(
    %Regular case
    forall(g in geneValues) (
        isLeftNeighbourConstant(max(stateIndices),goalGenome[g],goalGenome[g+1])
    ) /\ (
        isLeftNeighbourConstant(max(stateIndices),goalGenome[genomeLength],goalGenome[1])
    ) /\ (geneTakesGoalGenomeSign(1)) %If we go normally, don't change the input signs
) \/ (
    %Completely inverted case
    forall(g in geneValues) (
        isLeftNeighbourConstant(max(stateIndices),goalGenome[g+1],goalGenome[g])
    ) /\ (
        isLeftNeighbourConstant(max(stateIndices),goalGenome[1],goalGenome[genomeLength])
    ) /\ (geneTakesGoalGenomeSign(-1)) %If we go inverted, do change the input signs
);

%Also read in the signs
%Initial
constraint forall(g in geneValues) (
    ((initialGenome[g] < 0) -> (geneSign[1,abs(initialGenome[g])] = -1)) /\
    ((initialGenome[g] > 0) -> (geneSign[1,abs(initialGenome[g])] = 1))
);
%Final (this is a predicate as we use it above, we might choose to negate all genome signs if the solver would like to invert the goal genome)
predicate geneTakesGoalGenomeSign(int: multiplier) =  forall(g in geneValues) (
    ((goalGenome[g] < 0) -> (geneSign[max(stateIndices),abs(goalGenome[g])] = -multiplier)) /\
    ((goalGenome[g] > 0) -> (geneSign[max(stateIndices),abs(goalGenome[g])] = multiplier))
);

%---------GENERAL RULES---------

%each step is a cycle
constraint forall(t in stateIndices) (
        circuit([leftNeighbour[t,i] | i in geneValues])
);

%Make sure right neighbour holds
constraint forall(t in stateIndices) (
    forall(g in geneValues) (isLeftNeighbour(t,g,rightNeighbour[t,g]))
);

%can't both be neighbours of the same gene
constraint forall(t in stepIndices) (
    alldifferent(g in geneValues)(leftNeighbour[t,g])
);

%Only change the left neighbour if you are allowed to
constraint forall(t in stepIndices) (
    forall(g in geneValues) (
        (
                (not leftNeighbourChangeAllowed(t,g)) -> (not leftNeighbourChanges(t,g))
        ) /\
        (
                (not rightNeighbourChangeAllowed(t,g)) -> (not rightNeighbourChanges(t,g))
        )
    )
);

%You can't be your own left neighbour
constraint forall(t in stepIndices) (
    forall(g in geneValues) (
        leftNeighbour[t,g] != g
    )
);

%No inversion, no moving, then we should stay completely the same
constraint forall(t in stepIndices) (
	not(operationIsMoving(t) \/ inversionTookPlace[t]) ->
	(
		forall(g in geneValues) (
			leftNeighbour[t,g] = leftNeighbour[t+1,g]
		)
		/\
		(not inversionTookPlace[t])
	)
);

%No funny business with the parameters
%Don't let start or end be the target
constraint forall(t in stepIndices) (
        (operationStart[t] != operationTarget[t]) /\
        (operationEnd[t] != operationTarget[t])
    
);

%---------OPERATIONS---------
%----TRANSPOSITION----
constraint forall(t in stepIndices)
(
	(
		(not inversionTookPlace[t]) ->
		(
			%The case where an inversion did not take place (link the start and the end to the rest in the same orientation
			isLeftNeighbour(t+1, operationEnd[t], operationTarget[t]) /\ %end left of target
			(operationIsMoving(t) -> (isLeftNeighbour(t+1, leftNeighbour[t,operationTarget[t]], operationStart[t]))) /\ %(left of target) is now left of (start). Only bother if moving
			(operationIsMoving(t) -> (isLeftNeighbour(t+1, leftNeighbour[t,operationStart[t]], rightNeighbour[t,operationEnd[t]]))) %(left of start) is now left of (right of end). Only bother if moving
		)
	) /\
	(
		inversionTookPlace[t] ->
		(
			%The case where an inversion did take place (link the end in the start's position, and vice versa. Caps in comments indicate changes from above
			isLeftNeighbour(t+1, operationStart[t], operationTarget[t]) /\ %START left of target
			(operationIsMoving(t) -> (isLeftNeighbour(t+1, leftNeighbour[t,operationTarget[t]], operationEnd[t]))) /\ %(left of target) is now left of (END)
			(operationIsMoving(t) -> (isLeftNeighbour(t+1, leftNeighbour[t,operationStart[t]], rightNeighbour[t,operationEnd[t]]))) %(left of start) is now left of (right of end)
		)
	)
);


%----INVERSION----
%--SIGNS--

%First, we infer which blocks should be negated based on their signs
%We say that genes to the left and right of genes that are part of inversions become part of inversions (chain inference to the middle)
constraint forall(t in stepIndices) (
	inversionTookPlace[t] -> (
		forall(g in geneValues) (
			((partOfInversion(t,g) /\ (not (g=operationStart[t]))) -> (partOfInversion(t,leftNeighbour[t,g]))) /\ 
			((partOfInversion(t,g) /\ (not (g=operationEnd[t]))) -> (partOfInversion(t,rightNeighbour[t,g])))
		)
	)
);

%If an inversion took place, force it to change the sign of the start and the end, so we can chain inference into the middle (base case)
constraint forall(t in stepIndices) (
	inversionTookPlace[t] -> (partOfInversion(t,operationStart[t]) /\ partOfInversion(t,operationEnd[t]))
);

%And now for inferring which signs should not change
%We say that genes to the left of start and right of end stay out of inversions
constraint forall(t in stepIndices) (
	inversionTookPlace[t] -> (
		forall(g in geneValues) (
			(
				((not partOfInversion(t,g)) /\ (not (isLeftNeighbour(t,g,operationStart[t])))) -> (not partOfInversion(t,rightNeighbour[t,g])) %if the right is not the start, then the right isn't part of the inversion
			) /\ 
			(
				((not partOfInversion(t,g)) /\ (not (isLeftNeighbour(t,operationEnd[t],g)))) -> (not partOfInversion(t,leftNeighbour[t,g])) %if the left is not the end, then the left isn't part of the inversion
			)
		)
	)
);

%If an inversion took place, genes outside the block cannot change sign (base case)
constraint forall(t in stepIndices) (
	inversionTookPlace[t] -> (
		(not partOfInversion(t,leftNeighbour[t,operationStart[t]])) /\
		(not partOfInversion(t,rightNeighbour[t,operationEnd[t]]))
	)
);

%If an inversion did not take place, the sign can't change
constraint forall(t in stepIndices) (
	(not inversionTookPlace[t]) -> (
		forall(g in geneValues) (
			not partOfInversion(t,g)
		)
	)
);

%--ORIENTATION--
%If a gene is part of an inversion, usually the left and right neighbours need to be swapped between steps (edge cases too)
%Complicated by special case of a width one operation (in this case, don't swap the neighbours twice, it's both the start and the end which makes things confusing and wrong)
constraint forall(t in stepIndices) (
	forall(g in geneValues) (
		partOfInversion(t,g) -> (
			%don't flip anything if it's a single gene (in terms of orientation anyway, we'll change the sign)
			(
				widthOneOperation(t) -> (
					(leftNeighbour[t,g] = leftNeighbour[t+1,g]) /\ %we know g is the one that is the width one operation, since it inverted.
					(rightNeighbour[t,g] = rightNeighbour[t+1,g])
				)
			)/\
			%only do the rest if it's not a width one operation
			(not widthOneOperation(t)) -> (
				%if part of an inversion, swap neighbours, unless edge case
				(
					(g=operationStart[t]) -> (
						(rightNeighbour[t+1,g] = rightNeighbour[t,operationEnd[t]]) /\ %start moves to old end's position
						(leftNeighbour[t+1,g] = rightNeighbour[t,g])
					)
				
				)/\
				(
					(g=operationEnd[t]) -> (
						(leftNeighbour[t+1,g] = leftNeighbour[t,operationStart[t]]) /\ %end moves to old start's position
						(rightNeighbour[t+1,g] = leftNeighbour[t,g])
					)
				
				)/\
				(
					((g!=operationStart[t]) /\ (g!=operationEnd[t])) -> ( %anything in between has both neighbours flipped
						(leftNeighbour[t+1,g] = rightNeighbour[t,g]) /\
						(rightNeighbour[t+1,g] = leftNeighbour[t,g])
					)
				)
			)
		)
	)
);


%---------REDUNDANT CONSTRAINTS---------

%All noactions in a block
constraint forall(t in stepIndices) (
	(t=1) \/ (noAction(t) -> noAction(t-1))
);

%cost cap
constraint sum(actionCost) <= costCap;

%---------ACTION COSTS---------
%The actionCost array should contain the costs for each of the actions we are taking
constraint forall(t in stepIndices) (
	(inversionAction(t) -> (actionCost[t] = inversionPenalty)) /\
	(transpositionAction(t) -> (actionCost[t] = transpositionPenalty)) /\
	(transversionAction(t) -> (actionCost[t] = transversionPenalty)) /\
	(noAction(t) -> (actionCost[t] = 0))
);



solve minimize sum(actionCost);

output ["leftNeighbour:\n"] ++
["leftNeighbour t="++show(t)++": "++ show([leftNeighbour[t,i] | i in geneValues])++"\n" | t in stateIndices] ++
["\nrightNeighbour:\n"] ++
["rightNeighbour t="++show(t)++": "++ show([rightNeighbour[t,i] | i in geneValues])++"\n" | t in stateIndices] ++
["\nSigns:\n"] ++
["Signs t="++show(t)++": "++ show([geneSign[t,g] | g in geneValues])++"\n" | t in stateIndices] ++
["\n~~Operations~~\n"]++
["operationStarts:\t",show(operationStart),"\n"]++
["operationEnds:\t\t",show(operationEnd),"\n"]++
["operationTargets:\t",show(operationTarget),"\n"]++
["inversionTookPlace:\t",show(inversionTookPlace),"\n"]++
["\n~~Costs~~\n"]++
["actionCost:\t",show(actionCost),"\n"]++
["Total cost: ",show(sum(actionCost)), "\n"]++
["~~~~~\n"]
