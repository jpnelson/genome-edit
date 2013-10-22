include "alldifferent.mzn";
include "increasing.mzn";

%Parameters
int: inversionPenalty;
int: transpositionPenalty = 2;
int: genomeLength;
int: planLength; %Ignore the variable in this case, just use genomeLength as planLength

int: costCap; %A cap on the optimal cost - we may know this if we already have a potentially sub optimal plan from another

array[geneIndices] of int: initialGenome;
array[geneIndices] of int: goalGenome;
int: noAction = -(genomeLength*100); %an index of noAction represents no action

set of int: genes = (-genomeLength..genomeLength) diff {0}; %Possible gene values are from -length to the length of the genome, but 0 is impossible
set of int: geneIndices = 1..genomeLength;
set of int: geneIndicesWithNoAction = geneIndices union {noAction};
set of int: stepIndices = 1..genomeLength;
set of int: stateIndices = 1..genomeLength+1;

%Variables
array[stateIndices, geneIndices] of var genes:      planStates;
array[stepIndices] of var geneIndicesWithNoAction:  inversionStarts;           %A list of the inversion start actions we've taken. noAction means no inversion
array[stepIndices] of var geneIndicesWithNoAction:  inversionEnds;             %A list of the inversion ends we've taken at each step.

array[stepIndices] of var geneIndicesWithNoAction:  transpositionStarts;       %A list of the transposition start locations. noAction means no transposition
array[stepIndices] of var geneIndicesWithNoAction:  transpositionEnds;         %Where to end each transposition
array[stepIndices] of var geneIndicesWithNoAction:  transpositionShifts;       %How much each transposition is shifting by

array[stepIndices] of var bool:                    transversionStep;       %A boolean array specifying whether an inversion took place at the same time as the transposition

array[stepIndices] of var 0..max(inversionPenalty,transpositionPenalty):      actionCosts; %A list of the costs of the actions we have taken.
var 0..(max(inversionPenalty,transpositionPenalty) * genomeLength):              planCost;

array[stepIndices] of var geneIndicesWithNoAction:              lastGeneModified;       %An array used for symmetry breaking
array[stepIndices] of var geneIndicesWithNoAction:              firstGeneModified;      %Same as above

array[stateIndices, geneIndices] of var 0..genomeLength:          breakpoints;            %An array indicating how many breakpoints there are at each step and index
array[stateIndices] of var 0..genomeLength:          breakpointCount;        %An array indicating how many breakpoints there are at each step

%The goal should be the identity (1,2,3,4,...,genomeLength) in either direction (to be fair)
%constraint (forall(i in geneIndices) (planStates[genomeLength+1,i] = goalGenome[i]));
constraint exists(rotation in 0..(genomeLength-1)) (
    (
        %Direction = forwards
        forall(i in geneIndices) (
            let {int: iRotated = (i+rotation) mod genomeLength} in (
                if(iRotated=0)
                    then (planStates[genomeLength+1,i] = goalGenome[genomeLength])
                    else (planStates[genomeLength+1,i] = goalGenome[iRotated])
                endif
            )
        )
    ) \/
    (
        %Direction = backwards
        forall(i in geneIndices) (
            let {int: iRotated = (i+rotation) mod genomeLength} in (
                if(iRotated=0)
                    then (planStates[genomeLength+1,i] = -goalGenome[1])
                    else (planStates[genomeLength+1,i] = -goalGenome[(genomeLength - iRotated) + 1])
                endif
            )
        )
    )
);

%The initial state should be the initialGenome parameter
constraint forall(i in geneIndices) (planStates[1,i] = initialGenome[i]);

%Each step should contain each gene only once
constraint forall(t in stateIndices) (
    alldifferent(i in geneIndices)(planStates[t, i])
);

%Genomes can't contain a negative and a positive of the same gene 
constraint forall(t in stateIndices) (
    forall(i in geneIndices) (
        forall(j in geneIndices) (
            -planStates[t,i] != planStates[t,j]
        )
    )
);

%--------------------------------------
%       EFFICIENCY CONSTRAINTS
%--------------------------------------

%--------------------------------------
%       Symmetry breaking
%--------------------------------------

%Do all noActions first
constraint forall(t in stepIndices) (
    forall(j in stepIndices) (
        (noActionTookPlace(t) /\ (not noActionTookPlace(j))) -> t < j %If no action happened at t, but it did at j, then t happened first.
    )
);

%LAST INDEX
%-------------------

%Only allow operations to move forward along the genome sequentially
constraint forall(t in stepIndices) (
    (transpositionTookPlace(t) -> (lastGeneModified[t] = transpositionEnds[t]+transpositionShifts[t])) /\
    (inversionTookPlace(t) -> (lastGeneModified[t] = inversionEnds[t]))
);


%FIRST INDEX
%--------------------

constraint forall(t in stepIndices) (
    (transpositionTookPlace(t) -> (firstGeneModified[t] = transpositionStarts[t])) /\
    (inversionTookPlace(t) -> (firstGeneModified[t] = inversionStarts[t]))
);

%Now we assert that there must be some overlap / moving forward in the next operation
constraint forall(t in stepIndices) (
    noActionTookPlace(t) \/ noActionTookPlace(t+1) \/
    (
        (
            (firstGeneModified[t+1] < firstGeneModified[t]) /\
            (lastGeneModified[t+1] < firstGeneModified[t])
        ) -> (firstGeneModified[t] > lastGeneModified[t]) %We only allow this if a modular operation has occurred
    )
);


%-----------------------------------
%       Redundant constraints
%-----------------------------------

%Whether index i at time t is the center of an inversion operation (stationary between steps)
predicate inversionPivotPoint(var int: t, var int: i) = inversionTookPlace(t) /\ ((i-inversionStarts[t]) = (inversionEnds[t]-i));

%If a gene stays in the same position between steps, then it may be the center of an inversion, or it's not in an action
constraint forall(t in stepIndices) (
    noActionTookPlace(t) \/ (
        forall(i in geneIndices) (
            ((planStates[t,i] = planStates[t+1,i]) \/ (planStates[t,i] = -planStates[t+1,i])) <-> (
                (
                    (transpositionTookPlace(t) /\ ((i < transpositionStarts[t]) \/ (i > (transpositionEnds[t]+transpositionShifts[t])))) \/ %Case 1: not in a transposition
                    (inversionTookPlace(t) /\ ((i < inversionStarts[t]) \/ (i > (inversionEnds[t])))) \/ %Case 2: not in an inversion
                    inversionPivotPoint(t,i) \/ %Case 3: in an inversion, but at the center
                    (transpositionTookPlace(t) /\ (transpositionStarts[t] > transpositionEnds[t])) %Case 4: the transposition is wrapping around
                )
            )
        )
    )
);

%If the absolute value of the gene at index i changes between t and t+1
predicate geneMovedThisStep(var int: t, var int: i) = ((planStates[t,i] != planStates[t+1,i]) /\ (planStates[t,i] != -planStates[t+1,i]));

%Genes are usually modified in contiguous blocks
constraint forall(t in stepIndices) (
    noActionTookPlace(t) \/(
        forall(i in geneIndices) (
            forall(j in geneIndices) (
                (
                    (geneMovedThisStep(t,i) /\ geneMovedThisStep(t,j) /\ (i+1 < j)) -> %we reason about i+1, which is between i and j. Will only select groups as big as 3
                    (
                        geneMovedThisStep(t,i+1) \/
                        inversionPivotPoint(t,i+1) \/
                        (transpositionTookPlace(t) /\ (transpositionStarts[t] > transpositionEnds[t])) %Funny things happen with wrap around transpositions
                    )
                )
            )
        )
    )
);

%Genes in consecutive steps should only have signs changed if it was 1. inside an inversion 2. inside a transversion. Also, means an action had to take place
constraint forall(t in stepIndices) (
    forall(i in geneIndices) (
        forall(j in geneIndices) (
            (planStates[t,i] = -planStates[t+1,j]) -> (
                (
                    ( (inversionTookPlace(t) /\ (i >= inversionStarts[t]) /\ (i <= inversionEnds[t])) ) \/
                    (transversionTookPlace(t) /\ (i >= transpositionStarts[t]) /\ (i <= transpositionEnds[t] + transpositionShifts[t]))
                )
                /\
                (not noActionTookPlace(t))
            )
        )
    )
);

%Don't worry about transversions if it isn't a transposition step
constraint forall(t in stepIndices) (
    ((not transpositionTookPlace(t)) -> (not transversionStep[t]))
);

%At each step, genomes inside affected indices change
constraint forall(t in stepIndices) (
    (
        forall(i in geneIndices) (
                (not inModuloRange(i,firstGeneModified[t],lastGeneModified[t])) -> (planStates[t,i] = planStates[t+1,i])
        )
    )
);
%And those outside do not change (bar inversion centers)
constraint forall(t in stepIndices) (
    (not noActionTookPlace(t)) ->
    (
        forall(i in geneIndices) (
            (inModuloRange(i,firstGeneModified[t],lastGeneModified[t]) /\ (not geneMovedThisStep(t,i))) <-> (inversionTookPlace(t) /\ inversionPivotPoint(t,i))
        )
    )
);

%No action requires no action in other corresponding action arrays
constraint forall(t in stepIndices) (
    ((not transpositionTookPlace(t)) <-> ((transpositionStarts[t]=noAction) /\ (transpositionEnds[t]=noAction) /\ (transpositionShifts[t]=noAction))) /\
    ((not inversionTookPlace(t)) <-> ((inversionStarts[t]=noAction) /\ (inversionEnds[t]=noAction)))
);

%At most, only bother with costCap actions
constraint forall(t in stepIndices) (
    (t < (genomeLength-costCap)) -> noActionTookPlace(t) %remember the no actions are all at the start
);

%Never invert and transpose the same segment in sequential steps (we could just transvert and it'd be cheaper, we'd hope)
constraint forall(t in stepIndices) (
    not (inversionTookPlace(t) /\ transpositionTookPlace(t+1) /\ (inversionStarts[t] = transpositionStarts[t+1]) /\ (inversionEnds[t] = transpositionEnds[t+1])) /\
    not (inversionTookPlace(t+1) /\ transpositionTookPlace(t) /\ (inversionStarts[t+1] = transpositionStarts[t]) /\ (inversionEnds[t+1] = transpositionEnds[t]))
);

%Impose some restrictions on the first/last gene modified in the case of noAction
constraint forall(t in stepIndices) (
    noActionTookPlace(t) -> ((firstGeneModified[t] = noAction) /\ (lastGeneModified[t] = noAction))
);


%---------------------------------------------
%       Conditional Redundant constraints
%---------------------------------------------
%
% Note: the following constraints are conditional, in that there are circumstances when these constraints do not apply.
% It may be worth considering these constraints in some instances, but for correctness, they are commented out here.
% To use or expand upon these constraints, simply comment them back in again.

%Never do series of inversions we could just do with a transposition
%NOTE: this constraint assumes that 3 inversions are more expensive than a transposition. However, if they were not, the plan would contain no transpositions, as 3 inversions can make a transposition (the basis of this constraint)
%We can simulate a transposition with 3 inversions if we: 1) invert a gene segment, 2) invert some part of it beginning at the start, 3) invert the rest
%Not using this 'cos it's slower
%constraint forall(t in stepIndices) (
%    (inversionTookPlace(t) /\ inversionTookPlace(t+1) /\ inversionTookPlace(t+2)) -> (
%        let {var int: firstStart = inversionStarts[t], var int: firstEnd = inversionEnds[t]} in
%        (
%            not (
%                (
%                    (inversionStarts[t+1] = firstStart) /\ (inversionEnds[t+1] = inversionStarts[t+2]-1) /\ (inversionEnds[t+2] = firstEnd)
%                )
%                \/
%                (
%                    (inversionStarts[t+2] = firstStart) /\ (inversionEnds[t+2] = inversionStarts[t+1]-1) /\ (inversionEnds[t+1] = firstEnd)
%                )
%            )
%        )
%    )
%);

%BREAKPOINTS
%-----------
%NOTE: this section assumes the goal is the identity (usually true)

%predicate genesInSequence(var int: g1, var int: g2) = (g1-g2 = 1) \/ (g1-g2 = -1); %Tells us if a pair of genes is not a breakpoint (ie are g1 and g2 consecutive numbers, neg or pos)

%If in the initial state, some segment is already sorted, don't break it apart
%constraint forall(t in stepIndices) ( 
%    forall(i in 1..genomeLength-1) (
%        let {var int: gene1=planStates[1,i], var int: gene2=planStates[1,i+1]} in %TODO make it so that this wraps around
%        (
%            (genesInSequence(gene1,gene2)) -> ( %at every timestep, find pairs of genes that are sequential
%                forall(t2 in stepIndices) (
%                    (t2 > t) ->( %at all consequent steps they should not break apart
%                        exists(i2 in 1..genomeLength-1) (
%                            (
%                                (planStates[t2,i2] = gene1) /\ (planStates[t2,i2+1] = gene2) %we can have ...gene1, gene2... again
%                            )
%                            \/
%                            (
%                                (planStates[t2,i2] = -gene2) /\ (planStates[t2,i2+1] = -gene1) %or it might be reversed to ...-gene2,-gene1
%                            )
%                        )
%                    ) 
%                )
%            )
%        )
%    )
%);


%Count breakpoints at each index
%constraint forall(t in stepIndices) (
%    forall(i in geneIndices) (
%        (
%            genesInSequence(planStates[t,i],planStates[t,i+1]) -> (breakpoints[t,i]=0)
%        )
%        /\
%        (
%            (not genesInSequence(planStates[t,i],planStates[t,i+1])) -> (breakpoints[t,i]=1)
%        )
%    )
%);

%Sum them and store them in a step based array, breakpointCount
%constraint forall(t in stateIndices) (
%    breakpointCount[t] = sum([breakpoints[t,i] | i in geneIndices])
%);

%Constrain the change in breakpoints to be at most the operation that we did between the steps (trans* fix 3, inversions fix 2)
%constraint forall(t in stepIndices) (
%    (transpositionTookPlace(t) -> ((breakpointCount[t]-breakpointCount[t+1]) <= 3)) /\
%    (inversionTookPlace(t) -> ((breakpointCount[t]-breakpointCount[t+1]) <= 2))
%);



%COST CAP
%--------
constraint planCost <= costCap; %put a cap on the cost if we've already found a plan.

%------------------------
%        Actions
%------------------------

%Inversions and transpositions cannot occur at the same time step
predicate inversionTookPlace(var int: t)        = (inversionStarts[t] != noAction) /\ (inversionEnds[t] != noAction);
predicate transpositionTookPlace(var int: t)    = (transpositionStarts[t] != noAction) /\ (transpositionEnds[t] != noAction) /\ (transpositionShifts[t] != noAction);
predicate transversionTookPlace(var int: t)     = (transversionStep[t]);
predicate noActionTookPlace(var int: t)         = (not inversionTookPlace(t)) /\ (not transpositionTookPlace(t));

%Only one action can take place at a time
constraint forall(t in stepIndices) (not (inversionTookPlace(t) /\ transpositionTookPlace(t)));

%If no action took place, we force consecutive steps to be the same
constraint forall(t in stepIndices) (
    noActionTookPlace(t) <-> (forall(i in geneIndices) (planStates[t+1,i]=planStates[t,i]))
);

%The inversionStarts array should specify the changes between each planStates item
constraint forall(t in stepIndices) (
    (inversionTookPlace(t) ->
        (
            %If the range is wrapping around, it is the same as swapping the start and the end, and inverting the whole thing (consider 1| 2 3 4 |5 => 1| 4 3 2 |5 and 1| 2 3 4 |5 => 5| 2 3 4 |1)
            forall(i in geneIndices) (
                %In flip range, allow flipping
                (((i >= inversionStarts[t]) /\ (i <= inversionEnds[t])) -> (planStates[t+1,i] = -planStates[t,inversionEnds[t]-(i-inversionStarts[t])]))
                
                /\
                
                %If this gene isn't part of the flipping action, it should stay the same between steps
                (((i < inversionStarts[t]) \/ (i > inversionEnds[t])) -> planStates[t+1,i]=planStates[t,i])
            )
        )
    )
);

%Inversion starts should occur before inversion ends
constraint forall(t in stepIndices) (
    inversionStarts[t] <= inversionEnds[t]
);

%Transpositions should take place between steps if specified
constraint forall(t in stepIndices) (
    (transpositionTookPlace(t) <->
        (
            let {var int: start = transpositionStarts[t], var int: end = transpositionEnds[t], var int: shift = transpositionShifts[t]} in
            forall(i in geneIndices) (
                let{var int: iShiftedNoWrap = i+shift, var int: iShiftedWrap = iShiftedNoWrap-genomeLength, var int: iDisplacedNoWrap = start+(i-(end+1)), var int: iDisplacedWrap = iDisplacedNoWrap + genomeLength} in
                (
                    %Genes not affected by the transposition should stay the same
                    ((not inModuloRange(i,start,end+shift)) -> (planStates[t+1,i]=planStates[t,i]))
                    /\
                    %Genes which we are shifting
                    %Transversion step
                    (
                        transversionStep[t] -> 
                        (
                            inModuloRange(i,start,end) ->
                            (
                                ((iShiftedWrap <= 0)->(planStates[t,start+end-i]= -planStates[t+1,iShiftedNoWrap])) %we can't use the wrapping version as it's out of bounds
                                /\
                                ((iShiftedWrap > 0)->(planStates[t,start+end-i]= -planStates[t+1,iShiftedWrap])) %we can use the wrapping version - nowrap must be out of bounds
                            )
                        )
                    ) 
                    /\
                    %Transposition step
                    (
                        (not transversionStep[t]) ->
                        (
                            inModuloRange(i,start,end) ->
                            (
                                ((iShiftedWrap <=0) -> (planStates[t,i]=planStates[t+1,iShiftedNoWrap]))
                                /\
                                ((iShiftedWrap > 0) -> (planStates[t,i]=planStates[t+1,iShiftedWrap]))
                            )
                        )
                    )
                    /\
                    %Genes which are displaced by the shift move back
                    (
                        inModuloRange(i,end+1,end+shift) ->
                        (
                            ((iDisplacedNoWrap > 0) -> (planStates[t,i]=planStates[t+1,iDisplacedNoWrap])) %iDisplacedNoWrap > 0 means we can use it without issues
                            /\
                            ((iDisplacedNoWrap <= 0) -> (planStates[t,i]=planStates[t+1,iDisplacedWrap])) %we have to use the wrapping as the other is out of bounds
                        )
                    )
                )
            )
        )
    )
);

%---------------------
%    Action costs
%---------------------
%The actionCosts array should contain the costs for each of the actions we are taking
constraint forall(t in stepIndices) (
    (inversionTookPlace(t) -> (actionCosts[t] = inversionPenalty)) /\
    (transpositionTookPlace(t) -> (actionCosts[t] = transpositionPenalty)) /\
    (noActionTookPlace(t) -> (actionCosts[t] = 0))
);

%Sum up the costs
constraint planCost = sum(actionCosts);

%------------------------------------------
%         Predicates
%------------------------------------------
%Determines if x is in the range (start,end) modulo a number, inclusively
predicate inModuloRange(var int: x, var int: s, var int: e) = 
(
    ((s <= e) -> ((x >= s) /\ (x <= e)))
    /\
    ((s > e) -> ((x >= s) \/ (x <= e)))
);

%Determines if the pairs (a,b) (x,y) are overlapping, including modulo.
predicate overlapping(var int: start1, var int: end1, var int: start2, var int: end2) = 
(
    inModuloRange(start1, start2, end2) \/ inModuloRange(end1, start2, end2)
);

%Are operations overlapping at these time steps
predicate operationsOverlap(var int: time1, var int: time2) =
(
    overlapping(firstGeneModified[time1],lastGeneModified[time1],firstGeneModified[time2],lastGeneModified[time2])
);


solve minimize planCost;

output ["planStates:\n"]++
[
"State "++show(t)++": "++ show([planStates[t,i] | i in geneIndices])++"\n"
| t in stateIndices]++
["    inversionStarts:\t",show(inversionStarts),"\n"]++
["      inversionEnds:\t",show(inversionEnds),"\n\n"]++
["transpositionStarts:\t",show(transpositionStarts),"\n"]++
["  transpositionEnds:\t",show(transpositionEnds),"\n"]++
["transpositionShifts:\t",show(transpositionShifts),"\n"]++
["transversionStep:\t",show(transversionStep),"\n\n"]++
["lastGeneModified:\t\t",show(lastGeneModified),"\n"]++
["firstGeneModified:\t\t",show(firstGeneModified),"\n\n"]++
["breakpointCount:\t\t",show(breakpointCount),"\n\n"]++
["Costs: ",show(actionCosts),"\n"]++
["Total cost: ",show(planCost)];
