% VRPTW model using CP

% Libraries
:-lib(ic).
:-lib(ic_global).
:-lib(branch_and_bound).
:-lib(viewable).
:-lib(matrix_util).

:-['auxiliars.ecl'].
:-['constraintsTW.ecl'].
:-['heuristics.ecl'].


%-------------------------------------------------------------------------------

vrptw(ProblemName) :-
	compile(ProblemName),
	variables(VARIABLES,DIMENSIONS),
	domains(VARIABLES,DIMENSIONS),

%
% STW %%%%%% 
%	constraints(VARIABLES,DIMENSIONS,DeltaA,DeltaB,DeltaDep),
%	objective(VARIABLES,DIMENSIONS,DeltaA,DeltaB,DeltaDep,Cost),	% Objective STW
%
% HTW %%%%%%
%	constraints(VARIABLES,DIMENSIONS),
%	objective(VARIABLES,DIMENSIONS,Cost),						% Objective HTW
%%%%%%%
%
% Distance as objective function %%%%%% 
	constraints(VARIABLES,DIMENSIONS),
	objectiveDistance(VARIABLES,DIMENSIONS,Cost),						% Objective Distance + HTW
%
	preprocess_HTW(VARIABLES,DIMENSIONS),
	simple_solve(VARIABLES,DIMENSIONS,Cost,B),
%	vns(VARIABLES,DIMENSIONS,Cost,B),
	showSolution(VARIABLES,DIMENSIONS,Cost,B).
%	printSolution(ProblemName,VARIABLES,DIMENSIONS,DeltaA,DeltaB,DeltaDep,Cost,B).	% STW
%	printSolution(ProblemName,VARIABLES,DIMENSIONS,Cost,B).						% HTW

%-------------------------------------------------------------------------------

variables([V,Q,T,D,R,Qv,P,S,O,Pairs],[N,M]):-
	readCustomers(N,M,R),    
	readVehicles(M,Qv),
	pairs(Pairs),   % Vehicles
	Vdim is N + 2 * M,
	P_SN is N + M,
	length(V,Vdim),       % Visits
	length(Q,Vdim),       % Cummulative capacities
	length(T,Vdim),       % Cummulative times
	length(D,Vdim),       % Cummulative distances
	length(P,P_SN),     % Predecessors
	length(S,P_SN),     % Successors
	length(O,Vdim).	% Sequence variable
	

%-------------------------------------------------------------------------------

domains([V,Q,T,D,_R,Qv,P,S,O,_Pairs],[N,M]):-
    decompose(V,M,_,_,V_FL,_,_),
    V_FL #:: 1..M,
    (ic: max(Qv,Max)),
    Q #:: 0..Max,      % Cummulative capacities
    (foreach(Ti,T) do Ti #>= 0),      % Cummulative times
    (foreach(Di,D) do Di #>= 0),      % Cummulative distances
    length(P,P_SN),
    P #:: 1..P_SN,
    S #:: 1..P_SN,
    Vdim is N + 2 * M,
    O #::1..Vdim.

%-------------------------------------------------------------------------------

% STW's predicate

constraints([V,Q,T,D,R,Qv,P,S,O,Pairs],[N,M],DeltaA,DeltaB,DeltaDep):-	
    constraintsCiclicRoutes(V,M),
    constraintsDifferent(P,S,N,M),
    constraintsCoherence(P,S),
    constraintsPath(V,P,S,M),
    constraintsCapacity(Q,R,P,S,M),
    constraintsMaxCapacity(Q,V,Qv,M),
    constraintsCapacityInRoute(V,Qv,R,N,M),
	constraintTimePickUp(M,T,Pairs),
	constraintPickUp2(Pairs,O,V),
	constraintPickUp(N,M,P,S,O),
    constraintsTime(T,P,S,M),
    constraintsSoftTimeWindows(T,[N,M],DeltaA,DeltaB,DeltaDep),
    constraintsSymmetriesVisits(V,M),
    constraintsHamiltonianPath(P,S,N,M),
    constraintsDistance(D,P,S,M).
    
    
% HTW's predicate
    
constraints([V,Q,T,D,R,Qv,P,S,O,Pairs],[N,M]):-
    constraintsCiclicRoutes(V,M),
    constraintsDifferent(P,S,N,M),
    constraintsCoherence(P,S),
    constraintsPath(V,P,S,M),
    constraintsCapacity(Q,R,P,S,M),
    constraintsMaxCapacity(Q,V,Qv,M),
    constraintsCapacityInRoute(V,Qv,R,N,M),
    constraintsTime(T,P,S,M),
    constraintsHardTimeWindows(T,[N,M]),
    constraintsSymmetriesVisits(V,M),
    constraintsHamiltonianPath(P,S,N,M),
    constraintsDistance(D,P,S,M),
    	constraintTimePickUp(M,T,Pairs),
	constraintPickUp(N,M,P,S,O),
	constraintPickUp2(Pairs,O,V).

%-------------------------------------------------------------------------------

objective([_,_,T,_,_,_,_,_,_,_],[_,M],DeltaA,DeltaB,DeltaDep,Cost):-
    costFunction(T,M,DeltaA,DeltaB,DeltaDep,Cost).

objective([_,_,T,_,_,_,_,_,_,_],[_,M],Cost):-
    costFunction(T,M,Cost).
    
objectiveDistance([_,_,_,D,_,_,_,_,_,_],[_,M],Cost):-
    costDistance(D,M,Cost).

%-------------------------------------------------------------------------------

optimise([V,Q,T,_,_,_,P,S,_,_],[_,_],Cost,B):-
    viewable_create(p_s, [P,S]),
    viewable_create(v_q_t, [V,Q,T]),
    nearestNeighbourHeuristic(S,Distances),
    flatten([V,Distances,P],VARSflat),
    bb_min((search(VARSflat,0,smallest,indomain_min,complete,[backtrack(B)]),indomain(Cost)),Cost,bb_options{strategy:continue}).