%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%	Constraints related to the CVRP problem
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% constraintsCiclicRoutes(+V,+M)
% 
% V - Visits list
% M - Number of available vehicles
%
% Constraints ensuring vehicles start and finish their routes at
% the same node (the "depot")
%
% firstVisit(v) = lastVisit(v) for each vehicle

constraintsCiclicRoutes(V,M):-
    decompose(V,M,_,_,_,F,L),
    (foreach(Fi,F),foreach(Li,L),for(I,1,M) do
        Fi #= I,
        Li #= I
    ).

%-------------------------------------------------------------------------------

% constraintsDifferent(+P,+S,+N)
%
% P - Predecessors list
% S - Successors list
% N - Number of customers
%
% Constraint ensuring no repetitions in Predecessors and Successors
% lists of variables. One node cannot be neither the predecessor
% nor the successor of more than one another. 
% Furthermore, only depot nodes can be their own predecessor and
% successors if the vehicle is not used.
% !!! Notice that the 'sorted' constraints make necessary the
% vehicles in a depot to be sorted from smaller to bigger ones

constraintsDifferent(P,S,N,M):-
    decompose2(P,N,P_L,L),
    decompose2(S,N,S_F,F),
    (ic:alldifferent(P_L)),%ordered(<,L),
    (ic:alldifferent(S_F)),%ordered(<,F),
    (foreach(Pi,P_L),foreach(Si,S_F),for(I,1,N) do
        Pi #\= I,
        Si #\= I
    ),
    NM is N+M,
    L #:: 1..NM,
    F #:: 1..NM.

%-------------------------------------------------------------------------------

% constraintsCoherence(+P,+S)
%
% P - Predecessors list
% S - Successors list
%
% Constraint ensuring coherence (consistence) between Predecessors
% and Successors lists.
%
% successor(predecessor(i)) = i for each node

constraintsCoherence(P,S):-
    length(P,PL),
    (foreach(Pi,P),for(I,1,PL),param(S) do
        ith(Pi,S,I)
    ),
    (foreach(Sj,S),for(J,1,PL),param(P) do
        ith(Sj,P,J)
    ).

%-------------------------------------------------------------------------------

% constraintsUseAllVehicles(+P,+S,+N)
% [For VRP with multiple vehicles]
%
% P - Predecessors list
% S - Successors list
% N - Number of clients
%
% Constraint to compeal the use of
% all the available vehicles

constraintsUseAllVehicles(P,S,N):-
    decompose2(P,N,_,L),
    decompose2(S,N,_,F),
    L #:: 1..N,
    F #:: 1..N.

%-------------------------------------------------------------------------------

% constraintsPath(+V,+P,+S,+M)
%
% V - Visits list
% P - Predecessors list
% S - Successors list
% M - Number of available vehicles
%
% Constraint ensuring that along a route, visits are performed
% by the same vehicle.
%
% vehicle(i) = vehicle(predecessor(i)) for each i in V-F
% vehicle(i) = vehicle(successor(i)) for each i in V-L

constraintsPath(V,P,S,M):-
    decompose(V,M,V_F,V_L,_,_,_),
    length(V_F,V_FN),
    (foreach(V_Fi,V_F),for(I,1,V_FN),param(P,V) do
        ith(I,P,Pi),
        domainPS(Pi,V,VPi),
        V_Fi #= VPi
    ),
    (foreach(V_Li,V_L),for(I,1,V_FN),param(S,V) do
        ith(I,S,Si),
        domainPS(Si,V,VSi),
        V_Li #= VSi
    ).

%-------------------------------------------------------------------------------

% constraintsCapacity(+Q,+R,+P,+S,+M)
%
% Q - Capacities list
% R - Goods quantities list
% P - Predecessors list
% S - Successors list
% M - Number of available vehicles
%
% Constraint to accummulate vehicles' capacity use along
% routes.
%
% capacity_after_visit(i) = capacity_after_visit(predecessor(i)) 
% ... + capacity(i) for each i in V-F
% capacity_after_visit(i) = capacity_after_visit(successor(i)) 
% ... - capacity(successor(i)) for each i in V-L

constraintsCapacity(Q,R,P,S,M):-
    decompose(Q,M,Q_F,Q_L,_,QF,_),
    length(Q_F,Q_FN),
    (foreach(QFi,QF) do QFi #= 0),
    (foreach(Q_Fi,Q_F),foreach(Ri,R),for(I,1,Q_FN),param(P,Q_L) do
        ith(I,P,Pi),
        ith(Pi,Q_L,QPi),
        Q_Fi #= QPi + Ri
    ),
    (foreach(Q_Li,Q_L),for(I,1,Q_FN),param(Q_F,R,S) do
        ith(I,S,Si),
        ith(Si,Q_F,QSi),
        ith(Si,R,RSi),
        Q_Li #= QSi - RSi
    ).

%-------------------------------------------------------------------------------

% constraintsMaxCapacity(+Q,+V,+Qv,+M)
%
% Q - Capacities list
% V - Visits list
% Qv - Vehicles maximum capacities list
% M - Number of available vehicles
%
% Constraint ensuring that along a route, vehicles' capacities
% are not exceeded.
%
% capacity_after_visit(i) =< Vehicles_maximum_capacity for
% each i in V 

constraintsMaxCapacity(Q,V,Qv,M):-
    decompose(Q,M,_Q_F,_Q_L,Q_FL,F,L),
    decompose(V,M,_V_F,_V_L,V_FL,_,_),
    (foreach(Qi,Q_FL),foreach(Vi,V_FL),param(Qv) do
        ith(Vi,Qv,Qmaxi),
        Qi #=< Qmaxi
    ),
    (foreach(Fi,F),foreach(Li,L),foreach(Qmaxi,Qv) do
        Fi #=< Qmaxi,
        Li #=< Qmaxi
    ).

%-------------------------------------------------------------------------------

% constraintsCapacityInRoute(+V,+Qv,+R,+N,+M)
%
% V - Visits list
% Qv - Vehicles maximum capacities list
% R - Goods quantities list
% N - Number of customers
% M - Number of available vehicles
%
% Constraint ensuring that vehicles' capacities are not exceeded while
% allocating customers. This constraint is used to speed up model's
% performance. 
%

constraintsCapacityInRoute(V,Qv,R,N,M) :-
	decompose(V,M,_,_,V_FL,_,_),
	decompose2(R,N,R_L,_),
	(for(_,1,M),foreach(Q_M,Q_MV), param(N) do
	   length(Q_M,N)
	),
	transpose(Q_MV,Q_MVT),
	(foreach(Vi,V_FL),foreach(Q_MVi,Q_MVT) do
	   Q_MVi #:: [0,1],
%	   occurrences(Ri,Q_MVi,1),
	   atmost(1,Q_MVi,1),
	   ith(Vi,Q_MVi,1)
	),
	(foreach(Q_M,Q_MV),foreach(Qmax_V,Qv), param(R_L) do
	   (foreach(Ri,R_L), foreach(Q_Mi,Q_M), foreach(Dem_i,DemVehicleM) do
	   	Dem_i #= Ri * Q_Mi
	   ),
	   sumlist(DemVehicleM,Qm),
	   Qm #=< Qmax_V
	).

%-------------------------------------------------------------------------------

constraintPickUp(_,M,P,S,O):-
	decompose(O,M,O_F,O_L,_,OF,_),
	(foreach(Pi,P), foreach(Oi,O_F), param(O_L) do
		ith(Pi,O_L,OPi),
		OPi#=Oi-1
	),
	(foreach(Si,S), foreach(Oi,O_L), param(O_F) do
		ith(Si,O_F,OSi),
		OSi#=Oi+1
	),
	(foreach(OFi,OF) do OFi #= 1).

	
%-------------------------------------------------------------------------------

constraintPickUp2(Pairs,O,V):-
	
	(foreach(I,Pairs), param(O,V) do
		ith(1,I,PI),
		ith(2,I,PJ),
		ith(PI,O,OI),
		ith(PJ,O,OJ),
		ith(PI,V,Vi),
		ith(PJ,V,Vj),
		
		OJ#>OI,
		Vi#=Vj
	).

%-------------------------------------------------------------------------------
	
constraintTimePickUp(M,T,Pairs):-
	calculateMatrix(Tij),
	readServiceTimes(M,STimes),
	(foreach(I,Pairs), param(T,Tij,STimes) do
		ith(1,I,PI),
		ith(2,I,PJ),
		ith(PI,T,Ti),
		ith(PJ,T,Tj),
		ith(PI,Tij,TPI),
		ith(PJ,TPI,TPij),
		ith(PI,STimes,STi),
		
		Tj #>= Ti + TPij + STi
	).
	
%-------------------------------------------------------------------------------

% constraintsTime(+T,+P,+S,+M)
%
% T - Visits times list
% P - Predecessors list
% S - Successors list
% M - Number of available vehicles
%
% Constraint to accummulate time along routes.
%
% time_after_visit(i) = time_after_visit(predecessor(i)) 
% ... + travel_time(predecessor(i),i) for each i in V-F
% time_after_visit(i) = time_after_visit(successor(i)) 
% ... - travel_time(i,successor(i)) for each i in V-L

constraintsTime(T,P,S,M):-
    decompose(T,M,T_F,T_L,_,_TF,_),
    length(T_F,T_FN),
%    (foreach(TFi,TF) do TFi #= 0),
    calculateMatrix(Tij),
    readServiceTimes(M,STimes),
    (foreach(T_Fi,T_F),foreach(Pi,P),foreach(STi,STimes),for(I,1,T_FN),param(Tij,T_L) do
        ith(I,Tij,Ti),
        ith(Pi,T_L,TPi),
%        element(Pi,Ti,Tpi2i),
	ith(Pi,Ti,Tpi2i),
        T_Fi #>= TPi + Tpi2i + STi
%        T_Fi #= TPi + Tpi2i + STi
    ),
    (foreach(T_Li,T_L),foreach(Si,S),for(I,1,T_FN),param(Tij,T_F,STimes) do
        ith(I,Tij,Ti),
        ith(Si,T_F,TSi),
%        element(Si,Ti,Ti2si),
%        element(Si,STimes,STi),
        ith(Si,Ti,Ti2si),
	ith(Si,STimes,STi),
        T_Li #=< TSi - Ti2si - STi
%        T_Li #= TSi - Ti2si - STi
    ).

%-------------------------------------------------------------------------------

% constraintsHardTimeWindows(+T,[+N,+M])
%
% T - Visits times list
% N - Number of customers
% M - Number of available vehicles
%
% Constraint to impose hard time windows on the depot and visits.
%

constraintsHardTimeWindows(T,[N,M]):-
    time_windows(TW),
    decompose(T,M,_,_,Tcust,TF,TL),
    decompose2(TW,N,TWcust,TWdep),
    (foreach(Tcust_i,Tcust),foreach(TWi,TWcust) do
	element(1,TWi,Ai),
	element(2,TWi,Bi),
	Tcust_i #>= Ai,
 	Tcust_i #=< Bi
    ),
    (foreach(TFi,TF), foreach(TLi,TL),foreach(TWDi,TWdep) do
	element(1,TWDi,LB),
	element(2,TWDi,UB),
	TFi #>= LB,
	TLi #>= LB,
	TFi #=< UB,
	TLi #=< UB
    ).

%-------------------------------------------------------------------------------

% constraintsSoftTimeWindows(+T,[+N,+M],-DeltaA,-DeltaB,-DeltaDep)
%
% T - Visits times list
% N - Number of customers
% M - Number of available vehicles
% DeltaA - TW LB violations
% DeltaB - TW UB violations
% DeltaDep - Vehicles' scheduling horizon violations
%
% Constraint to impose soft time windows on the depot and visits.
%

constraintsSoftTimeWindows(T,[N,M],DeltaA,DeltaB,DeltaDep):-
    time_windows(TW),
    decompose(T,M,_,_,TCust,_,TL),
    decompose2(TW,N,TWcust,TWdep),
    (foreach(TCust_i,TCust),foreach(TWi,TWcust),foreach(DeltaAi,DeltaA),foreach(DeltaBi,DeltaB) do
	ith(1,TWi,Ai),
	ith(2,TWi,Bi),
	DeltaAi #>= Ai - TCust_i,
	DeltaAi #>= 0,			% Only = for HTW
 	DeltaBi #>= TCust_i - Bi,
	DeltaBi #>= 0			% Only = for HTW
    ),
    (foreach(TLi,TL),foreach(TWDi,TWdep),foreach(DeltaDepV,DeltaDep) do
	element(2,TWDi,UB),
	DeltaDepV #>= TLi - UB,
	DeltaDepV #>= 0			% Only = for HTW
    ).

%-------------------------------------------------------------------------------

% constraintsSymmetriesVisits(+V,+M)
% 
% V - Visits list
% M - Number of available vehicles
%
% Constraints ensuring the first visit is performed by the first
% vehicle, the second can be assigned either to the first or second,
% and so on. This constraint is added to avoid symmetric solutions when
% vehicles are identical.
% Enforcing this constraint all available vehicles must be used
%
% V = [1, {1..2}, ..., {1..M}, ...]

constraintsSymmetriesVisits(V,M):-
        length(VM,M),append(VM,_,V),
        (for(I,1,M),foreach(Vi,VM) do
            Vi #:: 1..I
        ).

%-------------------------------------------------------------------------------

% constraintsHamiltonianPath(+P,+S,+N,+M)
% 
% P - Predecessors list
% S - Successors list
% N - Number of customers
% M - Number of available vehicles
%
% It is not possible to visit consecutively the same client (that
% would mean a vehicle is not used). This constraint ensures all routes
% are Hamiltonian paths, i.e. each node has two and only two incident edges.
%
% P(I)!=I /\ S(I)!=I

constraintsHamiltonianPath(P,S,N,_M):-
    decompose2(P,N,P_L,_L),
    decompose2(S,N,S_F,_F),
%    length(P,PN),
    (foreach(Pi,P_L),foreach(Si,S_F),for(I,1,N) do
        Pi#\=I,
        Si#\=I
    ).
    
%-------------------------------------------------------------------------------

% constraintsDistance(+D,+P,+S,+M)
%
% D - Visits distance list
% P - Predecessors list
% S - Successors list
% M - Number of available vehicles
%
% Constraint to accummulate distances along routes.
%
% distance_after_visit(i) = distance_after_visit(predecessor(i)) 
% ... + travel_distance(predecessor(i),i) for each i in V-F
% distance_after_visit(i) = distance_after_visit(successor(i)) 
% ... - travel_distance(i,successor(i)) for each i in V-L

constraintsDistance(D,P,S,M):-
    decompose(D,M,D_F,D_L,_,DF,_),
    length(D_F,D_FN),
    ( foreach(DFi,DF) do DFi #= 0 ),
    calculateMatrix(Dij),
    ( foreach(D_Fi,D_F),foreach(Pi,P),for(I,1,D_FN),param(Dij,D_L) do
        ith(I,Dij,Di),
        ith(Pi,D_L,DPi),
	ith(Pi,Di,Dpi2i),
        D_Fi #= DPi + Dpi2i
    ),
    ( foreach(D_Li,D_L),foreach(Si,S),for(I,1,D_FN),param(Dij,D_F) do
        ith(I,Dij,Di),
        ith(Si,D_F,DSi),
        ith(Si,Di,Di2si),
        D_Li #= DSi - Di2si
    ).

%-------------------------------------------------------------------------------

% costFunction(+T,+M,-Cost)
%
% T - Visits times list
% M - Number of available vehicles
% Cost - Cost variable
%
% The cost is the addition of the final distances of all the
% vehicles for a homogeneous fleet. 

costFunction(T,M,Cost):-
    decompose(T,M,_,_,_,_,L),
    Cost#=sum(L).

%-------------------------------------------------------------------------------

% costFunction(+T,+M,+DeltaA,+DeltaB,+DeltaDep,-Cost)
%
% T - Visits times list
% M - Number of available vehicles
% DeltaA - LB TW constraints violation list
% DeltaB - UB TW constraints violation list
% DeltaDep - Vehicles' scheduling horizon violation list
% Cost - Cost variable
%
% The cost is the addition of the final distances of all the
% vehicles for a homogeneous fleet plus corresponding penalties for
% TW violations. 

costFunction(T,M,DeltaA,DeltaB,DeltaDep,Cost):-
    decompose(T,M,_,_,_,_,L),
    LB_viol #= sum(DeltaA),
    UB_viol #= sum(DeltaB),
    Dep_viol #= sum(DeltaDep),
    Cost #= sum(L) + 10*LB_viol + 50*UB_viol + 50*Dep_viol.
    
%-------------------------------------------------------------------------------

% costDistance(+D,+M,-Cost)
%
% D - Visits distance list
% M - Number of available vehicles
% Cost - Cost variable
%
% The cost is the addition of the final distances of all the
% vehicles for a homogeneous fleet. 

costDistance(D,M,Cost):-
    decompose(D,M,_,_,_,_,L),
    Cost#=sum(L).
    
%-------------------------------------------------------------------------------

% costVehicles(+V,+M,-Cost_Vehicles)
%
% V - Visits list
% M - Number of available vehicles
% Cost_Vehicles - Vehicle's cost variable
%
% This cost function is used when the number of used vehicles
% is to be minimised.
    
costVehicles(V,M,Cost_Vehicles) :-
	decompose(V,M,_,_,VisitsList,_,_),
	Cost_Vehicles #= max(VisitsList). 