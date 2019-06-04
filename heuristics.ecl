%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%	Heuristic functions for the CVRP model
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%----------------------------------------------------------------------
% VNS structure
%----------------------------------------------------------------------

%%%%% Simple solver for tests

simple_solve([V,_,T,_,_,_,_P,S,_O,_],[_N,_M],Cost,B) :-
	set_flag(print_depth,151),
%	orderingTW(S,FeasA),
	flatten([V,S],VARSflat),
	bb_min(
		(search(VARSflat,0,most_constrained,indomain_min,complete,[backtrack(B)]),indomain(Cost)),
		Cost,
		bb_options{strategy:continue}
	),
	once labeling(T)
	.

vns([V,_,T,_D,_,_,P,S,_,_],[N,M],Cost,B) :-
	init_memory(Memory),
	flatten([V,P,S,T],VARSflat),
	Number is 10,
	get_close_neighbours_list(N,Number,CloserLists),

	writeln('Launching VNS...'),

	bb_min((
		 ( no_remembered_values(Memory) ->
			once labeling(VARSflat),
			writeln(VARSflat),
			bb_min((
				search(VARSflat,0,most_constrained,indomain_min,complete,[backtrack(B)]),indomain(Cost)),
				Cost,bb_options{strategy:continue,timeout:60}
			),
			writeln('First solution found:'),
			writeln(V),
			writeln(P),
			writeln(S),
			remember_values(Memory,[V,P,S])
		 ;
			between(1,2,1,Neighbourhood),
			(Neighbourhood =:= 1 ->
				between(1,4,1,Area),
				bb_min((
					install_customers_by_area(Memory, [V,P,S], [N,M], Area),
					search(VARSflat,0,most_constrained,indomain_min,complete,[backtrack(B)]),indomain(Cost)),
					Cost,bb_options{strategy:restart,timeout:60}
				),
				remember_values(Memory,[V,P,S])
			;
				true
			),
			(Neighbourhood =:= 2 ->
				between(1,10,1,MaxCustomers),
				Probability is 0.5,
				bb_min((
					install_but_random_customers(Memory, [V,P,S], [N,M], CloserLists, MaxCustomers, Probability),
					search(VARSflat,0,most_constrained,indomain_min,complete,[backtrack(B)]),indomain(Cost)),
					Cost,bb_options{strategy:restart,timeout:60}
				),
				remember_values(Memory,[V,P,S])
			;
				true
			)
		 )
		),
		Cost,
		bb_options{strategy:restart}
	).


%----------------------------------------------------------------------
% Saving a solution
%----------------------------------------------------------------------

init_memory(Memory) :-
	shelf_create(memory([],[],[],_), Memory).

no_remembered_values(Memory) :-
	shelf_get(Memory, 1, []).

remember_values(_Memory, []) :- !.
remember_values(Memory, [V,P,S]) :-
	shelf_set(Memory, 1, V),
	shelf_set(Memory, 2, P),
	shelf_set(Memory, 3, S).


%----------------------------------------------------------------------
% Common predicates for all strategies
%----------------------------------------------------------------------

% get_affected_customers(+Customers,-Affected,+P_S_List)
%
% Customers - list of chosen customers
% Affected - list of chosen and affected customers
% List - Predecessors or Successors list to determine affected customers
%

get_affected_customers([],[],_) :- !.
get_affected_customers([Ci|Customers],[Ci,Pi|Tail],L) :-
	ith(Ci,L,Pi),
	get_affected_customers(Customers,Tail,L).


%----------------------------------------------------------------------
% Unfix customers in an area
%----------------------------------------------------------------------


% raw_beam_search(+N,+Area,-CustomersList)

raw_beam_search(N,Area,CustomersList) :-
	readCoordinates(Coord),
	decompose2(Coord,N,CoordWoDep,_),
	transpose(CoordWoDep,CoordWoDepT),
	(foreach(AxisCoord,CoordWoDepT),foreach(CoordCent_i,CoordCent), param(N) do
		CoordCent_i is sum(AxisCoord)/N
	),
	reverse(CoordWoDep,CoordReversed),
	choose_customers_in_area(N,CustomersList,CoordReversed,CoordCent,Area).

choose_customers_in_area(0,[],[],_,_) :- !.
choose_customers_in_area(N,[Selected_customer|Tail],[Coord_i|TailCoord],CoordC,Area) :-
	Area =:= 1,
	ith(1,Coord_i,Xi),
	ith(2,Coord_i,Yi),
	ith(1,CoordC,XC),
	ith(2,CoordC,YC),
	Xi >= XC,
	Yi >= YC,
	Naux is N-1,
	Selected_customer is N,
	choose_customers_in_area(Naux,Tail,TailCoord,CoordC,Area).
choose_customers_in_area(N,[Selected_customer|Tail],[Coord_i|TailCoord],CoordC,Area) :-
	Area =:= 2,
	ith(1,Coord_i,Xi),
	ith(2,Coord_i,Yi),
	ith(1,CoordC,XC),
	ith(2,CoordC,YC),
	Xi =< XC,
	Yi >= YC,
	Naux is N-1,
	Selected_customer is N,
	choose_customers_in_area(Naux,Tail,TailCoord,CoordC,Area).
choose_customers_in_area(N,[Selected_customer|Tail],[Coord_i|TailCoord],CoordC,Area) :-
	Area =:= 3,
	ith(1,Coord_i,Xi),
	ith(2,Coord_i,Yi),
	ith(1,CoordC,XC),
	ith(2,CoordC,YC),
	Xi =< XC,
	Yi =< YC,
	Naux is N-1,
	Selected_customer is N,
	choose_customers_in_area(Naux,Tail,TailCoord,CoordC,Area).
choose_customers_in_area(N,[Selected_customer|Tail],[Coord_i|TailCoord],CoordC,Area) :-
	Area =:= 4,
	ith(1,Coord_i,Xi),
	ith(2,Coord_i,Yi),
	ith(1,CoordC,XC),
	ith(2,CoordC,YC),
	Xi >= XC,
	Yi =< YC,
	Naux is N-1,
	Selected_customer is N,
	choose_customers_in_area(Naux,Tail,TailCoord,CoordC,Area).
choose_customers_in_area(N,Tail,[_|TailCoord],CoordC,Area) :-
	Naux is N-1,
	choose_customers_in_area(Naux,Tail,TailCoord,CoordC,Area).

install_customers_by_area(_Memory, [], _, _) :- !.
install_customers_by_area(Memory, [V,P,S], [N,M], Area) :-
	raw_beam_search(N,Area,SelectedCustomers),
	shelf_get(Memory, 1, PrevVwDep),
	shelf_get(Memory, 2, PrevP),
	shelf_get(Memory, 3, PrevS),
	decompose(PrevVwDep,M,_,_,PrevV,_,_),
	(foreach(PrevVi,PrevV), for(I,1,N), param(V,SelectedCustomers) do
		(member(I,SelectedCustomers) ->
			true
		;
			ith(I,V,PrevVi)
		)
	),
	get_affected_customers(SelectedCustomers,CustPredecessors,PrevS),
	get_affected_customers(SelectedCustomers,CustSuccessors,PrevP),
	Dim is N+M,
	(foreach(PrevPi,PrevP), foreach(PrevSi,PrevS), for(I,1,Dim), param(P,S,CustPredecessors,CustSuccessors) do
		(member(I,CustPredecessors) ->
			true
		;
			ith(I,P,PrevPi)
		),
		(member(I,CustSuccessors) ->
			true
		;
			ith(I,S,PrevSi)
		)
	).


%----------------------------------------------------------------------
% Unfix customers chosen randomly
%----------------------------------------------------------------------

% get_close_neighbours_list(+N,+Number,-CloserLists)
%
% N - number of customers
% Number - number of nearest neighbours to be chosen
% CloserLists - Nested lists with closest customers
%

get_close_neighbours_list(N,Number,CloserLists) :-
	calculateMatrix(Times),
	length(CloserLists,N),
	(for(I,1,N),param(Number,Times,CloserLists) do
		ith(I,Times,Ti),
		ith(I,CloserLists,CLi),
		length(CLi,Number),
		msort(Ti,TSi),
		ic: alldifferent(CLi),
%		(for(J,1,Number),param(CLi,Ti,TSi) do
%			Index is J+1,
%			ith(Index,TSi,Min),
%			position(Cust,Ti,Min),
%%			element(Cust,Ti,Min),
%			(member(Cust,CLi) ->
%						writeln(CLi),
%				Index_1 is J+2,
%				ith(Index_1,TSi,Min_1),
%				position(Cust_1,Ti,Min_1),
%				member(Cust_1,CLi)
%			;
%				member(Cust,CLi),
%				writeln('Cust was not found' - CLi)
%			)
%	 	),
		(fromto(1,In,Out,99),param(CLi,Ti,TSi) do
			Index is In+1,
			ith(Index,TSi,Min),
			position(Cust,Ti,Min),
%			element(Cust,Ti,Min),
			member(Cust,CLi),
			(ground(CLi) ->
				Out is 99
			;
				Out is In+1
			)
		),
		once labeling(CLi)
	).

% choose_random_customers
%
% Based on the following predicate:
% buildlist([],0).
% buildlist([N|Ts],N) :-
% 	Naux is N-1,
% 	buildlist(Ts,Naux).

choose_random_customers(_,[],0,_) :- !.
choose_random_customers(0,[],_,_) :- !.
choose_random_customers(N,[Selected_customer|Tail],How_many,Probability) :-
	(frandom =< Probability ->
		Naux is N-1,
		Selected_customer is N,
		Remaining is How_many - 1,
		choose_random_customers(Naux,Tail,Remaining,Probability)
	;
		fail
	).
choose_random_customers(N,Tail,How_many,Probability) :-
	Naux is N-1,
	choose_random_customers(Naux,Tail,How_many,Probability).

return_surrounding_customers([],_CloserLists,[]) :- !.
return_surrounding_customers([Pivot|PivotTail],CloserLists,[Pivot,SurrCust|SelTail]) :-
	ith(Pivot,CloserLists,SurrCust),
	return_surrounding_customers(PivotTail,CloserLists,SelTail).
	

install_but_random_customers(_Memory, [], _, _, _, _) :- !.
install_but_random_customers(Memory, [V,P,S], [N,M], CloserLists, MaxCustomers, Probability) :-
	choose_random_customers(N,PivotCustomers,MaxCustomers,Probability),
	return_surrounding_customers(PivotCustomers,CloserLists,SelectedNestedCustomers),
	flatten(SelectedNestedCustomers,SelectedCustomers),
	shelf_get(Memory, 1, PrevVwDep),
	shelf_get(Memory, 2, PrevP),
	shelf_get(Memory, 3, PrevS),
	decompose(PrevVwDep,M,_,_,PrevV,_,_),
	(foreach(PrevVi,PrevV), for(I,1,N), param(V,SelectedCustomers) do
		(member(I,SelectedCustomers) ->
			true
		;
			ith(I,V,PrevVi)
		)
	),
	get_affected_customers(SelectedCustomers,CustPredecessors,PrevS),
	get_affected_customers(SelectedCustomers,CustSuccessors,PrevP),
	Dim is N+M,
	(foreach(PrevPi,PrevP), foreach(PrevSi,PrevS), for(I,1,Dim), param(P,S,CustPredecessors,CustSuccessors) do
		(member(I,CustPredecessors) ->
			true
		;
			ith(I,P,PrevPi)
		),
		(member(I,CustSuccessors) ->
			true
		;
			ith(I,S,PrevSi)
		)
	).
	
	
%----------------------------------------------------------------------
% Time Windows Pre-processing
%----------------------------------------------------------------------

% preprocess_TW([+V,_,_,_,_,_,_,_,_,_],[+N,+M])
%
% V - Visits list
% P - Predecessors list
% S - Successors list
% N - Number of customers
% M - Number of available vehicles
%

preprocess_TW([V,_,_,_,_,_,_,_,_,_],[N,M]) :-
	calculateMatrix(Times),
	readServiceTimes(M,STimes),
	time_windows(TW),
	N1 is N-1,
	( for(I,1,N1), param(V,Times,STimes,TW,N) do
		I1 is I+1,
		( for(J,I1,N), param(V,Times,STimes,TW,I) do
			ith(I,Times,Ti),
			ith(J,Ti,Tij),
			ith(I,STimes,STi),
			ith(J,STimes,STj),
			ith(I,TW,TWi), ith(1,TWi,Ai), ith(2,TWi,Bi),
			ith(J,TW,TWj), ith(1,TWj,Aj), ith(2,TWj,Bj),
			Cost_i is Ai + STi + Tij,
			Cost_j is Aj + STj + Tij,
			( (Cost_i > Bj) and (Cost_j > Bi) ->
				ith(I,V,Vi), ith(J,V,Vj), Vi #\= Vj
			;
				true
			)
		)
	).
	
preprocess_HTW([V,_,_,_,_,_,_P,_S,_,_],[N,M]) :-
	calculateMatrix(Times),
	readServiceTimes(M,STimes),
	time_windows(TW),
	N1 is N-1,
	( for(I,1,N1), param(V,_P,_S,Times,STimes,TW,N) do
		I1 is I+1,
		( for(J,I1,N), param(V,_P,_S,Times,STimes,TW,I) do
			ith(I,Times,Ti),
			ith(J,Ti,Tij),
			ith(I,STimes,STi),
			ith(J,STimes,STj),
			ith(I,TW,TWi), ith(1,TWi,Ai), ith(2,TWi,Bi),
			ith(J,TW,TWj), ith(1,TWj,Aj), ith(2,TWj,Bj),
			Cost_i is Ai + STi + Tij,
			Cost_j is Aj + STj + Tij,
%			Cost_i2 is Bi + STi + Tij,
%			Cost_j2 is Bj + STj + Tij,
%			( Cost_i > Bj -> ith(J,P,Pj), ith(I,S,Si), Pj #\= I, Si #\= J ; true ),
%			( Cost_j > Bi -> ith(I,P,Pi), ith(J,S,Sj), Pi #\= J, Sj #\= I ; true ),
%			( Cost_i2 < Aj -> ith(J,P,Pj), ith(I,S,Si), Pj #\= I, Si #\= J ; true ),
%			( Cost_j2 < Ai -> ith(I,P,Pi), ith(J,S,Sj), Pi #\= J, Sj #\= I ; true ),
			( (Cost_i > Bj) and (Cost_j > Bi) ->
				ith(I,V,Vi), ith(J,V,Vj), Vi #\= Vj
			;
				true
			)
		)
	).
	


%----------------------------------------------------------------------
% Nearest Neighbour Heuristic
%----------------------------------------------------------------------

% nearestNeighbourHeuristic(+S,-Distances)
%
% S - List of successors
% Distances - Possible destinations for each customers
%
% Nearest Neighbour Heuristic combined with a 'smallest' search heuristic.
% This predicate return a list of distances to all connected nodes from
% a certain customers.
%

nearestNeighbourHeuristic(S,Distances) :-
	calculateMatrix(Tij),
	( foreach(DistancesFromI,Tij), foreach(SI,S), foreach(DistFromI,Distances) do
	    element(SI, DistancesFromI, DistFromI)
	).
	
	
%----------------------------------------------------------------------
% TW ordering Heuristic
%----------------------------------------------------------------------

orderingTW(S,FeasA) :-
	time_windows(TW),
	( foreach(TWi,TW), foreach(Ai,As) do
		element(1,TWi,Ai)
	),
	( foreach(Si,S), foreach(FeasAi, FeasA), param(As) do
		element(Si, As, FeasAi)
	).