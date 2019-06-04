%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%	Auxiliar functions for the CVRP model
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% decompose(+X,+M,?X_F,?X_L,?X_FL,?F,?L)
% This can be used with V (visits), Q (capacities) and T (times)
%
% X - List including (F)irst and (L)ast sublists
% M - Number of vehicles
% X_F - X without F
% X_L - X without L
% X_FL - X without F and L
% F - Sublist F
% L - Sublist L
%

decompose(X,M,X_F,X_L,X_FL,F,L):-
    length(L,M),once append(X_L,L,X),
    length(F,M),once append(X_FL,F,X_L),
    append(X_FL,L,X_F).

%-------------------------------------------------------------------------------

% decompose2(+X,+N,?X_L,?L)
% Notice this can be used with P, S and R
%
% X - List including First or (L)ast sublists
% N - Number of customers
% X_L - X without L
% L - Sublist L
%

decompose2(X,N,X_L,L):-
    length(X_L,N),once append(X_L,L,X).

%-------------------------------------------------------------------------------

% ith(+N,+L,-Nth)
%
% N - Position
% L - List
% Nth - Element in the Nth position of list L
% 

delay ith(N,V,_) if nonground(N).
ith(1,[H|_],H):-!.
ith(N,[_|T],P):-
    Naux is N-1,
    ith(Naux,T,P).

%-------------------------------------------------------------------------------

% position(-N,+L,+Nth)
%
% N - Position
% L - List
% Nth - Element in the Nth position of list L
% 

position(1,[H|_],H):-!.
position(N,[_|T],V):-
	position(Naux,T,V),
	N is Naux+1.

%-------------------------------------------------------------------------------

% domainPS(?I,+L,?Li)
%
% I - Position
% L - List
% Li - Element in the Nth position of list L
% 

delay domainPS(_,L,_) if nonground(L).
domainPS(I,L,Li) :- ground(L),!,element(I,L,Li).

%-------------------------------------------------------------------------------

% zeros(+N,-L)
%
% N - Length of list L
% L - List
% 
% Generates a list of N zeros
 
zeros(N,L):-
    length(L,N),!,
    (foreach(0,L) do true).
    
%-------------------------------------------------------------------------------

% instantiate(+-Real)
%
% Cost - A real variable with bounded domain
% 
% Instantiates a real variable to the lower bound of its domain.
% It works like indomain / 1 (IC library).

instantiate(Real) :-
	get_min(Real,MinReal),
	Real is MinReal.



% -----------------------------------------------------------------
% -----------------------------------------------------------------
% Input/Output rules for the Vehicle Routing Problem (VRP)
% -----------------------------------------------------------------
% -----------------------------------------------------------------

% readCustomers(-N,-M,-R)

readCustomers(N,M,R):-
    customers(Demands),
    vehicles(Capacities),
    length(Capacities,M),
    zeros(M,ZerosDepots),
    append(Demands,ZerosDepots,R),
%    append(TimesNoDepots,ZerosDepots,Times),
    length(Demands,N).

%-------------------------------------------------------------------------------

% readVehicles(+M,-Qv)

readVehicles(M,Qv):-
	vehicles(Qv),
	length(Qv,M).

%-------------------------------------------------------------------------------

% readVehicles(+M,-STimes)

readServiceTimes(M,STimes):-
	service_times(STimesNoDepot),
	zeros(M,ZerosDepots),
	append(STimesNoDepot,ZerosDepots,STimes).

%-------------------------------------------------------------------------------

% readCostsMatrix(-Times)

readCostsMatrix(Times) :-
	costs(Times).

%-------------------------------------------------------------------------------

% readCoordinates(-Coord)

readCoordinates(Coord) :-
	coords(Coord).

%-------------------------------------------------------------------------------

% calculateMatrix(-Times)

calculateMatrix(Times) :-
	coords(Coord),
	length(Coord,N),
	length(Times,N),
	(foreach(Ti,Times), param(N) do length(Ti,N)),
	(foreach([Xi,Yi|_],Coord), foreach(Ti,Times), param(Coord) do
		(foreach([Xj,Yj|_],Coord), foreach(Tij,Ti), param(Xi,Yi) do
			X_distance is (Xi-Xj)*(Xi-Xj),
			Y_distance is (Yi-Yj)*(Yi-Yj),
			Distance is X_distance + Y_distance,
			Euc_distance is sqrt(Distance),
			Tij is integer(round(Euc_distance))
		)
	).

%-------------------------------------------------------------------------------

% showSolution([+V,+Q,+T,+D,+R,+Qv,+P,+S],[+N,+M],+Cost,+B)
showSolution([V,Q,T,D,_R,_Qv,P,S,O,_Pairs],[_N,M],Cost,B):-
    cputime(CPUT),
    printf("--------------------------- %n",[]),
    printf("CPU Time = %p s %n",[CPUT]),
    decompose(V,M,_,_,VisitsList,_,_),
    NumVehicles is max(VisitsList),
    printf("Vehicles used = %p %n",[NumVehicles]),
    printf("--------------------------- %n",[]),
    printf("Visits = %p %n",[V]),
    printf("Cummulative capacities = %p %n",[Q]),
    printf("Cummulative times = %p %n",[T]),
    printf("Cummulative distance = %p %n",[D]),
    printf("Predecessors = %p %n",[P]),
    printf("Successors = %p %n",[S]),
    printf("Sequence = %p %n",[O]),
    printf("--------------------------- %n",[]),
    printf("Solution cost = %p %n",[Cost]),
    printf("Backtracks = %p %n",[B]).

%-------------------------------------------------------------------------------

% printSolution(+ProblemName,[+V,+Q,+T,+D,+R,+Qv,+P,+S],[+N,+M],+DeltaA,+DeltaB,+DeltaDep,+Cost,+B)
printSolution(ProblemName,[V,Q,T,D,_R,_Qv,P,S,O,_Pairs],[_N,M],DeltaA,DeltaB,DeltaDep,Cost,B):-
    cputime(CPUT),
    decompose(V,M,_,_,VisitsList,_,_),
    NumVehicles is max(VisitsList),
    sum(DeltaA,Aa),
    sum(DeltaB,Bb),
    sum(DeltaDep,Dep),
    open(ProblemName,write,file),
    set_flag(print_depth,151),
    printf(file,"CPU Time = %p s %n",[CPUT]),
    printf(file,"--------------------------- %n",[]),
    printf(file,"Vehicles used = %p %n",[NumVehicles]),
    printf(file,"Solution cost = %p %n",[Cost]),
    printf(file,"--------------------------- %n",[]),
    printf(file,"Visits = %p %n",[V]),
    printf(file,"Cummulative capacities = %p %n",[Q]),
    printf(file,"Cummulative times = %p %n",[T]),
    printf(file,"Cummulative distance = %p %n",[D]),
    printf(file,"Predecessors = %p %n",[P]),
    printf(file,"Successors = %p %n",[S]),
    printf(file,"Sequence = %p %n",[O]),
    printf(file,"--------------------------- %n",[]),
    printf(file,"Delta A = %p - %p %n",[Aa,DeltaA]),
    printf(file,"Delta B = %p - %p %n",[Bb,DeltaB]),
    printf(file,"Delta Depot = %p - %p %n",[Dep,DeltaDep]),
    printf(file,"--------------------------- %n",[]),
    printf(file,"Backtracks = %p %n",[B]),
    close(file).
    
% printSolution(+ProblemName,[+V,+Q,+T,+D,+R,+Qv,+P,+S],[+N,+M],+Cost,+B)
printSolution(ProblemName,[V,Q,T,D,_R,_Qv,P,S,O,_Pairs],[_N,M],Cost,B):-
    cputime(CPUT),
    decompose(V,M,_,_,VisitsList,_,_),
    NumVehicles is max(VisitsList),
    open(ProblemName,write,file),
    set_flag(print_depth,151),
    printf(file,"CPU Time = %p s %n",[CPUT]),
    printf(file,"--------------------------- %n",[]),
    printf(file,"Vehicles used = %p %n",[NumVehicles]),
    printf(file,"Solution cost = %p %n",[Cost]),
    printf(file,"--------------------------- %n",[]),
    printf(file,"Visits = %p %n",[V]),
    printf(file,"Cummulative capacities = %p %n",[Q]),
    printf(file,"Cummulative times = %p %n",[T]),
    printf(file,"Cummulative distance = %p %n",[D]),
    printf(file,"Predecessors = %p %n",[P]),
    printf(file,"Successors = %p %n",[S]),
    printf(file,"Sequence = %p %n",[O]),
    printf(file,"--------------------------- %n",[]),
    printf(file,"Backtracks = %p %n",[B]),
    close(file).