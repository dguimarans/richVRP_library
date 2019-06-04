% costFunction(-D,+M,-Cost)
%
% D - Distance list
% M - Number of available vehicles
% Cost - Cost variable
%
% The cost is the addition of the final distances of all the
% vehicles for a homogeneous fleet. 

costFunction(D,M,Cost):-
	percentage(PCT),			%El resultat segurament serà float! canviar perquè ppugui multiplicar floatds
	decompose(D,M,_,_,_,_,L),
	
	(foreach(Li,L), foreach(PCTi,PCT), foreach(Ci,C) do
		Ci #= Li*PCTi
	)
    
    Cost#=sum(C).
	    
%-------------------------------------------------------------------------------
	
% costFunctionDistance(+SD,+V)
%
% SD - List of Nodes that can not be visited by a vehicle
% V - List of Visits
%
% A Node can not be visited by a certain Vehicle.
	
constraintVehicleSiteDependant(SD,V):-

	(foreach(SDi,SD), param (V) do
		length(SDi,L),
		(for(I,1,L-1), param(V,L), do
			(for(J,I+1,L), param(V,I) do
				ith(J,V,Vj),
				ith(I,V,Vi),
				Vi #\= Vj
			)
		)
	).
    
%-------------------------------------------------------------------------------
	
% constraintMaximumRouteLimit(-D,+M,+DMax)
%
% D - Distance list
% M - Number of available vehicles
% DMax - Maximum Route Distance
%
% The Total Route Distance is limited by a Maximum Distance.

constraintMaximumRouteLimit(D,M,DMax):-
	decompose(D,M,_,_,_,_,L),
	
	(foreach(Li,L), foreach(DMaxi,DMax) do
		Li #=< DMaxi
	).
       
%------------------------------------------------------------------------------

% constraintBalancedRoutes(-D,+M)
%
% D - Distance list
% M - Number of available vehicles
%
% 

constraintBalancedRoutes(D,M):-
	decompose(D,M,_,_,_,_,L),
	epsilon(Epsilon),
	(for(I,1,M-1), param(Epsilon) do
		(for(J,I+1,M), param(Epsilon,I) do
			ith(I,L,Li),
			ith(J,L,Lj),
			Li-Lj #=< Epsilon,
		)
	).