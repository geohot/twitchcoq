:- include(emulate).
:- include(monsters). 
:- include(search). 
:- include(generate). 
:- include(analyse). 
:- include(top). 

:- op(1000, fx, timex).
timex G :- time(G).

twod1 :- tell('machines2d1.txt'), 
	machine2d1(1), 
	machine2d1(2), 
	machine2d1(3), 	
	machine2d1(4), 
	machine2d1(5), 
	machine2d1(6), 
	machine2d1(7), 
	machine2d1(8), 
	machine2d1(9), 
	told. 

machine2d1(N) :-
	machine2d(N,M), 
	format("Machine ~d: ", [N]), write(M), nl, 
	format("Native: ~n", []), 
	emulate_2d(M, blank, 100, naive, rel, [], [final], _Hops1, _Status1, Outputs1), !, 
	transform_rel_to_abs(M, MT), 
	format("Transformed : ", []), write(MT), nl, 
	initial_state(IState), initial_index(Index), initial_map(Map), blank_symbol(Symbol), 
	initial_direction(Direction), transform_state(IState, Direction, State), 
	emulate_2d(MT, config2d(State, Index, Map, Symbol), 100, naive, abs, [], [final], _Hops1T, _Status1T, Outputs1T), !, 
        member(config2d(_, _, MapA, _), Outputs1T), member(config2d(_, _, MapR, _, _), Outputs1), 
        (MapA == MapR -> format("Same maps~n~n",[]); format("Maps differ~n~n", [])), 
	transform_abs_to_rel(MT, MTT), 
	format("Re-transformed : ", []), write(MTT), nl, 
	transform_state(State, Direction, NewIState), format("New starting state is ~k~n", [NewIState]), 
	emulate_2d(MTT, config2d(NewIState, Index, Map, Symbol, Direction), 100, naive, rel, [], [final], _Hops1TT, _Status1TT, Outputs1TT), !, 
        member(config2d(_, _, MapRR, _, _), Outputs1TT), 
        (MapRR == MapR -> format("Still same maps!~n~n",[]); format("Oops! Maps differ~n~n", [])), 
	true. 
    
twod2 :- tell('machines2d2.txt'), 
	machine2d2(1), 
	told. 

machine2d2(N) :-
	machine2dabs(N,M), 
	format("Machine ~d: ", [N]), write(M), nl, 
	format("Native: ~n", []), 
	emulate_2d(M, blank, 100, naive, abs, [], [final], _Hops1, _Status1, Outputs1), !, 
	transform_abs_to_rel(M, MT), 
	format("Transformed : ", []), write(MT), nl, 
	initial_state(IState), initial_index(Index), initial_map(Map), blank_symbol(Symbol), 
	initial_direction(Direction), transform_state(IState, Direction, State), 
	emulate_2d(MT, config2d(State, Index, Map, Symbol, Direction), 100, naive, rel, [], [final], _Hops1T, _Status1T, Outputs1T), 
        member(config2d(_, _, MapA, _), Outputs1), member(config2d(_, _, MapR, _, _), Outputs1T), 
        (MapA == MapR -> format("Same maps~n~n",[]); format("Maps differ~n~n", [])), 
	transform_rel_to_abs(MT, MTT), 
	format("Re-transformed : ", []), write(MTT), nl, 
	transform_state(State, Direction, NewIState), format("New starting state is ~k~n", [NewIState]), 
	emulate_2d(MTT, config2d(NewIState, Index, Map, Symbol), 100, naive, abs, [], [final], _Hops1TT, _Status1TT, Outputs1TT), !, 
        member(config2d(_, _, MapAA, _), Outputs1TT), 
        (MapAA == MapA -> format("Still same maps!~n~n",[]); format("Oops! Maps differ~n~n", [])), 
	true. 

relative(N) :-
    N >= 1, N =< 9,
    machine2d(N,M), emulate_2d(M, blank, 100, naive, rel, [], [final], _Hops, _Status, _Outputs).

absolute(N) :-
    N == 1, machine2dabs(N,M), emulate_2d(M, blank, 100, naive, abs, [], [final], _Hops, _Status, _Outputs). 
