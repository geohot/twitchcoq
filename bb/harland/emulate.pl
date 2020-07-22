emulate_bb(M, Bound, Mode, Inputs, Ones, Hops, Status, Outputs) :-
    % emulate_general(M, blank, Bound, Mode, eval, [loop,blank,escape], Inputs, Hops, Status, Outputs),
    emulate_general(M, blank, Bound, Mode, eval, [loop,blank], Inputs, Hops, Status, Outputs),
    member(config(Left, State, Item, Dir, Right), Outputs),
    count_ones(config(Left, State, Item, Dir, Right), Ones),

    ( member(final, Inputs) ->   ( final_output(config(Left,State,Item,Dir,Right), Ones, Hops, Outputs)  ) ; true ), 
    ( member(machine, Inputs) -> ( (member(machine(_,Trans,_Otters), Outputs), display_trans(Trans), display_loops(Trans), nl) ) ; true ), 
    % display_otters(Otters), nl,
    true. 

final_output(config(Left,State,Item,Dir,Right), Ones, Hops, Outputs) :- 
    format("Final configuration is ", []), 
    display_config(config(Left, State, Item, Dir, Right)), !, % nl,
    format(" Ones: ", []), print_bignum(Ones), !, ttyflush, 
    format(" Hops: ", []), print_bignum(Hops), !, ttyflush, 
    member(steps(Steps), Outputs),           format(" Steps: ", []),  print_bignum(Steps), !, ttyflush, 
    member(otters(Otters), Outputs),         format(" Otters: ", []), print_bignum(Otters), !, ttyflush, 
    member(ottersnested(OttersNested), Outputs),         format(" Otters Nested: ", []), print_bignum(OttersNested), !, ttyflush, 
    member(ottersteps(OtterSteps), Outputs), format(" Otter Steps: ", []), print_bignum(OtterSteps), !, ttyflush, 
    member(otterjumps(OtterJumps), Outputs), format(" Otter Jumps: ", []), print_bignum(OtterJumps), !, ttyflush, 

    member(ocelots(Ocelots), Outputs),         format(" Ocelots: ", []), print_bignum(Ocelots), !, ttyflush, 
    member(ocelotsteps(OcelotSteps), Outputs), format(" Ocelot Steps: ", []), print_bignum(OcelotSteps), 
    extract_shape(config(Left, State, Item, Dir, Right), Shape), format(" Shape: ", []), display_config(Shape), 
    shape_size(config(Left, State, Item, Dir, Right), Size),     format(" Shape Size: ~d ", [Size]),  
    format("~n", []), !, ttyflush, 
    true.

extract_shape(config(Left, State, Item, Dir, Right), config(SLeft, State, SItem, Dir, SRight)) :-
    extract_shape1(Left, SLeft),												    
    extract_shape1([Item], [SItem]),
    extract_shape1(Right, SRight).

extract_shape1([], []).
extract_shape1([Item|Rest], [Item|Result]) :- is_input(Item), extract_shape1(Rest, Result).
extract_shape1([grp(I,N)|Rest], [grp(I,N)|Result]) :- integer(N), N =< 3, extract_shape1(Rest, Result). 
extract_shape1([grp(I,N)|Rest], [grp(I,'*')|Result]) :- integer(N), N > 3, extract_shape1(Rest, Result). 
extract_shape1([grp(I,N)|Rest], [grp(I,'*')|Result]) :- \+ integer(N), extract_shape1(Rest, Result).

shape_size(config(Left, _, Item, _, Right), Size) :-
    append(Left, [Item], Temp), append(Temp, Right, Tape),
    shape_size1(Tape, 0, Size).

shape_size1([], Size, Size).
shape_size1([Item|Rest], SizeSoFar, Size) :-
    is_input(Item), 
    NewSizeSoFar is SizeSoFar + 1,
    shape_size1(Rest, NewSizeSoFar, Size).
shape_size1([Item|Rest], SizeSoFar, Size) :-
    Item = grp(I,N), integer(N), N =< 3, length(I, L), 
    NewSizeSoFar is SizeSoFar + N*L,
    shape_size1(Rest, NewSizeSoFar, Size).
shape_size1([Item|Rest], SizeSoFar, Size) :-
    Item = grp(I,N), integer(N), N > 3, length(I, L), 
    NewSizeSoFar is SizeSoFar + 4*L,  % So all sizes 4 or bigger are the same ... 
    shape_size1(Rest, NewSizeSoFar, Size).
shape_size1([Item|Rest], SizeSoFar, Size) :-
    Item = grp(I,N), variable(N), length(I, L), 
    NewSizeSoFar is SizeSoFar + 4*L,  % Treat variables as 4 or bigger.
    shape_size1(Rest, NewSizeSoFar, Size).

% Need to think carefully about the verify case architecture ... 

initial_config(naive, eval, blank, config([], a, I, l, []), 0) :- blank_symbol(I), !. 
initial_config(naive, verify, blank, config([], a, I, l, []), 0) :- blank_symbol(I), !. % Only use variable hops for ossify, not verify. 
initial_config(naive, ossify, blank, config([], a, I, l, []), hops(0, [])) :- blank_symbol(I), !. 
initial_config(naive, eval, config(Left, State, Item, Dir, Right), config(Left, State, Item, Dir, Right), 0). 
initial_config(naive, verify, config(Left, State, Item, Dir, Right), config(Left, State, Item, Dir, Right), 0).
initial_config(naive, ossify, config(Left, State, Item, Dir, Right), config(Left, State, Item, Dir, Right), hops(0, VarList)) :- initial_vars(config(Left, State, Item, Dir, Right), VarList). 

initial_config(macro(K), eval, blank, config([], a, grp(List,1), l, []), 0) :- integer(K), blanks(K, List). 
initial_config(macro(K), verify, blank, config([], a, grp(List,1), l, []), 0) :- integer(K), blanks(K, List).
initial_config(macro(K), ossify, blank, config([], a, grp(List,1), l, []), hops(0, [])) :- integer(K), blanks(K, List).
initial_config(macro(_K), eval, config(Left, State, Item, Dir, Right), config(Left, State, Item, Dir, Right), 0). 
initial_config(macro(_K), verify, config(Left, State, Item, Dir, Right), config(Left, State, Item, Dir, Right), 0).
initial_config(macro(_K), ossify, config(Left, State, Item, Dir, Right), config(Left, State, Item, Dir, Right), hops(0, VarList)) :- initial_vars(config(Left, State, Item, Dir, Right), VarList). 
initial_config(adapt, eval, blank, config([], a, I, l, []), 0) :- blank_symbol(I), !. 
initial_config(adapt, verify, blank, config([], a, I, l, []), 0) :- blank_symbol(I), !. 
initial_config(adapt, ossify, blank, config([], a, I, l, []), hops(0,[])) :- blank_symbol(I), !. 
initial_config(adapt, eval, config(Left, State, Item, Dir, Right), config(Left, State, Item, Dir, Right), 0). 
initial_config(adapt, verify, config(Left, State, Item, Dir, Right), config(Left, State, Item, Dir, Right), 0).
initial_config(adapt, ossify, config(Left, State, Item, Dir, Right), config(Left, State, Item, Dir, Right), hops(0, VarList)) :- initial_vars(config(Left, State, Item, Dir, Right), VarList). 
initial_config(flex, eval, blank, config([], a, grp(List,1), l, []), 0) :- blanks(1, List), !. % Act like macro(1) initially
initial_config(flex, verify, blank, config([], a, grp(List,1), l, []), 0) :- blanks(1, List), !. % Act like macro(1) initially
initial_config(flex, ossify, blank, config([], a, grp(List,1), l, []), hops(0,[])) :- blanks(1, List), !. % Act like macro(1) initially
initial_config(flex, eval, config(Left, State, Item, Dir, Right), config(Left, State, Item, Dir, Right), 0). 
initial_config(flex, verify, config(Left, State, Item, Dir, Right), config(Left, State, Item, Dir, Right), 0).
initial_config(flex, ossify, config(Left, State, Item, Dir, Right), config(Left, State, Item, Dir, Right), hops(0, VarList)) :- initial_vars(config(Left, State, Item, Dir, Right), VarList). 

initial_vars(config(Left, _State, Item, _Dir, Right), VarList) :- append(Left, [Item|Right], Tape), initial_vars1(Tape, VarList). 
initial_vars1([], []).
initial_vars1([grp(_I, Num)|Rest], VarList) :- integer(Num), initial_vars1(Rest, VarList). 
initial_vars1([grp(_I, Num)|Rest], [h(Name,0)|VarList]) :- variable(Num), get_name(Num, Name), initial_vars1(Rest, VarList). 

% initial_config(_, config(Left, State, Item, Dir, Right), config(Left, State, Item, Dir, Right)). 
% initial_config(naive, blank, config([], a, I, l, [])) :- blank_symbol(I), !. 
% initial_config(macro(K), blank, config([], a, grp(List,1), l, [])) :- integer(K), blanks(K, List). 
% initial_config(adapt, blank, config([], a, I, l, [])) :- blank_symbol(I), !. 
% initial_config(flex, blank, config([], a, grp(List,1), l, [])) :- blanks(1, List), !. % Act like macro(1) initially
% initial_config(search, blank, config([], a, grp(List,1), l, [])) :- blanks(1, List), !. % Act like macro(1) initially

% Status is one of halts, going, going(S), abort, abort(S), loops(cycle), blank, loops(road_runner), target(_), will soon include others.

emulate_general(M, Start, B, Mode, Type, Termination, Inputs, Hops, Status, NewOutputs) :-
     initial_config(Mode, Type, Start, Config, InitHops), 
     machine(Mode, M, Machine), 
	number_of_states(Machine, States),
	number_of_symbols(Machine, Symbols),
	% number_of_dirs(Machine, Directions), 
	Directions = 2, 
     process_inputs(States, Symbols, Directions, Inputs, Config, Inputs1), 
     process_bound(B, Bound), 
     % format("about to execute~n", []), 
     output_status(M, Config, Mode, 0, Inputs1, NewInputs, init), 
     % format("Really!~n", []), 
     execute(Machine, Config, Bound, Mode, InitHops, Termination, NewInputs, Result), % Need to allow for Hops being a variable as well ... 
     Result = result(Machine1, Config1, Bound, Mode, Hops, _, Outputs, Status), 
     append(Outputs, [Machine1], Outputs1),  
     append([Config1], Outputs1, Outputs2),
     NewOutputs = Outputs2, 
     !. 
 
emulate_search(States, Symbols, Directions, M, Start, B, Mode, Termination, Inputs, FinalMachine, Ones, Hops, Status, NewOutputs) :-
     % initial_config(Mode, Start, Config), 
     initial_config(flex, eval, Start, Config, InitHops), 
     % format("% Init done~n", []), ttyflush, 

     machine(Mode, M, Machine),				
     process_inputs(States, Symbols, Directions, Inputs, Config, Inputs1), 
     process_bound(B, Bound), 
     % format("% Processing done~n", []), format("% Inputs are ", []), write(Inputs1), nl, ttyflush, 

     % format("% M is ", []), write(M), nl, 
     % format("% Machine is ", []), write(Machine), nl, 
     % output_status(Machine, Config, Mode, 0, Inputs1, NewInputs, init),

     output_status(Machine, Config, Mode, 0, Inputs1, NewInputs, init),
     % format("% Executing ... ~n", []), ttyflush, 
     execute_search(States, Symbols, Directions, Machine, Config, Bound, Mode, InitHops, Termination, NewInputs, Result),
     Result = result(FinalMachine, FinalConfig, _Bound1, Mode, Hops, _, Outputs, Status),
     % format("% Execution done with Machine ", []), write(FinalMachine), nl, 
     append(Outputs, [FinalMachine], Outputs1),  append([FinalConfig], Outputs1, Outputs2),
     NewOutputs = Outputs2, 
     % format("% Appending done~n", []), 
     count_ones(FinalConfig, Ones),
     % format("% Count done~n", []), 
     true.

emulate_2d(M, Start, B, Mode, Type, Termination, Inputs, Hops, Status, NewOutputs) :-
     machine(Mode, M, Machine), 
	number_of_states(Machine, States),
	number_of_symbols(Machine, Symbols),
	% number_of_dirs(Machine, Directions), 
	Directions = 4,
     % format("About to initialise~n", []), 
     initial_config2d(Type, Start, Config, InitHops), 	
     % format("About to process 1~n", []), 
     process_inputs(States, Symbols, Directions, Inputs, Config, Inputs1), 
     % format("About to process 2~n", []), 
     process_bound(B, Bound), 
     % format("about to execute~n", []), 
     output_status(M, Config, Mode, 0, Inputs1, NewInputs, init), 
     % format("Really!~n", []), 
     execute2d(Machine, Config, Bound, Mode, Type, InitHops, Termination, NewInputs, Result), 
     Result = result(Machine1, Config1, Bound, Mode, Hops, _, Outputs, Status), 
     append(Outputs, [Machine1], Outputs1),  
     append([Config1], Outputs1, Outputs2),
     NewOutputs = Outputs2,
     (member(final, Inputs) -> (output_config(M, Config1, Mode, Hops, Outputs, final), nl) ; true), 
     !.

initial_config2d(rel, config2d(State, Index, Map, Symbol, Direction), config2d(State, Index, Map, Symbol, Direction), 0).
initial_config2d(rel, blank, config2d(State, Index, Map, Symbol, Direction), 0) :- initial_state(State), initial_index(Index), initial_map(Map), initial_direction(Direction), blank_symbol(Symbol).
initial_config2d(abs, config2d(State, Index, Map, Symbol), config2d(State, Index, Map, Symbol), 0).
% initial_config2d(abs, blank, config2d(State, Index, Map, Symbol), 0) :- initial_index(Index), initial_map(Map), initial_direction(Direction), transform_state(a, Direction, State), blank_symbol(Symbol).
initial_config2d(abs, blank, config2d(State, Index, Map, Symbol), 0) :- initial_state(State), initial_index(Index), initial_map(Map), blank_symbol(Symbol).

% 11 x 11 blank grid
initial_map(map(
	row(0,  [B,B,B,B,B,B,B,B,B,B,B]),
	row(1,  [B,B,B,B,B,B,B,B,B,B,B]),
	row(2,  [B,B,B,B,B,B,B,B,B,B,B]),
	row(3,  [B,B,B,B,B,B,B,B,B,B,B]),
	row(4,  [B,B,B,B,B,B,B,B,B,B,B]),
	row(5,  [B,B,B,B,B,B,B,B,B,B,B]),
	row(6,  [B,B,B,B,B,B,B,B,B,B,B]),
	row(7,  [B,B,B,B,B,B,B,B,B,B,B]),
	row(8,  [B,B,B,B,B,B,B,B,B,B,B]),
	row(9,  [B,B,B,B,B,B,B,B,B,B,B]),
	row(10, [B,B,B,B,B,B,B,B,B,B,B])
        )
    ) :- blank_symbol(B).
initial_index(i(5,5)). % middle of grid
initial_direction(n).

process_inputs(States, _Symbols, Directions, Inputs, Config, Inputs2) :-
    Directions == 2, 
    (member(loop, Inputs); member(history, Inputs); member(otter, Inputs); member(ocelot, Inputs)), 
    set_type(Inputs, Type), 
    initial_history(Type, States, Directions, History), 	
    append([now(Config), history(History)], Inputs, Inputs1), % history initialisation
    append([pos(0), steps(0), otters(0), ottersnested(0), ottersteps(0), otterjumps(0), ocelots(0), ocelotsteps(0)], Inputs1, Inputs2).

process_inputs(_States, _Symbols, Directions, Inputs, _Config, Inputs1) :-
    Directions == 2, 
    \+ member(loop, Inputs), \+ member(history, Inputs), \+ member(otter, Inputs), \+ member(ocelot, Inputs), 
    append([pos(0), steps(0), otters(0), ottersnested(0), ottersteps(0), otterjumps(0), ocelots(0), ocelotsteps(0)], Inputs, Inputs1).

process_inputs(_States, _Symbols, Directions, Inputs, _Config, Inputs1) :-
    Directions > 2, % No history etc for now ... 
    append([steps(0)], Inputs, Inputs1).

process_bound(N, N) :- integer(N). 
process_bound(mill(N), Num) :- integer(N), Num is N*1000000. % Num is N million.
process_bound(bill(N), Num) :- integer(N), Num is N*1000000000. % Num is N billion.
process_bound(trill(N), Num) :- integer(N), Num is N*1000000000000. % Num is N trillion.
process_bound(tens(N), Num) :- integer(N), Num is 10 ** N. % Num is 10**N.

find_trans(machine(M,_,_), M).
find_trans(M, M) :- M \= machine(_,_,_). 

machine(_, M, M) :- M = machine(_,_,_), !. 
machine(naive, M, machine(M, [], [])).
machine(macro(_K), M, machine(M, [], [])).
machine(adapt, M, machine(M, [], [])).
machine(flex, M, machine(M, [], [])).
machine(search, M, machine(M, [], [])).

execute(M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
    % format("Halt?~n", []), 
    halt_execution(0,0,0, M, Config, Bound, Mode, Hops, Termination, Inputs, Result), !. 
execute(M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
    % format("About to config~n", []), ttyflush, 
    % write(Inputs), nl, write(Config), display_config(Config), nl, 
    next_config(0, 0, 0, M, Config, Mode, Hops, Inputs, NewM, NewConfig, NewHops, NewInputs, Used), !, 
    output_status(M, NewConfig, Mode, NewHops, NewInputs, NewerInputs, Used), !, 
    % display(NewInputs), nl, 
    execute(NewM, NewConfig, Bound, Mode, NewHops, Termination, NewerInputs, Result). 

% No cuts for this one ... 
% mode 'search' which subsumes flex, but has different behaviour on missing transitions and on termination.
% Need also to add more cases to `looping' termination to include all analysis ...

execute_search(States, Symbols, Dirs, M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
    halt_execution(States, Symbols, Dirs, M, Config, Bound, Mode, Hops, Termination, Inputs, Result),  
    % format("% Halted~n", []), 
    true. 
execute_search(States, Symbols, Dirs, M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
    \+ halt_execution(States, Symbols, Dirs, M, Config, Bound, Mode, Hops, Termination, Inputs, _Result), 
    % format("% Moving on ...~n", []), 
    % (Hops = 532 -> (output_config(M, Config, Mode, Hops, Inputs, copmlex),nl); true), 
    % find_trans(M, Trans), length(Trans, L), L < States * Symbols, 
    next_config(States, Symbols, Dirs, M, Config, Mode, Hops, Inputs, NewM, NewConfig, NewHops, NewInputs, _Used), 
    % format("% Machine is ", []), write(NewM), nl,
    % (Hops = 532 -> (output_config(NewM, NewConfig, Mode, NewHops, NewInputs, copmlexx),nl); true), 
    execute_search(States, Symbols, Dirs, NewM, NewConfig, Bound, Mode, NewHops, Termination, NewInputs, Result). 
% Need to find a way to stop finding alternative complex transitions...

execute2d(M, Config, Bound, Mode, Type, Hops, Termination, Inputs, Result) :-
    % format("Halt?~n", []), 
    halt_execution2d(M, Config, Bound, Mode, Type, Hops, Termination, Inputs, Result), !. 
execute2d(M, Config, Bound, Mode, Type, Hops, Termination, Inputs, Result) :-
    % format("About to config~n", []), ttyflush, 
    % write(Inputs), nl, write(Config), display_config(Config), nl, 
    next_config2d(M, Config, Mode, Type, Hops, Inputs, NewM, NewConfig, NewHops, NewInputs, Used), !, 
    output_status(M, NewConfig, Mode, NewHops, NewInputs, NewerInputs, Used), !, 
    % display(NewInputs), nl, 
    execute2d(NewM, NewConfig, Bound, Mode, Type, NewHops, Termination, NewerInputs, Result). 

halt_execution(_,_,_, M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
    % format("Halt 1~n", []), 
    Config = config(_Left, State, _Item, _Dir, _Right),
    halt_state(State), !, 
    % format("% Halted in halting state~k~n", [State]), !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, halts).
    
halt_execution(_,_,_, M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
    % format("Halt 2~n", []), 
    Config = config(_Left, State, _Item, _Dir, _Right),
    looping_state(State),  !, 
    % format("% Halted in looping state~k~n", [State]), !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, loops(cycle)).

halt_execution(_,_,_, M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
    % format("Halt 5~n", []), ttyflush,
    \+ member(Mode, [search]), 
    no_transition(M, Config, Mode), !,  
    % format("% Halted with no transition~n", []), !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, abort(Hops)).

% This is irrelevant due to the way that new_transition is defined, which checks if there is only one slot left, and if so adds the halt transition, and then the machine halts on the next step due to Case 1 or the next case, which will catch the ones when new_transition adds the halt transition as there is only one slot left.
halt_execution(States, Symbols, _Dirs, M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
     % format("Halt 6a~n", []),  ttyflush,
     member(Mode, [search]), 
     % format("Trying halt transition ... ~n", []), 
     halt_transition(States, Symbols, M, Config, NewM), !, 
     % format("Halt added~n", []), 
     % format("Machine found is ", []), write(NewM), nl, !, 
     Result = result(NewM, Config, Bound, Mode, Hops, Termination, Inputs, going(Hops)).

halt_execution(States, Symbols, _Dirs, M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
    % format("Halt 6b~n", []),  ttyflush,
    member(Mode, [search]), find_trans(M, Trans), length(Trans, L), L is States * Symbols, !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, going(Hops)).

halt_execution(_,_,_, M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
    % format("Halt 3~n", []), 
    integer(Hops), Hops >= Bound, !, 
    % format("% Bound of ~d exceeded~n", [Bound]), !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, going(Hops)).

halt_execution(_,_,_, M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
    % format("Halt 4~n", []), 
    member(maxsteps(Max), Inputs), member(steps(Steps), Inputs), Steps >= Max, !, 
    % format("% Bound of ~d exceeded~n", [Bound]), !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, going(Hops)).

halt_execution(_,_,_, M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
    % format("Halt 7~n", []),  ttyflush,
    member(loop, Termination),
    looping(Config, Inputs), !, 
    % format("% Repeated configuration~n", []), !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, loops(cycle)).

halt_execution(_,_,_, M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
    % format("Halt 8~n", []),  ttyflush,
    member(blank, Termination), Hops > 0, 
    blank_tape(Config), !, 
    % format("% Blank tape found~n", []), !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, blank).

halt_execution(_,_,_, M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
    % format("Halt 9~n", []),  ttyflush,
    member(escape, Termination),
    road_runner(M, Config), !, 
    % format("% Road runner found~n", []), !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, loops(road_runner)).

halt_execution(_,_,_, M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
    % format("Halt 10~n", []),  ttyflush,
    member(targets(Tlist), Termination),
    member(Target, Tlist), 
    % format("Checking targets~n", []), 
    reached(Config, Mode, Target), !, 
    % format("% Termination target ~k reached~n", [Target]), !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, target(Target)).

% This case needs looking at, particularly for history access. Avoid induction option for now ... 
halt_execution(_,_,_, M, Config, Bound, Mode, Hops, Termination, Inputs, Result) :-
     member(induction, Inputs), 
     Config = config(Left, State, Item, Dir, Right), 
     Item = grp(_I, _Number), 
     member(history(History), Inputs),

     set_type(Inputs, Type), 
     history_index(Type, Config, Index), 

     % (Hops = 393 -> format("% Progression 0~n", []); true), 

     lookup_history(Type, State, Dir, Index, s(Hops1, Config1, _, _), History), less_hops(Hops1, Hops), % Hops1 < Hops, %% history lookup
     Config1 = config(Left1, State, Item1, Dir, Right1), 
     same_shape(config(Left1, State, Item1, Dir, Right1), config(Left, State, Item, Dir, Right)),

     % (Hops = 393 -> format("% Progression 1~n", []); true), 
     progressive(config(Left1, State, Item1, Dir, Right1), config(Left, State, Item, Dir, Right)),
     % (Hops = 393 -> format("% Progressive ~d to ~d~n", [Hops1, Hops]); true), 
     % format("Same Shape (1) ~d to ~d~n", [Hops1, Hops]), 

     lookup_history(Type, State, Dir, Index, s(Hops2, Config2, _, _), History), less_hops(Hops2, Hops1), % Hops2 < Hops1, %% history lookup
     Config2 = config(Left2, State, Item2, Dir, Right2), 
     same_shape(config(Left2, State, Item2, Dir, Right2), config(Left1, State, Item1, Dir, Right1)),

     % format("Same Shape (2) ~d to ~d~n", [Hops2, Hops1]), 
     % format("Same (second) shape as ~d~n", [Hops2]), 
     % progression(config(Left2, State, Item2, Dir, Right2), config(Left1, State, Item1, Dir, Right1), LDiffs2, ItemDiff2, RDiffs2),
     progressive(config(Left2, State, Item2, Dir, Right2), config(Left1, State, Item1, Dir, Right1)),
     % (Hops = 393 -> format("% Progressive (second) ~d to ~d~n", [Hops2, Hops1]); true), 

     lookup_history(Type, State, Dir, Index, s(Hops3, Config3, _, _), History), less_hops(Hops3, Hops2), % Hops3 < Hops2, %% history lookup
     Config3 = config(Left3, State, Item3, Dir, Right3), 

     same_shape(config(Left3, State, Item3, Dir, Right3), config(Left2, State, Item2, Dir, Right2)),

     progressive(config(Left3, State, Item3, Dir, Right3), config(Left2, State, Item2, Dir, Right2)),

     % (Hops = 393 -> format("% Checking for real progression at ~d ~d ~d ~d~n", [Hops3, Hops2, Hops1, Hops]); true), 
     % write(Config3), write(Config2), write(Config1), write(Config), nl, 
     % (Hops = 393 -> (write(Config3), write(Config2), write(Config1), writeln(Config));true), 
     real_progression(Left3, Left2, Left1, Left, LDiffs), % (Hops = 393 -> format("% Left real~n",[]);true), 
     real_progression(Right3, Right2, Right1, Right, RDiffs), % (Hops = 393 -> (format("% Right real~n",[]),writeln(RDiffs)); true), 
     real_progression([Item3], [Item2], [Item1], [Item], [ItemDiff]), % (Hops = 393 -> (format("% Item real ItemDiff is ",[]),  writeln(ItemDiff)); true), 

     % progression(Left3, Left2, Left1, Left, LDiffs),
     % progression(Right3, Right2, Right1, Right, RDiffs), 
     % format("Checking progression (3) with ", []), write([Item3]), format(" to ", []), write([Item2]), format(" to ", []), write([Item1]), format(" to ", []), write([Item]), nl), 
     % progression([Item3], [Item2], [Item1], [Item], [ItemDiff]), 

     % format("% Progression with ", []), write(LDiffs), write(ItemDiff), write(RDiffs), nl, 
     % format("% Progression!! ~d to ~d to ~d to ~d ~n", [Hops3, Hops2, Hops1, Hops]), 

     % verifier(Config, diffs(LDiffs1, ItemDiff1, RDiffs1), InitConfig, FinalConfig),!, 
     variablise(Config, LDiffs, ItemDiff, RDiffs, InitConfig, FinalConfig),!, 
     % format("% Verifier is ", []), write(InitConfig), format(" to ", []), write(FinalConfig), format("Hops: ~d to ~d to ~d to ~d~n", [Hops3, Hops2, Hops1, Hops]), 
     
     % Bound = 100, %% Sheer guess. Need to calculate this better ... 
     % format("Emulating ...~n", []), 
     % emulate_general(M, InitConfig, Bound, flex, [trace],[targets([FinalConfig])], Hops, Status, Outputs), %% Do we need the otter here? Presumably!
     % Status == target(_), 
     % format("Verified!~n", []), 

     Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, loops(induction(Config,diffs(LDiffs,ItemDiff,RDiffs), hops(Hops3,Hops2,Hops1,Hops)))). 

% config2d(State, Index, Map, Symbol, Direction),
halt_execution2d(M, Config, Bound, Mode, _Type, Hops, Termination, Inputs, Result) :-
    % format("Halt 1~n", []), 
    (Config = config2d(State, _Index, _Map, _Symbol, _Direction) ; Config = config2d(State, _Index, _Map, _Symbol)),  
    halt_state(State), !, 
    % format("% Halted in halting state~k~n", [State]), !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, halts).

halt_execution2d(M, Config, Bound, Mode, _Type, Hops, Termination, Inputs, Result) :-
    % format("Halt 2~n", []),
    (Config = config2d(State, _Index, _Map, _Symbol, _Direction) ; Config = config2d(State, _Index, _Map, _Symbol)),  
    looping_state(State),  !, 
    % format("% Halted in looping state~k~n", [State]), !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, loops(cycle)).

halt_execution2d(M, Config, Bound, Mode, _Type, Hops, Termination, Inputs, Result) :-
    % format("Halt 5~n", []), ttyflush,
    \+ member(Mode, [search]), 
    no_transition2d(M, Config, Mode), !,  
    % format("% Halted with no transition~n", []), !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, abort(Hops)).

halt_execution2d(M, Config, Bound, Mode, _Type, Hops, Termination, Inputs, Result) :-
    % format("Halt 3~n", []), 
    integer(Hops), Hops >= Bound, !, 
    % format("% Bound of ~d exceeded~n", [Bound]), !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, going(Hops)).

halt_execution2d(M, Config, Bound, Mode, _Type, Hops, Termination, Inputs, Result) :-
    % format("Halt 4~n", []), 
    member(maxsteps(Max), Inputs), member(steps(Steps), Inputs), Steps >= Max, !, 
    % format("% Bound of ~d exceeded~n", [Bound]), !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, going(Hops)).

halt_execution2d(M, Config, Bound, Mode, _Type, Hops, Termination, Inputs, Result) :-
    % format("Halt 10~n", []),  ttyflush,
    member(targets(Tlist), Termination),
    member(Target, Tlist), 
    % format("Checking targets~n", []), 
    reached2d(Config, Mode, Target), !, 
    % format("% Termination target ~k reached~n", [Target]), !, 
    Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, target(Target)).

no_transition(M, Config, Mode) :-
    Mode = naive,
    Config = config(_Left, State, Item, _Dir, _Right), 
    \+ simple_transition(M, State, Item, _NewState, _OutItem, _OutDir, _Steps),
    true. 
no_transition(M, Config, Mode) :-
    member(Mode, [macro(_K),adapt,flex,search]), 
    Config = config(_Left, State, Item, Dir, _Right), 
    first_item(Item, Dir, I), % format("First Item done~n", []), 
    \+ simple_transition(M, State, I, _NewState, _OutItem, _OutDir, _Steps), % format("No Simple Transition~n", []), 
    true. 

no_transition2d(M, Config, _Mode) :-
    (Config = config2d(State, _Index, _Map, Symbol, _Direction) ; Config = config2d(State, _Index, _Map, Symbol)),  
    % format("M is ", []), write(M), format(" Config2d is ", []), writeln(Config), 
    \+ simple_transition(M, State, Symbol, _NewState, _OutItem, _OutDir, _Steps),
    true. 

zero_dextrous(States, M) :- 
    states_list(States, SList), zero_dextrous1(SList, M).

zero_dextrous1([], _).
zero_dextrous1([State|Rest], M) :-
    member(t(State,0,_,r,_), M), !, zero_dextrous1(Rest, M). 

first_item(I, _, I) :- is_input(I). 
first_item([I|_], l, I) :- is_input(I).
first_item(Item, r, I) :- reverse(Item, RevItem), RevItem = [I|_], is_input(I). 
first_item(grp(_Item,0), _, 0). 
first_item(grp([],_Num), _, 0).
first_item(grp(Item,Num), l, I) :- integer(Num), Num > 0, Item \= [], Item = [I|_].
first_item(grp(Item,Num), r, I) :- integer(Num), Num > 0, Item \= [], reverse(Item, RevItem), RevItem = [I|_].
first_item(grp(Item,Num), l, I) :- variable(Num), Item \= [], Item = [I|_].
first_item(grp(Item,Num), r, I) :- variable(Num), Item \= [], reverse(Item, RevItem), RevItem = [I|_].

% Only succeeds if it is appropriate to add the halt transition at this point. This includes the case where there is only one transition to add. 
halt_transition(States, Symbols, M, _Config, NewMachine) :-
    % format("aDDEr~N", []), 
    M = machine(List1, List2, List3), % Config = config(_Left, State, Item, _Dir, _Right), % format("Adding halt .. ~n", []), 
    length(List1,L), % number_of_states(List1, NumStates), format("Number of states is ~d~n", [NumStates]), 
    L is (States * Symbols) - 1, !, 

    % number_of_states_used(M, UsedStates), UsedStates == States, 
    % number_of_symbols_used(M, UsedSymbols), UsedSymbols == Symbols, % So the machine is 'full'
    % Full test is used in generating new transition. Only need exhaustiveness test here. 
    !, 
    states_list(States, StatesList),
    symbols_list1(Symbols, SymbolsList),
    once( missing(StatesList, SymbolsList, List1, NewState, NewSymbol) ), 
    halt_trans(t(NewState, NewSymbol, NewOut, NewDir, NewNewState)),
    append(List1, [t(NewState, NewSymbol, NewOut, NewDir, NewNewState)], NewList), % Makes it hard to have zero_dextrous test here - don't want further execution ... 
    NewMachine = machine(NewList, List2, List3), !, 
    true. 

missing(StatesList, SymbolsList, Transitions, State, Symbol) :-
    member(State, StatesList),
    member(Symbol, SymbolsList),
    \+ member(t(State, Symbol, _, _, _), Transitions),
    true. 

looping(Config, Inputs) :-
    member(history(History), Inputs),
    set_type(Inputs, Type), 
    history_index(Type, Config, Index), 
    Config = config(_, State, _, Dir, _), 
    lookup_history(Type, State, Dir, Index, s(_Hops, Config, _, _), History). %% history lookup 

blank_tape(config(Left, _State, Item, _Dir, Right)) :-
    is_blank(Item),
    all_blank(Left), all_blank(Right).

is_blank(I) :- blank_symbol(I).
is_blank(grp(I,_)) :- all_blank(I).

all_blank([]).
all_blank([I|Rest]) :- is_blank(I), all_blank(Rest). 

reached(Config, Mode, Target) :-
     Mode = naive,
     Config = Target. 
reached(Config, Mode, Target) :-
     Mode = macro(_K), 
     flatten(Config, FlatConfig),
     flatten(Target, FlatTarget), 
     FlatConfig == FlatTarget. 
reached(Config, Mode, Target) :-
     member(Mode, [adapt,flex,search]), 
     zero_instance(Config, Zero1), 
     zero_instance(Target, Zero2), Zero1 == Zero2, 
     one_instance(Config, One1), 
     one_instance(Target, One2), One1 == One2, 
     true. 

%% Need to check this when doing targets ... 
flatten(config(Left, State, Item, Dir, Right), config(NewLeft, State, NewItem, NewDir, NewRight)) :-
     % format("Left~n", []), 
     flatten_tape(left, Left, NLeft), 
     % format("Left~n", []), 
     flatten_tape(right, Right, NRight), 
     % format("Item~n", []), 
     flatten_tape(right, [Item], NItem), 
     % format("Balance", []), write(NLeft),  write(State), write(NItem),  write(Dir), write(NRight),  nl, 
     balance_config(config(NLeft, State, NItem, Dir, NRight), config(NewLeft, State, NewItem, NewDir, NewRight)),
     % format("Balanced", []),
     true. 

flatten_tape(_, [], []).
flatten_tape(right, [grp(I,N)|Rest], NewResult) :-
    flatten_tape_grp(I, N, Flat), flatten_tape(right, Rest, Result), append(Flat, Result, NewResult). 
flatten_tape(left, [grp(I,N)|Rest], NewResult) :-
    flatten_tape_grp(I, N, Flat), flatten_tape(left, Rest, Result), reverse(Flat, RevFlat), append(RevFlat, Result, NewResult). 
flatten_tape(Direction, [I|Rest], [I|Result]) :- is_input(I), flatten_tape(Direction, Rest, Result).
    
flatten_tape_grp(_I, 0, []).
flatten_tape_grp(I, 1, I).
flatten_tape_grp(I, N, Result) :- N > 1, N1 is N-1, flatten_tape_grp(I, N1, Rest), append(I, Rest, Result). 

balance_config(config(Left, State, Item, Dir, Right), config(NewLeft, State, NewItem, Dir, NewRight)) :-
    Dir = l, 
    append([I], Rest, Item), length([I], 1), 
    NewLeft = Left,
    NewItem = I,
    append(Rest, Right, NewRight), 
    true. 

balance_config(config(Left, State, Item, Dir, Right), config(NewLeft, State, NewItem, Dir, NewRight)) :-
    Dir = r, 
    append(Rest, [I], Item), length([I], 1), 
    append(Rest, Left, NewLeft), 
    NewItem = I,
    NewRight = Right, 
    true. 

zero_instance(config(Left, State, Item, Dir, Right), config(NewLeft, State, NewItem, Dir, NewRight)) :-
    zero_instance_tape(Left, NewLeft), 
    zero_instance_tape(Right, NewRight), 
    zero_instance_tape([Item], [NewItem]),
    true. 

one_instance(config(Left, State, Item, Dir, Right), config(NewLeft, State, NewItem, Dir, NewRight)) :-
   one_instance_tape(left, Left, NewLeft),  
   one_instance_tape(right, Right, NewRight),  
   one_instance_tape(right, [Item], [NewItem]).

zero_instance_tape([], []).
zero_instance_tape([I|Rest], [I|Result]) :- is_input(I), zero_instance_tape(Rest, Result). 
zero_instance_tape([grp(I,Num)|Rest], [grp(I,Num)|Result]) :- integer(Num), zero_instance_tape(Rest, Result). 
zero_instance_tape([grp(_I,Num)|Rest], Result) :- variable(Num), zero_instance_tape(Rest, Result). 

one_instance_tape(_, [], []).
one_instance_tape(Dir, [I|Rest], [I|Result]) :- is_input(I), one_instance_tape(Dir, Rest, Result). 
one_instance_tape(Dir, [grp(I,Num)|Rest], [grp(I,Num)|Result]) :- integer(Num), one_instance_tape(Dir, Rest, Result). 
one_instance_tape(right, [grp(I,Num)|Rest], NewResult) :- variable(Num), one_instance_tape(right, Rest, Result), append(I, Result, NewResult). 
one_instance_tape(left, [grp(I,Num)|Rest], NewResult) :- variable(Num), one_instance_tape(left, Rest, Result), reverse(I, RevI), append(RevI, Result, NewResult). 

road_runner(M, Config) :-
     M = machine(Translist, _, _),
     Config = config(Left, State, Item, _Dir, Right), 
     is_blank(Item), 
     road_runner1(Translist, Left, State, Right), 
     true.

road_runner1(Translist, _Left, State, Right) :-
     all_blank(Right),
     blank_cycle(Translist, State, r).
road_runner1(Translist, Left, State, _Right) :-
     all_blank(Left),
     blank_cycle(Translist, State, l).

blank_cycle(Translist, State, Dir) :-
     blank_symbol(Item),
     member(t(State, Item, _Out1, Dir, State), Translist),  % cycle length 1
     true. 
blank_cycle(Translist, State, Dir) :-
     blank_symbol(Item),
     member(t(State, Item, _Out1, Dir, NS), Translist), State \== NS, % cycle length 2
     member(t(NS, Item, _Out2, Dir, State), Translist),
     true. 
blank_cycle(Translist, State, Dir) :-
     blank_symbol(Item),
     member(t(State, Item, _Out1, Dir, NS), Translist), State \== NS, % cycle length 3
     member(t(NS, Item, _Out2, Dir, NS2), Translist), State \== NS2, NS \== NS2, 
     member(t(NS2, Item, _Out3, Dir, State), Translist),
     true. 
blank_cycle(Translist, State, Dir) :-
     blank_symbol(Item),
     member(t(State, Item, _Out1, Dir, NS), Translist), State \== NS, % cycle length 4
     member(t(NS, Item, _Out2, Dir, NS2), Translist), State \== NS2, NS \== NS2, 
     member(t(NS2, Item, _Out3, Dir, NS3), Translist), State \== NS3, NS \== NS3, NS2 \== NS3, 
     member(t(NS3, Item, _Out4, Dir, State), Translist), 
     true. 
blank_cycle(Translist, State, Dir) :-
     blank_symbol(Item),
     member(t(State, Item, _Out1, Dir, NS), Translist), State \== NS, % cycle length 5
     member(t(NS, Item, _Out2, Dir, NS2), Translist), State \== NS2, NS \== NS2, 
     member(t(NS2, Item, _Out3, Dir, NS3), Translist), State \== NS3, NS \== NS3, NS2 \== NS3, 
     member(t(NS3, Item, _Out4, Dir, NS4), Translist), State \== NS4, NS \== NS4, NS2 \== NS4, NS3 \== NS4, 
     member(t(NS4, Item, _Out5, Dir, State), Translist), 
     true. 
%% Should have cycle of any length, and certainly at least 6. 

%      Result = result(M, Config, Bound, Mode, Hops, Termination, Inputs, loops(induction(Config,diffs(LDiffs,ItemDiff,RDiffs), hops(Hops3,Hops2,Hops1,Hops)))). 

% These need checking ... 
verifier(Config, diffs(LDiffs, ItemDiff, RDiffs), InitConfig, FinalConfig) :-
    Config = config(Left, State, Item, Dir, Right), 
    generalise(Left, LDiffs, InitLeft, FinalLeft), !, 
    generalise([Item], [ItemDiff], [InitItem], [FinalItem]), !, 
    generalise(Right, RDiffs, InitRight, FinalRight), !, 
    InitConfig = config(InitLeft, State, InitItem, Dir, InitRight), 
    FinalConfig = config(FinalLeft, State, FinalItem, Dir, FinalRight), 

    % Work out a way to check that InitConfig leads to FinalConfig ... 
    true. 

generalise([], _, [], []).
generalise([grp(I,Num)|Rest], [m(K,L)|RestDiffs], [grp(I,Num)|Initial], [grp(I,Num)|Final]) :-
      K =< 1, L == 0, 
      generalise(Rest, RestDiffs, Initial, Final). 
generalise([grp(I,_Num)|Rest], [m(K,L)|RestDiffs], [grp(I,Var1)|Initial], [grp(KI,Var1)|Final]) :-
      \+ (K =< 1, L == 0), L == 0,
      items(I, K, [], KI), 
      new_variable(0,10,0,10,Var1), %% This needs updating
      generalise(Rest, RestDiffs, Initial, Final). 

generalise([grp(I,_Num)|Rest], [m(K,L)|RestDiffs], [grp(I,Var1)|Initial], NewFinal) :-
      \+ (K =< 1, L == 0), L > 0, 
      items(I, K, [], KI), % N becomes K*N + L ... 
      new_variable(0,10,0,10,Var1), %% This needs updating
      append([grp(KI,Var1)], [grp(I,L)], Temp), 
      generalise(Rest, RestDiffs, Initial, Final),
      append(Temp, Final, NewFinal). 

generalise([grp(I,_Num)|Rest], [m(K,L)|RestDiffs], NewInitial, NewFinal) :-
      \+ (K =< 1, L == 0), L < 0, % change variable
      items(I, K, [], KI), 
      M is ((0 - L) // K) + 1, 
      J is K*M + L, % J can't be zero ... 
      new_variable(0,10,0,10,Var1), %% This needs updating
      append([grp(I,Var1)], [grp(I,M)], TempInitial), 
      append([grp(KI,Var1)], [grp(I,J)], TempFinal), 

      generalise(Rest, RestDiffs, Initial, Final),
      append(TempInitial, Initial, NewInitial),
      append(TempFinal, Final, NewFinal),
      true. 
      
% When L < 0, we need to change variables, so that instead of N becoming 2*N - 7, we use N+4 becomes 2*N + 1. 
% Hence when L < 0, we use N + M -> K*N + J, where M = 1 + (abs(L) // K), J = K*M + L. 

next_config(_States, _Symbols, _Dirs, M, Config, Mode, Hops, Inputs, NewM, NewConfig, NewHops, NewInputs, simple) :-
     Mode = naive,
     Config = config(Left, State, Item, _Dir, Right), 
     % format("Outputting status~n", []), 
     
     % format("Finding transition~n", []), 
     simple_transition(M, State, Item, NewState, OutItem, OutDir, Steps),!, 
     % format("Updating tape~n", []), 
     updatetape(Mode, Left, OutItem, Right, OutDir, NewLeft, NewItem, NewRight, _Moves),
     NewHops is Hops + Steps,
     NewConfig = config(NewLeft, NewState, NewItem, l, NewRight),
     NewM = M,
     % format("Updating pos~n", []), display(Inputs), nl, 
     % display(Inputs1), nl, 
     % format("Updating inputs~n", []), 
     updateinputs(Config, Mode, Hops, OutDir, 1, naive, Inputs, NewConfig, NewHops, NewInputs), 
     % format("Updated inputs~n", []), 
     true. 

next_config(_States, _Symbols, _Dirs, M, Config, Mode, Hops, Inputs, NewM, NewConfig, NewHops, NewInputs, ocelot) :-
     member(ocelot, Inputs), 
     Mode = macro(_K),
     Config = config(_Left, _State, _Item, Dir, _Right), 

     M = machine(_, _, Otters), member(Ocelot, Otters), Ocelot = oo(InitConfig, FinalConfig, InitDiffs, HopsFormula), 
     
     % Work out if Config matches InitConfig
     % InitConfig = config(ILeft, IState, IItem, IDir, IRight), State = IState, Dir = IDir, 

     matches(InitConfig, InitDiffs, Config, _CoreLeft, ExtraLeft, _CoreRight, ExtraRight, Count, InitialVars), 
     % Constraints are expressed in terms of the variables in the initial configuration ... 
     % Then apply Count to get the instance of FinalConfig
     % format("Matched~n", []), 
     apply_count(Count, FinalConfig, InitialVars, NConfig), % display_config(NConfig), nl, 
     % format("Final configuration found~n", []), 
     add_context(NConfig, ExtraLeft, ExtraRight, NewConfig1), % display_config(NewConfig), nl, 
     % format("Context added~n", []), 
     % format("Reconfigurating ... ", []), write(NewConfig1), nl, 
     reconfigurate(Mode, NewConfig1, NewConfig),
     % format("Reconfigurated~n", []),  

     % Then use Count and HopsFormula to calculate Leaps. 
     calculate_leaps(Count, InitialVars, HopsFormula, Leaps), Leaps > 0, % Do we need this check?

     % format("Leaps found~n", []), 

     % Generalise ... 
     update_hops(Leaps, Hops, NewHops), 

     ( (member(otrace, Inputs) ) -> 
	 ( format("Ocelot Applied: Hops: ~d Count: ~d Leaps: ~d NewHops: ~d ", [Hops, Count, Leaps, NewHops]), 
	   display_config(Config), format(" ++> ", []), 
	   display_config(NewConfig), nl
          ) ; true ) , 

     OutDir = Dir, % Could get this from NewConfig ... 
     NewM = M, % no change to machine for this step

     update_ocelots(Leaps, Inputs, NInputs), 
     updateinputs(Config, Mode, Hops, OutDir, Leaps, ocelot, NInputs, NewConfig, NewHops, NewInputs), !, 
     true. 

next_config(_States, _Symbols, _Dirs, M, Config, Mode, Hops, Inputs, NewM, NewConfig1, NewHops, NewInputs, predict) :-
     % Case for ocelot testing. Do the same as the ocelot would, but don't jump to the predicted configuration, just make a prediction. 
     member(predict, Inputs), \+ member(prediction(Hops, _), Inputs), % Fail if prediction for this Hops has already been made
     Mode = macro(_K),
     Config = config(_Left, _State, _Item, _Dir, _Right), 

     M = machine(_, _, Otters), member(Ocelot, Otters), Ocelot = oo(InitConfig, FinalConfig, InitDiffs, HopsFormula), 
     
     % Work out if Config matches InitConfig
     % InitConfig = config(ILeft, IState, IItem, IDir, IRight), State = IState, Dir = IDir, 

     matches(InitConfig, InitDiffs, Config, _CoreLeft, ExtraLeft, _CoreRight, ExtraRight, Count, InitialVars), 
     % Constraints are expressed in terms of the variables in the initial configuration ... 
     % Then apply Count to get the instance of FinalConfig
     % format("Matched~n", []), 
     apply_count(Count, FinalConfig, InitialVars, NConfig), % display_config(NConfig), nl, 
     % format("Final configuration found~n", []), 
     add_context(NConfig, ExtraLeft, ExtraRight, NewConfig1), % display_config(NewConfig), nl, 
     % format("Context added~n", []), 
     % format("Reconfigurating ... ", []), write(NewConfig1), nl, 
     reconfigurate(Mode, NewConfig1, NewConfig),
     % format("Reconfigurated~n", []), 
     
     % Then use Count and HopsFormula to calculate Leaps. 
     % Get this from HopsFormula, but how exactly? Need to allow for a variable number of variables (arf!).

     calculate_leaps(Count, InitialVars, HopsFormula, Leaps), Leaps > 0, % Do we need this check?
     % NHops is Hops + Leaps,

     % Generalise ... 
     update_hops(Leaps, Hops, NHops), 

     append([prediction(NHops, NewConfig)], Inputs, NewInputs), 
     NewM = M, % no change to machine for this step
     NewConfig1 = Config, 
     NewHops = Hops, 
     true. 

next_config(_States, _Symbols, _Dirs, M, Config, Mode, Hops, Inputs, NewM, NewConfig, NewHops, NewInputs, otter) :-
     (member(otter, Inputs); (\+ member(otter, Inputs), member(ocelot, Inputs))), 
     % Mode = macro(_K),
     member(Mode, [macro(_),flex]), 
     Config = config(Left, State, Item, Dir, Right), 

     % Observant Otter, ie calculated, not found from stored pattern

     member(history(History), Inputs),
     % format("% Otter case~n", []), 
     % member(s(Hops1, config(Left1, State, Item1, Dir, Right1), _), History), Hops1 < Hops, %% history lookup
     % (member(trie(K), Inputs) -> Type = trie(K); Type = list), 
     set_type(Inputs, Type), 
     history_index(Type, Config, Index), 
     % ( Hops = 47165169 -> (write(Config),nl);true), 
     % ( Hops = 239 -> (tell('239-hist.txt'),display_history(0,History),write(History),nl,told);true), 
     % format("Looking up ~d ~k ~k ", [Hops, State, Dir]), write(Index), nl,
     % lookup_history(Type, State, Dir, Index, s(Hops1, config(Left1, State, Item1, Dir, Right1), _), History), Hops1 < Hops, %% history lookup
     lookup_history(Type, State, Dir, Index, s(Hops1, Config1, _, _), History), less_hops(Hops1, Hops), % Hops1 < Hops, %% history lookup
     % format("Found (1) ~d: ", [Hops1]), write(Config1), nl,  

     Config1 = config(Left1, State, Item1, Dir, Right1), 
     same_shape(config(Left1, State, Item1, Dir, Right1), config(Left, State, Item, Dir, Right)),
     % (Hops = 47165169 -> (format("Found (1) ~d: ", [Hops1]), write(Config1), nl); true), 
     % format("Same shape at ~d and ~d: ", [Hops1, Hops]), write(Config1), format(" and ", []), writeln(Config), 
     regression(config(Left1, State, Item1, Dir, Right1), config(Left, State, Item, Dir, Right), LDiffs1, ItemDiff1, RDiffs1),  
     % format("Regression~n", []), 
     % member(s(Hops2,config(Left2, State, Item2, Dir, Right2), _), History), Hops2 < Hops1, %% history lookup
%      lookup_history(Type, State, Dir, Index, s(Hops2,config(Left2, State, Item2, Dir, Right2), _), History), Hops2 < Hops1, %% history lookup
     lookup_history(Type, State, Dir, Index, s(Hops2,Config2, _, _), History), less_hops(Hops2, Hops1), % Hops2 < Hops1, %% history lookup
     % (Hops = 239 -> (format("Found (2) ~d: ", [Hops2]), write(Config2), nl); true), 
     Config2 = config(Left2, State, Item2, Dir, Right2), 
     same_shape(config(Left2, State, Item2, Dir, Right2), config(Left1, State, Item1, Dir, Right1)),
     % (Hops = 47165169 -> (format("Found (1) ~d: ", [Hops1]), write(Config1), nl, format("Found (2) ~d: ", [Hops2]), write(Config2), nl); true), 
     % format("Same shape at ~d, ~d, ~d~n", [Hops2, Hops1, Hops]), 
     regression(config(Left2, State, Item2, Dir, Right2), config(Left1, State, Item1, Dir, Right1), LDiffs2, ItemDiff2, RDiffs2), 
     % (Hops = 47165169 -> format("% Regression 2 ... ~n", []); true), 
     LDiffs1 == LDiffs2, ItemDiff1 == ItemDiff2, RDiffs1 == RDiffs2, 
     % format("Same Diffs ... ~n", []), 
     % (Hops = 47165169 -> format("% Same Diffs ... ~n", []); true), 
    % find minimum regressor
     regression_counters(Left, LDiffs1, [Item|Right], [ItemDiff1|RDiffs1], [], Regs), 
     % (Hops = 47165169 -> format("% Counters ... ~n", []); true), 
     length(Regs, N), N > 0, % write(Regs), nl, 

     ( member(reg(1,_), Regs) -> fail; true), % Ignore regression if one regressor is trivial % machines 17, 77 have many occurrences of this

     % format("Diffs are ",[]), write(LDiffs1), write(ItemDiff1), write(RDiffs1), nl, 
     % format("Regressors are ", []), write(Regs), nl, 

	 %%  display_config(config(Left2, State, Item2, Dir, Right2)), format(" + ", []), 
	 %%  display_config(config(Left1, State, Item1, Dir, Right1)), format(" + ", []), 
	 %%  display_config(config(Left, State, Item, Dir, Right)), nl,

     % (Hops = 47165169 -> format("% Regressions ... ~n", []); true), 

     ( (N > 1) -> (format("% Multiple regressors found: ", []),write(Regs),( member(single, Inputs) -> (format(" failing...~n",[]),fail); nl)) ; true), 

     minimum_regressor(Regs, MinNum, MinL, MinCount),  %%%% Need to make this work for variables for ocelot ..   %% For variables, we will assume there is only one ... 

     % (Hops = 47165169 -> format("Minimum regressor ~d ~d ~d ~d ~d ... ~n", [Hops, Hops1, Hops2, MinNum, MinL]); true), 
    
     setleaps(Hops, Hops1, Hops2, MinNum, MinL, Leaps), Leaps > 0, % Variables??

     % format("% about to verify ~n", []), 
     (member(verify, Inputs) -> (verify_otter(M, Mode, Config, LDiffs1, ItemDiff1, RDiffs1, OtterPattern) -> format("Otter verified~n", []); (format("Unverified otter~n", []), flush_output, fail));true), 

     % (Hops = 47165169 -> format("Set leaps ... ~n", []); true), 

     % !, % commit to this case --- Not yet! Need to verify otter first 

     ( (member(otrace, Inputs) ) -> 
	 ( format("Otter Observed: ~d ~d ~d Diff1 is ~d Diff2 is ~d Num is ~d L is ~d Count is ~d Leaps is ~d ", [Hops2, Hops1, Hops, Hops1 - Hops2, Hops - Hops1, MinNum, MinL, MinCount, Leaps]), % Hops2 < Hops1 < Hops
	   display_config(config(Left2, State, Item2, Dir, Right2)), format(" + ", []), 
	   display_config(config(Left1, State, Item1, Dir, Right1)), format(" + ", []), 
	   display_config(config(Left, State, Item, Dir, Right)), nl 
          ) ; true ) , 
  
     % member(pos(Pos), Inputs), % format("Pos is ~d~n", [Pos]), 

     % find final configuration by changing Config by Count appropriately

     % format("Calling final_config with ~d ~d ", [Num,L]), write(config(Left, State, Item, Dir, Right)), write(LDiffs1), write(ItemDiff1), write(RDiffs1), nl, 

     final_config(Mode, MinNum, MinL, config(Left, State, Item, Dir, Right), LDiffs1, ItemDiff1, RDiffs1, NewConfigTemp), % Variables??

     ( member(Mode, [flex]) -> new_compress_config(NewConfigTemp, NewConfig) ; (NewConfig = NewConfigTemp) ), 

     % Generalise ... need to think about this case, as we can't use update_otter_hops directly. 
     % Should be simply a matter of adding in Leaps as a list of variables rather than a number. 
     % May need to integrate this with setleaps ...

     % update_hops(Leaps, Hops, NewHops), % NewHops is Hops + Leaps, % Variables??
     add_hops(Leaps, Hops, NewHops), % NewHops is Hops + Leaps, % Variables??

     (member(otrace, Inputs) -> (format("Final otter is ~d:", [NewHops]), display_config(NewConfig), write(NewConfig), nl, ttyflush); true), 
     % append([s(Hops,Config,Pos)], History, History_Now), 

     % display_history(0, History), 

     %% Verify otter here????
     % format("Verifying...~n", []), 
     % (member(verify, Inputs) -> (verify_otter(M, Mode, Config, LDiffs1, ItemDiff1, RDiffs1, OtterPattern) -> format("Otter verified~n", []); (format("Unverified otter~n", []),fail));true), 
     !, % Now can commit to this case. 

     (member(ocelot, Inputs) -> update_machine(M, OtterPattern, NewM); NewM = M), 
     % format("Machine updated~n", []), 
     NewConfig = config(_,_,_,OutDir,_), 

     (member(predict, Inputs) -> check_predictions(Hops, Inputs, NewConfig, Inputs1); Inputs1 = Inputs),
     % format("prediction done~n", []), 

     Nested is 0, %% Work out how to do this better ... how do we tell whether this otter is nested or not? 
     update_otters(Leaps, 0, Nested, Inputs1, NInputs), 

     updateinputs(Config, Mode, Hops, OutDir, Leaps, otter, NInputs, NewConfig, NewHops, NewInputs), !, 
     % format("Inputs updated~n", []), 
     true. 

next_config(_States, _Symbols, _Dirs, M, Config, Mode, Hops, Inputs, NewM, NewConfig, NewHops, NewInputs, complex) :-
     Mode = macro(_K),
     member(Mode, [macro(_)]), 
     Config = config(_Left, State, Item, Dir, _Right), 

     Item = grp(I, Number), % format("Complex transition~n", []), % ttyflush, format("Right is ", []), write(Right), nl, format("show is ", []), show_me(Right), nl,  
     % format("Trying Transition ....~n", []), display(Config), format(" or ", []), display_config(Config), nl,  display(M),nl, ttyflush, 
     % (Hops == 4278 -> (format("Calling complex_transition with ~k ", [State]), display(I), format(" ~k ", [Dir]), nl); true), 
     % (Hops == 10241 -> (format("Calling complex_transition with ~k at ~d ", [State, Hops]), display(I), format(" ~k ", [Dir]), display_config(Config), nl); true),
     complex_transition(M, State, I, Dir, NewM, NewState, OutItem, OutDir, Steps),!, 
     % format("Complex transition found at ~d~n", [Hops]), ttyflush, 
     % format("Transition found~n", []), write(Config), nl, display_config(Config), write(trans(State, I, Dir, NewState, OutItem, OutDir, Steps)), nl,

     updatetapemacro(Config, Mode, trans(State, I, Dir, NewState, OutItem, OutDir, Steps), NLeft, NewItem, NewDir, NRight, Leaps, Moves),
     % format("Updated to ", []), write(config(NLeft, NewState, NewItem1, NewDir1, NRight)), nl, 
     check_blank(NLeft, NewLeft),
     check_blank(NRight, NewRight),

     % format("Calling compress with ", []), write(config(NewLeft1, NewState, NewItem1, NewDir1, NewRight1)), nl,
     % new_compress_config(config(NewLeft1, NewState, NewItem1, NewDir1, NewRight1), config(NewLeft, NewState, NewItem, NewDir, NewRight)), 
     % format("Compressed to ", []), write(config(NewLeft, NewState, NewItem, NewDir, NewRight)), nl,

     % format("Complex transition updated~n", []), ttyflush, 
     % NewHops is Hops + Leaps,
     update_hops(State, NewState, Dir, OutDir, Number, Leaps, Hops, NewHops),

     NewConfig = config(NewLeft, NewState, NewItem, NewDir, NewRight),
     updateinputs(Config, Mode, Hops, OutDir, Moves, complex, Inputs, NewConfig, NewHops, NewInputs), 
     true. 

%% No ocelot to start with ... 
% next_config(_States, _Symbols, _Dirs, M, Config, Mode, Hops, Inputs, NewM, NewConfig, NewHops, NewInputs, ocelot) :-
%     member(Mode, [flex,search]), 
%     member(ocelot, Inputs), 
%     Config = config(_Left, State, Item, Dir, _Right), 
%     Item = grp(I, _Number), 
%     % format("Trying Ocelot ....~n", []), ttyflush, % display(Config), display_config(Config), nl, display(M),nl, 
%     otter_transition(M, Hops, Config, Mode, NewConfig, OutDir, Leaps), !, 
%     % Ossified Ocelot, ie otter from pattern stored already
%     NewHops is Hops + Leaps,
%     format("~d: Otter Transition found:", [Hops]), display_config(Config),format(" to ~d:", [NewHops]), display_config(NewConfig), nl, 
%     updateinputs(Config, Mode, Hops, OutDir, Leaps, Inputs, NewConfig, NewHops, NewInputs), 
%     NewM = M, 
%     true. 

next_config(States, Symbols, Dirs, M, Config, Mode, Hops, Inputs, NewM, NewConfig, NewHops, NewInputs, extend) :-
     member(Mode, [search]), % format("% Searching~n", []), 
     Config = config(_Left, State, Item, Dir, _Right), 

     % (Hops = 532 -> (format("% Machine is ", []), write(M), write(State), write(Item), nl) ; true), 
     
     first_item(Item, Dir, I), 
     \+ simple_transition(M, State, I, _NewState, _OutItem, _OutDir, _Steps),
     % means we need to complete the machine for this state ... 
     % (Hops = 532 -> (format("% Searching with ", []), ttyflush, write(M), write(Config), nl); true), 

     % format("% Finding new transition ... ~n", []), 
     new_transition(States, Symbols, Dirs, M, Config, NewishM), 
     % format("% Found new transition ", []), writeln(NewishM), 
     % format("And searching 2~n", []), ttyflush, 
     % (Hops = 532 -> (format("% Newish Machine is ", []), write(NewishM), nl); true), 

     Item = grp(It,_),  
     complex_transition(NewishM, State, It, Dir, NewM, NewState, OutItem, OutDir, Steps), 

     % (Hops = 532 -> (format("% Found complex transition ~n", []) ); true), 

     % format("% New Machine is ", []), write(NewM), nl,
     % write(Config), nl, 
     % format("And searching 3~n", []), ttyflush, 
     % write(Config), 
     % write(trans(State, It, Dir, NewState, OutItem, OutDir, Steps)), 
     updatetapemacro(Config, Mode, trans(State, It, Dir, NewState, OutItem, OutDir, Steps), NLeft1, NItem, NewDir, NRight1, Leaps, _Moves),

     % (Hops = 532 -> (format("% Updated tape ~n", []) ); true), 

     % write(NItem), nl,
     % format(" And searching 4~n", []), ttyflush, 

     check_blank(NLeft1, NLeft),
     check_blank(NRight1, NRight),

     % (Hops = 532 -> (format("% Compressing with ", []), write(config(NLeft, NewState, NItem, NewDir, NRight)), nl); true), 

     ( member(optcom, Inputs) -> ( compress(config(NLeft, NewState, NItem, NewDir, NRight), config(NewLeft, NewState, NewItem, NewDir, NewRight)) ) ; 
	                         ( new_compress_config(config(NLeft, NewState, NItem, NewDir, NRight), config(NewLeft, NewState, NewItem, NewDir, NewRight)) ) ), 

     NewHops is Hops + Leaps,
     NewConfig = config(NewLeft, NewState, NewItem, NewDir, NewRight),
     % (Hops = 532 -> (format("% Updating inputs .... ~n", []) ); true), 

     % format("Inputs Updated~n", []),  ttyflush, 
     % format("~d: Extend Transition found:", [Hops]), display_config(Config),format(" to ~d:", [NewHops]), display_config(NewConfig), nl, 
     updateinputs(Config, Mode, Hops, OutDir, Leaps, extend, Inputs, NewConfig, NewHops, NewInputs), 

     % (Hops = 532 -> (format("% Updated inputs ~n", []) ); true), 

      true. 

% Check this case. No otter in search for now ... Need to update this for history changes. Make it as per macro case above. 
next_config(_States, _Symbols, _Dirs, M, Config, Mode, Hops, Inputs, NewM, NewConfig, NewHops, NewInputs, otter) :-
     % member(Mode, [flex, search]), 
     member(Mode, [search]), 
     member(otter, Inputs), 

     Config = config(Left, State, Item, Dir, Right), 
     Item = grp(_I, _Number), 
     member(history(History), Inputs),

     % ( Hops = 95547257425481 -> (format("Checking Otter~n", [])); true), 

     member(s(Hops1, config(Left1, State, Item1, Dir, Right1), _), History), Hops1 < Hops, 
     % Config1 = config(Left1, State, Item1, Dir, Right1), 
     same_shape(config(Left1, State, Item1, Dir, Right1), config(Left, State, Item, Dir, Right)),
     % format("~d Same shape as ~d~n", [Hops1, Hops]), 
     % write(Left1), format(" ~k ", [State]), write(Item1), format(" ~k ", [Dir]), write(Right1), nl, 
     % write(Left), format(" ~k ", [State]), write(Item), format(" ~k ", [Dir]), write(Right), nl, 
     regression(config(Left1, State, Item1, Dir, Right1), config(Left, State, Item, Dir, Right), LDiffs1, ItemDiff1, RDiffs1),
     % format("Regressive ~d to ~d~n", [Hops1, Hops]), write(LDiffs1),  format("+", []), write(ItemDiff1),  format("+", []), write(RDiffs1), nl, 
     member(s(Hops2,config(Left2, State, Item2, Dir, Right2), _), History), Hops2 < Hops1, 
     same_shape(config(Left2, State, Item2, Dir, Right2), config(Left1, State, Item1, Dir, Right1)),
     % format("Same (second) shape as ~d~n", [Hops2]), 
     regression(config(Left2, State, Item2, Dir, Right2), config(Left1, State, Item1, Dir, Right1), LDiffs2, ItemDiff2, RDiffs2),
     % format("Regressive (second) ~d to ~d~n", [Hops2, Hops1]), write(LDiffs2), format("+", []), write(ItemDiff2),  format("+", []), write(RDiffs2), nl, 

     LDiffs1 == LDiffs2, ItemDiff1 == ItemDiff2, RDiffs1 == RDiffs2, 
    
     % format("Diffs same ... ~n", []), 
     % find minimum regressor
     regression_counters(Left, LDiffs1, [Item|Right], [ItemDiff1|RDiffs1], [], Regs), 

     % format("Regression counters are: ", []), write(Regs), nl, 
     length(Regs, N), N > 0, 

     ( N > 1 -> (member(otrace,Inputs) ->  (format("% Multiple regressors found~n", []),fail) ; fail) ; true), %% Notify about multiple regressors if appropriate, but don't deal with them ... 
     
     % ( (N > 1, member(otrace,Inputs) ) -> (format("% Multiple regressors found~n", []), fail) ; true), 
     % N =< 1, 

     Regs = [reg(Num,L)|_], % set_new_count(Num, L, Count), Count > 0, % Count is Num // L, Count > 0, % No point unless we are going to change something!

     % format("Calculating minimum ...~n", []), 
     % New calculation of minimum value ...
     relevant_history(Hops2, Hops1, History, First_Section), 
     % format("Found history~n", []), 
     member(s(Hops1, Mid_Config, FinalPos), First_Section), 
     % format("Found Config~n", []), write(First_Section), nl, 
     max_pos(First_Section, FinalPos, MaxPos),
     % format("Found Max~n", []), 
     min_pos(First_Section, FinalPos, MinPos),
     % format("Finding Final value ...~n", []), 
     find_final_otter(MinPos, FinalPos, MaxPos, Mid_Config, LDiffs2, ItemDiff2, RDiffs2, FinalValue), FinalValue >= 0, 
     % format("Final value is ~d~n", [FinalValue]), 

     % Now need to make setleaps, predictleaps and set_new_count work on FinalValue rather than just Num and L ... % XXX Up to here
     % Perhaps make the above predicate work as if the minimum argument is 1 ...

     % Diff1 is Hops1 - Hops2, 
     % Diff2nd is (Hops - Hops1) - Diff1, Diff2nd >= 0, %% Avoid some weird cases ... 
     % setleaps(Diff1, Diff2nd, Num, L, FinalValue, Leaps), Leaps > 0, set_new_count(Num, L, Count), Count > 0, % format("Count is ~d~n", [Count]), 

     minimum_regressor(Regs, MinNum, MinL, MinCount),  %%%% Need to make this work for variables for ocelot ..   %% For variables, we will assume there is only one ...
     setleaps(Hops, Hops1, Hops2, MinNum, MinL, Leaps), Leaps > 0, % Variables??

     !, 
     ( (member(otrace, Inputs) ) -> 
	 ( format("Otter Observed: ~d ~d ~d Diff1 is ~d Diff2 is ~d Num is ~d L is ~d FinalValue is ~d Count is ~d Leaps is ~d ", [Hops2, Hops1, Hops, Hops1 - Hops2, Hops - Hops1, Num, L, FinalValue, MinCount, Leaps]), % Hops2 < Hops1 < Hops
	   display_config(config(Left2, State, Item2, Dir, Right2)), format(" + ", []), 
	   display_config(config(Left1, State, Item1, Dir, Right1)), format(" + ", []), 
	   display_config(config(Left, State, Item, Dir, Right)), nl 
          ) ; true ) , 
  
     % member(pos(Pos), Inputs), % format("Pos is ~d~n", [Pos]), 

     final_config(Mode, Num, L, config(Left, State, Item, Dir, Right), LDiffs1, ItemDiff1, RDiffs1, NewConfig),  !, % Commit to this case

     NewHops is Hops + Leaps, 
     (member(otrace, Inputs) -> (format("Final config is ~d:", [NewHops]), display_config(NewConfig), nl, ttyflush); true), 

     % append([s(Hops,Config,Pos)], History, History_Now), 

     % Below is for the ocelot. Leave this for now ...
     %% calculate_pattern(Mode, Hops2, Hops1, Hops, Pos, History_Now, Config, LDiffs1, ItemDiff1, RDiffs1, OtterPattern), 

     %% add otter to M ... 
     %M = machine(List, Trans, Otters),
     %append([OtterPattern], Otters, NewOtters), 
     %NewM = machine(List, Trans, NewOtters),  
     NewM = M, 
     % display_otters(NewOtters),      

     % append([s(Hops,Config,Pos)], History, History_Now), 

     Diff3 is Hops - Hops2, 

     Nested is 0, %% Work out how to do this better ... how do we tell whether this otter is nested or not? 
     update_otters(Leaps, Diff3, Nested, Inputs, NInputs), !, 

     % format("Updated otters~n", []), 

     NewConfig = config(_,_,_,OutDir,_), 
     updateinputs(Config, Mode, Hops, OutDir, Leaps, otter, NInputs, NewConfig, NewHops, NewInputs), 
     true. 

%% Use flex mode as general one. Need to incorporate variables into complex_transition and updatetapemaro (and add a simplex_transition case?)

% % New 'special' case for expanded loops .. 
next_config(_States, _Symbols, _Dirs, M, Config, Mode, Hops, Inputs, NewM, NewConfig, NewHops, NewInputs, cycle) :-
     member(Mode, [flex, search]), 
     member(loops, Inputs), 

     Config = config(_Left, State, Item, Dir, _Right), 
     Item = grp(I, Number), 

     % format("Calling loop with ~k ", [State]), write(I), format("~d ~k ~n", [Number, Dir]), 
     % ( Hops = 95547257425481 -> (format("Checking Loops~n", [])); true), 
     loop_transition(M, State, I, Number, Dir, NewM, NewI, Mult, OutItem, OutDir, Steps), % !, 
     format("% Found loop transition for ~k (", [State]), write(I), format(")^~d ~k: ", [Number, Dir]), write(NewI), write(Mult), write(OutItem), format(" ~k ~n", [OutDir]), 

    % Found loop, so munge configuration into shape ... 
     expand_item_config(Item, Number, NewI, Mult, Config, NConFig), 
     format("% Expansion: ", []), write(I), format(" to ", []), write(NewI), nl, write(NConFig), nl, 
     updatetapemacro(NConFig, Mode, trans(State, NewI, Dir, NewState, OutItem, OutDir, Steps), NLeft1, NItem, NewDir, NRight1, Leaps, Moves),

     check_blank(NLeft1, NLeft),
     check_blank(NRight1, NRight),

     % format("% Updated~n", []), 

     ( member(optcom, Inputs) -> ( compress(config(NLeft, NewState, NItem, NewDir, NRight), config(NewLeft, NewState, NewItem, NewDir, NewRight)), ! ) ; 
	                         ( new_compress_config(config(NLeft, NewState, NItem, NewDir, NRight), config(NewLeft, NewState, NewItem, NewDir, NewRight)), ! ) ), 

     NewHops is Hops + Leaps,
     NewConfig = config(NewLeft, NewState, NewItem, NewDir, NewRight),     

     updateinputs(Config, Mode, Hops, OutDir, Moves, cycle, Inputs, NewConfig, NewHops, NewInputs), !, 
     true. 

next_config(_States, _Symbols, _Dirs, M, Config, Mode, Hops, Inputs, NewM, NewConfig, NewHops, NewInputs, complex) :-
     member(Mode, [flex,search]), 
     % member(Mode, [search]), 
     % format("% Complex transition~n", []), 

     Config = config(_Left, State, Item, Dir, _Right), 
     Item = grp(I, _Number),  

     % format("% Machine is ", []), write(M), write(State), write(Item), nl,

     % format("% Complex transition~n", []), ttyflush, % format("Right is ", []), write(Right), nl, format("show is ", []), show_me(Right), nl,  
     % ( Hops = 95547257425481 -> (format("Checking Complex~n", [])); true), 
     complex_transition(M, State, I, Dir, NewM, NewState, OutItem, OutDir, Steps),  
     % ( member(Hops, [85112,85113]) ->  (format("Transition found at d~n", [Hops]), write(Config), display_config(Config), nl, write(trans(State, I, Dir, NewState, OutItem, OutDir, Steps)), nl); true ),
     % ( Hops = 95547257425481 -> (format("Transition Found~n", [])); true), 
     % format("% Transition found~n", []), 
     % format("% Transition found at d~n", [Hops]), write(Config), display_config(Config), nl,write(Mode), format(" ", []), write(trans(State, I, Dir, NewState, OutItem, OutDir, Steps)), nl,
     updatetapemacro(Config, Mode, trans(State, I, Dir, NewState, OutItem, OutDir, Steps), NLeft1, NItem, NewDir, NRight1, Leaps, Moves),
     % ( member(Hops, [85112,85113]) ->  (format("Updated to ", []), write(config(NLeft, NewState, NItem, NewDir, NRight)), display_config(config(NLeft, NewState, NItem, NewDir, NRight)), nl, ttyflush); true), 

     check_blank(NLeft1, NLeft),
     check_blank(NRight1, NRight),

     % format("% Updated~n", []), 

%%       output_config(M, Config, Mode, Hops, NewInputs, Used), nl, ttyflush, 

     ( member(compress1, Inputs) -> compress(config(NLeft, NewState, NItem, NewDir, NRight), config(NewLeft1, NewState, NewItem1, NewDir, NewRight1)); (NewLeft1 = NLeft, NewItem1 = NItem, NewRight1 = NRight) ), 
     ( member(ctrace, Inputs) -> (output_config(M, config(NLeft, NewState, NItem, NewDir, NRight), Mode, Hops, Inputs, complex), format(" to ", []), output_config(M, config(NewLeft1, NewState, NewItem1, NewDir, NewRight1),Mode,Hops,Inputs,complex),nl ); true ), 
     % ( member(ctrace, Inputs) -> (output_config(M, config(NLeft, NewState, NItem, NewDir, NRight),Mode,Hops,Inputs,complex) ); true ), 
     % ( member(ctrace, Inputs) -> (output_config(M, config(NewLeft1, NewState, NewItem1, NewDir, NewRight1),Mode,Hops,Inputs,complex),nl ); true ), 
     ( member(compress2, Inputs) -> new_compress_config(config(NewLeft1, NewState, NewItem1, NewDir, NewRight1), config(NewLeft2, NewState, NewItem2, NewDir, NewRight2)); (NewLeft2 = NewLeft1, NewItem2 = NewItem1, NewRight2 = NewRight1) ), 

     % ( member(optcom, Inputs) -> ( compress(config(NLeft, NewState, NItem, NewDir, NRight), config(NewLeft, NewState, NewItem, NewDir, NewRight)), ! ) ; 
     % 	                         ( new_compress_config(config(NLeft, NewState, NItem, NewDir, NRight), config(NewLeft, NewState, NewItem, NewDir, NewRight)), ! ) ), 

     NewLeft = NewLeft2, NewItem = NewItem2, NewRight = NewRight2, 

     !, 
     NewHops is Hops + Leaps,
     NewConfig = config(NewLeft, NewState, NewItem, NewDir, NewRight),

     % ( member(Hops, [47165163,47165164,47165165,47165166,47165167,47165168,47165169]) -> (format("~d: ", [NewHops]), writeln(NewConfig)); true ),  

     updateinputs(Config, Mode, Hops, OutDir, Moves, complex, Inputs, NewConfig, NewHops, NewInputs), 
     % format("% Inputs Updated~n", []),  ttyflush, 
     true.

%     next_config2d(M, Config, Mode, Type,Hops, Inputs, NewM, NewConfig, NewHops, NewInputs, Used), !, 
next_config2d(M, Config, Mode, Type, Hops, Inputs, NewM, NewConfig, NewHops, NewInputs, simple) :-
     Mode = naive, Type = rel,
     Config = config2d(State, Index, Map, Symbol, Direction),
     % format("Finding transition~n", []), 
     simple_transition(M, State, Symbol, NewState, OutItem, OutDir, Steps), !, 
     % format("Updating map~n", []), 
     updatemap_rel(Mode, Index, Map, OutItem, OutDir, Direction, NewIndex, NewMap, NewSymbol, NewDirection),
     NewHops is Hops + Steps,
     NewConfig = config2d(NewState, NewIndex, NewMap, NewSymbol, NewDirection), 
     NewM = M,
     % format("Updating pos~n", []), display(Inputs), nl, 
     % display(Inputs1), nl, 
     % format("Updating inputs~n", []), 
     % updateinputs(Config, Mode, Hops, OutDir, 1, naive, Inputs, NewConfig, NewHops, NewInputs), 
     update_steps(Inputs, NewInputs), % Just do this for now ... 
     % format("Updated inputs~n", []), 
     true. 

next_config2d(M, Config, Mode, Type, Hops, Inputs, NewM, NewConfig, NewHops, NewInputs, simple) :-
     Mode = naive, Type = abs,
     Config = config2d(State, Index, Map, Symbol),
     % format("Finding transition~n", []), 
     simple_transition(M, State, Symbol, NewState, OutItem, OutDir, Steps), !, 
     % format("Updating map~n", []), 
     updatemap_abs(Mode, Index, Map, OutItem, OutDir, NewIndex, NewMap, NewSymbol),
     NewHops is Hops + Steps,
     NewConfig = config2d(NewState, NewIndex, NewMap, NewSymbol), 
     NewM = M,
     % format("Updating pos~n", []), display(Inputs), nl, 
     % display(Inputs1), nl, 
     % format("Updating inputs~n", []), 
     % updateinputs(Config, Mode, Hops, OutDir, 1, naive, Inputs, NewConfig, NewHops, NewInputs), 
     update_steps(Inputs, NewInputs), % Just do this for now ... 
     % format("Updated inputs~n", []), 
     true. 

updatemap_rel(Mode, Index, Map, OutItem, OutDir, Direction, NewIndex, NewMap, NewSymbol, NewDirection) :-
    Mode = naive,
    % format("Replacing ~k ~n", [Index]), 
    replace_map(Index, Map, OutItem, NewMap),
    % format("Indexing ~k ~k ~k~n", [Index, OutDir, Direction]), 
    new_index_rel(Index, OutDir, Direction, NewIndex, NewDirection),
    % format("Looking up~n", []), 
    lookup_map(NewIndex, NewMap, NewSymbol).

updatemap_abs(Mode, Index, Map, OutItem, OutDir, NewIndex, NewMap, NewSymbol) :-
    Mode = naive, 
    % format("Replacing ~k ~n", [Index]),
    replace_map(Index, Map, OutItem, NewMap),
    % format("Indexing ~k ~k~n", [Index, OutDir]), 
    new_index_abs(Index, OutDir, NewIndex),
    % format("Looking up ~k~n", [NewIndex]), 
    lookup_map(NewIndex, NewMap, NewSymbol).

replace_map( i(0,Y), map(row( 0, Row0),R1,R2,R3,R4,R5,R6,R7,R8,R9,R10), Symbol, map(row(0, NewRow0),R1,R2,R3,R4,R5,R6,R7,R8,R9,R10)) :- replace_row(Y, Row0,  Symbol,  NewRow0). 
replace_map( i(1,Y), map(R0,row( 1, Row1),R2,R3,R4,R5,R6,R7,R8,R9,R10), Symbol, map(R0,row(1, NewRow1),R2,R3,R4,R5,R6,R7,R8,R9,R10)) :- replace_row(Y, Row1,  Symbol,  NewRow1). 
replace_map( i(2,Y), map(R0,R1,row( 2, Row2),R3,R4,R5,R6,R7,R8,R9,R10), Symbol, map(R0,R1,row(2, NewRow2),R3,R4,R5,R6,R7,R8,R9,R10)) :- replace_row(Y, Row2,  Symbol,  NewRow2). 
replace_map( i(3,Y), map(R0,R1,R2,row( 3, Row3),R4,R5,R6,R7,R8,R9,R10), Symbol, map(R0,R1,R2,row(3, NewRow3),R4,R5,R6,R7,R8,R9,R10)) :- replace_row(Y, Row3,  Symbol,  NewRow3). 
replace_map( i(4,Y), map(R0,R1,R2,R3,row( 4, Row4),R5,R6,R7,R8,R9,R10), Symbol, map(R0,R1,R2,R3,row(4, NewRow4),R5,R6,R7,R8,R9,R10)) :- replace_row(Y, Row4,  Symbol,  NewRow4). 
replace_map( i(5,Y), map(R0,R1,R2,R3,R4,row( 5, Row5),R6,R7,R8,R9,R10), Symbol, map(R0,R1,R2,R3,R4,row(5, NewRow5),R6,R7,R8,R9,R10)) :- replace_row(Y, Row5,  Symbol,  NewRow5). 
replace_map( i(6,Y), map(R0,R1,R2,R3,R4,R5,row( 6, Row6),R7,R8,R9,R10), Symbol, map(R0,R1,R2,R3,R4,R5,row(6, NewRow6),R7,R8,R9,R10)) :- replace_row(Y, Row6,  Symbol,  NewRow6). 
replace_map( i(7,Y), map(R0,R1,R2,R3,R4,R5,R6,row( 7, Row7),R8,R9,R10), Symbol, map(R0,R1,R2,R3,R4,R5,R6,row(7, NewRow7),R8,R9,R10)) :- replace_row(Y, Row7,  Symbol,  NewRow7). 
replace_map( i(8,Y), map(R0,R1,R2,R3,R4,R5,R6,R7,row( 8, Row8),R9,R10), Symbol, map(R0,R1,R2,R3,R4,R5,R6,R7,row(8, NewRow8),R9,R10)) :- replace_row(Y, Row8,  Symbol,  NewRow8). 
replace_map( i(9,Y), map(R0,R1,R2,R3,R4,R5,R6,R7,R8,row( 9, Row9),R10), Symbol, map(R0,R1,R2,R3,R4,R5,R6,R7,R8,row(9, NewRow9),R10)) :- replace_row(Y, Row9,  Symbol,  NewRow9). 
replace_map(i(10,Y), map(R0,R1,R2,R3,R4,R5,R6,R7,R8,R9,row(10, Row10)), Symbol, map(R0,R1,R2,R3,R4,R5,R6,R7,R8,R9,row(10,NewRow10))) :- replace_row(Y, Row10, Symbol, NewRow10). 

replace_row(N, Row, Symbol, NewRow) :- replace_row1(N, 0, [], Symbol, Row, NewRow).
replace_row1(N, M, SoFar, Symbol, [_|Rest], NewRow) :- N == M, append(SoFar, [Symbol], Temp), append(Temp, Rest, NewRow).
replace_row1(N, M, SoFar, Symbol, [This|Rest], NewRow) :- N > M, M1 is M + 1, append(SoFar, [This], NewSoFar), replace_row1(N, M1, NewSoFar, Symbol, Rest, NewRow).  
    
% Movement is one of l,r,f,b
% Direction is one of n,e,s,w
% new_index_rel(i(X,Y), Movement, Direction, i(NewX, NewY), NewDirection).
new_index_rel(i(X,Y), l, n, i(X, NewY), w) :- NewY is (Y-1) mod 11. 
new_index_rel(i(X,Y), r, s, i(X, NewY), w) :- NewY is (Y-1) mod 11. 
new_index_rel(i(X,Y), f, w, i(X, NewY), w) :- NewY is (Y-1) mod 11. 
new_index_rel(i(X,Y), b, e, i(X, NewY), w) :- NewY is (Y-1) mod 11. 
new_index_rel(i(X,Y), l, e, i(NewX, Y), n) :- NewX is (X-1) mod 11. 
new_index_rel(i(X,Y), r, w, i(NewX, Y), n) :- NewX is (X-1) mod 11. 
new_index_rel(i(X,Y), f, n, i(NewX, Y), n) :- NewX is (X-1) mod 11. 
new_index_rel(i(X,Y), b, s, i(NewX, Y), n) :- NewX is (X-1) mod 11.
new_index_rel(i(X,Y), l, s, i(X, NewY), e) :- NewY is (Y+1) mod 11.
new_index_rel(i(X,Y), r, n, i(X, NewY), e) :- NewY is (Y+1) mod 11.
new_index_rel(i(X,Y), f, e, i(X, NewY), e) :- NewY is (Y+1) mod 11.
new_index_rel(i(X,Y), b, w, i(X, NewY), e) :- NewY is (Y+1) mod 11.
new_index_rel(i(X,Y), l, w, i(NewX, Y), s) :- NewX is (X+1) mod 11. 
new_index_rel(i(X,Y), r, e, i(NewX, Y), s) :- NewX is (X+1) mod 11. 
new_index_rel(i(X,Y), f, s, i(NewX, Y), s) :- NewX is (X+1) mod 11. 
new_index_rel(i(X,Y), b, n, i(NewX, Y), s) :- NewX is (X+1) mod 11. 

% new_index_abs(i(X,Y), Movement, i(NewX,NewY)).
new_index_abs(i(X,Y), n, i(NewX,Y)) :- NewX is (X-1) mod 11.
new_index_abs(i(X,Y), e, i(X,NewY)) :- NewY is (Y+1) mod 11.
new_index_abs(i(X,Y), s, i(NewX,Y)) :- NewX is (X+1) mod 11.
new_index_abs(i(X,Y), w, i(X,NewY)) :- NewY is (Y-1) mod 11. 


% turn(Movement, Direction, NewDirection). 
% turn(l,n,w). 
% turn(r,s,w). 
% turn(f,w,w). 
% turn(b,e,w). 
% turn(l,e,n). 
% turn(r,w,n). 
% turn(f,n,n). 
% turn(b,s,n). 
% turn(l,s,e). 
% turn(r,n,e). 
% turn(f,e,e).
% turn(b,w,e). 
% turn(l,w,s). 
% turn(r,e,s). 
% turn(f,s,s).
% turn(b,n,s). 
turn(f,Dir,Dir) :- member(Dir, [n,e,s,w]). 
turn(b,Dir,OppDir) :- opposite(Dir, OppDir). 
turn(l,Dir,NewDir) :- left(Dir, NewDir).  
% turn(l,Dir,NewDir) :- right(Dir, RDir), opposite(RDir, NewDir).  
turn(r,Dir,NewDir) :- right(Dir, NewDir).

move(Dir, Dir, f).
move(Dir, OppDir, b) :- opposite(Dir, OppDir). 
move(Dir, LeftDir, l) :- left(Dir, LeftDir). 
move(Dir, RightDir, r) :- right(Dir, RightDir). 

left(n,w).
left(e,n).
left(s,e).
left(w,s).

right(n,e).
right(e,s).
right(s,w).
right(w,n). 

opposite(n,s). 
opposite(s,n). 
opposite(e,w). 
opposite(w,e). 
    
lookup_map( i(0,Y), map(row( 0, Row0),_,_,_,_,_,_,_,_,_,_),  Symbol) :- lookup_row(Y, Row0,  Symbol). 
lookup_map( i(1,Y), map(_,row( 1, Row1),_,_,_,_,_,_,_,_,_),  Symbol) :- lookup_row(Y, Row1,  Symbol). 
lookup_map( i(2,Y), map(_,_,row( 2, Row2),_,_,_,_,_,_,_,_),  Symbol) :- lookup_row(Y, Row2,  Symbol). 
lookup_map( i(3,Y), map(_,_,_,row( 3, Row3),_,_,_,_,_,_,_),  Symbol) :- lookup_row(Y, Row3,  Symbol). 
lookup_map( i(4,Y), map(_,_,_,_,row( 4, Row4),_,_,_,_,_,_),  Symbol) :- lookup_row(Y, Row4,  Symbol). 
lookup_map( i(5,Y), map(_,_,_,_,_,row( 5, Row5),_,_,_,_,_),  Symbol) :- lookup_row(Y, Row5,  Symbol). 
lookup_map( i(6,Y), map(_,_,_,_,_,_,row( 6, Row6),_,_,_,_),  Symbol) :- lookup_row(Y, Row6,  Symbol). 
lookup_map( i(7,Y), map(_,_,_,_,_,_,_,row( 7, Row7),_,_,_),  Symbol) :- lookup_row(Y, Row7,  Symbol). 
lookup_map( i(8,Y), map(_,_,_,_,_,_,_,_,row( 8, Row8),_,_),  Symbol) :- lookup_row(Y, Row8,  Symbol). 
lookup_map( i(9,Y), map(_,_,_,_,_,_,_,_,_,row( 9, Row9),_),  Symbol) :- lookup_row(Y, Row9,  Symbol). 
lookup_map(i(10,Y), map(_,_,_,_,_,_,_,_,_,_,row(10, Row10)), Symbol) :- lookup_row(Y, Row10, Symbol).  

lookup_row(0, [Symbol|_], Symbol). 
lookup_row(N, [_|Rest], Symbol) :- N > 0, N1 is N-1, lookup_row(N1, Rest, Symbol). 

% transform_rel_to_abs(RelativeMachine, AbsoluteMachine)
% Transforms RelativeMachine (with l,r,f,b transitions) to an equivalent AbsoluteMachine with 4 x the states and n,e,s,w transitions.

transform_rel_to_abs([], []).
transform_rel_to_abs([Trans|Rest], Result) :-
    transform_rel_dir(Trans, n, NTrans), 
    transform_rel_dir(Trans, e, ETrans),
    transform_rel_dir(Trans, s, STrans), 
    transform_rel_dir(Trans, w, WTrans),
    transform_rel_to_abs(Rest, RestMachine),
    append(NTrans, ETrans, Temp1),
    append(STrans, WTrans, Temp2),
    append(Temp1, Temp2, Temp3),
    append(Temp3, RestMachine, Result). 

transform_rel_dir(Trans, Dir, [t(StateDir, Input, Output, NewDir, NewStateNewDir)]) :-
    Trans = t(State, Input, Output, Dir1, NewState), 
    turn(Dir1, Dir, NewDir), 
    transform_state(State, Dir, StateDir),
    transform_state(NewState, NewDir, NewStateNewDir). 

transform_state(State, Dir, StateDir) :- 
    \+ halt_state(State), !, 
    atom_string(State, StateString), atom_string(Dir, DirString), 
    string_concat(StateString, DirString, Temp), 
    atom_string(StateDir, Temp). 
transform_state(State, _Dir, State) :- 
    halt_state(State). 

% transform_abs_to_rel(AbsoluteMachine, RelativeMachine)
% Transforms AbsoluteMachine (with n,e,s,w transitions) to an equivalent RelativeMachine with 4 x the states and l,r,f,b transitions.

transform_abs_to_rel([], []).
transform_abs_to_rel([Trans|Rest], Result) :-
    transform_abs_dir(Trans, n, NTrans), 
    transform_abs_dir(Trans, e, ETrans),
    transform_abs_dir(Trans, s, STrans), 
    transform_abs_dir(Trans, w, WTrans),
    transform_abs_to_rel(Rest, RestMachine),
    append(NTrans, ETrans, Temp1),
    append(STrans, WTrans, Temp2),
    append(Temp1, Temp2, Temp3),
    append(Temp3, RestMachine, Result). 

transform_abs_dir(Trans, Dir, [t(StateDir, Input, Output, OutDir, NewStateDir)]) :-
    Trans = t(State, Input, Output, Dir1, NewState), 
    move(Dir, Dir1, OutDir), 
    transform_state(State, Dir, StateDir),
    transform_state(NewState, Dir1, NewStateDir). 



% Predictions stuff ... 

check_predictions(Hops, Inputs, Config, NewInputs) :- 
     findall(prediction(Hops1, PredictedConfig), previous_prediction(Hops, Inputs, Hops1, PredictedConfig), Predictions),
     check_predictions1(Predictions, Hops, Config), 
     % then delete all predictions from Inputs
     delete_list(Inputs, Predictions, NewInputs). 

previous_prediction(Hops, Inputs, Hops1, PredictedConfig) :- member(prediction(Hops1, PredictedConfig), Inputs), Hops1 =< Hops. 

check_predictions1([], _, _).
check_predictions1([prediction(PHops, PredictedConfig)|Rest], Hops, Config) :-
     PHops < Hops, 
     format("% Prediction skipped at ~d, detected at ~d: ", [PHops, Hops]), display_config(PredictedConfig), format(" had instead ", []), display_config(Config), nl, 
     check_predictions1(Rest, Hops, Config).
check_predictions1([prediction(Hops, PredictedConfig)|Rest], Hops, Config) :-
     Config \== PredictedConfig, % Do we need to be more sophisticated? 
     format("% Prediction not found at ~d: ", [Hops]), display_config(PredictedConfig), format(" had instead ", []), display_config(Config), nl, 
     check_predictions1(Rest, Hops, Config).
check_predictions1([prediction(Hops, Config)|Rest], Hops, Config) :- 
    % Do we need to be more sophisticated? 
     check_predictions1(Rest, Hops, Config).

% delete_list(List1, List2, List3). List 3 is the result of deleting all elements of List2 from List1. 
delete_list(List1, [], List1). 
delete_list(List1, [Item|Rest], List3) :-
    member(Item, List1), delete(List1, Item, Temp), 
    delete_list(Temp, Rest, List3). 
delete_list(List1, [Item|Rest], List3) :-
    \+ member(Item, List1), 
    delete_list(List1, Rest, List3). 

matches(Pattern, Diffs, Config, CoreLeft, ExtraLeft, CoreRight, ExtraRight, Count, InitialVars) :-
    % InitialVars is the initial values of the variables, which come from Config
     Diffs = diffs(LDiffs, ItemDiff, RDiffs), 
     Config = config(Left, State, Item, Dir, Right), 
     Pattern = config(PLeft, PState, PItem, PDir, PRight), 
     State = PState, Dir = PDir, 
     % format("Matching "), write(Config), format(" with ", []), writeln(Pattern), 
     % format("Matching item~n", []), 
     matching([PItem], [Item], [ItemDiff], none, _, _, Count0, [], Vars1),      % Constraints are expressed in terms of the variables in the initial configuration ... 
     % format("Matching Right~n", []), 
     matching(PRight, Right, RDiffs, Count0, CoreRight, ExtraRight, Count1, Vars1, Vars2), 
     % format("Matching left~n", []), 
     matching(PLeft, Left, LDiffs, Count1, CoreLeft, ExtraLeft, Count2, Vars2, Vars3), 
     Count = Count2, 
     InitialVars = Vars3, 
     true. 

% matching(Pattern, Tape, Diffs, CountSoFar, Core, Extra, Count, VarsSoFar, Vars)
% Tape matches pattern Pattern, with Core being the matching part and Extra the unused context. Diffs are used to calculate Count, the maximum number of times this tape can be decremented. 

matching([], Tape, _Diffs, Count, [], Tape, Count, Vars, Vars). 
matching([Pattern|RestP], [], [_|Diffs], CountSoFar, [Item|Core], Extra, Count, VarsSoFar, Vars) :-
    Pattern = grp(I,Num), integer(Num), all_blank(I), Item = grp(I, Num), 
    matching(RestP, [], Diffs, CountSoFar, Core, Extra, Count, VarsSoFar, Vars).
matching([Pattern|RestP], [Item|Rest], [_Diff|Diffs], CountSoFar, [Item|Core], Extra, Count, VarsSoFar, Vars) :-
    Pattern = grp(I,Num), integer(Num), \+ all_blank(I), 
    % format("Case 2~n", []), 
    Item = grp(I, N), N = Num, 
    % format("Matched~n", []), 
    matching(RestP, Rest, Diffs, CountSoFar, Core, Extra, Count, VarsSoFar, Vars).
matching([Pattern|RestP], [Item|Rest], [m(K,L)|Diffs], CountSoFar, [Item|Core], Extra, Count, VarsSoFar, Vars) :-
    Pattern = grp(I,Num), variable(Num), 
    Item = grp(I, N), get_name(Num, Name), append(VarsSoFar, [var(Name, N, K, L)], NewVarsSoFar), 
    L >= 0, % Not regressor    
    % write(Item), format("Not regressor, recursing ... ~n", []), 
    matching(RestP, Rest, Diffs, CountSoFar, Core, Extra, Count, NewVarsSoFar, Vars).
matching([Pattern|RestP], [Item|Rest], [m(K,L)|Diffs], CountSoFar, [Item|Core], Extra, Count, VarsSoFar, Vars) :-
    Pattern = grp(I,Num), variable(Num), 
    Item = grp(I, N), get_name(Num, Name), append(VarsSoFar, [var(Name, N, K, L)], NewVarsSoFar), 
    L < 0, % Regressor, so check for minimum, and if applicable update Count.
    % write(Item), 
    get_minimum(Num, Min), N >= Min, % Ensure N is at least the minimum required 
    C is (N - Min)//(0-L) + 1, update_count(CountSoFar, C, NewCountSoFar), 
    % format("Count updated, recursing ... ~n", []), 
    matching(RestP, Rest, Diffs, NewCountSoFar, Core, Extra, Count, NewVarsSoFar, Vars).

% update_count(Count1, Count2, NewCount). 
update_count(Count1, Count2, Count2) :- integer(Count1), integer(Count2), Count2 < Count1. 
update_count(Count1, Count2, Count1) :- integer(Count1), integer(Count2), Count2 >= Count1. 
update_count(none, Count2, Count2).


% Apply Count to get the instance of FinalConfig
apply_count(Count, FinalConfig, Vars, NewConfig) :-
    FinalConfig = config(Left, State, Item, Dir, Right), 
    apply_count1(Count, Left, Vars, NewLeft),
    apply_count1(Count, [Item], Vars, [NewItem]), 
    apply_count1(Count, Right, Vars, NewRight), 
    NewConfig = config(NewLeft, State, NewItem, Dir, NewRight), 
	true. 
      
apply_count1(_Count, [], _, []).
apply_count1(Count, [Item|Rest], Vars, [NewItem|Result]) :-
    apply_count_item(Count, Item, Vars, NewItem), 
    apply_count1(Count, Rest, Vars, Result). 

apply_count_item(_Count, Item, _, Item) :- is_input(Item).
apply_count_item(_Count, Item, _, Item) :- Item = grp(_I, Num), integer(Num). 
apply_count_item(Count, Item, Vars, NewItem) :- 
    Item = grp(I, Num), variable(Num), 
    get_name(Num, Name), values_var(Name, Vars, Init, C, S), apply_count_variable(Count, C, S, Init, N), NewItem = grp(I,N), true. 

apply_count_variable(Count, C, S, I, N) :- C = 1, N is I + S*Count. 
apply_count_variable(Count, C, S, I, N) :- C > 1, N is (C**Count)*I + S*((C**Count)-1)//(Count-1). 

% Add context to get calculated configuration
add_context(Config, ExtraLeft, ExtraRight, NewConfig) :-
    Config = config(Left, State, Item, Dir, Right), 
    append(Left, ExtraLeft, NewLeft), 
    append(Right, ExtraRight, NewRight), 
    NewConfig = config(NewLeft, State, Item, Dir, NewRight), 
    true. 

verify_otter(M, Mode, Config, LDiffs, ItemDiff, RDiffs, OtterPattern) :-       
     format("Config is ", []), write(Config), format(" Diffs are ", []), write(LDiffs), format(" ", []), write(ItemDiff), format(" ", []), write(RDiffs), nl, 
     variablise(Config, LDiffs, ItemDiff, RDiffs, InitConfig, FinalConfig), 
     format("Variablised to ", []), write(InitConfig), format(" and ", []), write(FinalConfig), nl, 
     variable_bound(VarBound), % add(trace, Inputs, NInputs), 
     % format("Emulating ... ~n", []), 
     % format("M is ", []), writeln(M), 
     % format("InitConfig is ", []), writeln(InitConfig), 
     % format("Mode is ", []), writeln(Mode), 
     % format("FinalConfig is ", []), writeln(FinalConfig), 
     % format("NInputs is ", []), writeln(NInputs), 
     emulate_general(M, InitConfig, VarBound, Mode, verify, [targets([FinalConfig])], [maxsteps(VarBound), otter,trace,history,list], _VHops, VStatus, VOutputs),
	format("Status is ", []), write(VStatus), nl, 
     (VStatus = target(_) -> true; (format("Hit limit of ~d trying to verify otter~n", [VarBound]),fail)), 
	
     member(history(History), VOutputs), 
     
     % member(now(Now), VOutputs), Now = config(_, State, _, Dir, _), 
     % add_to_history(list, State, Dir, [], s(VHops,Now,0), History, NewHistory), reverse(NewHistory, OtterHistory),   

     reverse(History, OtterHistory),   
     % display_history(0, OtterHistory), 	
     OtterHistory = [First|RestHistory], First = s(_,Initial, _), 
     % writeln(VOutputs), 
     member(machine(_M1, M2, _M3), VOutputs), 
     % format("About to traverse~n", []), 
     % writeln(M2),
     % display_config(Initial), nl, 

     initial_varlist(Initial, VarList), 
     traverse_history(M2, 0, Initial, RestHistory, pos(0,0), left(0,0), right(0,0), hops(0, VarList), MaxLeft, MaxRight, FinalPos, FinalHopsList),
     % format("MaxLeft is ", []), write(MaxLeft), format(" MaxRight is ", []), write(MaxRight), nl, 
     % format("FinalPos is ", []), write(FinalPos), nl, 
     %% NOw apply MaxLeft and MaxRight to Config to get constraints for ossified ocelot ... 
     % format("Doing otter pattern ... ~n", []),
     otter_pattern(InitConfig, FinalConfig, Mode, MaxLeft, MaxRight, LDiffs, ItemDiff, RDiffs, FinalPos, OtterInit, OtterDiffs, OtterFinal),
     format("Otter pattern done ~n", []),
     % Next work out how to apply the otter pattern, so that we know what to store .... 

     % format("InitConfig is ", []), display_config(InitConfig), nl,
     % format("Otter Initial is ", []), display_config(OtterInit), nl, write(OtterInit), nl, 
     % format("FinalConfig is ", []), display_config(FinalConfig), nl,
     % format("Otter Final is ", []), display_config(OtterFinal), nl,
     % format("Otter Diffs are ", []), write(OtterDiffs), nl,
     % format("FinalHopsList is ", []), write(FinalHopsList), nl,

     % format("Final status is ", []), write(VStatus), nl,  % VStatus = target(FinalConfig), 
     %% Where do we get HopsFormula from? Use FinalHopsList ... 
     
     HopsFormula = FinalHopsList, 
     OtterPattern = oo(OtterInit, OtterFinal, OtterDiffs, HopsFormula), 

     format("OtterPattern is ", []), display_otters([OtterPattern]), nl,

     true. 

traverse_history(MacroM, _, Current, [], Pos, LeftSoFar, RightSoFar, HopsList, LeftSoFar, RightSoFar, FinalPos, FinalHopsList) :-
     % Just to update final position
     Current = config(_Left, State, Item, InDir, _Right), Item = grp(I, Num), length(I, N), 
     % format("State is ~k ", [State]), 
     member(trans(State, I, InDir, NewState, _OutItem, OutDir, Steps), MacroM), !,  % This will always be there as we already know the history. Doing this live would need complex_transition.
     % format("Transition found~n", []), 
     % format("Last transition ~k ~k ~k ~k ~d ", [State, NewState, InDir, OutDir, N]), write(Num), nl, 
     update_otter_position(Pos, State, NewState, InDir, OutDir, N, Num, FinalPos), 
     % format("Final position done~n", []), 
     update_otter_hops(State, NewState, InDir, OutDir, Num, Steps, HopsList, FinalHopsList),
     % format("Final otter hops done~n", []), 
     true.
	
traverse_history(MacroM, _Hops, Current, Rest, Pos, LeftSoFar, RightSoFar, HopsList, MaxLeft, MaxRight, FinalPos, NewHopsList) :-
     % format("Traversing ~d: ", [Hops]), display_config(Current), format(" HopsList is ", []), write(HopsList), 
     Current = config(_Left, State, Item, InDir, _Right), Item = grp(I, Num), length(I, N), 
     % format("State is ~k ", [State]), 
     member(trans(State, I, InDir, NewState, _OutItem, OutDir, Steps), MacroM), !,  % This will always be there as we already know the history. Doing this live would need complex_transition.
     % format("Transition ~k ~k ~k ~k ~d ", [State, NewState, InDir, OutDir, N]), write(Num), nl, 
     % format("Transition found~n", []), write(Pos), write(LeftSoFar), write(RightSoFar), nl, 
     update_otter_span(Pos, LeftSoFar, RightSoFar, State, NewState, InDir, OutDir, N, Num, NewLeftSoFar, NewRightSoFar), !,
     % format("Span done~n", []),      

     update_otter_position(Pos, State, NewState, InDir, OutDir, N, Num, NewPos), 
     % format("Position done ", []), write(Pos), write(NewPos), write(NewLeftSoFar), write(NewRightSoFar), nl, 

     update_otter_hops(State, NewState, InDir, OutDir, Num, Steps, HopsList, NHopsList), 

     % format(" New HopsList is ", []), write(NHopsList), nl,

     Rest = [Next|Rest1], Next = s(NextHops, NextConfig, _), 
     % format("Next!~n", []), 

     traverse_history(MacroM, NextHops, NextConfig, Rest1, NewPos, NewLeftSoFar, NewRightSoFar, NHopsList, MaxLeft, MaxRight, FinalPos, NewHopsList).

update_otter_position(Pos, _State, _NewState, l, l, _N, _Num, NewPos) :- MinusOne is 0 - 1, add_to_pos(Pos, 0, MinusOne, NewPos). 
update_otter_position(Pos, _State, _NewState, r, r, _N, _Num, NewPos) :- add_to_pos(Pos, 0, 1, NewPos). 
update_otter_position(Pos,  State,  NewState, l, r,  N, _Num, NewPos) :- State \== NewState, add_to_pos(Pos, 0, N, NewPos).
update_otter_position(Pos,  State,  NewState, l, r,  N,  Num, NewPos) :- State == NewState, integer(Num), Temp is N*Num, add_to_pos(Pos, 0, Temp, NewPos). % Acceleration case
update_otter_position(Pos,  State,  NewState, l, r,  N,  Num, NewPos) :- State == NewState, variable(Num), get_coefficient(Num, C), get_sum(Num, S), V1 is N*C, V2 is N*S, add_to_pos(Pos, V1, V2, NewPos). % Acceleration case
update_otter_position(Pos,  State,  NewState, r, l,  N, _Num, NewPos) :- State \== NewState, MinusN is 0 - N, add_to_pos(Pos, 0, MinusN, NewPos).
update_otter_position(Pos,  State,  NewState, r, l,  N,  Num, NewPos) :- State == NewState, integer(Num), Temp is 0 - N*Num, add_to_pos(Pos, 0, Temp, NewPos). % Acceleration case
update_otter_position(Pos,  State,  NewState, r, l,  N,  Num, NewPos) :- State == NewState, variable(Num), get_coefficient(Num, C), get_sum(Num, S), MinusV1 is 0- N*C, MinusV2 is 0 - N*S, add_to_pos(Pos, MinusV1, MinusV2, NewPos). % Acceleration case

update_otter_span(pos(P1,P2), left(L1,L2), right(R1,R2), _State, _NewState, l, l, N, _Num, left(L1, L2), NewRightSoFar) :- 
    Far is P2 + N - 1, maxright(right(R1,R2), pos(P1, Far), NewRightSoFar). 
update_otter_span(pos(P1,P2), left(L1,L2), right(R1,R2), _State, _NewState, r, r, N, _Num, NewLeftSoFar, right(R1,R2)) :- 
    Far is P2 - (N - 1), maxleft(left(L1,L2), pos(P1, Far), NewLeftSoFar). 
update_otter_span(pos(P1,P2), left(L1,L2), right(R1,R2), State, NewState, l, r, N, _Num, left(L1, L2), NewRightSoFar) :- 
    State \== NewState, 
    Far is P2 + N, maxright(right(R1,R2), pos(P1, Far), NewRightSoFar). 
update_otter_span(pos(P1,P2), left(L1,L2), right(R1,R2), State, NewState, l, r, N, Num, left(L1, L2), NewRightSoFar) :- 
    State == NewState, % Acceleration case
    integer(Num),     Far is P2 + N*Num, maxright(right(R1,R2), pos(P1, Far), NewRightSoFar). 
update_otter_span(pos(P1,P2), left(L1,L2), right(R1,R2), State, NewState, l, r, N, Num, left(L1, L2), NewRightSoFar) :- 
    State == NewState, % Acceleration case
    variable(Num), get_coefficient(Num, C), get_sum(Num, S), V1 is N*C, V2 is N*S, 
    add_to_pos(pos(P1,P2), V1, V2, pos(FarP1, FarP2)), 
    maxright(right(R1,R2), pos(FarP1, FarP2), NewRightSoFar). 
update_otter_span(pos(P1,P2), left(L1,L2), right(R1,R2), State, NewState, r, l, N, _Num, NewLeftSoFar, right(R1,R2)) :- 
    State \== NewState, 
    Far is P2 - N, maxleft(left(L1,L2), pos(P1, Far), NewLeftSoFar). 
update_otter_span(pos(P1,P2), left(L1,L2), right(R1,R2), State, NewState, r, l, N, Num, NewLeftSoFar, right(R1,R2)) :- 
    State == NewState, % Acceleration case
    integer(Num), 
    Far is P2 - N*Num, maxleft(left(L1,L2), pos(P1, Far), NewLeftSoFar). 
update_otter_span(pos(P1,P2), left(L1,L2), right(R1,R2), State, NewState, r, l, N, Num, NewLeftSoFar, right(R1,R2)) :- 
    State == NewState, % Acceleration case
    variable(Num), get_coefficient(Num, C), get_sum(Num, S), V1 is N*C, V2 is N*S, 
    MinusV1 is 0 - V1, MinusV2 is 0 - V2, 
    add_to_pos(pos(P1,P2), MinusV1, MinusV2, pos(FarP1,FarP2)), maxleft(left(L1,L2), pos(FarP1, FarP2), NewLeftSoFar). 

update_range(right(R1, R2), grp(I,Num), right(R1, NewR2)) :- 
    integer(Num), length(I, N), NewR2 is R2 - N*Num. 
update_range(right(R1, R2), grp(I,Num), right(NewR1, NewR2)) :- 
    variable(Num), length(I, N), get_coefficient(Num, C), get_sum(Num, S), NewR1 is R1 - N*C, NewR2 is R2 - N*S. 

update_range(left(L1, L2), grp(I,Num), left(L1, NewL2)) :- 
    integer(Num), length(I, N), NewL2 is L2 - N*Num. 
update_range(left(L1, L2), grp(I,Num), left(NewL1, NewL2)) :- 
    variable(Num), length(I, N), get_coefficient(Num, C), get_sum(Num, S), NewL1 is L1 - N*C, NewL2 is L2 - N*S. 

add_to_pos(pos(P1, P2), X, Y, pos(NewP1, NewP2)) :- NewP1 is P1 + X, NewP2 is P2 + Y. 

maxleft(left(L1,L2), pos(P1,P2), left(M1,M2)) :-   AbsP1 is abs(P1), AbsP2 is abs(P2), maxpos(pos(L1, L2), pos(AbsP1,AbsP2), pos(M1,M2)). 
maxright(right(R1,R2), pos(P1,P2), right(M1,M2)) :- maxpos(pos(R1,R2), pos(P1,P2), pos(M1,M2)). 

maxpos(pos(P1, P2), pos(P3, _P4), pos(P1, P2)) :- P1 > P3. 
maxpos(pos(P1, P2), pos(P3, P4), pos(P1, P2)) :- P1 == P3, P2 >= P4. 
maxpos(pos(P1, P2), pos(P3, P4), pos(P3, P4)) :- P1 =< P3, P4 > P2. 


less_hops(Hops1, Hops2) :- integer(Hops1), integer(Hops2), Hops1 < Hops2. 
less_hops(Hops1, Hops2) :- Hops1 = hops(Count1, Vars1), Hops2 = hops(Count2, Vars2), Count1 < Count2, less_list(Vars1, Vars2). % May need to think about this case ... 

less_list([], []).
less_list([h(Name, Count)|Rest], Vars) :-
	member(h(Name, Count2), Vars), Count < Count2,
	less_list(Rest, Vars). 

add_hops(Leaps, Hops, NewHops) :- integer(Hops), NewHops is Hops + Leaps.
add_hops(Leaps, Hops, NewHops) :- 
    \+ integer(Hops), Hops = hops(Count, VarList), Leaps = hops(Count1, VarList1), NewCount is Count + Count1, 
    add_vars(VarList, VarList1, NewVarList), NewHops = hops(NewCount, NewVarList).

add_vars([], _, []). 
add_vars([h(Name, Current)|Rest], VarsList1, [h(Name, NewCurrent)|Result]) :- 
    member(h(Name, Add), VarsList1), 
    NewCurrent is Current + Add,
    add_vars(Rest, VarsList1, Result), 
    true. 

% update_hops/8 is a generalisation of update_hops and update_otter_hops. 

update_hops(_State, _NewState, _Dir, _OutDir, _Number, Leaps, Hops, NewHops) :- integer(Hops), NewHops is Hops + Leaps. 
update_hops(State, NewState, Dir, OutDir, Number, Leaps, Hops, NewHops) :- \+ integer(Hops), 
      update_otter_hops(State, NewState, Dir, OutDir, Number, Leaps, Hops, NewHops).

update_hops(Leaps, Hops, NewHops) :- integer(Hops), NewHops is Hops + Leaps. 

% update_otter_hops(State, NewState, InDir, OutDir, Num, Steps, hops(Count, VarList), hops(NewCount, NewVarList))
update_otter_hops(_State, _NewState, l, l, _Num, Steps, hops(Count, VarList), hops(NewCount, VarList)) :- NewCount is Count + Steps.
update_otter_hops(_State, _NewState, r, r, _Num, Steps, hops(Count, VarList), hops(NewCount, VarList)) :- NewCount is Count + Steps.
update_otter_hops(State, NewState, l, r, _Num, Steps, hops(Count, VarList), hops(NewCount, VarList)) :- State \== NewState, NewCount is Count + Steps. 
update_otter_hops(State, NewState, r, l, _Num, Steps, hops(Count, VarList), hops(NewCount, VarList)) :- State \== NewState, NewCount is Count + Steps. 
update_otter_hops(State, NewState, l, r, Num, Steps, hops(Count, VarList), hops(NewCount, VarList)) :- State = NewState, integer(Num), NewCount is Count + Steps*Num. % Acceleration case
update_otter_hops(State, NewState, l, r, Num, Steps, hops(Count, VarList), hops(NewCount, NewVarList)) :- State = NewState, variable(Num), get_name(Num, Name), get_sum(Num, Sum), NewCount is Count + Steps*Sum, update_varlist(VarList, Name, Steps, NewVarList). % Acceleration case
update_otter_hops(State, NewState, r, l, Num, Steps, hops(Count, VarList), hops(NewCount, VarList)) :- State = NewState, integer(Num), NewCount is Count + Steps*Num. % Acceleration case
update_otter_hops(State, NewState, r, l, Num, Steps, hops(Count, VarList), hops(NewCount, NewVarList)) :- State = NewState, variable(Num), get_name(Num, Name), get_sum(Num, Sum), NewCount is Count + Steps*Sum, update_varlist(VarList, Name, Steps, NewVarList). % Acceleration case

% update_varlist(VarList, Name, Steps, NewVarList) Name is an integer from 1 upwards. VarList is a list of elements of the form h(Name, Current)
update_varlist(VarList, Name, Steps, NewVarList) :-
    member(h(Name, Current), VarList), 
    NewCurrent is Current + Steps, 
    delete(VarList, h(Name, Current), Temp), 
    append([h(Name, NewCurrent)], Temp, NewVarList). 

% varlist1([Item|Rest], 1, Prev, Prev, Item, Rest).
% varlist1([Item|Rest], N, Prev, NewPrev, Current, Next) :- N > 1, N1 is N-1, append(Prev, [Item], NPrev),  varlist1(Rest, N1, NPrev, NewPrev, Current, Next).

initial_varlist(Initial, VarList) :- Initial = config(Left, _, Item, _, Right), append(Left, [Item|Right], Tape), vars_init(Tape, [], VarList).

vars_init([], SoFar, SoFar).
vars_init([Item|Rest], SoFar, VarList) :- is_input(Item), vars_init(Rest, SoFar, VarList). 
vars_init([Item|Rest], SoFar, VarList) :- Item = grp(_, N), integer(N), vars_init(Rest, SoFar, VarList). 
vars_init([Item|Rest], SoFar, VarList) :- Item = grp(_, N), variable(N), get_name(N, Name), append(SoFar, [h(Name,0)], NewSoFar), vars_init(Rest, NewSoFar, VarList). 

% zeroes(0, []).
% zeroes(N, [0|Rest]) :- N > 0, N1 is N-1, zeroes(N1, Rest). 

otter_pattern(InitConfig, FinalConfig, Mode, MaxLeft, MaxRight, LDiffs, ItemDiff, RDiffs, FinalPos, OtterInit, diffs(LeftDiffs, OtterItemDiff, RightDiffs), OtterFinal) :-
    InitConfig = config(Left, State, Item, l, Right), % Include Item in right extent
    
    format("Measuring left ...", []), write(MaxLeft), write(Left), nl, 
    measure(Mode, Left, LDiffs, MaxLeft, OtterLeft, LeftDiffs), 
    % format("Otter left is ", []), write(OtterLeft), nl, 

    format("Measuring right ...", []), write(MaxRight), write(Item), nl, 
    measure(Mode, [Item|Right], [ItemDiff|RDiffs], MaxRight, OtterR, DiffsR),
    OtterR = [OtterItem|OtterRight], DiffsR = [OtterItemDiff|RightDiffs], 
   
    OtterInit = config(OtterLeft, State, OtterItem, l, OtterRight), 
    
    %% Next find the width of OtterInit

    format("Finding width of", []), write(OtterR), nl, 
    width([OtterItem|OtterRight], 0, 0, VarR, ConstR), InitMaxRight = right(VarR, ConstR), % format("Right width found~n", []), 
    width(OtterLeft, 0, 0, VarL, ConstL), InitMaxLeft = left(VarL, ConstL), % format("Left width found~n", []), 

    % format("Init Max Left is ", []), writeln(InitMaxLeft), 
    % format("Init Max Right is ", []), writeln(InitMaxRight), 

    %% Adjust this by FinalPos to find the corresponding parts of FinalConfig

    adjust(FinalPos, InitMaxLeft, FinalMaxLeft), 
    adjust(FinalPos, InitMaxRight, FinalMaxRight), 
    
    % format("Final Max Leaft is ", []), writeln(FinalMaxLeft), 
    % format("Final Max Right is ", []), writeln(FinalMaxRight), 

    %% Then use these updated values to measure FinalConfig to get OtterFinal

    FinalConfig = config(FLeft, State, FItem, l, FRight), 
    measure(Mode, FLeft, LDiffs, FinalMaxLeft, OtterFinalLeft, _),

    format("Measured left~n", []), 

    % Item must be present, so only measure extent into Right ...
    update_range(FinalMaxRight, Item, NewMaxRight), measure(Mode, FRight, RDiffs, NewMaxRight, OtterFinalRight, _), 
    format("Measured right~n", []), ttyflush, 
    OtterFinalItem = FItem,
    % format("Measured right~n", []), ttyflush, write(OtterFR), nl, 
    % OtterFR = [_|OtterFinalRight],  
    % format("Measured right~n", []), ttyflush, 
    % format("OtterFinalLeft is ", []), write(OtterFinalLeft), ttyflush, 
    % format("OtterFinalRight is ", []), write(OtterFinalRight), ttyflush, 
    % format("OtterFinalItem is ", []), write(OtterFinalItem), nl, ttyflush, 

    OtterFinal = config(OtterFinalLeft, State, OtterFinalItem, l, OtterFinalRight), 

    % Find minimal regressor, work out Count, apply that number of iterations to FinalConfig ...

    true. 

otter_pattern(InitConfig, FinalConfig, Mode, MaxLeft, MaxRight, LDiffs, ItemDiff, RDiffs, OtterInit, diffs(LeftDiffs, OtterItemDiff, RightDiffs), OtterFinal) :-
    InitConfig = config(Left, State, Item, r, Right), % Include Item in left extent
    measure(Mode, Right, RDiffs, MaxRight, OtterRight, RightDiffs), 
    measure(Mode, [Item|Left], [ItemDiff|LDiffs], MaxLeft, OtterL, DiffsL),
    OtterL = [OtterItem|OtterLeft], DiffsL = [OtterItemDiff, LeftDiffs], 

    OtterInit = config(OtterLeft, State, OtterItem, r, OtterRight), 

    %% Next find the width of OtterInit

    % format("Finding width of ", []), write(OtterL), nl, 
    width([OtterItem|OtterLeft], 0, 0, VarL, ConstL), InitMaxLeft = left(VarL, ConstL), % format("Left width found~n", []), 
    width(OtterRight, 0, 0, VarR, ConstR), InitMaxRight = right(VarR, ConstR), % format("Right width found~n", []), 

    % format("Init Max Left is ", []), writeln(InitMaxLeft), 
    % format("Init Max Right is ", []), writeln(InitMaxRight), 

    %% Adjust this by FinalPos to find the corresponding parts of FinalConfig

    adjust(FinalPos, InitMaxLeft, FinalMaxLeft), 
    adjust(FinalPos, InitMaxRight, FinalMaxRight), 

    %% Then use these updated values to measure FinalConfig to get OtterFinal
    FinalConfig = config(FLeft, State, FItem, r, FRight), % Include Item in left extent
    measure(Mode, FRight, RDiffs, FinalMaxRight, OtterFinalRight, _), 

   % Item must be present, so only measure extent into Left ...
    update_range(FinalMaxLeft, Item, NewMaxLeft), measure(Mode, FLeft, LDiffs, NewMaxLeft, OtterFL, _), 
    OtterFinalItem = FItem, 
    OtterFL = [_|OtterFinalLeft], 

    OtterFinal = config(OtterFinalLeft, State, OtterFinalItem, r, OtterFinalRight), 
    
    % Find minimal regressor, work out Count, apply that number of iterations to FinalConfig ...

    true. 

adjust(pos(P1,P2), left(L1, L2), left(NewL1, NewL2)) :- NewL1 is L1 + P1, NewL2 is L2 + P2. 
adjust(pos(P1,P2), right(R1, R2), right(NewR1, NewR2)) :- NewR1 is R1 - P1, NewR2 is R2 - P2. 

measure(_, _, Diffs, right(R1,R2), [], Diffs) :- R1 =< 0, R2 =< 0. 
measure(macro(K), [], Diffs, right(R1, R2), [grp(Blanks, N)], [m(1,0)|Diffs]) :- 
    R1 = 0, R2 > 0, N is (R2 + (K-1)) // K, blank_symbol(B), blanks(B, K, Blanks).  
measure(macro(K), [], Diffs, right(R1, R2), [grp(Blanks, N)], [m(1,0)|Diffs]) :- 
    R1 > 0, R2 > 0, N is (R2 + (K-1)) // K, blank_symbol(B), blanks(B, K, Blanks). %% ??? Shouldn't happen???  
measure(macro(K), [Item|RestTape], [ItemDiff|RestDiffs], right(R1, R2), [Item|NewTape], [ItemDiff|NewDiffs]) :-
    Item = grp(I, Num), integer(Num), length(I, N), R2 >= Num*N, !, NewR2 is R2 - Num,
    measure(macro(K), RestTape, RestDiffs, right(R1, NewR2), NewTape, NewDiffs). 
measure(macro(K), [Item|RestTape], [ItemDiff|RestDiffs], right(R1, R2), [grp(I,R2)|NewTape], [ItemDiff|NewDiffs]) :-
    Item = grp(I, Num), integer(Num), length(I,N), R2 < Num*N, !, 
    measure(macro(K), RestTape, RestDiffs, right(R1, 0), NewTape, NewDiffs). 
measure(macro(K), [Item|RestTape], [ItemDiff|RestDiffs], right(R1, R2), [Item|NewTape], [ItemDiff|NewDiffs]) :-
    Item = grp(I, Num), variable(Num), length(I,N), get_coefficient(Num, C), get_sum(Num, S), R1 >= N*C, !, NewR1 is R1 - N*C, NewR2 is R2 - N*S, 
    measure(macro(K), RestTape, RestDiffs, right(NewR1, NewR2), NewTape, NewDiffs). 
measure(macro(_K), [Item|_RestTape], [ItemDiff|_RestDiffs], right(0, R2), [grp(I,Num1)], [ItemDiff]) :-
    Item = grp(I, Num), variable(Num), length(I,N), R2 > 0, Min is  (R2 // N) + 1, add_to_minimum(Num, Min, Num1). %% Take it all from the variable ... 
measure(macro(_K), [Item|_RestTape], [ItemDiff|_RestDiffs], right(R1, _R2), [Item], [ItemDiff]) :-
    Item = grp(I, Num), variable(Num), length(I,N), get_coefficient(Num, C), R1 < N*C, R1 > 0, true. %% ??? Will have to think about this one ... 

measure(_, _, Diffs, left(L1,L2), [], Diffs) :- L1 =< 0, L2 =< 0. 
measure(macro(K), [], Diffs, left(L1, L2), [grp(Blanks, N)], [m(1,0)|Diffs]) :- 
    L1 = 0, L2 > 0, N is (L2 + (K-1)) // K, blank_symbol(B), blanks(B, K, Blanks).  
measure(macro(K), [], Diffs, left(L1, L2), [grp(Blanks, N)], [m(1,0)|Diffs]) :- 
    L1 > 0, L2 > 0, N is (L2 + (K-1)) // K, blank_symbol(B), blanks(B, K, Blanks). %% ??? Shouldn't happen???  
measure(macro(K), [Item|RestTape], [ItemDiff|RestDiffs], left(L1, L2), [Item|NewTape], [ItemDiff|NewDiffs]) :-
    Item = grp(I, Num), integer(Num), length(I, N),  L2 >= Num*N, !, NewL2 is L2 - Num*N,
    measure(macro(K), RestTape, RestDiffs, left(L1, NewL2), NewTape, NewDiffs). 
measure(macro(K), [Item|RestTape], [ItemDiff|RestDiffs], left(L1, L2), [grp(I,L2)|NewTape], [ItemDiff|NewDiffs]) :-
    Item = grp(I, Num), integer(Num), length(I,N), L2 < Num*N, !, 
    measure(macro(K), RestTape, RestDiffs, left(L1, 0), NewTape, NewDiffs). 
measure(macro(K), [Item|RestTape], [ItemDiff|RestDiffs], left(L1, L2), [Item|NewTape], [ItemDiff|NewDiffs]) :-
    Item = grp(I, Num), variable(Num), length(I,N), get_coefficient(Num, C), get_sum(Num, S), L1 >= N*C, !, NewL1 is L1 - N*C, NewL2 is L2 - N*S, 
    % format("New measure is ", []), write(left(NewL1, NewL2)), nl, 
    measure(macro(K), RestTape, RestDiffs, left(NewL1, NewL2), NewTape, NewDiffs). 
measure(macro(_K), [Item|_RestTape], [ItemDiff|_RestDiffs], left(0, L2), [grp(I,Num1)], [ItemDiff]) :-
    Item = grp(I, Num), variable(Num), length(I,N), L2 > 0, Min is  (L2 // N) + 1, add_to_minimum(Num, Min, Num1). %% Take it all from the variable ... 
measure(macro(_K), [Item|_RestTape], [ItemDiff|_RestDiffs], left(L1, _L2), [Item], [ItemDiff]) :-
    Item = grp(I, Num), variable(Num), length(I,N), get_coefficient(Num, C), L1 < N*C, L1 > 0, true. %% ??? Will have to think about this one ... 

width([], Var, Const, Var, Const).
width([grp(I,Num)|Rest], VarSoFar, ConstSoFar, Var, Const) :-
	integer(Num), length(I, N), NewConstSoFar is ConstSoFar + N*Num,
	width(Rest, VarSoFar, NewConstSoFar, Var, Const). 
width([grp(I,Num)|Rest], VarSoFar, ConstSoFar, Var, Const) :-
	variable(Num), length(I,N), get_coefficient(Num, C), get_sum(Num, S), NewVarSoFar is VarSoFar + N*C, NewConstSoFar is ConstSoFar + N*S, 
        width(Rest, NewVarSoFar, NewConstSoFar, Var, Const). 

%% Need to incorporate what rule was used here. 

setleaps(Hops, Hops1, Hops2, Num, L, Leaps) :-
     integer(Hops), integer(Hops1), integer(Hops2), 
     Diff1 is Hops1 - Hops2, 
     Diff2nd is (Hops - Hops1) - Diff1, % Diff2nd > 0, %% Why???
     set_new_count(Num, L, Count), % May need to change this ... 
     Leaps is ( Count*Count  + Count) *Diff2nd/2 + Count*(Diff2nd + Diff1), 
     % Leaps > 0, 
     true.

setleaps(Hops, Hops1, Hops2, Num, L, _Leaps) :-
     \+ (integer(Hops), integer(Hops1), integer(Hops2)), 
     format("Hops, Hops1, Hops2, Num, L: ", []), write(Hops), write(Hops1), write(Hops2), write(Num), write(L), nl, 
     true.

% setleaps(14, 7, 0, v(1, 1, -2, 0), 1, Leaps) 

set_new_count(Num, L, Count) :- integer(Num), X is Num mod L, X > 0, Count is Num // L, Count > 0. % Fail if Count = 0. 
set_new_count(Num, L, Count) :- integer(Num), X is Num mod L, X is 0, Count is (Num // L) - 1, Count > 0. % Fail if Count = 0.
set_new_count(Num, 1, Num) :- variable(Num). % , get_coefficient(Num, C), get_sum(Num, S), true.
set_new_count(Num, L, Count) :- variable(Num), L > 1, Count = Num // L. % , get_coefficient(Num, C), get_sum(Num, S), true.

set_new_var_count(Num, L, FinalValue, Count) :- 
        Count = ( (Num - FinalValue) // L).
set_new_var_count(Num, L, Count) :- 
       Count = (Num // L)  - (((Num//L)*L)//Num). % Second term is 0 if Num mod L > 0, 1 if Num mod L = 0. This means we can 'delay' the set_new_count calcuation until the value of Num is known. Crude, but ... 

predictleaps(Diff1, Diff2nd, Num, L, FinalValue, Leaps) :-
     % Uses formula for a_n - a_0 
     var(Num), 
     set_new_var_count(Num, L, FinalValue, Count), 
     Leaps = (Count)*Diff1 + (Count - 1)*(Count)*Diff2nd/2.

predictleaps(Diff1, Diff2nd, Num, L, Leaps) :-
     % Uses formula for a_n - a_0 
     var(Num), 
     set_new_var_count(Num, L, Count), 
     Leaps = (Count)*Diff1 + (Count - 1)*(Count)*Diff2nd/2.


%% Up to here ... 
calculate_leaps(Count, InitialVars, HopsFormula, Leaps) :-
    % InitialVars is the Yi0,ki and li values as a list of elements of the form var(Name, N, K, L), HopsFormula gives the ais and d
     HopsFormula = hops(D, AList), % Alist is a list of the form h(Name, Ai) 
     calculate_sum(AList, InitialVars, Count, 0, 0, AYS, ALT), 
     Leaps = D * Count + AYS + ALT, 
     true. 

calculate_sum([], _Vars, _Count, AYSSoFar, ALTSoFar, AYSSoFar, ALTSoFar).
calculate_sum([h(_Name,Ai)|Rest], Vars, Count, AYSSoFar, ALTSoFar, AYS, ALT) :-
    Ai = 0, calculate_sum(Rest, Vars, Count, AYSSoFar, ALTSoFar, AYS, ALT). 
calculate_sum([h(Name,Ai)|Rest], Vars, Count, AYSSoFar, ALTSoFar, AYS, ALT) :-
    Ai > 0, values_var(Name, Vars, N, K, L), 
    s_value(K, Count, NewAYS),  t_value(K, Count, NewALT), 
    NewAYSSoFar is AYSSoFar + Ai*N*NewAYS, 
    NewALTSoFar is ALTSoFar + Ai*L*NewALT, 
    calculate_sum(Rest, Vars, Count, NewAYSSoFar, NewALTSoFar, AYS, ALT). 

values_var(Name, Vars, N, K, L) :- member(var(Name, N, K, L), Vars). 

s_value(K, Count, Count) :- K = 1. 
s_value(K, 0, 0) :- K > 1. 
s_value(K, Count, AYS) :- K > 1, Count > 0, AYS is (K**Count - 1)//(K-1). 

t_value(K, Count, ALT) :- K = 1, ALT is Count*(Count-1)//2. 
t_value(K, Count, ALT) :- K > 1, T1 is (K-1)*(K-1), ALT is (K**Count -Count*K + Count - 1)//T1. 

minimum_regressor(Regs, MinNum, MinL, MinCount) :-
    all_integer(Regs), Regs = [reg(Num,L)|RestRegs], set_new_count(Num, L, Count),
    minimum_regressor1(RestRegs, Num, L, Count, MinNum, MinL, MinCount). 
minimum_regressor(Regs, Num, L, Count) :-
    \+ all_integer(Regs), Regs = [reg(Num,L)], %% Only allow a single regressor in the variable case, for now ... 
    set_new_count(Num, L, Count).

minimum_regressor1([], Num, L, Count, Num, L, Count).
minimum_regressor1([reg(Num,L)|Rest], _NumSoFar, _LSoFar, CountSoFar, MinNum, MinL, MinCount) :-
    set_new_count(Num, L, Count), Count < CountSoFar, 
    minimum_regressor1(Rest, Num, L, Count, MinNum, MinL, MinCount).
minimum_regressor1([reg(Num,L)|Rest], NumSoFar, LSoFar, CountSoFar, MinNum, MinL, MinCount) :-
    set_new_count(Num, L, Count), Count >= CountSoFar, 
    minimum_regressor1(Rest, NumSoFar, LSoFar, CountSoFar, MinNum, MinL, MinCount).

all_integer([]).
all_integer([reg(Num,_)|Rest]) :- integer(Num), all_integer(Rest). 

opposite_direction(l,r). 
opposite_direction(r,l). 

same_shape(config(Left1, State1, Item1, Dir1, Right1), config(Left2, State2, Item2, Dir2, Right2)) :-
     State1 == State2, 
     Dir1 == Dir2, 
     same_shape1(Left1, Left2),
     same_shape1([Item1], [Item2]),
     same_shape1(Right1, Right2).

same_shape1([], []).
same_shape1([grp(I1,N1)|Rest1], [grp(I2,N2)|Rest2]) :-
     integer(N1), integer(N2),
     I1 == I2,
     same_shape1(Rest1, Rest2). 
same_shape1([grp(I1,N1)|Rest1], [grp(I2,N2)|Rest2]) :-
     variable(N1), variable(N2),
     I1 == I2,
     same_shape1(Rest1, Rest2). 

regression(config(Left1, _State1, Item1, _Dir1, Right1), config(Left2, _State2, Item2, _Dir2, Right2), LDiffs, ItemDiff, RDiffs) :- 
     changes(Left1, Left2, LDiffs),    
     changes(Right1, Right2, RDiffs),  
     changes([Item1], [Item2], [ItemDiff]),
     append(LDiffs, [ItemDiff|RDiffs], List), 
     regressive(List).

changes([], [], []).
changes([grp(I1,N1)|R1], [grp(I2,N2)|R2], [m(1,L)|Rest]) :-
        I1 == I2, 
	integer(N1), integer(N2), 
	L is N2 - N1,
	changes(R1, R2, Rest), !. 
changes([grp(I1,N1)|R1], [grp(I2,N2)|R2], [m(1,L)|Rest]) :-
        I1 == I2, 
	variable(N1), variable(N2), 
        value(N1, V1), value(N2, V2), %%% Check this one!!
        L is V2 - V1,
	changes(R1, R2, Rest), !. 

regressive([m(_, LL)|_LDiffs], _RDiffs) :-  LL < 0. 
regressive([m(_,LL)|_LDiffs], [m(_,RR)|_RDiffs]) :- LL >= 0, RR < 0.
regressive([m(_,LL)|LDiffs], [m(_,RR)|RDiffs]) :- LL >= 0, RR >= 0, regressive(LDiffs, RDiffs).

regressive([m(_, LL)|_Diffs]) :- LL < 0.
regressive([m(_, LL)|Diffs]) :- LL >= 0, regressive(Diffs).

% Progression from Config1 to Config2 ... First check only 
progressive(config(Left1, State, Item1, Dir, Right1), config(Left2, State, Item2, Dir, Right2)) :-
     changes(Left1, Left2, LDiffs),    
     changes(Right1, Right2, RDiffs),  
     changes([Item1], [Item2], [ItemDiff]),
     append(LDiffs, [ItemDiff|RDiffs], List), 
     progressive1(List).

progressive1([]). 
progressive1([m(_,LL)|Diffs]) :- LL >= 0, progressive1(Diffs). 

real_progression([], [], [], [], []).
real_progression([grp(I,N0)|R0], [grp(I,N1)|R1], [grp(I,N2)|R2], [grp(I,N3)|R3], [Diff|Rest]) :-
	real_progression1(N0, N1, N2, N3, Diff), 
	real_progression(R0, R1, R2, R3, Rest). 	

% real_progression([grp(I,N0)|R0], [grp(I,N1)|R1], [grp(I,N2)|R2], [grp(I,N3)|R3], [m(K,L)|Rest]) :-
%         integer(N0), integer(N1), integer(N2), integer(N3), % format("% Linear case ~d ~d ~d ~d ~n", [N0,N1,N2,N3]), 
% 	N3 > N2, N2 > N1, N1 > N0, L is N1 - N0, L is N2 - N1, L is N3 - N2, !, % linear progression
% 	K is 1, 
% 
% real_progression([grp(I,N0)|R0], [grp(I,N1)|R1], [grp(I,N2)|R2], [grp(I,N3)|R3], [m(K,L)|Rest]) :-
%         integer(N0), integer(N1), integer(N2), integer(N3), 
% 	N3 > N2, N2 > N1, N1 > N0, N3 - N2 > N2 - N1, N2 - N1 > N1 - N0, 0 is (N3-N2) mod (N2-N1), !, 
% 	K is (N3-N2) // (N2-N1), 
% 	L is N1 - K*N0, L >= 0, 
% 	real_progression(R0, R1, R2, R3, Rest). 
% real_progression([grp(I,N0)|R0], [grp(I,N1)|R1], [grp(I,N2)|R2], [grp(I,N3)|R3], [m(0,0)|Rest]) :-
	% ((N2 = N1);(N2 > N1, N2 = N3)), 
%         integer(N0), integer(N1), integer(N2), integer(N3), 
% 	N1 = N2, N2 = N3, N1 = N0, !, 
% 	real_progression(R0, R1, R2, R3, Rest). 

%real_progression1(N0, N1, N2, N3, Diff). 
real_progression1(N0, N1, N2, N3, m(0,0)) :- 
	integer(N0), integer(N1), integer(N2), integer(N3), N1 is N2, N2 is N3, N1 is N0, !. 
real_progression1(N0, N1, N2, N3, m(1,L)) :- 
	integer(N0), integer(N1), integer(N2), integer(N3), 
	N3 > N2, N2 > N1, N1 > N0, L is N1 - N0, L is N2 - N1, L is N3 - N2, !. % linear progression
real_progression1(N0, N1, N2, N3, m(K,L)) :- 
        integer(N0), integer(N1), integer(N2), integer(N3), 
	N3 > N2, N2 > N1, N1 > N0, N3 - N2 > N2 - N1, N2 - N1 > N1 - N0, 0 is (N3-N2) mod (N2-N1), !, 
	K is (N3-N2) // (N2-N1), K is (N2-N1) // (N1-N0), K is (N3-N1) // (N2-N0), 
	L is N1 - K*N0, L >= 0, !. 

regression_counters([L1|Left], [LDiff|LDiffs], Right, RDiffs, SoFar, Counts) :-
      regressors(SoFar, L1, LDiff, NewSoFar), 
      regression_counters(Left, LDiffs, Right, RDiffs, NewSoFar, Counts). 
regression_counters([], [], [R1|Right], [RDiff|RDiffs], SoFar, Counts) :-
    regressors(SoFar, R1, RDiff, NewSoFar), 
      regression_counters([], [], Right, RDiffs, NewSoFar, Counts). 
regression_counters([], [], [], [], Counts, Counts). 

regressors(List, _Item, Diff, List) :-
      Diff = m(_K,L), L >= 0.
regressors(List, Item, Diff, [reg(Num, LL)|List]) :-
      Item = grp(_I,Num),  
      Diff = m(_K,L), L < 0, 
      LL is 0 - L,
      true. 
      % setcount(Num, LL, Count). 
      %%  Count is Num // LL.

eval_regs([], []).
eval_regs([reg(Num,LL)|Rest], [Count|Result]) :- integer(Num), integer(LL), Count is Num // LL, eval_regs(Rest, Result). 

% setcount(Num, L, Count). 
setcount(Num, L, Count) :-
      T is Num mod L, T > 0, Count is Num // L.
setcount(Num, L, Count) :-
       T is Num mod L, T = 0, Count is Num // L. % Trying to 0 ... 

minimum_list([List], List) :- length([List], 1).
minimum_list([Item|List], Minimum) :- minimum1(Item, List, Minimum).
minimum1(Item, [], Item).
minimum1(Item, [Item2|Rest], Minimum) :-
      Item =< Item2,
      minimum1(Item, Rest, Minimum). 
minimum1(Item, [Item2|Rest], Minimum) :-
      Item > Item2,
      minimum1(Item2, Rest, Minimum). 

final_config(_, Num, _L, Config, _LDiffs, _ItemDiff, _RDiffs, Config) :-
      integer(Num), Num is 0. 
final_config(Mode, Num, L, config(Left, State, Item, Dir, Right), LDiffs, ItemDiff, RDiffs, NewConFig) :-
      integer(Num), 
      Num > 0,
      configlist(Num, L, Left, LDiffs, NewL), %% check what happens in the variable case here
      configlist(Num, L, [Item], [ItemDiff], [NewI]), 
      configlist(Num, L, Right, RDiffs, NewR),
      reconfigurate(Mode, config(NewL, State, NewI, Dir, NewR), NewConFig),
      true. 
final_config(Mode, Num, L, config(Left, State, Item, Dir, Right), LDiffs, ItemDiff, RDiffs, NewConFig) :-
      \+ integer(Num), % assume it is an expression
      configlist(Num, L, Left, LDiffs, NewL), 
      configlist(Num, L, [Item], [ItemDiff], [NewI]), 
      configlist(Num, L, Right, RDiffs, NewR),
      reconfigurate(Mode, config(NewL, State, NewI, Dir, NewR), NewConFig),
      true. 

configlist(_Num, _LL, [], _Diffs, []). 
configlist(Num, LL, [Item|Rest], [Diff|Diffs], [NewItem|Result]) :-
      Item = grp(I,Num1),
      integer(Num), 
      integer(Num1), %%% Make sure a non-zero amount is left, for now ... 
      Diff = m(_K,L),
      set_new_count(Num, LL, Count), 
      NewNum is ( Count * (L)) + Num1, 
      NewItem = grp(I,NewNum), 
      configlist(Num, LL, Rest, Diffs, Result).       

configlist(Num, LL, [Item|Rest], [Diff|Diffs], [NewItem|Result]) :-
      Item = grp(I,Num1), \+ (integer(Num), integer(Num1)), 
      Diff = m(_K,L), L is 0, 
      NewNum = Num1, %% Own expression evaluator here?
      NewItem = grp(I,NewNum), 
      configlist(Num, LL, Rest, Diffs, Result).       

configlist(Num, LL, [Item|Rest], [Diff|Diffs], [NewItem|Result]) :-
      Item = grp(I,Num1), \+ (integer(Num), integer(Num1)), 
      Diff = m(_K,L), \+ (L is 0), %%%% Need to use predictleaps here,  to get the count correct ... 
      set_new_var_count(Num, LL, Count), 
      NewNum = ( (Count) * (L)) + Num1, %% Own expression evaluator here?
      NewItem = grp(I,NewNum), 
      configlist(Num, LL, Rest, Diffs, Result).       

% variablise(Config, LDiffs, ItemDiff, RDiffs, InitConfig, FinalConfig).
% Generates InitConfig and FinalConfig based on Config and differences.

variablise(Config, LDiffs, ItemDiff, RDiffs, InitConfig, FinalConfig) :-
    Config = config(Left, State, Item, Dir, Right), 
    variablise1(1, V1, Left, LDiffs, InitLeft, FinalLeft), 
    variablise1(V1, V2, [Item],  [ItemDiff], [InitItem], [FinalItem]), 
    variablise1(V2, _V3, Right, RDiffs, InitRight, FinalRight), 
    InitConfig = config(InitLeft, State, InitItem, Dir, InitRight), 
    FinalConfig = config(FinalLeft, State, FinalItem, Dir, FinalRight), 
    true. 

variablise1(V, V, [], _, [], []).
variablise1(V, NewV, [Item|Rest], [m(K,L)|RestDiffs], [Init|InitRest], [Final|FinalRest]) :-
    K == 1, L == 0, Item = grp(I,Num), Init = grp(I, Num), Final = grp(I, Num), 
    variablise1(V, NewV, Rest, RestDiffs, InitRest, FinalRest). 
variablise1(V, NewV, [Item|Rest], [m(K,L)|RestDiffs], [Init|InitRest], [Final|FinalRest]) :-
    \+ (K == 1, L == 0), Item = grp(I, _Num), 
    new_variable(V, Var), NV is V+1, var_compute(Var, m(K,L), NewVar), 
    Init = grp(I, Var), Final = grp(I, NewVar), 
    variablise1(NV, NewV, Rest, RestDiffs, InitRest, FinalRest). 

% variablise(config([grp([0,1],3)], a, grp([1],2), l, [grp([0,0],4)]), [m(1,0)], m(1,-1), [m(1,1)], Init, Final)

variable_bound(500). % How long to search for proof ... 

% This assumes no variables. 
compress_config(config(Left, State, Item, Dir, Right), N, config(NewLeft, State, Item, Dir, NewRight)) :- 
     compress_tape(left, N, Left, NewLeft), 
     compress_tape(right, N, Right, NewRight). 

compress_config(config(Left, State, Item, l, Right), N, config(NewLeft, State, Item, Dir, NewRight)) :- 
     compress_tape(Left, N, Left, NewLeft),
     compress_tape(right, N, [Item|Right], NRight), 
     append([NewItem], NewRight, NRight), length([NewItem], 1), 
     Dir = l.

compress_config(config(Left, State, Item, r, Right), N, config(NewLeft, State, Item, Dir, NewRight)) :- 
     compress_tape(Left, N, [Item|Left], NLeft),
     compress_tape(right, N, Right, NewRight), 
     append([NewItem], NewLeft, NLeft), length([NewItem], 1), 
     Dir = r.

compress_tape(_, _, [], []) :- !. 
compress_tape(_, _, Tape, Tape) :- 
     length(Tape, T), minimum_compress_size(S), T < S, !. 
compress_tape(left, N, Tape, Result) :- 
     length(Tape, T), minimum_compress_size(S), T >= S, % ..,
     flatten_tape(left, Tape, FlatTape), 
     compress1(left, 1, N, [], FlatTape, Result). 
compress_tape(right, N, Tape, Result) :- 
     length(Tape, T), minimum_compress_size(S), T >= S, % ..,
     flatten_tape(right, Tape, FlatTape), 
     compress1(right, 1, N, [], FlatTape, Result). 

compress1(Dir, M, N, SoFar, Tape, Result) :-
     M < N, 
     compress2(Dir, M, Tape, MResult), 
     append([MResult], SoFar, NewSoFar), 
     M1 is M + 1,
     compress1(Dir, M1, N, NewSoFar, Tape, Result). 

compress1(_Dir, M, N, SoFar, Tape, Result) :-
      M >= N, 
      best_compress(SoFar, Tape, Result). 

compress2(Dir, M, Tape, Result) :-
      % try all 1 ... M starting positions
      compress21(Dir, 0, M, Tape, [], Results), 
      % pick best one
      best_compress(Results, Tape, Result). 

compress21(Dir, L, M, Tape, SoFar, Results) :-
      L < M,
      compress3(Dir, L, M, Tape, ThisResult), 
      append(SoFar, [ThisResult], NewSoFar), 
      L1 is L+1,
      compress21(Dir, L1, M, Tape, NewSoFar, Results).       

compress21(_Dir, L, M, _Tape, SoFar, SoFar) :-
      L >= M.

% skip first L items and compress every M after that.
compress3(_Dir, L, _M, Tape, Tape) :-
      length(Tape, Len), Len =< L. 

compress3(Dir, L, M, Tape, Result) :-
      length(Tape, Len), Len > L, L == 0, 
      compress4(Dir, M, Tape, Result). 

compress3(Dir, L, M, Tape, Result) :-
      length(Tape, Len), Len > L, L > 0, 
      append(First, Rest, Tape), length(First, L), 
      compress4(Dir, M, Rest, TResult),
      append([grp(First,1)], TResult, Result). 

% Compress every M of Tape
compress4(_Dir, M, Tape, [grp(Tape,1)]) :-
     length(Tape, Len), Len < M. % No point if it is too short. 
compress4(Dir, M, Tape, Result) :-
     length(Tape, Len), Len >= M, 
     append(First, Rest, Tape), length(First, M),
     % format("% Calling compress5 with:", []), display(grp(First,1)), display(Rest), nl, 
     compress5(Dir, M, grp(First,1), Rest, [], Result).

compress5(_Dir, _M, grp(First,N), Tape, SoFar, Result) :-
     length(Tape, Len), Len == 0, 
     append(SoFar, [grp(First,N)], Result). 

compress5(_Dir, M, grp(First,N), Tape, SoFar, Result) :-
     length(Tape, Len), Len < M, Len > 0, 
     append(SoFar, [grp(First,N)], Res),
     append(Res, [grp(Tape,1)], Result). 
compress5(Dir, M, grp(First,N), Tape, SoFar, Result) :-
     length(Tape, Len), Len >= M, 
     append(Next, Rest, Tape), length(Next, M),
     First == Next,
     N1 is N+1,
     compress5(Dir, M, grp(First, N1), Rest, SoFar, Result). 
compress5(Dir, M, grp(First,N), Tape, SoFar, Result) :-
     length(Tape, Len), Len >= M, 
     append(Next, Rest, Tape), length(Next, M),
     First \== Next,
     append(SoFar, [grp(First,N)], NewSoFar), 
     compress5(Dir, M, grp(Next, 1), Rest, NewSoFar, Result). 

best_compress(List, _Tape, Best) :-
     length(List, N), N == 1, append([Best], [], List).  

best_compress(List, Tape, Best) :-
     length(List, N), N > 1, append([First], Rest, List), length([First], 1), 
     best_compress1(First, Rest, Tape, Best).

best_compress1(SoFar, [], _Tape, SoFar). 
best_compress1(SoFar, [Next|Rest], Tape, Result) :-
     quality(Next, Q1),
     quality(SoFar, Q2),  
     best_lower(Next, Q1, SoFar, Q2, Best),
     best_compress1(Best, Rest, Tape, Result). 

best_lower(Item1, [], _Item2, [], Item1). % arbitrary, so ... 
best_lower(_Item1, [], Item2, [_M2|_], Item2). % favour the finer one.
best_lower(Item1, [_M1|_], _Item2, [], Item1). % favour the finer one.
best_lower(Item1, [M1|_], _Item2, [M2|_], Item1) :- M1 < M2.
best_lower(_Item1, [M1|_], Item2, [M2|_], Item2) :- M1 > M2. 
best_lower(Item1, [M1|Rest1], Item2, [M2|Rest2], Item) :- M1 == M2, best_lower(Item1, Rest1, Item2, Rest2, Item).

quality(List, [Quality, Max]) :- length(List, Quality), max_group_length(List, 0, Max).

max_group_length([], SoFar, SoFar).
max_group_length([Item|Rest], SoFar, Max) :-
     Item = grp(I, _Num), length(I, Len),
     maximum(SoFar, Len, NewSoFar),
     max_group_length(Rest, NewSoFar, Max). 

maximum(X,Y,X) :- X >= Y,!.
maximum(X,Y,Y) :- X < Y.
minimum(X,Y,Y) :- X >= Y,!.
minimum(X,Y,X) :- X < Y.

simple_transition(M, State, Item, NewState, NewItem, Dir, 1):-
    \+ halt_state(State), 
     M = machine(TransList, _, _),
     member(t(State, Item, NewItem, Dir, NewState), TransList). 
simple_transition(M, State, Item, NewState, NewItem, Dir, 1):-
     \+ halt_state(State), 
     \+ (M = machine(_TransList, _, _)),
     member(t(State, Item, NewItem, Dir, NewState), M). 

% Think about how this would work for more than two symbols ... 
complex_transition(M, State, Item, InDir, NewM, NewState, OutItem, OutDir, Steps) :-
    \+ halt_state(State), 
    % format("Case 1~n", []), 
    M = machine(_, MacroList, _), 
    member(trans(State, Item, InDir, NewState, OutItem, OutDir, Steps), MacroList), !, 
    NewM = M.

complex_transition(M, State, Item, InDir,  NewM, NewState, OutItem, OutDir, Steps) :-
    \+ halt_state(State), 
    % format("Case 3~n", []), 
    M = machine(_, MacroList, _), 
    \+ member(trans(State, Item, InDir, _NewState, _OutItem, _OutDir, _Steps), MacroList), !, 
    % find new transition
    % format("Finding new transition~n", []), ttyflush, 
    length(Item, Len),
    number_of_states(M, Num), 
    B is truncate(Num * Len * 2**Len), % maxbound(B, Bound), 
    find_transition(M, State, Item, InDir, B, NewM, NewState, OutItem, OutDir, Steps), !. 

% Added case for halt transition 
new_transition(States, Symbols, _Dirs, M, Config, NewM) :-
    number_of_states_used(M, States), number_of_symbols_used(M, Symbols), % So M is "full" ... 
    M = machine(Transitions, List2, List3), % write(Config), nl, 
    Config = config(_Left, State, Item, Dir, _Right), 
    first_item(Item, Dir, I),
    halt_state(HaltState), 
    Trans =  t(State, I, 1, r, HaltState), % New halt transition ... 
    append(Transitions, [Trans], NewTransitions), 
    \+ zero_dextrous(States, NewTransitions), % Make sure the new machine is not 0-dextrous ... 
    NewM = machine(NewTransitions, List2, List3), 
    true. 

new_transition(States, Symbols, Dirs,  M, Config, NewM) :-
    % No need to be exclusive here --- we want this case to work even if the one above does ... 
    M = machine(Transitions, List2, List3), % write(Config), nl, 
    Config = config(_Left, State, Item, Dir, _Right), 
    first_item(Item, Dir, I),
    newstate(States, Symbols, Dirs, Transitions, NewState, Out, OutDir), 
    Trans =  t(State, I, Out, OutDir, NewState), 
    append(Transitions, [Trans], NewTransitions), 
    \+ zero_dextrous(States, NewTransitions), % Make sure the new machine is not 0-dextrous ... 
    add_halt_trans(States, Symbols, NewTransitions, NewTrans), 
    % If the new machine has only one available slot, add the halt transition now. 
    NewM = machine(NewTrans, List2, List3),
    true. 

newstate(States, Symbols, Dirs, List, NewState, Output, Dir) :-
 	dirs_list(Dirs, abs, DirList), % Compatibility hack for now ...
	symbols_list(Symbols, List, SymbolsList), 
	legitimate_list(States, List, StateList), 
	!, 
	member(NewState, StateList), 
        member(Output, SymbolsList), 
        member(Dir, DirList), 
	true. 

up_dir(Dir) :- dirs_list(3, rel, L), member(Dir, L), \+ member(Dir, [l,r]).
down_dir(Dir) :- dirs_list(3,rel, L1), dirs_list(4, rel, L2), member(Dir, L2), \+ member(Dir, L1). 

dirs_list(2, abs, [l,r]). 
dirs_list(2, rel, [f,b]). 
dirs_list(3, rel, [l,r,f]). 
dirs_list(3, abs, [n,s,e]). % ???
dirs_list(4, rel, [l,r,f,b]). 
dirs_list(4, abs, [n,s,e,w]). 

dir(Dirs, Style, X) :- dirs_list(Dirs, Style, List), member(X,List). 

symbols_list(Symbols, List, SymbolsList) :-
	symbols_list1(Symbols, List1),
	legal_list(List, List1, SymbolsList).

symbols_list1(2, [0,1]). 
symbols_list1(3, [0,1,2]). 
symbols_list1(4, [0,1,2,3]). 
symbols_list1(5, [0,1,2,3,4]). 
symbols_list1(6, [0,1,2,3,4,5]). 
symbols_list1(7, [0,1,2,3,4,5,6]). 
symbols_list1(8, [0,1,2,3,4,5,6,7]). 

symbol(N,X) :- symbols_list1(N, List), member(X, List). 

states_list(1, [a]). 
states_list(2, [a,b]). 
states_list(3, [a,b,c]). 
states_list(4, [a,b,c,d]).
states_list(5, [a,b,c,d,e]). 
states_list(6, [a,b,c,d,e,f]). 
states_list(7, [a,b,c,d,e,f,g]). 
states_list(8, [a,b,c,d,e,f,g,h]). 

state(N,X) :- states_list(N, List), member(X, List). 

next_state(a,b).
next_state(b,c).
next_state(c,d).
next_state(d,e).
next_state(e,f).
next_state(f,g).
next_state(g,h).
next_state(h,i).

legal_list(_List, [0,1], [0,1]).
legal_list(_List, [0,1,2], [0,1,2]).
legal_list(List, [0,1,2,3], [0,1,2,3]) :-
	once( member(t(_,_,2,_,_), List) ). 
legal_list(List, [0,1,2,3], [0,1,2]) :-
	\+ member(t(_,_,2,_,_), List). 
legal_list(List, [0,1,2,3,4], [0,1,2,3,4]) :-
	once( member(t(_,_,3,_,_), List) ). 
legal_list(List, [0,1,2,3,4], [0,1,2,3]) :-
    \+ member(t(_,_,3,_,_), List), once( member(t(_,_,2,_,_), List) ). 
legal_list(List, [0,1,2,3,4], [0,1,2]) :-
    \+ member(t(_,_,2,_,_), List).
legal_list(List, [0,1,2,3,4,5], [0,1,2,3,4,5]) :-
	once( member(t(_,_,4,_,_), List) ). 
legal_list(List, [0,1,2,3,4,5], [0,1,2,3,4]) :-
	\+ member(t(_,_,4,_,_), List), once( member(t(_,_,3,_,_), List) ). 
legal_list(List, [0,1,2,3,4,5], [0,1,2,3]) :-
	\+ member(t(_,_,3,_,_), List), once( member(t(_,_,2,_,_), List) ). 
legal_list(List, [0,1,2,3,4,5], [0,1,2]) :-
	\+ member(t(_,_,2,_,_), List).
legal_list(List, [0,1,2,3,4,5,6], [0,1,2,3,4,5,6]) :-
	once( member(t(_,_,5,_,_), List) ). 
legal_list(List, [0,1,2,3,4,5,6], [0,1,2,3,4,5]) :-
	\+ member(t(_,_,5,_,_), List), once( member(t(_,_,4,_,_), List) ). 
legal_list(List, [0,1,2,3,4,5,6], [0,1,2,3,4]) :-
	\+ member(t(_,_,4,_,_), List), once( member(t(_,_,3,_,_), List) ). 
legal_list(List, [0,1,2,3,4,5,6], [0,1,2,3]) :-
	\+ member(t(_,_,3,_,_), List), once( member(t(_,_,2,_,_), List) ). 
legal_list(List, [0,1,2,3,4,5,6], [0,1,2]) :-
	\+ member(t(_,_,2,_,_), List).

legitimate_list(2,_, [a,b]) :- !. 
legitimate_list(3,_, [a,b,c]) :- !. 
legitimate_list(4, List, [a,b,c,d]) :- once(  member(t(_,_,_,_,c), List) ). 
legitimate_list(4, List, [a,b,c]) :- \+ member(t(_,_,_,_,c), List) . 
legitimate_list(5, List, [a,b,c,d,e]) :- once(  member(t(_,_,_,_,d), List) ). 
legitimate_list(5, List, [a,b,c,d]) :- \+ member(t(_,_,_,_,d), List) , once(  member(t(_,_,_,_,c), List) ). 
legitimate_list(5, List, [a,b,c]) :- \+ member(t(_,_,_,_,d), List) , \+  member(t(_,_,_,_,c), List) . 
legitimate_list(6, List, [a,b,c,d,e,f]) :- once(  member(t(_,_,_,_,e), List) ). 
legitimate_list(6, List, [a,b,c,d,e]) :- \+ member(t(_,_,_,_,e), List) , once(  member(t(_,_,_,_,d), List) ). 
legitimate_list(6, List, [a,b,c,d]) :- \+ member(t(_,_,_,_,e), List) , \+ member(t(_,_,_,_,d), List) , once(  member(t(_,_,_,_,c), List) ). 
legitimate_list(6, List, [a,b,c]) :- \+ member(t(_,_,_,_,e), List) ,\+ member(t(_,_,_,_,d), List) , \+  member(t(_,_,_,_,c), List) . 

add_halt_trans(States, Symbols, Trans, Trans) :-
    length(Trans, L), Full is States * Symbols - 1, L < Full. 
add_halt_trans(States, Symbols, Trans, NewTrans) :-
    length(Trans, L), Full is States * Symbols - 1, L == Full,
    states_list(States, StatesList),
    symbols_list1(Symbols, SymbolsList),
    once( missing(StatesList, SymbolsList, Trans, NewState, NewSymbol) ), 
    halt_trans(t(NewState, NewSymbol, NewOut, NewDir, NewNewState)),
    append(Trans, [t(NewState, NewSymbol, NewOut, NewDir, NewNewState)], NewTrans).

 % loop_transition(M, State, I, Number, Dir, NewM, NewI, Mult, OutItem, OutDir, Steps), !, 
% % New 'special' case for expanded loops .. 
loop_transition(M, State, Item, _Number, InDir, NewM, NewI, Mult, OutItem, OutDir, Steps) :-
%   ... found already ... 
    \+ halt_state(State), 
    M = machine(_, MacroList, _), 
    loop_known(State, Item, InDir, NewI, Mult, OutItem, OutDir, Steps, MacroList), 
    NewM = M, 
    % format("Known Loop found for ", []), write(Item), format(" ~k ~k~n", [State, InDir]), write(MacroList), nl, 
    true.

loop_transition(M, State, Item, Number, InDir, NewM, _, Mult, OutItem, OutDir, Steps) :-
    \+ halt_state(State), 
    % format("Case 2~n", []), 
    M = machine(_, MacroList, _), 
    % \+ member(trans(State, Item, InDir, _NewState, _OutItem, _OutDir, _Steps), MacroList), 
    \+ loop_known(State, Item, InDir, _NewI, _Mult, _OutItem, _OutDir, _Steps, MacroList), 

    minimum_for_loop(Min), Number > Min, 
    maximum_for_loop(Max), 
    multiple_item(Item, NewItem, 1, Max, Mult),
    length(NewItem, Len), 
    number_of_states(M, Num), 
    B is truncate(Num * Len * 2**Len), % maxbound(B, Bound), 
    find_transition(M, State, NewItem, InDir, B, NewM, NewState, OutItem, OutDir, Steps),
    State == NewState, opposite_direction(InDir, OutDir), !,
    % format("Done Loop transition for ", []), write(Item), format(" ~k ~k~n", [State, InDir]), 
    true. 

loop_known(State, Item, InDir, NewI, Mult, OutItem, OutDir, Steps, MacroList) :-
    member(trans(State, NewI, InDir, State, OutItem, OutDir, Steps), MacroList),
    maximum_for_loop(Max), 
    multiple_item(Item, NewI, 1, Max, Mult).

minimum_for_loop(12). % minimum number of copies of item in original
maximum_for_loop(6). % maximum number of extra copies to try. 

multiple_item(Item, NewItem, SoFar, Max, SoFar) :-
    SoFar =< Max, 
    items(Item, SoFar, [], NewItem).

multiple_item(Item, NewItem, SoFar, Max, Mult) :-
    SoFar =< Max, 
    NewSoFar is SoFar + 1, 
    multiple_item(Item, NewItem, NewSoFar, Max, Mult). 

items(_I, 0, SoFar, SoFar).
items(I, N, SoFar, Item) :-
    N > 0, N1 is N - 1,
    append(SoFar, I, NewI),
    items(I, N1, NewI, Item).

expand_item_config(I, Number, NewI, Mult, config(Left, State, _Item, InDir, Right), config(NewLeft, State, NewItem, InDir, NewRight)) :-
    NewNumber is Number // Mult, 
    Extra is Number mod Mult, 
    NewItem = grp(NewI, NewNumber),
    add_extra(I, Extra, Left, Right, InDir, NewLeft, NewRight). 

add_extra(_I, 0, Left, Right, _InDir, Left, Right).
add_extra(I, Extra, Left, Right, l, Left, NewRight) :-
    Extra > 0,
    add_item(grp(I,Extra), Right, NewRight). 
add_extra(I, Extra, Left, Right, r, NewLeft, Right) :-
    Extra > 0,
    new_leftify(Left, NLeft),
    add_item(grp(I,Extra), NLeft, NLeft1),
    new_leftify(NLeft1, NewLeft). 

find_transition(M, State, Item, l, Bound, NewM, NewState, OutItem, OutDir, Steps) :-
    Item = [I|Rest], append(Rest, [right_end], NewRest), 
    % format("calling wombat left~n", []), ttyflush, 
    wild_wombat(config([left_end], State, I, l, NewRest), M, Bound, [pos(0)], 0, NewState, OutItem, OutDir, Steps),
    % format("wombat done~n", []), ttyflush, 
    M = machine(TransList, MacroList, List), 
    add(trans(State, Item, l, NewState, OutItem, OutDir, Steps), MacroList, NewMacroList),
    NewM = machine(TransList, NewMacroList, List). 

find_transition(M, State, Item, r, Bound, NewM, NewState, OutItem, OutDir, Steps) :-
    splitlast(Item, L1, [I]), reverse(L1, Left), !, append(Left, [left_end], NewLeft), 
    % format("Calling wombat right~n", []), display(NewLeft), display(I), nl, 
    wild_wombat(config(NewLeft, State, I, r, [right_end]), M, Bound, [pos(0)], 0, NewState, OutItem, OutDir, Steps),
    % format("wombat done~n", []), ttyflush, 
    M = machine(TransList, MacroList, List), 
    add(trans(State, Item, r, NewState, OutItem, OutDir, Steps), MacroList, NewMacroList),
    NewM = machine(TransList, NewMacroList, List). 

wild_wombat(config(Left, State, Item, _Dir, Right), _M, _Bound, _Inputs, Hops, NewState, OutItem, OutDir, Hops) :-
    halt_state(State), 	% format("Case 1~n", []), ttyflush, 
    NewState = State, 
    collect(Left, Item, Right, OutI), clean_tape(OutI, OutItem), 
    OutDir = r.

wild_wombat(config(Left, State, Item, Dir, Right), _M, Bound, _Inputs, Hops, loop, OutItem, Dir, Hops) :-
    \+ halt_state(State), 
    Hops >= Bound, 	% format("Case 2~n", []), ttyflush, 
    collect(Left, Item, Right, OutI), clean_tape(OutI, OutItem), 
    true. 

wild_wombat(config(Left, State, Item, Dir, Right), _M, Bound, _Inputs, Hops, State, OutItem, OutDir, Hops) :-
    \+ halt_state(State), 
    Hops < Bound,
    out_of_bounds(Left, Item, Right, Dir, OutItem, OutDir), % format("Case 3~n", []), ttyflush, 
    % This is normal termination. 
    true. 

wild_wombat(config(Left, State, Item, Dir, Right), M, Bound, Inputs, Hops, NewState, OutItem, OutDir, NewHops) :-
    \+ halt_state(State), 
    Hops < Bound,
    \+ out_of_bounds(Left, Item, Right, Dir, _, _), % format("Case 4~n", []), ttyflush, 
     simple_transition(M, State, Item, NState, NItem, NDir, Steps), % format("Case 4a~n", []), ttyflush, 
    updatetape(naive, Left, NItem, Right, NDir, NLeft, NewItem, NRight, _Moves), % format("Case 4b~n", []), ttyflush, 
    NewConfig = config(NLeft, NState, NewItem, NDir, NRight), 
    Hops1 is Hops + Steps, 
    wild_wombat(NewConfig, M, Bound, Inputs, Hops1, NewState, OutItem, OutDir, NewHops), 
    true. 
    
collect(Left, Item, Right, OutItem) :-
    append(Left, [Item], Temp), append(Temp, Right, OutItem). 

out_of_bounds([], left_end, Right, l, OutItem, l) :- clean_tape(Right, OutItem).
out_of_bounds(Left, right_end, [], r, OutItem, r) :- reverse(Left, New), clean_tape(New,OutItem). 

clean_tape([], []).
clean_tape([left_end|Rest], Result) :- clean_tape(Rest, Result). 
clean_tape([right_end|Rest], Result) :- clean_tape(Rest, Result). 
clean_tape([I|Rest], [I|Result]) :- I \== left_end, I\== right_end, clean_tape(Rest, Result). 

% otter_transition(machine([],[],[oo(config([grp([1,1,1],N)],a,grp([1,1,1],M), l, []),config([grp([1,1,1],N+M)], a, right, l, []), 9*M)]), config([grp([1,1,1],2)], a, grp([1,1,1],7), l, [grp([1,1,0],1)]), macro(3), NewConfig, OutDir, Leaps).

% Doesn't appear to be used now, but maintain for the moment. 
otter_transition(M, _Hops, Config, Mode, NewConfig, _OutDir, Leaps) :-
     M = machine(_,_,OtterList),
     % format("Machine~n", []), 
     Config = config(Left, State, Item, Dir, Right),
     % display(OtterList), nl, 

     copy_term(OtterList, NewOtterList), 
     % member(oo(config(NL, State, Item_Pattern, Dir, NR), config(NewL, State, OutItem_Pattern, NDir, NewR), Leaps1), NewOtterList),
     member_num(oo(config(NL, State, Item_Pattern, Dir, NR), config(NewL, State, OutItem_Pattern, NDir, NewR), Leaps1), NewOtterList, _Pattern_Number),
     copy_term(oo(config(NL, State, Item_Pattern, Dir, NR), config(NewL, State, OutItem_Pattern, NDir, NewR), Leaps1), _Pattern), 

     append(FirstLeft, RestLeft, Left),
     append(FirstRight, RestRight, Right),
     % format("Split~n", []), 
     Item = grp(I,Num),
     Item_Pattern = grp(I, Var), 
     Var = Num, 
     NL = FirstLeft,
     NR = FirstRight, 
     % format("Unified~n", []),  
     % display(NL), display(NR), display(Item_Pattern), nl, ttyflush, 
     % display(FirstLeft), display(FirstRight), display(Item), nl, ttyflush, 

     % format("NewL is ", []), display(NewL), nl, ttyflush, 
     % format("OutItem_Pattern is ", []), display(OutItem_Pattern), nl, ttyflush, 
     % format("NewR is ", []), display(NewR), nl, ttyflush, 
     % format("Leaps1 is ", []), display(Leaps1), nl, ttyflush, 
     eval_expressions(NewL, NewL1),
     eval_expressions(OutItem_Pattern, OutItem), 
     eval_expressions(NewR, NewR1),
     eval_expressions(Leaps1, Leaps), Leaps > 0, % Avoid pointless loops ...

     % format("Found ocelot transition at pattern number ~d~n", [Pattern_Number]), 

     % format("Evaluated~n", []), 
     append(NewL1, RestLeft, NL1),
     append(NewR1, RestRight, NR1),
     reconfigurate(Mode, config(NL1, State, OutItem, NDir, NR1), NewConfig), 
     % format("Reconfigurated~n", []), display_config(NewConfig), nl, 
     %NewConfig = config(NewLeft, State, NewItem, OutDir, NewRight),
     % format("From: ", []), display_config(Config), format(" To: ", []), display_config(NewConfig), nl,
     % format("General  Pattern: ", []), display_otters([Pattern]), 
     % format("Specific Pattern: ", []), display_otters([oo(config(NL, State, Item_Pattern, Dir, NR), config(NewL, State, OutItem_Pattern, NDir, NewR), Leaps1)]), 
     % format("Calculated: ", []), write(config(NewL1, State, OutItem, Dir, NewR1)), nl, 
     true. 

% For testing
otterlist([oo(config([grp([1,1,1],N)],a,grp([1,1,1],M), l, []),config([grp([1,1,1],N+M)], a, right, l, []), 9*M)]). 

% Revisit!
eval_expressions(grp(I, Exp), grp(I,Num)) :- Num is Exp, !. 
eval_expressions([], []) :- !. 
eval_expressions([I1|Rest], [NewI|Result]) :-
     eval_expressions(I1, NewI), !, 
     eval_expressions(Rest, Result).
eval_expressions(right,right) :- !. 
eval_expressions(left,left) :- !. 
eval_expressions(Exp, Val) :-
     Val is Exp. 

reconfigurate(_Mode, config(Left, State, Item, Dir, Right), config(Left, State, Item, Dir, Right)) :-
     Item = grp(I,Num), I \== [], integer(Num), Num > 0. 
reconfigurate(_Mode, config(Left, State, Item, Dir, Right), config(Left, State, Item, Dir, Right)) :-
     Item = grp(I,Num), I \== [], \+ integer(Num).

reconfigurate(Mode, config(Left, State, Item, l, Right), config(Left, State, NewItem, NewDir, NewRight)) :-
     Item = grp(I,Num), (I = []; (I \== [], (integer(Num), Num = 0);\+ integer(Num))), % format("Case1 ~n"i, []), 
     next_item(Mode, Right, NewItem, NewRight), % format("Case1 ~n", []), 
     NewDir = l. 
reconfigurate(Mode, config(Left, State, Item, r, Right), config(NewLeft, State, NewItem, NewDir, Right)) :-
     Item = grp(I,Num), (I = []; (I \== [], (integer(Num), Num = 0);\+ integer(Num))), % format("Case2 ~n", []), 
     next_item(Mode, Left, NewItem, NewLeft), % format("Case2 ~n", []), 
     NewDir = r. 
reconfigurate(Mode, config(Left, State, Item, _Dir, Right), config(Left, State, NewItem, NewDir, NewRight)) :-
     Item = right, 
     next_item(Mode, Right, NewItem, NewRight),
     NewDir = l. 
reconfigurate(Mode, config(Left, State, Item, _Dir, Right), config(NewLeft, State, NewItem, NewDir, Right)) :-
     Item = left, 
     next_item(Mode, Left, NewItem, NewLeft),
     NewDir = r. 

updatetape(Mode, Left, Item, Right, l, NewLeft, NewItem, NewRight, Move) :-
     append([Item], Right, NRight), check_blank(NRight, NewRight), 
     % display(Mode), display(Left), nl, 
     next_item(Mode, Left, NewItem, NLeft), 
     check_blank(NLeft, NewLeft), 
     Move is 0 - 1. 

updatetape(Mode, Left, Item, Right, r, NewLeft, NewItem, NewRight, 1) :-
     append([Item], Left, NLeft), check_blank(NLeft, NewLeft), 
     % display(Mode), display(Right), nl, 
     next_item(Mode, Right, NewItem, NRight),
     check_blank(NRight, NewRight), 
     true. 

check_blank(Tape, Tape) :- \+ all_blank(Tape). 
check_blank(Tape, []) :- all_blank(Tape). 

%% Need to update this for variables ... 
% updatetapemacro(config([grp([1], 1)], a, grp([0, 1], v(_G1390, 0, 10, 0, 10)), r, [grp([2], 1)]), flex, trans(a, [0, 1], r, a, [0, 0], r, 1), _G2515, _G2516, _G2517, _G2518, _G2519, _G2520) ?

updatetapemacro(Config, Mode, trans(State, I, Dir, NewState, OutI, OutDir, Steps), NewLeft, NewItem, NewDir, NewRight, Leaps, Moves) :-
     Config = config(Left, State, Item, Dir, Right), 
     Item = grp(I, Number), % integer(Number), %% will work for variables too 
     State == NewState, Dir = l, OutDir = r,  !, % Holkner case 1
     % format("Case 1~n", []), 
     add_item(grp(OutI, Number), Left, NewLeft),
     next_item(Mode, Right, NewItem, NewRight),
     NewDir = l,
     length(I, N), 
     (integer(Number) -> (Leaps is Steps * Number, Moves is N * Number); (Leaps is Steps, Moves is N) ), 
     true.

updatetapemacro(Config, Mode, trans(State, I, Dir, NewState, OutI, OutDir, Steps), NewLeft, NewItem, NewDir, NewRight, Leaps, Moves) :-
     Config = config(Left, State, Item, Dir, Right), 
     Item = grp(I, Number), % integer(Number), %% will work for variables too
     State == NewState, Dir = r, OutDir = l,  !, % Holkner case 2
     % format("Case 2~n", []), 
     add_item(grp(OutI, Number), Right, NewRight),
     % display(Mode), display(Left), nl, 
     next_item(Mode, Left, NewItem, NewLeft),
     NewDir = r,
     % format("Leaps ... ~n", []), 
     length(I, N), 
     (integer(Number) -> (Leaps is Steps * Number, Moves is 0 - N * Number); (Leaps is Steps, Moves is 0 - N) ),
     true. 

% add two extra cases here like the above for variables. % Should be okay given the way add_item works. 

updatetapemacro(Config, Mode, trans(State, I, Dir, _NewState, OutI, OutDir, Steps), NewLeft, NewItem, NewDir, NewRight, Leaps, Moves) :-
     Config = config(Left, State, Item, Dir, Right), 
     Item = grp(I, Number), %% (State \== NewState; (State == NewState, Dir == r)), 
     Number = 1, OutDir = r,  !, 
     % format("Case 3~n", []), % display(grp(OutI,Number)), display(Left), nl, 
     add_item(grp(OutI, Number), Left, NewLeft), 
     % format("Added~n", []), 
     next_item(Mode, Right, NewItem, NewRight),
     % format("Next~n", []), 
     NewDir = l,
     Leaps is Steps, 
     length(I, N), 
     set_moves(Dir, OutDir, N, Moves), 
     true. 

updatetapemacro(Config, Mode, trans(State, I, Dir, _NewState, OutI, OutDir, Steps), NewLeft, NewItem, NewDir, NewRight, Leaps, Moves) :-
     Config = config(Left, State, Item, Dir, Right), 
     Item = grp(I, Number), %% (State \== NewState; (State == NewState, Dir == l)), 
     Number = 1, OutDir = l,  !, 
     % format("Case 4~n", []), 
     add_item(grp(OutI, Number), Right, NewRight),
     % format("Added~n", []), 
     next_item(Mode, Left, NewItem, NewLeft),
     % format("Next~n", []), 
     NewDir = r,
     Leaps is Steps, 
     length(I, N), 
     set_moves(Dir, OutDir, N, Moves), 
     true. 

updatetapemacro(Config, Mode, trans(State, I, Dir, _NewState, OutI, OutDir, Steps), NewLeft, NewItem, NewDir, NewRight, Leaps, Moves) :-
     Config = config(Left, State, Item, Dir, Right), 
     Item = grp(I, Number),   ( (integer(Number), Number > 1) ; variable(Number) ),    
     Dir = r, OutDir = r, OutI == I, !, 
     % format("Case 5~n", []), 
     add_item(grp(I, Number), Left, NewLeft), 
     next_item(Mode, Right, NewItem, NewRight),  
     NewDir = l,
     Leaps is Steps, 
     Moves is 1. 

updatetapemacro(Config, Mode, trans(State, I, Dir, _NewState, OutI, OutDir, Steps), NewLeft, NewItem, NewDir, NewRight, Leaps, Moves) :-
     Config = config(Left, State, Item, Dir, Right), 
     Item = grp(I, Number),   ( (integer(Number), Number > 1) ; variable(Number)),  % format("Case 6~n", []), display(I), display(OutI), nl,  
     Dir = r, OutDir = r, OutI \== I, !, 
     % format("Case 6~n", []), 
     decrement_exponent(grp(I, Number), grp(I, N1)), % N1 is Number - 1, 
     add_item(grp(I, N1), Left, NLeft), 
     add_item(grp(OutI,1), NLeft, NewLeft), 
     next_item(Mode, Right, NewItem, NewRight),  
     NewDir = l, 
     Leaps is Steps,
     Moves is 1. 

updatetapemacro(Config, Mode, trans(State, I, Dir, _NewState, OutI, OutDir, Steps), NewLeft, NewItem, NewDir, NewRight, Leaps, Moves) :-
     Config = config(Left, State, Item, Dir, Right), 
     Item = grp(I, Number),  ( (integer(Number), Number > 1) ; variable(Number) ), 
     Dir = l, OutDir = l, OutI == I, !, 
     % format("Case 7~n", []), 
     add_item(grp(I, Number), Right, NewRight), 
     next_item(Mode, Left, NewItem, NewLeft),  
     NewDir = r,
     Leaps is Steps, 
     Moves is 0 - 1. 

updatetapemacro(Config, Mode, trans(State, I, Dir, _NewState, OutI, OutDir, Steps), NewLeft, NewItem, NewDir, NewRight, Leaps, Moves) :-
     Config = config(Left, State, Item, Dir, Right), 
     Item = grp(I, Number), ( (integer(Number), Number > 1) ; variable(Number)), 
     Dir = l, OutDir = l, OutI \== I, !, 
     % format("Case 8~n", []), 
     decrement_exponent(grp(I,Number), grp(I,N1)), %  N1 is Number - 1, 
     add_item(grp(I, N1), Right, NRight), 
     add_item(grp(OutI,1), NRight, NewRight), 
     next_item(Mode, Left, NewItem, NewLeft),  
     NewDir = r,
     Leaps is Steps, 
     Moves is 0 - 1. 

updatetapemacro(Config, _Mode, trans(State, I, Dir, NewState, OutI, OutDir, Steps), NewLeft, NewItem, NewDir, NewRight, Leaps, Moves) :-
     Config = config(Left, State, Item, Dir, Right), 
     Item = grp(I, Number), ( (integer(Number), Number > 1) ; variable(Number) ), 
     State \== NewState, Dir = l, OutDir = r, !, 
     % format("Case 9~n", []), 
     decrement_exponent(grp(I,Number), grp(I,N1)), % N1 is Number - 1, 
     NewItem = grp(I, N1), 
     add_item(grp(OutI,1), Left, NewLeft), 
     NewDir = l, 
     NewRight = Right, 
     Leaps is Steps, 
     length(I, N), 
     Moves is N.
      
updatetapemacro(Config, _Mode, trans(State, I, Dir, NewState, OutI, OutDir, Steps), NewLeft, NewItem, NewDir, NewRight, Leaps, Moves) :-
     Config = config(Left, State, Item, Dir, Right), 
     Item = grp(I, Number), ( (integer(Number), Number > 1) ; variable(Number) ), 
     State \== NewState, Dir = r, OutDir = l, !, 
     % format("Case 10~n", []), 
     decrement_exponent(grp(I,Number), grp(I,N1)), 
     NewItem = grp(I, N1), 
     add_item(grp(OutI,1), Right, NewRight), 
     NewDir = r,
     NewLeft = Left, 
     Leaps is Steps, 
     length(I, N), 
     Moves is 0 - N.

%% add cases analogous to 5,6,7,8,9,10 above here for variables. 

%% add_item(grp(I,N), List, NewList)
add_item(grp(I,_N), List, List) :- I == [].
add_item(grp(I,N), List, List) :- I \== [], integer(N), N == 0.
add_item(grp(I,N), [], [grp(I,N)]) :- I \== [], integer(N), N > 0.
add_item(grp(I,N), [], [grp(I,N)]) :- I \== [], variable(N).
add_item(grp(I1,N1), [grp(I2,N2)|Rest], [grp(I1,N3)|Rest]) :-
    I1 == I2, integer(N1), integer(N2), N3 is N1 + N2. 
add_item(grp(I1,N1), [grp(I2,N2)|Rest], [grp(I1,N3)|Rest]) :-
    I1 == I2, variable(N1), integer(N2), add_variable(N1, N2, N3). 
add_item(grp(I1,N1), [grp(I2,N2)|Rest], [grp(I1,N3)|Rest]) :-
    I1 == I2, integer(N1), variable(N2), add_variable(N2, N1, N3). 
add_item(grp(I1,N1), [grp(I2,N2)|Rest], Result) :-
    I1 == I2, variable(N1), variable(N2), 
    append([grp(I1,N1)], [grp(I2,N2)|Rest], Result). % Don't add variables, or at least not yet ... 
add_item(grp(I1,N1), [grp(I2,N2)|Rest], Result) :-
    \+ (I1 == I2), append([grp(I1,N1)], [grp(I2,N2)|Rest], Result). 
add_item(grp(I,N), [I2|Rest], Result) :-
    \+ (I2 = grp(_,_)), append([grp(I,N)], [I2|Rest], Result). 
%% could get fancier when variables are involved ... 

next_item(naive, [], Blank, []) :- blank_symbol(Blank).
next_item(naive, [I|Rest], I, Rest).

next_item(adapt, [], Blank, []) :- blank_symbol(Blank).
next_item(adapt, [I|Rest], I, Rest) :- I = grp(_Item, Num), Num > 0, I \== []. 
next_item(adapt, [I|Rest], NewItem, NewRest) :- I = grp(Item, Num), (Num is 0; (Num > 0, Item = [])), next_item(adapt, Rest, NewItem, NewRest). 
next_item(macro(K), [], grp(Blanks,1), []) :- blank_symbol(B), blanks(B, K, Blanks). 
next_item(macro(_K), [I|Rest], I, Rest) :- I = grp(_Item, Num), Num > 0, I \== []. 
next_item(macro(K), [I|Rest], NewItem, NewRest) :- I = grp(Item, Num), (Num is 0; (Num > 0, Item = [])), next_item(macro(K), Rest, NewItem, NewRest). 
next_item(flex, [], grp(Blanks,1), []) :- blank_symbol(B), blanks(B, 1, Blanks). 
next_item(flex, [I|Rest], I, Rest) :- I = grp(_Item, Num), integer(Num), Num > 0, I \== []. 
next_item(flex, [I|Rest], NewItem, NewRest) :- I = grp(Item, Num), integer(Num), (Num is 0; (Num > 0, Item = [])), next_item(flex, Rest, NewItem, NewRest). 
next_item(flex, [I|Rest], I, Rest) :- I = grp(_Item, Num), variable(Num).

next_item(search, [], grp(Blanks,1), []) :- blank_symbol(B), blanks(B, 1, Blanks). 
next_item(search, [I|Rest], I, Rest) :- I = grp(_Item, Num), integer(Num), Num > 0, I \== []. 
next_item(search, [I|Rest], NewItem, NewRest) :- I = grp(Item, Num), integer(Num), (Num is 0; (Num > 0, Item = [])), next_item(search, Rest, NewItem, NewRest). 
next_item(search, [I|Rest], I, Rest) :- I = grp(_Item, Num), variable(Num).

blanks(_, 0, []). 
blanks(Blank, N, [Blank|Result]) :- N > 0, N1 is N - 1, blanks(Blank, N1, Result). 

set_moves(l, r, N, N).
set_moves(r, l, N, M) :- M is 0 - N. 
set_moves(r, r, _N, 1). 
set_moves(l, l, _N, M) :- M is 0 - 1. 

splitlast(T, T1, T2) :- append(T1, T2, T), length(T2, 1). 

% updateinputs(Config, Mode, Hops, OutDir, 1, naive, Inputs, NewConfig, NewHops, NewInputs), 

updateinputs(_Config, Mode, Hops, Dir, Moves, Used, Inputs, NewConfig, _NewHops, NewInputs) :-
     % format("Updating history~n", []), % display(Inputs), nl, ttyflush,  
     update_history(Hops, Used, Inputs, NewConfig, Inputs1), 
     % format("Updating pos~n", []), % display(Inputs1), nl,   ttyflush,  
     update_pos(Mode, Inputs1, Dir, Moves, Inputs2), 
     % format("Updating steps~n", []), display(Inputs2), nl,   ttyflush,  
     update_steps(Inputs2, Inputs3), 
     NewInputs = Inputs3, 
     % display(NewInputs), nl, 
     true.

update_history(Hops, Used, Inputs, NewConfig, NewInputs) :-
     % format("History~n", []), % writeln(Inputs), 
     member(history(History), Inputs), 
     member(pos(Current), Inputs), 
     member(now(Now), Inputs),
     % format("Type ...~n", []), 
     set_type(Inputs, Type), 
     % (member(trie(K), Inputs) -> Type = trie(K); (member(newtrie(K,L), Inputs) -> Type = newtrie(K,L); Type = list)),
     % append([s(Hops,Now,Current)], History, NewHist), % history update
     Now = config(_, State, _, Dir, _), % Item = grp(I,_), % format("Adding ~k ~k ", [State, Dir]), write(I), format(" ", []), write(s(Hops,Now,Current)), nl, 
     % (Hops = 904 -> (format("Adding ~k ~k ", [State, Dir]), write(I), format(" ", []), write(s(Hops,Now,Current)), nl); true), 
     % format("Index~n", []), 
     history_index(Type, Now, Index), % format("State is ~k, Dir is ~k, Index is ", [State, Dir]), writeln(Index), 
     % display_history(0, History), writeln(History), 
     % format("Adding~n", []), 
     add_to_history(Type, State, Dir, Index, s(Hops,Now,Current,Used), History, NewHistory), !, % history update
     % display_history(0, NewHistory), writeln(NewHistory), 
     % (Hops = 904 -> display_history(0, NewHistory); true), % format("Added~n", []), 
     % trim_to_size(NewHist, NewHistory), % history update
     % format("Added~n", []), 
     delete(Inputs, history(History), Inps), 
     delete(Inps, now(Now), Is), 
     append(Is, [now(NewConfig),history(NewHistory)], NewInputs), !. 

update_history(_Hops, _Used, Inputs, _NewConfig, Inputs) :-
     \+ (member(history(_History), Inputs), member(now(_Now), Inputs)), 
     true. 

set_type(Inputs, trie(K)) :- member(trie(K), Inputs). 
set_type(Inputs, newtrie(K,L)) :- member(newtrie(K,L), Inputs), \+ member(trie(_), Inputs). 
set_type(Inputs, list(K)) :- member(list(K), Inputs), \+ member(newtrie(_,_), Inputs), \+ member(trie(_), Inputs). 
set_type(Inputs, list) :- \+ member(list(_), Inputs), \+ member(newtrie(_,_), Inputs), \+ member(trie(_), Inputs). 

history_memory(list, 300). 
history_memory(list(N), N). % New mode to allow per case list. 
history_memory(trie(N), N). % Experiment with this value - was originally 10. 
history_memory(newtrie(N,_), N). % Experiment with this value - was originally 10. 

initial_history(list, _, _, []).
initial_history(list(_), _, _, []).
initial_history(trie(_), States, Directions, History) :-
    empty_dir_list(Directions, DList), 
    empty_state_list(States, DList, History).
initial_history(newtrie(_,_), States, Directions, History) :-
    empty_dir_list(Directions, DList), 
    empty_state_list(States, DList, History).

empty_dir_list(2, [tr(l,[]),tr(r,[])]). % Only do two for now.

empty_state_list(2, DList, [tr(a,DList),tr(b,DList)]). 
empty_state_list(3, DList, [tr(a,DList),tr(b,DList),tr(c,DList)]). 
empty_state_list(4, DList, [tr(a,DList),tr(b,DList),tr(c,DList),tr(d,DList)]). 
empty_state_list(5, DList, [tr(a,DList),tr(b,DList),tr(c,DList),tr(d,DList),tr(e,DList)]). 
empty_state_list(6, DList, [tr(a,DList),tr(b,DList),tr(c,DList),tr(d,DList),tr(e,DList),tr(f,DList)]). 
empty_state_list(7, DList, [tr(a,DList),tr(b,DList),tr(c,DList),tr(d,DList),tr(e,DList),tr(f,DList),tr(g,DList)]). 
empty_state_list(8, DList, [tr(a,DList),tr(b,DList),tr(c,DList),tr(d,DList),tr(e,DList),tr(f,DList),tr(g,DList),tr(h,DList)]). 

% Trie structure is ... [tr(a,A),tr(b,B),tr(c,C),tr(d,D),tr(e,E)]
% A is [tr(l,Left),tr(r,Right)]
% Left is [tr(0,Zero),tr(1,One),tr(2,Two)]

history_index(list(_),  _, []) :- !. 
history_index(list,  _, []) :- !. 
history_index(trie(_),  Config, I) :-
	Config = config(_, _, Item, _, _), Item = grp(I,_), !. 
history_index(newtrie(_,L), Config, Index) :-
	Config = config(Left, _, Item, _, Right), Item = grp(I,_), 
% 	shape_limit(Limit), 
	shapelist(L, 0, Left, [], LS), !, 
	shapelist(L, 0, Right, [], RS), !, 
	append(I, LS, Temp), append(Temp, RS, Index), !. 

% shape_limit(5). 

shapelist(_, _, [], SoFar, SoFar) :- !. 
shapelist(Limit, Length, _, SoFar, SoFar) :- Length >= Limit, !. 
shapelist(Limit, Length, [grp(I,_)|Rest],SoFar, Result) :- Length < Limit, !, append(SoFar, I, NewSoFar), length(I, N), NewLength is Length + N, shapelist(Limit, NewLength, Rest, NewSoFar, Result).


%%lookup_history(Type, State, Dir, Index, s(Hops1, Config1, _, _), History), less_hops(Hops1, Hops), % Hops1 < Hops, %% history lookup

lookup_history(list,    _, _, _, s(Hops, Config, Pos, Used), History) :- member(s(Hops, Config, Pos, Used), History). % For history as a list. 
lookup_history(list(_), _, _, _, s(Hops, Config, Pos, Used), History) :- member(s(Hops, Config, Pos, Used), History). % For history as a list. 
lookup_history(trie(_), State, Dir, Item, Step, History) :- % For history as a trie.
     % member(Type, [newtrie(_,_),trie(_)]),
     member(tr(State, SList), History), !, % History is of the form [tr(a,A),tr(b,B),...]		 
     member(tr(Dir, DList), SList), !,  % SList is of the form [tr(l,L),tr(r,R)]	
     itemlist(Item, Step, DList), % DList is of the form [tr(0,Zero),tr(1,One),...]					
     true. 
lookup_history(newtrie(_,_), State, Dir, Item, Step, History) :- % For history as a trie.
     % member(Type, [newtrie(_,_),trie(_)]),
     member(tr(State, SList), History), !, % History is of the form [tr(a,A),tr(b,B),...]		 
     member(tr(Dir, DList), SList), !,  % SList is of the form [tr(l,L),tr(r,R)]	
     itemlist(Item, Step, DList), % DList is of the form [tr(0,Zero),tr(1,One),...]					
     true. 

add_to_history(list, _, _, _, s(Hops,Now,Current,Used), History, NewHistory) :- 
     append([s(Hops,Now,Current,Used)], History, NewHist), !, 
     trim_to_size(list, NewHist, NewHistory), true. % history update.
add_to_history(list(K), _, _, _, s(Hops,Now,Current,Used), History, NewHistory) :- 
     append([s(Hops,Now,Current,Used)], History, NewHist), !, 
     trim_to_size(list(K), NewHist, NewHistory), true. % history update.
add_to_history(Type, State, Dir, Item, Step, History, NewHistory) :- % For history as a trie.
     member(Type, [newtrie(_,_), trie(_)]), 
     member(tr(State, SList), History), !, % History is of the form [tr(a,A),tr(b,B),...]		 
     member(tr(Dir, DList), SList), !,  % SList is of the form [tr(l,L),tr(r,R)]
     % format("Adding ", []), write(Item), nl, ttyflush, 				
     add_to_itemlist(Type, Item, Step, DList, NewDList), !, % DList is of the form [tr(0,Zero),tr(1,One),...]
     delete(SList, tr(Dir, DList), SListTemp), append([tr(Dir,NewDList)], SListTemp, NewSList), 
     delete(History, tr(State, SList), HistTemp), append([tr(State, NewSList)], HistTemp, NewHistory),!, 
     true. 

itemlist([], Step, List) :- extract_step(Step, List). 
itemlist([I|Rest], Step, List) :- member(tr(I, IList), List), !, itemlist(Rest, Step, IList). 
itemlist([I|_Rest], Step, List) :- \+ member(tr(I, _IList), List), !, extract_step(Step, List). 

add_to_itemlist(trie(K), [], Step, List, NewIList) :- 
	append([Step], List, New), !, trim_to_size(trie(K), New, NewIList), true. 
add_to_itemlist(trie(K), [I|Rest], Step, List, NewList) :- 
	member(tr(I, IList), List), !, 
	add_to_itemlist(trie(K), Rest, Step, IList, NewIList),
	delete(List, tr(I, IList), ListTemp), append([tr(I,NewIList)], ListTemp, NewList). 
add_to_itemlist(trie(_), [I|_Rest], Step, List, NewList) :- 
	\+ member(tr(I, _IList), List), !, append([tr(I,[Step])], List, NewList). 
add_to_itemlist(newtrie(K,L), [], Step, List, NewIList) :- 
	append([Step], List, New), !, trim_to_size(newtrie(K,L), New, NewIList), true. 
add_to_itemlist(newtrie(K,L), [I|Rest], Step, List, NewList) :- 
	member(tr(I, IList), List), !, % format("Adding ~k~n", [I]), ttyflush, 				
	add_to_itemlist(newtrie(K,L), Rest, Step, IList, NewIList),
	delete(List, tr(I, IList), ListTemp), append([tr(I,NewIList)], ListTemp, NewList). 
add_to_itemlist(newtrie(K,L), [I|Rest], Step, List, NewList) :- 
	\+ member(tr(I, _IList), List), !, % format("Adding new ~k~n", [I]), ttyflush, 				
	add_to_itemlist(newtrie(K,L), Rest, Step, [], TList), !, append([tr(I,TList)], List, NewList). 

extract_step(Step, [Step|_List]) :- Step = s(_,_,_,_).
extract_step(Step, [Step1|_List]) :- Step1 = tr(_, Rest), extract_step(Step, Rest). 
extract_step(Step, [_|List]) :- extract_step(Step, List). 

trim_to_size(Type, History, History) :- length(History, Len), history_memory(Type, Size), Len =< Size, !. 
trim_to_size(Type, History, Trimmed) :- length(History, Len), history_memory(Type, Size), Len > Size, !, append(Trimmed, _, History), length(Trimmed, Size). 

% Update this??
display_history(_, []). 
display_history(N, [s(Hops, Config, Pos)|Rest]) :- 
      output_blanks(N), 
      format("~d: ", [Hops]), display_config(Config), format(" Pos: ~d~n", [Pos]), 
      display_history(N, Rest).
display_history(N, [s(Hops, Config, Pos, Used)|Rest]) :- 
      output_blanks(N), 
      format("~d: ", [Hops]), display_config(Config), format(" Pos: ~d    Used: ~k~n", [Pos,Used]), 
      display_history(N, Rest).
display_history(N, [tr(I, List)|Rest]) :- 
      N1 is N+1, output_blanks(N), 
      format("~k: ~n", [I]), 
      display_history(N1, List), display_history(N, Rest).

output_blanks(0).
output_blanks(N) :- N > 0, format("   ", []), N1 is N-1, output_blanks(N1). 

update_steps(Inputs, NewInputs) :-
      member(steps(S), Inputs), 
      delete(Inputs, steps(S), Inputs1), 
      S1 is S + 1,
      append([steps(S1)], Inputs1, NewInputs). 
update_steps(Inputs, Inputs) :-
      \+ member(steps(_S), Inputs). 

update_otters(Leaps, ExtraSteps, Nested, Inputs, NewInputs) :-
     member(otters(Otters), Inputs), NewOtters is Otters + 1, 
     member(ottersnested(OttersNested), Inputs), NewOttersNested is OttersNested + Nested, 
     member(ottersteps(OtterSteps), Inputs), NewOtterSteps is OtterSteps + Leaps, 
     member(otterjumps(OtterJumps), Inputs), NewOtterJumps is OtterJumps + Leaps + ExtraSteps, 

     delete(Inputs, otters(Otters), Inputs1), 
     delete(Inputs1, ottersnested(OttersNested), Inputs2), 
     delete(Inputs2, ottersteps(OtterSteps), Inputs3), 
     delete(Inputs3, otterjumps(OtterJumps), Inputs4), 
     append([otters(NewOtters),ottersnested(NewOttersNested),ottersteps(NewOtterSteps),otterjumps(NewOtterJumps)], Inputs4, NewInputs).
update_otters(_,_,_, Inputs, Inputs) :-
     \+ member(otters(_Otters), Inputs). 
update_otters(_,_,_, Inputs, Inputs) :-
     \+ member(ottersnested(_OttersNested), Inputs). 
update_otters(_,_,_, Inputs, Inputs) :-
     \+ member(ottersteps(_OtterSteps), Inputs). 
update_otters(_,_,_, Inputs, Inputs) :-
     \+ member(otterjumps(_OtterJumps), Inputs). 

update_ocelots(Leaps, Inputs, NewInputs) :-
     member(ocelots(Ocelots), Inputs), NewOcelots is Ocelots + 1, 
     member(ocelotsteps(OcelotSteps), Inputs), NewOcelotSteps is OcelotSteps + Leaps, 
     delete(Inputs, ocelots(Ocelots), Inputs1), 
     delete(Inputs1, ocelotsteps(OcelotSteps), Inputs2), 
     append([ocelots(NewOcelots),ocelotsteps(NewOcelotSteps)], Inputs2, NewInputs).
update_ocelots(Inputs, Inputs) :-
     \+ member(ocelots(_Ocelots), Inputs). 
update_ocelots(Inputs, Inputs) :-
     \+ member(ocelotsteps(_OcelotSteps), Inputs). 

update_pos(Mode, Inputs, _Dir, Num, Inputs1) :-
      \+ member(Mode, [naive]), 
      member(pos(Current), Inputs), delete(Inputs, pos(Current), Is),
      % set_new_current(Current, Dir, Num, NewCurrent),
      NewCurrent is Current + Num, 
      append([pos(NewCurrent)], Is, Inputs1). 
update_pos(Mode, Inputs, Dir, _Num, Inputs1) :-
      member(Mode, [naive]), 
      member(pos(Current), Inputs), delete(Inputs, pos(Current), Is),
      % set_new_current(Current, Dir, Num, NewCurrent),
      set_new_current(Current, Dir, 1, NewCurrent), 
      append([pos(NewCurrent)], Is, Inputs1). 
update_pos(Inputs, _Dir, _Num, Inputs) :-
      \+ member(pos(_Current), Inputs).

update_machine(M, Pattern, NewM) :-
    M = machine(Trans, Macro, Ocelots), 
    append([Pattern], Ocelots, NewOcelots),
    NewM = machine(Trans, Macro, NewOcelots). 

set_new_current(Current, l, Leap, NewCurrent) :- NewCurrent is Current - Leap.
set_new_current(Current, r, Leap, NewCurrent) :- NewCurrent is Current + Leap.

% output_status(Config, Mode, 0, Inputs1, NewInputs, init),!, 

output_status(M, Config, Mode, Hops, Inputs, NewInputs, Used) :-
      yes_to_output(Config, Hops, Inputs, NewInputs), !, % format("% Yes!~n", []), 
      % write(NewInputs), nl, write(Config), nl, 
      output_config(M, Config, Mode, Hops, NewInputs, Used), nl, ttyflush, 
      true, !. 
	    
output_status(_M, Config, _Mode, Hops, Inputs, Inputs, _Used) :-
      \+ yes_to_output(Config, Hops, Inputs, _NewInputs),
      true, !. 

yes_to_output(_Config, _Hops, Inputs, Inputs) :-
      member(trace, Inputs),!.
yes_to_output(Config, _Hops, Inputs, Inputs) :-
      member(watch(State), Inputs),
      Config = config(_Left, State, _Item, _Dir, _Right), !. 
yes_to_output(Config, _Hops, Inputs, Inputs) :-
      member(watch(State), Inputs),
      % Config = config2d(State, Index, Map, Symbol, Direction),
      (Config = config2d(State, _Index, _Map, _Symbol, _Direction); Config = config2d(State, _Index, _Map, _Symbol)), !. 
yes_to_output(Config, _Hops, Inputs, Inputs) :-
      member(watch(State, Item), Inputs),
      Config = config(_Left, State, Item, _Dir, _Right), !. 
yes_to_output(Config, _Hops, Inputs, Inputs) :-
      member(watch(State, Item), Inputs),
      (Config = config2d(State, _Index, _Map, Item, _Direction); Config = config2d(State, _Index, _Map, Item)), !. 
yes_to_output(Config, _Hops, Inputs, Inputs) :-
      member(match(Pattern), Inputs),
      match_config(Pattern, Config), !. 
yes_to_output(_Config, Hops, Inputs, Inputs) :-
      member(trace(Number), Inputs),
      Hops >= Number, !.
yes_to_output(Config, _Hops, Inputs, Inputs) :-
      member(rend, Inputs),
      Config = config(_Left, _State, _Item, _Dir, []), !. 
yes_to_output(Config, _Hops, Inputs, Inputs) :-
      member(lend, Inputs),
      Config = config([], _State, _Item, _Dir, _Right), !. 
yes_to_output(_Config, Hops, Inputs, NewInputs) :-
      member(over(Number), Inputs), 
      Hops >= Number, !,
      delete(Inputs, over(Number), Inputs1),
      member(every(Every), Inputs1), 
      NewOver is Number + Every,
      append([over(NewOver)], Inputs1, NewInputs).  

match_config(Pattern, Config) :- 
      \+ \+ (Pattern = Config), !. % Being pedantic to avoid bindings. 
 
output_config(M, Config, Mode, Hops, Inputs, Used) :-
      member(flatout, Inputs), % format("Flat out ... drinking lizards!~n", []), ttyflush, 
      flatten(Config, FlatConfig), 
      output_config1(FlatConfig, Mode, Hops, Inputs, Used), output_nonzeroes(M, FlatConfig), 
      true.
output_config(_M, Config, Mode, Hops, Inputs, Used) :-
      \+ member(flatout, Inputs), % format("No drinking lizards!~n", []), ttyflush, 
      output_config1(Config, Mode, Hops, Inputs, Used),
      true.

output_config1(Config, Mode, Hops, Inputs, Used) :-
      Config = config(Left, State, Item, Dir, Right), !, 
      count_ones(Config, Ones), % format("Splong 1!~n",[]),  ttyflush, 
      member(pos(Pos), Inputs), % format("Splong 2!~n",[]),  ttyflush, 
      prettyprint(State, Left, Item, Dir, Pos, Mode, Right, Hops, Ones, Used), !.

output_config1(Config, _Mode, Hops, _Inputs, _Used) :-
      Config = config2d(State, Index, Map, Symbol, Direction), !, 
      printmap(Map),
      Index = i(X,Y), 
      format("~d: ~k (~d,~d) ~k ~k~n", [Hops, State, X, Y, Symbol, Direction]).

output_config1(Config, _Mode, Hops, _Inputs, _Used) :-
      Config = config2d(State, Index, Map, Symbol), !, 
      printmap(Map),
      Index = i(X,Y), 
      format("~d: ~k (~d,~d) ~k~n", [Hops, State, X, Y, Symbol]).

output_nonzeroes(M, Config) :-
     count_nonzeroes(M, Config, Profile), format("	Profile ", []), 
     output_nonzeroes1(Profile), 
     true. 

output_nonzeroes1([]).
output_nonzeroes1([count(I,Num)|Rest]) :- format("#~d: ~d ", [I, Num]), output_nonzeroes1(Rest). 

count_nonzeroes(M,config(Left, _State, Item, _Dir, Right), Profile) :-
     number_of_symbols(M, N), 
     initialise_counts(N, Counts0), 
     count_nonzeroes1(N, Left, Counts0, Counts1), 
     count_nonzeroes1(N, [Item], Counts1, Counts2), 
     count_nonzeroes1(N, Right, Counts2, Counts3), 
     Profile = Counts3,
     true. 

count_nonzeroes1(_, [], Counts, Counts).
count_nonzeroes1(N, [Item|Rest], Counts, NewCounts) :-
      is_blank(Item), !, 
      count_nonzeroes1(N, Rest, Counts, NewCounts).
count_nonzeroes1(N, [Item|Rest], Counts, NewCounts) :-
      is_input(Item), 
      count_item(Item, Counts, Counts1), 
      count_nonzeroes1(N, Rest, Counts1, NewCounts),
      true. 
count_nonzeroes1(N, [grp(I,Num)|Rest], Counts, NewCounts) :-
      initialise_counts(N, Initial),
      count_nonzeroes1(N, I, Initial, Count1), 
      multiply_counts(Num, Count1, Count2), 
      add_counts(Counts, Count2, Counts3), 
      count_nonzeroes1(N, Rest, Counts3, NewCounts),
      true. 

count_item(Item, Counts, NewCounts) :-
      member(count(Item, Count), Counts),
      delete(Counts, count(Item, Count), Counts1),
      NewCount is Count + 1,
      append([count(Item, NewCount)], Counts1, NewCounts),
      true. 

multiply_counts(_N, [], []).
multiply_counts(N, [count(I,Num)|Rest], [count(I,NewNum)|Result]) :-
      NewNum is N*Num,
      multiply_counts(N, Rest, Result). 

add_counts([], Counts, Counts). 
add_counts([count(I,Num)|Rest], Counts, NewCounts) :-
      add_counts1(I, Num, Counts, Counts1),
      add_counts(Rest, Counts1, NewCounts). 

add_counts1(I, Num, Counts, NewCounts) :-
      member(count(I,N), Counts),
      delete(Counts, count(I,N), Counts2),
      NewN is N+Num, 
      append([count(I,NewN)], Counts2, NewCounts). 

initialise_counts(2, [count(0,0),count(1,0)]).
initialise_counts(N, Counts) :-
      N > 2, N1 is N-1,
      initialise_counts(N1, Counts1),
      append(Counts1, [count(N1,0)], Counts). 

display_config(config(Left, State, Item, Dir, Right)) :-
     % leftify(Left, RevLeft), 
     reverse(Left, RevLeft), 
     pprint(RevLeft), format("{~k}", [State]), pprint([Item]), format("{~k}", [Dir]), pprint(Right), true. 

new_leftify(Tape, Left) :-
	reverse(Tape, Rev),
	reverse_items(Rev, Temp),
	reverse(Temp, Left). 

reverse_items([], []).
reverse_items([Item|Rest], [Item|Result]) :-
	is_input(Item), reverse_items(Rest, Result).
reverse_items([Item|Rest], [grp(RevI,Number)|Result]) :-
	Item = grp(I,Number), reverse(I, RevI),
	reverse_items(Rest, Result).

display_trans([]).
display_trans([Trans|Rest]) :-
      Trans = trans(State, In, InDir, NewState, Out, OutDir, Steps),
      format("Trans: ~k ", [State]),
      display_string(In), 
      format(" ~k -> ~k ", [InDir,NewState]),
      display_string(Out), format(" ~k ~d~n", [OutDir,Steps]),
      display_trans(Rest). 

display_loops([]).
display_loops([Trans|Rest]) :-
      Trans = trans(State, In, InDir, NewState, Out, OutDir, Steps),
      ( is_loop(Trans) -> ( format("Loop: ~k ", [State]), display_string(In), format(" ~k -> ~k ", [InDir,NewState]), display_string(Out), format(" ~k ~d~n", [OutDir,Steps])); true ), 
      display_loops(Rest). 

is_loop(trans(State, _In, InDir, NewState, _Out, OutDir, _Steps)) :-
	State == NewState, ((InDir = l, OutDir = r); (InDir = r, OutDir = l)). 

display_otters([]).
display_otters([Otter|Rest]) :-
       copy_term(Otter, TempOtter), 
       TempOtter = oo(InitConfig, FinalConfig, Leaps), 
       format("From: ", []), display_config(InitConfig), 
       format(" To: ", []),  display_config(FinalConfig), 
       display_leaps(Leaps), nl, 
       display_otters(Rest). 

display_leaps(Leaps) :-
       integer(Leaps), format(" in ~d steps.~n", [Leaps]).  
display_leaps(Leaps) :-
       \+ integer(Leaps), format(" in ", []), display(Leaps), format(" steps.~n", []). 

display_string([]).
display_string([A|Rest]) :-
       display(A), display_string(Rest).

count_ones(config(Left, _State, Item, _Dir, Right), Ones) :-
      count_ones1(Left, C1), count_ones1([Item], C2), count_ones1(Right, C3),
      Ones is C1 + C2 + C3. 
count_ones1([], 0).
count_ones1([Item|Rest], Count) :-
      is_blank(Item), !, 
      count_ones1(Rest, Count).
count_ones1([Item|Rest], Count) :-
      is_input(Item), 
      count_ones1(Rest, Count1),
      Count is Count1 + 1. 
count_ones1([grp(I,N)|Rest], Count) :-
      integer(N),
      count_ones1(I, C), 
      count_ones1(Rest, Count1),
      Count is Count1 + N*C. 
count_ones1([grp(_I,N)|Rest], Count1) :-
      \+ integer(N), 
      count_ones1(Rest, Count1).

prettyprint(State, Left, Item, Dir, Pos, Mode, Right, Hops, Ones, Used) :-
	length(Left,L), setblanks(Pos, Mode, L, Blanks), 
	reverse(Left, PL), % invert(PL, PPL), 
	leftprint(Mode, Blanks, PL, State, Item, Dir, Right), 
	(integer(Hops) -> format(" Hops: ~d Ones: ~d Pos: ~d ", [Hops,Ones,Pos]); (write(Hops), format(" Ones: ~d Pos: ~d Used: ~k ", [Ones, Pos, Used])) ), 
	true.

setblanks(Pos, Type, L, Blanks) :-
	member(Type, [naive]), 
	padding(Pad), 
	Blanks is Pad + Pos - L.
setblanks(_Pos, Type, _L, 0) :-
	\+ member(Type, [naive]).

leftprint(_, Blanks, _PL, _State, _Item, _, Right) :-
	Blanks < 0, format("{too long on the left} ", []), pprint(Right).
leftprint(naive, Blanks, PL, State, Item, _, Right) :- 
	Blanks >= 0, nblanks(Blanks), pprint(PL), format("{~k}",[State]), pprint([Item]), pprint(Right).
leftprint(Mode, Blanks, PL, State, Item, Dir, Right) :- 
        member(Mode, [macro(_K), adapt, flex, search]), 
	Blanks >= 0, nblanks(Blanks), pprint(PL), format("{~k(",[State]), pprint([Item]), format(")~k}", [Dir]), pprint(Right).

padding(10). 
nblanks(N) :- N < 0, !, format("No space! ", []).
nblanks(0) :- !.
nblanks(N) :- N > 0, !, format(" ", []), N1 is N - 1, nblanks(N1). 

pprint([]). 
pprint([0|Rest]) :- !, format("0", []), pprint(Rest).
pprint([1|Rest]) :- !, format("1", []), pprint(Rest).
pprint([2|Rest]) :- !, format("2", []), pprint(Rest).
pprint([3|Rest]) :- !, format("3", []), pprint(Rest).
pprint([4|Rest]) :- !, format("4", []), pprint(Rest).
pprint([5|Rest]) :- !, format("5", []), pprint(Rest).
pprint([6|Rest]) :- !, format("6", []), pprint(Rest).
pprint([7|Rest]) :- !, format("7", []), pprint(Rest).

pprint([grp(T,C)|Rest]) :-
 	var(C), 
 	T = [_|_], !,
 	format("{",[]), 
 	pchars(T),
	format("}^(",[]), ttyflush, display(C), format(")", []), 
	pprint(Rest). 
pprint([grp(T,C)|Rest]) :-
 	% var(C), 
        nonvar(C), 
 	C = v(_V,Min,_,_,_), integer(Min), 
 	T = [_|_], !,
 	format("{",[]), 
 	pchars(T), 
	% format("}^(~k)",[C]), 
	% format("}^(~k)",[V]), 
	format("}^_[~d]",[Min]), 
	pprint(Rest). 
pprint([grp(T,C)|Rest]) :-
 	% var(C), 
        nonvar(C), 
 	C = *, 
 	T = [_|_], !,
 	format("{",[]), 
 	pchars(T), 
	% format("}^(~k)",[C]), 
	% format("}^(~k)",[V]), 
	format("}*",[]), 
	pprint(Rest). 
pprint([grp(T,C)|Rest]) :-
	% var(C), 
        nonvar(C), 
	C = v(_V,Min,_,_,_), \+ integer(Min), % var(Min), 
	T = [_|_], !,
	format("{",[]), 
	pchars(T), 
	% format("}^(~k)",[C]), 
	% format("}^(~k)",[V]), 
	format("}^_[~k]",[Min]), 
	pprint(Rest). 
pprint([grp(T,C)|Rest]) :-
        \+ integer(C), \+ (C = v(_V,_,_,_,_)),
        format("{",[]), 
	pchars(T), 
	format("}^_[", []),
        display(C),
        format("]",[]),
        pprint(Rest). 
pprint([grp(T,C)|Rest]) :-
	T = [_|_], % T is a list
	integer(C), 
	C > 1, !, 
	format("{",[]), 
	pchars(T), ttyflush, 
	print_exponent(C), !, 
	pprint(Rest). 
pprint([grp(T,C)|Rest]) :-
	T = [_|_], % T is a list
	integer(C),  
	C = 1, !, 
	pchars(T), 
	pprint(Rest). 
pprint([grp(T,C)|Rest]) :-
	T = [_|_], % T is a list
	integer(C), 
	C = 0, !, 
	pprint(Rest). 

pprint([grp(T,C,Visit)|Rest]) :-
 	% var(C), 
 	C = v(_V,Min,_,_,_), integer(Min), 
 	T = [_|_], !,
 	format("{",[]), 
 	pchars(T), 
	% format("}^(~k)",[C]), 
	% format("}^(~k)",[V]), 
	format("}^_[~d]{~d}",[Min,Visit]), 
	pprint(Rest). 
pprint([grp(T,C,Visit)|Rest]) :-
	% var(C), 
	C = v(_V,Min,_,_,_), var(Min), 
	T = [_|_], !,
	format("{",[]), 
	pchars(T), 
	% format("}^(~k)",[C]), 
	% format("}^(~k)",[V]), 
	format("}^_[~k]{~d}",[Min,Visit]), 
	pprint(Rest). 
pprint([grp(T,C,Visit)|Rest]) :-
	T = [_|_], % T is a list
	integer(C), 
	C > 1, !, 
	format("{",[]), 
	pchars(T), 
	format("}^(~d){~d}",[C,Visit]), 
	pprint(Rest). 
pprint([grp(T,C,Visit)|Rest]) :-
	T = [_|_], % T is a list
	integer(C), 
	C = 1, !, 
	pchars(T), format("{~d}", [Visit]), 
	pprint(Rest). 
pprint([grp(T,C,_Visit)|Rest]) :-
	T = [_|_], % T is a list
	integer(C), 
	C = 0, !, 
	pprint(Rest). 

print_exponent(N) :- max_print(Max), N =< Max, format("}^(~d)",[N]).
% print_exponent(C) :- max_print(Max), C > Max, Y is log(C)/log(10), X is round(Y + 0.5), format("}^(digits(~d))",[X]).
print_exponent(N) :- max_print(Max), N > Max, big_number_of_digits(N,  Number), format("}^(digits(~d))",[Number]), !.

print_bignum(N) :- print_bignum1(external, N).

print_bignum1(_,N) :- max_print(Max), N =< Max, format("~d", [N]), !. 
print_bignum1(external, N) :- max_print(Max), N > Max, !, big_number_of_digits(N, Number), format("(~d digits)", [Number]).
print_bignum1(internal, N) :- max_print(Max), N > Max, !, big_number_of_digits(N, Number), format("digits(~d)", [Number]).

max_print(999999999999999).

big_number_of_digits(N, M) :-
      X is 10 ** 80000, N >= X, 
      Number1 is N // X,
      number_of_digits(Number1, 80001, M). 

big_number_of_digits(N, M) :-
      X is 10 ** 60000, N >= X, 
      Y is 10 ** 80000, N < Y, !, 
      Number1 is N // X,
      number_of_digits(Number1, 60001, M). 

big_number_of_digits(N, M) :-
      X is 10 ** 40000, N >= X, 
      Y is 10 ** 60000, N < Y, !, 
      Number1 is N // X,
      number_of_digits(Number1, 40001, M). 

big_number_of_digits(N, M) :-
      X is 10 ** 20000, N >= X, 
      Y is 10 ** 40000, N < Y, !, 
      Number1 is N // X,
      number_of_digits(Number1, 20001, M). 

big_number_of_digits(N, M) :-
      X is 10 ** 20000, N < X, !,
      number_of_digits(N, 1, M). 

number_of_digits(N, M, M) :-
      N >= 0, N < 10.
number_of_digits(N, M, Number) :-
      N >= 10, 
      NewN is N // 10, 
      NewM is M + 1, 
      number_of_digits(NewN, NewM, Number). 
number_of_digits(N, M, Number) :-
      N < 0, !, 
      NewN is 0 - N,
      number_of_digits(NewN, M, Number).

pchars([]). 
pchars([0|Rest]) :- !, format("0",[]), pchars(Rest). 
pchars([1|Rest]) :- !, format("1",[]), pchars(Rest). 
pchars([2|Rest]) :- !, format("2",[]), pchars(Rest). 
pchars([3|Rest]) :- !, format("3",[]), pchars(Rest). 
pchars([4|Rest]) :- !, format("4",[]), pchars(Rest). 
pchars([5|Rest]) :- !, format("5",[]), pchars(Rest). 
pchars([6|Rest]) :- !, format("6",[]), pchars(Rest). 
pchars([7|Rest]) :- !, format("7",[]), pchars(Rest). 

printmap( map(Row0,Row1,Row2,Row3,Row4,Row5,Row6,Row7,Row8,Row9,Row10)) :- 
        print_row(Row0), 
        print_row(Row1), 
        print_row(Row2), 
        print_row(Row3), 
        print_row(Row4), 
        print_row(Row5), 
        print_row(Row6), 
        print_row(Row7), 
        print_row(Row8), 
        print_row(Row9), 
        print_row(Row10), !. 

print_row(row(_, [S0,S1,S2,S3,S4,S5,S6,S7,S8,S9,S10])) :- format("~k  ~k  ~k  ~k  ~k  ~k  ~k  ~k  ~k  ~k  ~k~n", [S0,S1,S2,S3,S4,S5,S6,S7,S8,S9,S10]). 

% Machine language predicates. 

blank_symbol(0). % default
initial_state(a). % default
halt_state(z). % default. 
looping_state(loop). % default. 

% Book-keeping
% v(Name, Min, Max?, Init?, ??)
decrement_exponent(grp(I,Number), grp(I,NewNumber)) :-
	integer(Number), Number > 1, NewNumber is Number - 1.
decrement_exponent(grp(I,Number), grp(I,NewNumber)) :-
	variable(Number), decrement_variable(Number, NewNumber).

% variable(v(Name, Coefficient, Sum, Minimum)). This is Coefficient * X + Sum. The minimum value is Minimum. 
new_variable(Name, v(Name, 1,0,0)). 
variable(v(_,_,_,_)). % Internal representation of variables for compress adapt form.
value(v(_,C,S,_Min), Value) :- Value is 100*C + S. %% Need to work out what to do here ... 
decrement_variable(Var, NewVar) :- subtract_variable(Var, 1, NewVar). 
subtract_variable(v(Name, C,S,M), N, v(Name, C, NewS,M)) :- NewS is S - N. % Do we update M here? 
increment_variable(Var, NewVar) :- add_variable(Var, 1, NewVar). 
add_variable(v(Name,C,S,M), N, v(Name,C,NewS,M)) :- NewS is S + N.
multiply_variable(v(Name,C,S,M), N, v(Name,NewC,NewS,M)) :- NewC is C*N, NewS is S*N.
assign_variable(v(_Name,C,S,_M), Value, NewValue) :- NewValue is C*Value + S. % Do we check minimum value here? 
get_name(v(N,_C,_S,_M), N).
get_coefficient(v(_,C,_S,_M), C).
get_sum(v(_,_C,S,_M), S).
get_minimum(v(_,_C,_S,M), M).
get_initial(v(_,_C,_S,M), M).  % ???? Make sure this is right ... 
set_minimum(v(Name,C,S,_), NewMin, v(Name,C,S,NewMin)).
add_to_minimum(v(Name,C,S,M), N, v(Name,C,S,NewMin)) :- NewMin is M + N.

var_compute(v(Name,C,S,M), m(K,L), v(Name,NewC, NewS,M)) :- NewC is K*C, NewS is K*S + L. 

minimum_compress_size(6). 

input([grp(In,_)|_], In) :- !. 
input([In|_], In) :- is_input(In), !. 

is_state(a).
is_state(b).
is_state(c).
is_state(d).
is_state(e).
is_state(f).
is_state(g).
is_state(h).
is_input(0).
is_input(1).
is_input(2).
is_input(3).
is_input(4).
is_input(5).
is_input(6).
is_input(7).

is_tape([]).
is_tape([I|Rest]) :- is_input(I), is_tape(Rest). 

blanks(I, []) :- blank_symbol(I). 
blanks(K, [I|Rest]) :- blank_symbol(I), K > 0, K1 is K-1, blanks(K1, Rest).

number_of_states(machine(M, _, _), N) :-
       states(M, Ss), length(Ss, N). 
number_of_states(M, N) :-
       M \== machine(_,_,_),
       states(M, Ss), length(Ss, N). 

states(M, States) :- states1(M, [], States). 
states1([], States, States).
states1([t(S,_,_,_,_)|Rest], StatesSoFar, States) :-
	add(S, StatesSoFar, NewSoFar),
	states1(Rest, NewSoFar, States).

number_of_states_used(machine(M, _, _), N) :-
       states_used(M, Ss), length(Ss, N). 
number_of_states_used(M, N) :-
       M \== machine(_,_,_),
       states_used(M, Ss), length(Ss, N). 

number_of_symbols_used(machine(M, _, _), N) :-
       symbols_used(M, Ss), length(Ss, N). 
number_of_symbols_used(M, N) :-
       M \== machine(_,_,_),
       symbols_used(M, Ss), length(Ss, N). 

states_used(M, States) :- states_used1(M, [], States). 
states_used1([], States, States).
states_used1([t(S,_,_,_,NS)|Rest], StatesSoFar, States) :-
	add(S, StatesSoFar, NewSoFar1),
	add(NS, NewSoFar1, NewSoFar2),
	states_used1(Rest, NewSoFar2, States).

symbols_used(M, Symbols) :- symbols_used1(M, [], Symbols). 
symbols_used1([], Symbols, Symbols).
symbols_used1([t(_,S1,S2,_,_)|Rest], SymbolsSoFar, Symbols) :-
	add(S1, SymbolsSoFar, NewSoFar1),
	add(S2, NewSoFar1, NewSoFar2),
	symbols_used1(Rest, NewSoFar2, Symbols).

add(Item, List, List) :-
	member(Item, List). 
add(Item, List, NewList) :-
	\+ member(Item, List), append(List, [Item], NewList). 

number_of_symbols(machine(M, _, _), N) :-
       symbols(M, Ss), length(Ss, N). 
number_of_symbols(M, N) :-
       M \== machine(_,_,_),
       symbols(M, Ss), length(Ss, N). 

symbols(M, Symbols) :- symbols1(M, [], Symbols). 
symbols1([], Symbols, Symbols).
symbols1([t(_,I,O,_,_)|Rest], SymbolsSoFar, Symbols) :-
	add(I, SymbolsSoFar, NewSoFar1),
	add(O, NewSoFar1, NewSoFar2),
        symbols1(Rest, NewSoFar2, Symbols). 

number_of_dirs(machine(M,_,_),N) :- number_of_dirs1(M,N).
number_of_dirs(M,N) :- M \== machine(_,_,_), number_of_dirs1(M,N). 

number_of_dirs1(M,2) :- up_dir(UpDir), down_dir(DownDir), \+ member(t(_,_,_,UpDir,_), M), \+ member(t(_,_,_,DownDir,_), M),!.
number_of_dirs1(M,3) :- up_dir(UpDir), down_dir(DownDir), member(t(_,_,_,UpDir,_), M), \+ member(t(_,_,_,DownDir,_), M),!.
number_of_dirs1(M,4) :- down_dir(DownDir), member(t(_,_,_,DownDir,_), M),!.

% number_of_dirs(M, N) :- number_of_dirs1(M, N), N > 1.
% number_of_dirs(M, 2) :- number_of_dirs1(M, N), N =< 1.
% 
% number_of_dirs1(machine(M, _, _), N) :-
%        num_dirs(M, Ss), length(Ss, N). 
% number_of_dirs1(M, N) :-
%        M \== machine(_,_,_),
%       num_dirs(M, Ss), length(Ss, N). 
% 
% num_dirs(M, Symbols) :- dirs1(M, [], Symbols). 
% dirs1([], Dirs, Dirs).
% dirs1([t(_,_,_,Dir,_)|Rest], DirsSoFar, Dirs) :-
%	add(Dir, DirsSoFar, NewSoFar),
%        dirs1(Rest, NewSoFar, Dirs). 

bound_max(1000000). 
maxbound(B, B) :-  bound_max(Bound), B =< Bound, !. 
maxbound(B, Bound) :- bound_max(Bound), B > Bound, !. %% Do not run for more than this many steps looking for a transition! May need to change this value ... 

% Removes Item from List leaving NewList.
% Fails if Item is not in List. 
remove(Item, List, NewList) :- member(Item, List), delete(List, Item, NewList). 

% There is a path in machine M of length N from S to NS
path(S,NS,N,M,[t(S,I,O,D,NS)]) :-
      N is 1, remove(t(S,I,O,D,NS), M, _RestM). 
path(S,NS,N,M,[t(S,I,O,D,S1)|Path]) :-
      N > 1, remove(t(S,I,O,D,S1), M, RestM), 
      N1 is N - 1, 
      path(S1,NS,N1,RestM,Path).
      
% There is a simple path in machine M of length N from S to NS.
% This means that S does not appear in the interal part of the path. 
simple_path(S,NS,N,M,Path) :- simple_path1(S, S,NS,N,M,Path).
simple_path1(_Source, S,NS,N,M,[t(S,I,O,D,NS)]) :-
      N is 1, remove(t(S,I,O,D,NS), M, _RestM). 
simple_path1(Source, S,NS,N,M,[t(S,I,O,D,S1)|Path]) :-
      N > 1, remove(t(S,I,O,D,S1), M, RestM), 
      N1 is N - 1, 
      Source \== S1, 
      simple_path1(Source,S1,NS,N1,RestM,Path).

% There is a cycle in machine M of length N from S to S
cycle(S,N,M,Path) :- path(S,S,N,M,Path). 

% There is a path in machine M of length somewhere between 1 and size(M) from S to NS
some_path(S,NS,M,Path) :-
     dimension(M,Size), 
     between(1,Size,N),
     path(S,NS,N,M,Path).

% There is a simple path in machine M of length somewhere between 1 and size(M) from S to NS
some_simple_path(S,NS,M,Path) :-
     dimension(M,Size), 
     between(1,Size,N),
     simple_path(S,NS,N,M,Path).

% Size is the size of M. One day this will include direction as well. 
dimension(M, Size) :-
     number_of_states(M,States), 
     number_of_symbols(M,Symbols), 
     Size is States * Symbols, !. 
     
% % M is between Lower and Upper inclusive.
% There is a built-in predicate for this.
% between(Lower,Upper,M) :- Upper >= Lower, M is Lower. 
% between(Lower,Upper,M) :- Upper >= Lower, L1 is Lower + 1, between(L1, Upper, M).

% member_num(X, List, N)
% X is the Nth member of List. Fails if X is not a member of List. 
member_num(X, List, N) :- member_num0(X, 1, List, N).  

member_num0(X, NumSoFar, [X|_], NumSoFar). 
member_num0(X, NumSoFar, [Y|Rest], N) :-
      X \== Y,
      NewNumSoFar is NumSoFar + 1, 
      member_num0(X, NewNumSoFar, Rest, N). 

%%% Measure size to depth ratio of configuration. Only compress if this is too low.

compress(ConFig, NewConFig) :-
        depth_config(ConFig, Depth),
        size_config(ConFig, Size),
        max_power_config(ConFig, Max), 
        compress_or_not(ConFig, Size, Depth, Max, NewConFig).

compress_or_not(ConFig, Size, Depth, Max, ConFig) :-
        ignore_compress(ConFig, Size, Depth, Max), !. 
compress_or_not(ConFig, _Size, _Depth, _Max, NewConFig) :-
        % \+ ignore_compress(ConFig, Size, Depth, Max),
        % format("Compressing ... ", []), write(ConFig), nl, 
        new_compress_config(ConFig, NewConFig),
	% format("Compressed~n", []),
	true. 

ignore_compress(_ConFig, _Size, Depth, Max) :- Max > 10, Depth < 20. 
% ignore_compress(ConFig, Size, Depth, Max) :- Max =< 10, Size / Depth < 3. %% Need to play with this
%        Max > 10, Depth < 10. 

% [grp([1],1), grp([0,0],1), grp([1],1), grp([0,0],1), grp([1],1), grp([0,0],1), grp([1],1), grp([0,0],1), grp([1],1), grp([0,0],1), grp([1],1), grp([0,0],1), grp([1],1), grp([1,1],1)]

% %ignore_compress(config(Left, _, _Item, _, Right),  Size, Depth, Max) :-
% %	Max > 100. 
% ignore_compress(config(_Left, _, _Item, _, _Right),  _Size, Depth, Max) :-
%         % Size / Depth < 3. %% Need to play with this
%         Max > 20, Depth < 8, true. % incompatible(Left), incompatible(Right). 

% ignore_compress(config(_Left, _, _Item, _, _Right), _Size, Depth, Max) :-  Max > 5, Depth < 30. 
% ignore_compress(config(_Left, _, _Item, _, _Right), _Size, Depth, _Max) :-  Depth < 8.

% incompatible(Tape) :-
%         elements(Tape, [], Els), 
%	minimise_elements(Els, [], Mins),
%	contains_duplicates(Mins).

% elements([], Elements, Elements). 
% elements([grp(I,_)|Rest], SoFar, Elements) :-
%         append(SoFar, [I], NewSoFar),
% 	elements(Rest, NewSoFar, Elements).

% minimise_elements([], Mins, Mins). 
% minimise_elements([I|Rest], SoFar, Mins) :-
%         squash(I, _, IMin),
% 	append(SoFar, [IMin], NewSoFar),
% 	minimise_elements(Rest, NewSoFar, Mins).

% contains_duplicates(List) :-
%         delete_one(X, [], List, NewList), member(X, NewList), !. 

% % delete_one(X, SoFar, [], SoFar). 
% delete_one(X, SoFar, [X|Rest], Result) :- 
%         append(SoFar, Rest, Result). 
% delete_one(X, SoFar, [Y|Rest], Result) :-
%         append(SoFar, [Y], NewSoFar),
%         delete_one(X, NewSoFar, Rest, Result).

max_power_config(config(Left, _State, Item, _Dir, Right), Max) :-
        max_config(Left, 0, Max1), 
	max_config([Item], Max1, Max2), 
	max_config(Right, Max2, Max). 

max_config([], Max, Max).
max_config([I|Rest], SoFar, Max) :-
        is_input(I), 
	maximum(1, SoFar, NewSoFar),
	max_config(Rest, NewSoFar, Max).
max_config([grp(_I,Number)|Rest], SoFar, Max) :-
	maximum(Number, SoFar, NewSoFar),
	max_config(Rest, NewSoFar, Max).

depth_config(config(Left, _State, _Item, _Dir, Right), Depth) :-
        length(Left, L1),
        length(Right, L2),
        Depth is L1 + 1 + L2. % 1 is for Item ...

length_config(config(Left, _State, Item, _Dir, Right), Length) :-
	length_tape(Left, Length1), 
	length_tape([Item], Length2), 
	length_tape(Right, Length3), 
	Length = Length1 + Length2 + Length3.

length_tape([],0).
length_tape([Item|Rest], Result) :-
        length_item(Item, Length),
        length_tape(Rest, Tape_Length),
        Result is Length + Tape_Length.

length_item(I, 1) :- is_input(I).
length_item(grp(I,Num), Length) :-
        integer(Num),
        length(I, Length). 

size_config(config(Left, _State, Item, _Dir, Right), Size) :-
        size_tape(Left, Size1),
        size_tape([Item], Size2),
        size_tape(Right, Size3),
        Size is Size1 + Size2 + Size3.

size_tape([], 0).
size_tape([Item|Rest], Result) :-
        size_item(Item, Size),
        size_tape(Rest, Tape_Size),
        Result is Size + Tape_Size.

size_item(I, 1) :- is_input(I).
size_item(grp(I,Num), Size) :-
        integer(Num),
        length(I, S), Size is Num*S.
% size_item(grp(I,Num), Size) :-
%       variable(Num),
%         length(I, S), Size is Num*S.

%% Compression should work like this. First 'Squash', so that (11)^40 becomes 1^80 etc. Then look to combine neighbours. No -- test first to see if compression is necessary ... NO --- ewhat about things like [grp([1],3000), grp([0,1],1), grp([0,1],1),grp([0,1],1)]?? Need to check each element of the list ... 

new_compress_config(config(Left, State, Item, l, Right), config(NewLeft, State, NewItem, l, NewRight)) :-
 
       new_leftify(Left, NLeft), 
       compresstape(NLeft, NLeft2),
       new_leftify(NLeft2, NewLeft), 

       compresstape([Item|Right], NRight),!, 
       append([NewItem], NewRight, NRight). 

new_compress_config(config(Left, State, Item, r, Right), config(NewLeft, State, NewItem, r, NewRight)) :-

       new_leftify([Item|Left], NLeft), 
       compresstape(NLeft, NLeft2),
       new_leftify(NLeft2, NLeft1), 
       append([NewItem], NewLeft, NLeft1), 

       compresstape(Right, NewRight), !. 

compresstape(Tape, NewTape) :-
	% squash_tape(Tape, Tape1), !, % format("Squashed ", []), write(Tape), format(" to ", []), write(Tape1), nl, 
	% squish_tape(Tape1, Tape2), !, % format("Squished ", []), write(Tape1), format(" to ", []), write(Tape2), nl, 
	
	squish_tape(Tape, Tape1), !, % format("Squished ", []), write(Tape), format(" to ", []), write(Tape1), nl, 
        squash_tape(Tape1, Tape2), !, % format("Squashed ", []), write(Tape1), format(" to ", []), write(Tape2), nl, 
	merge_tape(Tape2, Tape3), !, 
        NewTape = Tape3, 
	true. 

merge_tape(Tape, Tape) :- length(Tape, N), N < 2, !. 
merge_tape([Item|Rest], Result) :-
        length([Item|Rest], N), N >= 2, 
	Item = grp(I,N1),
	Rest = [Item2|Rest2],
	Item2 = grp(I,N2), integer(N1), integer(N2), !, 
	NewN is N1+N2, 
	merge_tape([grp(I,NewN)|Rest2], Result). 
merge_tape([Item|Rest], [Item|Result]) :-
        length([Item|Rest], N), N > 1, 
	Item = grp(I,N1),
	Rest = [Item2|Rest2],
	( Item2 \== grp(I,_); ( Item2 = grp(I,N2), \+ ( integer(N1), integer(N2) ) ) ), !, 
	merge_tape([Item2|Rest2], Result). 

squash_tape([], []) :- !. 
squash_tape([Item|Rest], [NewItem|Result]) :-
	squash_item(Item, NewItem), !, 
        squash_tape(Rest, Result). 

squash_item(grp(I,Num), grp(L, NewNum)) :-
        integer(Num), 
	squash(I, K, L), !, 
        NewNum is K*Num. 
squash_item(grp(I,Num), grp(I, Num)) :-
	\+ (integer(Num), squash(I, _K, _L)).

% squash(List, K, NewList)
% Can squash List into K copies of NewList. So squash([1,1,1], 3, [1]) and squash([0,1,0,1], 2, [0,1]) both hold. 
 
squash(List, K, NewList) :-
      length(List, N), 
      N > 1, % can't squash anything smaller
      sublists(N, NList), member(M, NList),
      all_sublists_same(List, M, NewList), 
      K is N // M, !. 

all_sublists_same(List, M, One) :-
      split(List, M, [One|Rest]), 
      all_same(One, Rest), 
      true.

split(List, M, [List]) :-
      length(List, N), N =< M, !. 
split(List, M, [First|Lists]) :-
      length(List, N), N > M,
      append(First, Rest, List), length(First, M),
      split(Rest, M, Lists). 

all_same(One, [One]) :- !. 
all_same(One, Rest) :-
	length(Rest, N), N > 1,
	Rest = [First|Others],
        One == First,
	all_same(One, Others).

% sublists(N,M)
% For a list of length N, consider only sublists of length M
sublists(2,[1]).
sublists(3,[1]).
sublists(4,[1,2]).
sublists(5,[1]).
sublists(6,[1,2,3]).
sublists(7,[1]).
sublists(8,[1,2,4]).
sublists(9,[1,3]).
sublists(10,[1,2,5]).
sublists(11,[1]).
sublists(12,[1,2,3,4,6]).
sublists(13,[1]).
sublists(14,[1,2,7]).
sublists(15,[1,3,5]).
sublists(16,[1,2,4,8]).
sublists(17,[1]).
sublists(18,[1,2,3,6,9]).
sublists(19,[1]).
sublists(20,[1,2,4,5,10]).
sublists(21,[1,3,7]).
sublists(22,[1,2,11]).
sublists(23,[1]).
sublists(24,[1,2,3,4,6,8,12]).
sublists(25,[1,5]).
sublists(26,[1,2,13]).
sublists(27,[1,3,9]).
sublists(28,[1,2,4,7,14]).
sublists(29,[1]).
sublists(30,[1,2,3,5,6,10,15]).

squish_tape([], []) :- !. 
squish_tape(Tape, Tape) :- length(Tape, 1), Tape = [grp(I,N)], integer(N), I \== [], N > 0, !. 
squish_tape(Tape, Tape) :- length(Tape, 1), Tape = [grp(I,N)], variable(N), I \== [], !. 
squish_tape(Tape, Result) :- Tape = [grp([],_N)|Rest], squish_tape(Rest, Result), !. 
squish_tape(Tape, Result) :- Tape = [grp(_I,0)|Rest],  squish_tape(Rest, Result), !.

squish_tape(Tape, NewTape) :- 
	length(Tape, N), N > 1,
        Tape = [Item|Rest],
        Item = grp(_I,Number), variable(Number), 
        % No such pattern because of the variable, so give up and move on ... 
	squish_tape(Rest, NewSquish), 
        append([Item], NewSquish, NewTape), !, 
	true. 

% T = [grp([0],2),grp([1],1),grp([0],2),grp([1],1),grp([0],1),grp([0,1,0],112),grp([0],1),grp([1],2)], squish_tape(T,T2).
squish_tape(Tape, NewTape) :- 
	length(Tape, N), N > 1,
	dominants(Tape, [], Dominants), Dominants \== [], 
	% format("Squishing to dominants ...", []), writeln(Dominants), 
        squish_to_dominants(Dominants, Tape, NewTape). 

% squish_tape(Tape, NewTape) :- 
% 	length(Tape, N), N > 1,
%   
%  	% If there is a dominant item (eg grp([1], 3853)) then use that as the pattern ...
% 	dominant_item(Item, Tape), Item = grp(I,Number), integer(Number), 
% 
% 	length(I, Size), 
% 	% format("Trying dominant size ~d...~n", [Size]), 
% 	next_items(Size, Tape, I2, Rest), I2 == I, !, % So this is looking good ... 
%         % format("List1 is ", []), write(List1), format(" Rest1 is ", []), write(Rest1), format(" Rest2 is ", []), write(Rest2), nl, 
% 	squish_to_pattern(grp(I,1), Rest, I, grp(I, NewN), NewRest), %% What about variables??
%         % format("Squishing .. ", []), write(NewRest), nl, ttyflush, 
% 	squish_tape(NewRest, NewSquish), !, 
%         append([grp(I,NewN)], NewSquish, NewTape), !, 
% 	true. 

squish_tape(Tape, NewTape) :- 
	length(Tape, N), N > 1,
        Tape = [Item|_Rest],
        Item = grp(_I,Number), integer(Number), \+ dominant_item(_, Tape), 

        % Find appropriate pattern, if any ...   %% Sort out this case for variables ... 
	pattern_size(Size),
	% format("Trying ~d~n", [Size]), 
	next_items(Size, Tape, List1, Rest1),  % format("List1 is ", []), write(List1), %%% Perhaps make this three patterns before compressing ??? Yes!
	next_items(Size, Rest1, List2, Rest2), % format(" List2 is ", []), write(List2), nl, 
	next_items(Size, Rest2, List3, _Rest3), % format(" List3 is ", []), write(List3), nl, 
	List1 == List2, List2 == List3, !, 
        % format("Size is ~d ", [Size]), format("List1 is ", []), write(List1), format(" Rest1 is ", []), write(Rest1), format(" Rest2 is ", []), write(Rest2), nl, 
	squish_to_pattern(grp(List1,0), Rest2, List1, grp(List1, Extra), NewRest), %% What about variables??
        % format("Squishing .. ", []), write(NewRest), nl, ttyflush, 
	squish_tape(NewRest, NewSquish), !, 
        NewN is Extra + 2, % 2 for the initial pair List1 and List2
        append([grp(List1,NewN)], NewSquish, NewTape), !, 
	true. 

squish_tape(Tape, NewTape) :- 
	length(Tape, N), N > 1,
        Tape = [Item|Rest],
        % Item = grp(I,Number), integer(Number), I \== [], Number > 0, 
        % Number < 3, 
        % Time to give up and move on ... 
        % format("Moving on to squish ", []), writeln(Rest), 
	squish_tape(Rest, NewSquish), 
        append([Item], NewSquish, NewTape), !, 
	true. 

squish_to_dominants(_, [], []) :- !. 
squish_to_dominants([], Tape, Tape) :- !. 
squish_to_dominants(Dominants, Tape, NewTape) :- 
        Dominants = [I|RestDoms], 
	length(I, Size), 
	next_items(Size, Tape, I2, Rest1), I2 == I, !, % So this is looking good ... 
	squish_to_pattern(grp(I,1), Rest1, I, grp(I, NewN), NewRest), %% What about variables??
	squish_to_dominants(RestDoms, NewRest, NewSquish), !, 
	append([grp(I,NewN)], NewSquish, NewTape), !, 
	true. 
squish_to_dominants(Dominants, Tape, NewTape2) :- 
        Dominants = [I|RestDoms], 
	length(I, Size), 
	next_items(Size, Tape, I2, _Rest1), I2 \== I, !, % So no pattern here, but lets keep looking ...
	next_items(1, Tape, I2, RestTape), 
	squish_to_dominants(Dominants, RestTape, NewRest),
	add_item(grp(I2,1), NewRest, NewTape1), 
	squish_to_dominants(RestDoms, NewTape1, NewTape2), !, 
	true. 

pattern_size(N) :- between(1,30,N). % May need more? 20367 in 3x3 needs 24 .. 
% pattern_size(N) :- member(N,[30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1]). % May need more? 
%% Compress this! 
% config([grp([2],1),grp([0],1),grp([1],1),grp([2],8),grp([0],1),grp([1],2)],a,grp([1],1),r,[grp([2],10),grp([0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2],12),grp([0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],1),grp([2],10),grp([1],1)])

dominants([], SoFar, SoFar). 
dominants(Tape, SoFar, List) :-
        Tape = [grp(I,Num)|Rest], ((integer(Num), Num > 20); variable(Num)), 
	append(SoFar, [I], NewSoFar),
	dominants(Rest, NewSoFar, List).
dominants(Tape, SoFar, List) :-
        Tape = [grp(_I,Num)|Rest], integer(Num), \+ (Num > 20),
	dominants(Rest, SoFar, List).

dominant_item(Item, Tape) :-
	member(Item, Tape), Item = grp(_I, Number), Number > 20. % Experiment with this value ... 

% Tape can be compressed using Pattern, giving Item followed by Rest
squish_to_pattern(grp(Pattern,Number), Tape, Pattern, Item, Rest) :-
	Tape = [grp(Pattern, N)|RestTape], integer(N), 
 	N1 is Number + N, !, 
	squish_to_pattern(grp(Pattern,N1), RestTape, Pattern, Item, Rest). 

squish_to_pattern(grp(Pattern,Number), Tape, Pattern, Item, Rest) :-
	Tape \= [grp(Pattern, _)|Rest], 
	length(Pattern, N), 
        next_items(N, Tape, List, NewTape), 
	List == Pattern, % keep going
	N1 is Number + 1, !, 
	squish_to_pattern(grp(Pattern,N1), NewTape, Pattern, Item, Rest). 

squish_to_pattern(SoFar, Tape, _Pattern, SoFar, Tape) :- !. % time to stop, including when there is a variable (and hence next_items fails ... 

% next_items(N, Tape, First, Rest).
% First is the first N items in Tape, Rest is the rest.
%% What happens with variables?

% T = [grp([0],2),grp([1],1),grp([0],2),grp([1],1),grp([0],1),grp([0,1,0],112),grp([0],1),grp([1],2)], next_items(1, T, I, Rest).
% I = [0],
% Rest = [grp([], 1), grp([0], 1), grp([1], 1), grp([0], 2), grp([1], 1), grp([0], 1), grp([0|...], 112), grp([...], 1), grp(..., ...)] 

next_items(_, [], [], []).
next_items(N, Tape, List, Rest) :-
	Tape = [grp(_I,Number)|Rest1], integer(Number), Number == 0, 
	next_items(N, Rest1, List, Rest), !. 
next_items(N, Tape, List, Rest) :-
	Tape = [grp(I,Number)|Rest1], integer(Number), length(I,L), Number > 0, 
	N =< L, !, 
	append(I1, I2, I), length(I1, N), 
	List = I1, N1 is Number-1,
	add_item(grp(I,N1), Rest1, T1),
	add_item(grp(I2,1), T1, T2),
	Rest = T2, !. 
next_items(N, Tape, List, Rest) :-
	Tape = [grp(I,Number)|Rest1], integer(Number), length(I,L), Number > 0, 
	N > L, !, NewN is N - L, N1 is Number-1,
	add_item(grp(I,N1), Rest1, T1),!, 
	next_items(NewN, T1, List2, Rest2),
	append(I, List2, List), 
	Rest = Rest2. 

old_next_items(_N, [], [], []) :- !. 
old_next_items(N, Tape, List, Rest) :-
	Tape = [grp(I,Number)|Rest1], integer(Number), 
	length(I,L), N =< L*Number, 
 	N == 1, !, 
	extract(0, 1, I, Number, List, Others),
	append(Others, Rest1, Rest). 

old_next_items(N, Tape, List, Rest) :-
	Tape = [grp(I,Number)|Rest1], integer(Number), 
	length(I,L), N =< L*Number, 
	N > 1, !, 
	N1 is N // L,
	N2 is N mod L,	% format("Extracting with ~d ~d ", [N1, N2]), write(I), format(" ~d~n", [Number]), ttyflush, 
     	extract(N1, N2, I, Number, List, Others),
	% format("Extracted~n", []), ttyflush, 
	append(Others, Rest1, Rest).

old_next_items(N, Tape, List, Rest) :-
	Tape = [grp(I,Number)|Rest1], integer(Number), 
	length(I,L), N > L*Number, 
	N1 is N - L*Number, !, 
        % format("Calling next with ~d ", [N1]), write(Rest1), nl, ttyflush, 
	old_next_items(N1, Rest1, List1, Rest),
	flatten_tape(right, [grp(I,Number)], List0), 
	append(List0, List1, List).

extract(N1, N2, I, Number, List, Rest) :-
	N1 == 0,
	N2 > 0,
	Number == 1, !, 
	append(I1, I2, I), length(I1, N2),
	List = I1, 
	add_item(grp(I2,1), [], Rest).
% Check this case --- extract(0,1,[0], 2, [0], [grp([0],1)]). 
extract(N1, N2, I, Number, List, Rest) :-
	N1 == 0,
	N2 >  0,
	Number > 1, !, 
	append(I1, I2, I), length(I1, N2),
	List = I1, 
	N3 is Number - 1,
	append([grp(I2,1)], [grp(I,N3)], Rest).
extract(N1, N2, I, Number, List, Rest) :-
	N1 > 0,
	N2 == 0, !, % N1 =< Number
	flatten_tape(right, [grp(I,N1)], List), 
	N3 is Number - N1,
	add_item(grp(I,N3), [], Rest).
extract(N1, N2, I, Number, List, Rest) :-
	N1 > 0,
	N2 > 0,
	Number is N1 + 1, !, 
	flatten_tape(right, [grp(I,N1)], List1), 
	append(I1, I2, I), length(I1, N2),
	append(List1, I1, List), 
	Rest = [grp(I2,1)].
extract(N1, N2, I, Number, List, Rest) :-
	N1 > 0,
	N2 > 0,
	Number > N1 + 1, !, 
	flatten_tape(right, [grp(I,N1)], List1), 
	append(I1, I2, I), length(I1, N2),
	append(List1, I1, List), 
	N3 is Number - N1 - 1,
	append([grp(I2,1)], [grp(I,N3)], Rest).

% Debugging tool ... 
show_me([]).
show_me([I|Rest]) :-
      I = grp(I1,_Num), show_me_special(I1), show_me(Rest).
show_me([I|Rest]) :-
      I \= grp(_,_), show_me(Rest).

show_me_special([]).
show_me_special([1|Rest]) :- format("One", []), show_me_special(Rest).
show_me_special([l|Rest]) :- format("Left", []), show_me_special(Rest).
show_me_special([X|Rest]) :- X \== 1, X \== l, write(X), show_me_special(Rest).


%  config([grp([1,1],1),grp([1,0],2),grp([1,1],1),grp([1],17485730)],e,grp([1,0],1),l,[grp([0],1),grp([1],1),grp([0],3)])
%  config([grp([0],1),grp([2],1),grp([1],1),grp([2],1),grp([2,1],435909),grp([1],2)],c,grp([2],653864),l,[grp([1],1)])
%  config([grp([0],1),grp([2],1),grp([1],1),grp([2],1),grp([2,1],4),grp([1],2)],c,grp([2],653864),l,[grp([1],1)])
%  config([grp([0],1),grp([2],1),grp([1],1),grp([2],1),grp([2,1],435909),grp([1],2)],c,grp([2],6),l,[grp([1],1)])


%  Left = [grp([0],1),grp([2],1),grp([1],1),grp([2],1),grp([2,1],435909),grp([1],2)], new_leftify(Left, NLeft), compresstape(NLeft, NLeft2).
%List1 is [2,1] Rest1 is [grp([2],1),grp([1,2],435909),grp([1],2)] Rest2 is [grp([2],1),grp([1,2],435908),grp([1],2)]
%Left = [grp([0], 1), grp([2], 1), grp([1], 1), grp([2], 1), grp([2, 1], 435909), grp([1], 2)],
%NLeft = [grp([0], 1), grp([2], 1), grp([1], 1), grp([2], 1), grp([1, 2], 435909), grp([1], 2)],
%NLeft2 = [grp([0], 1), grp([2, 1], 435911), grp([1], 1)].

%% new_compress_config( config([grp([1],v(_G8879,0,10,0,10))],b,grp([1],1),l,[]) , New).


