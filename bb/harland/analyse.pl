analyse(N, M, Ones, Hops, Status, Args, NewOnes, NewHops, NewStatus, NewOutputs) :- 
	number_of_states(M, States),
	number_of_symbols(M, Symbols),
	number_of_dirs(M, Dirs),
	analyse(States, Symbols, Dirs, N, M, Ones, Hops, Status, Args, NewOnes, NewHops, NewStatus, NewOutputs). 

analyse(States, Symbols, Dirs, N, M, Ones, Hops, Status, Outputs, Ones, Hops, Status, Outputs) :- 
    % \+ member(Status, [going,going(_),unknown]), !. 
    % format("% Checking status~n", []), 
    check_status(Status, States, Symbols, Dirs, N, M), 
    % format("% Checked~n", []), 
    !. 

analyse(_States, _Symbols, _Dirs, _N, M, _Ones, _Hops, Status, Args, NewOnes, NewHops, NewStatus, NewOutputs) :-
     member(Status, [going,going(_),unknown]), 
    %  format("% Static check .... ~n", []), 
     static_checks(M, Args, NewOnes, NewHops, NewStatus, NewOutputs),
     \+ member(NewStatus, [going,going(_),unknown]), 
     % format("% Static check done~n", []), 
     !. 

analyse(States, Symbols, Dirs, _N, M, _Ones, _Hops, Status, Args, NewOnes, NewHops, NewStatus, NewOutputs) :-
    member(Status, [going,unknown]), 
    % format("% Analysing 1 (~k)~n", [Status]), 
    bound(States, Symbols, Dirs, analyse, Bound, MaxSteps),  
    % format("% Analysing 1 ", []), write(Status), format(" with Bound ~d~n", [Bound]), 
    % emulate_bb(M, Bound, flex, [maxsteps(MaxSteps),loop,escape,blank,otter,induction,optcom,newtrie(10,5)], NewOnes, NewHops, NewStatus, NewOutputs), 
    % emulate_bb(M, Bound, flex, [maxsteps(MaxSteps),otter,induction,optcom,newtrie(10,5)], NewOnes, NewHops, NewStatus, NewOutputs), 
    emulate_bb(M, Bound, flex, [maxsteps(MaxSteps),otter,induction,compress2,trie(20)], NewOnes, NewHops, NStatus, NewOutputs), 
    % format("Emulation done, NStatus is ~k~n", [NStatus]), 
    set_status(NStatus, NewStatus), 
    % format("% Analysing 1: ~k to ~k~n", [Status,NewStatus]),  
    ( member(nomonster, Args) -> true; \+ member(NewStatus, [going,going(_),unknown]) ), % Give up here unless monster search is specified.
    !. 

analyse(States, Symbols, Dirs, _N, M, _Ones, _Hops, Status, Args, NewOnes, NewHops, NewStatus, NewOutputs) :-
    member(Status, [going(SoFar)]), 
    % format("% Analysing 1 (~k)~n", [Status]), 
    bound(States, Symbols, Dirs, analyse, Bound1, MaxSteps),  
    Bound is max(2*SoFar, Bound1), 
    % format("% Analysing 2 ", []), write(Status), format(" with Bound ~d~n", [Bound]), 
    % emulate_bb(M, Bound, flex, [maxsteps(MaxSteps),loop,escape,blank,otter,induction,optcom,newtrie(10,5)], NewOnes, NewHops, NewStatus, NewOutputs), 
    % emulate_bb(M, Bound, flex, [maxsteps(MaxSteps),otter,induction,optcom,newtrie(10,5)], NewOnes, NewHops, NewStatus, NewOutputs), 
    emulate_bb(M, Bound, flex, [maxsteps(MaxSteps),otter,induction,compress2,trie(20)], NewOnes, NewHops, NStatus, NewOutputs), 
    set_status(NStatus, NewStatus), 
    % format("% Analysing 2: ~k to ~k~n", [Status, NewStatus]),  
    ( member(nomonster, Args) -> true; \+ member(NewStatus, [going,going(_),unknown]) ), % Give up here unless monster search is specified.
     !. 

% Dynamic nontermination checks go here, if any ... 
% Punt that it is a monster and then give up.
analyse(States, Symbols, Dirs, _N, M, _Ones, _Hops, Status, Args, NewOnes, NewHops, NewStatus, NewOutputs) :-
    member(Status, [going,going(_),unknown]), 
    \+ member(nomonster, Args), 
    % format("% Analysing 2 (~k)~n", [Status]), 
    bound(States, Symbols, Dirs, monster, Bound, MaxSteps), % Punt that it is a monster ...
    % format("% Analysing 3 ", []), write(Status), format(" with Bound ~d~n", [Bound]), 
    % format("% Monster punt (~k) with Bound ~d~n", [Status,Bound]), 
    emulate_bb(M, Bound, flex, [maxsteps(MaxSteps),otter,compress2,trie(20)], NewOnes, NewHops, NewStatus, NewOutputs), 
    % format("% Analysing 2 (~k)~n", [Status]), 
    % \+ member(NewStatus, [going,going(_),unknown]), !. 
    true, !. 

% analyse(States, Symbols, Dirs, _N, M, Ones, Hops, Status, Args, NewOnes, NewHops, NewStatus, NewOutputs) :-
%     member(Status, [going,going(_),unknown]), 
%     member(nomonster, Args), 
%     % Give up!
%     NewOnes = Ones, NewHops = Hops, 
%     set_status(Status, NewStatus), 
%     NewOutputs = Outputs, 
%    !, true. 

check_status(Status, _States, _Symbols, _Dirs, _N, _Machine) :- \+ member(Status, [going,going(_),unknown,abort,abort(_)]), !. 
check_status(Status, States, Symbols, Dirs, N, Machine) :- 
	member(Status, [abort,abort(_)]), !, 
	directory(output, States, Symbols, Dirs, tnf, Base), ensure_exists(Base), 
	filename(Base, input, States, Symbols, Dirs, tnf, abort, 1, Name, AbortInFile), 
	filename(Base, output, States, Symbols, Dirs, tnf, abort, 1, Name, AbortOutFile), 
	find_extra_machines(States, Symbols, Dirs, N, Machine, AbortInFile, AbortOutFile).

set_status(S, S) :- \+ member(S, [going, going(_), unknown]). 
set_status(unknown,going).
set_status(going,going).
set_status(going(N),going(N)).

bound(M, Type, Bound, Steps) :-
	number_of_states(M, States),
	number_of_symbols(M, Symbols),
	number_of_dirs(M, Dirs),
	bound(States, Symbols, Dirs, Type, Bound, Steps).

bound(2,2,2,search,  50,    50).
bound(2,2,2,analyse, 100,   100).
bound(2,2,2,abort,   100,   100).
bound(2,2,2,monster, 1000,  1000).
bound(3,2,2,search,  50,    100).
bound(3,2,2,analyse, 200,   100).
bound(3,2,2,abort,   200,   100).
bound(3,2,2,monster, 1000,  1000).
bound(2,3,2,analyse, 10000, 1000).
bound(2,3,2,abort,   1000,  1000).
bound(2,3,2,monster, 100000, 2000).
bound(2,3,2,search,  50,     100).
bound(4,2,2,monster, 150000, 2000).% Some 4,2 cases need history 1,000 and hops 150,000 ... 
bound(4,2,2,analyse, 50000,  10000).
bound(4,2,2,search,  100,    100).
bound(4,2,2,abort,   100,    100).
bound(2,4,2,analyse, 500000, 20000).
bound(2,4,2,abort,   1000,   1000).
bound(2,4,2,monster, 5000000, 200000).
bound(2,4,2,search,  100,    100).
bound(3,3,2,analyse, 20000,  1000).
bound(3,3,2,monster, 10000000000, 20000000).
bound(3,3,2,search,  100,    100).
bound(3,3,2,abort,   1000,   1000).
bound(5,2,2,analyse, 20000,  1000).
bound(5,2,2,monster, 50000000, 50000).
bound(5,2,2,search,  300,    300).
bound(5,2,2,abort,   1000,   1000).
bound(2,5,2,analyse, 10000,  1000).
bound(2,5,2,monster, 100000000, 5000).
bound(2,5,2,search,  200,    200).
bound(2,5,2,abort,   1000,   1000).

bound(6,2,2,search,100,100).
bound(4,3,2,search,100,100).
bound(3,4,2,search,100,100).
bound(2,6,2,search,100,100).

meander(1,[t(a,0,4,l,b),t(a,1,1,r,z),t(a,2,2,r,a),t(a,3,0,l,b),t(a,4,3,l,b),t(b,0,2,r,a),t(b,1,3,l,b),t(b,2,3,r,b),t(b,3,2,l,b),t(b,4,1,l,b)]).  % Not a meanderer!
meander(2,[t(a,0,1,r,b),t(a,1,1,r,z),t(a,2,2,r,a),t(a,3,0,l,b),t(a,4,3,l,b),t(b,0,2,r,a),t(b,1,3,l,b),t(b,2,3,r,b),t(b,3,2,l,b),t(b,4,1,l,b)]).  % Not a meanderer!
meander(3,[t(a,0,1,r,b),t(a,1,2,l,a),t(a,2,1,r,a),t(b,0,1,l,c),t(b,1,1,l,a),t(b,2,2,r,c),t(c,0,1,l,z),t(c,1,1,l,a),t(c,2,2,r,b)]). % Not a meanderer!
meander(4,[t(a,0,1,r,b),t(a,1,1,l,a),t(b,0,0,l,a),t(b,1,1,l,c),t(c,0,1,r,z),t(c,1,0,l,d),t(d,0,1,r,d),t(d,1,0,l,a)]). % Meanderer from CATS07 paper. 

% Designed to normalise Machines generated elsewhere. NewMachine will have the properties below.
% The first transition (when run on a blank tape) will be t(a,0,1,r,b).
% NewMachine will be a sorted list of transitions, sorted by lexographic ordering on States x Symbols
normalise(Machine, NewMachine) :-
	set_first_state(a, Machine, Machine1),
	set_first_output(1, Machine1, Machine2),
	set_first_direction(r, Machine2, Machine3),
	sort_transitions(Machine3, Machine4),
	NewMachine = Machine4,!, 
	true. 
normalise(Machine, Machine) :- format("Normalisation failed for ", []), write(Machine), nl.

set_first_state(State, Machine, Machine) :- \+ member(t(a,0,0,_,_), Machine). 
set_first_state(State, Machine, NewMachine) :-
        member(t(a,0,0,_,_), Machine), 
	% This is only needed if the first transitions is of the form t(a,0,0,D,NS)
        Bound = 10, 
	find_true_first(Machine, a, First, 0, Bound),
	swap_states(State, First, [], Machine, NewMachine). 

find_true_first(Machine, State, First, Now, Bound) :- 
        Now < Bound, 
        member(t(State, 0, O, _D, NS), Machine), O \== 0,
	First = NS. 
find_true_first(Machine, State, First, Now, Bound) :- 
        Now < Bound, 
        member(t(State, 0, 0, _D, NS), Machine), Now1 is Now + 1, 
	find_true_first(Machine, NS, First, Now1, Bound). 

swap(State1, State2, State3, NewState) :-
	State3 == State1, NewState = State2.
swap(State1, State2, State3, NewState) :-
	State3 == State2, NewState = State1.
swap(State1, State2, State3, NewState) :-
	State3 \== State1, State3 \== State2, NewState = State3.

swap_states(_State1, _State2, SoFar, [], SoFar).
swap_states(State1, State2, SoFar, [t(S,I,O,D,NS)|Rest], NewMachine) :-
	swap(State1, State2,  S,  NewS), 
	swap(State1, State2, NS, NewNS), 
	append(SoFar, [t(NewS, I, O, D, NewNS)], NewSoFar),
	swap_states(State1, State2, NewSoFar, Rest, NewMachine).

set_first_output(Output, Machine, NewMachine) :-
	member(t(a,0,Out,_D,_NS), Machine), Out == Output, 
	Machine = NewMachine. 
set_first_output(Output, Machine, NewMachine) :-
	member(t(a,0,Out,_D,_NS), Machine), Out \== Output, 
	swap_symbols(Output, Out, [], Machine, NewMachine).

swap_symbols(_Symbol1, _Symbol2, SoFar, [], SoFar).
swap_symbols(Symbol1, Symbol2, SoFar, [t(S,I,O,D,NS)|Rest], NewMachine) :-
	swap(Symbol1, Symbol2, I, NewI), 
	swap(Symbol1, Symbol2, O, NewO), 
	append(SoFar, [t(S, NewI,  NewO, D, NS)], NewSoFar),
	swap_symbols(Symbol1, Symbol2, NewSoFar, Rest, NewMachine).

set_first_direction(Dir, Machine, NewMachine) :-
	member(t(a,0,_Out,Dir,_NS), Machine),
	NewMachine = Machine.
set_first_direction(Dir, Machine, NewMachine) :-
	member(t(a,0,_Out,D,_NS), Machine), D \== Dir, 
	swap_directions(D, Dir, [], Machine, NewMachine).

swap_directions(_Direction1, _Direction2, SoFar, [], SoFar).
swap_directions(Direction1, Direction2, SoFar, [t(S,I,O,D,NS)|Rest], NewMachine) :-
	swap(Direction1, Direction2, D, NewD), 
	append(SoFar, [t(S, I,  O, NewD, NS)], NewSoFar),
	swap_directions(Direction1, Direction2, NewSoFar, Rest, NewMachine).

sort_transitions(Machine, NewMachine) :-
	number_of_states(Machine, States),
        number_of_symbols(Machine, Symbols), 
        sortmachine(0, States, Symbols, a,0,[],Machine,SortM),
	NewMachine = SortM, % Need to work on this!
	true. 

static_checks(_M, _Outputs, _NewOnes, _NewHops, _NewStatus, _NewOutputs) :- fail. % To test induction ... 
% static_checks(M, _Outputs, NewOnes, NewHops, NewStatus, NewOutputs) :-
%     meandering(M), 
%     NewOnes = 0,
%     NewHops = 0,
%     NewStatus = meander,
%     NewOutputs = []. 
%     % fail. 

% nonterminating(M, _Outputs, NewStatus) :- looping(M), !, NewStatus = loops.
nonterminating(M, _Outputs, NewStatus) :- meandering(M), !, NewStatus = meander.

meandering(M) :-
    member(t(S,I,_O,_D,H), M), halt_state(H), 
    % format("Halt transition is ~k, ~k, ~k, ~k, ~k~n", [S,I,O,D,H]), 
    % run_backwards(M, ....),
    % \+ run_backwards(state([],S,[I]), M, 100, naive, 0, 0),
    backwards_bound(Bound), 
    \+ run_backwards(config([], S, I, l, []), M, Bound, naive, 0), 
    true. 

backwards_bound(10). % Experiment with this value.

run_backwards(_Config, _M, Bound, Mode, Hops) :-
    member(Mode, [naive]), 
    Hops > Bound, 
    % format("Finishing with ", []), display_config(Config), nl, 
    true.

run_backwards(Config, _M, Bound, Mode, Hops) :-
    member(Mode, [naive]), 
    Hops =< Bound, 
    Config = config(Left, State, Item, Dir, Right), check_blank(Left, Left1), check_blank(Right, Right1), 
    initial_config(naive,eval,blank,config(Left1, State, Item, Dir, Right1),_), 
    % format("Initial Configuration ", []), display_config(Config), nl, 
    true. 
run_backwards(config(Left, State, Item, Dir, Right), M, Bound, Mode, Hops) :-
    member(Mode, [naive]), 
    Hops =< Bound, 
    \+ initial_config(naive,eval,blank,config(Left, State, Item, Dir, Right),_), 
    % format("Up to ~d: ", [Hops]), display_config(config(Left, State, Item, Dir, Right)), 
    member(t(NewState, In, Out, TransDir, State), M),
    % format(" Current transition is ~k, ~k, ~k, ~k, ~k", [NewState, In, Out, TransDir, State]),  
    update_backwards(config(Left, State, Item, TransDir, Right), t(NewState, In, Out, TransDir, State), config(NewLeft, NewState, NewItem, NewDir, NewRight)),
    % format(" Updated ", []), display_config(config(NewLeft, NewState, NewItem, NewDir, NewRight)), nl, 
    Hops1 is Hops + 1,
    run_backwards(config(NewLeft, NewState, NewItem, NewDir, NewRight), M, Bound, Mode, Hops1). 

update_backwards(config(Left, State, Item, _Dir, Right), t(NewState, In, _Out, r, State), config([], NewState, In, l, [Item|Right])) :-	Left == [].
update_backwards(config(Left, State, Item, _Dir, Right), t(NewState, In, Out, r, State), config(RestL, NewState, In, l, [Item|Right])) :- Left = [Out|RestL]. 
update_backwards(config(Left, State, Item, _Dir, Right), t(NewState, In, _Out, l, State), config([Item|Left], NewState, In, l, [])) :- Right == [].
update_backwards(config(Left, State, Item, _Dir, Right), t(NewState, In, Out, l, State), config([Item|Left], NewState, In, l, RestR)) :- Right = [Out|RestR].

% looping(_M) :- fail.  %% Is this really needed? 

output_row(Symbols) :- output_row1(0, Symbols).
output_row1(Current, Final) :- Current >= Final. 
output_row1(Current, Final) :- Current < Final, format("<td><a class=heading>~d</a>", [Current]), NewCurrent is Current + 1, output_row1(NewCurrent, Final). 
	
output_html_table(Symbols, M) :-
	sortmachine(Symbols, a, 0, [], M, SortM),
        format("<table border=1><tr><td>&nbsp;", []), 
	output_row(Symbols), 
	output_html_table1(SortM).

output_html_table1([]). 
output_html_table1([t(S,I,O,D,NS)|Rest]) :-
	format("<tr><td><a class=heading>~k</a>", [S]), 
	output_html_table2(S,[t(S,I,O,D,NS)|Rest]).
	
output_html_table2(S, [t(S,_I,O,D,NS)|Rest]) :-
	format("<td><a>~k ~k ~k</a>", [O, D, NS]), 
	output_html_table2(S, Rest). 

output_html_table2(State, [t(S,I,O,D,NS)|Rest]) :-
	State \== S, % Finished this row
	format("~n"),
	output_html_table1([t(S,I,O,D,NS)|Rest]). 
	
output_html_table2(_State, []) :-
	% Finished last row
	format("~n</table>~n"). 


