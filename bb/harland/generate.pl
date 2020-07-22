create_machines(States, Symbols, Dirs, Style, Type) :-
        generate_machines(States, Symbols, Dirs, Style, Type), % format("Numbering~n", []), 
        number_machines(States, Symbols, Dirs, Style, Type).

generate_machines(States, Symbols, _Dirs, _Style, _Type) :-
	States * Symbols >= 13, !, 
	format("Too large!~n", []).

generate_machines(States, Symbols, _Dirs, Style, _Type) :-
	States * Symbols < 13, \+ member(Style, [rel,abs]), !, 
	format("Unknown style ~k~n", [Style]).

generate_machines(States, Symbols, _Dirs, Style, Type) :-
	States * Symbols < 13, member(Style, [rel,abs]), \+ member(Type, [all,free,tnf]), !, 
	format("Unknown type ~k~n", [Type]).

generate_machines(States, Symbols, Dirs, Style, Type) :-
        States * Symbols < 13, member(Style, [rel,abs]), member(Type, [all,free,tnf]), !,
    	% format("Calling directory~n", []), 

	%% How do we cope with Style information here??
	directory(input, States, Symbols, Dirs, Style, Type, Base1), ensure_exists(Base1),
	% format("Calling filename~n", []), format("Base 1: ~s~n", [Base1]), ttyflush, 
        filename(Base1, generate, States, Symbols, Dirs, Style, Type, raw, 1, Name, _File), 

	NewFileName = Name, 
	% format("Name is ~s~n", [Name]), ttyflush, 
	string_concat(NewBaseName, "-part1.pl", NewFileName), 
	% format("NewBaseName is ~s~n", [NewBaseName]), ttyflush, 
	atom_codes(NewFile, NewFileName), 

	retractall(fragment(_)), assert(fragment(1)),
	tell(NewFile), !, 
	generate_machines1(NewBaseName, States, Symbols, Dirs, Style, Type), !, 
	told.
 
generate_machines1(Name, States, Symbols, Dirs, Style, Type) :-
	find_machine(States, Symbols, Dirs, Style, Type, Machine, Ones, Hops, Status),
	find_trans(Machine, M), 
	write_machine(Name, M, Ones, Hops, Status), 
	fail. 
generate_machines1(_Name, _States, _Symbols, _Dirs, _Style, _Type) :- !. 

write_machine(_Name, Machine, Ones, Hops, Status) :-
	current_output(Stream), line_count(Stream, Count), 
 	filelinemax(Max), Count =< Max, !, % Keep writing to same file
 	bbinternalprint(bb, 3, Machine, Ones, Hops, Status), !. 

write_machine(Name, Machine, Ones, Hops, Status) :-
	current_output(Stream), line_count(Stream, Count), 
 	filelinemax(Max), Count > Max, !, % Time for a new file
	retract(fragment(Frag)), NewFrag is Frag+1, assert(fragment(NewFrag)),
	number_string(NewFrag, NewF), 

	% append(Name, "-part", NewF, T1), append(T1, ".pl" , NewFileName),
	string_concat(Name, "-part", T11), string_concat(T11, NewF, T1), string_concat(T1, ".pl" , NewFileName), 
	atom_codes(NewFile, NewFileName), % format("% New file is ~k~n", [NewFile]),!, 

	told,
	tell(NewFile),
 
	bbinternalprint(bb,3,Machine,Ones,Hops,Status), !.

filelinemax(1000000) :- !. % maximum number of lines to write to a file before starting a new one. 
% filelinemax(50) :- !. % maximum number of lines to write to a file before starting a new one. 

% find_machine(States, Symbols, Dirs, Style, Type, Machine, Ones, Hops, Status, ),
find_machine(1, _Symbols, Dirs, Style, tnf, [t(a,0,O,D,N)], 0, 0, unknown) :- halt_trans(Dirs, Style, t(a,0,O,D,N)). 
find_machine(States, Symbols, Dirs, Style, tnf, Machine, Ones, Hops, Status) :-
        Dirs = 2, Style = abs, % Don't know how to do relative machines in one-dimension yet ... 
        States > 1, bound(States, Symbols, Dirs, search, Bound, _MaxSteps), 
	initial_machine(States, Symbols, Dirs, Style, M),
	% format("Initialised~n",[]), 
	%% Hmmm... may need to think about arguments here and variety of generation -- eg raw but later most efficiently sorted ...
        emulate_search(States, Symbols, Dirs, M, blank, Bound, search, [blank,loop], [], Machine, Ones, Hops, Status, _).
	% format("Searched~n", []), 
        % true.

find_machine(States, Symbols, Dirs, Style, free, _Machine, 0, 0, unknown) :-
        Dirs = 2, Style = abs, 
        States > 1, 
	States * Symbols > 10, !, format("Too big for free generation~n", []).

find_machine(States, Symbols, Dirs, Style, free, Machine, 0, 0, unknown) :-
        Dirs = 2, Style = abs, 
        States > 1, 
	States * Symbols =< 10, !, 
	free_trans(States, Symbols, List), 
	append(Pre, [p(S,I)|Post], List),	
	b0_transition(States, Symbols, Dirs, Style, t(b,0,O1,D1,N1)), 
	trans(States, Symbols, Dirs, Pre, Trans1), trans(States, Symbols, Dirs, Post, Trans2),
	halt_trans(Dirs, Style, t(S,I,O,D,N)),
	append([t(a,0,1,r,b),t(b,0,O1,D1,N1)], Trans1, [t(S,I,O,D,N)], Temp1),
	append(Temp1, Trans2, Machine). 

find_machine(States, Symbols, _Dirs, _Style, all, _Machine, 0, 0, unknown) :-
	States * Symbols > 8,!, format("Too big for all generation~n", []).

find_machine(States, Symbols, Dirs, Style, all, Machine, 0, 0, unknown) :-
        % 1-halting case
	States * Symbols =< 8, 
	all_trans(States, Symbols, List), 
	append(Pre, [p(S,I)|Post], List),
	trans(States, Symbols, Dirs, Style, Pre, Trans1), trans(States, Symbols, Dirs, Style, Post, Trans2),
	halt_trans(Dirs, Style, t(S,I,O,D,N)),
	append(Trans1, [t(S,I,O,D,N)], Trans2, Machine). 
find_machine(States, Symbols, Dirs, Style, all, Machine, 0, 0, unknown) :-
        % 0-halting case, which doesn't make sense for bb machines ... 
        Dirs > 2, 
	States * Symbols =< 8, 
	all_trans(States, Symbols, List), 
	trans(States, Symbols, Dirs, Style, List, Machine). 

free_trans(2, 2, [p(a,1),p(b,1)]).
free_trans(2, 3, [p(a,1),p(b,1),p(a,2),p(b,2)]).
free_trans(3, 2, [p(a,1),p(b,1),p(c,0),p(c,1)]).
free_trans(2, 4, [p(a,1),p(b,1),p(a,2),p(b,2),p(a,3),p(b,3)]).
free_trans(4, 2, [p(a,1),p(b,1),p(c,0),p(c,1),p(d,0),p(d,1)]).

all_trans(1, 2, [p(a,0),p(a,1)]). 
all_trans(1, 3, [p(a,0),p(a,1),p(a,2)]). 
all_trans(1, 4, [p(a,0),p(a,1),p(a,2),p(a,3)]). 
all_trans(2, 2, [p(a,0),p(a,1),p(b,0),p(b,1)]).
all_trans(2, 3, [p(a,0),p(a,1),p(a,2),p(b,0),p(b,1),p(b,2)]).
all_trans(3, 2, [p(a,0),p(a,1),p(b,0),p(b,1),p(c,0),p(c,1)]).
all_trans(2, 4, [p(a,0),p(a,1),p(a,2),p(a,3),p(b,0),p(b,1),p(b,2),p(b,3)]).
all_trans(4, 2, [p(a,0),p(a,1),p(b,0),p(b,1),p(c,0),p(c,1),p(d,0),p(d,1)]).

halt_trans(2, abs, t(_,_,1,r,Halt)) :- halt_state(Halt). 
halt_trans(Dirs, abs, t(_,_,1,n,Halt)) :- Dirs > 2, halt_state(Halt). 
halt_trans(_Dirs, rel, t(_,_,1,f,Halt)) :- halt_state(Halt). 

trans(_States, _Symbols, _Dirs, _Style, [], []) :- !. 
trans(States, Symbols, Dirs, Style, [p(S,I)|Rest], [t(S,I,O,D,N)|Result]) :-
	state(States, N), symbol(Symbols, O), dir(Dirs, Style, D), 
	trans(States, Symbols, Dirs, Style, Rest, Result).

% Make this far more specific for initial testing ... 
initial_machine(States, Symbols, Dirs, Style, [t(a,0,1,r,b), BTrans]) :- b0_transition(States, Symbols, Dirs, Style, BTrans).
	
b0_transition(_States, _Symbols, _Dirs, _Style, t(b,0,S,l,a)) :- member(S, [0,1]). % If new state is a or b, direction must be left. 
b0_transition(_States, Symbols, _Dirs, _Style, t(b,0,2,l,a)) :- Symbols > 2. % Third symbol, if any, must be 2. 
b0_transition(_States, _Symbols, _Dirs, _Style, t(b,0,S,l,b)) :- member(S, [0,1]). 
b0_transition(_States, Symbols, _Dirs, _Style, t(b,0,2,l,b)) :- Symbols > 2. % Third symbol, if any, must be 2. 
b0_transition(States, _Symbols, Dirs, Style, t(b,0,S,Dir,c)) :- States > 2, member(S, [0,1]), dir(Dirs, Style, Dir). 
b0_transition(States, Symbols, Dirs, Style, t(b,0,2,Dir,c)) :- States > 2, Symbols > 2, dir(Dirs, Style, Dir). % Third symbol, if any, must be 2. 

%% Can probably delete this looping(), but want to make sure ... 
%% looping(_List, state(Left, _State, In, Right), _History) :- all_blank(Left), all_blank(Right), all_blank([In]). % Blank tape, so it is of no interest
%% looping(_List, state(Left, State, In, Right), History) :- member(state(Left, State, In, Right), History).  % Looping
%% looping(List, state(Left, State, In, Right), _History) :- blank_symbol(In), road_runner1(List, Left, State, Right).

% Numbering

number_machines(States, Symbols, Dirs, Style, Type) :-
        number_all_machine_files(States, Symbols, Dirs, Style, Type, 1, 1). 

number_all_machine_files(States, Symbols, Dirs, Style, Type, N1, _) :- 
 	directory(input, States, Symbols, Dirs, Style, Type, Base1), 
        filename(Base1, generate, States, Symbols, Dirs, Style, Type, raw, N1, Name, _File), 
	NewFileName = Name, 
        \+ exists_file(NewFileName),  
	% No more files, so stop ... 
	!, true. 

number_all_machine_files(States, Symbols, Dirs, Style, Type, N1, Current) :- 
 	directory(input, States, Symbols, Dirs, Style, Type, Base1), 
        filename(Base1, generate, States, Symbols, Dirs, Style, Type, raw, N1, Name, _File), 
	NewFileName = Name, 
        exists_file(NewFileName), !, 
	% Another file, so ...
	% format("File found~n", []),
	number_one_file(NewFileName, States, Symbols, Dirs, Style, Type, N1, Current, Next), !, 
	NNew is N1 + 1, !,
	% format("Next file ...~n", []),
	number_all_machine_files(States, Symbols, Dirs, Style, Type, NNew, Next), !. 

number_one_file(RawName, States, Symbols, Dirs, Style, Type, N, Current, Result) :-
 	directory(input, States, Symbols, Dirs, Style, Type, Base1), % beaver_output(Base2),
 	filename(Base1, input, States, Symbols, Dirs, Style, Type, number, N, NameOut, _),
	NewFileName = RawName, 
	atom_codes(NewFile, NewFileName), 
      	open(NewFile, read, Input),
	atom_codes(Out, NameOut),
 	tell(Out), !, 
 	process_number(Current, Input, Result), 
 	close(Input),
 	told, 
	delete_file(NewFile), % Remove temp-THING now that it is numbered ... 
 	true. 

process_number(Current, Input, Result) :-
	read(Input, Term), !, 
	process_number1(Current, Input, Term, Result).

process_number1(Current, _, end_of_file, Current) :- !.
% process_number1(_Current, _Input, Term, _Result) :- 
%	Term \== end_of_file,
%	Term \= bb(_, _M, _Ones, _Hops, _Status), !,
%	format("% Unknown term ", []), display(Term), nl, !.
process_number1(Current, Input, Term, Result) :- 
	Term \== end_of_file,
	Term = bb(_, M, Ones, Hops, Status), !,
	bbinternalprint(bb,Current,M,Ones,Hops,Status),
	NewCurrent is Current + 1, !, 
	process_number(NewCurrent, Input, Result).

% Use this when we need to number from the name of the file (Demon Duck of Doom will probably require this)
% number_machines_files(4,2,2,abs,all,1,100)
number_machines_files(_States, _Symbols, _Dirs, _Style, _Type, Start, End) :-  Start > End. 
number_machines_files(States, Symbols, Dirs, Style, Type, Start, End) :-  
       Start =< End,
       directory(input, States, Symbols, Dirs, Style, Type, Base1), 
       filename(Base1, generate, States, Symbols, Dirs, Style, Type, raw, Start, Name, _File), 
       NewFileName = Name, 
       \+ exists_file(NewFileName),  !, 
       % Don't number this one, but keep going ...
       NewStart is Start + 1, 
       number_machines_files(States, Symbols, Dirs, Style, Type, NewStart, End). 

number_machines_files(States, Symbols, Dirs, Style, Type, Start, End) :-  
       Start =< End,
       directory(input, States, Symbols, Dirs, Style, Type, Base1), 
       filename(Base1, generate, States, Symbols, Dirs, Style, Type, raw, Start, Name, _File), 
       NewFileName = Name, 
       exists_file(NewFileName),  !, 
       % Number this one and move on ... 
       % Assumes 1,000,000 machines per file ... 
       % Machines in file N are numbered (N-1) million + 1 to N million
       Number is (Start - 1)*1000000 + 1, 
       number_one_file(NewFileName, States, Symbols, Dirs, Style, Type, Start, Number, _Next), !, 
       NewStart is Start + 1, 
       number_machines_files(States, Symbols, Dirs, Style, Type, NewStart, End). 
