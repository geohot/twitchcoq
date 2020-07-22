% Search only, not generation as well
% analyses(2,3,2,tnf,analyse,[small,medium,large]).
% Designed to be used once the list of machines has been generated.

process(States, Symbols, Dirs, Type, Mode, Args) :- process(States, Symbols, Dirs, abs, Type, Mode, Args). % For backwards compatibility ... 
process(States, Symbols, Dirs, Style, Type, Mode, Args) :-
	% files(States, Symbols, Dirs, Type, Number),

	initialise_counters(Counters), 
	% format("About to iterate~n", []), flush_output, 
	iterate_file(States, Symbols, Dirs, Type, Mode, Args, Counters, Final_Counters, 1), !, 

	% format("Outputting summary~n", []), flush_output, 
	% Now write summary file
	% beaver_output(Base2), 
	directory(output,States,Symbols,Dirs,Style,Type,Base2), ensure_exists(Base2), 
	filename(Base2, output, States, Symbols, Dirs, Style, Type, Mode, 1, Name, _),
	% format("Summary Filename is ~s~n", [Name]), flush_output, 
	basename(Name, BaseName), 
	summary_name(Mode, M), append(BaseName, M, "-summary.pl", RealName), 
	% format("Summary is ~s~n", [RealName]), flush_output, 
	atom_codes(File, RealName), 
	% format("Outputting counters~n", []), flush_output, 
 
	tell(File), output_counters(Final_Counters), told.

iterate_file(States, Symbols, Dirs, Style, Type, Mode, Args, Counters, Final_Counters, N1) :- 
	which_dir(Mode, States, Symbols, Dirs, Style, Type, Base1), % format("Calling filename~n",[]),
	mode_status(Mode, Status), 
	filename(Base1, Status, States, Symbols, Dirs, Style, Type, Mode, N1, _Name, File),
	% format("Filename is ~s~n", [Name]), 
	\+ exists_file(File),    

	% When the Mode is refine, we need to refine the output Abort file. Otherwise update counters from the output Abort file, if any.
	% format("% Handling aborts~n", []), flush_output, 
	handle_aborts(States, Symbols, Dirs, Style, Type, Mode, Args, Counters, Final_Counters),
        % format("% Aborts done~n", []), flush_output,
        true. 
    
iterate_file(States, Symbols, Dirs, Style, Type, Mode, Args, Counters, Final_Counters, N1) :-
	which_dir(Mode, States, Symbols, Dirs, Style, Type, Base1), % format("Calling filename again~n",[]),
	mode_status(Mode, Status), 
        filename(Base1, Status, States, Symbols, Dirs, Style, Type, Mode, N1, _Name, File),
	% format("Filename is ~s~n", [Name]), 
	exists_file(File), !, 

	% format("Processing one file with ~k ~k ~n", [Type,Mode]), 
	process_one_file(States, Symbols, Dirs, Style, Type, Mode, Args, N1, Counters, NewCounters), !, 
	NNew is N1 + 1, !, 	
	% output_counters(NewCounters),
	iterate_file(States, Symbols, Dirs, Type, Mode, Args, NewCounters, Final_Counters, NNew), !. 

process_one_file(States, Symbols, Dirs, Style, Type, Mode, Args, N, Counters, Final_Counters) :-
	Mode = analyse, 
	directory(input, States, Symbols, Dirs, Style, Type, Base1), directory(output, States, Symbols, Dirs, Style, Type, Base2), 
	ensure_exists(Base1), ensure_exists(Base2), 
	filename(Base1, input, States, Symbols, Dirs, Style, Type, Mode, N, _Name, File),
	filename(Base2, output, States, Symbols, Dirs, Style, Type, Mode, N, NameOut, _),
        append_to_plfile(NameOut, "-out", OutName),
	append_to_plfile(NameOut, "-going", GoingName), 
	open(File, read, Input),
	atom_codes(Out, OutName),
	tell(Out), 
	atom_codes(GoingFile, GoingName),
	open(GoingFile, write, Go),

	initialise_local_counters(Counters, NewCounters),
	process_one_file1(States, Symbols, Dirs, Style, Input, analyse, Args, Go, NewCounters, Final_Counters), !, 
	output_counters(Final_Counters), 

	close(Input), close(Go), told.

process_one_file(States, Symbols, Dirs, Style, Type, Mode, Args, N, Counters, Final_Counters) :-
	Mode = refine, 
	% beaver_input(Base1), beaver_output(Base2),
        directory(output, States, Symbols, Dirs, Style, Type, Base2), ensure_exists(Base2), 
	filename(Base2, input, States, Symbols, Dirs, Style, Type, Mode, N, _Name, File),
	filename(Base2, output, States, Symbols, Dirs, Style, Type, Mode, N, OutName, Out),
 	append_to_plfile(OutName, "-going", GoingName), 
	open(File, read, Input),
	tell(Out), 
	atom_codes(GoingFile, GoingName),
	open(GoingFile, write, Go),

	initialise_local_counters(Counters, NewCounters), 
	process_one_file1(States, Symbols, Dirs, Style, Input, analyse, Args, Go, NewCounters, Final_Counters), !, 
	output_counters(Final_Counters), 

	close(Input), close(Go), told.

process_one_file(States, Symbols, Dirs, Style, Type, Mode, Args, N, Counters, Final_Counters) :-
	Mode = pseudouni, 
	directory(input, States, Symbols, Dirs, Style, Type, Base1), directory(output, States, Symbols, Dirs, Style, Type, Base2), 
	ensure_exists(Base1), ensure_exists(Base2), 
	filename(Base1, input, States, Symbols, Dirs, Style, Type, Mode, N, _Name, File),
	filename(Base2, output, States, Symbols, Dirs, Style, Type, Mode, N, NameOut, _),
        append_to_plfile(NameOut, "-pseudo", OutName), 
	open(File, read, Input),
	atom_codes(Out, OutName),
	tell(Out), 

	initialise_local_counters(Counters, NewCounters), 
	process_one_file1(States, Symbols, Dirs, Style, Input, pseudouni, Args, _Go, NewCounters, Final_Counters), !, 
	output_counters(Final_Counters), 

	close(Input), told. 

process_one_file(States, Symbols, Dirs, Style, Type, Mode, Args, N, Counters, Final_Counters) :-
	Mode = stats, 
	directory(input, States, Symbols, Dirs, Style, Type, Base1), % output_dir(States, Symbols, Dirs, Base2), 
	ensure_exists(Base1), 

	filename(Base1, input, States, Symbols, Dirs, Style, Type, Mode, N, _, File),
	% filename(Base2, output, States, Symbols, Dirs, Type, Mode, N, NameOut, _),
	% add_to_plfile(NameOut, "-stats", OutName),
	open(File, read, Input),
	% atom_codes(Out, OutName),
	% tell(Out), 

	initialise_local_counters(Counters, NewCounters), 
	process_one_file1(States, Symbols, Dirs, Style, Input, stats, Args, _Go, NewCounters, Final_Counters), !, 
	output_counters(Final_Counters), 

	close(Input). 

process_one_file(States, Symbols, Dirs, Style, Type, Mode, Args, N, Counters, Final_Counters) :-
	Mode = status, 
	directory(output, States, Symbols, Dirs, Style, Type, Base2), ensure_exists(Base2), 

	filename(Base2, output, States, Symbols, Dirs, Style, Type, Mode, N, _, File),
	% filename(Base2, output, States, Symbols, Dirs, Type, Mode, N, NameOut, _),
	open(File, read, Input),
	% atom_codes(Out, OutName),
	% tell(Out), 

	initialise_local_counters(Counters, NewCounters), 
	process_one_file1(States, Symbols, Dirs, Style, Input, status, Args, _Go, NewCounters, Final_Counters), !, 
	output_counters(Final_Counters), 

	close(Input).

process_one_file(States, Symbols, Dirs, Style, Type, Mode, Args, N, Counters, Final_Counters) :-
	Mode = convert(Format, Numbered), % format("Converting ... ~n", []),  
	member(Format, [marxen]), 
	directory(input, States, Symbols, Dirs, Style, Type, Base1), 
	filename(Base1, input, States, Symbols, Dirs, Style, Type, Mode, N, _InName, InFile),
	filename(Base1, output, States, Symbols, Dirs, Style, Type, Mode, N, OutName, _OutFile),
	% format("Names done~n", []),  
	open(InFile, read, Input),
	append(BaseName, ".pl", OutName), append(BaseName, ".txt", RealOutName), 
	% format("RealOutName is ~s~n", [RealOutName]), 
	atom_codes(Out, RealOutName),
	tell(Out), 

	process_one_file1(States, Symbols, Dirs, Style, Input, convert(Format, Numbered), Args, _Go, Counters, Final_Counters), 

	close(Input).

process_one_file(_States, _Symbols, _Dirs, _Style, _Type, Mode, _Args, _N, Counters, Counters) :-
	Mode = convert(Format, _Numbered), 
	\+ member(Format, [marxen]), 
	!, true. 

process_one_file1(States, Symbols, Dirs, Style, Input, Mode, Args, GoFile, Counters, Final_Counters) :-
        read(Input, Term), !, 
	process_one_file11(States, Symbols, Dirs, Style, Term, Input, Mode, Args, GoFile, Counters, Final_Counters).

process_one_file11(_States, _Symbols, _Dirs, _Style, end_of_file, _Input, _Mode, _Args, _GoFile, Counters, Counters).
process_one_file11(States, Symbols, Dirs, Style, Term, Input, Mode, Args, GoFile, Counters, Final_Counters) :-
        Term \== end_of_file,
	process_term(States, Symbols, Dirs, Style, Term, Mode, Args, GoFile, Counters, NCounters), !, 
	process_one_file1(States, Symbols, Dirs, Style, Input, Mode, Args, GoFile, NCounters, Final_Counters).

process_term(_,_,_,_,end_of_file, _, _, _, Counters, Counters) :- !. 
process_term(States, Symbols, Dirs, _Style, bb(N, Machine, Ones, Hops, Status), Mode, Args, GoFile, Counters, Final_Counters) :- 
	Mode = analyse, \+ member(Status, [abort, abort(_)]), 
	% format("% Analysing: ", []), bbinternalprint(bb, N, Machine, 0, 0, unknown),  
        analyse(States, Symbols, Dirs, N, Machine, Ones, Hops, Status, Args, NewOnes, NewHops, NewStatus, _NewOutputs), !, 
	bbinternalprint(bb, N, Machine, NewOnes, NewHops, NewStatus),  !, flush_output, 
	check_going(GoFile, N, Machine, NewOnes, NewHops, NewStatus),  !, flush_output, 
	update_counters(Machine, NewOnes, NewHops, NewStatus, Counters, Final_Counters), !.
process_term(States, Symbols, Dirs, Style, bb(N, Machine, Ones, Hops, Status), Mode, _Args, _GoFile, Counters, Final_Counters) :- 
	Mode = analyse, member(Status, [abort, abort(_)]), 
	format("% Processing abort ~n", []), 
	% First output original machine ... 
	bbinternalprint(bb, N, Machine, Ones, Hops, Status),  !, flush_output, 
	update_counters(Machine, Ones, Hops, Status, Counters, Final_Counters), 
	% Then find some more machines and write them to an 'extra' file. 
	format("% Finding Files~n", []), 
	directory(output, States, Symbols, Dirs, Style, tnf, Base), ensure_exists(Base), 
	filename(Base, input, States, Symbols, Dirs, Style, tnf, abort, 1, _Name1, AbortInFile),
 	format("% Found input~n", []), 
	filename(Base, output, States, Symbols, Dirs, Style, tnf, abort, 1, _Name2, AbortOutFile), 
	format("% Finding extras~n", []), 
	find_extra_machines(States, Symbols, Dirs, Style, N, Machine, AbortInFile, AbortOutFile).

process_term(_States, _Symbols, _Dirs, _Style, bb(N, Machine, _Ones, _Hops, _Status), Mode, _Args, _GoFile, Counters, Final_Counters) :- 
	Mode = analyse, % In case analysis fails for some reason ... 
        bbinternalprint(bb, N, Machine, 0, 0, unknown), !,  flush_output, 
        update_counters(Machine, 0, 0, unknown, Counters, Final_Counters), !.

process_term(_States, _Symbols, _Dirs, _Style, bb(N, Machine, Ones, Hops, Status), Mode, Args, _GoFile, Counters, Final_Counters) :- 
	Mode = pseudouni, !, 
	pseudouni(Machine, Args, Ones, Hops, Status, NewOnes, NewHops, NewStatus), !,
	bbinternalprint(bb, N, Machine, NewOnes, NewHops, NewStatus),  !, 
	update_counters(Machine, NewOnes, NewHops, NewStatus, Counters, Final_Counters), !. 

process_term(_States, _Symbols, _Dirs, _Style, bb(_N, Machine, Ones, Hops, Status), Mode, _Args, _, Counters, Final_Counters) :- 
 	member(Mode, [stats,status]), !, 
        % ( member(Status, [abort, abort(_)]) -> 
	%     ( directory(output, States, Symbols, Dirs, tnf, Base), ensure_exists(Base), 
	%       filename(Base, input, States, Symbols, Dirs, tnf, abort, 1, Name, AbortInFile),
	%       open(AbortInFile, append, File),
	%       write(File, bb(N, Machine, Ones, Hops, Status)),  put_char(File, '.'), nl(File), 
	%       close(File)
	%       )
	% ; true ), 
	update_counters(Machine, Ones, Hops, Status, Counters, Final_Counters), !.

process_term(States, Symbols, Dirs, _Style, bb(N, Machine, _Ones, _Hops, _Status), Mode, _Args, _GoFile, Counters, Counters) :- 
	Mode = convert(Format, Numbered), 
	% format("Converting ... ~n", []), 
	convert_machine(Format, States, Symbols, Dirs, Machine, NewMachine), 
	(Numbered == numbered -> ( format("~d", [N]), separator(S), format("~s", [S]) ) ; true ), 
	format("~s~n", [NewMachine]), % NewMachine is a string, whatever format is used
	flush_output, 
	!.

process_term(_States, _Symbols, _Dirs, _Style, Term, _, _Args, _, Counters, Counters) :- 
	Term \== bb(_N, _Machine, _Ones, _Hops, _Status),
	format("Unknown term ", []), display(Term), nl.

separator(",").
% separator(" ").

append_to_plfile(Name, Suffix, NewName) :-
	append(RealName, ".pl", Name), append(RealName, Suffix, ".pl", NewName).

prepend_to_plfile(Name, Prefix, NewName) :-
	split_file(Name, Dir, File), append(Prefix, File, NewFile), append(Dir, NewFile, NewName).

split_file(Name, Dir, File) :-
	append(Dir, File, Name), append(_, "/", Dir), \+ member(47, File). % 47 is "/" but without the list type. 

find_extra_machines(States, Symbols, Dirs, Style, N, Machine, Raw, Refined) :-
	open(Raw, append, RawOutput), 
	open(Refined, append, RefinedOutput), 
	find_extra_machines1(States, Symbols, Dirs, Style, N, Machine, RawOutput, RefinedOutput), 
	close(RawOutput), close(RefinedOutput).  

find_extra_machines1(States, Symbols, Dirs, _Style, N, Machine, RawOutput, RefinedOutput) :-
	find_trans(Machine, M), 
	bound(States, Symbols, Dirs, abort, Bound, _), 
	emulate_search(States, Symbols, Dirs, M, blank, Bound, search, [loop], [], NewMachine, Ones, Hops, Status, _), 
	find_trans(NewMachine, NewTrans), 
	write(RawOutput, bb(N, NewTrans, Ones, Hops, Status)), put_char(RawOutput, '.'), nl(RawOutput), 
	analyse(States, Symbols, Dirs, N, NewMachine, Ones, Hops, Status, [], NewOnes, NewHops, NewStatus, _), 
	write(RefinedOutput, bb(N, NewTrans, NewOnes, NewHops, NewStatus)), put_char(RefinedOutput, '.'), nl(RefinedOutput), 
	%% Can't do counters here because of fail-driven loop. Ensure analyse and refine cases also used abort file for input and output. 
	fail.
find_extra_machines1(_States, _Symbols, _Dirs, _Style, _N, _Machine, _RawOutput, _RefinedOutput).

% Status can be unknown, going, going(_), halts, meander, blank, loops(cycle), loops, loops(cycle(_)), loops(road_runner), loops(induction(_)), normal, pseudo, pseudo(_,_), 

initialise_counters(counters(local(0,0,0,0,0,0,0,0,0,0), global(0,0,0,0,0,0,0,0,0,0), records([]) ) ) :- true.
initialise_local_counters(counters(_, Global, Records), counters(local(0,0,0,0,0,0,0,0,0,0), Global, Records) ) :- true.
output_counters(counters(
local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort),
Records
)) :-
    LSum is LocalUnknown + LocalGoing + LocalHalt + LocalMeander + LocalBlank + LocalCycle + LocalRoadRunner + LocalInduction + LocalPseudo + LocalAbort, 
    GSum is GlobalUnknown + GlobalGoing + GlobalHalt + GlobalMeander + GlobalBlank + GlobalCycle + GlobalRoadRunner + GlobalInduction + GlobalPseudo + GlobalAbort, 
    format("% Local: Unknown: ~d Going: ~d Halt: ~d Meander: ~d Blank: ~d Cycle: ~d RoadRunner: ~d Induction: ~d Pseudo: ~d Abort ~d Total: ~d~n", [LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort, LSum]), 
    ( GSum > 0 ->
    (
    format("% Global: Unknown: ~d (~1f%)", [GlobalUnknown, 100*GlobalUnknown/GSum]), 
    format("% Going: ~d (~1f%)", [GlobalGoing, 100*GlobalGoing/GSum]), 
    format("% Halt: ~d (~1f%) ", [GlobalHalt, 100*GlobalHalt/GSum]), 
    format("% Meander: ~d (~1f%) ", [GlobalMeander, 100*GlobalMeander/GSum]), 
    format("% Blank: ~d (~1f%) ", [GlobalBlank, 100*GlobalBlank/GSum]), 
    format("% Cycle: ~d (~1f%) ", [GlobalCycle, 100*GlobalCycle/GSum]), 
    format("% RoadRunner: ~d (~1f%)", [GlobalRoadRunner, 100*GlobalRoadRunner/GSum]), 
    format("% Induction: ~d (~1f%) ", [GlobalInduction, 100*GlobalInduction/GSum]), 
    format("% Pseudo: ~d (~1f%) ", [GlobalPseudo, 100*GlobalPseudo/GSum]), 
    format("% Abort ~d (~1f%) ", [GlobalAbort, 100*GlobalAbort/GSum]), 
    format("% Total: ~d~n", [GSum]) ) 
     ;
    (
    format("% Global: Unknown: ~d ", [GlobalUnknown]), 
    format("% Going: ~d ", [GlobalGoing]), 
    format("% Halt: ~d ", [GlobalHalt]), 
    format("% Meander: ~d ", [GlobalMeander]), 
    format("% Blank: ~d ", [GlobalBlank]), 
    format("% Cycle: ~d ", [GlobalCycle]), 
    format("% RoadRunner: ~d ", [GlobalRoadRunner]), 
    format("% Induction: ~d ", [GlobalInduction]), 
    format("% Pseudo: ~d ", [GlobalPseudo]), 
    format("% Abort ~d ", [GlobalAbort]), 
    format("% Total: ~d~n", [GSum]) ) 
    ), 

    Records = records(List), 
    format("% Records: ~n", []), 
    sort_records(List, SList), reverse(SList, FinalList), output_records(FinalList), 
    true.

update_counters(_Machine, _Ones, _Hops, Status, 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), Records), 
counters(local(NewLocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(NewGlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), Records) ) :-
    member(Status, [unknown]), 
    NewLocalUnknown is LocalUnknown + 1, 
    NewGlobalUnknown is GlobalUnknown + 1, 
    true.
update_counters(_Machine, _Ones, _Hops, Status, 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), Records), 
counters(local(LocalUnknown, NewLocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, NewGlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), Records) ) :-
    member(Status, [going,going(_)]), 
    NewLocalGoing is LocalGoing + 1, 
    NewGlobalGoing is GlobalGoing + 1,
    true.
update_counters(Machine, Ones, Hops, Status, 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), records(List)), 
counters(local(LocalUnknown, LocalGoing, NewLocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, NewGlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), records(NewList)) ) :-
    member(Status, [halts]), 
    NewLocalHalt is LocalHalt + 1, 
    NewGlobalHalt is GlobalHalt + 1, 
    checkmax(List, Machine, Ones, Hops, NList), !, checkmin(NList, Machine, Ones, Hops, NewList), !,
    true.
update_counters(_Machine, _Ones, _Hops, Status, 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), Records), 
counters(local(LocalUnknown, LocalGoing, LocalHalt, NewLocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, NewGlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), Records) ) :-
    member(Status, [meander]), 
    NewLocalMeander is LocalMeander + 1, 
    NewGlobalMeander is GlobalMeander + 1, 
    true.
update_counters(_Machine, _Ones, _Hops, Status, 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), Records), 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, NewLocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, NewGlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), Records) ) :-
    member(Status, [blank]), 
    NewLocalBlank is LocalBlank + 1, 
    NewGlobalBlank is GlobalBlank + 1, 
    true.
update_counters(_Machine, _Ones, _Hops, Status, 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), Records), 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, NewLocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, NewGlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), Records) ) :-
    member(Status, [loops,loops(cycle),loops(cycle(_))]), 
    NewLocalCycle is LocalCycle + 1, 
    NewGlobalCycle is GlobalCycle + 1, 
    true.
update_counters(_Machine, _Ones, _Hops, Status, 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), Records), 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, NewLocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, NewGlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), Records) ) :-
    member(Status, [loops(road_runner)]), 
    NewLocalRoadRunner is LocalRoadRunner + 1, 
    NewGlobalRoadRunner is GlobalRoadRunner + 1, 
    true.
update_counters(_Machine, _Ones, _Hops, Status, 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), Records), 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, NewLocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, NewGlobalInduction, GlobalPseudo, GlobalAbort), Records) ) :-
    member(Status, [loops(induction(_,_,_))]), 
    NewLocalInduction is LocalInduction + 1, 
    NewGlobalInduction is GlobalInduction + 1, 
    true.
update_counters(_Machine, _Ones, _Hops, Status, 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), Records), 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, NewLocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, NewGlobalPseudo, GlobalAbort), Records) ) :-
    member(Status, [pseudo,pseudo(_)]), 
    NewLocalPseudo is LocalPseudo + 1, 
    NewGlobalPseudo is GlobalPseudo + 1, 
    true.
update_counters(_Machine, _Ones, _Hops, Status, 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, LocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, GlobalAbort), Records), 
counters(local(LocalUnknown, LocalGoing, LocalHalt, LocalMeander, LocalBlank, LocalCycle, LocalRoadRunner, LocalInduction, LocalPseudo, NewLocalAbort),
global(GlobalUnknown, GlobalGoing, GlobalHalt, GlobalMeander, GlobalBlank, GlobalCycle, GlobalRoadRunner, GlobalInduction, GlobalPseudo, NewGlobalAbort), Records) ) :-
    member(Status, [abort, abort(_)]), 
    NewLocalAbort is LocalAbort + 1, 
    NewGlobalAbort is GlobalAbort + 1, 
    true.

update_counters(_Machine, _Ones, _Hops, Status, Counters, Counters) :-
    \+ member(Status, [unknown,going,going(_),halts,meander,blank,loops,loops(cycle),loops(cycle(_)),loops(road_runner),loops(induction),pseudo,pseudo(_),abort,abort(_)]), 
    format("% Unknown status: ", []), write(Status), nl, !.

handle_aborts(States, Symbols, Dirs, _Type, _Mode, _Args, Counters, Counters) :-
	format("Looking 1~n", []), 
	directory(output, States, Symbols, Style, Dirs, tnf, Base), 
	filename(Base, input, States, Symbols, Dirs, Style, tnf, abort, 1, _InName, AbortInFile),
	filename(Base, output, States, Symbols, Dirs, Style, tnf, abort, 1, _OutName, AbortOutFile),

	\+ exists_file(AbortInFile),  
	\+ exists_file(AbortOutFile), 
	format("No abort files~n", []), 
	!. % No abort files, so nothing to do. 

handle_aborts(States, Symbols, Dirs, _Type, _Mode, Args, Counters, Final_Counters) :-
	format("Looking 2~n", []), 
	directory(output, States, Symbols, Style, Dirs, tnf, Base), 
	filename(Base, input, States, Symbols, Dirs, Style, tnf, abort, 1, _InName, AbortInFile),
	filename(Base, output, States, Symbols, Dirs, Style, tnf, abort, 1, OutName, AbortOutFile),
	exists_file(AbortInFile),  
	\+ exists_file(AbortOutFile), !, % Can this happen?? 

	format("Abort input, but no output~n", []), 
 	append_to_plfile(OutName, "-going", GoingName), 

	open(AbortInFile, read, Input), 
	tell(OutName), 
	atom_codes(GoingFile, GoingName),
	open(GoingFile, write, Go),
	process_one_file1(States, Symbols, Dirs, Input, analyse, Args, Go, Counters, Final_Counters), !, 
	close(Input), close(Go), told, 
	true. 

handle_aborts(States, Symbols, Dirs, Type, Mode, Args, Counters, Final_Counters) :-
	format("Looking 3~n", []), 
	directory(output, States, Symbols, Style, Dirs, tnf, Base), 
	filename(Base, input, States, Symbols, Dirs, Style, tnf, abort, 1, _InName, AbortInFile),
	filename(Base, output, States, Symbols, Dirs, Style, tnf, abort, 1, _OutName, AbortOutFile),
	exists_file(AbortInFile),  
	exists_file(AbortOutFile), !, 
	format("Abort input and output found~n", []), 
	handle_aborts1(States, Symbols, Dirs, Type, Mode, Args, AbortInFile, AbortOutFile, Counters, Final_Counters).

handle_aborts1(States, Symbols, Dirs, _Type, Mode, _Args,  _AbortInFile, AbortOutFile,Counters, Final_Counters) :-
	member(Mode, [analyse,status]), 
	open(AbortOutFile, read, Input), 
	process_one_file1(States, Symbols, Dirs, Input, stats, [], _GoFile, Counters, Final_Counters),
	close(Input), 
	true. 
handle_aborts1(States, Symbols, Dirs, _Type, Mode, Args,  _AbortInFile, AbortOutFile, Counters, Final_Counters) :-
	Mode == refine, 

	atom_codes(AbortOutFile, OutName), 
 	append_to_plfile(OutName, "-going", GoingName), 
 	append_to_plfile(OutName, "-out", Out), 

	open(AbortOutFile, read, Input),
	tell(Out), 
	atom_codes(GoingFile, GoingName),
	open(GoingFile, write, Go),

	process_one_file1(States, Symbols, Dirs, Input, analyse, Args, Go, Counters, Final_Counters), !, 
	output_counters(Final_Counters), 

	close(Input), close(Go), told.

handle_aborts1(States, Symbols, Dirs, _Type, Mode, Args,  AbortInFile, _AbortOutFile,Counters, Final_Counters) :-
	Mode == pseudouni, 

	atom_codes(AbortInFile, InName), 
        append_to_plfile(InName, "-pseudo", OutName), 
	open(AbortInFile, read, Input),
	atom_codes(Out, OutName),
	tell(Out), 

	process_one_file1(States, Symbols, Dirs, Input, pseudouni, Args, _Go, Counters, Final_Counters), !, 
	output_counters(Final_Counters), 

	close(Input), told. 

handle_aborts1(States, Symbols, Dirs, _Type, Mode, Args,  AbortInFile, _AbortOutFile, Counters, Final_Counters) :-
	Mode == stats, 
	open(AbortInFile, read, Input),
	process_one_file1(States, Symbols, Dirs, Input, stats, Args, _Go, Counters, Final_Counters), !, 
	output_counters(Final_Counters), 
	close(Input). 

% filename(Base1, generate, States, Symbols, Dirs, Type, Mode, 1, Name, File), 
filename(Base, Dir, States, Symbols, Dirs, Style, Type, Mode, Start, RealName, File) :-

        % Dependence on Style is this: if Style = abs, no change. Otherwise put "rel" in the right spot ... 

    	number_string(States,S1), number_string(Symbols,S2), number_string(Dirs,S3), number_string(Start,S4), 
	% format("Dir is ~k, Type is ~k~n", [Dir,Type]), 
	typecode(Dir, Type, T1), modecode(Dir, Mode, T2), extracode(Dir, Mode, Extra), precode(Dir, Mode, Pre), stylecode(Dirs, Style, StyleCode), 
	% format("Appending 0 ... T1 is ~s~n", [T1]), 
        % format("T2 is ~s~n", [T2]),  ttyflush,
        % format("S1 is ~s~n", [S1]),  ttyflush,
	% format("S2 is ~s~n", [S2]),  ttyflush,
	% format("S3 is ~s~n", [S3]),  ttyflush, 
	string_concat(S1,S2,Temp01), string_concat(Temp01, S3, Temp11), string_concat(Temp11, StyleCode, Temp1), 
	% format("Appended~n", []), format("~s ", [T1]), format("~s ~n", [T2]), 
	string_concat(T1, T2, Temp2), 
	% format("Appended 2~n", []),
	% format("Temp1 is ~s~n", [Temp1]),  ttyflush,
	% format("Temp2 is ~s~n", [Temp2]),  ttyflush, 
	% format("Appending 1 ... ~n", []), ttyflush, 
        string_concat(Pre, "busybeaver", Prefix), 
	% format("Appending 2 ...Prefix is ~s~n", [Prefix]),  ttyflush, 
        % format("Temp1 is ~s~n", [Temp1]), 
        % format("Temp2 is ~s~n", [Temp2]), 
 	string_concat(Prefix, Temp1, Temp12), string_concat(Temp12, Temp2, Temp3),
	% format("Appending 3 ... Base is ~s~n", [Base]),  ttyflush, 
	% format("Temp3 is ~s~n", [Temp3]), 
	string_concat(Base, Temp3, Name),
	% format("Appending 4 ... Name is ~s~n", [Name]),  ttyflush, 
        partcode(Mode, S4, Temp45),
	string_concat(Name, Temp45, Temp4), 
	% format("Appending 5 ... Temp4 is ~s~n", [Temp4]), ttyflush, 
	% format("Extra is ~s~n", [Extra]), 
	string_concat(Temp4, Extra, Temp9), string_concat(Temp9, ".pl", RealName), 
	% format("Appending 6 ... RealName is ~s~n", [RealName]), 
	atom_codes(File, RealName).

checkmax(List, M, Ones, Hops, NewList) :-
	\+ member(max(Ones, _, _), List), !, 
	append([max(Ones, M, Hops)], List, NewList), !. 
checkmax(List, _M, Ones, Hops, List) :-
	member(max(Ones, _M1, H1), List),
	H1 >= Hops, !.
checkmax(List, M, Ones, Hops, NewList) :-
	member(max(Ones, M1, H1), List),
	H1 < Hops,!, 
	delete(List, max(Ones, M1, H1), NL),
	append([max(Ones, M, Hops)], NL, NewList), !. 

checkmin(List, M, Ones, Hops, NewList) :-
	\+ member(min(Ones, _, _), List),!, 
	append([min(Ones, M, Hops)], List, NewList),!. 
checkmin(List, _M, Ones, Hops, List) :-
	member(min(Ones, _M1, H1), List),
	H1 =< Hops, !.
checkmin(List, M, Ones, Hops, NewList) :-
	member(min(Ones, M1, H1), List),
	H1 > Hops,!, 
	delete(List, min(Ones, M1, H1), NL),
	append([min(Ones, M, Hops)], NL, NewList), !.

basename(Name, BaseName) :- append(BaseName, Suffix, Name), append("-", _, Suffix). 

% Utilities

append(W,X,Y,Z) :- append(W,X,T), append(T,Y,Z). 

bbinternalprint(Pred, N, M, O, H, Status) :-
	format("~k(~d,[", [Pred,N]),!, 
	printint(M), !, 
	format("],~d,~d,", [O,H]),!, 
	write(Status), !,  
	format(").~n", []), !. 

sort_records([], []). 
sort_records(List, List) :- length(List, 1). 
sort_records(List, SortedList) :-
      length(List, N), N >= 2, 
      divide(List, First, Second),
      sort_records(First, Fs),
      sort_records(Second, Ss),
      merge_records(Fs, Ss, SortedList).

merge_records([], Ys, Ys).
merge_records(Ys, [], Ys).

merge_records([S1|Fs], [S2|Ss], [S1|Ys]) :- 
      less_equal(S1, S2), merge_records(Fs, [S2|Ss], Ys).

merge_records([S1|Fs], [S2|Ss], [S2|Ys]) :- 
      \+ less_equal(S1, S2), merge_records([S1|Fs], Ss, Ys).

divide(List, First, Second) :-
      length(List, N), Half is N // 2, 
      length(First, Half), 
      append(First, Second, List).

less_equal(max(O1,_,_), min(O2,_,_)) :- O1 < O2. 
less_equal(min(O1,_,_), max(O2,_,_)) :- O1 < O2. 
less_equal(min(O1,_,_), min(O2,_,_)) :- O1 < O2. 
less_equal(max(O1,_,_), max(O2,_,_)) :- O1 < O2. 
less_equal(min(O1,_,_), max(O2,_,_)) :- O1 == O2. 

output_records([]) :- !.
output_records([max(O, M, H)|Rest]) :- 
	!, format("% ", []), bbinternalprint(maximum, 5, M, O, H, halts),
	output_records(Rest).
output_records([min(O, M, H)|Rest]) :- 
	!, format("% ", []), bbinternalprint(minimum, 5, M, O, H, halts),
	output_records(Rest).

printint([]) :- !. 
printint([A]) :- format("~k", [A]), !. 
printint(Arg) :- Arg = [A1|Temp], Temp = [A2|Rest], !, format("~k,", [A1]), !, printint([A2|Rest]).

% bbsortout(Pred, N, M) :-
% 	format("~k(~d, [", [Pred,N]),
% 	sortmachine(N, a, 0, [], M, M1), !, 
% 	printint(M1),
% 	format("]).~n", []).

sortmachine(_N, _States, _Symbols, _State, _Input, Done, [], M) :- reverse(Done, M),!. 
sortmachine(N, States, Symbols, State, Input, Done, Todo, Result) :-
	length(Todo, T), T > 0,
	member(t(State, Input, Output, Dir, NewState), Todo), !, 
	% format("% Found~n", []), 
	delete(Todo, t(State, Input, Output, Dir, NewState), Rest),
	% format("% Incrementing ~k ~k~n", [State,Input]), 
	(Rest \== [] -> increment(States, Symbols, State, Input, NS, NI); (NS = State, NI = Input) ), !, 
	% format("% Incremented~n", []), 
	sortmachine(N, States, Symbols, NS, NI, [t(State, Input, Output, Dir, NewState)|Done], Rest, Result).

sortmachine(N, States, Symbols, State, Input, Done, Todo, Result) :-
	length(Todo, T), T > 0,
	\+ member(t(State, Input, _Output, _Dir, _NewState), Todo), !, 
	% format("% Not found~n", []), 
	(Todo \== [] -> increment(States, Symbols, State, Input, NS, NI); (NS = State, NI = Input) ), !,
	% format("% Incremented~n", []), 
	sortmachine(N, States, Symbols, NS, NI, Done, Todo, Result).

padmachine(States, Symbols, _Dirs, M, PadM) :-
        length(M, L), L is States * Symbols, !, PadM = M. 
padmachine(States, Symbols, Dirs, M, PadM) :-
        length(M, L), L < States * Symbols, !, 
	states_list(States, StatesList), 
	symbols_list1(Symbols, SymbolsList), 
	once( missing(StatesList, SymbolsList, M, S1, Sym1) ), halt_state(Halt), 
	append(M, [t(S1, Sym1, Sym1, r, Halt)], NewM),
	padmachine(States, Symbols, Dirs, NewM, PadM),!. 

increment(_States, Symbols, State, Symbol, State, NSym) :-
    % If we can increment the symbol, do it ....
    NSym is Symbol+1, 
    symbols_list1(Symbols, List), member(NSym, List), !.

increment(States, _Symbols, State, _Symbol, NState, 0) :-
    % Otherwise symbol is 0 and take the next state (if it exists)
    states_list(States, List), 
    next_state(State, NState), !, 
    member(NState, List). 

convert_machine(marxen, States, Symbols, Dirs, machine(List, _, _), NewM) :- convert_machine(States, Symbols, Dirs, List, NewM). 
convert_machine(marxen, States, Symbols, Dirs, M, NewM) :- M \== machine(_,_,_), convert_machine0(States, Symbols, Dirs, M, NewM).
convert_machine(Format, _States, _Symbols, _Dirs, _M, NewM) :- \+ member(Format, [marxen]), NewM = "". 

convert_machine0(States, Symbols, Dirs, M, NewM) :- 
      % format("% Padding~n", []), 
      padmachine(States, Symbols, Dirs, M, PadM), 
      % sortmachine(Symbols, a,0,[], PadM, SortM),
      % format("% Sorting ", []), writeln(PadM), 
      sortmachine(0, States, Symbols, a, 0, [], PadM, SortM),
      % format("% Converting~n", []), 
      convert_machine1(SortM, [], NewM). % NewM is a string representing the Marxen representation of the machine.

convert_machine1([], SoFarNewM, SoFarNewM).
convert_machine1([t(_S,_I,O,D,NS)|Rest], SoFarNewM, NewM) :-
	atom_codes(O, NewO), 
	atom_codes(D, NewD),
	atom_codes(NS, NewNS), 
	append(NewO,NewD,Temp), append(Temp, NewNS, NewTrans), 
	append(SoFarNewM, NewTrans, NewSoFarNewM),
	convert_machine1(Rest, NewSoFarNewM, NewM). 

duplicates(InFile) :-
	atom_codes(InFile, I), 
	append(Name, ".pl", I),
	append(Name, "-duplicates.pl", OutName),
	% string2term(OutName, OutFile),!, 
	atom_codes(OutFile, OutName),!, 
	open(InFile, read, Input), 
	tell(OutFile), 
        read(Input, Term1),
        copies(Term1, Input),
        close(Input),
        told.

copies(end_of_file, _).
copies(Current, Input) :-
        Current \== end_of_file, 
        read(Input, Term2),
        process_copy(Current, Term2),!, 
        copies(Term2, Input).

process_copy(_, end_of_file).
process_copy(Term1, Term2) :-
        Term1 = bb(N1, M1, O1, H1, S1), 
        Term2 = bb(N2, M2, O2, H2, S2), 
        M1 = M2, !, 
        format("% Duplicates:~n", []), 
        bbinternalprint(bb, N1, M1, O1, H1, S1), 
        bbinternalprint(bb, N2, M2, O2, H2, S2), 
        format("%%%%%~n", []), 
        true. 
process_copy(Term1, Term2) :-
        Term1 = bb(_N1, M1, _O1, _H1, _S1), 
        Term2 = bb(_N2, M2, _O2, _H2, _S2), 
        M1 \= M2, !, 
        %format("% Non-duplicates:~n", []), 
        %bbinternalprint(bb, N1, M1, O1, H1, S1), 
        %bbinternalprint(bb, N2, M2, O2, H2, S2), 
        %format("%%%%%~n", []), 
        true. 
process_copy(Term1, Term2) :-
        (Term1 \= bb(_N1, _M1, _O1, _H1, _S1); Term2 \= bb(_N2, _M2, _O2, _H2, _S2)).

% [abort,abort(_),unknown,going,going(_),halts,meander,blank,loops,loops(cycle),loops(cycle(_)),loops(road_runner),loops(induction),pseudo,pseudo(_)]), 

check_going(Going, N, Machine, Ones, Hops, going) :-	!, write(Going, bb(N, Machine, Ones, Hops, going)),    put_char(Going, '.'), nl(Going), !. 
check_going(Going, N, Machine, Ones, Hops, going(S)) :- !, write(Going, bb(N, Machine, Ones, Hops, going(S))), put_char(Going, '.'), nl(Going), !. 
check_going(Going, N, Machine, Ones, Hops, unknown) :-  !, write(Going, bb(N, Machine, Ones, Hops, unknown)),  put_char(Going, '.'), nl(Going), !. 
check_going(_Going, _N,_Machine, _Ones, _Hops, Status) :- member(Status, [abort,abort(_),halts,meander,blank,loops,loops(_),pseudo,pseudo(_)]), !.

typecode(_, free, "free").
typecode(_, all, "all").
typecode(_, tnf, "tnf").
% typecode(_, newtnf, "newtnf").

modecode(output, raw, "raw").
modecode(output, analyse, "").
modecode(output, refine, "").
modecode(output, pseudouni, "").
modecode(output, stats, "").
modecode(output, status, "").
modecode(output, abort, "").
modecode(output, convert(F,N), Name) :- atom_codes(F, FName), atom_codes(N, NName), string_concat(FName, NName, Temp), string_concat(Temp, "raw", Name). 
modecode(input, raw, "raw").
modecode(input, analyse, "raw").
modecode(input, refine, "").
modecode(input, status, "").
modecode(input, pseudouni, "raw").
modecode(input, stats, "raw").
modecode(input, number, "raw").
modecode(input, abort, "raw").
modecode(input, convert(_,_), "raw").
modecode(generate, _, "raw").

stylecode(2, abs, ""). 
stylecode(2, rel, "rel"). 
stylecode(Dirs, abs, "abs") :- Dirs > 2. 
stylecode(Dirs, rel, "rel") :- Dirs > 2. 

extracode(input, M, "") :- \+ member(M, [refine, status]).
extracode(input, refine, "-going").
extracode(input, status, "-out").
extracode(output, M, "") :- \+ member(M, [abort, refine, status]).
extracode(output, refine, "-going-out").
extracode(output, status, "-out").
extracode(output, abort, "-out"). % ~~~??
extracode(generate, _, ""). 

mode_status(status, output). 
mode_status(Mode, input) :- Mode \= status. 
    
precode(_, input, "").
precode(_, output, "").
precode(_, number, "").
precode(_, analyse, "").
precode(_, abort, "").
precode(_, refine, "").
precode(_, stats, "").
precode(_, status, "").
precode(_, convert(_,_), "").
precode(_, pseudoni, "").
precode(_, raw, "temp-"). 

partcode(Mode, S4, Code) :- Mode \== abort, string_concat("-part", S4, Code). 
partcode(abort, _, "abort"). 

summary_name(analyse, "analyse").
summary_name(abort, "abort").
summary_name(refine, "refine").
summary_name(raw, "").
summary_name(number, "").
summary_name(pseudouni, "pseudouni").
summary_name(stats, "stats").
summary_name(status, "status").
summary_name(convert(_,_), "convert").

% Parameters. These need to be rationalised!

compress_length(10). % Was 5, but then found long(4,1,M) and then example(3,M). 

beaver(input,  "C:/busybeaver/Data/Raw/"). % Directory for input
beaver(output, "C:/busybeaver/Data/Results/"). % Directory where results get written. 

which_dir(Mode,States,Symbols,Dirs,Style,Type,Directory) :- member(Mode,[refine,status]), directory(output,States,Symbols,Dirs,Style,Type,Directory).
which_dir(Mode,States,Symbols,Dirs,Style,Type,Directory) :- \+ member(Mode, [refine, status]), directory(input,States,Symbols,Dirs,Style,Type,Directory).

directory(Mode, States, Symbols, Dirs, _Style, Type, Directory) :-
        Dimension is States * Symbols * Dirs, 
	((Dimension < 16); (Dimension == 16, Type \== all)), 
	beaver(Mode, Base), Directory = Base. 
directory(Mode, States, Symbols, Dirs, Style, Type, Directory) :-
        Dimension is States * Symbols * Dirs, 
	((Dimension > 16);(Dimension == 16, Type == all)), % Use subdirectory for larger cases. 16 is file unless Type is all
	beaver(Mode, Base), 
	number_string(States,S1), number_string(Symbols,S2), number_string(Dirs,S3),
	% append(S1,S2,S3,Temp1), 
	% append("busybeaver", Temp1, "/", Temp3),
	% append(Base, Temp3, Directory).
	(Style = rel -> string_concat(S3,"rel", S4); S4 = S3), 
	string_concat(S1,S2,Temp0), string_concat(Temp0, S4, Temp1),
	string_concat("busybeaver", Temp1, Temp2),
	string_concat(Temp2, "/", Temp3),
	string_concat(Base, Temp3, Directory). 

ensure_exists(Directory) :- atom_codes(Real, Directory), exists_directory(Real). 
ensure_exists(Directory) :- atom_codes(Real, Directory), \+ exists_directory(Real), make_directory(Real). 

compare(File1, File2) :-
	open(File1, read, Input1),
	open(File2, read, Input2),

        read(Input1, Term1),
        read(Input2, Term2),

	process_compare(Term1, Term2, 1, Input1, Input2), 

	close(Input1),
	close(Input2),
	true. 

process_compare(end_of_file, end_of_file, N, _Input1, _Input2) :- format("Both done after ~d lines~n", [N]).
process_compare(end_of_file, Term2, N,_Input1, _Input2) :-
        Term2 \== end_of_file,
	format("File 1 ended first at line ~d~n", [N]), 
	true. 

process_compare(Term1, end_of_file, N,_Input1, _Input2) :-
        Term1 \== end_of_file,
	format("File 2 ended first at line ~d~n", [N]), 
	true. 

process_compare(Term1, Term2, N, _Input1, _Input2) :-
        Term1 \== end_of_file, Term2 \== end_of_file, 
	\+ (Term1 = bb(N, M, _Ones1, _Hops1, _Status1), Term2 = bb(N, M, _Ones2, _Hops2, _Status2)),!, 
	format("Mismatch at line~d: ~n", [N]), write(Term1), nl, write(Term2), nl, 
	true. 

process_compare(Term1, Term2, N, Input1, Input2) :-
        Term1 \== end_of_file, Term2 \== end_of_file, 
	Term1 = bb(N, M, Ones1, Hops1, Status1), Term2 = bb(N, M, Ones2, Hops2, Status2), !, 
        % ( (0 is N mod 10000) -> (format("Line ~d: ", [N]), write(Term1), format(" and~nLine ~d: ", [N]), write(Term2), nl) ; true), 
        % ( (N > 999990) -> (format("Line ~d: ", [N]), write(Term1), format(" and~nLine ~d: ", [N]), write(Term2), nl) ; true), 
	\+ (Ones1 = Ones2, Hops1 = Hops2, Status1 = Status2), 
	format("Different results at line ~d: ~d ~d ~k versus ~d ~d ~k~n", [Ones1,Hops1,Status1,Ones2,Hops2,Status2]), 
        read(Input1, NewTerm1), read(Input2, NewTerm2), N1 is N+1, 
	process_compare(NewTerm1, NewTerm2, N1, Input1, Input2),
	true. 

process_compare(Term1, Term2, N, Input1, Input2) :-
        Term1 \== end_of_file, Term2 \== end_of_file, 
	\+ (
	    Term1 = bb(N, M, Ones1, Hops1, Status1), Term2 = bb(N, M, Ones2, Hops2, Status2), \+ (Ones1 = Ones2, Hops1 = Hops2, Status1 = Status2) 
        ), 
        read(Input1, NewTerm1), read(Input2, NewTerm2), N1 is N+1, 
	process_compare(NewTerm1, NewTerm2, N1, Input1, Input2),
	true. 

special_check(File) :-
	open(File, read, Input),
	initialise_counters(Counters), 
	read(Input, Term),
	stats_check(Input, Term, Counters, FinalCounters), % Or others .... 
	output_counters(FinalCounters), 
	close(Input).

check_terms1(N, _, end_of_file) :- format("Number of terms found: ~d~n", [N-1]).
check_terms1(N, Input, Term) :- 
	Term \== end_of_file,
	Term = bb(_, _M, _Ones, _Hops, _Status),!, 
	N1 is N+1, 
	read(Input, NewTerm),
	check_terms1(N1, Input, NewTerm).
check_terms1(N, Input, Term) :- 
	Term \== end_of_file,
	Term \= bb(_, _M, _Ones, _Hops, _Status),!,
	format("Non-term found at ~d: ", [N]), write(Term), nl, 
	read(Input, NewTerm),
	check_terms1(N, Input, NewTerm).

meander_check1(_, end_of_file) :- !. 
meander_check1(Input, Term) :- 
	Term \== end_of_file,
	Term = bb(_, _M, _Ones, _Hops, Status), \+ member(Status, [meander]), !, 
	read(Input, NewTerm),
	meander_check1(Input, NewTerm).
meander_check1(Input, Term) :- 
	Term \== end_of_file,
	Term = bb(N, M, _Ones, _Hops, Status), member(Status, [meander]), !, 
	emulate_bb(M, 10000, flex, [loop,escape,blank,otter], _NewOnes, _NewHops, NewStatus, _NewOutputs), 
	format("Machine ~d: ",[N]), write(M), format(" meander and ", []), write(NewStatus), nl, 

	read(Input, NewTerm),
	meander_check1(Input, NewTerm).

meander_check2(_, end_of_file) :- !. 
meander_check2(Input, Term) :- 
	Term \== end_of_file,
	Term = bb(N, M, _Ones, _Hops, Status), !, 

	( (meandering(M), member(Status, [halts])) -> (format("Machine ~d: ",[N]), write(M), format(" meander and ", []), write(Status), nl); true), 

	read(Input, NewTerm),
	meander_check2(Input, NewTerm).

induction_check(Number, Max, Total, _Input, end_of_file) :- format("Number is ~d, Max is ~d, Average is ~1f~n", [Number, Max, Total/Number]), true. 
induction_check(Number, Max, Total, Input, Term) :-
	Term \== end_of_file,
	Term = bb(_, _M, _Ones, _Hops, Status),
	\+ member(Status, [loops(induction(_,_,_))]), 
	read(Input, NewTerm),
	induction_check(Number, Max, Total, Input, NewTerm).
induction_check(Number, Max, Total, Input, Term) :-
	Term \== end_of_file,
	Term = bb(_, _M, _Ones, Hops, Status),
	member(Status, [loops(induction(_Config,_Diffs,_Hopses))]), 
	
	Number1 is Number + 1,
	NewMax is max(Hops, Max), 
	NewTotal is Total + Hops, 
	read(Input, NewTerm),
	induction_check(Number1, NewMax, NewTotal, Input, NewTerm).


stats_check(_Input, end_of_file, Counters, Counters). 
stats_check(Input, Term, Counters, FinalCounters) :-
	Term \== end_of_file,
	Term = bb(_, M, Ones, Hops, Status),
	update_counters(M, Ones, Hops, Status, Counters, NewCounters), 
	read(Input, NewTerm),
	stats_check(Input, NewTerm, NewCounters, FinalCounters).

final(File) :-
	open(File, read, Input),
	read(Input, Term),tell('Output2.pl'), 
	final_few(Input, Term),
	close(Input).

final_few(_Input, end_of_file).
final_few(Input, Term) :-
	Term \== end_of_file,
	Term = bb(Number, M, _, _, Status),
	format("~d: ~k: ", [Number, Status]), write(M), nl, 
	emulate_bb(M, 1000, flex, [otter,otrace,trace(980),final], _Ones, _Hops, _NewStatus, _Outputs), 
	format("Done ~n", []), 
	read(Input, NewTerm),
	final_few(Input, NewTerm).
    
