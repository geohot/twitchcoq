create(States, Symbols, Dirs, Type) :- create(States, Symbols, Dirs, abs, Type). % For backwards compatibility ... 
create(States, Symbols, Dirs, Style, Type) :-
    format("% Creating ~d ~d ~d ~k ~k case ... ", [States, Symbols, Dirs, Style, Type]), 
    get_time(T1),
    create_machines(States, Symbols, Dirs, Style, Type), !, 
    get_time(T2), Time is T2-T1, 
    format("took ~2f seconds~n", [Time]), flush_output, !. 

create_bilby :-
    create(2,2,2,tnf), !, 
    create(3,2,2,tnf), !, 
    create(2,3,2,tnf), !, 
    true. 
create_elephant :-
    create(4,2,2,tnf), !, 
    create(2,4,2,tnf), !, 
    true. 
create_whale :-
    create(3,3,2,tnf), !, flush_output, 
    create(5,2,2,tnf), !, flush_output, 
    create(2,5,2,tnf), !, flush_output, 
    true. 
create_duck :-
    create(6,2,2,tnf), !, flush_output, 
    create(4,3,2,tnf), !, flush_output, 
    create(3,4,2,tnf), !, flush_output, 
    create(2,6,2,tnf), !, flush_output, 
    true. 

create_bilby_extra :- 
    create(2,2,2,free), !, 
    create(3,2,2,free), !, 
    create(2,3,2,free), !, 
    create(2,2,2,all),  !, 
    create(3,2,2,all),  !, 
    create(2,3,2,all),  !, 
    true. 
create_elephant_extra :- create(4,2,2,free), create(2,4,2,free). 

create622 :- tell('622.txt'), create(6,2,2,tnf), told.
create432 :- tell('432.txt'), create(4,3,2,tnf), told.
create342 :- tell('342.txt'), create(3,4,2,tnf), told.
create262 :- tell('262.txt'), create(2,6,2,tnf), told.

papertable :- tell('papertable.txt'), create_bilby, create_bilby_extra, create_elephant, create_elephant_extra, told.
whaletable :- tell('whaletable.txt'), create_whale, told. 
bag :- tell('creation.txt'), create_bilby, create_elephant, create_whale, told.
extra :- tell('extra.txt'), create_bilby_extra, create_elephant_extra, told. 

batch :-
    create_machines(5,2,2,abs,tnf),
    create_machines(2,5,2,abs,tnf), 
    process(2,4,2,tnf,analyse,[]), 
    process(3,3,2,tnf,analyse,[]),
    process(5,2,2,tnf,analyse,[]),
    process(2,5,2,tnf,analyse,[]),
    true. 

bilby :-
    process(2,2,2,tnf,analyse,[]), 
    process(3,2,2,tnf,analyse,[]), 
    process(2,3,2,tnf,analyse,[]),
    true. 

bilby_all :-
    process(2,2,2,tnf,analyse,[]), 
    process(2,2,2,free,analyse,[]), 
    process(2,2,2,all,analyse,[]), 
    process(3,2,2,tnf,analyse,[]), 
    process(3,2,2,free,analyse,[]), 
    process(3,2,2,all,analyse,[]), 
    process(2,3,2,tnf,analyse,[]),
    process(2,3,2,free,analyse,[]),
    process(2,3,2,all,analyse,[]),
    true. 

elephant :-
    process(4,2,2,tnf,analyse,[]), 
    process(2,4,2,tnf,analyse,[]), 
    true. 

elephant_free :-
    process(4,2,2,free,analyse,[]), 
    process(2,4,2,free,analyse,[]), 
    true. 

whale :-
    process(3,3,2,tnf,analyse,[nomonster]), 
    process(5,2,2,tnf,analyse,[nomonster]), 
    process(2,5,2,tnf,analyse,[nomonster]), 
    true. 

convert_bilby :-
    process(2,2,2,tnf,convert(marxen,numbered), []),
    process(3,2,2,tnf,convert(marxen,numbered), []),
    process(2,3,2,tnf,convert(marxen,numbered), []),
    true. 
convert_elephant :-
    process(4,2,2,tnf,convert(marxen,numbered), []),
    process(2,4,2,tnf,convert(marxen,numbered), []),
    true. 
convert_whale :-
    process(3,3,2,tnf,convert(marxen,numbered), []),
    process(5,2,2,tnf,convert(marxen,numbered), []),
    process(2,5,2,tnf,convert(marxen,numbered), []),
    true. 



 % tell('SixTwentyTwo'), time(test6(22,6,[otter], Ones, Hops, Status, Outputs)), told.
 % tell('SixTwentyOne'), time(test6(21,6,[otter], Ones, Hops, Status, Outputs)), told.
 % tell('SixTwenty'), time(test6(20,4,[otter], Ones, Hops, Status, Outputs)), told.
 % tell('SixNineteen'), time(test6(19,6,[otter], Ones, Hops, Status, Outputs)), told.

label(N,M,L) :- format("Monster ~d (~d x ~d): ", [N,M,L]).

test(Num, Bound, Macro) :- 
    time(( monster(Num,M), emulate_bb(M,Bound,macro(Macro), [otter], _, _, _, _)  )).

test1(Num, Bound, Macro) :- 
    get_time(T1),
    monster(Num,M), emulate_bb(M,Bound,macro(Macro), [otter,final], _, _, _, _),
    % format("Emulation Done ... ", []), flush_output, 
    get_time(T2), Time is T2-T1, 
    format("Took ~f seconds~n", [Time]). 

test2(Num, Bound, Macro, Options) :- 
    get_time(T1),
    monster(Num,M), emulate_bb(M,Bound,macro(Macro), Options, _, _, _, _),
    get_time(T2), Time is T2-T1, 
    format("Took ~f seconds~n", [Time]). 

test3(Num, Bound) :- 
    get_time(T1),
    monster(Num,M), emulate_bb(M,Bound,flex, [otter,final,optcom], _, _, _, _),
    get_time(T2), Time is T2-T1, 
    format("Took ~f seconds~n", [Time]). 

test4(Num, Bound, Options) :- 
    get_time(T1),
    monster(Num,M), emulate_bb(M,Bound,flex, Options, _, _, _, _),
    get_time(T2), Time is T2-T1, 
    format("Took ~f seconds~n", [Time]). 

test5(Num, _Bound) :- 
    get_time(T1),
    monster(Num,M), analyse(M, 0, 0, going, [], Ones, Hops, Status, _Outputs), 
    get_time(T2), Time is T2-T1, 
    format("Status: ", []), write(Status), format(" Ones: ~d Hops: ~d~n", [Ones, Hops]), 
    format("Time: ~f seconds~n", [Time]). 





% monster(30,M), emulate_general(M, config([grp([3,3],v(1,0)), grp([0,1],1)], b, grp([3,3],v(1,0)),l, []), 100, macro(2), [target([config([grp([3,3],v(1,5)), grp([0,1],1)],b,grp([3,3],v(1,-4)), l, [])])], [trace], Hops, Status, Outputs) 
