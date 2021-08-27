%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%														   %
%  DOCUMENTO COM O ALGORITMO DE INFERENCIA DE TIPOS FINAL  %
%														   %
% 1 - TERM EXPANSION DO INPUT							   %
%														   %
% 2 - GERACAO DE CONSTRAINTS							   %
%														   %
% 3 - RESOLUCAO DE CONSTRAINTS							   %
%														   %
%   - RESOLVER IGUALDADES								   %
%	- RESOLVER INEQUACOES								   %
%	- SIMPLIFICAR SUBSTITUICAO NAS TYPEDEFS				   %
%	- OBTER TYPEDEFS FINAIS								   %
%														   %
% 4 - OPCIONAL CLOSURE									   %
%														   %
% 5 - IMPRESSAO DO OUTPUT								   %
%														   %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% 1 - TERM EXPANSION DO INPUT %%

:- recorda(frame,[newvar,0],_).
:- recorda(data,[(tnam(num,[]),[basetype(int),basetype(float)])],_).
:- dynamic typing_flag/1.
:- dynamic basetype_flag/1.
:- dynamic closure_flag/1.
:- dynamic list_flag/1.
:- op(1200,yfx,type).
:- ['Generation.pl','Solver.pl','New_Better_Closure.pl','PP.pl'].

typing_flag(false).
basetype_flag(on).

switch(Initial,Final) :-
	retract(typing_flag(Initial)),
	assert(typing_flag(Final)).

typed_compile(F) :-
    switch(_,true),
    ensure_loaded(F),
    switch(_,false),
    findall(X, clause(X),List),
    solve(List).
    
solve(List) :- (list_flag(on) -> 
			recorda(data,[(tnam(list,[VAR]),[func([],[]),func('[|]',[VAR,tnam(list,[VAR])])])],_);
			true),
			findall(X,recorded(data,[X],_),Data),
			(length(Data,N), N > 1 -> assert(closure_flag(on));
			true -> true),
			solve_for_each(List),
			print_data(Data),
			retractall(clause(_)),
			findall(X,recorded(data,_,X),L),
			eraseall(L).

eraseall([]).
eraseall([R|Rs]) :- erase(R), eraseall(Rs).

solve_for_each([]).
solve_for_each([Cl|Cls]) :-
					Cl =.. [cl,Head,_],
					(constraint_gen(Cl,_,Env,Eq,Ineq,TypeDef); writeln('Constraint Generation failed on clause: '), write(Cl), fail),!,
					% print_each(Env), nl, print_each(Eq), nl, print_each(Ineq), nl, print_each(TypeDef), nl,
					constraint_solve(Eq,Ineq,TypeDef,FinalDef),!,
					% print_each(FinalDef), nl,
					print_solution(Head,Env,FinalDef),!,
					solve_for_each(Cls).

term_expansion(end_of_file,end_of_file) :- switch(_,false).

term_expansion((:- closure_flag(X)),notclause) :-
	assert(closure_flag(X)).

term_expansion((:- list_flag(X)),notclause) :-
	assert(list_flag(X)).

term_expansion((:- basetype_flag(X)),notclause) :-
	retractall(basetype_flag(_)),
	assert(basetype_flag(X)).

term_expansion((:- type B = C),notclause) :-
	B =.. [Name | Args], NAME =.. [tnam, Name, Args],
	type_def(C,B,LIST),
	recorda(data,[(NAME,LIST)]).

type_def((A + B),Type,LIST) :-
	type_def(B,Type,Temp),
	type_term(A,Type,NA),
	LIST = [NA|Temp].

type_def((A),Type,[NA]) :-
	type_term(A,Type,NA).

type_term(X,Type,Output) :-
	var(X) -> Output = X;
	X == Type -> Type =.. [Name | Args], Output =.. [tnam, Name, Args];
	X =.. [F | Args],
	type_terms(Args, Type, NArgs),
	Output =.. [func, F, NArgs].

type_terms([],_,[]).

type_terms([A|As],Type,[B|Bs]) :-
	type_term(A,Type,B),
	type_terms(As,Type,Bs).

term_expansion((H:-T), O) :-
    typing_flag(true),
    H =.. [Pred | Args],
    NH =.. [pred, Pred, Args],
    body(T,NT),
    O = cl(NH,NT),!,
    assert(clause(O)).

body((A;B),Output) :-
	body(A,NA),
	body(B,NB),
	NA =.. [or, Args1],
	NB =.. [or, Args2],
	append(Args1,Args2,FArgs),
	Output =.. [or, FArgs].
	
body((A),Output) :-
	single_body(A,NA),
	Output =.. [or , [NA]].
	
single_body((A,B),Output) :- !,
	single_body(A,NA),
	single_body(B,NB),
	NA =.. [and, Args1],
	NB =.. [and, Args2],
	append(Args1,Args2,FArgs),
	Output =.. [and, FArgs].
	
single_body(A,Output) :-
	single_call(A,New),
	Output =.. [and , [New]].

single_call((A = B),Output) :-
	term(A,NA),
	term(B,NB),
	Output =.. [equals, NA, NB].

single_call((A < B),Output) :-
	get_vars(A,VarsA),
	get_vars(B,VarsB),
	append_without_repeating(VarsA,VarsB,Vars),
	Output =.. [pred, '<', Vars].

single_call((A =< B),Output) :-
	get_vars(A,VarsA),
	get_vars(B,VarsB),
	append_without_repeating(VarsA,VarsB,Vars),
	Output =.. [pred, '=<', Vars].

single_call((A > B),Output) :-
	get_vars(A,VarsA),
	get_vars(B,VarsB),
	append_without_repeating(VarsA,VarsB,Vars),
	Output =.. [pred, '>', Vars].

single_call((A >= B),Output) :-
	get_vars(A,VarsA),
	get_vars(B,VarsB),
	append_without_repeating(VarsA,VarsB,Vars),
	Output =.. [pred, '>=', Vars].

single_call(Call,Output) :-
	Call =.. [Pred | Args],
	terms(Args,NArgs),
	Output =.. [pred, Pred, NArgs].

term(X, Output) :-
	var(X) -> recorded(frame,[newvar, VN],_), X = myvar(VN), VN1 is VN + 1, recorda(frame,[newvar, VN1],_), Output = X;
	X =.. [myvar , _] -> Output = X;
	X =.. [F | Args],
	terms(Args, NArgs),
	Output =.. [func, F, NArgs].

terms([],[]).

terms([A|As],[B|Bs]) :-
	term(A,B),
	terms(As,Bs).

get_vars(X,Output) :-
	var(X) -> recorded(frame,[newvar, VN],_), X = myvar(VN), VN1 is VN + 1, recorda(frame,[newvar, VN1],_), Output = [X];
	X =.. [myvar , _] -> Output = [X].

get_vars(A + B,Output) :-
	get_vars(A,VarsA),
	get_vars(B,VarsB),
	append_without_repeating(VarsA,VarsB,Output).

get_vars(A - B,Output) :-
	get_vars(A,VarsA),
	get_vars(B,VarsB),
	append_without_repeating(VarsA,VarsB,Output).

get_vars(A * B,Output) :-
	get_vars(A,VarsA),
	get_vars(B,VarsB),
	append_without_repeating(VarsA,VarsB,Output).

get_vars(A / B,Output) :-
	get_vars(A,VarsA),
	get_vars(B,VarsB),
	append_without_repeating(VarsA,VarsB,Output).

get_vars(A // B,Output) :-
	get_vars(A,VarsA),
	get_vars(B,VarsB),
	append_without_repeating(VarsA,VarsB,Output).

get_vars(_,[]).

print_each([]).
print_each([A|As]) :- write(A), nl, print_each(As).