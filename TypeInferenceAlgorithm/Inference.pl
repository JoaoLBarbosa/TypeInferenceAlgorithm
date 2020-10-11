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
%	- SIMPLIFICAR IGUALDADES							   %
%	- OBTER CONSTRAINTS FINAIS							   %
%														   %
% 4 - POSSIVEL CLOSURE									   %
%														   %
% 5 - IMPRESSAO DO OUTPUT								   %
%														   %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% 1 - TERM EXPANSION DO INPUT %%

:- recorda(frame,[newvar,0],_).
:- recorda(frame,[newtype,0],_).
:- dynamic typing_flag/1.
:- dynamic basetype_flag/1.
:- dynamic closure_flag/1.
:- dynamic list_flag/1.
:- dynamic data/1.
:- dynamic is_the_same/2.
:- dynamic already_compared/1.

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
			assertz(data(type(tnam(list,[VAR]),[func([],[]),func('[|]',[VAR,tnam(list,[VAR])])])));
			true),
			findall(X,data(X),Data),
			(length(Data,N), N > 0 -> assert(closure_flag(on));
			true -> true),
			solve_for_each(List,Data),
			print_data(Data),
			retractall(clause(_)),
			retractall(data(_)).

solve_for_each([],_).
solve_for_each([Cl|Cls],Data) :-
					Cl =.. [cl,Head,Body],
					constraint_gen(Cl,Data,Type,Env,Eq,Ineq),!,
					constraint_solve(Eq,Ineq,Solution),!,
					print_solution(Head,Env,Solution),!,
					solve_for_each(Cls,Data),
					recorda(frame,[newvar,0],_).

term_expansion(end_of_file,end_of_file) :- switch(_,false).

term_expansion((:- closure_flag(X)),notclause) :-
	assert(closure_flag(X)).

term_expansion((:- list_flag(X)),notclause) :-
	assert(list_flag(X)).

term_expansion((:- basetype_flag(X)),notclause) :-
	retractall(basetype_flag(_)),
	assert(basetype_flag(X)).

term_expansion((:- type -> B = C),notclause) :-
	B =.. [Name | Args], NAME =.. [tnam, Name, Args],
	type_def(C,B,LIST),
	assert(data(type(NAME,LIST))).

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
	NA =.. [or | Args1],
	NB =.. [or | Args2],
	append(Args1,Args2,FArgs),
	Output =.. [or | FArgs].
	
body((A),Output) :-
	single_body(A,NA),
	Output =.. [or , NA].
	
single_body((A,B),Output) :- !,
	single_body(A,NA),
	single_body(B,NB),
	NA =.. [and | Args1],
	NB =.. [and | Args2],
	append(Args1,Args2,FArgs),
	Output =.. [and | FArgs].
	
single_body(A,Output) :-
	single_call(A,New),
	Output =.. [and , New].

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
	Call =.. [is, A, B], !,
	get_vars(A,VarsA),
	get_vars(B,VarsB),
	append_without_repeating(VarsA,VarsB,Vars),
	Output =.. [pred,is,Vars].
	
single_call(Call,Output) :-
	Call =.. [Pred | Args],
	terms(Args,NArgs),
	Output =.. [pred, Pred, NArgs].

term(X, Output) :-
	var(X) -> recorded(frame,[newvar, VN],_), X = myvar(VN), VN1 is VN + 1, recorda(frame,[newvar, VN1],_), Output = X;
	X =.. [myvar , N] -> Output = X;
	X =.. [F | Args],
	terms(Args, NArgs),
	Output =.. [func, F, NArgs].

terms([],[]).

terms([A|As],[B|Bs]) :-
	term(A,B),
	terms(As,Bs).

get_vars(X,Output) :-
	var(X) -> recorded(frame,[newvar, VN],_), X = myvar(VN), VN1 is VN + 1, recorda(frame,[newvar, VN1],_), Output = [X];
	X =.. [myvar , N] -> Output = [X].

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





























%% 2 - GERACAO DE CONSTRAINTS %%

constraint_gen(X,Data,Type,Env,Eq,Ineq) :- (
					X = myvar(Y) -> gen_fresh_var(1,[Type]), Env = [(myvar(Y),Type)], Eq = [], Ineq = [];

					X = func(C,[]) -> basetype(C,Data,Type), Env = [], Eq = [], Ineq = [];

					X = func(F,Args) -> constraint_gen_args(Args,Data,Types,Envs,Eqs,Ineqs),
										cross_prod(Envs,Env),
										basetypefunc(F,Data,Temp,Name),
										(Temp = arit -> Type = Name, EqExtra = [], gen_arith(Types,NIneqs), append(Ineqs,[NIneqs],FIneqs);
										Temp = no_occurrence -> EqExtra = [], Type =.. [func, F, Types], FIneqs = Ineqs;
										Temp =.. [func, F, TempArgs] -> gen_eq_cons(Types,TempArgs,EqExtra), Type = Name, FIneqs = Ineqs),
										cup([EqExtra|Eqs],Eq), cup(Fneqs,Ineq);

					X = equals(T1,T2) -> constraint_gen(T1,Data,Type1,Env1,Eq1,Ineq1),
										constraint_gen(T2,Data,Type2,Env2,Eq2,Ineq2),
										Type = bool, cross_prod([Env1,Env2],Env),
										cup([[eq(Type1,Type2)],Eq1,Eq2],Eq), cup([Ineq1,Ineq2],Ineq);

					X = pred(Op,Args),
					(Op = '<'; Op = '>'; Op = is; Op = '=<'; Op = '>=') ->
										constraint_gen_args(Args,Data,Types,Envs,Eqs,Ineqs),
										cross_prod(Envs,Env), gen_arith(Types,AritCons),
										cup(Eqs,Eq), cup([AritCons|Ineqs],Ineq),
										Type = bool ;

					X = pred(P,Args) -> clause(cl(pred(P,Args1),Body)),
										constraint_gen(cl(pred(P,Args1),Body),Data,bool,EnvPrime,Eqs,Ineqs),
										constraint_solve(Eqs,Ineqs,NEqs),
										get_from_env(Args1,EnvPrime,TypesPrime), length(Args,N),
										gen_fresh_var(N,Vars), gen_fresh_type(N,Types),
										gen_subt_cons(Vars,Types,Ineq),
										rename_types(P,NEqs,Types,Eq), Type = bool,
										on_each(Args,Vars,Env);

					X = rec(pred(P,Args)) -> length(Args,N), gen_fresh_var(N,Types),
										on_each(Args,Types,Env), Eq = [],
										gen_predicate_tvar(P,1,N,PredTypes),
										gen_subt_cons(Types,PredTypes,Ineq);

					X =.. [and | Calls] -> length(Calls,NumerodeCalls),
										varied(Data,NumerodeCalls,[],Datas),
										constraint_gen_all(Calls,Datas,Envs,Eqs,Ineqs),
										cross_prod(Envs,Env), cup(Eqs, Eq),
										cup(Ineqs,Ineq), Type = bool ;

					X =.. [or | Bodies] -> length(Bodies,NumerodeBodies), varied(Data,NumerodeBodies,[],Datas),
										constraint_gen_all(Bodies,Datas,Envs,Eqs,Ineqs),
										cross_sum(Envs,Env,Sums), cup([Sums|Eqs], Eq),
										cup(Ineqs,Ineq), Type = bool ;

					X = cl(Head,Body) -> Head =.. [pred, P , Args], length(Args,N),
										mark_recursive(P,Body,NBody),
										constraint_gen(NBody,Data,bool,Env,Eqs,Ineq),
										get_from_env(Args,Env,Types),
										gen_predicate_tvar(P,1,N,PredTypes),
										(N = 0 -> NewEq = [];
										true -> gen_eq_cons(Types,PredTypes,NewEq)),
										append(NewEq,Eqs,Eq), Type = bool
					).

% Generates "fresh" type variables

gen_fresh_var(1,[NewVar]).
gen_fresh_var(N,[NewVar|OtherVars]) :- M is N - 1, gen_fresh_var(M,OtherVars).


% Generates "fresh" type names

gen_fresh_type(1,[NewType]) :-
					recorded(frame,[newtype,Number],_), NewType = tvar(Number,Number,Number),
					N is Number + 1, recorda(frame,[newtype,N],_).
gen_fresh_type(N,[NewType|Others]) :-
					recorded(frame,[newtype,Number],_), NewType = tvar(Number,Number,Number),
					Number2 is Number + 1, recorda(frame,[newtype,Number2],_), M is N - 1,
					gen_fresh_type(M,Others).


% Verifies what is the basetype of a constant or function symbol

basetype(C,Data,Type) :- get_from_data(C,Data,_,Type);
					basetype_flag(on) -> basetype_of(C,Type);
					Type = basetype(C).

basetypefunc(ARITFUNC,_,arit,sum([basetype(int),basetype(float)])) :- ARITFUNC == '*'; ARITFUNC == '+'; ARITFUNC == '-'; ARITFUNC == '/'.
basetypefunc(F,Data,Type,Name) :- (get_from_data(F,Data,Type,Name);
					Type = no_occurrence, Name = no_occurrence).

get_from_data(F,[type(Name,List)|Data],Occurence,Name) :- is_present(F,List,Occurence).
get_from_data(F,[_|Data],Occurence,Name) :- get_from_data(F,Data,Occurence,Name).

is_present(F,[Y|Ys],Y) :- Y =.. [func, F|Args], !.
is_present(F,[Y|Ys],Z) :- Y =.. [func, G|Args], G \= F, is_present(F,Ys,Z).

basetype_of(C,Type) :- C = [], Type = basetype([]).
basetype_of(C,Type) :- integer(C), Type = basetype(int).
basetype_of(C,Type) :- float(C), Type = basetype(float).
basetype_of(C,Type) :- string(C), Type = basetype(string).
basetype_of(C,Type) :- atom(C), Type = basetype(atom).


% Applies constraint_gen to the arguments of a function symbol

constraint_gen_args([],Data,[],[],[],[]).
constraint_gen_args([Arg|Args],Data,[Type|Types],[Env|Envs],[Eq|Eqs],[Ineq|Ineqs]) :-
					constraint_gen(Arg,Data,Type,Env,Eq,Ineq),
					constraint_gen_args(Args,Data,Types,Envs,Eqs,Ineqs).


% Calculates the cross product of the Environments

cross_prod(Envs,Env) :- cup(Envs,TempEnv), deal_with_repeated(TempEnv,Env).

deal_with_repeated([],[]).
deal_with_repeated([(Var,Type)|Rest],[(Var,NType)|RestPrime]) :-
					occurences(Var,Rest,[],List,NewRest), (
					List = [] -> NType = Type;
					List \= [] -> gen_fresh_var(1,[NType]), unify_all(NType,[Type|List]) ),
					deal_with_repeated(NewRest,RestPrime).

occurences(_,[],Final,Final,[]).
occurences(Var,[(Var,Type)|Rest],Acc,List,Rest1) :- !, occurences(Var,Rest,[Type|Acc],List,Rest1).
occurences(Var,[(OtherVar,Type)|Rest],Acc,List,[(OtherVar,Type)|Rest1]) :-
					Var \= OtherVar, !, occurences(Var,Rest,Acc,List,Rest1).

unify_all(NType,[]).
unify_all(NType,[Type|Rest]) :- NType = Type, unify_all(NType,Rest).

gen_cons_product(_,[],[]).
gen_cons_product(NType,[Oc|Ocs],[eq(NType,Oc)|More]) :- gen_cons_product(NType,Ocs,More).


% Does the union of the lists in A on a single list B

cup(A,B) :- cup(A,[],B).

cup([],Final,Final).
cup([L|Ls],Acc,Final) :- append(L,Acc,NAcc), cup(Ls,NAcc,Final).


% Concatenates two lists

append([],L,L).
append([X|Xs],Y,[X|Zs]) :- append(Xs,Y,Zs).


% Concatenates two lists without repeating elements

append_without_repeating([],L,L).
append_without_repeating([H|T],Y,L) :- (
					var(H), occurs_in(H,Y) -> append(T,Y,L);
					member(H,Y) -> append(T,Y,L);
					true -> append(T,Y,L1), L = [H|L1]).

occurs_in(H,[X|_]) :- H == X, !.
occurs_in(H,[_|Rest]) :- occurs_in(H,Rest).


% Generates equality constraints with num on the right-hand side for each variable in the list

gen_arith([],[]).
gen_arith([T|Ts],[subt(T,sum([basetype(int),basetype(float)]))|Eqs]) :-
					gen_arith(Ts,Eqs).


% Finds the types for the list of variables in the Environment and gathers them on the list of types

get_from_env([],Env,[]).
get_from_env([Var|Vars],Env,[Type|Types]) :- is_in(Var,Env,Type), get_from_env(Vars,Env,Types).

is_in(Var,[(Var,Type)|Pairs],Type) :- !.	
is_in(Var,[(Varprime,_)|Pairs],Type) :- Var \= Varprime, is_in(Var,Pairs,Type).


% Generates inequality constraints for each pair of arguments of both lists

gen_subt_cons([],[],[]).
gen_subt_cons([A|As],[B|Bs],[subt(A,B)|Rest]) :- gen_subt_cons(As,Bs,Rest).


% Generates equality constraints for each pair of arguments of both lists.

gen_eq_cons([],[],[]).
gen_eq_cons([A|As],[B|Bs],[eq(A,B)|Rest]) :- gen_eq_cons(As,Bs,Rest).


% Generates pairs for the Environment from each pair of arguments of both lists

on_each([],[],[]).
on_each([A|As],[B|Bs],[(A,B)|Rest]) :- on_each(As,Bs,Rest).


% Generates types for the predicate P

gen_predicate_tvar(P,N,0,[tvar(P,0,0)]).
gen_predicate_tvar(P,N,N,[tvar(P,N,N)]).
gen_predicate_tvar(P,M,N,[tvar(P,M,N)|Types]) :- M < N, Q is M + 1, gen_predicate_tvar(P,Q,N,Types).


% Changes the free variables in the Data for new occurences

varied(Data,0,List,List).
varied(Data,N,Acc,Final):-
					N1 is N - 1, generate_fresh_data(Data,FData),
					append([FData],Acc,NAcc), varied(Data,N1,NAcc,Final).

generate_fresh_data([],[]).
generate_fresh_data([Type|Types],[NType|NTypes]) :-
					Type =.. [type, Name, Rule], Name =.. [tnam, Nome, Args],
					length(Args,N), gen_fresh_var(N,Fresh), replace_in_a_rule(Args,Fresh,Rule,NRule),
					NType =.. [type, tnam(Nome,Fresh),NRule],
					generate_fresh_data(Types,NTypes).

replace_in_a_rule([],[],L,L).
replace_in_a_rule([A|As],[B|Bs],Rule,NRule) :-
					replace_one_in_a_rule(A,B,Rule,Temp),
					replace_in_a_rule(As,Bs,Temp,NRule).

replace_one_in_a_rule(A,B,[],[]).
replace_one_in_a_rule(A,B,[F|Fs],[G|Gs]) :- (
					F == A -> G = B;	
					F =.. [func, _, []] -> G = F;
					F =.. [func, HHH, Args] -> replace_in_rule_args(A,B,Args,NArgs), G =.. [func, HHH, NArgs];
					F =.. [tnam, Name, Args] -> replace_in_rule_args(A,B,Args,NArgs), G =.. [tnam, Name, NArgs];
					true -> G = F),
					replace_one_in_a_rule(A,B,Fs,Gs).
replace_in_rule_args(A,B,[],[]).
replace_in_rule_args(A,B,[F|Fs],[G|Gs]) :- (
					F == A -> G = B;	
					F =.. [func, _, []] -> G = F;
					F =.. [func, HHH, Args] -> replace_in_rule_args(A,B,Args,NArgs), G =.. [func, HHH, NArgs];
					F =.. [tnam, Name, Args] -> replace_in_rule_args(A,B,Args,NArgs), G =.. [tnam, Name, NArgs];
					true -> G = F),
					replace_one_in_a_rule(A,B,Fs,Gs).


% Calculates the cross sum of the Environments

cross_sum(Envs,Env,Cprime) :- cup(Envs,TempEnv), repeated_gather(TempEnv,Env,Cprime).

repeated_gather([],[],[]).
repeated_gather([(V,T)|Rest],[(V,Type)|Others],[eq(Type,Sum)|More]) :-
					all_occurrences(V,Rest,All), All \= [] -> remove_from_env(V,Rest,NRest),
					gen_fresh_var(1,[Type]), Sum =.. [sum , [T|All]], repeated_gather(NRest,Others,More).
repeated_gather([(V,T)|Rest],[(V,T)|Others],Constraints) :-
					repeated_gather(Rest,Others,Constraints).

all_occurrences(V,[],[]).
all_occurrences(V,[(V,T)|Rest],[T|More]) :- !, all_occurrences(V,Rest,More).
all_occurrences(V,[(K,_)|Rest],More) :- all_occurrences(V,Rest,More).

remove_from_env(_,[],[]).
remove_from_env(V,[(V,_)|Rest],Others) :- remove_from_env(V,Rest,Others).
remove_from_env(V,[(K,T)|Rest],[(K,T)|Others]) :- remove_from_env(V,Rest,Others).


% Applies constaint_gen to each argument of the list, with slightly different Datas

constraint_gen_all([],[],[],[],[]).
constraint_gen_all([Arg|Args], [Data|Datas], [Env|Envs], [Eq|Eqs], [Ineq|Ineqs]) :-
					constraint_gen(Arg,Data,_,Env,Eq,Ineq),
					constraint_gen_all(Args,Datas,Envs,Eqs,Ineqs).


% Marks recursive predicate calls on the body of a clause

mark_recursive(P,Body,NBody) :-
					Body =.. [or | Bodies], mark_recursive_all(P,Bodies,NBodies), NBody =.. [or | NBodies];
					Body =.. [and | Calls], mark_recursive_all(P,Calls,NCalls), NBody =.. [and | NCalls];
					Body =.. [equals, T1, T2], NBody = Body;
					Body =.. [pred, Q , Args1], P \= Q, NBody = Body;
					Body =.. [pred, P , Args1], NBody = rec(Body).

mark_recursive_all(P,[],[]).
mark_recursive_all(P,[X|Xs],[Y|Ys]) :- mark_recursive(P,X,Y), mark_recursive_all(P,Xs,Ys).

% Renames the types defined in Neq.

rename_types(_,[],NewTypes,[]).
rename_types(P,[C|Constraints],NewTypes,[NC|NewConstraints]) :-
					rename_constraint(P,C,NewTypes,NC),
					rename_types(P,Constraints,NewTypes,NewConstraints).

rename_constraint(P,eq(Type,Def),NewTypes,eq(Fresh,NDef)) :-
					(Type =.. [_, P, Pos, _] ->
					get_type(Pos,NewTypes,Fresh);
					Fresh = Type),
					rename_definition(P,Def,NewTypes,NDef).

rename_definition(P,Def,NewTypes,NDef) :- (
					var(Def) -> NDef = Def;
					Def =.. [tvar, P, A, N] -> get_type(A,NewTypes,NDef);
					Def =.. [tvar | _] -> NDef = Def;
					Def =.. [basetype, _] -> NDef = Def;
					Def = sum(List) -> rename_args(P,List,NewTypes,NList), NDef = sum(NList);
					Def =.. [Type, Name, Args] -> rename_args(P,Args,NewTypes,NArgs), NDef =.. [Type,Name,NArgs]).

rename_args(_,[],_,[]).
rename_args(P,[A|As],NewTypes,[NA|NAs]) :- rename_definition(P,A,NewTypes,NA), rename_args(P,As,NewTypes,NAs).

get_type(1,[A|_],A).
get_type(N,[_|Rest],A) :- M is N - 1, get_type(M,Rest,A).




























%% 3 - CONSTRAINT SOLVING %%

constraint_solve(Eq,Ineq,ActualFinal) :-
					algorithm(Eq,NewEq), simplify(NewEq,NewEq,NEq),!,
					ineq_algorithm(Ineq,NEq,FinalIneq,FinalEq), retractall(already_compared(_)),
					retractall(is_the_same(_,_)), simplify(FinalEq,FinalEq,FEq),
					important_types(FEq,TheOnes),
					(closure_flag(on) -> closure(TheOnes,ActualFinal);
						true -> ActualFinal = TheOnes).

%% ALGORITHM TO SOLVE THE EQUALITY CONSTRAINTS %%

algorithm(Eq,NEq) :- (
					case1(Eq,Constraint) -> remove_constraint(Constraint,Eq,TEq), !,
						algorithm(TEq,NEq);
					case2(Eq,Constraint) -> Constraint =.. [eq, X, Rest],
						remove_constraint(Constraint,Eq,TempEq),
						X = Rest, !,
						algorithm(TempEq,NEq) ;
					case3(Eq,Constraint) -> remove_constraint(Constraint,Eq,TempEq),
						Constraint =.. [eq, Arg1,Arg2], NConstraint =.. [eq,Arg2,Arg1],
						TEq = [NConstraint | TempEq], !,
						algorithm(TEq,NEq);
					case4(Eq,Constraint) -> Constraint =.. [eq, T1, T2],
						T1 =.. [A, F, Args1], T2 =.. [A, F, Args2],
						remove_constraint(Constraint,Eq,TempEq),
						gen_eq_cons(Args1,Args2,Temp), append(Temp,TempEq,TEq), !,
						algorithm(TEq,NEq);
					case5(Eq,Constraint) -> !, NEq = []
					).
algorithm(Eq,Eq) :- !, in_solved_form(Eq).



% The 5 cases for the Algorithm:


% t = t

case1([eq(T1,T2)|Cs],eq(T1,T2)) :- T1 == T2, !.
case1([C|Cs],C1) :- case1(Cs,C1).

% x = T and var(x) and T2 \= sum(List)

case2([eq(T1,T2)|Cs],Constraint) :- var(T1), (var(T2); true), occur_check(T1,T2), !,
					Constraint = eq(T1,T2).
case2([C|Cs],Cons) :- case2(Cs,Cons).

% t = x, t not a var, x a var

case3([eq(T1,T2)|Cs],eq(T1,T2)) :- not(var(T1)), not(T1 =.. [tvar, P, A, N]), var(T2), !.
case3([C|Cs],C1) :- case3(Cs,C1).

% f(t1,...,tn) = f(s1,...,sn)

case4([eq(T1,T2)|Cs],eq(T1,T2)) :- T1 =.. [func, F, Args], T2 =.. [func, F, Args1], !.
%case4([eq(T1,T2)|Cs],eq(T1,T2)) :- T1 =.. [func, F, Args], T2 =.. [tnam, Name, Argss], !.
case4([eq(T1,T2)|Cs],eq(T1,T2)) :- T1 =.. [tnam, Name, Args], T2 =.. [tnam, Name, Args2], !.
case4([C|Cs],C1) :- case4(Cs,C1).


% f(t1,...,tn) = g(s1,...,sn), f \= g

case5([eq(T1,T2)|Cs],eq(T1,T2)) :- T1 =.. [func, F, Args], T2 =.. [func, G , Args1], F \= G, !.
case5([eq(T1,T2)|Cs],eq(T1,T2)) :- T1 =.. [basetype, F], T2 =.. [basetype, G], F \= G, !.
case5([eq(T1,T2)|Cs],eq(T1,T2)) :- T1 =.. [tnam, F, Args], T2 =.. [tnam, G , Args1], F \= G, !.
case5([eq(T1,T2)|Cs],eq(T1,T2)) :- T1 =.. [basetype, _], T2 =.. [func, _, _], !.
case5([eq(T1,T2)|Cs],eq(T1,T2)) :- T2 =.. [basetype, _], T1 =.. [func, _, _], !.
case5([eq(T1,T2)|Cs],eq(T1,T2)) :- T1 =.. [basetype, _], T2 =.. [tnam, _, _], !.
case5([eq(T1,T2)|Cs],eq(T1,T2)) :- T2 =.. [basetype, _], T1 =.. [tnam, _, _], !.
case5([C|Cs],C1) :- !, case5(Cs,C1).


% Auxiliary functions for the Algorithm.

% occur_check

occur_check(T,T1) :- var(T1), T == T1, !, fail.
occur_check(T,tvar(P,A,N)) :- T == tvar(P,A,N), !,fail.
occur_check(T,basetype(K)) :- T == basetype(K), !, fail.
occur_check(T1,T2) :- not(var(T2)), T2 =.. [T, F, Args], occur_check_args(T1,Args), !.
occur_check(T1,T2) :- T1 == T2, !, fail.
occur_check(T1,T2).

occur_check_args(T,[]).
occur_check_args(T,[A|As]) :- occur_check(T,A), occur_check_args(T,As).

% removing a constraint C from a list of constraints

remove_constraint(C,[C1|Cs],Cs) :- C == C1, !.
remove_constraint(C,[X|Cs],[X|Xs]) :- remove_constraint(C,Cs,Xs).

% removing a list of constraints from a list.

remove_all_constraints([],R,R).
remove_all_constraints([C|Cs],List,NewList) :-
					remove_constraint(C,List,TempList),
					remove_all_constraints(Cs,TempList,NewList).

% verifies if a list of constraints is in solved form

in_solved_form([]).
in_solved_form([C|Cs]) :- C = eq(X,Y), !, X = tvar(P,A,N), in_solved_form(Cs).




%% SIMPLIFICATION STEP %%

simplify([],Output,Output).
simplify([eq(A,B)|Rest],List,Output) :-
					(step0(B,A,Bprime), TList = List;
					step1(B,Bprime), TList = List;
					step2(B,Bprime), TList = List;
					step3(A,B,Bprime), TList = List;
					step4(A,B,List,Bprime), TList = List;
					step5(B,Bprime), TList = List;
					step6(B,Bprime), TList = List;
					step7(B,Bprime,ToAdd), TList = List;
					step8(A,B,List,TList), Bprime = B;
					step9(A,B,List,TList), Bprime = B, Flag = true) ->
					(Bprime == B, TempList = TList ; replace(eq(A,B),eq(A,Bprime),TList,TempList)),
					(ToAdd = []; true),
					append(ToAdd,TempList,NList), append(ToAdd,Rest,NRest),
					(Flag == true -> simplify(NList,NList,TOutput), Output = [eq(A,B)|TOutput];
					Bprime == B -> simplify(NRest,NList,Output);
					simplify([eq(A,Bprime)|NRest],NList,Output)).
simplify([eq(A,B)|Rest],List,Output) :- simplify(Rest,List,Output).

step0(X,_,X) :- var(X), !, fail.
step0(X,X,V) :- gen_fresh_var(1,[V]).

step1(X,X) :- var(X),!, fail.
step1(sum([X]),X):- !.

step2(X,X) :- var(X),!, fail.
step2(sum(List),Final) :- list_has_sum(List,List1,TempList), append(TempList,List1,NList), Final = sum(NList).

step3(_,X,X) :- var(X),!, fail.
step3(A,sum(List),Final) :- possibly_remove_from(A,List,NList) -> Final = sum(NList).

step4(_,X,_,X) :- var(X), !, fail.
step4(A,Type,Defs,Final) :- Type =.. [tvar| _], get_definition(Type,Defs,TempDef),
					(var(TempDef) -> Def = TempDef;
					TempDef = sum(List) -> remove_type_from_list(Type,List,NList), Def = sum(NList);
					TempDef == Type -> fail;
					true -> Def = TempDef),
					replace_in_def(Def,Type,A,Final).
step4(A,sum(List),Defs,Final) :-
					list_has_type(List,A,Type,TempList), get_definition(Type,Defs,TempDef),
					(var(TempDef) -> Def = TempDef;
					TempDef = sum(List2) -> remove_type_from_list(Type,List2,NList), Def = sum(NList);
					TempDef == Type -> fail;
					true -> Def = TempDef),
					replace_in_def(Def,Type,A,NDef), append([NDef],TempList,NList), Final = sum(NList).

step5(X,X) :- var(X), !, fail.
step5(sum(List),Final) :- list_has_repeated(List) -> remove_repeated(List,NList), Final = sum(NList).

step6(X,X) :- var(X), !, fail.
step6(sum(List),Final) :- list_has_cons(List,Oc1,Oc2,TempList), sum_oc_pointwise(Oc1,Oc2,FinalOc),
					Final = sum([FinalOc|TempList]).

step7(X,X,[]) :- var(X), !, fail.
step7(Term,Final,ToAdd) :-
					Term =.. [FORT, Name, Args],
					list_has_sum_in_cons(Args,ToAdd,NArgs),
					Final =.. [FORT,Name,NArgs].
step7(sum(List),Final,ToAdd) :-
					list_has_cons_with_sums(List,NOccurence,ToAdd,TempList),
					NOccurence =.. [FORT, Name, Args],
					Final = sum([NOccurence|TempList]).

step8(A,B,List,TList) :-
					remove_constraint(eq(A,B),List,TempList), any_other_same_body(B,TempList,eq(C,D)),
					(A =.. [tvar, N, N, N] -> replace_in_constraints(A,C,TempList,TList), assert(is_the_same(A,C));
					C =.. [tvar, N, N, N] -> remove_constraint(eq(C,B),TempList,TempList2), assert(is_the_same(C,A)),
										replace_in_constraints(C,A,TempList2,TempList3),
										TList=[eq(A,B)|TempList3]).

step9(A,B,List,TList) :-
					(var(B);
					B =.. [basetype | _];
					B =.. [tnam, _, Args], not(occur_check_args(A,Args));
					B =.. [func, _, Args], not(occur_check_args(A,Args))) ->
					A =.. [tvar, N, N, N], !,
					remove_constraint(eq(A,B),List,TempList), assert(is_the_same(A,B)),
					replace_in_constraints(A,B,TempList,TList).


% Auxiliary functions

list_has_sum([A|B],List,B) :- not(var(A)), A = sum(List),!.
list_has_sum([A|B],List,[A|C]) :- list_has_sum(B,List,C).

remove_from_list(_,[],[]).
remove_from_list(T,[X|Rest],Others) :- (
					X == T -> remove_from_list(T,Rest,Others);
					true -> remove_from_list(T,Rest,Temp), Others = [X|Temp]).

possibly_remove_from(_,[],_) :- !, fail.
possibly_remove_from(T,[X|Rest],Others) :-
					(T == X -> Rest = Others;
					true -> possibly_remove_from(T,Rest,Temp), Others = [X|Temp]).


list_has_type([Head|Rest],A,Head,Rest) :- not(var(Head)), Head \= A, Head =.. [tvar | _], !.
list_has_type([Head|Rest],A,Not,[Head|Others]) :- list_has_type(Rest,A,Not,Others).

remove_type_from_list(_,[],[]).
remove_type_from_list(Type,[X|Rest],NRest) :- X == Type,!, remove_type_from_list(Type,Rest,NRest).
remove_type_from_list(Type,[X|Rest],[X|NRest]) :- remove_type_from_list(Type,Rest,NRest).

replace_in_def(sum(List),Type,A,sum(NList)) :- replace_type_by_def(Type,A,List,NList).
replace_in_def(X,Type,A,Y) :- replace_type_by_def(Type,A,[X],[Y]).

replace_type_by_def(Type,ToSub,[],[]).
replace_type_by_def(Type,ToSub,[A|As],[B|Bs]) :- (
					var(A) -> B = A;
					A == Type -> B = ToSub;
					A =.. [FORT, F, Args] -> replace_type_by_def(Type,ToSub,Args,NArgs), B =.. [FORT, F, NArgs];
					true -> B = A),
					replace_type_by_def(Type,ToSub,As,Bs).

list_has_cons([A|Rest],A,Oc2,TempList) :-
					not(var(A)), (A =.. [func, F, _];A =.. [tnam, F, _]),
					list_has_second_cons(Rest,F,Oc2,TempList), !, Oc1 = A.
list_has_cons([A|Rest],Oc1,Oc2,[A|Others]) :- list_has_cons(Rest,Oc1,Oc2,Others).

list_has_second_cons([A|Rest],F,A,Rest) :- not(var(A)), (A =.. [func, F, _];A =.. [tnam, F, _]), !.
list_has_second_cons([A|Rest],F,B,[A|Others]) :- list_has_second_cons(Rest,F,B,Others).

sum_oc_pointwise(func(F,Args1),func(F,Args2),func(F,FinalArgs)) :-
					sum_pointwise(Args1,Args2,FinalArgs).
sum_oc_pointwise(tnam(F,Args1),tnam(F,Args2),tnam(F,FinalArgs)) :-
					sum_pointwise(Args1,Args2,FinalArgs).

sum_pointwise([],[],[]).
sum_pointwise([A|As],[B|Bs],[C|Cs]) :- var(A), var(B), C = sum([A,B]), sum_pointwise(As,Bs,Cs).
sum_pointwise([A|As],[B|Bs],[C|Cs]) :- var(A), B = sum(List), C = sum([A|List]), sum_pointwise(As,Bs,Cs).
sum_pointwise([A|As],[B|Bs],[C|Cs]) :- var(B), A = sum(List), C = sum([B|List]), sum_pointwise(As,Bs,Cs).
sum_pointwise([A|As],[B|Bs],[C|Cs]) :- var(A), C = sum([A,B]), sum_pointwise(As,Bs,Cs).
sum_pointwise([A|As],[B|Bs],[C|Cs]) :- var(B), C = sum([A,B]), sum_pointwise(As,Bs,Cs).
sum_pointwise([A|As],[B|Bs],[C|Cs]) :-
					A = sum(List1), B = sum(List2), append(List1,List2,List), C = sum(List),
					sum_pointwise(As,Bs,Cs).
sum_pointwise([A|As],[B|Bs],[C|Cs]) :- A = sum(List), C = sum([B|List]), sum_pointwise(As,Bs,Cs).
sum_pointwise([A|As],[B|Bs],[C|Cs]) :- B = sum(List), C = sum([A|List]), sum_pointwise(As,Bs,Cs).
sum_pointwise([A|As],[B|Bs],[C|Cs]) :- C = sum([A,B]), sum_pointwise(As,Bs,Cs).

list_has_repeated([]) :- !, fail.
list_has_repeated([A|Rest]) :- occurs_in(A,Rest).
list_has_repeated([A|Rest]) :- list_has_repeated(Rest).

remove_repeated([],[]).
remove_repeated([A|Rest],[A|List]) :- remove_from_list(A,Rest,Temp), remove_repeated(Temp,List).

list_has_cons_with_sums([A|As],B,T,As) :-
					not(var(A)), A =.. [FORT, F, List], list_has_sum_in_cons(List,T,NList),!,
					B =.. [FORT, F, NList].
list_has_cons_with_sums([A|As],List,T,[A|Bs]) :- list_has_cons_with_sums(As,List,T,Bs).

list_has_sum_in_cons([A|As],ToAdd,[T|As]) :-
					not(var(A)), A = sum(List), gen_fresh_type(1,[T]), !, ToAdd = [eq(T,A)].
list_has_sum_in_cons([A|As],ToAdd,[A|Bs]) :-
					list_has_sum_in_cons(As,ToAdd,Bs).

replace_in_constraints(_,_,[],[]).
replace_in_constraints(A,B,[eq(X,C)|Cs],[eq(X,D)|Ds]) :-
					replace_in_a_right(A,B,C,D), replace_in_constraints(A,B,Cs,Ds).

replace_in_a_right(A,B,C,D) :-
					var(C) -> D = C;
					C == A -> D = B;
					C =.. [basetype | _] -> D = C;
					C =.. [tvar | _] -> D = C;
					C =.. [FORT, Name, Args] -> replace_in_args(A,B,Args,NArgs), D =.. [FORT,Name,NArgs];
					C = sum(List) -> replace_in_args(A,B,List,NList), D = sum(NList).

replace_in_args(A,B,[],[]).
replace_in_args(A,B,[C|Cs],[D|Ds]) :- replace_in_a_right(A,B,C,D), replace_in_args(A,B,Cs,Ds).

any_other_same_body(B,[eq(A,C)|Rest],eq(A,C)) :- C == B, !.
any_other_same_body(B,[eq(A,C)|Rest],X) :- any_other_same_body(B,Rest,X).


%% ALGORITHM FOR SOLVING INEQUATIONS %%

ineq_algorithm(Ineq,BoundDefinitions,SolvedIneq,FinalDefinitions) :-
					icase1(Ineq,Constraint) -> remove_constraint(Constraint,Ineq,NeqIneq), !,
										ineq_algorithm(NeqIneq,BoundDefinitions,SolvedIneq,FinalDefinitions);
					icase2(Ineq,Constraint) -> remove_constraint(Constraint,Ineq,NeqIneq),!,
										Constraint =.. [subt, T1, T2],
										T1 =.. [_,_,Args1],
										T2 =.. [_,_,Args2],
										gen_subt_cons(Args1,Args2,ExtraIneq),
										append(ExtraIneq,NeqIneq,FinalIneq),!,
										ineq_algorithm(FinalIneq,BoundDefinitions,SolvedIneq,FinalDefinitions);
					icase3(Ineq,Constraint1,Constraint2) -> remove_constraint(Constraint1,Ineq,TempIneq),
										remove_constraint(Constraint2,TempIneq,NeqIneq),
										Constraint1 =.. [_,X,T1], Constraint2 =.. [_,X,T2],
										intersect(T1,T2,BoundDefinitions,T,[],C), Sub =.. [subt,X,T],
										append([Sub],NeqIneq,FinalIneq),!,
										append(C,BoundDefinitions,NBoundDefs),
										simplify(NBoundDefs,NBoundDefs,NBD),!,
										ineq_algorithm(FinalIneq,NBD,SolvedIneq,FinalDefinitions);
					icase4(Ineq,Constraint,Extra) -> remove_constraint(Constraint,Ineq,NeqIneq),
										Constraint =.. [subt, T1, T2], T1 = Extra,!,
										simplify(BoundDefinitions,BoundDefinitions,NBD),!,
										ineq_algorithm(NeqIneq,NBD,SolvedIneq,FinalDefinitions);
					icase5(Ineq,Constraint) -> remove_constraint(Constraint,Ineq,NeqIneq),
										Constraint =.. [subt, sum(List), T],
										for_each_generate_subt(List,T,NewIneqs),
										append(NewIneqs,NeqIneq,FinalIneq), !,
										ineq_algorithm(FinalIneq,BoundDefinitions,SolvedIneq,FinalDefinitions);
					icase6(Ineq,Constraint) -> remove_constraint(Constraint,Ineq,NeqIneq),
										Constraint =.. [subt, VAR, T], (
										already_compared((VAR,T)) -> FinalIneq = NeqIneq;
										true -> (get_definition(VAR,BoundDefinitions,Def);is_the_same(VAR,Def)),
										Sub =.. [subt, Def, T], append([Sub],NeqIneq,FinalIneq),
										assert(already_compared((VAR,T)))), !,
										ineq_algorithm(FinalIneq,BoundDefinitions,SolvedIneq,FinalDefinitions);
					icase7(Ineq,Var,Constraints) -> remove_all_constraints(Constraints,Ineq,NeqIneq),
										get_all_lefts(Constraints,Lefts),
										(length(Lefts,1) -> Lefts = [Var]; true -> Var = sum(Lefts)),
										simplify(BoundDefinitions,BoundDefinitions,NBD),!,
										ineq_algorithm(NeqIneq,NBD,SolvedIneq,FinalDefinitions);
					icase8(Ineq,Constraint) -> remove_constraint(Constraint,Ineq,NeqIneq),
										Constraint =.. [subt, T, sum(List)], !,
										search_for_compatible(T,List,List,T1), Sub =.. [subt, T, T1],
										append([Sub],NeqIneq,FinalIneq), !,
										ineq_algorithm(FinalIneq,BoundDefinitions,SolvedIneq,FinalDefinitions);
					icase9(Ineq,Constraint) -> remove_constraint(Constraint,Ineq,NeqIneq),
										Constraint =.. [subt, T, VAR], (
										already_compared((T,VAR)) -> FinalIneq = NeqIneq;
										true -> (get_definition(VAR,BoundDefinitions,Def);is_the_same(VAR,Def)),
										Sub =.. [subt, T, Def], append([Sub],NeqIneq,FinalIneq),
										assert(already_compared((T,VAR)))),!,
										ineq_algorithm(FinalIneq,BoundDefinitions,SolvedIneq,FinalDefinitions);
					icase10(Ineq) -> fail.
ineq_algorithm(FinalIneq,FinalDefinitions,FinalIneq,FinalDefinitions) :- !, in_solved_ineq_form(FinalIneq).

icase1([subt(T,NT)|Rest],Constraint) :-
					(NT == T -> Constraint = subt(T,NT);
					(var(NT);var(T)), not(NT == T) -> icase1(Rest,Constraint);
					T = basetype(K), NT = basetype(int), integer(K), Constraint = subt(T,NT);
					T = basetype(K), NT = basetype(float), float(K), Constraint = subt(T,NT)).

icase2([subt(T1,T2)|Rest],Constraint) :-
					(not(var(T1)), T1 =.. [Type, F, Args1],
					not(var(T2)), T2 =.. [Type, F, Args2] -> Constraint = subt(T1,T2);
					true -> icase2(Rest,Constraint)).

icase3([subt(NT,T1)|Rest],Constraint,Constraint2) :- 
					(var(NT), other_ineq_right(NT,Rest,Constraint2) -> Constraint = subt(NT,T1);
					true -> icase3(Rest,Constraint,Constraint2)).

icase4([subt(NT,T)|Rest],Constraint,Extra) :-
					(var(NT), occur_checking(NT,T),
					(var(T), Extra = T;
					T =.. [tvar | _], is_the_same(T,T1), icase4([subt(NT,T1)],_,Extra);
					Extra = T) -> Constraint = subt(NT,T);
					true -> icase4(Rest,Constraint,Extra)).

icase5([subt(S,T)|Rest],Constraint) :-
					(not(var(S)), S =.. [sum, Args] -> Constraint = subt(S,T);
					true -> icase5(Rest,Constraint)).

icase6([subt(NT,T)|Rest],Constraint) :- 
					(not(var(NT)), NT =.. [tvar | _], not(var(T)) -> Constraint = subt(NT,T);
					true -> icase6(Rest,Constraint)).

icase7([subt(T,VAR)|Rest],VAR,List) :-
					(var(VAR), other_ineqs_left(VAR,Rest,All) -> List = [subt(T,VAR)|All];
					true -> icase7(Rest,VAR,Constraint)).

icase8([subt(T,S)|Rest],Constraint) :-
					(S =.. [sum, Args] -> Constraint = subt(T,S);
					true -> icase8(Rest,Constraint)).

icase9([subt(T,NT)|Rest],Constraint) :-
					(NT =.. [tvar | _] -> Constraint = subt(T,NT);
					true -> icase9(Rest,Constraint)).

icase10([subt(T1,T2)|_]) :-
					T1 =.. [basetype, _], T2 =.. [func, _, _];
					T1 =.. [basetype, _], T2 =.. [tnam, _, _];
					T1 =.. [basetype, K], T2 =.. [basetype, L], K \= L;
					T1 =.. [func, _, _], T2 =.. [tnam, _ ,_];
					T1 =.. [func, _, _], T2 =.. [basetype, _];
					T1 =.. [func, F, _], T2 =.. [func, G, _], F \= G;
					T1 =.. [tnam, _ ,_], T2 =.. [basetype, _];
					T1 =.. [tnam, _, _], T2 =.. [func, _, _];
					T1 =.. [tnam, Name, _], T2 =.. [tnam, Other, _], Name \= Other.
icase10([_|Rest]) :- icase10(Rest).

in_solved_ineq_form([]).


occur_checking(VAR,T) :-
					T == VAR -> fail;
					var(T) -> true;
					T = sum(List) -> occur_checking_args(VAR,List);
					T =.. [Type, _, Args] -> occur_checking_args(VAR,Args);
					true -> true.

occur_checking_args(VAR,[]).
occur_checking_args(VAR,[A|As]) :- occur_checking(VAR,A), occur_checking_args(VAR,As).

for_each_generate_subt([],T,[]).
for_each_generate_subt([A|As],T,[subt(A,T)|Subts]) :- for_each_generate_subt(As,T,Subts).

get_definition(VAR,[eq(VAR,Def)|_],Def).
get_definition(VAR,[eq(NOTVAR,_)|BoundDefinitions],Def) :-
					NOTVAR \= VAR, get_definition(VAR,BoundDefinitions,Def).

search_for_compatible(T,[T1|Rest],List,T1) :-
					var(T), T1 == T.
search_for_compatible(T,[T1|Rest],List,T1) :- 
					T =.. [basetype, K], not(var(T1)),
					(T1 = basetype(K);
					T1 = basetype(int), integer(K);
					T1 = basetype(float), float(K)).
search_for_compatible(T,[T1|Rest],List,T1) :-
					T =.. [func, F, Args2], not(var(T1)), T1 = func(F,Args).
search_for_compatible(T,[T1|Rest],List,T1) :-
					T =.. [tnam, Name, Args2], not(var(T1)), T1 = tnam(Name,Args).
search_for_compatible(T,[_|Rest],List,T1) :- search_for_compatible(T,Rest,List,T1).
search_for_compatible(T,[],List,T1) :- search_for_var(T,List,T1).

search_for_var(T,[T1|_],T1) :- var(T1), not(occurs_in_term(T1,T)).
search_for_var(T,[_|Rest],T1) :- search_for_var(T,Rest,T1).

occurs_in_term(T1,T) :- T =.. [func, F, Args] -> occurs_in_args(T1,Args).
occurs_in_term(T1,T) :- T =.. [tnam, Name, Args] -> occurs_in_args(T1,Args).

occurs_in_args(T1,[A|As]) :- (T1 == A; not(var(A)), occurs_in_term(T1,A)).
occurs_in_args(T1,[_|As]) :- occurs_in_args(T1,As).

do_equalities([]).
do_equalities([eq(T1,T2)|Rest]) :- T1 = T2, do_equalities(Rest).

intersect(T1,T2,BoundDefinitions,T,Pairs,C) :-
					var(T1) -> T = T2, C = [];
					var(T2) -> T = T1, C = [];
					T1 = tvar(P,A,N), T2 = tvar(Q,B,M) ->
										gen_fresh_type(1,[T]), (get_definition(T1,BoundDefinitions,Def1);is_the_same(T1,Def1)),
										(get_definition(T2,BoundDefinitions,Def2);is_the_same(T2,Def2)),
										cpi(Def1,Def2,FinalDef,BoundDefinitions,[(T1,T2,T)|Pairs],Cs),
										append([eq(T,FinalDef)],Cs,C);
					T1 = sum(List) -> cpi(T1,T2,T,BoundDefinitions,Pairs,Cs), cup(Cs,C);
					T2 = sum(List) -> cpi(T1,T2,T,BoundDefinitions,Pairs,Cs), cup(Cs,C);
					T1 = tvar(P,A,N) -> (get_definition(T1,BoundDefinitions,Def1);is_the_same(T1,Def1)),
										(var(Def1) -> T = T2, C = [];
										intersect(Def1,T2,BoundDefinitions,T,Pairs,C));
					T2 = tvar(Q,B,M) -> (get_definition(T2,BoundDefinitions,Def2);is_the_same(T2,Def2)), (var(Def2) -> T = T2, C = [];
										intersect(Def2,T1,BoundDefinitions,T,Pairs,C));
					T1 =.. [basetype, K], T2 =.. [basetype, K] -> T = T1, C = [];
					T1 =.. [Something, Name, Args1], T2 =.. [Something, Name, Args2] ->
										intersect_args(Args1,Args2,BoundDefinitions,ArgsFinal,Pairs,C),
										T =.. [Something, Name, ArgsFinal];

					true -> fail.

cpi(Def1,Def2,FinalDef,BoundDefinitions,Pairs,Cs):-
					Def1 =.. [sum , List] ->
										intersect_for_each_left(List,Def2,AList,BoundDefinitions,Pairs,Cs),
										cup(AList,FList), remove_from_list([],FList,FFList),
										join_sums(FFList,FinalDef);
					Def2 =.. [sum, List] ->
										intersect_for_each_left(List,Def1,AList,BoundDefinitions,Pairs,Cs),
										cup(AList,FList), remove_from_list([],FList,FFList),
										join_sums(FFList,FinalDef);
					intersect(Def1,Def2,BoundDefinitions,FinalDef,Pairs,Cs).

intersect_for_each_left([],_,[],_,_,[]).
intersect_for_each_left([One|Others],Def2,[First|Rest],BoundDefinitions,Pairs,Cs) :- (
					Def2 =.. [sum , List2] -> intersect_for_each_right(One,List2,First,BoundDefinitions,Pairs,C);
					true -> (intersect(One,Def2,BoundDefinitions,F,Pairs,C), First = [F];First= [],C=[])),
					intersect_for_each_left(Others,Def2,Rest,BoundDefinitions,Pairs,Cprime),
					append(C,Cprime,Cs).

intersect_for_each_right(_,[],[],_,_,[]).
intersect_for_each_right(A,[One|Others],[First|Rest],BoundDefinitions,Pairs,Cs) :- 
					(intersect(A,One,BoundDefinitions,First,Pairs,C);
					First= [], C= []),
					intersect_for_each_right(A,Others,Rest,BoundDefinitions,Pairs,Cprime),
					append(C,Cprime,Cs).

intersect_args([],[],_,[],_,[]).
intersect_args([A1|Args1],[A2|Args2],BoundDefinitions,[AFinal|ArgsFinal],Pairs,SeveralC) :-
					intersect(A1,A2,BoundDefinitions,AFinal,Pairs,C),
					intersect_args(Args1,Args2,BoundDefinitions,ArgsFinal,Pairs,Cprime),
					append(C,Cprime,SeveralC).

remove_all_constraints([],R,R).
remove_all_constraints([C|Cs],List,NewList) :-
					remove_constraint(C,List,TempList),
					remove_all_constraints(Cs,TempList,NewList).

get_all_lefts([],[]).
get_all_lefts([subt(A,B)|Ss],[A|As]) :- get_all_lefts(Ss,As).

other_ineq_right(T,[subt(T1,R)|_],subt(T1,R)) :- T == T1, !.
other_ineq_right(T,[_|Rest],Some) :- other_ineq_right(T,Rest,Some).

other_ineqs_left(T,[],[]).
other_ineqs_left(T,[subt(R,T1)|Rest],[subt(R,T1)|Others]) :- T == T1, !, other_ineqs_left(T,Rest,Others).
other_ineqs_left(T,[_|Rest],Others) :- other_ineqs_left(T,Rest,Others).

important_types(A,B) :- get_types_for_pred(A,Important,Types,Rest), important_types(Important,Types,Rest,B).

get_types_for_pred([],[],[],[]).
get_types_for_pred([eq(T,B)|Rest],Important,Types,[eq(T,B)|Rest2]) :- 
					T =.. [tvar, N, N, N], !, get_types_for_pred(Rest,Important,Types,Rest2).
get_types_for_pred([eq(T,B)|Rest],[eq(T,B)|Important],Types,Rest2) :-
					get_types_from_body(B,T,Type), get_types_for_pred(Rest,Important,NType,Rest2),
					append_without_repeating(Type,NType,Types).

important_types(Final,[],_,Final).
important_types(Important,[T|Ts],Temp,Final) :-
					remove_type_from_temp(eq(T,B),Temp,NTemp),!,
					get_types_from_body(B,T,Types),
					append_without_repeating(Types,Ts,NTs),
					important_types([eq(T,B)|Important],NTs,NTemp,Final).
important_types(Important,[T|Ts],Temp,Final) :- important_types(Important,Ts,Temp,Final).

get_types_from_body(Body,T,Types) :-
					var(Body) -> Types = [];
					Body =.. [tvar, _, _, _ ], Body \= T -> Types = [Body];
					Body = T -> Types = [];
					Body = basetype(K) -> Types = [];
					Body =.. [FORT, _, Args] -> get_types_from_args(Args,T,Types);
					Body = sum(List) -> get_types_from_args(List,T,Types).

get_types_from_args([],_,[]).
get_types_from_args([A|As],T,Types) :-
					get_types_from_body(A,T,Type), get_types_from_args(As,T,MoreTypes),
					append_without_repeating(Type,MoreTypes,Types).

remove_type_from_temp(eq(T,B),[],[]) :- fail.
remove_type_from_temp(eq(T,B),[eq(T,C)|Rest],Rest) :- B = C.
remove_type_from_temp(eq(T,B),[eq(T1,C)|Rest],[eq(T1,C)|Final]) :- T \= T1, remove_type_from_temp(eq(T,B),Rest,Final).
























%% 4 - POSSIVEL CLOSURE %%

closure(ConstraintList,NewConstraintList) :- 
					self_intro(ConstraintList,SelfConstraintList),
					opentypes(SelfConstraintList,SelfConstraintList,OpenTypes,VarList), !,
					(OpenTypes = [] -> NewConstraintList = ConstraintList;
					proper_vars_domains(VarList,SelfConstraintList,Domains),
					apply_substitutions(VarList,Domains,SelfConstraintList,TempConstraintList), !,
					self_remove(TempConstraintList,NoSelfConstraintList),
					simplify(NoSelfConstraintList,NoSelfConstraintList,NewConstraintList)).

self_intro([],[]).
self_intro([C|Cs],[NC|NCs]) :-
					self_intro_in_one(C,NC),
					self_intro(Cs,NCs).

self_intro_in_one(eq(A,B),eq(A,NB)) :-
					replace_by_self(A,B,NB).

replace_by_self(A,Body,NBody) :-
					var(Body) -> NBody = Body;
					Body == A -> NBody = self;
					Body =.. [sum, List] -> replace_by_self_in_args(A,List,NList), NBody =.. [sum, NList];
					Body =.. [func, F, Args] -> replace_by_self_in_args(A,Args,NArgs), NBody =.. [func, F, NArgs];
					true -> NBody = Body.

replace_by_self_in_args(_,[],[]).
replace_by_self_in_args(A,[Arg|Args],[NA|NArgs]) :-
					replace_by_self(A,Arg,NA), replace_by_self_in_args(A,Args,NArgs).

opentypes([],_,[],[]).
opentypes([eq(A,B)|Rest],List,[eq(A,B)|Others],Vars) :-
					(var(B) -> remove_constraint(eq(A,B),List,NList), unconstrained(B,NList,[B]), !, fail;
					B =.. [sum, Summands], opencomposite(Summands,NVars), NVars \= [];
					true -> fail),
					opentypes(Rest,List,Others,FVars),
					append_without_repeating(NVars,FVars,Vars).
opentypes([_|Rest],List,Others,Vars) :- opentypes(Rest,List,Others,Vars).

opencomposite([],[]).
opencomposite([B|Rest],Vars) :- (
					var(B) -> opencomposite(Rest,Temp), append([B],Temp,Vars);
					B =.. [tnam, _, _] -> opencomposite(Rest,Vars);
					B =.. [tvar | _] -> opencomposite(Rest,Vars);
					B =.. [func, _, _] -> opencomposite(Rest,Vars);
					B =.. [basetype, _] -> opencomposite(Rest,Vars);
					B = self -> opencomposite(Rest,Vars)).	

unconstrained(B,List,_) :-
					occurs_in_constraints(B,List) -> fail; true.

occurs_in_constraints(B,[eq(A,Body)|Rest]) :- occurs_in_constraint(B,Body) ; occurs_in_constraints(B,Rest).

occurs_in_constraint(B,Body) :- (
					var(Body) -> B == Body;
					Body =.. [func, F, Args] -> not(occur_checking_args(B,Args));
					Body = sum(List) -> not(occur_checking_args(B,List));
					true -> fail).

proper_vars_domains([],_,[]).
proper_vars_domains([V|Vs],List,[sum(Domain)|Ds]) :-
					proper_var_domain(V,List,List,D),
					remove_repeated(D,Domain),
					proper_vars_domains(Vs,List,Ds).

proper_var_domain(V,[],_,[]).
proper_var_domain(V,[C|Rest],List,FinalDomain) :- (
					occurs_in_sum(V,[C]) -> proper_domain(C,List,Domain);
					true -> Domain = []),
					proper_var_domain(V,Rest,List,OtherDomain),
					append(Domain,OtherDomain,TempDomain),
					remove_vars_from_list(TempDomain,FinalDomain).

occurs_in_sum(V,[eq(A,B)]) :- not(var(B)), B =.. [sum, List], occurs_in(V,List).

proper_domain(eq(A,B),List,Types) :-
					constructors_in(B,Cons),
					types_with_constructors(Cons,List,TypesFromCons),
					not_var_terms(B,Terms), append([A|Terms],TypesFromCons,Types).

not_var_terms(X,List) :-
					var(X) -> List = [];
					X = sum(Args) -> not_var_terms(Args,List);
					X = [] -> List = [];
					X = [A |As] -> not_var_terms(A,List1), not_var_terms(As,List2), append_without_repeating(List1,List2,List);
					X = basetype(_) -> List = [X];
					X =.. [_, _, _] -> List = [X].

constructors_in(B,List) :-
					var(B) -> List = [];
					B = [] -> List = [];
					B = [H] -> constructors_in(H,List);
					B = [H|T] -> constructors_in(H,List1), constructors_in(T,List2), append(List1,List2,List);
					B =.. [basetype, _] -> List = [];
					B = self -> List = [];
					B =.. [func, F, Args] -> List = [F];
					B =.. [tnam, Name, Args] -> List = [Name];
					B =.. [tvar, _, _, _] -> List = [];
					B =.. [sum, Summands] -> constructors_in(Summands,List).

types_with_constructors([],_,[]).
types_with_constructors([F|Fs],List,Final) :-
					types_with_constructor(F,List,Body),
					types_with_constructors(Fs,List,OtherBodies), append(Body,OtherBodies,Final).

types_with_constructor(F,[],[]).
types_with_constructor(F,[eq(A,B)|Cs],Final) :-
					is_in_constraint(F,B), !, (B = sum(List); List = [B]),
					types_with_constructor(F,Cs,Bs), not_var_terms(List,NList), append(NList,Bs,Final).
types_with_constructor(F,[_|Cs],Bs) :-
					types_with_constructor(F,Cs,Bs).

is_in_constraint(F,B) :- (
					var(B) -> fail;
					B = [H | T] -> (is_in_constraint(F,H); is_in_constraint(F,T));
					B = [] -> fail;
					B =.. [tvar | _] -> fail;
					B =.. [basetype, _] -> fail;
					B = self -> fail;
					B =.. [sum, Summands]-> is_in_constraint(F,Summands);
					B =.. [_, _, _] -> true).

remove_vars_from_list([],[]).
remove_vars_from_list([H|T],R) :- var(H), !, remove_vars_from_list(T,R).
remove_vars_from_list([H|T],[H|R]) :- remove_vars_from_list(T,R).

join_sums([X],sum([X])) :- var(X).
join_sums([sum(List)],sum(List)).
join_sums([X],sum([X])) :- X \= [].
join_sums([[]],sum([])).
join_sums([X|Rest],Sum) :- join_sums(Rest,sum(List)), (
					var(X) -> Sum = sum([X|List]);
					X = [] -> Sum = sum(List);
					X = sum(List1) -> append(List1,List,Final), Sum = sum(Final);
					true -> Sum = sum([X|List])).

apply_substitutions(_,_,[],[]).
apply_substitutions(Vars,Domains,[eq(A,B)|Ts],[eq(A,C)|NTs]) :-
					apply_substitutions_to_a_type(Vars,Domains,B,C),
					apply_substitutions(Vars,Domains,Ts,NTs).

apply_substitutions_to_a_type(Vars,Domains,B,C) :-
					(var(B) ->find_in_substitutions(B,Vars,Domains,C);
					B =.. [tvar, N, N, N] -> C = B;
					B =.. [tvar, _, _, _] -> find_in_substitutions(B,Vars,Domains,Domain),
										(do_sum(Domain,C); C = B);
					B =.. [func,F,Args] -> C =.. [func, F, Args];
					B =.. [basetype, _] -> C = B;
					B = self -> C = B;

					B =.. [tnam, Name, Args] -> apply_substitutions_to_args(Vars,Domains,Args,NArgs),
										C =.. [tnam, Name, NArgs];
					B =.. [sum, Summands] -> apply_substitutions_to_args(Vars,Domains,Summands,NSummands),
										join_sums(NSummands,C)).

apply_substitutions_to_args(_,_,[],[]).
apply_substitutions_to_args(Vars,Domains,[A|As],[B|Bs]) :-
					apply_substitutions_to_a_type(Vars,Domains,A,B),
					apply_substitutions_to_args(Vars,Domains,As,Bs).

find_in_substitutions(B,[],[],B).
find_in_substitutions(B,[B1|_],[D|_],D) :- B == B1, !.
find_in_substitutions(B,[_|Bs],[_|Ds],D) :- find_in_substitutions(B,Bs,Ds,D).

replace([],[],Final,Final).
replace([OT|OTs],[CT|CTs],ConstraintList,NewConstraintList) :-
					replace(OT,CT,ConstraintList,TempList),
					replace(OTs,CTs,TempList,NewConstraintList).
replace(OT,CT,[OT|Rest],[CT|Rest]) :- !.
replace(OT,CT,[DONT|Rest],[DONT|Other]) :- replace(OT,CT,Rest,Other).

self_remove([],[]).
self_remove([C|Cs],[NC|NCs]) :-
					self_remove_in_one(C,NC),
					self_remove(Cs,NCs).

self_remove_in_one(eq(A,B),eq(A,NB)) :-
					remove_self(B,C),
					remove_self(A,C,NB).

remove_self(A,Body,NBody) :-
					var(Body) -> NBody = Body;
					Body = self -> NBody = A;
					Body =.. [sum, Args] -> remove_self_in_args(A,Args,NArgs),NBody = sum(NArgs);
					Body =.. [func, F, Args] -> remove_self_in_args(A,Args,NArgs), NBody =.. [func, F, NArgs];
					true -> NBody = Body.

remove_self_in_args(_,[],[]).
remove_self_in_args(A,[Arg|Args],[NArg|NArgs]) :-
					remove_self(A,Arg,NArg), remove_self_in_args(A,Args,NArgs).

remove_self(D,E) :-
					var(D) -> E = D;
					D = sum(List)-> remove_self_from_list(List,NList), E = sum(NList);
					true -> E = D.

remove_self_from_list([],[]).
remove_self_from_list([self|Rest],Others) :- !, remove_self_from_list(Rest,Others).
remove_self_from_list([X|Rest],[X|Others]) :- remove_self_from_list(Rest,Others).




























%% PRINTING %%

print_solution(Head,Env,Solution) :-
					Head =.. [pred , P, Args],
					search_headvarstypes(Args,Env,Types),
					print_output(P,Solution,Types).

search_headvarstypes([],_,[]).
search_headvarstypes([V|Vs],Env,[T|Ts]) :- search_headvartype(V,Env,T), search_headvarstypes(Vs,Env,Ts).

search_headvartype(V,[(V,T)|_],T).
search_headvartype(V,[(_,_)|Rest],T) :- search_headvartype(V,Rest,T).

print_output(P,Solution,Types) :-
					write(P), write(' :: '), print_types(Types), nl,
					print_constraints(Types,Solution,[]), nl, nl.

print_types([]).
print_types([T|Ts]) :- (
					var(T) -> write(T);
					T =.. [sum, List] -> print_sum(List);
					T =.. [func, _, _] -> print_f(T);
					T =.. [tvar, P, A, N] -> (integer(P) -> write('$VAR'(P));
											true -> write(P), write(A), write('/'), write(N));
					T =.. [basetype, Base] -> write(Base);
					T =.. [tnam, Name, Args] -> write(Name), write('('), print_args(Args), write(')')
					), (
					Ts == [] -> print_types(Ts);
					Ts \= [] -> write(' x '), print_types(Ts) ).

print_constraints([],_,_).
print_constraints([T|Ts],Solution,Done) :-
					search_constraints(T,Solution,C), print_constraint(C), C = eq(T,B), new_types_on(B,New),
					not_on_done(New,[T|Done],NNew), append(Ts,NNew,Final),
					print_constraints(Final,Solution,[T|Done]).

search_constraints(T,[eq(T,C)|_],eq(T,C)) :- !.
search_constraints(T,[eq(T1,_)|Rest],C) :- T1 \= T, !, search_constraints(T,Rest,C).

new_types_on(B,List) :-
					var(B) -> List = [];
					B =.. [basetype, _] -> List = [];
					B =.. [tvar, _, _, _] -> List = [B];
					B =.. [sum, Lista] -> new_types_on_each(Lista,List);
					B =.. [tnam, _, _] -> List = [];
					B =.. [func, _, Args] -> new_types_on_each(Args,List).

new_types_on_each([],[]).
new_types_on_each([A|As],List) :- new_types_on(A,L), new_types_on_each(As,Ls), append(L,Ls,List).

not_on_done([],_,[]).
not_on_done([A|As],Done,Bs) :- (occurs_in(A,Done) -> not_on_done(As,Done,Bs);
					true -> not_on_done(As,Done,Cs), Bs = [A|Cs]).

print_constraint(eq(A1,B1)) :-
					A1 =.. [tvar, P, A, N] -> (integer(P) -> write('$VAR'(P));
										true -> write(P), write(A), write('/'), write(N)),
										write(' = '),
					(
					var(B1) -> write(B1);
					B1 =.. [basetype, Base] -> write(Base);
					B1 =.. [tvar, P2, A2, N2] -> (integer(P2) -> write('$VAR'(P2));
										true -> write(P2), write(A2), write('/'), write(N2));
					B1 = sum(List) -> print_sum(List);
					B1 =.. [tnam, Name, Args] -> write(Name), write('('), print_args(Args), write(')');
					B1 =.. [func, _, _] -> print_f(B1)), nl.

print_sum([A]) :- !, print_types([A]).
print_sum([A|B]) :- print_types([A]), write(' + '), print_sum(B).

print_f(func('.',[A,B])) :- write('[ '), print_types([A]), write(' | '), print_types([B]), write(' ]').
print_f(func('[|]',[A,B])) :- write('[ '), print_types([A]), write(' | '), print_types([B]), write(' ]').

print_f(func(C,[])) :- write(C).
print_f(func(F,Args)) :- write(F), write('('), print_args(Args), write(')').

print_args([A]) :- !, print_types([A]).
print_args([A|As]) :- print_types([A]), write(', '), print_args(As).

print_data([]).
print_data([type(Name,List)|Rest]) :- print_name_of_type(Name), print_type_definition(List), print_data(Rest).

print_name_of_type(tnam(Name,Args)) :- write(Name), write('('), print_args(Args), write(')'), write(' = ').

print_type_definition([One|Rest]) :- print_types([One]), (Rest \= [] -> write(' + '), print_type_definition(Rest); true -> writeln('')).