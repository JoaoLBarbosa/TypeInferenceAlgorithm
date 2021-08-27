%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%																										 %
%								    3 - RESOLUÇÃO DE CONSTRAINTS										 %
%																										 %
% solve_eq -> receives as input equality constraints and rewrites them until they are in normal form     %
%             then immediatly applies the final substitution to the inequalities and type definitions    %
% solve_ineq -> receives as input the inequality constraints and type definitions and outputs the        %
%               new type definitions that correspond to applying the substitution generated from solving %
% 				the equality constraints immediatly 													 %
% simplify -> simplifies the presentation of the type definitions, like removing duplicates, making sure %
%             the definitions are deterministic, etc... 												 %
% closure -> preforms closure on the type definitions if the flag is on 								 %
%																										 %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(clpfd)).

constraint_solve(Eq,Ineq,TypeDefs,FinalDefs) :-
					sort(Eq,NewEq),
					(solve_eq(NewEq); writeln('Equality Constraint Solver failed on constraints: '), writeln(Eq), writeln(TypeDefs), fail), !,
					(simplify_type_definitions(TypeDefs,SimplifiedTypeDefs); writeln('Simplification failed on type defs: '), writeln(TypeDefs), fail), !,
					sort(Ineq,NewIneq),
					(solve_ineq(NewIneq,SimplifiedTypeDefs,[],NewDefs); writeln('Subtyping Constraint Solver failed on constraints: '), writeln(Ineq), writeln(SimplifiedTypeDefs), fail),
					(clean_output(NewDefs,CleanDefs); writeln('Somehow Cleaning the output failed on type defs: '), writeln(NewDefs), fail),!,
					(closure_flag(on) -> (closure(CleanDefs,FinalDefs); writeln('Closure failed on type defs: '), writeln(CleanDefs), fail);
						true -> FinalDefs = CleanDefs).


% Equality Constraint Solving Algorithm
%
% 1. t = t, Rest -> Rest
% 2. \alpha = t, Rest -> Rest [\alpha -> t]
% 3. t = \alpha, Rest -> \alpha = t, Rest, where \alpha var and t not var
% 4. f(t1,...,tn) = f(s1,...,sn), Rest -> t1 = s1, ..., tn = sn, Rest
% 5. otherwise -> fail


solve_eq([]).
solve_eq(Eqs) :- (
			case1(Eqs,Constraint) -> remove_constraint(Constraint,Eqs,NewEqs),
								solve_eq(NewEqs);
			case2(Eqs,Constraint) -> remove_constraint(Constraint,Eqs,NewEqs),
								Constraint = eq(X, Rest), X = Rest, !,
								solve_eq(NewEqs) ;
			case3(Eqs,Constraint) -> remove_constraint(Constraint,Eqs,NewEqs),
								Constraint = eq(Arg1,Arg2), NewConstraint = eq(Arg2,Arg1),
								solve_eq([NewConstraint|NewEqs]);
			case4(Eqs,Constraint) -> remove_constraint(Constraint,Eqs,TempEqs),
								Constraint = eq(T1, T2),
								T1 =.. [FuncOrName, F, Args1], T2 =.. [FuncOrName, F, Args2],
								gen_eq_cons(Args1,Args2,Temps), append(Temps,TempEqs,NewEqs), !,
								solve_eq(NewEqs);
			case5(Eqs,_) -> !, fail
			).



% The 5 cases for the Algorithm:


% t = t

case1([eq(T1,T2)|_],eq(T1,T2)) :- T1 == T2, !.
case1([_|Cs],C1) :- case1(Cs,C1).

% x = T and x a var

case2([eq(T1,T2)|_],Constraint) :- var(T1), (var(T2); true), occur_check(T1,T2), !,
					Constraint = eq(T1,T2).
case2([_|Cs],Cons) :- case2(Cs,Cons).

% t = x, t not a var, x a var

case3([eq(T1,T2)|_],eq(T1,T2)) :- not(var(T1)), var(T2), !.
case3([_|Cs],C1) :- case3(Cs,C1).

% f(t1,...,tn) = f(s1,...,sn)

case4([eq(T1,T2)|_],eq(T1,T2)) :- T1 = func(F, _), T2 = func(F, _), !.
case4([eq(T1,T2)|_],eq(T1,T2)) :- T1 = tnam(N, _), T2 = tnam(N, _), !.
case4([_|Cs],C1) :- case4(Cs,C1).


% f(t1,...,tn) = g(s1,...,sn), f \= g

case5([eq(T1,T2)|_],eq(T1,T2)) :- T1 = func(F, _), T2 = func(G , _), F \= G, !.
case5([eq(T1,T2)|_],eq(T1,T2)) :- T1 = basetype(F), T2 = basetype(G), F \= G, !.
case5([eq(T1,T2)|_],eq(T1,T2)) :- T1 = tnam(F, _), T2 = tnam(G , _), F \= G, !.
case5([eq(T1,T2)|_],eq(T1,T2)) :- T1 = basetype(_), T2 = func(_, _), !.
case5([eq(T1,T2)|_],eq(T1,T2)) :- T2 = basetype(_), T1 = func(_, _), !.
case5([eq(T1,T2)|_],eq(T1,T2)) :- T1 = basetype(_), T2 = tnam(_, _), !.
case5([eq(T1,T2)|_],eq(T1,T2)) :- T2 = basetype(_), T1 = tnam(_, _), !.
case5([_|Cs],C1) :- !, case5(Cs,C1).

% occur_check

occur_check(T,T1) :- var(T1), T == T1, !, fail.
occur_check(T,tvar(P,A,N)) :- T == tvar(P,A,N), !,fail.
occur_check(T,basetype(K)) :- T == basetype(K), !, fail.
occur_check(T,T1) :- not(var(T1)), T1 =.. [_, _, Args], !, occur_check_args(T,Args).
occur_check(T,T1) :- not(var(T1)), T1 =.. ['[|]' | Args],!, occur_check_args(T,Args).
occur_check(T,T1) :- T == T1, !, fail.
occur_check(_,_).

occur_check_args(T,[A|As]) :- occur_check(T,A), occur_check_args(T,As).
occur_check_args(_,[]).

% removes a constraint from a list of constraints

remove_constraint(C,[C1|Cs],Cs) :- C == C1, !.
remove_constraint(C,[X|Cs],[X|Xs]) :- remove_constraint(C,Cs,Xs).


% Subtyping Constraint Solving Algorithm
%
% 1. t <= t, Rest -> Rest
% 2. f(t1,...,tn) <= f(s1,...,sn), Rest -> t1 <= s1, ..., tn <= sn, Rest
% 3. \alpha <= t1, \alpha <= t2, Rest -> \alpha <= t, Rest, where t = intersect(t1,t2)
% 4. \alpha <= t, Rest -> Rest [\alpha -> t]
% 5. t1 + ... + tn <= t, Rest -> t1 <= t, ..., tn <= t, Rest
% 6. typename <= t, Rest -> Rest, if already_compared(typename,t)
% 7. typename <= t, Rest -> def(typename) <= t, Rest
% 8. t1 <= \alpha, ..., tn <= \alpha, Rest -> Rest [\alpha -> t1 + ... + tn]
% 9. t <= t1 + ... + tn, Rest -> t <= ti, Rest, for some 1 <= i <= n
% 10. t <= typename, Rest -> Rest, if already_compared(t,typename)
% 11. t <= typename, Rest -> t <= def(typename), Rest
% 12. otherwise -> fail
%
% Ainda precisa se ser resolvido o facto de, ao unificar variáveis com tipos, posso estar a unificar com uma soma e isso precisa de ser simplificado
% porque pode dar problemas.
% A solução perfeita seria ter um algoritmo de simplificação que corria a cada passo do solver. Mas isso pode atrasar bastante a execução caso não
% seja eficiente. Para além disso, deveria ser dependente? Ou será que é sequer dependente? Ou é mesmo só um problema técnico da implementação em vez
% de teórico do algoritmo? Nesse caso precisa de ficar sequer explícito no paper?

solve_ineq([],FinalDefs,_,FinalDefs).
solve_ineq(Ineq,TypeDefs,HaltCondition,NewDefs) :- (
					icase1(Ineq,Constraint) -> remove_constraint(Constraint,Ineq,NIneq),
										solve_ineq(NIneq,TypeDefs,HaltCondition,NewDefs);
					icase2(Ineq,Constraint) -> remove_constraint(Constraint,Ineq,NIneq),
										Constraint =.. [_, T1, T2],
										T1 =.. [_,_,Args1],
										T2 =.. [_,_,Args2],
										gen_subt_cons(Args1,Args2,MoreIneqs),
										append(MoreIneqs,NIneq,FIneq),
										solve_ineq(FIneq,TypeDefs,HaltCondition,NewDefs);
					icase3(Ineq,Constraint1,Constraint2,TypeDefs) -> remove_constraint(Constraint1,Ineq,Ineq2),
										remove_constraint(Constraint2,Ineq2,Ineq3),
										Constraint1 =.. [_,X,T1],
										Constraint2 =.. [_,X,T2],
										intersect(T1,T2,TypeDefs,[],T,TempDefs,out),
										simplify_type_definitions(TempDefs,NewTempDefs),
										Sub = ineq(X,T),
										solve_ineq([Sub|Ineq3],NewTempDefs,HaltCondition,NewDefs);
					icase4(Ineq,Constraint,TypeDefs) -> remove_constraint(Constraint,Ineq,NIneq),
										Constraint = ineq(T1, T2),
										T1 = T2, simplify_type_definitions(TypeDefs,NewTypeDefs),
										solve_ineq(NIneq,NewTypeDefs,HaltCondition,NewDefs);
					icase5(Ineq,Constraint) -> remove_constraint(Constraint,Ineq,NIneq),
										Constraint = ineq(List, T),
										for_each_generate_subt(List,T,TempIneq),
										append(TempIneq,NIneq,FIneq),
										solve_ineq(FIneq,TypeDefs,HaltCondition,NewDefs);
					icase6(Ineq,Constraint,HaltCondition,TypeDefs) -> remove_constraint(Constraint,Ineq,NIneq),
										solve_ineq(NIneq,TypeDefs,HaltCondition,NewDefs);
					icase7(Ineq,Constraint,TypeDefs) -> remove_constraint(Constraint,Ineq,NIneq),
										Constraint =.. [_, Type, T],
										get_from_definitions(Type,TypeDefs,Def), (
										length(Def,1) -> Def = [D], TempIneq = ineq(D,T);
										true -> TempIneq = ineq(Def,T) ),
										NewHaltCondition = [already_compared(Type,T)|HaltCondition],
										append([TempIneq],NIneq,FIneq),
										solve_ineq(FIneq,TypeDefs,NewHaltCondition,NewDefs);
					icase8(Ineq,Var,Constraints,TypeDefs) -> remove_all_constraints(Constraints,Ineq,NIneq), (
										length(Constraints,1) ->
											Constraints = [ineq(Left,Var)], Var = Left, NTypeDefs = TypeDefs;
										true ->
											get_all_lefts(Constraints,Lefts), gen_type_definitions([Var],[Lefts],[Type]),
											NTypeDefs = [Type|TypeDefs] ),
										simplify_type_definitions(NTypeDefs,NewTypeDefs),
										solve_ineq(NIneq,NewTypeDefs,HaltCondition,NewDefs);
					icase9(Ineq,Constraint) -> remove_constraint(Constraint,Ineq,NIneq),
										Constraint = ineq(T, List), !,
										(search_for_compatible(T,List,List,TypeDefs,T1) ->
											Sub = ineq(T, T1),
											solve_ineq([Sub|NIneq],TypeDefs,HaltCondition,NewDefs);
										var(T) ->
											T = List, simplify_type_definitions(TypeDefs,TempTypeDefs),
											solve_ineq(NIneq,TempTypeDefs,HaltCondition,NewDefs);
										true -> search_for_a_var_occur_check(T,List,V),
											T = V, simplify_type_definitions(TypeDefs,TempTypeDefs),
											solve_ineq(NIneq,TempTypeDefs,HaltCondition,NewDefs) );

											% alternativa que não funciona sem "anti-unificação"
											% 
											% for_each_generate_subt_right(T,List,Subs),
											% distribute_among_ineq_sets(Subs,NIneq,NewIneqSets),
											% solve_several_ineq_sets(NewIneqSets,TypeDefs,HaltCondition,NewTypeDefs),
											% merge(NewTypeDefs,NewDefs) );
					icase10(Ineq,Constraint,HaltCondition,TypeDefs) -> remove_constraint(Constraint,Ineq,NIneq),
										solve_ineq(NIneq,TypeDefs,HaltCondition,NewDefs);
					icase11(Ineq,Constraint,TypeDefs) -> remove_constraint(Constraint,Ineq,NIneq),
										Constraint =.. [_, T, Type],
										get_from_definitions(Type,TypeDefs,Def), (
										length(Def,1) -> Def = [D], TempIneq = ineq(T,D);
										true -> TempIneq = ineq(T,Def) ), 
										NewHaltCondition = [already_compared(T,Type)|HaltCondition],
										append([TempIneq],NIneq,FIneq),
										solve_ineq(FIneq,TypeDefs,NewHaltCondition,NewDefs);
					true -> fail ).


% The 11 cases for the algorithm

% t <= t

icase1([C|_],C) :- C = ineq(A, B), A == B, !.
icase1([C|_],C) :- C = ineq(A, B), A == basetype(int), B == tnam(num,[]), !.
icase1([C|_],C) :- C = ineq(A, B), A == basetype(float), B == tnam(num,[]), !.
icase1([_|Cs],C) :- icase1(Cs,C).

% f(t1,...,tn) <= f(s1,...,sn)

icase2([C|_],C) :- C = ineq(A, B),
					not(var(A)), A =.. [FuncOrName, F, _],
					not(var(B)), B =.. [FuncOrName, F, _], !.
icase2([_|Cs],C) :- icase2(Cs,C).

% \alpha <= t1, \alpha <= t2

icase3([C1|Cs],C1,C2,TypeDefs) :- C1 =  ineq(V, _), var(V), not(is_in_type_defs(V,TypeDefs)), other_constraint_alpha(V,Cs,C2), !.
icase3([_|Cs],C1,C2,TypeDefs) :- icase3(Cs,C1,C2,TypeDefs).

other_constraint_alpha(V,[C|_],C) :- C = ineq(T1, _), T1 == V, !.
other_constraint_alpha(V,[_|Cs],C) :- other_constraint_alpha(V,Cs,C).

% \alpha <= t

icase4([C|_],C,TypeDefs) :- C = ineq(A, B), var(A), not(is_in_type_defs(A,TypeDefs)), (var(B);not(B = [_|_])),!.
icase4([_|Cs],C,TypeDefs) :- icase4(Cs,C,TypeDefs).

% t1 + ... + tn <= t

icase5([C|_],C) :- C = ineq(A, _), not(var(A)), is_list(A), !.
icase5([_|Cs],C) :- icase5(Cs,C).

% typename <= t and already_compared(typename,t)

icase6([C|_],C,List,TypeDefs) :- C = ineq(A, B), var(A), is_in_type_defs(A,TypeDefs), is_in(already_compared(A,B),List), !.
icase6([C|_],C,List,_) :- C = ineq(A, B), not(var(A)), A = tvar(_,_,_), is_in(already_compared(A,B),List), !.
icase6([_|Cs],C,List,TypeDefs) :- icase6(Cs,C,List,TypeDefs).

% typename <= t

icase7([C|_],C,TypeDefs) :- C = ineq(A, _), var(A), is_in_type_defs(A,TypeDefs), !.
icase7([C|_],C,_) :- C = ineq(A, _), not(var(A)), A = tvar(_,_,_), !.
icase7([_|Cs],C,TypeDefs) :- icase7(Cs,C,TypeDefs).

% t1 <= \alpha , ... , tn <= \alpha

icase8([C|Cs],V,ListOfConstraints,TypeDefs) :-
					C = ineq(A, B), var(B), not(is_in_type_defs(B,TypeDefs)), occur_check(B,A),
					other_constraints_beta(B,Cs,TempList),
					V = B, ListOfConstraints = [C|TempList].
icase8([_|Cs],V,L,TypeDefs) :- icase8(Cs,V,L,TypeDefs).

other_constraints_beta(_,[],[]).
other_constraints_beta(V,[C|Cs],[C|Rest]) :- C = ineq(A, B), V == B, occur_check(B,A), !, other_constraints_beta(V,Cs,Rest).
other_constraints_beta(V,[_|Cs],Rest) :- other_constraints_beta(V,Cs,Rest).

% t <= t1 + ... + tn

icase9([C|_],C) :- C = ineq(_, B), not(var(B)), is_list(B), !.
icase9([_|Cs],C) :- icase9(Cs,C).

% t <= typename and already_compared(t,typename)

icase10([C|_],C,List,TypeDefs) :- C = ineq(A, B), var(B), is_in_type_defs(B,TypeDefs), is_in(already_compared(A,B),List), !.
icase10([C|_],C,List,_) :- C = ineq(A, B), not(var(B)), B = tvar(_,_,_), is_in(already_compared(A,B),List), !.
icase10([_|Cs],C,List,TypeDefs) :- icase10(Cs,C,List,TypeDefs).

% t <= typename

icase11([C|_],C,TypeDefs) :- C = ineq(_, B), var(B), is_in_type_defs(B,TypeDefs), !.
icase11([C|_],C,_) :- C = ineq(_, B), not(var(B)), B = tvar(_,_,_), !.
icase11([_|Cs],C,TypeDefs) :- icase11(Cs,C,TypeDefs).


for_each_generate_subt([],_,[]).
for_each_generate_subt([A|As],B,[ineq(A,B)|Ss]) :-
					for_each_generate_subt(As,B,Ss).

for_each_generate_subt_right(_,[],[]).
for_each_generate_subt_right(A,[B|Bs],[ineq(A,B)|Ss]) :-
					for_each_generate_subt_right(A,Bs,Ss).

remove_all_constraints([],R,R).
remove_all_constraints([C|Cs],List,NewList) :-
					remove_constraint(C,List,TempList),
					remove_all_constraints(Cs,TempList,NewList).

get_all_lefts([],[]).
get_all_lefts([ineq(A,_)|Ss],[A|As]) :- get_all_lefts(Ss,As).

search_for_compatible(T,[],L,TypeDefs,T1) :- var(T), search_for_a_var(L,TypeDefs,T1).
search_for_compatible(T,[A|As],L,TypeDefs,T1) :- (
					var(T), T == A -> T1 = T;
					not(var(T)), T =.. [FuncOrName, F, _], not(var(A)), A =.. [FuncOrName, F, _] -> T1 = A;
					T == A -> T1 = A;
					true -> search_for_compatible(T,As,L,TypeDefs,T1) ).

search_for_a_var([V|_],TypeDefs,Out) :- var(V), not(is_in_type_defs(V,TypeDefs)), !, Out = V.
search_for_a_var([_|Vs],TypeDefs,Out) :- search_for_a_var(Vs,TypeDefs,Out).

search_for_a_var_occur_check(T,[V|_],V) :- var(V), occur_check(V,T), !.
search_for_a_var_occur_check(T,[_|Vs],V) :- search_for_a_var_occur_check(T,Vs,V).

distribute_among_ineq_sets([],_,[]).
distribute_among_ineq_sets([S|Ss],Ineqs,[[S|Ineqs]|MoreIneqs]) :-
					distribute_among_ineq_sets(Ss,Ineqs,MoreIneqs).

solve_several_ineq_sets([],_,_,[]).
solve_several_ineq_sets([Ineq|Ineqs],TypeDefs,HaltCondition,[NewDefs|MoreNewDefs]) :-
					(solve_ineq(Ineq,TypeDefs,HaltCondition,NewDefs);NewDefs = []),
					solve_several_ineq_sets(Ineqs,TypeDefs,HaltCondition,MoreNewDefs).

merge(NewTypeDefs,NewDefs) :- merge(NewTypeDefs,[],NewDefs).

merge([],Final,TheFinal) :- simplify_type_definitions(Final,TheFinal).
merge([Set|Sets],Acc,Final) :-
					merge_one(Set,Acc,NewAcc),
					merge(Sets,NewAcc,Final).

merge_one([],Final,Final).
merge_one([def(T,Def)|Defs],Acc,Final) :- (
					member(def(T,Def2),Acc) ->
										remove_from_list(def(T,Def2),Acc,TempAcc),
										append_without_repeating(Def,Def2,Def3),
										NewAcc = [def(T,Def3)|TempAcc];
					true -> NewAcc = [def(T,Def)|Acc] ),
					merge_one(Defs,NewAcc,Final).

remove_from_list(A,[B|Bs],Bs) :- A == B, !.
remove_from_list(A,[B|Bs],[B|As]) :- remove_from_list(A,Bs,As).

append_without_repeating([],List,List).
append_without_repeating([H|T],ListB,FinalList) :- (
					is_in(H,ListB) -> append_without_repeating(T,ListB,FinalList);
					true -> append_without_repeating(T,[H|ListB],FinalList) ).

is_in(H,[T|_]) :- H == T, !.
is_in(H,[_|Ts]) :- is_in(H,Ts).

is_in_type_defs(H,[def(T,_)|_]) :- H == T, !.
is_in_type_defs(H,[_|Rest]) :- is_in_type_defs(H,Rest).

% Intersection Algorithm
% 
% Termination: [(T1,T2,T)], where intersect(T1,T2) = T
% Care of empty types:
%		intersect(T1,T2) = fail | f(...,fail,...) | def(Typename,[])

intersect(T1,T2,TypeDefs,Termination,T,FinalDefs,Flag) :- (
					T1 == T2 -> T = T1, FinalDefs = TypeDefs;
					var(T1), not(is_in_type_defs(T1,TypeDefs)), var(T2), not(is_in_type_defs(T2,TypeDefs)) ->
										T1 = T2, T = T1, FinalDefs = TypeDefs;
					var(T1), not(is_in_type_defs(T1,TypeDefs)) -> (Flag == in;T1 = T2), T = T2, FinalDefs = TypeDefs;
					var(T2), not(is_in_type_defs(T2,TypeDefs)) -> (Flag == in;T1 = T2), T = T1, FinalDefs = TypeDefs;
					is_in(pair(T1,T2,Tf),Termination) -> T = Tf, 
					var(T1), is_in_type_defs(T1,TypeDefs), var(T2), is_in_type_defs(T2,TypeDefs) ->
										gen_fresh_type(1,[Temp]),
										get_from_definitions(T1,TypeDefs,Def1),
										get_from_definitions(T2,TypeDefs,Def2),
										cpi(Def1,Def2,TypeDefs,[(T1,T2,Temp)|Termination],FinalDef,FinalTypeDefs), (
										FinalDef = [] -> T = fail;
										true -> T = Temp ),
										FinalDefs = [def(Temp,FinalDef)|FinalTypeDefs];
					(var(T1), is_in_type_defs(T1,TypeDefs), T2 = tvar(_,_,_);
					 var(T2), is_in_type_defs(T2,TypeDefs), T1 = tvar(_,_,_);
					 T1 = tvar(_,_,_), T2 = tvar(_,_,_)) ->
										gen_fresh_type(1,[Temp]),
										get_from_definitions(T1,TypeDefs,Def1),
										get_from_definitions(T2,TypeDefs,Def2),
										cpi(Def1,Def2,TypeDefs,[(T1,T2,Temp)|Termination],FinalDef,FinalTypeDefs), (
										FinalDef = [] -> T = fail;
										true -> T = Temp ),
										FinalDefs = [def(Temp,FinalDef)|FinalTypeDefs];
					var(T1), is_in_type_defs(T1,TypeDefs) ->
										gen_fresh_type(1,[Temp]),
										get_from_definitions(T1,TypeDefs,Def1),
										cpi(Def1,[T2],TypeDefs,[(T1,T2,Temp)|Termination],FinalDef,FinalTypeDefs), (
										FinalDef = [] -> T = fail;
										true -> T = Temp ),
										FinalDefs = [def(Temp,FinalDef)|FinalTypeDefs];
					var(T2), is_in_type_defs(T2,TypeDefs) -> 
										gen_fresh_type(1,[Temp]),
										get_from_definitions(T2,TypeDefs,Def2),
										cpi([T1],Def2,TypeDefs,[(T1,T2,Temp)|Termination],FinalDef,FinalTypeDefs), (
										FinalDef = [] -> T = fail;
										true -> T = Temp ),
										FinalDefs = [def(Temp,FinalDef)|FinalTypeDefs];
					T1 = tvar(_,_,_) ->
										gen_fresh_type(1,[Temp]),
										get_from_definitions(T1,TypeDefs,Def1),
										cpi(Def1,[T2],TypeDefs,[(T1,T2,Temp)|Termination],FinalDef,FinalTypeDefs), (
										FinalDef = [] -> T = fail;
										true -> T = Temp ),
										FinalDefs = [def(Temp,FinalDef)|FinalTypeDefs];
					T2 = tvar(_,_,_) -> 
										gen_fresh_type(1,[Temp]),
										get_from_definitions(T2,TypeDefs,Def2),
										cpi([T1],Def2,TypeDefs,[(T1,T2,Temp)|Termination],FinalDef,FinalTypeDefs), (
										FinalDef = [] -> T = fail;
										true -> T = Temp ),
										FinalDefs = [def(Temp,FinalDef)|FinalTypeDefs];
					T1 =.. [FuncOrName, F, Args1], T2 =.. [FuncOrName, F, Args2] ->
										intersect_args(Args1,Args2,TypeDefs,Termination,FinalArgs,FinalDefs,Flag), (
										if_any_fail(FinalArgs) -> T = fail;
										true ->	T =.. [FuncOrName, F, FinalArgs] )
										;
					true -> T = fail, FinalDefs = TypeDefs
					).

intersect_args([],[],TypeDefs,_,[],TypeDefs,_).
intersect_args([T1|T1s],[T2|T2s],TypeDefs,Termination,[T|Ts],NDefs,Flag) :-
					intersect(T1,T2,TypeDefs,Termination,T,FDefs,Flag),
					intersect_args(T1s,T2s,FDefs,Termination,Ts,NDefs,Flag).

cpi([],_,TypeDefs,_,[],TypeDefs).
cpi([A|As],Bs,TypeDefs,Termination,Fs,FDefs) :-
					cpi_right(A,Bs,TypeDefs,Termination,Cs,NDefs),
					cpi(As,Bs,NDefs,Termination,Css,FDefs),
					append(Cs,Css,Fs).

cpi_right(_,[],TypeDefs,_,[],TypeDefs).
cpi_right(A,[B|Bs],TypeDefs,Termination,[C|Cs],FDefs) :-
					intersect(A,B,TypeDefs,Termination,C,NDefs,in), C \= fail, !,
					cpi_right(A,Bs,NDefs,Termination,Cs,FDefs).
cpi_right(A,[_|Bs],TypeDefs,Termination,Cs,FDefs) :-
					cpi_right(A,Bs,TypeDefs,Termination,Cs,FDefs).

if_any_fail([X|_]) :- X == fail.
if_any_fail([_|L]) :- if_any_fail(L).



% SIMPLIFICATION ALGORITHM
% 
% Make sure that type definitions are deterministic, i.e.:
%
% 1. A type symbol cannot occur as a summand of a type definitions
% 2. If there is a complex type term as a summand of a type definition, starting with a function symbol f,
%    then there is no other summand starting with that same function symbol

% simplify_type_definitions(TypeDefs,FinalDefs) :-
%					remove_duplicates(TypeDefs,NoDupTypeDefs),
%					flatten_defs(NoDupTypeDefs,FlatTypeDefs),
%					remove_equal_types(FlatTypeDefs),
%					remove_extra_types(FlatTypeDefs,TempTypeDefs),
%					replace_by_self(TempTypeDefs,SelfTypeDefs),
%					expand_type_in_def(SelfTypeDefs,SelfTypeDefs,ExpandedTypeDefs),
%					remove_duplicates(ExpandedTypeDefs,NoDupExpTypeDefs),
%					remove_equal_types(NoDupExpTypeDefs),
%					remove_extra_types(NoDupExpTypeDefs,SingleSelfTypeDefs),
%					gather_constructor(SingleSelfTypeDefs,NewTypeDefs),
%					remove_self_from_sum(NewTypeDefs,BetterTypeDefs),
%					if_singleton(BetterTypeDefs,SimpleTypeDefs),
%					remove_self_from_sum(SimpleTypeDefs,SimplerTypeDefs),
%					remove_equal_types(SimplerTypeDefs),
%					remove_extra_types(SimplerTypeDefs,BestTypeDefs),
%					replace_self_back(BestTypeDefs,FinalTypeDefs), (
%					FinalTypeDefs == TypeDefs -> FinalDefs = FinalTypeDefs;
%					true -> simplify_type_definitions(FinalTypeDefs,FinalDefs)
%					).

simplify_type_definitions(TypeDefs,FinalDefs) :-
					sort(TypeDefs,SortedTypeDefs),
					remove_selfish_from_sum(SortedTypeDefs,NSortedTypeDefs),
					remove_equal_types(NSortedTypeDefs),
					remove_extra_types(NSortedTypeDefs,NoDupTypeDefs),
					replace_by_self(NoDupTypeDefs,SelfTypeDefs),
					remove_equal_types(SelfTypeDefs),
					remove_extra_types(SelfTypeDefs,NoDupSelfTypeDefs),
					expand_type_in_def(NoDupSelfTypeDefs,NoDupSelfTypeDefs,ExpandedTypeDefs),
					sort_all(ExpandedTypeDefs,NoDupExpandedTypeDefs),
					remove_equal_types(NoDupExpandedTypeDefs),
					remove_extra_types(NoDupExpandedTypeDefs,SingleSelfTypeDefs),
					replace_self_back(SingleSelfTypeDefs,SimpleTypeDefs),
					gather_constructor(SimpleTypeDefs,NewTypeDefs),
					remove_equal_types(NewTypeDefs),
					remove_extra_types(NewTypeDefs,BetterTypeDefs),
					if_singleton(BetterTypeDefs,FinalTypeDefs), (
					FinalTypeDefs == TypeDefs -> FinalDefs = FinalTypeDefs;
					true -> simplify_type_definitions(FinalTypeDefs,FinalDefs)
					).

sort_all([],[]).
sort_all([def(T,Def)|Defs],[def(T,BestDef)|NoDupDefs]) :-
					flatten(Def,TempDef),
					sort(TempDef,SortedDef),
					arit_case(SortedDef,BestDef), sort_all(Defs,NoDupDefs).

arit_case([],[]).
arit_case([X|Rest],[X|NewRest]) :-
					X == tnam(num,[]),
					(remove_from_list(basetype(int),Rest,TempRest);TempRest = Rest),
					(remove_from_list(basetype(float),TempRest,NewRest);NewRest = TempRest).
arit_case([X|Rest],NewRest) :-
					(X == basetype(int); X == basetype(float)),
					is_in(tnam(num,[]),Rest),
					(remove_from_list(basetype(int),Rest,TempRest);TempRest = Rest),
					(remove_from_list(basetype(float),TempRest,NewRest);NewRest = TempRest).
arit_case([X|Rest],[X|NewRest]) :- arit_case(Rest,NewRest).

remove_equal_types([]).
remove_equal_types([def(T,Def)|Defs]) :-
					remove_equal_to_this_type(def(T,Def),Defs),
					remove_equal_types(Defs).

remove_equal_to_this_type(_,[]).
remove_equal_to_this_type(def(T,Def),[def(T1,Def1)|Defs]) :- are_the_same(Def,Def1), T1 = T, remove_equal_to_this_type(def(T,Def),Defs).
remove_equal_to_this_type(def(T,Def),[_|Defs]) :- remove_equal_to_this_type(def(T,Def),Defs).

are_the_same(Def,Def1) :- all_one_in_two(Def,Def1), all_one_in_two(Def1,Def).

all_one_in_two([],_).
all_one_in_two([X|Xs],Def) :- is_in(X,Def), all_one_in_two(Xs,Def).

remove_extra_types([],[]).
remove_extra_types([def(T,_)|Defs],Rest) :- is_in_type_defs(T,Defs), !, remove_extra_types(Defs,Rest).
remove_extra_types([def(T,Def)|Defs],[def(T,Def)|Rest]) :- remove_extra_types(Defs,Rest).


flatten([],[]).
flatten([X|Xs],List) :- is_list(X), !, flatten(Xs,Temp), append(X,Temp,List).
flatten([X|Xs],[X|Rest]) :- flatten(Xs,Rest).

remove_duplicates_from_list([],[]).
remove_duplicates_from_list([A|As],Final) :- is_in(A,As), !, remove_duplicates_from_list(As,Final).
remove_duplicates_from_list([A|As],[A|Final]) :- remove_duplicates_from_list(As,Final).

replace_by_self([],[]).
replace_by_self([def(T,Def)|Defs],[def(T,NDef)|NDefs]) :-
					replace_by_self_in_one(T,Def,NDef),
					replace_by_self(Defs,NDefs).

replace_by_self_in_one(_,[],[]).
replace_by_self_in_one(T,[T1|T1s],[T2|T2s]) :- (
					T1 == T -> T2 = self;
					var(T1) -> T2 = T1;
					T1 =.. [FuncOrName, F, Args] -> replace_by_self_in_args(T,Args,NArgs), T2 =.. [FuncOrName, F, NArgs];
					true -> T2 = T1 ),
					replace_by_self_in_one(T,T1s,T2s).

replace_by_self_in_args(_,[],[]).
replace_by_self_in_args(T,[A|As],[B|Bs]) :- (
					T == A -> B = self;
					var(A) -> B = A;
					A =.. [FuncOrName, F, Args] -> replace_by_self_in_args(T,Args,NArgs), B =.. [FuncOrName, F, NArgs];
					true -> B = A ),
					replace_by_self_in_args(T,As,Bs).

remove_selfish_from_sum([],[]).
remove_selfish_from_sum([def(Type,Def)|Defs],[def(Type,NDef)|NDefs]) :-
					(remove_from_list(Type,Def,NDef);NDef = Def),
					remove_selfish_from_sum(Defs,NDefs).



remove_self_from_sum([],[]).
remove_self_from_sum([def(Type,Def)|Defs],[def(Type,NewDef)|NewDefs]) :- (
					length(Def,N), N > 1 -> remove_self_from_def(Def,NewDef);
					true -> NewDef = Def), remove_self_from_sum(Defs,NewDefs).


remove_self_from_def([],[]).
remove_self_from_def([A|As],Bs) :- A == self, !, remove_self_from_def(As,Bs).
remove_self_from_def([A|As],[A|Bs]) :- remove_self_from_def(As,Bs).


replace_self_back([],[]).
replace_self_back([def(T,Def)|Defs],[def(T,NDef)|NDefs]) :-
					replace_self_back_in_one(T,Def,NDef),
					replace_self_back(Defs,NDefs).

replace_self_back_in_one(_,[],[]).
replace_self_back_in_one(T,[T1|T1s],[T2|T2s]) :- (
					var(T1) -> T2 = T1;
					T1 =.. [FuncOrName, F, Args] -> replace_self_back_in_args(T,Args,NArgs), T2 =.. [FuncOrName, F, NArgs];
					T1 == self -> T2 = T;
					true -> T2 = T1 ),
					replace_self_back_in_one(T,T1s,T2s).

replace_self_back_in_args(_,[],[]).
replace_self_back_in_args(T,[A|As],[B|Bs]) :- (
					var(A) -> B = A;
					A == self -> B = T;
					A =.. [FuncOrName, F, Args] -> replace_self_back_in_args(T,Args,NArgs), B =.. [FuncOrName, F, NArgs];
					true -> B = A ),
					replace_self_back_in_args(T,As,Bs).
					

expand_type_in_def([],_,[]).
expand_type_in_def([def(T,Def)|MoreDefs],TypeDefs,[def(T,NDef)|OtherDefs]) :-
					types_in_def(Def,TypeDefs,Types,DefWithoutTypes),
					get_from_defs(Types,TypeDefs,Defs),
					cup([DefWithoutTypes|Defs],NDef),
					expand_type_in_def(MoreDefs,TypeDefs,OtherDefs).

types_in_def([],_,[],[]).
types_in_def([T|Ts],TypeDefs,[T|Rest],Other) :-
					var(T), is_in_type_defs(T,TypeDefs),
					types_in_def(Ts,TypeDefs,Rest,Other).
types_in_def([T|Ts],TypeDefs,[T|Rest],Other) :-
					not(var(T)), T = tvar(_,_,_),
					types_in_def(Ts,TypeDefs,Rest,Other).
types_in_def([T|Ts],TypeDefs,Rest,Other) :-
					not(var(T)), T == self, Ts \= [],
					types_in_def(Ts,TypeDefs,Rest,Other).
types_in_def([T|Ts],TypeDefs,Rest,[T|Other]) :-
					types_in_def(Ts,TypeDefs,Rest,Other).


gather_constructor([],[]).
gather_constructor([def(T,Def)|MoreDefs],[def(T,NDef)|OtherDefs]) :-
					%replace_self_back_in_one(T,Def,TempDef),
					gather_constructor_for_one(Def,NDef,ExtraDefs),
					%replace_by_self_in_one(T,NDef,FinalDef),
					append(ExtraDefs,MoreDefs,NextDefs),
					gather_constructor(NextDefs,OtherDefs).

gather_constructor_for_one([],[],[]).
gather_constructor_for_one([T|Ts],Def,FinalExtra) :- (
					var(T) -> T2 = T, Tss = Ts, Extra = [];
					T =.. [FuncOrName, F, Args] -> other_occurences(T,Ts,Oc,Tss), sum_pointwise([Args|Oc],Final,Extra), T2 =.. [FuncOrName, F, Final];
					true -> T2 = T, Tss = Ts, Extra = []
					), gather_constructor_for_one(Tss,D,MoreExtra), append(MoreExtra,Extra,FinalExtra), Def = [T2|D].

other_occurences(_,[],[],[]).
other_occurences(func(F,_),[T|Ts],[Args|Rest],Others) :-
					not(var(T)), T = func(F, Args) -> other_occurences(func(F,_),Ts,Rest,Others).
other_occurences(tnam(Name,_),[T|Ts],[Args|Rest],Others) :-
					not(var(T)), T = tnam(Name, Args) -> other_occurences(tnam(Name,_),Ts,Rest,Others).
other_occurences(F,[T|Ts],Rest,[T|Others]) :- other_occurences(F,Ts,Rest,Others).

sum_pointwise([],[],[]).
sum_pointwise(Args,Types,[]) :- length(Args,1), Args = [X], no_list_in_args(X), !, Args = [Types].
sum_pointwise(Args,Types,Extra) :-
					length(Args,1), Args = [X], lists_in_args(X,Defs),
					length(Defs,N),
					gen_fresh_type(N,TempTypes),
					replace_all(Defs,TempTypes,X,Types),
					gen_compose_type_definitions(TempTypes,Defs,Extra).
sum_pointwise(Args,Types,Extra) :-
					transpose(Args,Defs),
					length(Defs,N),
					gen_fresh_type(N,Types),
					gen_compose_type_definitions(Types,Defs,Extra).

no_list_in_args([]).
no_list_in_args([H|T]) :- not(is_list(H)), no_list_in_args(T).

lists_in_args([],[]).
lists_in_args([H|T],[H|Ts]) :- is_list(H), !, lists_in_args(T,Ts).
lists_in_args([_|T],Ts) :- lists_in_args(T,Ts).

replace_all([],[],Final,Final).
replace_all([A|As],[B|Bs],[C|Cs],[D|Ds]) :- (
					A == C -> D = B, replace_all(As,Bs,Cs,Ds);
					true -> D = C, replace_all([A|As],[B|Bs],Cs,Ds)). 

gen_compose_type_definitions([],[],[]).
gen_compose_type_definitions([T|Ts],[Def|Defs],[def(T,Def)|Others]) :- gen_compose_type_definitions(Ts,Defs,Others).

if_singleton([],[]).
if_singleton([def(Type,Def)|Defs],Final) :-
					var(Type), length(Def,0), !,
					if_singleton(Defs,Final).
if_singleton([def(Type,Def)|Defs],Final) :-
					var(Type), length(Def,1),
					Def = [X], occur_check(Type,X), !,
					Type = X,
					if_singleton(Defs,Final).
if_singleton([Def|Defs],[Def|Final]) :-
					if_singleton(Defs,Final).

%%%%%% CLEAN OUTPUT %%%%%%

clean_output(List,Final) :-
					get_main_types(List,Main),
					all_important(Main,List,[],Temp),
					remove_duplicates_from_list(Temp,Final).

get_main_types([],[]).
get_main_types([def(Type,Def)|Rest],[def(Type,Def)|Others]) :- not(var(Type)), !, get_main_types(Rest,Others).
get_main_types([_|Rest],Others) :- get_main_types(Rest,Others).


all_important([],Types,Final,FinalDefs) :- get_defs(Final,Types,FinalDefs).
all_important([def(Type,Def)|Rest],Types,Acc,FinalDefs) :-
					new_types_on(Def,Types,New),
					not_on_done(New,Acc,Temp),
					get_defs(Temp,Types,TempDefs),
					append(Rest,TempDefs,NewRest),
					all_important(NewRest,Types,[Type|Acc],FinalDefs).


new_types_on([],_,[]).
new_types_on([T|Ts],TypeDefs,Final) :- (
					var(T), is_in_type_defs(T,TypeDefs), List = [T];
					var(T) -> List = [];
					T = basetype(_) -> List = [];
					T = tvar(_, _, _) -> List = [T];
					T = tnam(_, Args) -> new_types_on(Args,TypeDefs,List);
					T = func(_, Args) -> new_types_on(Args,TypeDefs,List) ),
					new_types_on(Ts,TypeDefs,List1), append(List,List1,Final).


not_on_done([],_,[]).
not_on_done([T|Ts],Done,Bs) :-
					(is_in(T,Done) -> not_on_done(Ts,Done,Bs);
					recorded(type_equivs,[T,God],_), is_in(God,Done) -> not_on_done(Ts,Done,Bs);
					true -> not_on_done(Ts,[T|Done],Cs), Bs = [T|Cs]).

get_defs([],_,[]).
get_defs([T|Ts],Types,[def(T,Def)|Defs]) :- get_from_definitions(T,Types,Def), get_defs(Ts,Types,Defs).