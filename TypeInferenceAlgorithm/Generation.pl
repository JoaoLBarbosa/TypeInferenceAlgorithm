%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%																												%
%										2 - GERACAO DE CONSTRAINTS 												%
%																												%
% X -> Part of program as input to be typed 																	%
% Data -> List of type definitions given as input 																%
% Type -> Output type of X 																						%
%		Grammar of Type: TypeVar | basetype(B) | func(F,[Args]) | tvar(Pred,Pos,Arity) | tnam(Name,[Args])		%
%																												%
% Env -> List of assumptions for type variables of the form (v1,t1), where v1 = tvar(N) and tau is a type name  %
% Eq -> List of equality constraints of the form eq(t1,t2), where t1 and t2 are types (but never type names)    %
% Ineq -> List of subtyping constraints of the form ineq(t1,t2), where t1 and t2 are types 						%
% TypeDef -> List of type definitions.  																		%
%		Grammar of TypeDef: def(TypeName,[Type]) 																%
%		Grammar of TypeName: TypeVar | tvar(Pred,Pos,Arity) 													%
%																												%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint_gen(X,Type,Env,Eq,Ineq,TypeDef) :- (
					X = myvar(Y) -> gen_fresh_var(1,[Var]),
									gen_fresh_type(1,[TypeName]),
									Env = [(myvar(Y),TypeName)],
									Type = Var,
									Eq = [], Ineq = [], TypeDef = [def(TypeName,[Var])];

					X = func(C,[]) -> basetype(C,Type), Env = [], Eq = [], Ineq = [], TypeDef = [];

					X = func(Op,Args), (Op = '+'; Op = '-'; Op = '*'; Op = '/'; Op = '**') ->
										constraint_gen_args(Args,Types,Envs,Eqs,Ineqs,TypeDefs),
										cup(TypeDefs,TypeDef),
										cross_prod(Envs,TypeDef,Env),
										cup(Eqs,Eq),
										gen_arith(Types,Arith),
										cup([Arith|Ineqs],Ineq),
										Type = basetype(int);

					X = func(F,Args) -> constraint_gen_args(Args,Types,Envs,Eqs,Ineqs,TypeDefs),
										cup(TypeDefs,TypeDef),
										cross_prod(Envs,TypeDef,Env),
										basetypefunc(F,Types,Type,ExtraIneq),
										cup(Eqs,Eq),
										cup([ExtraIneq|Ineqs],Ineq);

					X = equals(T1,T2) -> constraint_gen(T1,Type1,Env1,Eq1,Ineq1,TypeDef1),
										constraint_gen(T2,Type2,Env2,Eq2,Ineq2,TypeDef2),
										Type = bool,
										cup([TypeDef1,TypeDef2],TypeDef),
										cross_prod([Env1,Env2],TypeDef,Env),
										cup([[eq(Type1,Type2)],Eq1,Eq2],Eq),
										cup([Ineq1,Ineq2],Ineq) ;

					X = pred(Op,Args), (Op = '<'; Op = '>'; Op = is; Op = '=<'; Op = '>=') ->
										constraint_gen_args(Args,Types,Envs,Eqs,Ineqs,TypeDefs),
										cup(TypeDefs,TypeDef),
										cross_prod(Envs,TypeDef,Env),
										gen_arith(Types,AritCons),
										cup(Eqs,Eq),
										cup([AritCons|Ineqs],Ineq),
										Type = bool ;

					X = pred(P,Args) -> clause(cl(pred(P,Args1),Body)),
										constraint_gen(cl(pred(P,Args1),Body),bool,EnvPrime,Eqs,Ineqs,TypeDefs),
										constraint_solve(Eqs,Ineqs,TypeDefs,TypeDef1),
										get_from_env(Args1,EnvPrime,TypesPrime),
										rename_types(TypesPrime,TypeDef1,NewTypesPrime,NewTypeDef),
										length(Args,N), gen_fresh_var(N,Vars), gen_fresh_type(N,Types),
										gen_type_definitions(Types,Vars,TypeDef2),
										gen_subt_cons(Types,NewTypesPrime,Ineq),
										Type = bool, Eq = [],
										cup([NewTypeDef,TypeDef2],TypeDef),
										on_each(Args,Types,Env);

					X = rec(pred(P,Args)) -> length(Args,N), gen_fresh_var(N,Vars),
										gen_fresh_type(N,Types),
										on_each(Args,Types,Env), Eq = [], Type = bool,
										gen_type_definitions(Types,Vars,TypeDef),
										gen_predicate_tvar(P,1,N,PredTypes),
										gen_subt_cons(Types,PredTypes,Ineq);

					X = and(Calls) -> constraint_gen_all(Calls,Envs,Eqs,Ineqs,TypeDefs),
										cup(TypeDefs,TypeDef),
										cross_prod(Envs,TypeDef,Env),
										cup(Eqs, Eq),
										cup(Ineqs,Ineq),
										Type = bool ;

					X = or(Bodies) -> constraint_gen_all(Bodies,Envs,Eqs,Ineqs,TypeDefs),
										cup(TypeDefs,TempTypeDef),
										cross_sum(Envs,TempTypeDef,Env,NTypeDefs),
										append(TempTypeDef,NTypeDefs,TypeDef),
										cup(Eqs, Eq),
										cup(Ineqs,Ineq),
										Type = bool ;

					X = cl(Head,Body) -> Head = pred(P , Args), length(Args,N),
										mark_recursive(P,N,Body,NBody),
										constraint_gen(NBody,bool,Env,Eq,Ineq,TypeDef),
										get_from_env(Args,Env,Types),
										gen_predicate_tvar(P,1,N,PredTypes),
										(N = 0 -> true;
										true -> Types = PredTypes), Type = bool
					).



% Generates "fresh" type variables

gen_fresh_var(0,[]).
gen_fresh_var(1,[_]).
gen_fresh_var(N,[_|OtherVars]) :- M is N - 1, gen_fresh_var(M,OtherVars).


% Generates "fresh" type names

gen_fresh_type(0,[]).
gen_fresh_type(N,[_|Others]) :-
					M is N - 1,
					gen_fresh_type(M,Others).


% Verifies what is the basetype of a constant or function symbol

basetype(C,Type) :- get_from_data(C,Type,[]);
					basetype_flag(on) -> basetype_of(C,Type);
					Type = basetype(C).

basetypefunc(F,Types,Type,Ineq) :- (
					get_from_data(F,Type,Vars) , gen_subt_cons(Types,Vars,Ineq);
					Type = func(F, Types), Ineq = [] ).

get_from_data(F,Name,Vars) :- findall(X,recorded(data, [X], _), Data), get_from_data(F,Data,Name,Vars).

get_from_data(F,[(Name,List)|_],Name,Vars) :- is_present(F,List,Vars), !.
get_from_data(F,[_|Data],Name,Vars) :- get_from_data(F,Data,Name,Vars).

is_present(F,[Y|_],Vars) :- Y = func(F, Vars), !.
is_present(F,[Y|Ys],Vars) :- Y = func(G, _), G \= F, is_present(F,Ys,Vars).

basetype_of(C,Type) :- C = [], Type = basetype([]).
basetype_of(C,Type) :- integer(C), Type = basetype(int).
basetype_of(C,Type) :- float(C), Type = basetype(float).
basetype_of(C,Type) :- string(C), Type = basetype(string).
basetype_of(C,Type) :- atom(C), Type = basetype(atom).


% Applies constraint_gen to the arguments of a function symbol

constraint_gen_args([],[],[],[],[],[]).
constraint_gen_args([Arg|Args],[Type|Types],[Env|Envs],[Eq|Eqs],[Ineq|Ineqs],[TypeDef|TypeDefs]) :-
					constraint_gen(Arg,Type,Env,Eq,Ineq,TypeDef),
					constraint_gen_args(Args,Types,Envs,Eqs,Ineqs,TypeDefs).


% Applies constaint_gen to each argument of the list, with slightly different Datas (renaming of vars)

constraint_gen_all([],[],[],[],[]).
constraint_gen_all([Arg|Args], [Env|Envs], [Eq|Eqs], [Ineq|Ineqs], [TypeDef|TypeDefs]) :-
					constraint_gen(Arg,_,Env,Eq,Ineq,TypeDef),
					constraint_gen_all(Args,Envs,Eqs,Ineqs,TypeDefs).


% Calculates the cross product of the Environments

cross_prod(Envs,TypeDefs,Env) :- cup(Envs,TempEnv), deal_with_repeated(TempEnv,TypeDefs,Env).

deal_with_repeated([],_,[]).
deal_with_repeated([(Var,Type)|Rest],TypeDefs,[(Var,Type)|RestPrime]) :-
					occurences(Var,Rest,[],List,NewRest), (
					List = [] -> true;
					List \= [] -> get_from_defs(List,TypeDefs,Defs),
										get_from_definitions(Type,TypeDefs,Def),
										all_eq([Def|Defs]) ),
					deal_with_repeated(NewRest,TypeDefs,RestPrime).

occurences(_,[],Final,Final,[]).
occurences(Var,[(Var,Type)|Rest],Acc,List,Rest1) :- !,
					occurences(Var,Rest,[Type|Acc],List,Rest1).
occurences(Var,[(OtherVar,Type)|Rest],Acc,List,[(OtherVar,Type)|Rest1]) :-
					Var \= OtherVar, !, occurences(Var,Rest,Acc,List,Rest1).

get_from_defs([],_,[]).
get_from_defs([A|As],TypeDefs,[B|Bs]) :- get_from_definitions(A,TypeDefs,B), get_from_defs(As,TypeDefs,Bs).

get_from_definitions(A,[def(B,C)|_],C) :- A == B, !.
get_from_definitions(A,[_|Rest],C) :- get_from_definitions(A,Rest,C).

all_eq([_]).
all_eq([A,B|Rest]) :- A = B, all_eq([A|Rest]).


% Calculates the cross sum of the environments and type definitions

cross_sum(Envs,TypeDefs,Env,TypeDef) :- cup(Envs,TempEnv), sum_repeated(TempEnv,TypeDefs,Env,TypeDef).

sum_repeated([],_,[],[]).
sum_repeated([(Var,Type)|Rest],TypeDefs,[(Var,NType)|RestPrime],TypeDef) :-
					occurences(Var,Rest,[],List,NewRest), (
					List = [] -> TempDef = [], NType = Type;
					List \= [] -> get_from_defs(List,TypeDefs,Defs),
										get_from_definitions(Type,TypeDefs,Def),
										gen_fresh_type(1,[NType]),
										cup([Def|Defs],FDef),
										TempDef = [def(NType,FDef)] ),
					sum_repeated(NewRest,TypeDefs,RestPrime,OtherDef), append(TempDef,OtherDef,TypeDef).



% Cup generates the union of sets from a list of sets

cup(A,B) :- cup(A,[],B).

cup([],Final,Final).
cup([A|As],Acc,Final) :- append(A,Acc,NewAcc), cup(As,NewAcc,Final).


% Generates arithmetic constraints

gen_arith([],[]).
gen_arith([A|As],[ineq(A,tnam(num,[]))|Bs]) :- gen_arith(As,Bs).


% Getting the types associated to variables from the environment

get_from_env([],_,[]).
get_from_env([Var|Vars],Env,[Type|Types]) :- get_from_environment(Var,Env,Type), get_from_env(Vars,Env,Types).

get_from_environment(Var,[(V2,Type)|_],Type) :- Var == V2, !.
get_from_environment(Var,[_|Rest],Type) :- get_from_environment(Var,Rest,Type).

% Generating constraints, type definitions, environments, and predicate types

gen_eq_constraints(_,[],[]).
gen_eq_constraints([A],[[B]|Bs],[eq(A,B)|Eqs]) :- gen_eq_constraints([A],Bs,Eqs).


gen_eq_cons([],[],[]).
gen_eq_cons([A|As],[B|Bs],[eq(A,B)|Eqs]) :- gen_eq_cons(As,Bs,Eqs).


gen_subt_cons([],[],[]).
gen_subt_cons([A|As],[B|Bs],[ineq(A,B)|Eqs]) :- gen_subt_cons(As,Bs,Eqs).


gen_type_definitions([],[],[]).
gen_type_definitions([T|Ts],[V|Vs],[def(T,[V])|Defs]) :- gen_type_definitions(Ts,Vs,Defs).


on_each([],[],[]).
on_each([V|Vs],[T|Ts],[(V,T)|Env]) :- on_each(Vs,Ts,Env).


gen_predicate_tvar(P,_,0,[tvar(P,0,0)]).
gen_predicate_tvar(P,N,N,[tvar(P,N,N)]).
gen_predicate_tvar(P,M,N,[tvar(P,M,N)|Types]) :- M < N, Q is M + 1, gen_predicate_tvar(P,Q,N,Types).

gen_env_piece([],[],[]).
gen_env_piece([V|Vs],[T|Ts],[(V,T)|VTs]) :- gen_env_piece(Vs,Ts,VTs).

rename_types([],L,[],L).
rename_types([T|Ts],Defs,[NT|NTs],NDefs) :-
					gen_fresh_type(1,[NT]),
					replace_in_defs(T,NT,Defs,TempDefs),
					rename_types(Ts,TempDefs,NTs,NDefs).

replace_in_defs(_,_,[],[]).
replace_in_defs(T,NT,[def(T1,Def)|Rest],[def(T2,NDef)|Others]) :- (
					T1 == T -> T2 = NT;
					true -> T2 = T1), 
					replace_in_def_body(T,NT,Def,NDef),
					replace_in_defs(T,NT,Rest,Others).

replace_in_def_body(_,_,[],[]).
replace_in_def_body(T,NT,[A|As],[B|Bs]) :-(
					var(A) -> B = A;
					A == T -> B = NT;
					A =.. [FuncOrName, F, Args] -> replace_in_def_body(T,NT,Args,NArgs), B =.. [FuncOrName, F, NArgs];
					true -> B = A),
					replace_in_def_body(T, NT, As, Bs).


%% To create new instances of Data for each call

replace_in_a_rule([],[],L,L).
replace_in_a_rule([A|As],[B|Bs],Rule,NRule) :-
					replace_one_in_a_rule(A,B,Rule,Temp),
					replace_in_a_rule(As,Bs,Temp,NRule).

replace_one_in_a_rule(_,_,[],[]).
replace_one_in_a_rule(A,B,[F|Fs],[G|Gs]) :- (
					F == A -> G = B;	
					F = func(_, []) -> G = F;
					F = func(HHH, Args) -> replace_in_rule_args(A,B,Args,NArgs), G = func(HHH, NArgs);
					F = tnam(Name, Args) -> replace_in_rule_args(A,B,Args,NArgs), G = tnam(Name, NArgs);
					true -> G = F),
					replace_one_in_a_rule(A,B,Fs,Gs).
replace_in_rule_args(_,_,[],[]).
replace_in_rule_args(A,B,[F|Fs],[G|Gs]) :- (
					F == A -> G = B;	
					F = func(_, []) -> G = F;
					F = func(HHH, Args) -> replace_in_rule_args(A,B,Args,NArgs), G = func(HHH, NArgs);
					F = tnam(Name, Args) -> replace_in_rule_args(A,B,Args,NArgs), G = tnam(Name, NArgs);
					true -> G = F),
					replace_one_in_a_rule(A,B,Fs,Gs).


% Marks recursive predicate calls on the body of a clause

mark_recursive(P,N,Body,NBody) :-
					Body = or(Bodies), mark_recursive_all(P,N,Bodies,NBodies), NBody = or(NBodies);
					Body = and(Calls), mark_recursive_all(P,N,Calls,NCalls), NBody = and(NCalls);
					Body = equals(_, _), NBody = Body;
					Body = pred(Q , _), P \= Q, NBody = Body;
					Body = pred(P , Args), length(Args,N), NBody = rec(Body);
					Body = pred(P , _), NBody = Body.

mark_recursive_all(_,_,[],[]).
mark_recursive_all(P,N,[X|Xs],[Y|Ys]) :- mark_recursive(P,N,X,Y), mark_recursive_all(P,N,Xs,Ys).