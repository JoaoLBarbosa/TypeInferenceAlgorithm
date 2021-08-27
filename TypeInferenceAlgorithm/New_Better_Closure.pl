%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 										  %
%			CLOSURE OPERATION			  %
%										  %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

closure(OpenTypes,ClosedTypes) :-
					(delete_lonely_vars(OpenTypes,OpenTypes,TempTypes); writeln('Deleting lonely vars wasn\'t a good idea: '), writeln(OpenTypes), fail),
					(simplify_type_definitions(TempTypes,SimplerTypeDefs); writeln('Simplification after deleting lonely vars failed: '), writeln(TempTypes), fail),
					replace_by_self(SimplerTypeDefs,NewOpenTypes),
					open_types(NewOpenTypes,OpenTypeDefs,Vars),
					calculate_proper_domains(OpenTypeDefs,NewOpenTypes,ProperDomains),
					calculate_proper_var_domains(Vars,OpenTypeDefs,ProperDomains,ProperVarDomains),
					(close_types(Vars,ProperVarDomains,NewTypeDefs); writeln('Replacing vars with their proper domains failed: '), writeln(Vars), writeln(ProperVarDomains), writeln(OpenTypeDefs), fail),
					append(NewTypeDefs,NewOpenTypes,UnTypeDefs),
					flatten_defs(UnTypeDefs,NewTempTypes),
					(pre_simplification(NewTempTypes,PreClosedTypes); writeln('PreSimplification failed:' ), writeln(NewTempTypes), fail),
					(simplify_type_definitions(PreClosedTypes,ClosedTypes); writeln('Simplification after closure failed: '), writeln(TempTypes), fail).

all_vars([]).
all_vars([X|Xs]) :- var(X), all_vars(Xs).

delete_lonely_vars([],_,[]).
delete_lonely_vars([def(T,Def)|Defs],NewOpenTypes,[def(T,NewDef)|NewDefs]) :-
					all_vars(Def), remove_from_list(def(T,Def),NewOpenTypes,OpenTypes),
					delete_vars_in_one(Def,OpenTypes,NewDef), length(NewDef,N), N > 0, !,
					delete_lonely_vars(Defs,NewOpenTypes,NewDefs).
delete_lonely_vars([Def|Defs],NewOpenTypes,[Def|NewDefs]) :-
					delete_lonely_vars(Defs,NewOpenTypes,NewDefs).

delete_vars_in_one([],_,[]).
delete_vars_in_one([V|Vs],OpenTypes,Final) :- var(V), occurs_nowhere(V,OpenTypes), !, delete_vars_in_one(Vs,OpenTypes,Final).
delete_vars_in_one([V|Vs],OpenTypes,[V|Final]) :- delete_vars_in_one(Vs,OpenTypes,Final).

occurs_nowhere(_,[]).
occurs_nowhere(V,[def(_,Def)|Defs]) :- occur_check_def(V,Def), occurs_nowhere(V,Defs).

occur_check_def(_,[]).
occur_check_def(V,[T|Ts]) :- occur_check(V,T), occur_check_def(V,Ts).

open_types([],[],[]).
open_types([def(T,Def)|Defs],[def(T,Def)|Others],FinalVars) :-
					is_open(Def,Vars), Vars \= [], !,
					open_types(Defs,Others,OtherVars),
					append(Vars,OtherVars,FinalVars).
open_types([_|Defs],Others,Vars) :- open_types(Defs,Others,Vars).

is_open([],[]).
is_open([T|Ts],[T|Rest]) :- var(T), !, is_open(Ts,Rest).
is_open([_|Ts],Rest) :- is_open(Ts,Rest).

calculate_proper_domains([],_,[]).
calculate_proper_domains([Type|Types],OpenTypes,[Domain|Domains]) :-
					calculate_proper_domain(Type,OpenTypes,Domain),
					calculate_proper_domains(Types,OpenTypes,Domains).

calculate_proper_domain(def(_,Def),OpenTypes,Domain) :-
					get_constructor_terms(Def,ConstructorTerms),
					gather_type_terms_for_domain(ConstructorTerms,OpenTypes,OpenTypes,Domain).

get_constructor_terms([],[]).
get_constructor_terms([T|Ts],[T|Cs]) :-
					not(var(T)), (T = func(_,_) ; T = tnam(_,_)), get_constructor_terms(Ts,Cs).
get_constructor_terms([_|Ts],Cs) :- get_constructor_terms(Ts,Cs).


gather_type_terms_for_domain(_,[],_,[]).
gather_type_terms_for_domain(Cs,[def(_,Def)|Defs],OpenTypes,Domain) :-
					constructor_term_in_def(Cs,OpenTypes,Def), !,
					non_var_type_terms(Def,TempDom),
					gather_type_terms_for_domain(Cs,Defs,OpenTypes,TempRest),
					append_without_repeating(TempDom,TempRest,Domain).
gather_type_terms_for_domain(Cs,[_|Defs],OpenTypes,Domain) :-
					gather_type_terms_for_domain(Cs,Defs,OpenTypes,Domain).

constructor_term_in_def([CT|_],OpenTypes,Def) :- (is_in(CT,Def);unifiable_verification(CT,OpenTypes,Def)), !.
constructor_term_in_def([_|CTs],OpenTypes,Def) :- constructor_term_in_def(CTs,OpenTypes,Def).

unifiable_verification(CT,OpenTypes,[X|_]) :-
					not(var(X)), X =.. [FuncOrName, F, Args1], CT =.. [FuncOrName, F, Args2],
					unifiable_args(Args1,Args2,OpenTypes).
unifiable_verification(CT,OpenTypes,[_|Xs]) :- unifiable_verification(CT,OpenTypes,Xs).

unifiable_args(A,B,_) :- A == B, !.
unifiable_args([A|As],[B|Bs],OpenTypes) :- can_unify(A,B,OpenTypes), unifiable_args(As,Bs,OpenTypes).

can_unify(A,B,_) :- A == B, !.
can_unify(A,B,OpenTypes) :- var(A), is_in_type_defs(A,OpenTypes), var(B), is_in_type_defs(B,OpenTypes),
					get_from_defs([A,B],OpenTypes,[Def1,Def2]), unifiable_defs(Def1,Def2,OpenTypes).
can_unify(A,B,OpenTypes) :- var(A), not(is_in_type_defs(A,OpenTypes)), B == self.
can_unify(A,B,OpenTypes) :- var(B), not(is_in_type_defs(B,OpenTypes)), A == self.
can_unify(A,B,OpenTypes) :- not(var(A)), not(var(B)), A =.. [FuncOrName, F, Args1], B =.. [FuncOrName, F, Args2],
					unifiable_args(Args1,Args2,OpenTypes).

unifiable_defs(Def1,Def2,OpenTypes) :- sort(Def1,DefA), sort(Def2,DefB), unifiable_args(DefA,DefB,OpenTypes).

non_var_type_terms([],[]).
non_var_type_terms([T|Ts],[T|Tss]) :- not(var(T)), !, non_var_type_terms(Ts,Tss).
non_var_type_terms([_|Ts],Tss) :- non_var_type_terms(Ts,Tss).


calculate_proper_var_domains([],_,_,[]).
calculate_proper_var_domains([V|Vs],OpenTypeDefs,ProperDomains,[Dom|Doms]) :-
					calculate_proper_var_domain(V,OpenTypeDefs,ProperDomains,[],Dom),
					calculate_proper_var_domains(Vs,OpenTypeDefs,ProperDomains,Doms).

calculate_proper_var_domain(V,[],[],Dom,Final) :- remove_self_referencing_terms(V,Dom,Final).
calculate_proper_var_domain(V,[def(_,Def)|Defs],[Dom|Doms],Acc,Final) :- (
					is_in(V,Def) -> append_without_repeating(Dom,Acc,NewAcc);
					true -> NewAcc = Acc),
					calculate_proper_var_domain(V,Defs,Doms,NewAcc,Final).

remove_self_referencing_terms(_,[],[]).
remove_self_referencing_terms(V,[T|Ts],Tss) :- (
					V == T; T =.. [_, _, Args], is_in(V,Args)),
					!, remove_self_referencing_terms(V,Ts,Tss).
remove_self_referencing_terms(V,[T|Ts],[T|Tss]) :- remove_self_referencing_terms(V,Ts,Tss).


close_types([],[],[]).
close_types([V|Vs],[[]|Doms],New) :-
					V = self, close_types(Vs,Doms,New).
close_types([V|Vs],[Dom|Doms],New) :-
					length(Dom,1), Dom = [Term], V = Term, close_types(Vs,Doms,New).
close_types([V|Vs],[Dom|Doms],[Def|New]) :-
					gen_fresh_type(1,[Type]), V = Type, gen_type_definitions([Type],[Dom],[Def]), close_types(Vs,Doms,New).

flatten_defs([],[]).
flatten_defs([def(T,Def)|Defs],[def(T,NewDef)|Others]) :- flatten(Def,NewDef), flatten_defs(Defs,Others).

pre_simplification([],[]).
pre_simplification([def(T,Def)|Defs],[def(T,SimpleDef)|Others]) :-
					remove_self(Def,TempDef),
					TempDef \= [], !, TempDef = SimpleDef,
					pre_simplification(Defs,Others).
pre_simplification([Def|Defs],[Def|Others]) :- pre_simplification(Defs,Others).

remove_self([],[]).
remove_self([X|Xs],Ys) :- X == self, !, remove_self(Xs,Ys).
remove_self([X|Xs],[X|Ys]) :- remove_self(Xs,Ys).