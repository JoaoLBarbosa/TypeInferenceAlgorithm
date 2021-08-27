%%%%%%%%%%%%%%%%%%
%				 %
% Pretty Printer %
%				 %
%%%%%%%%%%%%%%%%%%

print_solution(Head,Env,FinalDef) :-
					Head = pred(P, Args),
					search_headvarstypes(Args,Env,Types),
					print_output(P,FinalDef,Types).

search_headvarstypes([],_,[]).
search_headvarstypes([V|Vs],Env,[T|Ts]) :- search_headvartype(V,Env,T), search_headvarstypes(Vs,Env,Ts).

search_headvartype(V,[(V1,T)|_],T) :- V == V1, !.
search_headvartype(V,[_|Rest],T) :- search_headvartype(V,Rest,T).

print_output(P,FinalDef,Types) :-
					write(P), write(' :: '), print_types(Types), nl, nl,
					print_defs(Types,FinalDef,[]), nl, nl.

print_types([]).
print_types([T|Ts]) :- 
					(var(T) -> write(T);
					T = tvar(P,A,N) -> write(P), write(A), write('/'), write(N)
					) , (
					Ts == [] -> print_types(Ts);
					Ts \= [] -> write(' x '), print_types(Ts) ).


print_defs([],_,_).
print_defs([T|Ts],FinalDef,Done) :-
					get_from_definitions(T,FinalDef,Def), print_types([T]), write(' = '), sort(Def,SortedDef), print_def(SortedDef,T), nl,
					new_types_on(Def,FinalDef,New), append(Ts,[T|Done],NDONE),
					not_on_done(New,NDONE,Temp), append(Ts,Temp,Final),
					print_defs(Final,FinalDef,[T|Done]).

print_def([],_) :- !, write(_).
print_def([A],T) :- !, print_type_term(A,T).
print_def([A|B],T) :- print_type_term(A,T), write(' + '), print_def(B,T).


print_type_term(T,Type) :- (
					T == Type -> write('self');
					var(T) -> write(T);
					T = basetype(Base) -> write(Base);
					T = tvar(P2, A2, N2) -> (integer(P2) -> write('$VAR'(P2));
										true -> write(P2), write(A2), write('/'), write(N2) );
					T = tnam(Name, Args) -> write(Name), write('('), print_args(Args,Type), write(')');
					T = func(_, _) -> print_f(T,Type) ).


print_f(func('.',[A,B]),T) :- write('[ '), print_type_term(A,T), write(' | '), print_type_term(B,T), write(' ]').
print_f(func('[|]',[A,B]),T) :- write('[ '), print_type_term(A,T), write(' | '), print_type_term(B,T), write(' ]').

print_f(func(C,[]),_) :- write(C), !.
print_f(func(F,Args),T) :- write(F), write('('), print_args(Args,T), write(')').

print_args([],_).
print_args([A],T) :- !, print_type_term(A,T).
print_args([A|As],T) :- print_type_term(A,T), write(', '), print_args(As,T).


print_data([]).
print_data([(Name,List)|Rest]) :- print_name_of_type(Name), print_def(List,_), nl, print_data(Rest), !.

print_name_of_type(tnam(Name,Args)) :- write(Name), write('('), print_args(Args,_), write(')'), write(' = ').