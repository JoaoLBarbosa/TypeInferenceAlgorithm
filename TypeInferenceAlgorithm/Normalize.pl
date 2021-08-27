term_expander(end_of_file,end_of_file) :-
	findall(X,clause(X),List),
	retractall(clause(_)),
	join_same_pred(List).

term_expander((H :- T), O) :-
    normalize_body(T,NT),
    normalize_head(H,FH,C),!,
    with_comma([NT|C],FT), O = (FH :- FT),
    assert(clause(O)).

term_expander((H),O) :-
	normalize_head(H,NH,C),
	with_comma(C,Body), O = (NH :- Body),
	assert(clause(O)).

normalize_head(H,FH,C) :-
	H =.. [Pred | Args],
	newvarshead(NArgs,Args,C),
	FH =.. [Pred | NArgs].

newvarshead([],[],[]).
newvarshead([X|Xs],[A|As],[(X = A)|Cs]) :-
	newvarshead(Xs,As,Cs).

newvars([],[],[]).
newvars([X|Xs],[A|As],Cs) :-
	var(A), !, X = A, newvars(Xs,As,Cs).
newvars([X|Xs],[A|As],[(X = A)|Cs]) :-
	newvars(Xs,As,Cs).

normalize_body((A,B),Final) :-
	normalize_body(A,FA),
	normalize_body(B,FB),
	Final = (FA,FB).

normalize_body(A,Final) :-
	A =.. [Pred | _], (
	Pred = '<' ;
	Pred = '>' ;
	Pred = '<=';
	Pred = '>=';
	Pred = is ;
	Pred = '='
	) -> Final = A.

normalize_body(A,Final) :-
	A =.. [Pred | Args] -> newvars(NArgs,Args,C),
		NA =.. [Pred | NArgs],
		with_comma([NA|C],Final);
	true -> Final = A.

with_comma([A], A).
with_comma([A|As], X) :- with_comma(As,NAs), X = (A, NAs).

join_same_pred([]).
join_same_pred([(Pred :- Body)|Others]) :-
	Pred =.. [P | Vars],
	get_other_p(P,Others,VVars,Bodies,Rest),
	substitution_of_vars(Vars,VVars),
	with_semi_colon([Body|Bodies],Final),
	assert(clause((Pred :- Final))),
	join_same_pred(Rest).

get_other_p(_,[],[],[],[]).
get_other_p(P,[(Pred :- Body)|Continue],[Args|Vars],[Body|Bodies],Rest) :-
	Pred =.. [P | Args], !,  get_other_p(P,Continue, Vars,Bodies,Rest).
get_other_p(P,[(Pred :- Body)|Continue],Vars,Bodies,[(Pred :- Body)|Rest]) :-
	get_other_p(P,Continue,Vars,Bodies,Rest).

substitution_of_vars(_,[]).
substitution_of_vars(Vars,[NVars|Others]) :-
	Vars = NVars,
	substitution_of_vars(Vars,Others).

with_semi_colon([A],A).
with_semi_colon([A|As],X) :- with_semi_colon(As,NAs), X = (A ; NAs).