%:- closure_flag(on).
%:- list_flag(on).

p(A):- A = a.
s :- p(B), B=b.
r(C) :- C=b.