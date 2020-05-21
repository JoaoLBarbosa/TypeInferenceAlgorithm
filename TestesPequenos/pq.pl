%:- closure_flag(on).
%:- list_flag(on).
%:- type(tnam(struct,[tvar(-3)]),[func(a,[]),func(f,[tvar(-3)])]).

p(A):-(q(B),B=C),A=C.

q(D):-(r(E),E=F),D=F.
	
r(G):-G=a;(r(H),H=I),G=f(I).