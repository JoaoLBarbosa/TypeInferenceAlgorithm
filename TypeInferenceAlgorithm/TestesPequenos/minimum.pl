%:- closure_flag(on).
%:- list_flag(on).
%:- type(tnam(tree,[tvar(-3)]),[func(void,[]),func(tree,[tvar(-3),tnam(tree,[tvar(-3)]),tnam(tree,[tvar(-3)])])]).

minimum(L,M):-L=tree(N,void,O),M=N;(minimum(P,Q),P=R,Q=S),L=tree(T,R,U),M=S.

p(V,W):-(minimum(X,Y),X=tree(a,Z,Z),Y=BA),V=Z,W=BA.

