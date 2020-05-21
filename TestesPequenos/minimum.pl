%:- closure_flag(on).
%:- list_flag(on).
%:- type(tnam(tree,[X]),[func(void,[]),func(tree,[X,tnam(tree,[X]),tnam(tree,[X])])]).

minimum(L,M):-L=tree(N,void,O),M=N;(minimum(P,Q),P=R,Q=S),L=tree(T,R,U),M=S.

p(V,W):-(minimum(X,Y),X=tree(a,Z,Z),Y=BA),V=Z,W=BA.

