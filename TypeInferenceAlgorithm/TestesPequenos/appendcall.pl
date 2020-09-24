%:- closure_flag(on).
%:- list_flag(on).

p(L):-((app(M,N,O),M=[a],N=[b],O=P),app(Q,R,S),Q=[P],R=[P],S=T),L=T.

app(A,B,C):-A=[],B=D,C=D;(app(E,F,G),E=H,F=I,G=J),A=[K|H],B=I,C=[K|J].