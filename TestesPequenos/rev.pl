%:- closure_flag(on).
%:- list_flag(on).


rev(A,B):-A=[],B=[];((rev(C,D),C=E,D=F),app(G,H,I),G=F,H=[J],I=K),A=[J|E],B=K.

app(A,B,C):-A=[],B=D,C=D;(app(E,F,G),E=H,F=I,G=J),A=[K|H],B=I,C=[K|J].