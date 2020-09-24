%:- closure_flag(on).
%:- list_flag(on).


concat(X1,X2) :- X1 = [], X2 = []; X1 = [X|Xs], X2 = List, concat(Xs,NXs), app(X,NXs,List).


app(A,B,C):-A=[],B=D,C=D;(app(E,F,G),E=H,F=I,G=J),A=[K|H],B=I,C=[K|J].