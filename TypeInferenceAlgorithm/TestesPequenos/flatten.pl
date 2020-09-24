%:- closure_flag(on).
%:- list_flag(on).


flatten(X1,X2) :- X1 = [], X2 = [] ; X1 = [L|Ls], X2 = FlatL, Y1 = L, Y2 = NewL, Z1 = Ls, Z2 = NewLs, W1 = NewL, W2 = NewLs, W3 = FlatL, flatten(Y1,Y2), flatten(Z1,Z2), app(W1,W2,W3); X1 = LL, X2 = [LL].

%flatten(X1,X2) :- X1 = [], X2 = []; X1 = X, X2 = [X], constant(X); X1 = [Y|Ys], X2 = Lista, flatten(Y,NY), flatten(Ys,NYs), app(NY,NYs,Lista).

app(A,B,C):-A=[],B=D,C=D;(app(E,F,G),E=H,F=I,G=J),A=[K|H],B=I,C=[K|J].

constant(X) :- X = 1; X=a.