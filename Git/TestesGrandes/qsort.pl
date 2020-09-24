%:- closure_flag(on).
%:- list_flag(on).


qsort(X1,X2) :- X1 = [X|L], X2 = R, Y1 = L, Y2 = X, Y3 = L1, Y4 = L2, Z1 = L2, Z2 = R2, W1 = L1, W2 = R1, T1 = R2, T2 = [X|R1], T3 = R, partition(Y1,Y2,Y3,Y4), qsort(Z1,Z2), qsort(W1,W2), append(T1,T2,T3); X1 = [], X2 = [].

partition(X1,X2,X3,X4) :- X1 = [], X2 = AAA, X3 = [], X4 = []; X1 = [E|R], X2 = C, X3 = [E|Left], X4 = Right, E < C, Y1 = R, Y2 = C, Y3 = Left, Y4 = Right, partition(Y1,Y2,Y3,Y4); X1 = [E1|R1], X2 = C1, X3 = Left1, X4 = [E1|Right1], E1 >= C1, Y11 = R1, Y22 = C1, Y33 = Left1, Y44 = Right1, partition(Y11,Y22,Y33,Y44).

append(X1,X2,X3) :- X1 = [], X2 = X, X3 = X; X1 = [H|T], X2 = Y, X3 = [H|Z], Y1 = T, Y2 = Y, Y3 = Z, append(Y1,Y2,Y3).