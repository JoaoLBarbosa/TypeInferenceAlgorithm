%:- closure_flag(on).
%:- list_flag(on).


power(A,B,C):-A=D,B=0,C=1;A=E,B=1,C=E;(F>1,G is F-1,(power(H,I,J),H=K,I=G,J=L),M is L*K),A=K,B=F,C=M.

square(T,U):-(power(V,W,X),V=Y,W=2,X=Z),T=Y,U=Z.