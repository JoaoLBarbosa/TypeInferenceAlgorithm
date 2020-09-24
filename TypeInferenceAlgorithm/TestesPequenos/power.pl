%:- closure_flag(on).
%:- list_flag(on).


power(A,B,C):- A=D,B=0,C=1;A=E,B=1,C=E;((F>G,F=H,G=1),(I is J,I=K,J=H-1),(power(L,M,N),L=O,M=K,N=P),Q is R,Q=S,R=P*O),A=O,B=H,C=S.

square(T,U):-(power(V,W,X),V=Y,W=2,X=Z),T=Y,U=Z.