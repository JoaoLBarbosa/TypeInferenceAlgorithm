%:- closure_flag(on).
%:- list_flag(on).


rev(A,B,C):-A=[],B=D,C=D;(rev(E,F,G),E=H,F=I,G=[J|K]),A=[J|H],B=I,C=K.

