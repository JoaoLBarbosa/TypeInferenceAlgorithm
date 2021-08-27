%:- closure_flag(on).
%:- list_flag(on).
%:- basetype_flag(off).

% arit(X) :- X > 1.
% arit(X) :- X < 0.5.

arit(A) :- B > 1, A=B ; C < 0.5, A=C.

% (DATA +) INTER | UNIF + NOCLO | CLO | NEWCLO | NEWBETCLO
%
% arit :: arit1/1
%
% arit1/1 = num()