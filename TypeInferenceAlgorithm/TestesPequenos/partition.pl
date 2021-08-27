%:- closure_flag(on).
%:- list_flag(on).
%:- basetype_flag(off).

% partition([],A,[],[]).
% partition([H|T],A,[H|L],R) :- H < A, partition(T,A,L,R).
% partition([H|T],A,L,[H|R]) :- H >= A, partition(T,A,L,R).

partition(A, B, C, D) :- A=[], B=E, C=[], D=[] ; F<G, partition(H, G, I, J), A=[F|H], B=G, C=[F|I], D=J ; K>=L, partition(M, L, N, O), A=[K|M], B=L, C=N, D=[K|O].

% INTER | UNIF + NOCLO
%
% partition :: partition1/4 x partition2/4 x partition3/4 x partition4/4
%
% partition1/4 = [] + [ num() | self ]
% partition2/4 = _70 + num()
% partition3/4 = [] + [ num() | self ]
% partition4/4 = [] + [ num() | self ]
%
% INTER | UNIF + CLO | NEWCLO| NEWBETCLO
%
% partition :: partition1/4 x partition2/4 x partition3/4 x partition4/4
%
% partition1/4 = [] + [ num() | self ]
% partition2/4 = num()
% partition3/4 = [] + [ num() | self ]
% partition4/4 = [] + [ num() | self ]
%
% DATA + INTER + CLO | NEWCLO | NEWBETCLO
%
% partition :: partition1/4 x partition2/4 x partition3/4 x partition4/4
%
% partition1/4 = list(self)
% partition2/4 = num()
% partition3/4 = list(self)
% partition4/4 = list(self)
%
% DATA + UNIF + CLO | NEWCLO | NEWBETCLO
%
% partition :: partition1/4 x partition2/4 x partition3/4 x partition4/4
%
% partition1/4 = list(partition2/4)
% partition2/4 = num()
% partition3/4 = list(partition2/4)
% partition4/4 = list(partition2/4)