%:- closure_flag(on).
%:- list_flag(on).
%:- basetype_flag(on).
%:- type tree(X) = empty + node(X,tree(X),tree(X)).

% tree_minimum(empty,0).
% tree_minimum(node(N,L,R),Final) :- tree_minimum(L,A), tree_minimum(R,B), minimum([A,B,N],Final).
%
% minimum([A],A).
% minimum([A|As],N) :- minimum(As,N), A =< N.
% minimum([A|As],A) :- minimum(As,N), N =< A.

tree_minimum(A, B) :- A=empty, B=0 ; tree_minimum(C, D), tree_minimum(E, F), minimum(G, H), G=[D, F, I], A=node(I, C, E), B=H.

minimum(A, B) :- A=[C], B=C ; minimum(D, E), F=<E, A=[F|D], B=E ; minimum(G, H), H=<I, A=[I|G], B=I.

% INTER | UNIF + NOCLO
%
% tree_minimum :: tree_minimum1/2 x tree_minimum2/2
%
% tree_minimum1/2 = atom + node(tree_minimum2/2, self, self)
% tree_minimum2/2 = _534 + num()
%
%
% minimum :: minimum1/2 x minimum2/2
%
% minimum1/2 = [ minimum2/2 | _382 ]
% minimum2/2 = _46 + num()
% $VAR(_382) = [] + [ minimum2/2 | self ]
%
% INTER | UNIF + CLO | NEWCLO | NEWBETCLO
%
% tree_minimum :: tree_minimum1/2 x tree_minimum2/2
%
% tree_minimum1/2 = atom + node(num(), self, self)
% tree_minimum2/2 = num()
%
%
% minimum :: minimum1/2 x minimum2/2
%
% minimum1/2 = [ minimum2/2 | _87316 ]
% minimum2/2 = num()
% $VAR(_87316) = [] + [ minimum2/2 | self ]
%
% DATA + INTER | UNIF + CLO | NEWCLO | NEWBETCLO
%
% tree_minimum :: tree_minimum1/2 x tree_minimum2/2
%
% tree_minimum1/2 = tree(tree_minimum2/2)
% tree_minimum2/2 = num()
%
%
% minimum :: minimum1/2 x minimum2/2
%
% minimum1/2 = list(num())
% minimum2/2 = num()
%
% DATA + UNIF + CLO | NEWCLO | NEWBETCLO
%
% tree_minimum :: tree_minimum1/2 x tree_minimum2/2
%
% tree_minimum1/2 = tree(tree_minimum2/2)
% tree_minimum2/2 = num()
%
%
% minimum :: minimum1/2 x minimum2/2
%
% minimum1/2 = list(minimum2/2)
% minimum2/2 = num()