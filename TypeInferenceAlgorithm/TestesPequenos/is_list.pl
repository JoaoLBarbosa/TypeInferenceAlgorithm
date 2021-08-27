%:- closure_flag(on).
%:- list_flag(on).
%:- basetype_flag(off).

% is_list([]).
% is_list([X | Xs]) :- is_list(Xs).

is_list(A) :- A = []; is_list(B), A = [X|B].