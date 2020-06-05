# TypeInferenceAlgorithm
This folder consists of the files necessary to perform type inference on Prolog programs.

-- normalize.pl --

Performs normalization of programs. A program is normalized if there is only one clause defining each predicate and the body of the clause is the or of the bodies of each separate clause in the non-normalized program. The head contains only variables, which are the only variables that can be shared by different or-bodies.

Example:

add(zero,X,X).
add(s(X),Y,s(Z)) :- add(X,Y,Z).

add(X1,X2,X3) :- (X1 = zero, X2 = X, X3 = X ; X1 = s(X'), X2 = Y, X3 = s(Z), X4 = X', X5 = Y, X6 = Z, add(X4,X5,X6)).


-- inference.pl --

Performs type inference. It can be separated in several steps: 1) term_expansion - transforms the normalized programs in a easier construct to use on the algorithms; 2) constraint_generation - generates constraints from the program; 3) constraint_solve - solves the generated constraints; 4) closure - may occur or not depending on the flag in the input program; 5) print_solution - pretty prints the solved constraints that represent the interesting types for each predicate.
