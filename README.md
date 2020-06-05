# TypeInferenceAlgorithm
This folder consists of the files necessary to perform type inference on Prolog programs.

-- normalize.pl --

Performs normalization of programs. A program is normalized if there is only one clause defining each predicate and the body of the clause is the or of the bodies of each separate clause in the non-normalized program. The head contains only variables, which are the only variables that can be shared by different or-bodies.

Example:

add(zero,X,X).
add(s(X),Y,s(Z)) :- add(X,Y,Z).

add(X1,X2,X3) :- (X1 = zero, X2 = X, X3 = X ; X1 = s(X'), X2 = Y, X3 = s(Z), X4 = X', X5 = Y, X6 = Z, add(X4,X5,X6)).

To run normalize:
1) term_expander((clause),_). where clause is the clause to normalize.
2) repeat for all clauses.
3) term_expander(end_of_file,_).
4) findall(X, clause(X), List).
5) List is the list of all normalized clauses.


-- inference.pl --

Performs type inference. It can be separated in several steps: 1) term_expansion - transforms the normalized programs in a easier construct to use on the algorithms; 2) constraint_generation - generates constraints from the program; 3) constraint_solve - solves the generated constraints; 4) closure - may occur or not depending on the flag in the input program; 5) print_solution - pretty prints the solved constraints that represent the interesting types for each predicate.

To run inference:
1) typed_compile(file). where file is the file that contains the Prolog program to infer types for.
2) see printed output.
