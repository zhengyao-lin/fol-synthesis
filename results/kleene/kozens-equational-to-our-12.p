fof(axiom_0, axiom, ! [C, B, A] : union(A, union(B, C)) = union(union(A, B), C)).
fof(axiom_1, axiom, ! [B, A] : union(A, B) = union(B, A)).
fof(axiom_2, axiom, ! [A] : union(A, zero) = A).
fof(axiom_3, axiom, ! [A] : union(A, A) = A).
fof(axiom_4, axiom, ! [C, B, A] : concat(A, concat(B, C)) = concat(concat(A, B), C)).
fof(axiom_5, axiom, ! [A] : concat(one, A) = A).
fof(axiom_6, axiom, ! [A] : concat(A, one) = A).
fof(axiom_7, axiom, ! [C, B, A] : concat(A, union(B, C)) = union(concat(A, B), concat(A, C))).
fof(axiom_8, axiom, ! [C, B, A] : concat(union(A, B), C) = union(concat(A, C), concat(B, C))).
fof(axiom_9, axiom, ! [A] : concat(zero, A) = zero).
fof(axiom_10, axiom, ! [A] : concat(A, zero) = zero).
fof(axiom_11, axiom, ! [A] : union(union(one, concat(A, closure(A))), closure(A)) = closure(A)).
fof(axiom_12, axiom, ! [A] : union(union(one, concat(closure(A), A)), closure(A)) = closure(A)).

fof(goal, conjecture, ! [C, B, A] : concat(concat(A, C), B) = concat(A, concat(C, B))).
