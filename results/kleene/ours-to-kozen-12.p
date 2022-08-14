fof(axiom_0, axiom, ! [B] : zero = concat(zero, B)).
fof(axiom_1, axiom, ! [B] : zero = concat(B, zero)).
fof(axiom_2, axiom, closure(zero) = one).
fof(axiom_3, axiom, ! [B] : union(closure(zero), closure(B)) = closure(union(one, B))).
fof(axiom_4, axiom, ! [B, A] : union(concat(zero, zero), union(A, B)) = union(union(B, A), A)).
fof(axiom_5, axiom, ! [B] : closure(closure(B)) = concat(closure(B), union(B, one))).
fof(axiom_6, axiom, ! [B] : union(closure(B), union(one, B)) = closure(B)).
fof(axiom_7, axiom, ! [A] : concat(union(A, A), closure(A)) = concat(closure(A), A)).
fof(axiom_8, axiom, ! [B, A] : concat(concat(one, A), union(one, B)) = union(concat(A, B), A)).
fof(axiom_9, axiom, ! [A] : union(A, A) = A).
fof(axiom_10, axiom, ! [B] : closure(union(B, B)) = concat(closure(B), closure(B))).
fof(axiom_11, axiom, ! [C, B, A] : union(B, union(C, A)) = union(union(C, A), union(A, B))).
fof(axiom_12, axiom, ! [C, B, A] : concat(concat(A, C), B) = concat(A, concat(C, B))).
fof(axiom_13, axiom, ! [C, B, A] : concat(union(A, A), union(B, C)) = union(concat(A, C), concat(A, B))).
fof(axiom_14, axiom, ! [C, B, A] : union(concat(C, B), concat(A, B)) = concat(union(C, A), B)).

fof(goal, conjecture, ! [A] : union(union(one, concat(closure(A), A)), closure(A)) = closure(A)).
