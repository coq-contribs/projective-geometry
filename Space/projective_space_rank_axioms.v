Require Export sets_of_points. 
Require Export matroids_axioms.

Module Type RankProjectiveSpace (DecPoints: FSetInterface.WS).

Module Export FiniteSetsDefs := BuildFSets DecPoints.

Definition set_of_points := t.
Definition Point := DecPoints.t.

(** General Axioms of Matroids *)

Parameter rk : set_of_points -> nat.

Axiom matroid1_a  : forall X, rk X >= 0.

Axiom matroid1_b : forall X, rk X <= cardinal X.

Axiom matroid2: forall X Y, Subset X Y -> rk X <= rk Y.

Axiom matroid3: forall X Y,
 rk(union X Y) + rk(inter X Y) <= rk X + rk Y. 

(** Axioms needed for projective geometry *)

Axiom rk_singleton_ge : forall P, rk (singleton P) >= 1.

Axiom rk_couple_ge : forall P Q, ~ P [==] Q -> rk(couple P Q) >= 2.

Axiom pasch : forall A B C D, rk (quadruple A B C D) <= 3 -> 
exists J, rk (triple A B J) = 2 /\ rk (triple C D J) = 2.

Axiom three_points_on_lines : forall A B, exists C, 
rk (triple A B C) = 2 /\ rk (couple B C) = 2 /\ rk (couple A C) = 2.

Parameter P0 P1 P2 P3 : Point.

Axiom lower_dim : rk (quadruple P0 P1 P2 P3) >= 4.

End RankProjectiveSpace.

