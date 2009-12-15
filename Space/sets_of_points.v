Require Export FSets.

(** This module takes a decidable type and 
build finite sets of this type, tactics and defs *)

Module BuildFSets (DecPoints: FSetInterface.WS ).

Module Export FiniteSetsOfPoints := FSetWeakList.Make DecPoints.
Module Export FiniteSetsOfPointsProperties := WProperties FiniteSetsOfPoints.
Module Export Dec := WDecide FiniteSetsOfPoints.
Export Dec.F.

Lemma test_fsetdec : forall X x,
In x X ->
Equal (inter X (singleton x)) (singleton x).
Proof.
intros.
fsetdec. 
Qed.

Definition set_of_points := t.
Definition Point := DecPoints.t.

Definition couple(x y :Point) : set_of_points := 
add x (add y empty).

Definition triple(x y t :Point): set_of_points :=
add x (add y (add t empty)).

Definition quadruple(x y t u :Point): set_of_points :=
add x (add y (add t  (add u empty))).

Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).
Notation "s [==] t" := (DecPoints.eq s t) (at level 70, no associativity).

Lemma couple_singleton_eq : forall x y :Point, x [==] y -> 
Equal (couple x y) (singleton x).
Proof.
intros.
unfold couple.
subst.
fsetdec.
Qed.

Lemma test_fsetdec2 : forall X x,
In x X ->
inter X (singleton x)[=]singleton x.
Proof.
intros.
fsetdec.
Qed.

Lemma test : forall P A B C A' B' C',
union (singleton P) (union (triple A B C) (triple A' B' C'))[=]
union (triple P B B') (union (couple P A) (triple C A' C')).
Proof.
intros.
unfold triple, couple.

unfold Equal.
intro.
autorewrite with set_simpl in *.
fsetdec.
Qed.

Lemma test2 : forall A B C,
 (union (singleton C) (couple A B)) [=] (triple A B C).
Proof.
intros.
unfold triple, couple.
fsetdec.
Qed.
 
Lemma subset_exists : forall A B, Subset A B -> exists C, Equal (union A C) B.
Proof.
intros.
exists (diff B A).
fsetdec.
Qed.

Lemma triple_1 : forall a b c, Equal (triple a b c) (triple a c b).
Proof.
intros.
unfold triple;fsetdec.
Qed.

Lemma triple_2 : forall a b c, Equal (triple a b c) (triple b a c).
Proof.
intros.
unfold triple;fsetdec.
Qed.

Lemma triple_3 : forall a b c, Equal (triple a b c) (triple b c a).
Proof.
intros.
unfold triple;fsetdec.
Qed.

Lemma triple_4 : forall a b c, Equal (triple a b c) (triple c a b).
Proof.
intros.
unfold triple;fsetdec.
Qed.

Lemma triple_5 : forall a b c, Equal (triple a b c) (triple c b a).
Proof.
intros.
unfold triple;fsetdec.
Qed.

Lemma couple_1 : forall a b, Equal (couple a b) (couple b a).
Proof.
intros.
unfold couple;fsetdec.
Qed.

Lemma triple_couple_1 : forall a b, Equal (triple a b b) (couple a b).
Proof.
intros.
unfold couple, triple;fsetdec.
Qed.

Lemma triple_couple_2 : forall a b, Equal (triple a b b) (couple b a).
Proof.
intros.
unfold couple, triple;fsetdec.
Qed.

Lemma triple_couple_3 : forall a b, Equal (triple b a b) (couple a b).
Proof.
intros.
unfold couple, triple;fsetdec.
Qed.

Lemma triple_couple_4 : forall a b, Equal (triple b a b) (couple b a).
Proof.
intros.
unfold couple, triple;fsetdec.
Qed.

Lemma triple_couple_5 : forall a b, Equal (triple b b a) (couple a b).
Proof.
intros.
unfold couple, triple;fsetdec.
Qed.

Lemma triple_couple_6 : forall a b, Equal (triple b b a) (couple b a).
Proof.
intros.
unfold couple, triple;fsetdec.
Qed.

Hint Immediate 
   triple_1 triple_2 triple_3 triple_4 triple_5
   triple_couple_1 triple_couple_2 triple_couple_3
   triple_couple_4 triple_couple_5  triple_couple_6
   couple_1
 : hset.

Ltac clear_all := repeat match goal with 
| H: _ |-_ => clear H
end.

Lemma inter_fsetdecide_1 : forall A B C D, ~ A[==]B -> 
inter (triple A C D) (triple B C D)[=]couple C D.
Proof.
intros.
unfold couple, triple.
split; intros.
assert  (In a (add A (add C (add D empty)))).
fsetdec.
assert  (In a (add B (add C (add D empty)))).
fsetdec.
elim (DecPoints.eq_dec a A); intros.
rewrite a0 in H0,H1.
elim (DecPoints.eq_dec a B); intros.
rewrite a1 in *.
assert (A[==]B).
symmetry.
assumption.
intuition.
clear a0.
apply (FSetDecideTestCases.test_add_In a B (add C (add D empty))); solve [auto].
apply (FSetDecideTestCases.test_add_In a A (add C (add D empty))); solve [auto].
intros; fsetdec.
Qed.

Lemma inter_fsetdecide_2 : forall A B C alpha beta, 
             ~ alpha[==]beta -> 
inter (union (triple A B C) (singleton alpha))
  (union (triple A B C) (singleton beta))[=]triple A B C.
Proof.
intros.
split; intros.
setoid_replace (union (triple A B C) (singleton alpha)) with (add alpha (triple A B C)) in H0 by (clear H; fsetdec).
setoid_replace (union (triple A B C) (singleton beta)) with (add beta (triple A B C)) in H0 by (clear H; fsetdec).
assert (In a (add alpha (triple A B C))) by fsetdec.
assert (In a  (add beta (triple A B C))) by fsetdec.
elim (DecPoints.eq_dec a alpha); intros.
rewrite a0 in H0,H1.
elim (DecPoints.eq_dec a beta); intros.
rewrite a1 in *.
assert (alpha[==]beta).
symmetry.
assumption.
solve [intuition].
clear a0.

apply (FSetDecideTestCases.test_add_In a beta); solve[auto].
apply (FSetDecideTestCases.test_add_In a alpha); solve[auto]. 
intros; fsetdec.
Qed.
(*
Lemma inter_fsetdecide_3 : forall A B C alpha beta gamma,
 ~ alpha[==]gamma -> 
 ~ beta[==]gamma ->
inter (union (triple A B C) (couple alpha beta))
  (union (triple A B C) (singleton gamma))[=]triple A B C.
Proof.
intros.
assert (inter (couple alpha beta) (singleton gamma) [=] empty).
intros; split;intros.
assert (In a  (singleton gamma)) by fsetdec.
assert (In a (couple alpha beta)) by fsetdec.
elim (DecPoints.eq_dec a alpha).
intros.
rewrite a0 in *.
assert (alpha [==] gamma) by fsetdec.
intuition.
intros.
elim (DecPoints.eq_dec a beta).
intros.
rewrite a0 in *.
assert (beta [==] gamma) by fsetdec.
intuition.
intros.
unfold couple in H3.
apply (FSetDecideTestCases.test_add_In a beta); [idtac | auto].
apply (FSetDecideTestCases.test_add_In a alpha);solve[auto].
fsetdec. 
fsetdec.
Qed.
*)
Lemma inter_fsetdecide_4 : forall ps alpha beta,
 ~ alpha[==]beta ->
inter (union ps (singleton alpha)) (union ps (singleton beta))[=]ps.
Proof.
intros.
assert (inter (singleton alpha) (singleton beta) [=] empty).
intros; split; intros.
assert (In a (singleton alpha)) by fsetdec.
assert (In a (singleton beta)) by fsetdec.
elim (DecPoints.eq_dec a alpha).
intros.
rewrite a0 in *.
assert (alpha[==]beta) by fsetdec.
solve [intuition].
intros.
elim (DecPoints.eq_dec a beta).
intros.
rewrite a0 in *.
assert (beta[==]alpha) by fsetdec.
solve [intuition].
intros.
assert (a[==]alpha) by fsetdec.
solve [intuition].
fsetdec.
fsetdec.
Qed.

Lemma inter_fsetdecide_5 : forall ps alpha beta gamma,
 ~ alpha[==]gamma ->
 ~ beta[==]gamma ->
inter (union ps (couple alpha beta)) (union ps (singleton gamma))[=]ps.
Proof.
intros.
assert (inter (couple alpha beta) (singleton gamma) [=] empty).
intros; split;intros.
assert (In a  (singleton gamma)) by fsetdec.
assert (In a (couple alpha beta)) by fsetdec.
elim (DecPoints.eq_dec a alpha).
intros.
rewrite a0 in *.
assert (alpha [==] gamma) by fsetdec.
intuition.
intros.
elim (DecPoints.eq_dec a beta).
intros.
rewrite a0 in *.
assert (beta [==] gamma) by fsetdec.
intuition.
intros.
unfold couple in H3.
apply (FSetDecideTestCases.test_add_In a beta); [idtac | auto].
apply (FSetDecideTestCases.test_add_In a alpha);solve[auto].
fsetdec. 
fsetdec.
Qed.

Lemma union_fsetdecide : forall A0 B0 A1 B1 A C,  
(union (union (quadruple A0 B0 A1 B1) (triple A0 B0 A))
           (triple A1 B1 C)) [=] (union (quadruple A0 B0 A1 B1) (couple A C)).
Proof.
intros; split; intros.
unfold couple, triple, quadruple in *; fsetdec.
unfold couple, triple, quadruple in *; fsetdec.
Qed.

Hint Resolve inter_fsetdecide_1 inter_fsetdecide_2 union_fsetdecide
                       inter_fsetdecide_4 inter_fsetdecide_5 : hset.

Ltac fsetdecide := solve [auto with hset] || (unfold couple, triple, quadruple in *; fsetdec).

Ltac fsetdecide_no_hyps := (clear_all;fsetdecide).

End BuildFSets.