Require Export matroids_axioms.

(** A functor to go from Matroid to Matroid' *)

Module matroid_to_matroid' (DecPoints: FSetInterface.WS) (M: Matroid DecPoints) : Matroid' DecPoints
with Module FiniteSetsDefs := M.FiniteSetsDefs
with Definition rk:=M.rk.

Export M.

Module Export FiniteSetsDefs := M.FiniteSetsDefs.
Definition rk:=M.rk.

Import M.FiniteSetsDefs.FiniteSetsOfPoints.

Lemma rk_compat:
  forall x x', Equal x x' ->
     rk x = rk x'.
Proof.
intros.
apply le_antisym.
apply matroid2.
firstorder.
apply matroid2.
firstorder.
Qed.

Add Morphism rk : rk_c.
Proof.
exact rk_compat.
Qed.

Lemma matroid1' : rk empty = 0.
Proof.
assert (rk empty >= 0).
apply matroid1_a.
assert (rk empty <= 0).
apply matroid1_b.
omega.
Qed.

Import M.

Lemma test_fsetdec : forall X x,
In x X ->
inter X (singleton x)[=]singleton x.
Proof.
intros.
fsetdec.
Qed.


Lemma rk_singleton : forall x, rk (singleton x) <= 1.
Proof.
intros.
apply matroid1_b.
Qed.
Import M.
Lemma matroid2' : forall X:set_of_points, forall x : Point, 
rk(X)<=rk (add x X) <= rk(X)+1.
Proof.
intros.
split.
apply (matroid2).
fsetdecide.
assert (rk (union X (singleton x)) + rk (inter X (singleton x)) <=
       rk X + rk (singleton x)).
apply matroid3.
elim (In_dec x X).
intro.
setoid_replace (inter X (singleton x)) with (singleton x)  in H.
rewrite union_sym in H.
rewrite <- add_union_singleton in H.
omega.

unfold Equal;intro.
split.
fsetdecide.
intros.

fsetdecide. 
intro.
setoid_replace (inter X (singleton x)) with (empty)  in H.
replace (rk empty) with 0 in H.
assert (rk (singleton x) <= 1).
apply rk_singleton.
rewrite union_sym in H.
rewrite <- add_union_singleton in H.
omega.
symmetry.
apply matroid1'.

unfold Equal;intro.
split.
clear H.
fsetdec. 
autorewrite with set_simpl in *.
intuition.
Qed.

Lemma matroid3_useful : forall e e' ei : set_of_points,
 Subset ei (inter e e') ->
 rk(union e e') + rk(ei) <= rk(e) + rk(e').
Proof.
intros.
assert (rk (union e e') + rk (inter e e') <= rk e + rk e').
apply matroid3.
assert (rk (ei) <= rk (inter e e')).
apply matroid2;auto.
omega.
Qed.

Lemma add_union_singleton_sym : forall (s : t) (x : elt), 
Equal (add x s) (union s (singleton x)).
Proof.
intros.
rewrite union_sym.
apply add_union_singleton.
Qed.

Lemma matroid3': forall X y z, 
   rk(add y X) = rk(add z X) ->
   rk(add z X) = rk(X) ->
   rk(X) = rk(union X (couple y z)).
Proof.
intros.
assert (rk(X) <= rk(union X (couple y z))).
apply matroid2.
fsetdecide.
assert  (rk(union X (couple y z)) <= rk(X)).
assert ( rk (union (union X (singleton y)) (union X (singleton z))) + rk X <=
       rk (union X (singleton y)) + rk (union X (singleton z))).
apply matroid3_useful.
fsetdecide.
repeat (rewrite <- add_union_singleton_sym in H2).
setoid_replace (union (add y X) (add z X)) with (union X (couple y z)) in H2.
omega.
fsetdecide.
omega.
Qed.


End matroid_to_matroid'.
