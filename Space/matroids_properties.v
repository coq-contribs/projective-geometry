Require Export matroid_to_matroid_p.

Module Matroid_Properties  (DecPoints: FSetInterface.WS) (Import M: Matroid DecPoints).

Module Export M' := matroid_to_matroid' DecPoints M.

Export M.FiniteSetsDefs.

Add Morphism rk : rk_mor.
Proof.
 exact rk_compat.
Qed.

Add Morphism couple: couple_mor.
Proof.
intros.
unfold couple.
rewrite H.
rewrite H0.
fsetdecide.
Qed.

Lemma add_inj : forall x E E', 
 E [=] E' -> (Equal (add x E) (add x E')).
Proof.
intros.
rewrite H.
fsetdecide.
Qed.

Add Morphism triple: triple_mor.
Proof.
intros.
unfold triple.
rewrite H;clear H.
apply add_inj.
rewrite H0; clear H0.
apply add_inj.
rewrite H1; clear H1.
fsetdecide.
Qed.

Add Morphism quadruple: quadruple_mor.
Proof.
intros.
unfold quadruple.
rewrite H;clear H.
apply add_inj.
rewrite H0; clear H0.
apply add_inj.
rewrite H1; clear H1.
apply add_inj.
rewrite H2.
fsetdecide.
Qed.

Lemma rk_singleton_le :  forall p:Point, rk (singleton p)<= 1.
Proof.
generalize (matroid2' empty).
intro.
rewrite matroid1' in H.
intro.
assert (T:= H p).
setoid_replace (add p empty) with (singleton p) in T.
omega.
fsetdecide.
Qed.

Lemma matroid1_b_useful :  forall X m,  cardinal X <= m -> rk X <= m.
Proof.
intros.
assert (rk X <= cardinal X).
apply matroid1_b;auto.
omega.
Qed.


Lemma cardinal_couple : forall p q, ~ p [==] q -> cardinal (couple p q) = 2.
Proof.
intros.
unfold couple.
repeat (rewrite (add_cardinal_2)).
rewrite empty_cardinal;auto.
fsetdecide.
fsetdecide.
Qed.

Lemma eq_point_dec : forall a b: Point, {a[==]b}+{~ a[==]b}.
Proof.
intros.
elim (DecPoints.eq_dec a b);auto.
Qed.

Lemma rk_couple_2 : forall p q:Point, rk(couple p q)<=2.
Proof.
intros.
elim (eq_point_dec p q).
intro.
setoid_replace p with q by auto. 
setoid_replace (couple q q) with (singleton q) by fsetdecide.
apply matroid1_b_useful.
auto with set.
intro.
apply matroid1_b_useful.
rewrite cardinal_couple;
auto.
Qed.

Lemma rk_triple_le : forall A B C : Point, rk (triple A B C) <= 3.
Proof.
intros.
assert (T:=matroid2' (couple A B) C).
decompose [and] T;clear T.
setoid_replace (add C (couple A B)) with (triple A B C) in H0 by fsetdecide.
assert (rk (couple A B) <= 2) by apply rk_couple_2.
omega.
Qed.

Lemma rk_quadruple_le : forall A B C D : Point, rk (quadruple A B C D) <= 4.
Proof.
intros.
assert (T:=matroid2' (triple A B C) D).
decompose [and] T;clear T.
setoid_replace (add D (triple A B C)) with (quadruple A B C D) in H0 by fsetdecide.
assert (rk (triple A B C) <= 3) by apply rk_triple_le.
omega.
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

Lemma matroid3'_gen : forall E A B, 
rk (union E A) = rk E ->
rk (union E B) = rk E ->
rk (union E (union A B)) = rk E.
Proof.
intros.
apply le_antisym.
setoid_replace (union E (union A B)) with (union (union E A) (union E B)) by fsetdecide.
assert (rk (union (union E A) (union E B)) + rk E <=
  rk (union E A) + rk (union E B)).
apply (matroid3_useful (union E A) (union E B) E).
fsetdecide.
rewrite H in H1.
rewrite H0 in H1.
omega.
apply matroid2.
fsetdecide.
Qed.

End Matroid_Properties.

