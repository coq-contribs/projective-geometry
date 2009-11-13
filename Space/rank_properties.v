Require Export projective_space_rank_axioms. 
Require Export Omega.
Require Export matroids_properties.

Module RankProperties (DecPoints: FSetInterface.WS) (M: RankProjectiveSpace DecPoints).

Module Export Mat_Props := Matroid_Properties DecPoints M.

Module Export Matroid' := matroid_to_matroid' DecPoints M.

Export M.

(** We define the morphism to allow easier rewriting using setoids. *)

Lemma rk_compat:
  forall x x', Equal x x' ->
     rk x = rk x'.
Proof.
intros.
apply le_antisym;apply matroid2;firstorder.
Qed.

Add Morphism rk : rk_mor.
Proof.
 exact rk_compat.
Qed.

Lemma rk_singleton : forall p:Point, rk (singleton p)=1.
Proof.
intros.
assert (rk (singleton p)<= 1).
apply (rk_singleton_le);auto.
assert (rk (singleton p)>= 1).
apply (rk_singleton_ge);auto.
omega.
Qed.

Hint Resolve rk_couple_2 : rk.

Lemma rk_couple1 : forall p q:Point,~ p [==] q -> rk(couple p q)=2.
Proof.
intros.
assert (rk(couple p q)<=2).
apply (rk_couple_2).
assert (rk(couple p q)>=2).
apply (rk_couple_ge);auto.
omega.
Qed.

Lemma couple_rk2 : forall p q:Point, rk(couple p q)=1 -> p [==] q.
Proof.
intros.
elim (eq_point_dec p q);auto.
intro.
assert (rk(couple p q)=2).
apply rk_couple1;assumption.
rewrite H in H0.
assert False.
intuition.
intuition.
Qed.

Hint Resolve couple_rk2: rk.

Lemma rk_couple2 : forall p q:Point, p[==]q -> rk(couple p q)=1.
Proof.
intros.
setoid_replace (couple p q) with (singleton p).
apply (rk_singleton).
apply (couple_singleton_eq).
assumption.
Qed.

Lemma rk_couple_1 : forall p q, 1 <= rk (couple p q).
Proof.
intros.
elim (eq_point_dec p q).
intro.
rewrite rk_couple2.
omega.
assumption.
intro.
rewrite rk_couple1.
omega.
assumption.
Qed.

Hint Resolve rk_couple_1 : rk.

Lemma couple_rk1 : forall p q:Point, rk(couple p q)=2 -> ~ p [==] q.
Proof.
intros.
unfold not;intro.
assert (rk (couple p q) = 1).
setoid_replace (couple p q) with (singleton p).
apply rk_singleton.
apply (couple_singleton_eq).
assumption.
intuition.
Qed.

Lemma couple_rk_degen : forall p, rk (couple p p) = 2 -> False.
Proof.
intros.
assert (rk (couple p p) = 1).
setoid_replace (couple p p) with (singleton p).
apply rk_singleton.
fsetdecide.
intuition.
Qed.

Hint Resolve couple_rk_degen : rk.

Lemma eq_point_dec_rk : forall P Q, 
{rk(couple P Q)=1}+{rk(couple P Q)=2}.
Proof.
intros.
elim (eq_point_dec P Q).
intro.
left.
setoid_replace P with Q.
apply rk_couple2.
reflexivity.
auto.
intro.
right.
apply rk_couple1;auto.
Qed.

Lemma base_points_distinct_1 : ~ P0 [==] P1.
Proof.
assert (T:=lower_dim).
unfold not;intro.
rewrite H in T.
setoid_replace (quadruple P1 P1 P2 P3) with (triple P1 P2 P3) in T by fsetdecide.
assert (rk (triple P1 P2 P3) <= 3).
apply rk_triple_le.
omega.
Qed.

Lemma base_points_distinct_2 : ~ P2 [==] P3.
Proof.
assert (T:=lower_dim).
unfold not;intro.
rewrite H in T.
setoid_replace (quadruple P0 P1 P3 P3) with (triple P0 P1 P3) in T by fsetdecide.
assert (rk (triple P0 P1 P3) <= 3).
apply rk_triple_le.
omega.
Qed.

Lemma rk_lemma_1 : forall A B P Q,
rk (couple A B) = 2 ->
rk (triple A B P) = 2 ->
rk (triple A B Q) = 2 ->
rk (quadruple A B P Q) = 2.
Proof.
intros.
assert (rk (union (triple A B P) (triple A B Q)) + rk (couple A B) <=
           rk (triple A B P) + rk (triple A B Q)).
apply (matroid3_useful (triple A B P) (triple A B Q) (couple A B)).
clear_all.
fsetdecide.


assert (rk (union (triple A B P) (triple A B Q)) <= 2).
omega.
setoid_replace (union (triple A B P) (triple A B Q)) with (quadruple A B P Q) in H3 by fsetdecide_no_hyps.
apply le_antisym.
auto.
cut (rk (couple A B) <= rk (quadruple A B P Q)).
omega.
apply matroid2.
fsetdecide_no_hyps.
Qed.

Ltac Collapse := match goal with
H: rk (couple ?A ?B) = 1 |- _ => let T := fresh in assert (T:=couple_rk2 A B H); clear H;subst
end.

Lemma col_trans : forall A B C D:Point, 
rk (triple A C D)=2 -> rk (triple B C D)=2 -> rk (couple C D)=2 -> rk(triple A B C)<=2.
Proof.
intros A B C D HACD HBCD HCD.
elim (eq_point_dec_rk A B);intro.
Collapse.
rewrite H in *.
setoid_replace (triple B B C) with (couple B C).
apply rk_couple_2.
fsetdecide.
generalize (matroid3 (triple A C D) (triple B C D)).
rewrite HACD.
rewrite HBCD.
setoid_replace (inter (triple A  C D) (triple B C D)) with (couple C D).
rewrite HCD.
intros.
assert (rk (union (triple A C D) (triple B C D))<=2).
omega.
clear H.
assert (Hsubset : Subset (triple A B C) (union (triple A C D) (triple B C D))).
fsetdecide_no_hyps.
generalize (matroid2  (triple A B C) (union (triple A C D) (triple B C D)) Hsubset).
omega.

assert (~ (A [==] B)).
apply couple_rk1;auto.

clear HACD HBCD HCD b.
fsetdecide.
Qed.

Lemma rk_triple_ABC_couple_AB :  forall A B C, rk(triple A B C)=3 -> rk(couple A B)=2.
Proof.
intros A0 B0 C0 rABC0.
assert (rk(couple A0 B0)=1\/rk(couple A0 B0)=2).
assert (rk (couple A0 B0) <= 2).
apply (rk_couple_2 A0 B0).
assert (1 <= rk (couple A0 B0)).
apply (rk_couple_1 A0 B0).
omega.
elim H.
2:auto.
intros H'.
rewrite (couple_rk2 A0 B0 H') in rABC0.
setoid_replace (triple B0 B0 C0) with (couple B0 C0) in rABC0 by fsetdecide.
assert (rk (couple B0 C0) <= 2).
apply (rk_couple_2 B0 C0).
omega.
Qed.

Lemma rk_triple_ABC_couple_BC :  forall A B C, rk(triple A B C)=3 -> rk(couple B C)=2.
Proof.
intros.
eapply rk_triple_ABC_couple_AB with (C:=A).
setoid_replace (triple B C A) with (triple A B C) by fsetdecide.
assumption.
Qed.

Lemma rk_triple_ABC_couple_AC :  forall A B C, rk(triple A B C)=3 -> rk(couple A C)=2.
Proof.
intros.
eapply rk_triple_ABC_couple_AB with (C:=B).
setoid_replace (triple A C B) with (triple A B C) by fsetdecide.
assumption.
Qed.

Hint Resolve rk_triple_ABC_couple_AB rk_triple_ABC_couple_BC rk_triple_ABC_couple_AC : rk.

Lemma rk_triple_singleton :forall (x y z a:Point),
rk(triple x y z)=3 /\ rk(couple x a)=2 /\ rk(triple y z a)=2
-> rk(union (triple x y z) (singleton a))=3.
Proof.
intros a b c alpha H.
elim H;clear H;intros rabc H.
elim H;clear H;intros ranalpha rbcalpha.

assert (rab : rk (couple a b) =2).
eauto with rk.
assert (rac : rk (couple a c) =2).
eauto with rk.
assert (rbc : rk (couple b c) =2).
eauto with rk.

apply le_antisym.
(* <= *)
assert (T: rk (union (triple a b c) (triple b c alpha)) + rk (couple b c) <=
    rk (triple a b c) + rk (triple b c alpha)).
apply (matroid3_useful (triple a b c) (triple b c alpha) (couple b c)).
fsetdecide_no_hyps.
setoid_replace  (union (triple a b c) (triple b c alpha))
                 with (union (triple a b c) (singleton alpha)) in T by fsetdecide_no_hyps.
omega.

(* >= *)
assert (Hsubset : (Subset (triple a b c) (union (triple a b c) (singleton alpha)))) by fsetdecide_no_hyps.
generalize (matroid2 (triple a b c) (union (triple a b c) (singleton alpha)) Hsubset).
rewrite rabc.
auto.
Qed.

Hint Resolve  rk_triple_singleton : rk.

Lemma rk_couple_not_zero : forall A B, (rk (couple A B) = 0) -> False.
Proof.
unfold not; intros.
elim (eq_point_dec A B);intros.
generalize (rk_couple2 A B).
intuition.
generalize (rk_couple1 A B).                                                                                                             
intuition.
Qed.

Hint Resolve rk_couple_not_zero : rk.

Ltac simplify_rk := match goal with
| H: rk (couple ?A ?B) = 1 |- _ => 
      let id := fresh in 
           assert (id: A [==] B); 
           try (apply (couple_rk2 A B H));
           subst;clear H
| H :rk (couple ?A ?B) = 0 |- _ => 
           assert False; 
           try apply (rk_couple_not_zero A B);
           intuition
| H : rk (couple ?A ?A) = 2 |- _ =>
           assert False; 
           try apply (couple_rk_degen A);
           intuition
 end.

Ltac smart_subst := repeat (progress subst); try simplify_rk.

Lemma sym : forall A B:Point, A<>B->B<>A.
Proof.
auto.
Qed.

Lemma L1beta_gen : forall A B C beta, 
rk(triple A C beta) = 2  -> 
rk (triple A B C) = 3 -> 
rk(union (triple A B C) (singleton beta))=3.
Proof.
intros  A B C beta.
intro rACbeta.
intro rABC.
apply le_antisym.
assert (T : rk (union (triple A B C) (triple A C beta)) + rk (couple A C) <=
       rk (triple A B C) + rk (triple A C beta)).
apply (matroid3_useful (triple A B C) (triple A C beta) (couple A C)).
fsetdecide_no_hyps.
setoid_replace (union(triple A B C)(triple A C beta)) with (union(triple A B C)(singleton beta)) in T by fsetdecide_no_hyps.
assert (HrAC : rk (couple A C) = 2) by eauto with rk.
omega.

(*>=*)
assert( Hsubset : (Subset (triple A B C) (union (triple A B C) (singleton beta)))).
fsetdecide_no_hyps.
generalize (matroid2 (triple A B C) (union (triple A B C) (singleton beta)) Hsubset).
rewrite rABC.
auto.
Qed.

Lemma L1gamma_gen : forall A B C gamma, 
rk (triple A B C) = 3 ->
rk (triple A B gamma) = 2 ->
rk(union (triple A B C) (singleton gamma))=3.
Proof.
intros.
setoid_replace (union (triple A B C) (singleton gamma)) 
with (union (triple A C B) (singleton gamma)) by fsetdecide_no_hyps.
apply L1beta_gen.
assumption.
setoid_replace (triple A B C) with (triple A C B) in H by fsetdecide_no_hyps.
assumption.
Qed.

Lemma coplanar : forall O A B C A' B' C' : Point,
rk (triple A B C ) = 3 ->
rk (couple A' B) = 2 ->
rk (couple C' B) = 2 ->
rk (couple A B') = 2 ->
rk (couple B' C) = 2 ->
rk (triple A' B' C' ) = 3 ->
rk (triple O B B')  = 2 ->
rk (union (couple O A) (triple C A' C')) = 2 ->
rk (union (triple A B C) (triple A' B' C')) <> 4.
Proof.
intros O A B C A' B' C'.
intro rABC.
intro rA'B.
intro rC'B.
intro rAB'.
intro rB'C.
intro rA'B'C'.
intro rOBB'.
intro rOACA'C'.
unfold not.
intro.
assert (T: rk (union (triple O B B') (union (couple O A) (triple C A' C'))) +
      rk (singleton O) <=
      rk (triple O B B') + rk (union (couple O A) (triple C A' C'))).
apply (matroid3_useful  (triple O B B') (union (couple O A) (triple C A' C')) (singleton O)).
fsetdecide.
rewrite rOBB' in T.
rewrite rOACA'C' in T.
rewrite rk_singleton in T.
assert (rk (union (triple A B C) (triple A' B' C')) <=
    rk (union (singleton O) (union (triple A B C) (triple A' B' C')))).
apply matroid2.
fsetdecide.
setoid_replace ((union (singleton O) (union (triple A B C) (triple A' B' C')))) with (union (triple O B B') (union (couple O A) (triple C A' C'))) in H0.
omega.
unfold Equal; split; fsetdecide_no_hyps.
Qed.

Lemma rk_quadruple_ABCD_couple_AB :  
forall A B C D, rk(add D (triple A B C))>=4 -> rk(couple A B)=2.
Proof.
intros A0 B0 C0 D0 rABCD0.
assert (rk(couple A0 B0)=1\/rk(couple A0 B0)=2).

assert (rk (couple A0 B0) <= 2).
apply (rk_couple_2 A0 B0).
assert (1 <= rk (couple A0 B0)).
apply (rk_couple_1 A0 B0).
omega.
elim H.
2:auto.
intros H'.
rewrite (couple_rk2 A0 B0 H') in rABCD0.
setoid_replace (add D0 (triple B0 B0 C0)) with (triple B0 C0 D0) in rABCD0 by fsetdecide_no_hyps.
assert (rk (triple B0 C0 D0) <= 3) by apply (rk_triple_le B0 C0 D0).
omega.
Qed.

Lemma rk_quadruple_ABCD_couple_AC :  
forall A B C D, rk(add D (triple A B C))>=4 -> rk(couple A C)=2.
Proof.
intros A0 B0 C0 D0 rABCD0.
eapply (rk_quadruple_ABCD_couple_AB A0 C0 B0 D0).
setoid_replace (add D0 (triple A0 C0 B0)) with (add D0 (triple A0 B0 C0)) by fsetdecide.
assumption.
Qed.

Lemma rk_quadruple_ABCD_couple_AD :  
forall A B C D, rk(add D (triple A B C))>=4 -> rk(couple A D)=2.
Proof.
intros A0 B0 C0 D0 rABCD0.
eapply (rk_quadruple_ABCD_couple_AB A0 D0 B0 C0).
setoid_replace (add C0 (triple A0 D0 B0)) with (add D0 (triple A0 B0 C0)) by fsetdecide_no_hyps.
assumption.
Qed.

Lemma rk_quadruple_ABCD_couple_BC :  
forall A B C D, rk(add D (triple A B C))>=4 -> rk(couple B C)=2.
Proof.
intros A0 B0 C0 D0 rABCD0.
eapply (rk_quadruple_ABCD_couple_AB B0 C0 D0 A0).
setoid_replace (add D0 (triple A0 B0 C0)) with (add A0 (triple B0 C0 D0)) in rABCD0 by fsetdecide_no_hyps.
assumption.
Qed.

Lemma rk_quadruple_ABCD_couple_BD :  
forall A B C D, rk(add D (triple A B C))>=4 -> rk(couple B D)=2.
Proof.
intros A0 B0 C0 D0 rABCD0.
eapply (rk_quadruple_ABCD_couple_AB B0 D0 C0 A0).
setoid_replace (add A0 (triple B0 D0 C0)) with (add D0 (triple A0 B0 C0)) by fsetdecide_no_hyps.
assumption.
Qed.

Lemma rk_quadruple_ABCD_couple_CD :  
forall A B C D, rk(add D (triple A B C))>=4 -> rk(couple C D)=2.
Proof.
intros A0 B0 C0 D0 rABCD0.
eapply (rk_quadruple_ABCD_couple_AB C0 D0 A0 B0).
setoid_replace (add B0 (triple C0 D0 A0)) with (add D0 (triple A0 B0 C0)) by fsetdecide_no_hyps.
assumption.
Qed.

Lemma rk_quadruple_ABCD_triple_ABC :  
forall A B C D, rk(add D (triple A B C))>=4 -> rk(triple A B C)=3.
Proof.
intros A0 B0 C0 D0 rABCD0.
apply le_antisym.
apply rk_triple_le.
assert (rk (triple A0 B0 C0) <=
             rk (add D0 (triple A0 B0 C0)) <=
             rk (triple A0 B0 C0) + 1).
apply matroid2';auto.
intuition.
Qed.

Lemma intersecting_lines_rank_3 : forall A B C D I,
rk (triple A B I) <= 2 ->
rk (triple C D I) <= 2 ->
rk (union (singleton I) (quadruple A B C D)) <= 3.
Proof.
intros.
assert (rk (union (triple A B I) (triple C D I)) +
       rk (singleton I) <=
       rk (triple A B I) + rk (triple C D I)).
apply (matroid3_useful (triple A B I) (triple C D I) (singleton I)).
fsetdecide.
rewrite rk_singleton in H1.
setoid_replace (union (triple A B I) (triple C D I)) 
with (union (singleton I) (quadruple A B C D)) in H1.
omega.
unfold Equal; split; fsetdecide_no_hyps.
Qed.

(** Uniqueness of inter *)
Lemma uniq_inter : 
forall A B C D M P, 
rk(couple A B)=2 -> 
rk(couple C D) = 2 ->
rk(triple A B M) <= 2 -> 
rk(triple C D M) <= 2 -> 
rk(triple A B P) <= 2 ->
rk(triple C D P) <= 2 -> 
rk(quadruple A B C D) >= 3 -> 
rk(couple M P) = 1.
Proof.
intros A B C D M P rAB rCD rABM rCDM rABP rCDP rABCD.
apply le_antisym.

assert (rk(add P (triple A B M))<=2).
generalize (matroid3 (triple A B M) (triple A B P)).
setoid_replace (union (triple A B M) (triple A B P)) 
with (add P (triple A B M)) by fsetdecide_no_hyps.
assert (rk (inter (triple A B M) (triple A B P))>=rk(couple A B)).
apply matroid2.
fsetdecide_no_hyps.
omega.
assert (rk(add P (triple C D M))<=2).
generalize (matroid3 (triple C D M) (triple C  D P)).
setoid_replace (union (triple C D M) (triple C D P)) 
with (add P (triple C D M)) by fsetdecide_no_hyps.
assert (rk (inter (triple C D M) (triple C D P))>=rk(couple C D)).
apply matroid2.
fsetdecide_no_hyps.
omega.
assert(rk(union (triple A B C) (triple D M P))>=3).
assert(rk (quadruple A B C D) <= 3).
assert (rk (union (singleton M) (quadruple A B C D)) <= 3).
apply (intersecting_lines_rank_3 A B C D M);auto.
assert (rk (quadruple A B C D) <=
       rk (union (singleton M) (quadruple A B C D))).
apply matroid2.
fsetdecide_no_hyps.
omega.
assert (rABCD' : rk (quadruple A B C D) = 3).
omega.
rewrite <- rABCD'.
apply matroid2.
fsetdecide_no_hyps.

generalize (matroid3 (add P (triple A B M))  (add P (triple C D M))).
setoid_replace (union (add P (triple A B M)) (add P (triple C D M))) with
(union (triple A B C) (triple D M P)) by (unfold Equal; split; fsetdecide_no_hyps).
assert (rk((inter (add P (triple A B M)) (add P (triple C D M))))>=rk(couple M P)).
apply matroid2.
fsetdecide_no_hyps.
omega.
apply rk_couple_1.
Qed.

Lemma uniq_inter_spec : forall gamma a b B,
rk (triple a b gamma) <= 2 ->
rk (triple a B gamma) <= 2 ->
rk (triple a b B) >= 3 ->
rk (couple a gamma) = 1.
Proof.
intros.
elim (eq_point_dec_rk a gamma);intro.
auto.
assert (rk (union (triple a b gamma) (triple a B gamma)) + rk (couple a gamma) <=
       rk (triple a b gamma) + rk (triple a B gamma)).
apply matroid3_useful.
fsetdecide_no_hyps.
rewrite b0 in H2.
assert (rk (quadruple a b B gamma) <= 2).
setoid_replace (quadruple a b B gamma) with  (union (triple a b gamma) (triple a B gamma)) by fsetdecide_no_hyps.
omega.
assert (rk (triple a b B)  <= rk (quadruple a b B gamma)).
apply matroid2.
fsetdecide_no_hyps.
omega.
Qed.

Lemma uniq_inter_spec_bis : forall gamma a b B,
rk (triple a b gamma) <= 2 ->
rk (triple a B gamma) <= 2 ->
rk (couple a gamma) = 1 \/  rk (triple a b B) <= 2.
Proof.
intros.
assert (rk (triple a b B) <= 2 \/ rk (triple a b B) >= 3).
omega.
elim H1;intro.
right; auto.
left.
eapply (uniq_inter_spec).
apply H.
apply H0.
auto.
Qed.

Lemma stays_in_plane : forall E a b x, rk(E)<=3 -> In a E -> In b E -> 
rk(couple a b)=2->
rk(triple a b x)=2 -> 
rk(add x E)<=3.
Proof.
intros E m n x.
intros.
generalize (matroid3 E (triple m n x)).
assert (rk (union E (triple m n x))>=rk (add x E)).
apply matroid2; fsetdecide_no_hyps.
assert (rk(inter E (triple m n x))>=rk(couple m n)).
apply matroid2.
clear H2 H3 H4; fsetdecide.
omega.
Qed.

Lemma stays_in_the_plane : forall M N P Q,
rk(triple M N P) = 3 -> rk(triple M N Q) = 2 -> rk(add Q (triple M N P)) = 3.
Proof.
intros M N P Q rMNP rMNQ.
assert (rk(couple M N) = 2).
eapply rk_triple_ABC_couple_AB.
eassumption.
apply le_antisym.
generalize (matroid3 (triple M N P) (triple M N Q)).
setoid_replace (union (triple M N P) (triple M N Q)) 
with (add Q (triple M N P)) by fsetdecide_no_hyps.
assert (rk(inter (triple M N P) (triple M N Q))>=rk(couple M N)) 
by (apply matroid2;fsetdecide_no_hyps).
omega.
rewrite <- rMNP.
apply matroid2;fsetdecide_no_hyps.
Qed.

(** How to remove a point from a flat of 4 points whose rank is 3 ? *) 
Lemma rk2_3 : forall P Q R S, 
rk(add S (triple P Q R))=3->
rk(triple P Q R)=2->
rk(couple P Q)=2 ->
rk(couple R S)=2 ->
rk(triple P Q S)=3.
Proof.
intros X Y Z T HXYZT HXYZ HXY HZT.
apply le_antisym.
apply rk_triple_le.
generalize (matroid3 (triple X Y Z) (triple X Y T)).
setoid_replace (union (triple X Y Z) (triple X Y T)) with (add T (triple X Y Z))
by fsetdecide_no_hyps.
rewrite HXYZT.
assert (rk  (inter (triple X Y Z) (triple X Y T))>=rk (couple X Y)) 
  by (apply matroid2; fsetdecide_no_hyps).
omega.
Qed.

(** changing one of the points defining a plane in a 3D figure *)
Lemma rk3_4 : forall A B C M P,
rk(add M (triple A B C)) = 3 ->
rk(triple B C M) = 3 -> 
rk(add P (triple A B C)) >= 4 ->
rk(add P (triple M B C)) >= 4.
Proof.
intros A B C M P rABCM rBCM rABCP.
generalize (matroid3 (add P (triple M B C)) (add M (triple A B C))).
setoid_replace  (union (add P (triple M B C)) (add M (triple A B C))) with
(union (triple A B C) (couple M P)) by (unfold Equal; split; fsetdecide_no_hyps).
assert  (rk (inter (add  P (triple M B C)) (add M (triple A B C)))>= rk (triple B C M)).
apply matroid2; fsetdecide_no_hyps.
assert (rk(union (triple A B C) (couple M P)) >= rk(add P (triple A B C)))
by (apply matroid2;fsetdecide_no_hyps).
omega.
Qed.

Lemma rank_not_empty : forall E, (exists x, In x E) -> rk E > 0.
Proof.
intros.
elim H; intros x H1; clear H.
assert (Subset (singleton x) E) by fsetdecide.
assert (rk (singleton x) <= rk E) by (apply matroid2; fsetdecide).
rewrite rk_singleton in H0.
omega.
Qed.

Lemma double_flag : forall  x A B, 
rk (add x A) <= 2 ->
rk (add x B) <= 2 ->
rk (add x (union A B)) <= 3.
Proof.
intros.
assert (rk (union (add x A) (add x B)) + rk (singleton x) <=
       rk (add x A) + rk (add x B)).
apply (matroid3_useful).
fsetdecide.
rewrite rk_singleton in H1.
setoid_replace (add x (union A B))  with (union (add x A) (add x B)) by fsetdecide.
omega.
Qed.

Lemma construction : 
 forall n , forall E, rk E = n -> n<=3 -> exists P, rk (add P E) = n+1.
Proof.
intros.
assert (T:=lower_dim).
assert (rk (quadruple P0 P1 P2 P3) = 4).
apply le_antisym.
apply rk_quadruple_le.
auto.
clear H1.
assert (n=0 \/ n=1 \/ n=2 \/ n=3) by omega.

(** Case n=0 *)
intuition.
subst.
rewrite H2.
assert (rk (add P0 E) = 0 \/ rk (add P0 E) = 1).
assert (rk E <= rk (add P0 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P1 E) = 0 \/ rk (add P1 E) = 1).
assert (rk E <= rk (add P1 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P2 E) = 0 \/ rk (add P2 E) = 1).
assert (rk E <= rk (add P2 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P3 E) = 0 \/ rk (add P3 E) = 1).
assert (rk E <= rk (add P3 E) <= rk E + 1) by apply matroid2'.
omega.

elim H;intro;[idtac|firstorder];clear H.
elim H1;intro;[idtac|firstorder];clear H1.
elim H3;intro;[idtac|firstorder];clear H3.
elim H4;intro;[idtac|firstorder];clear H4.
assert (rk E = rk (union E (couple P0 P1))).
eapply matroid3';unfold Matroid'.rk;congruence.

rewrite H2 in H4.
assert (rk (couple P0 P1) <= rk  (union E (couple P0 P1))).
apply matroid2;fsetdecide.
assert (rk (couple P0 P1) <= 0) by omega.
assert (rk (couple P0 P1) >= 1).
apply rk_couple_1.
cut False;intuition.

(** Case n=1 *)
subst.
rewrite H1.
assert (rk (add P0 E) = 1 \/ rk (add P0 E) = 2).
assert (rk E <= rk (add P0 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P1 E) = 1 \/ rk (add P1 E) = 2).
assert (rk E <= rk (add P1 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P2 E) = 1 \/ rk (add P2 E) = 2).
assert (rk E <= rk (add P2 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P3 E) = 1 \/ rk (add P3 E) = 2).
assert (rk E <= rk (add P3 E) <= rk E + 1) by apply matroid2'.
omega.
elim H;intro;[idtac|firstorder];clear H.
elim H3;intro;[idtac|firstorder];clear H3.
elim H2;intro;[idtac|firstorder];clear H2.
elim H4;intro;[idtac|firstorder];clear H4.
assert (rk E = rk (union E (couple P0 P1))).
eapply matroid3';unfold Matroid'.rk;congruence.

assert (rk E = rk (union E (couple P2 P3))).
apply matroid3';unfold Matroid'.rk;congruence.

assert (rk (union E (union (couple P0 P1) (couple P2 P3))) =rk E).
apply (matroid3'_gen E (couple P0 P1) (couple P2 P3));symmetry;auto.
rewrite H1 in H7.
assert (rk (quadruple P0 P1 P2 P3) <= rk (union E (union (couple P0 P1) (couple P2 P3)))).
apply (matroid2).
fsetdecide_no_hyps.
cut False;intuition.

subst.
rewrite H2.
assert (rk (add P0 E) = 2 \/ rk (add P0 E) = 3).
assert (rk E <= rk (add P0 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P1 E) = 2 \/ rk (add P1 E) = 3).
assert (rk E <= rk (add P1 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P2 E) = 2 \/ rk (add P2 E) = 3).
assert (rk E <= rk (add P2 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P3 E) = 2 \/ rk (add P3 E) = 3).
assert (rk E <= rk (add P3 E) <= rk E + 1) by apply matroid2'.
omega.
elim H;intro;[idtac|firstorder];clear H.
elim H1;intro;[idtac|firstorder];clear H1.
elim H3;intro;[idtac|firstorder];clear H3.
elim H4;intro;[idtac|firstorder];clear H4.

assert (rk E = rk (union E (couple P0 P1))).
eapply matroid3';unfold Matroid'.rk;congruence.

assert (rk E = rk (union E (couple P2 P3))).
apply matroid3';unfold Matroid'.rk;congruence.

assert (rk (union E (union (couple P0 P1) (couple P2 P3))) =rk E).
apply (matroid3'_gen E (couple P0 P1) (couple P2 P3));symmetry;auto.
rewrite H2 in H7.
assert (rk (quadruple P0 P1 P2 P3) <= rk (union E (union (couple P0 P1) (couple P2 P3)))).
apply (matroid2).
fsetdecide_no_hyps.
cut False;intuition.

subst.
rewrite H2.
assert (rk (add P0 E) = 3 \/ rk (add P0 E) = 4).
assert (rk E <= rk (add P0 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P1 E) = 3 \/ rk (add P1 E) = 4).
assert (rk E <= rk (add P1 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P2 E) = 3 \/ rk (add P2 E) = 4).
assert (rk E <= rk (add P2 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P3 E) = 3 \/ rk (add P3 E) = 4).
assert (rk E <= rk (add P3 E) <= rk E + 1) by apply matroid2'.
omega.
elim H;intro;[idtac|firstorder];clear H.
elim H1;intro;[idtac|firstorder];clear H1.
elim H3;intro;[idtac|firstorder];clear H3.
elim H4;intro;[idtac|firstorder];clear H4.

assert (rk E = rk (union E (couple P0 P1))).
apply matroid3';unfold Matroid'.rk;congruence.

assert (rk E = rk (union E (couple P2 P3))).
apply matroid3';unfold Matroid'.rk;congruence.

assert (rk (union E (union (couple P0 P1) (couple P2 P3))) =rk E).
apply (matroid3'_gen E (couple P0 P1) (couple P2 P3));symmetry;auto.
rewrite H2 in H7.
assert (rk (quadruple P0 P1 P2 P3) <= rk (union E (union (couple P0 P1) (couple P2 P3)))).
apply (matroid2).
fsetdecide_no_hyps.
cut False;intuition.
Qed.

End RankProperties.
