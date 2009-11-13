Require Export projective_space_axioms.
Require Export projective_space_rank_axioms.
Require Export rank_properties.

Module RankProjectiveSpaceToProjectiveSpaceOrHigher 
 (Import DecPoints: FSetInterface.WS) (Import M:RankProjectiveSpace DecPoints) : ProjectiveSpaceOrHigher DecPoints
with Definition Point:= M.Point.

Module Export Props := RankProperties DecPoints M.

Definition Point:= Point.

Open Scope type_scope.

Inductive LineInd : Type :=
| Cline : forall (A B:Point) (H: ~ A [==] B), LineInd.

Definition Line := LineInd.

Definition fstP : Line -> Point.
intros.
elim X.
intros.
exact A.
Defined.

Definition sndP : Line -> Point.
intros.
elim X.
intros.
exact B.
Defined.

Definition Incid (A:Point) (l:Line) := rk (triple (fstP l) (sndP l) A) = 2.

Lemma incid_dec :  forall (A:Point)(l:Line), {Incid A l} + {~Incid A l}.
Proof.
intros.
unfold Incid.
exact (eq_nat_dec (rk (triple (fstP l) (sndP l) A)) 2).
Qed.

Lemma second_point : forall A: Point, {B | ~ A [==] B}.
Proof.
intro.
assert (T:= lower_dim).

elim (eq_dec P0 A);intro;unfold DecPoints.eq in *.
elim (eq_dec P1 P0);intro;unfold DecPoints.eq in *.
rewrite a0 in *; clear a0.
elim (eq_dec P2 P0);intro;unfold DecPoints.eq in *.
rewrite a0 in *; clear a0.
elim (eq_dec P3 P0);intro;unfold DecPoints.eq in *.
rewrite a0 in *; clear a0.
setoid_replace (quadruple P0 P0 P0 P0) with (singleton P0) in T by fsetdecide.
rewrite rk_singleton in T.
cut False.
intuition.
omega.
rewrite a in *.
exists P3;auto.
intuition.
rewrite a in *.
exists P2;auto.
intuition.
rewrite a in *.
exists P1;auto.
intuition.
exists P0;auto.
intuition.
Qed.

Definition line_eq l m := rk (quadruple (fstP l) (sndP l) (fstP m) (sndP m)) = 2.

Lemma line_eq_refl : forall l, line_eq l l.
Proof.
intro.
induction l.
unfold line_eq, Incid.
simpl.
setoid_replace (quadruple A B A B) with (couple A B) by fsetdecide.
apply rk_couple1.
auto.
Qed.

Lemma line_eq_sym : forall l m, line_eq l m -> line_eq m l.
Proof.
intros.
induction l.
induction m.
unfold line_eq, Incid in *.
simpl in *.
setoid_replace (quadruple A0 B0 A B) with (quadruple A B A0 B0).
auto.
clear H0 H1 H; fsetdecide.
Qed.

Lemma line_eq_trans : forall l m n, line_eq l m -> line_eq m n -> line_eq l n.
Proof.
intros.
induction l.
induction m.
induction n.
unfold line_eq, Incid in *.
simpl in *.
assert (rk (union (quadruple A B A0 B0) (quadruple A0 B0 A1 B1)) +
           rk (couple A0 B0) <=
           rk (quadruple A B A0 B0) + rk (quadruple A0 B0 A1 B1)).
apply matroid3_useful.
clear_all; fsetdecide.
assert (rk (couple A0 B0) = 2).
apply rk_couple1;auto.
assert (rk (union (quadruple A B A0 B0) (quadruple A0 B0 A1 B1)) <= 2).
omega.
apply le_antisym.
cut (rk (quadruple A B A1 B1) <= rk (union (quadruple A B A0 B0) (quadruple A0 B0 A1 B1)) ).
omega.
apply matroid2;clear_all; fsetdecide.
assert (rk (couple A1 B1) = 2).
apply rk_couple1;auto.
rewrite <- H7.
apply matroid2;clear_all;fsetdecide.
Qed.

Lemma a1_exists : forall (A B :Point) , {l : Line | Incid A l /\ Incid B l}.
Proof.
intros.
elim (eq_dec A B);intro.
elim (second_point B).
intros C H.
exists (Cline B C H).
unfold Incid.
simpl.
rewrite a in *; clear a.
setoid_replace (triple B C B) with (couple C B) by (clear_all;fsetdecide).
split.
apply rk_couple1.
auto.
apply rk_couple1.
auto.
exists (Cline A B b).
unfold Incid.
simpl.
setoid_replace (triple A B A) with (couple A B) by (clear_all;fsetdecide).
setoid_replace (triple A B B) with (couple A B) by (clear_all;fsetdecide).
split.
apply rk_couple1.
auto.
apply rk_couple1.
auto.
Qed.

Lemma uniqueness : forall (A B :Point)(l1 l2:Line),
   Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> A [==] B \/ line_eq l1 l2.
Proof.
intros A B l1 l2.
elim (DecPoints.eq_dec A B);intro.
left;auto.
unfold DecPoints.eq in *.
elim l1;intros P Q HPQ.
elim l2;intros R S HRS.
intros.
right.
unfold Incid, line_eq in *.
simpl in *.
assert (rk (couple P Q) = 2).
apply rk_couple1;assumption.
assert (rk (couple R S) = 2).
apply rk_couple1;assumption.
assert (rk (couple A B) = 2).
apply rk_couple1;assumption.

assert (rk (quadruple P Q A B) = 2).
apply le_antisym.
assert (rk (union (triple P Q A) (triple P Q B)) + rk (couple P Q) <=
           rk (triple P Q A) + rk (triple P Q B)).
apply (matroid3_useful (triple P Q A) (triple P Q B) (couple P Q)).
clear_all; fsetdecide.
setoid_replace (union (triple P Q A) (triple P Q B)) with (quadruple P Q A B) in H6 by (clear_all;fsetdecide).
omega.
rewrite <- H0.
apply matroid2; clear_all; fsetdecide.

assert (rk (quadruple R S A B) = 2).
apply le_antisym.
assert (rk (union (triple R S A) (triple R S B)) + rk (couple R S) <=
           rk (triple R S A) + rk (triple R S B)).
apply (matroid3_useful (triple R S A) (triple R S B) (couple R S)).
clear_all; fsetdecide.
setoid_replace (union (triple R S A) (triple R S B)) with (quadruple R S A B) in H7 by (clear_all; fsetdecide).
omega.
rewrite <- H1.
apply matroid2; (clear_all; fsetdecide).
 
assert (rk (union (quadruple P Q A B) (quadruple R S A B)) +
           rk (couple A B) <=
           rk (quadruple P Q A B) + rk (quadruple R S A B)).
apply (matroid3_useful (quadruple P Q A B) (quadruple R S A B) (couple A B)).
(clear_all; fsetdecide).
assert (rk (union (quadruple P Q A B) (quadruple R S A B)) <= 2).
omega.
apply le_antisym.
assert (rk (quadruple P Q R S) <= rk (union (quadruple P Q A B) (quadruple R S A B))).
apply matroid2.
(clear_all; fsetdecide).
omega.
rewrite <- H3.
apply matroid2.
(clear_all; fsetdecide).
Qed.

(* A2 : Pasch's axiom *)
Definition dist4 A B C D  := 
 ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ 
 ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D.

Definition dist3 A B C  := 
 ~ A [==] B /\ ~ A [==] C /\ ~ B [==] C.

Lemma a2 : forall A B C D:Point, forall lAB lCD lAC lBD :Line, 
dist4 A B C D -> 
Incid A lAB/\Incid B lAB ->  
Incid C lCD/\Incid D lCD -> 
Incid A lAC/\Incid C lAC -> 
Incid B lBD/\Incid D lBD ->
(exists I:Point, (Incid I lAB /\ Incid I lCD)) -> exists J:Point, (Incid J lAC /\Incid J lBD).
Proof.
intros.
induction lAB.
induction lCD.
induction lAC.
induction lBD.
unfold Incid in *.
simpl in *.
decompose [and] H0; clear H0.
decompose [and] H1; clear H1.
decompose [and] H2; clear H2.
decompose [and] H3; clear H3.
elim H4;clear H4.
intro P.
intros.
decompose [and] H3;clear H3.
assert (HC:rk (quadruple A B C D) >= 3 \/ rk (quadruple A B C D) < 3).
omega.
elim HC;intro HABCD;clear HC.

apply (pasch A2 B2 A3 B3).

assert(rk (union (singleton P) (quadruple A0 B0 A1 B1)) <= 3).
apply (intersecting_lines_rank_3 A0 B0 A1 B1 P);omega.
assert (rk (quadruple A0 B0 A1 B1) <= 3).
cut (rk (quadruple A0 B0 A1 B1) <=  rk (union (singleton P) (quadruple A0 B0 A1 B1))).
omega.
apply matroid2; (clear_all; fsetdecide).

assert (rk (couple A0 B0) = 2).
apply rk_couple1;auto.
assert (rk (couple A1 B1) = 2).
apply rk_couple1;auto.
assert (rk (couple A2 B2) = 2).
apply rk_couple1;auto.
assert (rk (couple A3 B3) = 2).
apply rk_couple1;auto.

assert (rk (union (quadruple A0 B0 A1 B1) (triple A0 B0 A)) + rk (couple A0 B0) <=
           rk (quadruple A0 B0 A1 B1) + rk (triple A0 B0 A)).
apply (matroid3_useful (quadruple A0 B0 A1 B1) (triple A0 B0 A) (couple A0 B0)).
(clear_all; fsetdecide).

assert (rk (union (quadruple A0 B0 A1 B1) (triple A0 B0 A))  <= 3).
omega.
clear H20.
assert (rk
         (union (union (quadruple A0 B0 A1 B1) (triple A0 B0 A))
            (triple A1 B1 C)) + rk (couple A1 B1) <=
       rk (union (quadruple A0 B0 A1 B1) (triple A0 B0 A)) +
       rk (triple A1 B1 C)).
apply (matroid3_useful (union (quadruple A0 B0 A1 B1) (triple A0 B0 A))
 (triple A1 B1 C) (couple A1 B1)).
(clear_all; fsetdecide).
assert (rk
        (union (union (quadruple A0 B0 A1 B1) (triple A0 B0 A))
           (triple A1 B1 C)) <= 3).
omega.
clear H20 H21.
setoid_replace (union (union (quadruple A0 B0 A1 B1) (triple A0 B0 A))
           (triple A1 B1 C)) with (union (quadruple A0 B0 A1 B1) (couple A C)) in H22 by fsetdecide.
assert (rk
         (union (union (quadruple A0 B0 A1 B1) (couple A C)) (triple A0 B0 B)) +
       rk (couple A0 B0) <=
       rk (union (quadruple A0 B0 A1 B1) (couple A C)) +
       rk (triple A0 B0 B)).
apply (matroid3_useful (union (quadruple A0 B0 A1 B1) (couple A C))
(triple A0 B0 B) (couple A0 B0)).
(clear_all; fsetdecide).
assert ( rk
        (union (union (quadruple A0 B0 A1 B1) (couple A C)) (triple A0 B0 B)) <= 3).
omega.
clear H20.
assert (rk
         (union
            (union (union (quadruple A0 B0 A1 B1) (couple A C))
               (triple A0 B0 B)) (triple A1 B1 D)) + rk (couple A1 B1) <=
       rk
         (union (union (quadruple A0 B0 A1 B1) (couple A C)) (triple A0 B0 B)) +
       rk (triple A1 B1 D)).
apply (matroid3_useful  (union (union (quadruple A0 B0 A1 B1) (couple A C)) (triple A0 B0 B)) 
(triple A1 B1 D) (couple A1 B1)).
(clear_all; fsetdecide).
assert ( rk
        (union
           (union (union (quadruple A0 B0 A1 B1) (couple A C))
              (triple A0 B0 B)) (triple A1 B1 D)) <= 3).
omega.
clear H20 H21 H22.
assert (rk (quadruple A B C D) <= 3).
cut (rk (quadruple A B C D) <= rk
        (union
           (union (union (quadruple A0 B0 A1 B1) (couple A C))
              (triple A0 B0 B)) (triple A1 B1 D)) ).
omega.
apply matroid2;(clear_all; fsetdecide).
clear H23.
assert (rk (quadruple A B C D) = 3).
omega.

assert (rk (quadruple A2 B2 A C) = 2).
apply rk_lemma_1;auto.
assert (rk (quadruple A3 B3 B D) = 2).
apply rk_lemma_1;auto.

unfold dist4 in H.
decompose [and] H.
assert (rk (couple A C) =2).
apply rk_couple1;auto.
assert (rk (couple A D) =2).
apply rk_couple1;auto.
assert (rk (couple B C) =2).
apply rk_couple1;auto.
assert (rk (couple B D) =2).
apply rk_couple1;auto.

assert (rk (union (quadruple A2 B2 A C) (quadruple A B C D)) +
            rk (couple A C) <=
           rk (quadruple A2 B2 A C) + rk (quadruple A B C D)).
apply (matroid3_useful (quadruple A2 B2 A C) (quadruple A B C D) (couple A C)).
(clear_all; fsetdecide).
assert (rk (union (quadruple A2 B2 A C) (quadruple A B C D)) <= 3).
omega.
clear H34.
assert (rk (union (quadruple A3 B3 B D) (quadruple A B C D)) +
            rk (couple B D) <=
           rk (quadruple A3 B3 B D) + rk (quadruple A B C D)).
apply (matroid3_useful (quadruple A3 B3 B D) (quadruple A B C D) (couple B D)).
(clear_all; fsetdecide).
assert ( rk (union (quadruple A3 B3 B D) (quadruple A B C D))  <= 3).
omega.
clear H34.
assert (rk
         (union (union (quadruple A2 B2 A C) (quadruple A B C D))
            (union (quadruple A3 B3 B D) (quadruple A B C D))) +
       rk (quadruple A B C D) <=
       rk (union (quadruple A2 B2 A C) (quadruple A B C D)) +
       rk (union (quadruple A3 B3 B D) (quadruple A B C D))).
apply (matroid3_useful (union (quadruple A2 B2 A C) (quadruple A B C D))).
(clear_all; fsetdecide).
assert (rk
        (union (union (quadruple A2 B2 A C) (quadruple A B C D))
           (union (quadruple A3 B3 B D) (quadruple A B C D))) <= 3).
omega.
cut (rk (quadruple A2 B2 A3 B3) <=  rk
        (union (union (quadruple A2 B2 A C) (quadruple A B C D))
           (union (quadruple A3 B3 B D) (quadruple A B C D)))).
omega.
apply matroid2.
(clear_all; fsetdecide).

exists A2.
split.
setoid_replace (triple A2  B2 A2) with (couple A2 B2) by (clear_all; fsetdecide).
apply rk_couple1;auto.
assert (rk (quadruple A B C D) = 2).
apply le_antisym.
omega.
unfold dist4 in H.
assert (rk (couple A B) =2).
apply rk_couple1;intuition.
rewrite <- H3.
apply matroid2.
(clear_all; fsetdecide).

assert (rk (couple A0 B0) = 2).
apply rk_couple1;auto.
assert (rk (couple A1 B1) = 2).
apply rk_couple1;auto.
assert (rk (couple A2 B2) = 2).
apply rk_couple1;auto.
assert (rk (couple A3 B3) = 2).
apply rk_couple1;auto.

assert (rk (quadruple A2 B2 A C) = 2).
apply rk_lemma_1;auto.
assert (rk (quadruple A3 B3 B D) = 2).
apply rk_lemma_1;auto.

unfold dist4 in H.
decompose [and] H.
assert (rk (couple A C) =2).
apply rk_couple1;auto.
assert (rk (couple A D) =2).
apply rk_couple1;auto.
assert (rk (couple B C) =2).
apply rk_couple1;auto.
assert (rk (couple B D) =2).
apply rk_couple1;auto.

assert (rk (union (quadruple A3 B3 B D) (quadruple A B C D)) +
       rk (couple B D) <=
       rk (quadruple A3 B3 B D) + rk (quadruple A B C D)).
apply (matroid3_useful (quadruple A3 B3 B D) (quadruple A B C D) (couple B D)).
(clear_all; fsetdecide).
assert ( rk (union (quadruple A3 B3 B D) (quadruple A B C D)) <= 2).
omega.
clear H31.

assert (rk
         (union (union (quadruple A3 B3 B D) (quadruple A B C D))
            (quadruple A2 B2 A C)) + rk (couple A C) <=
       rk (union (quadruple A3 B3 B D) (quadruple A B C D)) +
       rk (quadruple A2 B2 A C)).
apply matroid3_useful.
(clear_all; fsetdecide).
assert ( rk
        (union (union (quadruple A3 B3 B D) (quadruple A B C D))
           (quadruple A2 B2 A C)) <= 2).
omega.
clear H31.
apply le_antisym.
cut (rk (triple A3 B3 A2)  <=  rk
        (union (union (quadruple A3 B3 B D) (quadruple A B C D))
           (quadruple A2 B2 A C))).
omega.
apply matroid2.
unfold Subset; intros; fsetdecide.
rewrite <- H18.
apply matroid2.
(clear_all; fsetdecide).
Qed.

(* A3 : dimension-related axioms *)

Lemma a3_1 : 
  forall l:Line,exists A:Point, exists B:Point, exists C:Point, 
 dist3  A B C/\Incid A l /\Incid B l /\ Incid C l.
Proof.
intros.
induction l.
exists A.
exists B.
elim (three_points_on_lines A B).
intro C.
intros.
exists C.
unfold Incid.
simpl.
setoid_replace (triple A B A) with (couple A B) by (clear_all; fsetdecide).
setoid_replace (triple A B B) with (couple A B) by (clear_all; fsetdecide).
assert (rk (couple A B) = 2).
apply rk_couple1;auto.
intuition.
unfold dist3.
repeat split.
auto.
apply couple_rk1;auto.
apply couple_rk1;auto.
Qed.



Lemma a3_2 (* dim >= 3 *) : exists l1:Line, exists l2:Line, forall p:Point, ~(Incid p l1/\Incid p l2).
Proof.
exists (Cline P0 P1 base_points_distinct_1).
exists (Cline P2 P3 base_points_distinct_2).
intros.
unfold Incid.
simpl.
unfold not;intro.
decompose [and] H; clear H.
assert (rk (union (triple P0 P1 p) (triple P2 P3 p)) + rk (singleton p) <=
           rk (triple P0 P1 p) + rk (triple P2 P3 p)).
apply matroid3_useful.
(clear_all; fsetdecide).
rewrite rk_singleton in H.
assert (rk (union (triple P0 P1 p) (triple P2 P3 p)) <= 3).
omega.
clear H.
assert (rk (quadruple P0 P1 P2 P3) <= 3).
cut (rk (quadruple P0 P1 P2 P3) <= rk (union (triple P0 P1 p) (triple P2 P3 p)) ).
omega.
apply matroid2.
(clear_all; fsetdecide).
assert (T:=lower_dim).
omega.
Qed.

End RankProjectiveSpaceToProjectiveSpaceOrHigher.

