Require Export projective_space_axioms.
Require Setoid.

(* We derive some lemmas needed to show decidability of equality *)
(*
Module Type MoreProjectiveSpace.

Parameter Line : Type.
Parameter Point : Type.
Parameter Incid : Point -> Line -> Prop.
 
Axiom incidABl : forall (A B:Point)(l:Line), ~Incid A l /\ Incid B l -> A <> B.
Axiom incidAl1l2 : forall (l1 l2:Line)(A:Point), ~Incid A l1 /\ Incid A l2 -> l2 <> l1.
Axiom a1_unique : forall (A B :Point)(l1 l2:Line),
  A<>B -> Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> l1=l2.
Axiom a2_unique : forall(l1 l2 :Line)(A B :Point),
  l1<>l2 -> Incid A l1 -> Incid A l2 -> Incid B l1 -> Incid B l2 -> A = B.
Axiom eq_line_dec : forall d1 d2 : Line, d1 = d2\/d1 <> d2.
Axiom eq_point_dec : forall A B: Point, A = B\/A <> B.

Axiom second_point : forall A:Point, forall l:Line, Incid A l -> exists B : Point, (B<>A)/\(Incid B l).

End MoreProjectiveSpace.
*)

Module ProjectiveSpaceFacts (DecPoints: FSetInterface.WS) (M: ProjectiveSpace DecPoints). 

(*: MoreProjectiveSpace 
 with Definition Line:=M.Line 
with Definition Point:= M.Point
with Definition Incid := M.Incid.
*)

Definition Line:=M.Line.
Definition Point:= M.Point.
Definition Incid := M.Incid.

Import M. (* to avoid qualified names *)

Lemma incidABl : forall (A B:Point)(l:Line), ~Incid A l /\ Incid B l -> A <> B.
intros A B l H HAB.
subst A.
tauto.
Qed.

Hint Resolve incidABl : incidence.

Lemma incidAl1l2 : forall (l1 l2:Line)(A:Point), ~Incid A l1 /\ Incid A l2 -> l2 <> l1.
intros l1 l2 A H Hl2l1. 
subst l1.
tauto.
Qed.

Hint Resolve incidAl1l2 : incidence.

Lemma a1_unique : forall (A B :Point)(l1 l2:Line),
  ~ A [==] B -> Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> l1=l2.
intros.
assert (A[==]B\/l1=l2).
eapply uniqueness; intuition.
intuition.
Qed.

Lemma a2_unique : forall(l1 l2 :Line)(A B :Point),
  l1<>l2 -> Incid A l1 -> Incid A l2 -> Incid B l1 -> Incid B l2 -> A [==] B.
intros.
assert (A [==] B\/l1=l2).
eapply uniqueness; intuition.
intuition.
Qed.

Lemma eq_line_dec :  
  forall d1 d2 : Line, d1 = d2\/d1 <> d2.
generalize a3_1 a3_2.
intros Hsa31' Hsa32'.
intros l1 l2.
elim (Hsa31' l1).
intros M HM; elim HM; clear HM; intros N HN; elim HN; clear HN; intros P HMNP.
elim (incid_dec M l2).
intros HMl2; elim (incid_dec N l2).
intros HNl2.
left.
decompose [and] HMNP.
assert ((N [==] M)\/(l1=l2)).
apply uniqueness; intuition.
assert (~ N [==] M).
unfold dist3 in *.
decompose [and] H.
intro.
apply H4.
apply DecPoints.eq_sym.
auto.
intuition.

intro.
right.
apply incidAl1l2 with (A:=N).
intuition.
intro.
right.
apply incidAl1l2 with (A:=M); intuition.
Qed.

Lemma two_lines_aux : 
  forall P, forall l, ~Incid P l -> exists m:Line, exists n:Line, m<>n /\ Incid P m /\ Incid P n.
generalize a3_1 a3_2 a3_3.
intros H1 H2 H3.
intros P l HPl.
elim (H1 l).
intros A HA; elim HA; clear HA; intros B HB; elim HB; clear HB; intros C HC.
elim (a1_exists P A).
intros l1 Hl1.
elim (a1_exists P B).
intros l2 Hl2.
exists l1.
exists l2.
intuition.
subst.
assert ((A [==] B)\/l2=l).
apply uniqueness; intuition.
case H9.
intro.
unfold dist3 in *;  intuition.
intro.
subst;
intuition.
Qed.

Lemma two_lines_P : forall P:Point, exists l1:Line, exists l2:Line, l1<>l2/\Incid P l1/\Incid P l2.
generalize a3_3 a3_2 a3_1.
intros H1 H2 H3.
intros P.
elim H2; intros l1 Hl1; elim Hl1; clear Hl1; intros l2 Hl2.
elim (incid_dec P l1).
intros.
elim (incid_dec P l2).
intros.
assert False.
apply (Hl2 P); intuition.
intuition.
intros HPl2.
eapply two_lines_aux; eauto with incidence.
intros HPl2.
eapply two_lines_aux; eauto with incidence.
Qed.

Lemma only_one_intersection : forall l1 l2:Line, forall B C:Point,Incid C l1 /\ ~Incid C l2 /\ Incid B l2 /\ ~Incid B l1 ->
exists l3:Line,   l1 <>l3 /\ l2 <> l3/\ (Intersect l3 l1) /\(Intersect l3 l2).
Proof.
intros l1 l2 B C (HCl1,(HCl2,( HBl2, HBl1))).
elim (a1_exists B C).
intros l (HBl, HCl).
exists l.
split.
intro; subst; intuition.
split.
intro;subst;intuition.
unfold Intersect; firstorder.
Qed.

Lemma two_points_not_incident_l1l2 : 
forall l1 l2:Line, l1<>l2 -> exists B, 
(Incid B l1 /\ ~Incid B l2) /\ exists C, 
(~Incid C l1 /\ Incid C l2).
Proof.
intros l1 l2 Hl1l2.
elim (a3_1 l1); intros A1 HA1; elim HA1; clear HA1; intros B1 HB1; elim HB1; clear HB1; intros C1 Hl1.
elim (a3_1 l2); intros A2 HA2; elim HA2; clear HA2; intros B2 HB2; elim HB2; clear HB2; intros C2 Hl2.
elim (incid_dec A1 l2).
intros.
assert (~Incid B1 l2).
intro.
assert (A1 [==] B1).
apply a2_unique with (l1:=l1) (l2:=l2); intuition.
unfold dist3 in *;intuition.
elim (incid_dec A2 l1).
intros.
assert (~Incid B2 l1).
intro.
assert (A2 [==] B2).
apply a2_unique with (l1:=l1) (l2:=l2); intuition.
unfold dist3 in *;intuition.
firstorder.

intro.

firstorder.
intro.
exists A1.
firstorder.

elim (incid_dec A2 l1).
intros HA2l1.
assert (~Incid B2 l1).
intro.
assert (A2 [==] B2).
apply a2_unique with (l1:=l1) (l2:=l2); intuition.
unfold dist3 in *;intuition.
firstorder.
intros HA2l1.
firstorder.
Qed.

Lemma third_line : forall l1 l2:Line, 
exists l3 :Line,  l1 <>l3 /\ l2 <> l3/\ (Intersect l3 l1) /\(Intersect l3 l2).
Proof.
intros l1 l2.
elim (eq_line_dec l1 l2).
intro; subst.
elim (a3_1 l2); intros A2 HA2; elim HA2; clear HA2; intros B2 HB2; elim HB2; clear HB2; intros C2 Hl2.
elim (two_lines_P A2).
intros d1 Hd1; elim Hd1; intros d2 Hd.
elim (eq_line_dec l2 d1).
intro; subst.
exists d2.
unfold Intersect in *; firstorder.
intro; subst.
exists d1.
unfold Intersect in *; firstorder.
intros Hl1l2.
elim (two_points_not_incident_l1l2 l1 l2 Hl1l2).
intros A (HA, Hex).
elim Hex; intros B HB. 
apply (only_one_intersection l1 l2 B A).
intuition.
Qed.

Lemma a3_3simplified : forall l1 l2:Line, exists l3 :Line, l1 <>l3 /\ l2 <> l3.
Proof.
intros l1 l2; elim (third_line l1 l2).
intros l H; elim H; intros A HA; elim HA; intros B HB.
exists l; intuition.
Qed.

Lemma second_line : forall l1 : Line, exists l2:Line, l1<>l2.
Proof.
intros l1.
elim a3_2.
intros d1 H; elim H; intros d2 H'.
elim (third_line l1 d2).
intros d (Hd1, (Hd2, (HexI, HexJ))).
exists d.
intuition.
Qed.

Lemma second_point : forall A:Point, forall l:Line, Incid A l -> exists B : Point, (~ B [==]A)/\(Incid B l).
Proof.
intros A l HAl.
elim (a3_1 l).
intros P1 H.
elim H; intros P2 H'.
elim H'; intros P3 H''.
elim (DecPoints.eq_dec A P1).
intros HAP1.
exists P2.
unfold dist3 in *.
intuition.
apply H2.
apply DecPoints.eq_trans with (s':=A).
apply DecPoints.eq_sym.
assumption.
apply DecPoints.eq_sym.
assumption.
intros Hnew.
exists P1.
intuition.
apply Hnew.
apply DecPoints.eq_sym.
assumption.
Qed.

Export Setoid.

Add Parametric Relation : (Point) (DecPoints.eq)
  reflexivity proved by DecPoints.eq_refl
  symmetry proved by DecPoints.eq_sym
  transitivity proved by DecPoints.eq_trans
as PointsEqSetoid .

Axiom Incid_mor : 
forall x y : Point, x[==]y -> forall y0 : Line, Incid x y0 <-> Incid y y0.


Add Parametric Morphism (Point:Type) : Incid 
with signature (DecPoints.eq ) ==> eq ==> iff  as incid_mor.
Proof.
apply Incid_mor.
Qed.

Lemma third_point : forall A B:Point, forall l:Line, 
 ~ A [==]B /\ 
   Incid A l/\Incid B l -> 
exists C:Point, dist3 A B C/\Incid C l.
Proof.
intros A B l HABl.
elim (a3_1 l).
intros P1 H.
elim H; intros P2 H'.
elim H'; intros P3 H''.
clear H H'.
elim (DecPoints.eq_dec A P1).
intros HAP1.

decompose [and] H''.
unfold dist3 in *.
setoid_rewrite <- HAP1 in H.

elim (DecPoints.eq_dec B P2).
intros HBP2.
setoid_rewrite <- HBP2 in H.
exists P3.
unfold dist3 in *; intuition.
intros HBP2.
exists P2.
unfold dist3 in *; intuition.
intros HBP2.
decompose [and] HABl; clear HABl.
decompose [and] H''; clear H''.
unfold dist3 in H0.
decompose [and] H0;clear H0.


elim (DecPoints.eq_dec B P1).
intros HBP1.
elim (DecPoints.eq_dec A P2).
intros.
exists P3.
unfold dist3.
rewrite HBP1 in *.
rewrite a in *.
intuition.

intros HAP2.
rewrite HBP1 in *.

elim (DecPoints.eq_dec B P2).
intros.
rewrite a in *.
cut False;
intuition.


exists P2.
unfold dist3 in *; intuition.
apply H.
rewrite H0.
assumption.
intros HBP1.

exists P1.
unfold dist3 in *;intuition.
Qed.

End ProjectiveSpaceFacts.




