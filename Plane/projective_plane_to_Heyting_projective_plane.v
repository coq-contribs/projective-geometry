Require Import decidability.
Require Import Heyting_projective_plane_axioms.
Require Import Classical.
Require Import forth.
Require Import basic_facts_plane.

Module ProjectivePlane2HeytingProjectivePlane (M:ProjectivePlane) <: HeytingProjectivePlane
 with Definition Point := M.Point
 with Definition Line := M.Line
 with Definition Incid := M.Incid.

Definition Point := M.Point.
Definition Line := M.Line.
Definition Incid := M.Incid.

Module Export uniq := uniqueness_axioms M.

Definition Apart : Point -> Point -> Prop := fun A B => A <> B.

Notation "x # y" := (Apart x y) (at level 20).
Notation "x @ y" := (Incid x y) (at level 20).

Definition out (A : Point) (l : Line) : Prop := forall B, B @ l -> B # A.
Definition apart_l  (l m : Line) : Prop := exists A, A @ l /\ out A m. 

Notation "x ## y" := (apart_l x y) (at level 20).

(** %\textbf{% Apartness axioms. %}% *)

Lemma S1 : forall A B, A # B -> B # A.
Proof.
intros.
unfold Apart in *.
auto.
Qed.



Lemma S2 : forall A B, ~ A # B <-> A=B.
Proof.
intros.
unfold Apart.
intuition.
apply NNPP.
tauto.
Qed.

Hint Extern 4 (?X1 = ?X2) => subst.

Lemma S3 : forall A B, A # B -> forall C, C # A \/ C # B.
Proof.
intros.
unfold Apart in *.
classical_left.
intuition.
Qed.

(** %\textbf{% Geometric axioms. %}% *)

Lemma P1 : forall A B,  A # B -> exists l, A @ l /\ B @ l.
Proof.
intros.
elim (M.a1_exist A B); intro l; intro H2.
exists l;auto.
Qed.

Lemma P2 : forall A B l m, A # B /\ A @ l /\ A @ m /\ B @ l /\ B @ m -> l=m.
Proof.
intros.
apply (a1_unique A B l m);intuition.
Qed.

Hint Unfold out.

Lemma P3 : forall l m, l ## m -> exists A, A @ l /\ A @ m.
Proof.
intros.
unfold apart_l in *.
elim H; intro A; clear H; intro H.
assert (l<>m).
  unfold not;intro;intuition.
  subst l.
  unfold out in *.
  apply H2 in H1.
  auto.
elim (M.a2_exist l m); intros x Hx.
exists x;auto.
Qed.

Lemma P4 : forall A B C l m, A # B /\ A @ l /\ B @ l /\ 
       out C l /\ A @ m /\ C @ m -> out B m.
Proof.
intros.
unfold out.
intros.
unfold not;intro.
subst B.
intuition.
unfold out in *.
assert (l=m).
eapply P2;eauto.
subst.
apply H3 in H6.
auto.
Qed.

Lemma P5i :exists A, exists B, A # B.
Proof.
assert (T:=M.a3).
destruct T as [A [B [C [D T]]]].
elim (M.a1_exist A B); intros l H.
assert (U:=T l);clear T.
decompose [and] U; clear U.
unfold dist4 in H0.
exists A; exists B;intuition.
Qed.

(** This axiom is our a3_1 so we can use our forth functor *)

Module M' := forth.forth M.

Lemma P5ii: forall l, exists A, exists B, exists C, 
        A @ l /\ B @ l /\ C @  l /\ A # B /\ A # C /\ B # C.
Proof.
intro l.
assert (T:=M'.a3_1 l).
destruct T as [A [ B [ C [H1 H2]]]].
exists A.
exists B.
exists C.
unfold Apart, dist3 in *.
intuition.
Qed.

Module Export Facts := decidability.decidability M.

Lemma P5iii: forall l, exists A, out A l.
Proof.
intros.
elim (Facts.outsider l l); intros P H.
exists P.
unfold out.
intros.
unfold Apart.
intuition.
subst B.
intuition.
Qed.

End ProjectivePlane2HeytingProjectivePlane.
