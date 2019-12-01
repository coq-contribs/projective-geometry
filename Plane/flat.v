Require Export Arith.
Require Export projective_plane_inst.
Require Export Classical.
Require Export Ensembles.

Arguments  Included : default implicits.
Arguments In : default implicits.


Export AbstractProjectivePlane.
Export AbstractProjectivePlane'.
Module Export uniq := (uniqueness_axioms AbstractProjectivePlane).
Module Export decid := (decidability.decidability AbstractProjectivePlane).

(* flat property *)
Definition pset := Ensemble Point.

Definition pempty : pset := fun (x:Point) => False.
Definition pplane : pset := fun (x:Point) => True.
Definition psingleton (x:Point) : pset := fun (y:Point) => if (eq_point_dec x y) then True else False.
Definition pline (l:Line) : pset :=fun (x:Point) => (if incid_dec x l then True else False).

Definition flat (v:pset) : Prop := 
  forall A B:Point, v A -> v B -> A<>B ->
    forall l:Line, Incid A l -> Incid B l -> 
      forall C:Point, Incid C l -> v C.

(* the empty set is a flat *)
Lemma fp_empty : flat (pempty).
unfold flat, pempty.
intros; tauto.
Qed.

(* the whole plane is a flat *)
Lemma fp_plane :  flat (pplane). 
unfold flat, pplane.
tauto.
Qed.

(* singleton points are flats *)
Lemma fp_singleton : forall x:Point, flat (psingleton x). 
intros X; unfold flat,psingleton.
intros A B.
elim (eq_point_dec X A).
elim (eq_point_dec X B).
intros HXB HXA Ht1 Ht2 HAB l HAl HBl C HCl.
elim (eq_point_dec X C).
tauto.
intros HCX.
subst A.
subst B.
apply HAB; trivial.
tauto.
elim (eq_point_dec X B).
tauto.
tauto.
Qed.

(* lines are flats *)
Lemma fp_line : forall l:Line, flat (pline l).
intros l.
unfold pline, flat.
intros A B.
elim (incid_dec A l).
elim (incid_dec B l).
intros HAl HBl Ht1 Ht2 HAB.
intros l0 HAl0 HBl0.
assert (l=l0).
apply (a1_unique A B l l0 HAB); assumption.
subst l0.
intros C HCl.
elim (incid_dec C l).
trivial.
intros Hf; apply Hf; assumption.
tauto.
tauto.
Qed.

(* characterization *)

(* decomposition requires excluded middle *)
Lemma set01 : forall v:pset, (exists x:Point, v(x)) \/ forall x:Point, ~v(x).
intros v.
elim (classic (exists x:Point, v(x))).
intros; left; intuition.
intros H; right.
intros x Hx.
apply H.
exists x.
assumption.
Qed.

Lemma set12 : forall v:pset, (exists x:Point, v(x)) -> 
(exists a :Point, exists b:Point, a<>b/\v(a)/\v(b))\/(exists w:Point, v(w)/\forall p:Point, p<>w -> ~v(p)).
intros v H.
elim H; intros v1 Hv1; clear H.
elim (classic (forall p:Point, p<>v1 -> ~v(p))).
intros Hc.
right.
exists v1.
intuition.
intros Hc.
left.
exists v1.
apply not_all_not_ex.
intros H.
apply Hc.
intros p Hpv1.
generalize (H p).
intuition.
Qed.

(* either zero, one or at least 2 points in v *)

Lemma pset_decompose : 
forall v:pset, 
(forall x:Point, ~(v x))
\/(exists y:Point, v y /\ forall x:Point, x<>y -> ~v x)
\/(exists z :Point, exists t : Point, z <> t /\ v z /\ v t).
intros v.
elim (set01 v).
intros H.
elim (set12 v H).
intros H'.
right;right.
assumption.
intros H''.
right;left.
assumption.
intros H''.
left.
assumption.
Qed.


(* either v is included in w or there exists p in v and not in w *)
Lemma included_or_not : forall v w: pset,
(forall p:Point, v(p) -> w(p))\/(exists p:Point, v(p)/\~ w(p)).
intros v w.
elim (classic (forall p : Point, v p -> w p)).
intros; left; intuition.
intros;right.
apply not_all_not_ex.
intros H'.
apply H.
intros p Hvp.
elim  (not_and_or (v p) (~ w p) (H' p)).
intros H2; cut False.
intros Hf; elim Hf.
apply H2; assumption.
intros Hnotnot.
elim (classic (w p)).
intuition.
intros Hmagic.
elim (Hnotnot Hmagic).
Qed.


(* "en dim 2, les seuls plats sont : l'ensemble vide, les points (singletons), les droites (d:M | Incid M d) et le plan entier" *)

Lemma characterization : forall v:pset, flat v -> 
(forall x:Point, (v x)<->(pempty x))
\/ (exists y:Point, forall x:Point, ((v x) <-> ((psingleton y) x))) 
\/   (exists l:Line, forall x:Point, ((v x) <-> ((pline l) x)))
\/ (forall x:Point, (v x) <-> (pplane x)).
intros v Hflat.
unfold flat in Hflat.
elim (pset_decompose v).
(* empty set *)
intros Hempty.
left.
unfold pempty.
intros x; split.
apply Hempty.
intuition.
intros Helim; elim Helim.
(* singleton *)
intros Hsingleton.
right; left.
elim Hsingleton.
intros wit [Hwit1 Hwit2].
unfold psingleton.
exists wit.
intros x; split.
generalize Hwit1 Hwit2; case (eq_point_dec wit x).
intros Hwitx; subst wit.
intuition.
intros Hwitx Hvwit Hforall Hvx0.
assert (x <> wit) by intuition.
exact (Hwit2 x H Hvx0).
generalize Hwit1 Hwit2; case (eq_point_dec wit x).
intros H; subst x.
intuition.
intuition.
clear Helim; intros Hatleast2.
(* at least 2 elements *) 
elim Hatleast2; intros A H'; elim H'; clear H'.
intros B.
(* a line *)
intros [ HnAB [HvA HvB]].
elim (a1_exist A B).
intros l [ HAl HBl ].
(* at least 2 points in v : all on the same line or one outside of this line *)
elim (included_or_not v (fun p => Incid p l)).
(* every single point belongs to l *)
intros H.
right;right;left.
exists l.
unfold pline.
intros x; elim (incid_dec x l).
intros Hxl.
split.
intuition.
intros Htrue.
eapply Hflat with (A:=A) (B:=B) (l:=l); assumption.
intros Hnxl.
split.
intros Hvx.
elim (Hnxl (H x Hvx)).
intros Hf; elim Hf.
(* one pt of v does not belong to l *) 
intros H.
elim H; intros q [Hvq Hiq].
right;right;right.
intros x; unfold pplane.
split.
intuition.
intros Htrue.
elim (incid_dec x l).
intros Hxl.
eapply Hflat with (A:=A) (B:=B) (l:=l); intuition.
intros Hxl.
elim (a1_exist q x).
intros l' [Hql' Hxl'].
elim (a2_exist l l').
intros I (HI1, HI2).
assert (HvI : v(I)).
apply Hflat with (A:=A) (B:=B) (l:=l); intuition.
elim (eq_point_dec I q).
intros HIq.
subst q.
assert (Hf:False).
apply Hiq; assumption.
elim Hf.
intros HIq.
apply Hflat with (A:=I) (B:=q) (l:=l'); intuition.
Qed.

 
