Require Export decidability.

(** Duality **)

Module swap (M': ProjectivePlane') <: ProjectivePlane'.

Definition Point := M'.Line.
Definition Line := M'.Point.

Definition Incid := fun (x:Point) (y:Line) => M'.Incid y x.
Definition incid_dec : forall (A : Point) (l : Line), {Incid A l} + {~ Incid A l}.
Proof.
unfold Incid.
intros.
apply M'.incid_dec.
Qed.

Definition a1_exist := M'.a2_exist.
Definition a2_exist := M'.a1_exist.

Lemma uniqueness : forall A B :Point, forall l m : Line,
Incid A l -> Incid B l  -> Incid A m -> Incid B m -> A=B\/l=m.
intros.
unfold Point, Line, Incid in *.
assert ((l=m)\/(A=B)).
apply M'.uniqueness; assumption.
intuition.
Qed.

Require Export back.
Module M := back.back M'.
Module ProjectivePlaneFacts_m := decidability.decidability M.

Module uniq := uniqueness_axioms M'.

Ltac Apply_unicity := match goal with
H1: ?A <> ?B, H2: ?Incid ?A ?l, H3: ?Incid ?B ?l, H4 : ?Incid ?A ?m, H5: ?Incid ?B ?m |- _ =>
let id:= fresh in assert (id: l=m); try apply (uniq.a1_unique A B l m H1 H2 H3 H4 H5);subst l
| H1: ?l <> ?m, H2: ?Incid ?A ?l, H3: ?Incid ?A ?m, H4 : ?Incid ?B ?l, H5: ?Incid ?B ?m |- _ =>
let id:= fresh in assert (id: A=B); try apply (uniq.a2_unique l m A B H1 H2 H3 H4 H5);subst A
end.

Ltac Collapse := repeat (Apply_unicity; CleanDuplicatedHyps).

Ltac line_through l A B Ha Hb := elim (M'.a1_exist A B); intros l [Ha Hb].


Lemma a3_1_aux :
  forall (P: Point) (l:Line),
  ~ Incid P l -> {A:Point & {B:Point & {C:Point |
 (dist3 A B C/\Incid A l /\Incid B l /\ Incid C l)}}}.
Proof.
intro l1.
intro P.
intro Hincid.

elim (M'.a3_1 l1).
intros A HA; elim HA.
intros B HB; elim HB.
intros C (Hz1,(Hz2,(Hz3,Hz4))); clear HA HB.

line_through m1 P A Hm1A Hm1B.
line_through m2 P B Hm2A Hm2B.
line_through m3 P C Hm3A Hm3B.
exists m1.
exists m2.
exists m3.

split.
2:intuition.
unfold dist3.
split.
intros Hm1m2.
subst m1.
assert (A=B).
assert (m2<>l1).
intro Hm2l1.
subst m2.
intuition.

apply (uniq.a2_unique m2 l1 A B H) ; intuition.
subst A.
unfold dist3 in Hz1; intuition.

split.

intros Hm1m2.
subst m1.
assert (A=C).
assert (m3<>l1).
intro Hm3l1.
subst.
intuition.

apply (uniq.a2_unique m3 l1 A C H) ; intuition.
subst.
unfold dist3 in Hz1; intuition.

intros Hm1m2.
subst.
assert (B=C).
assert (m3<>l1).
intro Hm3l1.
subst.
intuition.

apply (uniq.a2_unique m3 l1 B C H) ; intuition.
subst.
unfold dist3 in Hz1; intuition.
Qed.

Definition a3_1: 
 forall l:Line,{A:Point & {B:Point & {C:Point |
 (dist3 A B C/\Incid A l /\Incid B l /\ Incid C l)}}}.
(** Using a3_2, we build two lines l1 and l2.
The we perform case distinction on Incid P l1 and Indic P l2 
If P does not belong to l1 or l2 we use the previous lemma.
Othewise P belongs to l1 and l2, we use the outsider lemma.
*)

(*
unfold Line, Point, Incid.
*)

elim M'.a3_2 ; intros l1 Hl1.
elim Hl1; intros l2 Hl2; clear Hl1.

intros P.
elim (M'.incid_dec P l1);intros HMl1.
elim (M'.incid_dec P l2);intros HMl2.

(** Case P is at the intersections of l1 and l2 **)

exists l1.
exists l2.

elim (ProjectivePlaneFacts_m.outsider l1 l2).

intros K (HK1, HK2).

line_through m P K Hm1 Hm2.
exists m.

unfold dist3.
unfold ProjectivePlaneFacts_m.Incid in *.
unfold M.Incid in *.
intuition;subst;intuition.

(** Case P is not on l2 *)

apply (a3_1_aux) with (P:=l2);assumption.

(** Case P is not on l1 *)
apply (a3_1_aux) with (P:=l1);assumption.
Qed.

Definition a3_2 : {l1:Line & {l2:Line | l1 <> l2}}.
generalize M'.a3_2  M'.a3_1.
intros H1 H2.
elim H1.
intro l.
intro Hl2.
elim (H2 l).
intros P H';elim H'.
intro Q.
intros.
elim p.
intros x (H1', (H2', (H3', H4'))).
exists P.
exists Q.
unfold dist3 in H1'; tauto.
Qed.

End swap.

Module example (M': ProjectivePlane').

Module Swaped := swap M'.
Export M'.

Lemma dual_example : 
forall P : Point,
       {l1 : Line & 
       {l2 : Line & 
       {l3 : Line |
       dist3 l1 l2 l3 /\
       Incid P l1 /\ Incid P l2 /\ Incid P l3}}}.
Proof.
apply Swaped.a3_1.
Qed.

End example.
