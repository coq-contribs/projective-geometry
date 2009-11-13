Require Export projective_plane_axioms.

Module uniqueness_axioms (M:PreProjectivePlane) : PreProjectivePlane2
with Definition Point := M.Point
with Definition Line := M.Line
with Definition Incid := M.Incid.

Definition Point := M.Point.
Definition Line := M.Line.
Definition Incid := M.Incid.

Definition incid_dec := M.incid_dec.
Definition a1_exist := M.a1_exist.
Definition a2_exist := M.a2_exist.
Definition uniqueness := M.uniqueness.

Lemma a1_unique:forall (A B :Point)(l1 l2:Line),
  A<>B -> Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> l1=l2.
Proof.
intros A B l1 l2 HAB HAl1 HBl1 HAl2 HBl2.
assert ((A=B)\/(l1=l2)).
apply uniqueness; intuition.
intuition.
Qed.

Lemma a2_unique : forall(l m :Line)(A B :Point), 
  l<>m -> Incid A l -> Incid A m -> Incid B l -> Incid B m -> A=B. 
Proof.
intros l1 l2 A B Hl1l2 HAl1 HAl2 HBl1 HBl2.
assert ((A=B)\/(l1=l2)).
apply uniqueness; intuition.
intuition.
Qed.


Ltac Apply_unicity := match goal with
H1: ?A <> ?B, H2: ?Incid ?A ?l, H3: ?Incid ?B ?l, H4 : ?Incid ?A ?m, H5: ?Incid ?B ?m |- _ => 
let id:= fresh in assert (id: l=m); try apply (a1_unique A B l m H1 H2 H3 H4 H5);subst l 
| H1: ?l <> ?m, H2: ?Incid ?A ?l, H3: ?Incid ?A ?m, H4 : ?Incid ?B ?l, H5: ?Incid ?B ?m |- _ => 
let id:= fresh in assert (id: A=B); try apply (a2_unique l m A B H1 H2 H3 H4 H5);subst A 
end.

Ltac Collapse := repeat (Apply_unicity; CleanDuplicatedHyps).

(* Tests for the tactic
Export M.
Lemma essai2:
forall A B l m, A<>B ->
 Incid A l -> Incid B l -> Incid A m -> Incid B m -> True.
Proof.
intros.
Collapse.
auto.
Qed.

Lemma essai:
forall A B l m, l<>m ->
 Incid A l -> Incid B l -> Incid A m -> Incid B m -> True.
Proof.
intros.
Collapse.
auto.
Qed.

*)

Lemma incidAl1l2 :forall (l1 l2:Line)(A:Point), ~Incid A l1 /\ Incid A l2 -> l2 <> l1.
Proof.
intros A B l H HAB; subst A; tauto.
Qed.

Lemma incidABl : forall (A B:Point)(l:Line), ~Incid A l /\ Incid B l -> A <> B.
Proof.
intros l1 l2 A H Hl2l1; subst l1; tauto.
Qed.

End uniqueness_axioms.
