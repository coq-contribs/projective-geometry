Require Export basic_facts_plane.
Require Export forth.

(** First, we derive some lemmas needed to show duality. **)

Module Type Decidability.

Parameter Line : Set.
Parameter Point : Set.
Parameter Incid : Point -> Line -> Prop.

Axiom eq_line_dec : forall d1 d2 : Line, {d1 = d2}+{d1 <> d2}.
Axiom eq_point_dec : forall A B: Point, {A = B}+{A <> B}.
(* should be moved somewhere else *)
Axiom outsider : forall l1 l2: Line, { P:Point | ~Incid P l1/\~Incid P l2}.

End Decidability.

Module decidability (M:ProjectivePlane) : Decidability 
with Definition Line:=M.Line 
with Definition Point:= M.Point
with Definition Incid := M.Incid.

Definition Line:=M.Line.
Definition Point:= M.Point.
Definition Incid := M.Incid.

Module Export ProjectivePlane' := forth.forth M.
Module Export uniq := uniqueness_axioms M.

(* Decidability of point equality / line equality *)

Lemma eq_point_dec_sublemma :  
  forall A B : Point, forall d : Line, ~Incid A d -> ~Incid B d -> {A = B}+{A <> B}.
generalize a3_1 a3_2.
intros Ha31' Ha32'.
intros A B d HAd HBd.
elim (Ha31' d).
intros M HM.
elim HM; clear HM; intros N HN.
elim HN; clear HN; intros P HMNP.
elim (a1_exist A M).
intros l1 Hl1.
elim (a1_exist A N).
intros l2 Hl2.
assert (l1 <> l2).
intros Hl1l2.
subst l1.
elim Hl2; intros Hl2a Hl2b.
elim Hl1; intros Hl1a Hl1b.
assert (N <> M).
unfold dist3 in HMNP; intuition.
elim HMNP; clear HMNP; intros Hdist3 HMNP.
elim HMNP; clear HMNP; intros HM HNP.
elim HNP; clear HNP; intros HN HP.
generalize (a1_unique N M l2 d H Hl2b Hl1b HN HM).
intros Hl2d.
subst l2.
tauto.
elim (incid_dec B l1).
intros HBl1.
elim (incid_dec B l2).
intros HBl2.
left.
eapply a2_unique.
apply H.
tauto.
tauto.
assumption.
intuition.
intros HBl2.
right.
assert (B<>A) ; [idtac | intuition].
eapply incidABl.
split.
apply HBl2.
tauto.
intros HBl1.
right.
assert (B<>A); [idtac | intuition].
eapply incidABl.
split.
apply HBl1.
tauto.
Qed.

Lemma eq_point_dec : forall A B: Point, {A = B}+{A <> B}.
generalize a3_1 a3_2.
intros Ha31' Ha32'.
elim Ha32'; intros delta_0 Hdelta.
elim Hdelta; clear Hdelta; intros delta_1 Hdelta.
intros A B.
elim (incid_dec A delta_0).
intros HAd.
elim (incid_dec B delta_0).
intros HBd.
elim (incid_dec A delta_1).

(* cas1 *)
intros HAd1.
elim (incid_dec B delta_1).
intros HBd1.
left.
eapply a2_unique;eauto.

intros HBd1.
right.
assert (B<>A).
eapply (incidABl B A);eauto.
intuition.


intros HAd1.
elim (incid_dec B delta_1).
intros HBd1.
right.
eapply incidABl.
split.
apply HAd1.
apply HBd1.
(* cas 2 *)
intros HBd1.
eapply eq_point_dec_sublemma; eauto.

intros HBd.
right.
assert (B<>A).
apply (incidABl B A delta_0).
split.
assumption.
assumption.
intuition.

intros HAd.
elim (incid_dec B delta_0).
intros HBd.
right.
eapply incidABl with (l:=delta_0).
split.
assumption.
assumption.
(* cas 2 *)
intros HBd.
eapply eq_point_dec_sublemma; eauto.
Qed.

Ltac Apply_unicity := match goal with
H1: ?A <> ?B, H2: ?Incid ?A ?l, H3: ?Incid ?B ?l, H4 : ?Incid ?A ?m, H5: ?Incid ?B ?m |- _ => 
let id:= fresh in assert (id: l=m); try apply (a1_unique A B l m H1 H2 H3 H4 H5);subst l 
| H1: ?l <> ?m, H2: ?Incid ?A ?l, H3: ?Incid ?A ?m, H4 : ?Incid ?B ?l, H5: ?Incid ?B ?m |- _ => 
let id:= fresh in assert (id: A=B); try apply (a2_unique l m A B H1 H2 H3 H4 H5);subst A 
end.

Ltac Collapse := repeat (Apply_unicity; CleanDuplicatedHyps).

Lemma eq_line_dec :  
  forall d1 d2 : Line, {d1 = d2}+{d1 <> d2}.
Proof.
generalize a3_1 a3_2.
intros Hsa31' Hsa32'.
intros l1 l2.
elim (Hsa31' l1).
intros M HM; elim HM; clear HM; intros N HN; elim HN; clear HN; intros P HMNP.
elim (incid_dec M l2).
intros HMl2; elim (incid_dec N l2).
intros HNl2.
left.
unfold dist3 in *;decompose [and] HMNP;Collapse.

intros HNl2.
right.
apply incidAl1l2 with (A:=N).
intuition.
right.
apply incidAl1l2 with (A:=M); intuition.
Qed.

Lemma first_point : forall l:Line, {V:Point| Incid V l}.
Proof.
intros l.
elim (a3_1 l).
intros P HP.
elim HP; intros B HB ; elim HB; intros.
exists P; intuition.
Qed.


(*** essai de preuve de décidabilité de l'incidence à partir de celles de l'égalité
pour les points et aussi pour les droites *)

Lemma incid_dec2 : forall A:Point, forall l:Line, {Incid A l}+{~Incid A l}. 
Proof.
intros A l.
elim (first_point l).
intros M HM.
elim (eq_point_dec A M).
intros; subst; left; auto.
intros HAM.
elim (a1_exist A M).
intros lAM (HA,HM').
elim (eq_line_dec lAM l).
intros; subst; left; auto.
intros;right; unfold not; intro H.
generalize (a1_unique A M lAM l HAM HA HM' H HM).
intros; subst; intuition.
Qed.

Lemma second_line : forall l1 : Line, {l2:Line | l1<>l2}.
intros l1.
elim a3_2.
intros d1 Hd1.
elim Hd1; clear Hd1; intros d2 Hd1d2.
elim (eq_line_dec l1 d1). 
intros Hl1d1; subst l1.
exists d2.
assumption.
intros Hl1d1.
exists d1.
assumption.
Qed.

Lemma second_point : forall A:Point, forall l:Line, Incid A l -> {B : Point | (B<>A)/\(Incid B l)}.
intros A l HAl.
elim (a3_1 l).
intros P1 H.
elim H; intros P2 H'.
elim H'; intros P3 H''.
elim (eq_point_dec A P1).
intros HAP1.
subst A.
exists P2.
unfold dist3 in *; intuition.
intros Hnew.
exists P1.
intuition.
Qed.

Lemma third_point : forall A B:Point, forall l:Line, A<>B/\Incid A l/\Incid B l -> 
{C:Point | dist3 A B C/\Incid C l}.
intros A B l HABl.
elim (a3_1 l).
intros P1 H.
elim H; intros P2 H'.
elim H'; intros P3 H''.
elim (eq_point_dec A P1).
intros HAP1.
subst A.
elim (eq_point_dec B P2).
intros HBP2.
subst B.
exists P3.
unfold dist3 in *; intuition.
intros HBP2.
exists P2.
unfold dist3 in *; intuition.
intros HAP1.
elim (eq_point_dec B P1).
intros HBP1.
subst B.
elim (eq_point_dec A P2).
exists P3.
subst A.
unfold dist3 in *; intuition.
intros HAP2.
exists P2.
unfold dist3 in *; intuition.
intros HBP1.
exists P1.
unfold dist3 in *;intuition.
Qed.

Lemma outsider : forall l1 l2: Line, { P:Point | ~Incid P l1/\~Incid P l2}.
intros l1 l2.
elim (eq_line_dec l1 l2).
intros Hl1l2; subst l1.
elim (second_line l2).
intros d Hl2d.
elim (a3_1 d).
intros P HP.
elim (incid_dec P l2).
intros HPl2.
elim (incid_dec P d).
intros HPd.
elim (second_point P d HPd). 
intros Q (HQP,HQd).
exists Q.
assert (~Incid Q l2).
intros HQl2.
apply HQP.
eapply (a2_unique l2 d Q P Hl2d); assumption.
tauto.
intros HPd.
elim (a2_exist l2 d); intros C (HCl2,HCd).
elim (second_point C d HCd). 
intros Q (HQC,HQd).
exists Q.
assert (~Incid Q l2).
intros HQl2.
apply HQC.
apply (a2_unique l2 d Q C); assumption.
tauto.
intros HPl2; exists P; tauto.

intros Hl1l2.
elim (a2_exist l1 l2).
intros C (HCl1,HCl2).
elim (second_point C l1 HCl1).
intros P1 (HP1C,HP1l1).
elim (second_point C l2 HCl2).
intros P2 (HP2C,HP2l2).
elim (a1_exist P1 P2).
intros d (HP1d,HP2d).
elim (eq_point_dec P1 P2).

intros HP1P2.
subst P1.
assert (P2=C).
eapply (a2_unique l1 l2 P2 C); assumption. 
assert (Hf:False) by (apply (HP2C H)).
elim Hf.
intros HP1P2.
elim (third_point P1 P2 d (conj HP1P2 (conj HP1d HP2d))).
intros newP (Hdist3,HnewPd).
exists newP.
split.
intros HnewPl1.
assert (H:(newP<>P1)) by (unfold dist3 in *; intuition).
apply H.
assert (d<>l1).
intros Hdl1.
subst l1.
apply HP2C.
eapply (a2_unique d l2 P2 C); assumption.
eapply (a2_unique d l1 newP P1); assumption.
intros HnewPl2.
assert (H:(newP<>P2)) by (unfold dist3 in *; intuition).
apply H.
assert (d<>l2).
intros Hdl2.
subst l2.
apply HP1C.
eapply (a2_unique l1 d P1 C) ; assumption.
eapply (a2_unique d l2 newP P2); try assumption. 
Qed.

End decidability.




