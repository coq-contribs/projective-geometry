Require Export projective_plane_axioms.

(** Fano's plane **)
(** also known as PG(2,2). **)

(** To show that our axiom system is consistent we build a finite model. **)

Module FanoPlane : ProjectivePlane.

(** We define point and line by an inductive type representing the seven possibilities. **)
(** We can not use directly the inductive type for 
  a technical reason related to Coq's implementation. **)

Inductive ind_Point : Set := A | B | C | D | E | F | G.
Inductive ind_line    : Set := ABF | BCD | CAE | ADG | BEG | CFG | DEF.

Definition Point : Set := ind_Point.
Definition Line    : Set := ind_line.

Definition Incid_bool : Point -> Line -> bool := fun P L =>
 match (P,L) with
 (A,ABF) | (A,CAE) | (A,ADG) | (B, BCD) | (B, BEG) | (B, ABF) 
|(C,BCD) | (C,CAE) | (C,CFG) | (D,BCD) | (D,ADG) | (D,DEF) 
|(E,CAE) | (E,BEG) | (E,DEF) | (F,ABF) | (F,DEF) | (F,CFG)
|(G,ADG) | (G,CFG) | (G,BEG)  => true
| _ => false
end.

Definition Incid : Point -> Line -> Prop := fun P L =>
 (Incid_bool P L =true).
 
Hint Unfold Incid Incid_bool.

Lemma incid_dec : forall (A:Point)(l:Line), {Incid A l} + {~Incid A l}.
Proof.
intros.
unfold Incid.
elim l;elim A0;unfold Incid_bool;simpl;auto;right;discriminate.
Qed.

(** A1 : any two points lie on a unique line **) 

Ltac solve_ex L := solve [exists L;auto].

Lemma a1_exist : forall ( A B :Point) ,{l:Line | Incid A l /\ Incid B l}.
Proof with auto.
intros.
elim A0;elim B0;
(** A tactic which tries all possible lines **)
first [solve_ex ABF
     |  solve_ex BCD
     |  solve_ex CAE
     |  solve_ex ADG
     |  solve_ex BEG
     |  solve_ex CFG
     |  solve_ex DEF
 ].
Qed.

Lemma degen_point: forall A:Point, forall P: Prop, A<>A -> P.
Proof.
intuition.
Qed.

Lemma degen_line: forall A:Line, forall P: Prop, A<>A -> P.
Proof.
intuition.
Qed.


Ltac remove_degen := match goal with
| H: ?A <> ?A |- ?G => apply (degen_point A G H) || apply (degen_line A G H)
end.

Lemma a1_unique:forall (A B :Point)(l1 l2:Line),
  ~A=B -> Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> l1=l2.
Proof.
intros X Y l1 l2 HXY H1 H2 H3 H4.
induction X;induction Y; try remove_degen;
induction l1;try discriminate; induction l2; discriminate || reflexivity.
Qed.

(** A2 : any two lines meet in a unique point **)
Lemma a2_exist : forall (l1 l2:Line), {A:Point | Incid A l1 /\ Incid A l2}.
Proof.
intros.
induction l1;induction l2;
(** A tactic which tries all possible points **)
first [solve_ex A
     |  solve_ex B
     |  solve_ex C
     |  solve_ex D
     |  solve_ex E
     |  solve_ex F
     |  solve_ex G
 ].
Qed.

Lemma a2_unique : forall(l1 l2 :Line)(A B :Point), 
  ~l1=l2 -> Incid A l1 -> Incid A l2 -> Incid B l1 -> Incid B l2 -> A=B.
Proof.
intros l1 l2 X Y H H1 H2 H3 H4.
 induction X;induction Y;try reflexivity;
 induction l1;try discriminate;
 induction l2;try discriminate;try remove_degen.
Qed.

Lemma uniqueness : forall A B :Point, forall l m : Line,
 Incid A l -> Incid B l  -> Incid A m -> Incid B m -> A=B\/l=m.
intros P Q l m H1 H2 H3 H4.
 induction P; induction Q; try ((left;reflexivity) || (right;reflexivity));
 induction l; try discriminate;
 induction m; try discriminate; try (left; reflexivity) ; try (right; reflexivity); try remove_degen.
Qed.

(** A3 : there exist four points with no three collinear **)
Lemma a3: {A:Point & {B :Point & {C:Point & {D :Point |
  (forall l :Line, dist4 A B C D/\ 
    (Incid A l /\ Incid B l -> ~Incid C l /\ ~Incid D l)
    /\ (Incid A l /\ Incid C l -> ~Incid B l /\ ~Incid D l)
    /\  (Incid A l /\ Incid D l -> ~Incid C l /\ ~Incid B l)
    /\  (Incid C l /\ Incid B l -> ~Incid A l /\ ~Incid D l)
    /\ (Incid D l /\ Incid B l -> ~Incid C l /\ ~Incid A l)
    /\  (Incid C l /\ Incid D l -> ~Incid B l /\ ~Incid A l))}}}}.
Proof.
exists A.
exists B.
exists C.
exists G.
intros.
split.
unfold dist4;intuition;discriminate.
elim l;unfold Incid, Incid_bool;intuition;discriminate.
Qed.


End FanoPlane.
