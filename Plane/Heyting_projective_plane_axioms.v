(* Formalization of Heyting's axiomatic *)

(** We use the axioms proposed in the paper 
"Axioms for intuitionistic plane affine geometry". *)

Module Type HeytingProjectivePlane.

(** We assume that we have a set of points and of lines.  *)

Parameter Point : Set.
Parameter Line : Set.

(** Heyting's axiomatic is based on two predicates. *)

Parameter Incid : Point -> Line -> Prop.
Parameter Apart : Point -> Point -> Prop.

Notation "x # y" := (Apart x y) (at level 20).
Notation "x @ y" := (Incid x y) (at level 20).

Definition out (A : Point) (l : Line) : Prop := forall B, B @ l -> B # A.
Definition apart_l  (l m : Line) : Prop := exists A, A @ l /\ out A m. 

Notation "x ## y" := (apart_l x y) (at level 20).

(** %\textbf{% Apartness axioms. %}% *)

Axiom S1 : forall A B, A # B -> B # A.

Axiom S2 : forall A B, ~ A # B <-> A=B.

Axiom S3 : forall A B, A # B -> forall C, C # A \/ C # B.

(** %\textbf{% Geometric axioms. %}% *)

Axiom P1 : forall A B,  A # B -> exists l, A @ l /\ B @ l.

Axiom P2 : forall A B l m, A # B /\ A @ l /\ A @ m /\ B @ l /\ B @ m -> l=m.

Axiom P3 : forall l m, l ## m -> exists A, A @ l /\ A @ m.

Axiom P4 : forall A B C l m, A # B /\ A @ l /\ B @ l /\ 
       out C l /\ A @ m /\ C @ m -> out B m.

Axiom P5i :exists A, exists B, A # B.

Axiom P5ii: forall l, exists A, exists B, exists C, 
        A @ l /\ B @ l /\ C @  l /\ A # B /\ A # C /\ B # C.

Axiom P5iii: forall l, exists A, out A l.

Hint Immediate S1 : Heyting.
Hint Resolve S2 S3 : Heyting.
Hint Resolve P1 P2 P3 P4 P5i P5ii P5iii : Heyting.

Ltac eHeyting := eauto with Heyting.
Ltac Heyting := auto with Heyting.

End HeytingProjectivePlane.
