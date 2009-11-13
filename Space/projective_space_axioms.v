Require Export FSets.


Definition dist_3 (S:Type) (A B C  : S) : Prop := A <> B /\ A <> C /\ B <> C. 

Definition dist_4 (S:Type) (A B C D :S) : Prop := 
  A <> B /\ A <> C /\ A <> D /\ B <> C /\ B <> D /\ C <> D. 


Module Type ProjectiveSpace (DecPoints: FSetInterface.WS).

Notation "s [==] t" := (DecPoints.eq s t) (at level 70, no associativity).

Definition dist4 A B C D  := 
 ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ 
 ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D.

Definition dist3 A B C  := 
 ~ A [==] B /\ ~ A [==] C /\ ~ B [==] C.

(*** Projective geometry ****)
Definition Point := DecPoints.t.
Parameter Line: Type.
Parameter Incid : Point -> Line -> Prop.

Axiom incid_dec : forall (A:Point)(l:Line), {Incid A l} + {~Incid A l}.

(* A1 : any two points lie on a unique Line *) 

Axiom a1_exists : forall A B : Point, {l : Line | Incid A l /\ Incid B l}.

Axiom uniqueness : forall (A B :Point)(l1 l2:Line),
   Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> A [==] B \/ l1 = l2.

(* A2 : Pasch's axiom *)

Axiom a2 : forall A B C D:Point, forall lAB lCD lAC lBD :Line, 
dist4 A B C D -> 
Incid A lAB/\Incid B lAB ->  
Incid C lCD/\Incid D lCD -> 
Incid A lAC/\Incid C lAC -> 
Incid B lBD/\Incid D lBD ->
(exists I:Point, (Incid I lAB /\ Incid I lCD)) -> exists J:Point, (Incid J lAC /\Incid J lBD). 

(** A3 : dimension-related axioms *)

Axiom a3_1 : 
  forall l:Line,exists A:Point, exists B:Point, exists C:Point, 
 dist3 A B C/\Incid A l /\Incid B l /\ Incid C l.

Definition Intersect (l1 l2:Line) := exists P:Point, Incid P l1 /\ (Incid P l2).

(** there exists 2 lines which do not intersect *)
Axiom a3_2 (* dim >= 3 *) : exists l1:Line, exists l2:Line, forall p:Point, ~(Incid p l1/\Incid p l2). 

Definition Intersect_In (l1 l2 :Line) (P:Point) := Incid P l1 /\ Incid P l2.

Axiom a3_3 :  forall l1 l2 l3:Line, dist_3 Line l1 l2 l3 -> 
exists l4 :Line,  exists J1:Point, exists J2:Point, exists J3:Point, (dist3 J1 J2 J3) /\ 
     (Intersect_In l1 l4 J1) /\ (Intersect_In l2 l4 J2) /\ (Intersect_In l3 l4 J3).


End ProjectiveSpace.

Module Type ProjectiveSpaceOrHigher (DecPoints: FSetInterface.WS).

Notation "s [==] t" := (DecPoints.eq s t) (at level 70, no associativity).

Definition dist4 A B C D  := 
 ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ 
 ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D.

Definition dist3 A B C  := 
 ~ A [==] B /\ ~ A [==] C /\ ~ B [==] C.

(*** Projective geometry ****)
Definition Point := DecPoints.t.
Parameter Line : Type.

(** We do force to use Coq equality for line equality in order to be able to prove that the rank axiom system
implies this one *)

(* Of course one can implement this using Coq's equality without problem. *)

Parameter line_eq : Line -> Line -> Prop.
Axiom line_eq_sym : forall l m, line_eq l m -> line_eq m l.
Axiom line_eq_trans : forall l m n, line_eq l m -> line_eq m n ->  line_eq l n.
Axiom line_eq_refl : forall l, line_eq l l.

Parameter Incid : Point -> Line -> Prop.

Axiom incid_dec : forall (A:Point)(l:Line), {Incid A l} + {~Incid A l}.

(* A1 : any two points lie on a unique Line *) 

Axiom a1_exists : forall A B : Point, {l : Line | Incid A l /\ Incid B l}.

Axiom uniqueness : forall (A B :Point)(l1 l2:Line),
   Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> A [==] B \/ line_eq l1 l2.

(* A2 : Pasch's axiom *)

Axiom a2 : forall A B C D:Point, forall lAB lCD lAC lBD :Line, 
dist4 A B C D -> 
Incid A lAB/\Incid B lAB ->  
Incid C lCD/\Incid D lCD -> 
Incid A lAC/\Incid C lAC -> 
Incid B lBD/\Incid D lBD ->
(exists I:Point, (Incid I lAB /\ Incid I lCD)) -> exists J:Point, (Incid J lAC /\Incid J lBD). 

(** A3 : dimension-related axioms *)

Axiom a3_1 : 
  forall l:Line,exists A:Point, exists B:Point, exists C:Point, 
 dist3 A B C/\Incid A l /\Incid B l /\ Incid C l.

(** there exists 2 lines which do not intersect *)
Axiom a3_2 (* dim >= 3 *) : exists l1:Line, exists l2:Line, forall p:Point, ~(Incid p l1/\Incid p l2). 

End ProjectiveSpaceOrHigher.

Module Type VeblenYoungProjectiveSpace.

Parameter Point: Set.
Parameter Line: Set.
Parameter Incid : Point -> Line -> Prop.


(* A1 line existence *)
Axiom A1 : forall A B, A <> B -> {l:Line | Incid A l /\ Incid B l}.

(* A2 line unicity *)
Axiom A2 : forall (A B :Point)(l1 l2:Line), A<>B ->
   Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> l1=l2.

Definition collinear A B C := exists l, Incid A l /\ Incid B l /\ Incid C l.

Axiom A3: forall A B C D E, ~ collinear A B C -> D<>E -> collinear B C D -> collinear C A E ->
 {F:Point | collinear A B F /\ collinear D E F}.

Axiom E0: forall l, {A:Point & {B:Point & {C:Point | (dist_3 Point A B C/\Incid A l /\Incid B l /\ Incid C l)}}}.

(* E1 *)
Axiom l0 : Line.

Axiom E2: ~ exists l, forall A, Incid A l.

(* E3 all points are not on the same plane *) 

(* E3' if S3 is a three space, every point is on S3 *)


(* E3' is equivalent to any two distinct planes have a line in common *)
(* E3' is equivalent to every set of five points lie on the same three-space *)


End VeblenYoungProjectiveSpace.

