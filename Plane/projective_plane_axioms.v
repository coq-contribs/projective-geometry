Require Export general_tactics.

(** PreProjective plan **)

Module Type PreProjectivePlane.

Parameter Point: Set.
Parameter Line: Set.
Parameter Incid : Point -> Line -> Prop.

Axiom incid_dec : forall (A:Point)(l:Line), {Incid A l} + {~Incid A l}.

(** A1 : any two points lie on a line **) 

Axiom a1_exist : forall (A B :Point) ,{l:Line | Incid A l /\ Incid B l}.

(** A2 : any two lines meet in a point **)
Axiom a2_exist : forall (l1 l2:Line), {A:Point | Incid A l1 /\ Incid A l2}.

(** uniqueness **)
Axiom uniqueness : forall A B :Point, forall l m : Line, 
 Incid A l -> Incid B l  -> Incid A m -> Incid B m -> A=B\/l=m.

End PreProjectivePlane.

(** PreProjective plan with useful version of unicity **)

Module Type PreProjectivePlane2.

Parameter Point: Set.
Parameter Line: Set.
Parameter Incid : Point -> Line -> Prop.

Axiom incid_dec : forall (A:Point)(l:Line), {Incid A l} + {~Incid A l}.

(** A1 : any two points lie on a line **) 

Axiom a1_exist : forall (A B :Point) ,{l:Line | Incid A l /\ Incid B l}.

(** A2 : any two lines meet in a point **)
Axiom a2_exist : forall (l1 l2:Line), {A:Point | Incid A l1 /\ Incid A l2}.

(** uniqueness **)
Axiom uniqueness : forall A B :Point, forall l m : Line, 
 Incid A l -> Incid B l  -> Incid A m -> Incid B m -> A=B\/l=m.

Axiom a1_unique:forall (A B :Point)(l1 l2:Line),
  ~A=B -> Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> l1=l2.

Axiom a2_unique : forall(l1 l2 :Line)(A B :Point), 
  ~l1=l2 -> Incid A l1 -> Incid A l2 -> Incid B l1 -> Incid B l2 -> A=B. 

Axiom incidAl1l2 :forall (l1 l2:Line)(A:Point), ~Incid A l1 /\ Incid A l2 -> l2 <> l1.

Axiom incidABl : forall (A B:Point)(l:Line), ~Incid A l /\ Incid B l -> A <> B.
End PreProjectivePlane2.

(** Projective plane **)

Module Type ProjectivePlane.

Parameter Point: Set.
Parameter Line: Set.
Parameter Incid : Point -> Line -> Prop.

Axiom incid_dec : forall (A:Point)(l:Line), {Incid A l} + {~Incid A l}.

(** A1 : any two points lie on a line **) 

Axiom a1_exist : forall (A B :Point) ,{l:Line | Incid A l /\ Incid B l}.

(** A2 : any two lines meet in a point **)
Axiom a2_exist : forall (l1 l2:Line), {A:Point | Incid A l1 /\ Incid A l2}.

(** uniqueness **)
Axiom uniqueness : forall A B :Point, forall l m : Line, 
 Incid A l -> Incid B l  -> Incid A m -> Incid B m -> A=B\/l=m.


(** A3 : there exist four points with no three collinear **)
Axiom a3: {A:Point & {B :Point & {C:Point & {D :Point |
  (forall l :Line, dist4 A B C D/\ 
    (Incid A l /\ Incid B l -> ~Incid C l /\ ~Incid D l)
    /\ (Incid A l /\ Incid C l -> ~Incid B l /\ ~Incid D l)
    /\  (Incid A l /\ Incid D l -> ~Incid C l /\ ~Incid B l)
    /\  (Incid C l /\ Incid B l -> ~Incid A l /\ ~Incid D l)
    /\ (Incid D l /\ Incid B l -> ~Incid C l /\ ~Incid A l)
    /\  (Incid C l /\ Incid D l -> ~Incid B l /\ ~Incid A l))}}}}.

End ProjectivePlane.

(** A variant of projective geometry **)

Module Type ProjectivePlane'.

Parameter Point :Set.
Parameter Line:Set.
Parameter Incid : Point -> Line -> Prop.

Axiom incid_dec : forall (A:Point)(l:Line), {Incid A l} + {~Incid A l}.

(** A1 : any two Points lie on a line **) 

Axiom a1_exist : forall ( A B :Point) ,{l:Line | Incid A l /\ Incid B l}.

(** A2 : any two lines meet in a point **)
Axiom a2_exist : forall (l1 l2:Line), {A:Point | Incid A l1 /\ Incid A l2}.

(** uniqueness **)
Axiom uniqueness : forall A B :Point, forall l m : Line, 
 Incid A l -> Incid B l  -> Incid A m -> Incid B m -> A=B\/l=m.

(** A3s :  each line has at least three points and there are at least two lines **)

Axiom a3_1 : 
  (forall l:Line,{A:Point & {B:Point & {C:Point | (dist3 A B C/\Incid A l /\Incid B l /\ Incid C l)}}}).

Axiom a3_2 : {l1:Line & {l2:Line | l1 <> l2}}.

End ProjectivePlane'.

(** Another variant of projective geometry **)

Module Type ProjectivePlane2.

Parameter Point :Set.
Parameter Line:Set.
Parameter Incid : Point -> Line -> Prop.

Axiom incid_dec : forall (A:Point)(l:Line), {Incid A l} + {~Incid A l}.

(** A1 : any two points lie on a unique line *) 

Axiom a1_exist : forall ( A B :Point) ,{l:Line | Incid A l /\ Incid B l}.

Axiom a1_unique:forall (A B :Point)(l1 l2:Line),
  ~A=B -> Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> l1=l2.

(** A2 : any two lines meet in a unique point *)
Axiom a2_exist : forall (l1 l2:Line), {A:Point | Incid A l1 /\ Incid A l2}.

Axiom a2_unique : forall(l1 l2 :Line)(A B :Point), 
  ~l1=l2 -> Incid A l1 -> Incid A l2 -> Incid B l1 -> Incid B l2 -> A=B. 

(** A3s :  each line has at least three points and there are at least two lines *)

Axiom a3_1 : 
  (forall l:Line,{A:Point & {B:Point & {C:Point | (dist3 A B C/\Incid A l /\Incid B l /\ Incid C l)}}}).

Axiom a3_2 : {A:Point & {l:Line | ~Incid A l}}.

End ProjectivePlane2.

(** Bezem & Hendriks' axioms for projective geometry **)

Module Type CoherentProjectivePlane.

Parameter Point :Set.
Parameter Line:Set.
Parameter Incid : Point -> Line -> Prop.

Axiom incid_dec : forall (A:Point)(l:Line), {Incid A l} + {~Incid A l}.

(** A1 : any two points lie on a unique line *) 

Axiom a1_exist : forall ( A B :Point) ,{l:Line | Incid A l /\ Incid B l}.

(** A2 : any two lines meet in a unique Point *)
Axiom a2_exist : forall (l1 l2:Line), {A:Point | Incid A l1 /\ Incid A l2}.

Axiom uniqueness : forall(l1 l2 :Line)(A B :Point), 
 Incid A l1 -> Incid A l2 -> Incid B l1 -> Incid B l2 -> l1=l2\/A=B. 

(** A3s :  each line has at least three points and there are at least two lines *)

Axiom a3_1 : 
  (forall l:Line,{A:Point & {B:Point & {C:Point | (dist3 A B C/\Incid A l /\Incid B l /\ Incid C l)}}}).

(** We skolemize the second part of a3 *)
Parameters l1 l2 : Line.
Axiom a3_2 : l1<>l2.

End CoherentProjectivePlane.

(** Projective geometry **)
(** Axioms used by Coxeter **)
(** Desarguian Projective plane **)

Module Type CoxeterProjectivePlane.

Parameter Point: Set.
Parameter Line: Set.
Parameter Incid : Point -> Line -> Prop.

Axiom incid_dec : forall (A:Point)(l:Line), {Incid A l} + {~Incid A l}.

(* 2.13 *)
Axiom a1_unique:forall (A B :Point)(l1 l2:Line),
  ~A=B -> Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> l1=l2.

(* 3.11 *)
(* A2 : any two lines meet in a unique point *)
Axiom a2_exist : forall (l1 l2:Line), {A:Point | Incid A l1 /\ Incid A l2}.

(* 3.12 *)
(* A3 : there exist four points with no three collinear *)
Axiom a3: {A:Point & {B :Point & {C:Point & {D :Point |
  (forall l :Line, dist4 A B C D/\ 
    (Incid A l /\ Incid B l -> ~Incid C l /\ ~Incid D l)
    /\ (Incid A l /\ Incid C l -> ~Incid B l /\ ~Incid D l)
    /\  (Incid A l /\ Incid D l -> ~Incid C l /\ ~Incid B l)
    /\  (Incid C l /\ Incid B l -> ~Incid A l /\ ~Incid D l)
    /\ (Incid D l /\ Incid B l -> ~Incid C l /\ ~Incid A l)
    /\  (Incid C l /\ Incid D l -> ~Incid B l /\ ~Incid A l))}}}}.

Definition collinear A B C :=  exists l, Incid A l /\ Incid B l /\ Incid C l.

Definition is_inter I A B C D := collinear I A B /\ collinear I C D.

(* 2.17 *)
(* The three diagonal points of a complete quadrangle are never collinear *)
Axiom a2_17: forall P Q R S A B C, 
is_inter A Q R P S -> is_inter B Q S P R  -> is_inter C Q P R S -> ~ collinear A B C.

Definition injective (U V : Set) (f:U -> V) := forall x y:U, f x = f y -> x = y.
Definition surjective  (U V : Set) (f:U -> V) := forall y:V, exists x, f x = y.
Definition bijective U V f := surjective U V f /\ injective U V f.

Definition is_elementary_projectivity (f : Point -> Line) := 
  (bijective Point Line f) /\ (forall x : Point, Incid x (f x)).

Definition is_perspectivity (f: Point -> Point) := True.

(* 2.18 *)
(* If a projectivity leaves invariant each of three distinct points
 on a line, it leaves invariant every point on the line *)
Axiom l2_18 : 
forall A B C, forall f: Point -> Point, is_perspectivity f -> A<>B -> A<>C -> B<>C ->
f A = A -> f B = B -> f C = C -> forall X, f X = X.

(* 2.32 *)
(* Desargues *)
(* Todo *)

End CoxeterProjectivePlane.
