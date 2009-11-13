Require Export decidability.

Module AbstractProjectivePlane : ProjectivePlane.

Parameter Point :Set.
Parameter Line:Set.
Parameter Incid : Point -> Line -> Prop.

(* distinct *)
Axiom incid_dec : forall (A:Point)(l:Line), {Incid A l} + {~Incid A l}.

(* A1 : any two points lie on a unique line *) 
Axiom a1_exist : forall ( A B :Point) ,{l:Line | Incid A l /\ Incid B l}.

(* A2 : any two lines meet in a unique point *)
Axiom a2_exist : forall (l1 l2:Line), {A:Point | Incid A l1 /\ Incid A l2}.

Axiom uniqueness : forall (A B :Point)(l1 l2:Line),
   Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> A=B\/l1=l2.

(* A3 : there exist four points with no three collinear *)
Axiom a3: {A:Point & {B :Point & {C:Point & {D :Point |
  (forall l :Line, dist4 A B C D/\ 
    (Incid A l /\ Incid B l -> ~Incid C l /\ ~Incid D l)
    /\ (Incid A l /\ Incid C l -> ~Incid B l /\ ~Incid D l)
    /\  (Incid A l /\ Incid D l -> ~Incid C l /\ ~Incid B l)
    /\  (Incid C l /\ Incid B l -> ~Incid A l /\ ~Incid D l)
    /\ (Incid D l /\ Incid B l -> ~Incid C l /\ ~Incid A l)
    /\  (Incid C l /\ Incid D l -> ~Incid B l /\ ~Incid A l))}}}}.

End AbstractProjectivePlane.

Require Export forth.

Module AbstractProjectivePlane' := forth.forth AbstractProjectivePlane.

Export AbstractProjectivePlane.
Export AbstractProjectivePlane'.
(*
Require Export basic_facts. 

Module Basic_facts := basic_facts.uni AbstractProjectivePlane.

Export Basic_facts.
*)
