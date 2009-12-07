(* Require Export sets_of_points.*)
Require Export Omega.
Require Export sets_of_points.

Module Type Matroid (DecPoints: FSetInterface.WS).

Declare Module Export FiniteSetsDefs : BuildFSets DecPoints (* DecPoints *).

(** The rank of a set of points *)
Parameter rk : set_of_points -> nat.

(*1. 0<=rk(X)<=|X| *)
(*2. (subset e e') => rk(e)<=rk(e')*)
(*3. rk(union e e')+rk(intersection e e')<= rk(e')+rk(e)*)

Axiom matroid1_a  : forall X, rk X >= 0.

Axiom matroid1_b : forall X, rk X <= cardinal X.

Axiom matroid2:
forall e e':set_of_points, Subset e e' -> rk(e)<=rk(e').

Axiom matroid3:
forall e e':set_of_points,
 rk(union e e') + rk(inter e e') <= rk(e) + rk(e'). 

End Matroid.

Module Type Matroid' (DecPoints: FSetInterface.WS).

Declare Module Export FiniteSetsDefs : BuildFSets DecPoints.

(** The rank of a set of points *)
(** alternative definition *)

Parameter rk : set_of_points -> nat.

Axiom rk_compat:
  forall x x', Equal x x' ->
     rk x = rk x'.

(*1. rk(O)=0 *)
(*2. rk(X) <= rk(Xu{x})<=rk(X)+1*)
(*3. rk(X \u222a {y}) = rk(X \u222a {z}) = rk(X) \u21d2 rk(X) =
 rk(X \u222a {y, z})*)

Axiom matroid1'  : rk empty = 0.

Axiom matroid2':
forall X:set_of_points, forall x : Point, rk(X)<=rk (add x X) <= rk(X)+1.

Axiom matroid3': forall X y z, 
   rk(add y X) = rk(add z X) ->
   rk(add z X) = rk(X) ->
   rk(X) = rk(union X (couple y z)).

End Matroid'.

