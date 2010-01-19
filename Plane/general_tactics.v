(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.*)
(* Julien Narboux (Julien.Narboux@inria.fr)                                     *)
(* LIX/INRIA FUTURS 2004-2008                                                     *)
(***************************************************************************)

Ltac ExistHyp t := match goal with
                   | H1:t |- _ => idtac
                   end.

Ltac HypOfType t := match goal with
                    | H1:t |- _ => H1
                    end.

Ltac CleanDuplicatedHyps :=
  repeat match goal with
         | H:?X1 |- _ => clear H; ExistHyp X1
         end.

Ltac not_exist_hyp t := match goal with
  | H1:t |- _ => fail 2
 end || idtac.

Ltac assert_if_not_exist H :=
  not_exist_hyp H;assert H.

Ltac suppose t := cut t;[intro|idtac].

Ltac DecompEx H P := elim H;intro P;intro;clear H.

Ltac DecompExAnd H P :=
  elim H;intro P;
  let id:=fresh in intro id;decompose [and] id;clear id;clear H.

Ltac DecompAndAll :=
 repeat
 match goal with
   | H:(?X1 /\ ?X2) |- _ => decompose [and] H;clear H
end.

Ltac use H := decompose [and ex] H; clear H.

Ltac use_all := repeat match goal with
| H: ?A /\ ?B  |- _ => use H
| H: ex ?P |- _ => use H
end.

Definition dist3 (S:Set) (A B C  : S) : Prop := 
  A <> B /\ A <> C /\ 
  B <> C. 

Definition dist4 (S:Set) (A B C D :S) : Prop := 
  A <> B /\ A <> C /\ A <> D /\ 
  B <> C /\ B <> D /\ 
  C <> D. 

Definition dist6 (S:Set) (A B C D E F : S) := 
  A<>B /\ A<>C /\ A<>D /\ A<>E /\ A<>F /\
  B<>C /\ B<>D /\ B<>E /\ B<>F /\
  C<>D /\ C<>E /\ C<>F /\
  D<>E /\ D<>F /\
  E<>F.

Implicit Arguments dist3.
Implicit Arguments dist4.
Implicit Arguments dist6.
