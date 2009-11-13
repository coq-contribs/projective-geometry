(*
                     Tactic gb
                     L.Pottier, 02-2008

Tactic gb proves p1=0, ... , pn=0 => p=0
where p1,...,pn,p are arithmetic expressions on real numbers.
Example: x^2+2*x*y=0 -> y^2=0 -> x+y=0.

The tactic uses Gröbner bases computations, 
with ocaml extracted code from the proof of Buchberger algorithm in Coq by L.Théry, 
but man written polynomial arithmetics. 
It uses also some code from the sos tactic by L.Théry.

Some examples:

Goal forall x y z:R, x^2+x*y=0 -> y^2+x*y=0 -> x+y=0.
gb.
Qed.

Goal forall x y:R, x*y + x = 0 -> y=1 -> 2*x=0.
Time gb.
Qed.

Goal forall a b c:R, a^2+b^2+c^2=0 -> a*b+b*c+a*c=0 -> a+b+c=0.
Time gb.
Qed.

Goal forall a b c s1 s2 s3:R, 
 s1=a+b+c->s2=a*b+b*c+a*c -> s3=a*b*c 
 -> a^3-s1*a^2+s2*a-s3=0.
Time gb.
Qed.

This examples needs too much time:

Goal forall a b c d s1 s2 s3 s4:R,
 s1=a+b+c+d -> s2=a*b+b*c+c*d+d*a -> s3= a*b*c+b*c*d+c*d*a+d*a*b->s4=a*b*c*d
-> a^4 - s1*a^3 + s2*a^2 -s3*a +s4 =0.
Time gb.

*)

Require Import ZArith.
Require Import Znumtheory.
Require Export Reals.
Require Import List.
Require Export gbtypes.


Open Scope R_scope.

(********************************************)
(* Convert positive into R                  *)
(********************************************)

Fixpoint IPR p {struct p}: R :=
  match p with
    xH => 1
  | xO xH => 1 + 1
  | xO p1 => 2 * (IPR p1)
  | xI xH => 1 + (1 + 1)
  | xI p1 => 1 + 2 * (IPR p1)
  end.

Definition IZR1 z :=
  match z with Z0 => 0 
             | Zpos p => IPR p 
             | Zneg p => -(IPR p) 
  end.


(********************************************)
(* Test for constant in R                   *)
(********************************************)

Ltac NCst t :=
 match t with
 | O => constr:(1%positive)
 | S O => constr:(1%positive)
 | S ?t1 =>
    match (NCst t1) with
    | false => constr:false
    | ?x1 => let x2 := 
                eval compute in (Psucc x1) in x2
    end
 | _ => constr:false
 end.
(********************************************)
(* Belonging in a list for R                *)
(********************************************)

Ltac rIN a l :=
 match l with
 | (cons a ?l) => constr:true
 | (cons _ ?l) => rIN a l
 | _ => constr:false
 end.

(********************************************)
(* Adding a variable in a list for R        *)
(********************************************)

Ltac rAddFv a l :=
 match (rIN a l) with
 | true => constr:l
 | _ => constr:(cons a l)
 end.

(********************************************)
(* Adding a variable in a list for R        *)
(********************************************)

Ltac rFind_at a l :=
 match l with
 | (cons a _) => constr:xH
 | (cons _ ?l) => let p := rFind_at a l in 
                  let v := constr:(Psucc p) in
                  let v1 := eval compute in v in
                  v1
 | _ => constr:xH
 end.

(********************************************)
(* Computing the list of variables for R    *)
(********************************************)

Ltac variables t :=
 let rec aux t fv :=
  match t with
| 0 => fv
| 1 => fv
| False  => fv
| ?t1 -> ?g1 =>
       let fv1  := aux t1 fv in
       let fv2  := aux g1 fv1 in constr: fv2
| (_ <= ?t1) => aux t1 fv 
| (_ < ?t1) => aux t1 fv 
| (?t1 = _) => aux t1 fv 
| (?t1 + ?t2) => 
       let fv1  := aux t1 fv in
       let fv2  := aux t2 fv1 in constr: fv2
| (?t1 * ?t2) => 
       let fv1  := aux t1 fv in
       let fv2  := aux t2 fv1 in constr: fv2
| (?t1 - ?t2) => 
       let fv1  := aux t1 fv in
       let fv2  := aux t2 fv1 in constr: fv2
| (-?t1) => 
       let fv1  := aux t1 fv in fv1
| (?t1 ^ ?t2) => 
       let fv1  := aux t1 fv in
       match NCst t2 with
       | false => let fv1 := rAddFv t fv in constr:fv1
       | _ => fv1
       end
| _ => let fv1 := rAddFv t fv in constr:fv1
  end
  in aux t (@nil R).

(********************************************)
(* Syntaxification tactic for R             *)
(********************************************)

Ltac abstrait t fv :=
 let rec aux t :=
  match t with
| 0 => constr:(Const 0 1)
| 1 => constr:(Const 1 1)
| 2 => constr:(Const 2 1)
| (?t1 = 0) -> ?g1 =>
       let v1  := aux t1 in
       let v2  := aux g1 in constr: (lceq v1 v2)
| (?t1 = 0) =>
       let v1  := aux t1 in constr: (lceq v1 lnil)
| (?t1 + ?t2) => 
       let v1  := aux t1 in
       let v2  := aux t2 in constr:(Add v1 v2)
| (?t1 * ?t2) => 
       let v1  := aux t1 in
       let v2  := aux t2 in constr:(Mul v1 v2)
| (?t1 - ?t2) => 
       let v1  := aux t1 in
       let v2  := aux t2 in constr:(Sub v1 v2)
| (?t1 ^ 0) => 
       constr:(Const 1 1)
| (?t1 ^ ?n) => 
       match NCst n with
       | false => let p := rFind_at t fv in constr:(Var p)
       | ?n1 => let v1  := aux t1 in constr:(Pow v1 n1)
       end
| (- ?t1) => 
       let v1  := aux t1 in constr:(Opp v1)
|  False  => constr:lnil
| _ =>
   let p := rFind_at t fv in constr:(Var p)
end
in aux t.

(********************************************)
(* Unsyntaxification for R                  *)
(********************************************)

Fixpoint interpret t fv {struct t}: R :=
  match t with
| (Add t1 t2) => 
       let v1  := interpret t1 fv in
       let v2  := interpret t2 fv in (v1 + v2)
| (Mul t1 t2) => 
       let v1  := interpret t1 fv in
       let v2  := interpret t2 fv in (v1 * v2)
| (Sub t1 t2) => 
       let v1  := interpret t1 fv in
       let v2  := interpret t2 fv in (v1 - v2)
| (Opp t1) => 
       let v1  := interpret t1 fv in (-v1)
| (Pow t1 t2) => 
       let v1  := interpret t1 fv in v1 ^(nat_of_P t2)
| (Const t1 t2) => (IZR1 t1)
|(Var n) => nth (pred (nat_of_P n)) fv 0
| Zero => 0
  end.

Fixpoint interpret_list l fv {struct l}:list R :=
 match l with
| lnil => nil
| lceq t l1 => (interpret t fv)::(interpret_list l1 fv)
end.

Fixpoint combine l1 l2 {struct l1}:R :=
 match l1 with
 |nil => 0
 |a::l11 => match l2 with 
                  |nil => 0
                  |b::l21 => a*b+(combine l11 l21)
                end
end.

Lemma psos_r1b: forall x y, x - y = 0 -> x = y.
intros x y H; replace x with ((x - y) + y);  
  [rewrite H | idtac]; ring.
Qed.

Lemma psos_r1: forall x y, x = y -> x - y = 0.
intros x y H; rewrite H; ring.
Qed.

Ltac equalities_to_goal := 
  match goal with 
|  H: (@eq R ?x 0) |- _ =>
        try generalize H; clear H
|  H: (@eq R 0 ?x) |- _ =>
        try generalize (sym_equal H); clear H
|  H: (@eq R ?x ?y) |- _ =>
        try generalize (psos_r1 _ _ H); clear H
 end.

Lemma gb_l1:forall c p:R, forall n:nat, ~n=O -> ~c=0 -> c*p^n=0 -> p=0.
Proof.
intros c p n Hn Hc Hp.
case (Rmult_integral _ _ Hp); clear Hp.
intros HH; case Hc; auto.
generalize Hn; case n; clear n c Hn Hc.
intros HH; case HH; auto.
intros n _; elim n; simpl; clear n; auto.
intros H1; rewrite <-H1; ring.
intros n Hrec H1.
case (Rmult_integral _ _ H1); clear H1; auto.
Qed.

Ltac rewrite_with_hyps :=
   match goal with 
|  H: (@eq R ?x 0) |- _ => rewrite H
end.

Ltac gb := 
  intros;
  apply psos_r1b;
  repeat equalities_to_goal;
  match goal with 
   |- ?t =>
    let l := variables t in
    let a := abstrait t l in
    let lp1:=constr:(List.rev (interpret_list a l))  in
    let p:= constr:(List.hd 0 lp1) in
    let lp:= constr:(List.rev (List.tail lp1)) in
(* we want show lp=0 => p=0 *)
    let t:= external "./gb/gb" "" a in 
(* t contains p^d, c and lc such that c*p^d = lc*lp *)
       match t with
        | lceq (Pow ?p0 ?d)  (lceq ?c ?lc) =>
              let lc:= constr:(interpret_list lc l) in
              let p0 := constr:(interpret p0 l) in
              let c := constr:(interpret c l) in
              let e := constr:(combine lc lp) in
              let Hgb1:=fresh "Hgb" in
              let Hgb2:=fresh "Hgb" in
         cut (p=p0);
            [simpl;intro Hgb1;rewrite Hgb1;
              cut (c*p0^(nat_of_P d)=e);
               [simpl;idtac
                |simpl; try ring]
           |simpl;try ring];
        intro Hgb2; intros;
        apply gb_l1 with c (nat_of_P d);
       [try (simpl;unfold nat_of_P;simpl; discriminate)
        |try(simpl; discrR)
        |try(simpl; rewrite Hgb2; repeat rewrite_with_hyps;ring)]
   end
end.







