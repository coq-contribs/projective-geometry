Require Export desargues2Dlemmas3.
Require Export desargues3Dspecial.

Module Desargues2Dfinal  (DecPoints: FSetInterface.WS) (M: RankProjectiveSpace DecPoints).

Module Export Desargues_2D_lem3 := Desargues2Dlemmas3 DecPoints M.
Module Export Desargues_3D := Desargues3Dspecial DecPoints M.

Section desargues_theorem.
Variables A' B' C' : Point.
Variables A B C : Point.

Variables O : Point.

Variable rABC : rk(triple A B C)=3.
Variable rA'B'C' : rk(triple A' B' C')=3.
Variable rABCA'B'C'O : rk(union (triple A B C) (union (triple A' B' C') (singleton O)))=3.

Variable rABO : rk(triple A B O)=3.
Variable rACO :rk(triple A C O)=3.
Variable rBCO : rk (triple B C O)=3.

Variable rAA'O : rk(triple A A' O)=2.
Variable rBB'O : rk(triple B B' O)=2.
Variable rCC'O : rk(triple C C' O)=2.

Variable rA'O : rk(couple A' O)=2.
Variable rB'O : rk(couple B' O)=2.
Variable rC'O : rk(couple C' O)=2.

Lemma rA'B'O' : rk(triple A' B' O)=3.
Proof.
eapply (l1_scheme A' B' A B O); try assumption.
Qed.

Lemma rA'C'O' :rk(triple A' C' O)=3.
Proof.
eapply (l1_scheme A' C' A C O); try assumption.
Qed.

Lemma rB'C'O' : rk (triple B' C' O)=3.
Proof.
eapply (l1_scheme B' C' B C O); try assumption.
Qed.

Hint Resolve rA'B'O' rA'C'O' rB'C'O' : rk.

(* all points are distinct, especially ABC A'B'C and O *)
(* If needed, for any 2 points, rk(X,Y)=2 *)
(* triangles are truely perspective in the plane *)

Variable rAA' : rk(couple A A')=2.
Variable rBB' : rk(couple B B')=2.
Variable rCC' : rk(couple C C')=2.

Variables alpha beta gamma : Point.

Variable rABgamma : rk(triple A B gamma)=2.
Variable rA'B'gamma : rk(triple A' B' gamma)=2.

Variable rACbeta : rk(triple A C beta)=2.
Variable rA'C'beta : rk(triple A' C' beta)=2.

Variable rBCalpha : rk(triple B C alpha)=2.
Variable rB'C'alpha : rk(triple B' C' alpha) =2.

Lemma Desargues_plane : rk (triple alpha beta gamma) <= 2.
Proof.
elim (l2rABOP A' B' C' A B C O); try assumption.
intros P (rABOP, rOP).
elim (ex_o O P).
intros o (rOPo,(rOo, rPo)).
setoid_replace (triple O P o) with (triple o O P) in rOPo by fsetdecide. 
assert (T:exists a : Point, rk (triple o A a) = 2 /\ rk (triple P A' a) = 2).
eapply ra;eauto with rk.
elim T;intros a (Ha2,Ha2');clear T.
assert (Tb:exists b : Point, rk (triple o B b) = 2 /\ rk (triple P B' b) = 2).
eapply rb;eauto with rk.
elim Tb;intros b (Hb2,Hb2');clear Tb.
assert (Tc:exists c : Point, rk (triple o C c) = 2 /\ rk (triple P C' c) = 2).
eapply rc;eauto with rk.
elim Tc;intros c (Hc2,Hc2');clear Tc.
(* we prove r(a,b,c)=3 in advance, so we can reuse it in subsequent sections of the proof *)
assert (rabc3:rk(triple a b c)=3).
apply le_antisym.
apply rk_triple_le.
assert (rk (union (triple a b c) (couple o A))>=4).
generalize (matroid3 (union (triple a b c) (couple o A)) (triple o B b)).
setoid_replace (union (union (triple a b c) (couple o A)) (triple o B b)) with
(union (triple a b c) (triple o A B)) by (unfold Equal; split; fsetdecide_no_hyps).
assert (rk(union (triple a b c) (triple o A B))>=4).
generalize (matroid3 (union (triple a b c) (triple o A B)) (triple o C c)).
assert (rk (union (union (triple a b c) (triple o A B)) (triple o C c)) >=4).
assert (rk (add c (triple A B C)) >=4).
generalize (rABOc A' B' C' A B C O rABC rABCA'B'C'O rABO rACO rCC'O rCC' P rABOP o); intro Hr.
assert (rk (add c (triple A B C)) >= 4).
setoid_replace (triple A B C) with (triple C B A) by fsetdecide_no_hyps.
apply (rk3_4 O B A C c).
apply le_antisym.
assert (rk (union (triple A B C) (union (triple A' B' C') (singleton O))) >= rk (add C (triple O B A))).
apply matroid2; fsetdecide_no_hyps.
omega.
assert (rk(triple A B C)<=rk(add C (triple O B A))).
apply matroid2; fsetdecide_no_hyps.
omega.
setoid_replace (triple B A C) with (triple A B C) by fsetdecide_no_hyps.
assumption.
setoid_replace (triple O B A) with (triple A B O) by fsetdecide_no_hyps.
eapply Hr; try eassumption.
omega.
assert (rk (union (union (triple a b c) (triple o A B)) (triple o C c)) >=rk (add c (triple A B C))).
apply matroid2; fsetdecide_no_hyps.
omega.
assert (rk (inter (union (triple a b c) (triple o A B)) (triple o C c)) >=
rk (couple o c)).
apply matroid2; fsetdecide_no_hyps.
assert (rk (couple o c)>=2).
setoid_replace (couple o c) with (couple c o) by fsetdecide_no_hyps.
generalize (rco A' B' C' A B C O rA'B'C' rABCA'B'C'O rACO rA'B'O' rA'C'O' rB'C'O' rAA'O rBB'O rCC'O rCC' P rABOP o rOPo rOo rPo c Hc2 Hc2'); omega.
omega.
assert (rk(inter (union (triple a b c) (couple o A)) (triple o B b))>=rk(couple o b)).
apply matroid2; fsetdecide_no_hyps.
assert (rk(couple o b)>=2).
setoid_replace (couple o b) with (couple b o) by fsetdecide_no_hyps.
generalize (rbo A' B' C' A B C O rABC rA'B'C' rABCA'B'C'O rABO rACO rA'B'O' rA'C'O' rB'C'O' rAA'O rBB'O rCC'O rBB' P rABOP o rOPo rOo rPo b Hb2 Hb2') ; omega.
omega.
generalize (matroid3 (triple a b c) (triple o A a)).
setoid_replace (union (triple a b c) (triple o A a))
with (union (triple a b c) (couple o A)) by (unfold Equal; split; fsetdecide_no_hyps).
assert (rk(inter (triple a b c) (triple o A a))>=rk(singleton a)).
apply matroid2; fsetdecide_no_hyps.
rewrite rk_singleton in H0.
omega.
(* end of the proof of r(a,b,c)=3 *)
eapply (Desargues A B C a b c alpha beta gamma o).
setoid_replace (triple A a o) with (triple o A a) by fsetdecide_no_hyps;assumption.
setoid_replace (triple B b o) with (triple o B b) by fsetdecide_no_hyps;assumption.
setoid_replace (triple C c o) with (triple o C c) by fsetdecide_no_hyps;assumption.
assumption.
assumption.

(* r(a,b,c,A,B,C)>=4 *)
assert (rk(add b (triple A B C))<= rk (union (triple a b c) (triple A B C))).
apply matroid2; fsetdecide_no_hyps.
assert (rk(add b (triple A B C)) >= 4).
generalize (rABOb A' B' C' A B C O rABC rABCA'B'C'O rABO rACO rBB'O rBB' P rABOP o rOPo rOo b Hb2 Hb2'); intros HrABOb.
generalize (matroid3 (add b (triple A B C)) (add O (triple A B C))).
setoid_replace (union (add b (triple A B C)) (add O (triple A B C))) 
with (union (triple A B C) (couple O b)) by (unfold Equal; split; fsetdecide_no_hyps).
assert (rk(inter (add b (triple A B C)) (add O (triple A B C)))>=rk(triple A B C)).
apply matroid2; fsetdecide_no_hyps.
assert (rk(add b (triple A B C))<=rk(union (triple A B C) (couple O b))).
apply matroid2; fsetdecide_no_hyps.
assert (rk (add b (triple A B C))>=4).
setoid_replace (triple A B C) with (triple C A B) by fsetdecide_no_hyps.
apply (rk3_4 O A B C b).
apply le_antisym.
assert (rk(add C (triple O A B))<=rk
                (union (triple A B C) (union (triple A' B' C') (singleton O))) ).
apply matroid2; fsetdecide_no_hyps.
omega.
assert (rk(add C (triple O A B)) >=rk(triple A B C)).
apply matroid2; fsetdecide_no_hyps.
omega.
assumption.
setoid_replace (triple O A B) with (triple A B O) by fsetdecide_no_hyps.
assumption.
omega.
assert (rk(add C (triple O A B))<=rk
                (union (triple A B C) (union (triple A' B' C') (singleton O)))).
apply matroid2; fsetdecide_no_hyps.
omega.

(* gamma *)
apply (beta_ok' A' C' B' A C B O) with (P:=P) (o:=o) (alpha:=alpha) (gamma:=beta) (b:=c); try eassumption.
setoid_replace (triple A C B) with (triple A B C) by fsetdecide_no_hyps; assumption.
setoid_replace (triple A' C' B') with (triple A' B' C') by fsetdecide_no_hyps; assumption.
setoid_replace (triple A C B) with (triple A B C) by fsetdecide_no_hyps.
setoid_replace (triple A' C' B') with (triple A' B' C') by fsetdecide_no_hyps; assumption.
setoid_replace (triple C B O) with (triple B C O) by fsetdecide_no_hyps;assumption.
eauto with rk.
eauto with rk.
eauto with rk.
setoid_replace (triple C' B' O) with (triple B' C' O) by fsetdecide_no_hyps; eauto with rk.
apply (rACOP A' B' C' A B C); try assumption.
setoid_replace (triple C B alpha) with (triple B C alpha) by fsetdecide_no_hyps; assumption.
setoid_replace (triple C' B' alpha) with (triple B' C' alpha) by fsetdecide_no_hyps; assumption.
setoid_replace (triple a c b) with (triple a b c) by fsetdecide_no_hyps; assumption.

assumption.
(* beta *)
apply (beta_ok' A' B' C' A B C O) with (P:=P) (o:=o) (alpha:=alpha) (gamma:=gamma) (b:=b); try eassumption.
eauto with rk.
eauto with rk.
eauto with rk.
assumption.
(* alpha *)
apply (beta_ok' B' A' C' B A C O) with (P:=P) (o:=o) (alpha:=beta) (gamma:=gamma) (b:=a); try eassumption.
setoid_replace (triple B A C) with (triple A B C) by fsetdecide_no_hyps ; assumption.
setoid_replace (triple B' A' C') with (triple A' B' C') by fsetdecide_no_hyps ; assumption.
setoid_replace (triple B A C) with (triple A B C) by fsetdecide_no_hyps.
setoid_replace (triple B' A' C') with (triple A' B' C') by fsetdecide_no_hyps.
assumption.
setoid_replace (triple B A O) with (triple A B O) by fsetdecide_no_hyps; assumption.
setoid_replace (triple B' A' O) with (triple A' B' O) by fsetdecide_no_hyps; eauto with rk.
eauto with rk.
eauto with rk.
setoid_replace (triple B A O) with (triple A B O) by fsetdecide_no_hyps; assumption.
setoid_replace (triple B A gamma) with (triple A B gamma) by fsetdecide_no_hyps; assumption.
setoid_replace (triple B' A' gamma) with (triple A' B' gamma) by fsetdecide_no_hyps; assumption.
setoid_replace (triple b a c) with (triple a b c) by fsetdecide_no_hyps; assumption.

assumption.
eauto with rk.
eauto with rk.
eauto with rk.
Qed.

End desargues_theorem.

End Desargues2Dfinal.

