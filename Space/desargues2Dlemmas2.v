Require Export desargues2Dlemmas.

Module Desargues2Dlemmas2  (DecPoints: FSetInterface.WS) (M: RankProjectiveSpace DecPoints).

Export M.

Module Export Desargues_plane_lem := Desargues2Dlemmas DecPoints M.

Section desargues_plane.

Variables A' B' C' : Point.
Variables A B C : Point.

Variables O : Point.

Variable rABC : rk(triple A B C)=3.
Variable rA'B'C' : rk(triple A' B' C')=3.
Variable rABCA'B'C'O : rk(union (triple A B C) (union (triple A' B' C') (singleton O)))=3.

Variable rABO : rk(triple A B O)=3. 
Variable rACO :rk(triple A C O)=3.
Variable rBCO : rk (triple B C O)=3.

Variable rA'B'O' : rk(triple A' B' O)=3. 
Variable rA'C'O' :rk(triple A' C' O)=3.
Variable rB'C'O' : rk (triple B' C' O)=3.

Variable rAA'O : rk(triple A A' O)=2.
Variable rBB'O : rk(triple B B' O)=2.
Variable rCC'O : rk(triple C C' O)=2.

Variable rAA' : rk(couple A A')=2.
Variable rBB' : rk(couple B B')=2.
Variable rCC' : rk(couple C C')=2.


Lemma rA'O : rk(couple A' O)=2.
Proof.
eapply rk_triple_ABC_couple_AC; eauto.
Qed.

Lemma rB'O : rk(couple B' O)=2.
Proof.
eapply rk_triple_ABC_couple_BC; eauto.
Qed.

Lemma rC'O : rk(couple C' O)=2.
Proof.
eapply rk_triple_ABC_couple_BC; eauto.
Qed.

Lemma rAO : rk(couple A O)=2.
Proof.
eapply rk_triple_ABC_couple_AC; eauto.
Qed.

Lemma rBO : rk(couple B O)=2.
Proof.
eapply rk_triple_ABC_couple_BC; eauto.
Qed.

Lemma rCO : rk(couple C O)=2.
Proof.
eapply rk_triple_ABC_couple_BC; eauto.
Qed.

Hint Resolve rA'O rB'O rC'O rAO rBO rCO.

Lemma l1A'B'O : rk (triple A' B' O)=3.
Proof.
apply l1_scheme with (A:=A) (B:=B) (A':=A') (B':=B'); auto.
Qed.

Lemma l1A'C'O : rk (triple A' C' O)=3.
Proof.
apply l1_scheme with (A:=A) (B:=C) (A':=A') (B':=C'); auto.
Qed.

Lemma l1B'C'O : rk (triple B' C' O)=3.
Proof.
apply l1_scheme with (A:=B) (B:=C) (A':=B') (B':=C'); auto.
Qed.

Lemma l2rABOP : exists P:Point, rk(add P (triple A B O))>=4 /\ rk(couple O P)=2.
Proof.
assert (T:3 <= 3);auto.
elim (construction 3 (triple A B O) rABO T).
intros P HP.
exists P.
split.
omega.
apply rk_couple1.
intro H; rewrite H in *;clear H.
setoid_replace (add P (triple A B P)) with (triple A B P) in HP.
omega.
unfold Equal; split; fsetdecide_no_hyps.
Qed.

Section P_exists.
(* P will be instanciated using lemma l2rABOP *)
Variable P:Point.

Hypothesis rABOP: rk(add P (triple A B O))>=4 .
Hypothesis rOP : rk(couple O P)=2.

Lemma rACOP: rk(add P (triple A C O))>=4.
Proof.
setoid_replace (triple A C O) with (triple C A O) by fsetdecide.
apply (rk3_4 B A O C P).
apply le_antisym.
assert (rk (add C (triple B A O)) <= rk
                (union (triple A B C) (union (triple A' B' C') (singleton O)))).
apply matroid2; fsetdecide_no_hyps.
omega.
assert (rk (add C (triple B A O))>=rk (triple A B C)).
apply matroid2; fsetdecide_no_hyps.
omega.
setoid_replace (triple A O C) with (triple A C O) by fsetdecide_no_hyps; assumption. 
setoid_replace (triple B A O) with (triple A B O) by fsetdecide_no_hyps; assumption.
Qed.

Lemma rBCOP: rk(add P (triple B C O))>=4.
Proof.
setoid_replace (triple B C O) with (triple C B O) by fsetdecide.
apply (rk3_4 A B O C P).
apply le_antisym.
assert (rk (add C (triple A B O)) <= rk
                (union (triple A B C) (union (triple A' B' C') (singleton O)))).
apply matroid2; fsetdecide_no_hyps.
omega.
assert (rk (add C (triple A B O))>=rk (triple A B C)).
apply matroid2; fsetdecide_no_hyps.
omega.
setoid_replace (triple B O C) with (triple B C O) by fsetdecide_no_hyps; assumption.
assumption.
Qed.

Lemma l2rABMP : forall M:Point, M=C\/M=A'\/M=B' ->
rk(add P (triple A B M))>=4.
Proof.
intros M HM.
apply (l2rABMP_scheme  A' B' C' A B C O rABC rABCA'B'C'O rABO rAA'O rBB'O rAO rBO rAA' rBB' P rABOP); auto.
Qed.

Lemma l2rACMP : forall M:Point, M=B\/M=A'\/M=C' ->
rk(add P (triple A C M))>=4.
Proof.
intros M HM.
apply (l2rABMP_scheme  A' C' B' A C B O).
setoid_replace (triple A C B) with (triple A B C) by fsetdecide_no_hyps; assumption.
setoid_replace (triple A C B) with (triple A B C) by fsetdecide_no_hyps.
setoid_replace (triple A' C' B') with (triple A' B' C') by fsetdecide_no_hyps; assumption.
assumption.
assumption.
assumption.
auto.
auto.
assumption.
assumption.
apply rACOP.
intuition.
Qed.

Lemma l2rA'B'OP : rk(add P (triple A' B' O))>=4.
Proof.
assert (rk(union (triple A A' B') (couple O P))>=4).
generalize (matroid3 (union (triple A A' B') (couple O P)) (triple B B' O)).
assert (rk (inter (union (triple A A' B') (couple O P)) (triple B B' O)) >= rk(couple B' O)).
apply matroid2; fsetdecide_no_hyps.
assert (rk (union (union (triple A A' B') (couple O P)) (triple B B' O))>=rk (add P (triple A B O)) ).
apply matroid2; fsetdecide_no_hyps.
generalize rB'O; omega.
generalize (matroid3 (add P (triple A' B' O)) (triple A A' O)).
assert (rk (inter (add P (triple A' B' O)) (triple A A' O)) >= rk(couple A' O)).
apply matroid2; fsetdecide_no_hyps.
setoid_replace (union (add P (triple A' B' O)) (triple A A' O))  with (union (triple A A' B') (couple O P)) by (unfold Equal; split; fsetdecide_no_hyps).
generalize rA'O;omega.
Qed.

Lemma rA'C'OP: rk(add P (triple A' C' O))>=4.
Proof.
setoid_replace (triple A' C' O) with (triple C' A' O) by fsetdecide_no_hyps.
apply (rk3_4 B' A' O C' P).
apply le_antisym.
assert (rk (add C' (triple B' A' O)) <= rk
                (union (triple A B C) (union (triple A' B' C') (singleton O)))).
apply matroid2; fsetdecide_no_hyps.
omega.
assert (rk (add C' (triple B' A' O))>=rk (triple A' B' C')).
apply matroid2; fsetdecide_no_hyps.
omega.
setoid_replace (triple A' O C') with (triple A' C' O) by fsetdecide_no_hyps; assumption.
setoid_replace (triple B' A' O)  with (triple A' B' O) by fsetdecide_no_hyps.
apply l2rA'B'OP.
Qed.

Lemma rB'C'OP: rk(add P (triple B' C' O))>=4.
Proof.
setoid_replace (triple B' C' O) with (triple C' B' O) by fsetdecide_no_hyps.
apply (rk3_4 A' B' O C' P).
apply le_antisym.
assert (rk (add C' (triple A' B' O)) <= rk
                (union (triple A B C) (union (triple A' B' C') (singleton O)))).
apply matroid2; fsetdecide_no_hyps.
omega.
assert (rk (add C' (triple A' B' O))>=rk (triple A' B' C')).
apply matroid2; fsetdecide_no_hyps.
omega.
setoid_replace (triple B' O C') with (triple B' C' O) by fsetdecide; assumption.
apply l2rA'B'OP.
Qed.

Lemma ex_o : exists o:Point, rk(triple O P o)=2 /\ rk(couple O o)=2/\rk(couple P o)=2.
Proof.
assert (T:= three_points_on_lines O P).
firstorder.
Qed.

Section o_exists.
Variable o:Point.
Variable rko1: rk(triple o O P)=2.
Variable rko2: rk(couple O o)=2.
Variable rko3:rk(couple P o)=2.

Lemma rABOo : rk(add o (triple A B O))>=4.
Proof.
apply (rABOo_scheme A B O P); auto.
Qed.

Lemma rACOo : rk(add o (triple A C O))>=4.
Proof.
apply (rABOo_scheme A C O P); auto.
apply rACOP.
Qed.

Lemma rABCo : rk(add o (triple A B C))>=4.
Proof.
setoid_replace (triple A B C) with (triple C B A) by fsetdecide_no_hyps.
apply (rk3_4 O B  A C o).
setoid_replace  (add C (triple O B A)) with (add C (triple A B O)) by fsetdecide_no_hyps.
apply le_antisym.
assert (rk (add C (triple A B O)) <=rk
                (union (triple A B C) (union (triple A' B' C') (singleton O)))).
apply matroid2; fsetdecide_no_hyps.
omega.
assert (rk (add C (triple A B O))>=rk (triple A B C)).
apply matroid2; fsetdecide_no_hyps.
omega.
setoid_replace (triple B A C) with (triple A B C) by fsetdecide_no_hyps.
assumption.
setoid_replace (triple O B A) with (triple A B O) by fsetdecide_no_hyps.
apply rABOo.
Qed.

Lemma rACMo : forall M:Point, M=B\/M=A'\/M=C' -> 
rk(add o (triple A C M))>=4.
Proof.
apply (l2rABMP_scheme A' C' B' A C B O); auto.
setoid_replace (triple A C B) with (triple A B C) by fsetdecide_no_hyps ; assumption.
setoid_replace (triple A C B) with (triple A B C) by fsetdecide_no_hyps.
setoid_replace (triple A' C' B') with (triple A' B' C') by fsetdecide_no_hyps; assumption.
apply  rACOo.
Qed.

Lemma rA'B'Oo : rk(add o (triple A' B' O))>=4.
Proof.
apply (rABOo_scheme A' B' O P); auto.
apply l2rA'B'OP.
Qed.

Lemma rA'C'Oo : rk(add o (triple A' C' O))>=4.
Proof.
apply (rABOo_scheme A' C' O P); auto.
apply rA'C'OP.
Qed.

Lemma perm3 : forall x y z x' y' z' a, 
rk (union (triple x y z) (union (triple x' y' z') (singleton a)))=
rk (union (triple x' y' z') (union (triple x y z) (singleton a))).
Proof.
intros.
apply le_antisym.
apply matroid2; fsetdecide_no_hyps.
apply matroid2; fsetdecide_no_hyps.
Qed.

Lemma rA'B'Mo : forall M:Point, M=A\/M=B\/M=C' -> 
rk(add o (triple A' B' M))>=4.
Proof.
intros M HM.
apply (l2rABMP_scheme A B C A'  B' C' O) with (P:=o) (M:=M); auto.
rewrite perm3.
assumption.
setoid_replace (triple A' A O) with (triple A A' O) by fsetdecide_no_hyps ; assumption.
setoid_replace (triple B' B O) with (triple B B' O) by fsetdecide_no_hyps ; assumption.
setoid_replace (couple A' A) with (couple A A') by fsetdecide_no_hyps;assumption.
setoid_replace (couple B' B) with (couple B B') by fsetdecide_no_hyps;assumption.
apply rA'B'Oo.
decompose [or] HM; clear HM;auto.
Qed.

Lemma rA'C'Mo : forall M:Point, M=B'\/M=A\/M=C -> 
rk(add o (triple A' C' M))>=4.
Proof.
apply (l2rABMP_scheme A C B A' C' B' O) with (P:=o); auto.
setoid_replace (triple A' C' B') with (triple A' B' C') by fsetdecide_no_hyps; assumption.
rewrite perm3.
setoid_replace (triple A C B) with (triple A B C) by fsetdecide_no_hyps.
setoid_replace (triple A' C' B') with (triple A' B' C') by fsetdecide_no_hyps; assumption.
setoid_replace (triple A' A O) with (triple A A' O) by fsetdecide_no_hyps ; assumption.
setoid_replace (triple C' C O) with (triple C C' O) by fsetdecide_no_hyps ; assumption.
setoid_replace (couple A' A) with (couple A A') by fsetdecide_no_hyps;assumption.
setoid_replace (couple C' C) with (couple C C') by fsetdecide_no_hyps;assumption.
apply rA'C'Oo.
Qed.

Lemma rc : exists c:Point,
rk (triple o C c)=2  /\ rk (triple P C' c)=2.
Proof.
assert (Hrk : (rk(quadruple o C P C')<=3)).
generalize (matroid3 (triple C C' O) (triple o O P)).
assert (rk (union (triple C C' O) (triple o O P)) >= rk (quadruple o C P C')).
apply matroid2; fsetdecide_no_hyps.
assert (rk (inter (triple C C' O) (triple o O P))>= rk(singleton O)).
apply matroid2; fsetdecide_no_hyps.
rewrite rk_singleton in H0.
omega.
elim (pasch o C P C' Hrk).
intros I (HI1,HI2).
exists I; intuition.
Qed.

Section c_exists.

Variable c:Point.
Hypothesis rkc2 : rk(triple o C c)=2.
Hypothesis rkc2' : rk(triple P C' c)=2.

Lemma rCC'oPc : rk(union (triple C C' o) (couple P c))=3.
Proof.
apply (rCC'oPc_scheme A' B' C' A B C O); auto.
Qed.


Lemma rCC'oc : rk(add c (triple C C' o))=3.
Proof.
apply  (rCC'oc_scheme A' B' C' A B C O) with (P:=P); auto.
Qed.

Lemma rcC' : rk(couple c C')=2.
Proof.
apply (rcC'_scheme A' B' C' A B C O) with (P:=P) (o:=o); auto.
Qed.

Lemma rcC : rk(couple c C) = 2.
Proof.
apply (rcC_scheme A' B' C' A B C O) with (P:=P) (o:=o); auto.
Qed.

Lemma rABCc : rk(add c (triple A B C))>=4.
Proof.
apply (rABCc_scheme A' B' C' A B C O) with (P:=P) (o:=o); auto.
apply rABCo.
Qed.

Lemma rABOc : rk(add c (triple A B O))>=4.
Proof.
apply (rABOc_scheme A' B' C' A B C O) with (P:=P) (o:=o); auto.
apply rABCo.
Qed.

Lemma rco : rk(couple c o)=2.
Proof.
apply (rco_scheme A' B' C' A B C O) with (P:=P) (o:=o); auto.
apply l2rA'B'OP.
Qed.
End c_exists.

Lemma rb : exists b:Point, 
rk(triple o B b)=2/\rk(triple P B' b)=2.
Proof.
assert (Hrk : (rk(quadruple o B P B')<=3)).
generalize (matroid3 (triple B B' O) (triple o O P)).
assert (rk (union (triple B B' O) (triple o O P)) >= rk (quadruple o B P B')).
apply matroid2; fsetdecide_no_hyps.
assert (rk (inter (triple B B' O) (triple o O P))>= rk(singleton O)).
apply matroid2; fsetdecide_no_hyps.
rewrite rk_singleton in H0.
omega.
elim (pasch o B P B' Hrk).
intros I (HI1,HI2).
exists I; intuition.
Qed.


Section b_exists.

Variable b:Point.
Hypothesis rkb2 : rk(triple o B b)=2.
Hypothesis rkb2' : rk(triple P B' b)=2.


Lemma rABOb : rk(add b (triple A B O))>=4.
Proof.
assert (rk (add b (triple A C O)) >= 4).
apply (rABOc_scheme A' C' B' A  C  B O) with (P:=P) (o:=o) (c:=b); try assumption.
setoid_replace (triple A C B) with (triple A B C) by fsetdecide_no_hyps ; assumption.
setoid_replace (triple A C B) with (triple A B C) by fsetdecide_no_hyps.
setoid_replace (triple A' C' B') with (triple A' B' C') by fsetdecide_no_hyps.
assumption.
apply rACOP.
setoid_replace (triple A C B) with (triple A B C) by fsetdecide_no_hyps.
apply rABCo.
setoid_replace (triple A B O) with (triple B O A) by fsetdecide_no_hyps.
apply (rk3_4 C O A B b).
apply le_antisym.
rewrite <- rABCA'B'C'O.
apply matroid2; fsetdecide_no_hyps.
rewrite <- rABC.
apply matroid2; fsetdecide_no_hyps.
setoid_replace (triple O A B) with (triple A B O) by fsetdecide_no_hyps ; assumption.
setoid_replace (triple C O A)  with (triple A C O) by fsetdecide_no_hyps; assumption.
Qed.

Lemma rbo :rk(couple b o)=2.
Proof.
apply (rco_scheme A' C' B' A C B O) with (P:=P) (o:=o); auto.
setoid_replace (triple A' C' B') with (triple A' B' C') by fsetdecide_no_hyps; assumption.
setoid_replace (triple A C B)  with (triple A B C) by fsetdecide_no_hyps.
setoid_replace (triple A' C' B') with (triple A' B' C') by fsetdecide_no_hyps; assumption.
apply rACOP.
apply rA'C'OP.
Qed.

End b_exists.

Lemma ra : exists a:Point,
rk(triple o A a)=2/\rk(triple P A' a)=2. 
Proof.
assert (Hrk : (rk(quadruple o A P A')<=3)).
generalize (matroid3 (triple A A' O) (triple o O P)).
assert (rk (union (triple A A' O) (triple o O P)) >= rk (quadruple o A P A')).
apply matroid2; fsetdecide_no_hyps.
assert (rk (inter (triple A A' O) (triple o O P))>= rk(singleton O)).
apply matroid2; fsetdecide_no_hyps.
rewrite rk_singleton in H0.
omega.
elim (pasch o A P A' Hrk).
intros I (HI1,HI2).
exists I; intuition.
Qed.


Section a_exists.

Variable a:Point.
Hypothesis rka2 : rk(triple o A a)=2.
Hypothesis rka2' : rk(triple P A' a)=2.

Lemma rABCa : rk(add a (triple A B C))>=4.
Proof.
setoid_replace (triple A B C) with (triple C B A) by fsetdecide_no_hyps.
apply (rABCc_scheme C' B' A' C B A O) with (P:=P) (o:=o); auto.
setoid_replace (triple C B A) with (triple A B C) by fsetdecide_no_hyps; assumption.
setoid_replace (triple C B A) with (triple A B C) by fsetdecide_no_hyps.
setoid_replace (triple C' B' A') with (triple A' B' C') by fsetdecide_no_hyps; assumption.
setoid_replace (triple C A O) with (triple A C O) by fsetdecide_no_hyps; assumption.
eapply rk3_4; try eassumption.
apply le_antisym.
rewrite <- rABCA'B'C'O.
apply matroid2; fsetdecide_no_hyps.
rewrite <- rABC.
apply matroid2; fsetdecide_no_hyps.
setoid_replace (triple B O C) with (triple B C O) by fsetdecide_no_hyps; assumption.
setoid_replace (triple C B A) with (triple A B C) by fsetdecide_no_hyps. 
apply rABCo.
Qed.

Lemma rao: rk(couple a o)=2.
Proof.
apply (rco_scheme C' B' A' C B A O) with (P:=P) (o:=o); auto.
setoid_replace (triple C' B' A') with (triple A' B' C') by fsetdecide_no_hyps; assumption.
setoid_replace (triple C B A) with (triple A B C) by fsetdecide_no_hyps.
setoid_replace (triple C' B' A') with (triple A' B' C') by fsetdecide_no_hyps; assumption.
setoid_replace (triple C A O) with (triple A C O) by fsetdecide_no_hyps; assumption.
setoid_replace (triple C B O) with (triple B C O) by fsetdecide_no_hyps.
apply rBCOP.
setoid_replace (triple C' B' O) with (triple B' C' O) by fsetdecide_no_hyps.
apply rB'C'OP.
Qed.

End a_exists.

End o_exists.
End P_exists.

End desargues_plane.

End Desargues2Dlemmas2.