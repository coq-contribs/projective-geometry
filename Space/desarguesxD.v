Require Export desargues2Dmore.
Require Export desargues3Dspecial.

Module DesarguesxD (DecPoints: FSetInterface.WS) (M: RankProjectiveSpace DecPoints).

Module Export Desargues_2D := Desargues2Dfinal2 DecPoints M.
Module Export Desargues_3D := Desargues3Dspecial DecPoints M.

Section desargues_theorem.
Variables A' B' C' : Point.
Variables A B C : Point.

Variables O : Point.

Variable rABC : rk(triple A B C)=3.
Variable rA'B'C' : rk(triple A' B' C')=3.

Variable rABO : rk(triple A B O)=3.
Variable rACO :rk(triple A C O)=3.
Variable rBCO : rk (triple B C O)=3.

Variable rAA'O : rk(triple A A' O)=2.
Variable rBB'O : rk(triple B B' O)=2.
Variable rCC'O : rk(triple C C' O)=2.

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

Lemma Desargues_xD : rk (triple alpha beta gamma) <= 2.
Proof.
assert  (rk(union (triple A B C) (triple A' B' C'))=3 \/
rk(union (triple A B C) (triple A' B' C'))>=4).
assert (rk(union (triple A B C) (triple A' B' C'))>=3).
rewrite <- rABC.
apply matroid2; fsetdecide_no_hyps.
omega. 
elim H.
intro rABCA'B'C'.
assert (rk(union (triple A B C) (union (triple A' B' C') (singleton O)))=3 ).
clear H.
apply le_antisym.
setoid_replace (union (triple A B C) (union (triple A' B' C') (singleton O))) with
(add O (union (triple A B C) (triple A' B' C'))) by fsetdecide_no_hyps.
apply (stays_in_plane (union (triple A B C) (triple A' B' C')) A A' O); auto.
omega.
fsetdecide_no_hyps.
fsetdecide_no_hyps.
rewrite <- rABC.
apply matroid2; fsetdecide_no_hyps.
rename H0 into rABCA'B'C'O.

eapply (Desargues_plane A' B' C' A B C O);assumption.

intro.
eapply (Desargues A B C A' B' C' alpha beta gamma O); auto.
setoid_replace (union (triple A' B' C') (triple A B C)) with (union (triple A B C) (triple A' B' C')) by (unfold Equal; split; fsetdecide_no_hyps).
omega.
Qed.

End desargues_theorem.

Check Desargues_xD.

Lemma Desargues_xD'
     : forall A' B' C' A B C O0 : Point,
       rk (triple A B C) = 3 ->
       rk (triple A' B' C') = 3 ->
       rk (triple A B O0) = 3 ->
       rk (triple A C O0) = 3 ->
       rk (triple B C O0) = 3 ->
       rk (triple A A' O0) = 2 ->
       rk (triple B B' O0) = 2 ->
       rk (triple C C' O0) = 2 ->
       rk (couple A A') = 2 ->
       rk (couple B B') = 2 ->
       rk (couple C C') = 2 ->
       forall alpha beta gamma : Point,
       rk (triple A B gamma) = 2 ->
       rk (triple A' B' gamma) = 2 ->
       rk (triple A C beta) = 2 ->
       rk (triple A' C' beta) = 2 ->
       rk (triple B C alpha) = 2 ->
       rk (triple B' C' alpha) = 2 -> rk (triple alpha beta gamma) <= 2.
exact Desargues_xD.
Qed.

End DesarguesxD.


