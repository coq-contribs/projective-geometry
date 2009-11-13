Require Export projective_plane_inst.

Module Export uniq := (uniqueness_axioms AbstractProjectivePlane).
 
Lemma Incid_property : 
forall A B C D : Point,
A <> B ->
forall L1 L2: Line, 
  Incid A L1 -> Incid B L1 -> Incid C L1 ->
  Incid A L2 -> Incid B L2 -> Incid D L2 ->
  exists L3 : Line, 
    (Incid A L3)/\(Incid B L3)/\(Incid C L3)/\(Incid D L3).
intros A B C D.
intros Hdistincts.
intros D1 D2.
intros HAD1 HBD1 HCD1 HAD2 HBD2 HDD2.
intuition.
elim (a1_exist A B).
intros L1 HL1.
cut ((D1=L1)/\(D2=L1)).
intros (HD1,HD2).
exists L1.
pattern L1 at 1 2 3; rewrite <-HD1.
rewrite <- HD2.
intuition.
split.
apply (a1_unique A B);intuition.
apply (a1_unique A B);intuition.
Qed.

Theorem c :
  (exists A:Point,exists B:Point,exists C:Point,exists D:Point, dist4 A B C D) ->
  (exists M:Point,exists N:Point,exists P:Point,exists l:Line,
    dist3 M N P/\Incid M l/\Incid N l/\Incid P l).
intros.
elim H;clear H.
intros A.
intros Ha.
elim Ha;clear Ha.
intros B.
intros Hb.
elim Hb;clear Hb.
intros C.
intros Hc.
elim Hc;clear Hc.
intros D.
intros H.

generalize(a1_exist A B).
intros Hl1;elim Hl1; clear Hl1.
intros l1 Hl1.
assert(A <> B).
unfold dist4 in H.
tauto.
elim (incid_dec C l1).
intros HCl1.
exists A.
exists B.
exists C.
exists l1.
unfold dist3.
unfold dist4 in H.
tauto.
intros HCl1.
elim (incid_dec D l1).
intros HDl1.
exists A.
exists B.
exists D.
exists l1.
unfold dist3.
unfold dist4 in H.
tauto.
intros HDl1.

generalize(a1_exist C D).
intros Hl2;elim Hl2; clear Hl2.
intros l2 Hl2.
intros.
assert(C <> D).
unfold dist4 in H.
tauto.
elim (incid_dec A l2).
intros HAl2.
exists C.
exists D.
exists A.
exists l2.
unfold dist3.
unfold dist4 in *.
intuition. (* tauto failed ??? *)
intros HAl2.
elim (incid_dec B l2).
intros HBl2.
exists C.
exists D.
exists B.
exists l2.
unfold dist3.
unfold dist4 in *.
solve [intuition].
intros HBl2. 
generalize (a2_exist l1 l2).
intros HI.
assert (l1 <> l2).
intros Hl1l2.
subst l1.
apply HAl2.
tauto.
elim HI; clear HI; intros I HI.
exists I.
exists C.
exists D.
exists l2.
unfold dist3.
unfold dist4 in H.
split.
split.
intros HIC.
subst I.
tauto.
split.
intros HID.
subst I.
tauto.
tauto.
tauto.
Qed.
