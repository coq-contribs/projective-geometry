Require Export basic_facts_plane.

Module back (M: ProjectivePlane') : ProjectivePlane
with Definition Point := M.Point
with Definition Line := M.Line
with Definition Incid := M.Incid.

Definition Point := M.Point.
Definition Line := M.Line.
Definition Incid := M.Incid.

Definition incid_dec := M.incid_dec.
Definition a1_exist := M.a1_exist.
Definition a2_exist := M.a2_exist.
Definition uniqueness := M.uniqueness.

Module Import uniq := uniqueness_axioms M.

(** M and P are the same and lie at the meeting point between l1 and l2 **)

Lemma case1 : forall M N O P Q R : Point, forall l1 l2 : Line, 
  l1 <> l2 -> 
  dist3 M N O /\ Incid M l1 /\ Incid N l1 /\ Incid O l1 ->
  dist3 P Q R /\ Incid P l2 /\ Incid Q l2 /\ Incid R l2 ->
  Incid M l2 -> Incid P l1 -> 
  {A : Point & {B : Point & {C : Point & {D : Point |
          forall l : Line,
            dist4 A B C D /\
            (Incid A l /\ Incid B l -> ~ Incid C l /\ ~ Incid D l) /\
            (Incid A l /\ Incid C l -> ~ Incid B l /\ ~ Incid D l) /\
            (Incid A l /\ Incid D l -> ~ Incid C l /\ ~ Incid B l) /\
            (Incid C l /\ Incid B l -> ~ Incid A l /\ ~ Incid D l) /\
            (Incid D l /\ Incid B l -> ~ Incid C l /\ ~ Incid A l) /\
            (Incid C l /\ Incid D l -> ~ Incid B l /\ ~ Incid A l)}}}}.
intros M N O P Q R l1 l2 H1 H2 H3 HMl2 HPl1.
unfold dist3 in H2,H3.
intuition.
assert (~Incid N l2).
intro HNl2.
generalize (a2_unique l1 l2 M N H1 H HMl2 H5 HNl2); intros H'.
subst M.
apply H3; trivial.
assert (~Incid O l2).
intro HOl2.
generalize (a2_unique l1 l2 M O H1 H HMl2 H10 HOl2); intros H'.
subst M.
apply H4; trivial.
assert (~Incid Q l1).
intros HQl1.
generalize (a2_unique l1 l2 P Q H1 HPl1 H2 HQl1 H7); intros H'.
subst P.
apply H0; trivial.
assert (~Incid R l1).
intros HRl1.
generalize (a2_unique l1 l2 P R H1 HPl1 H2 HRl1 H12); intros H'.
subst P.
apply H6; trivial.
exists N. 
exists O. 
exists Q. 
exists R.
intros l.
split.
split.
assumption.
split.
intros HNQ.
subst N.
tauto.
split.
intros HNR.
subst N.
tauto.
split.
intros HOQ.
subst O.
tauto.
split.
intros HOR.
subst O.
tauto.
assumption.
split.
intros (Hnew1, Hnew2).
generalize (a1_unique N O l l1 H9 Hnew1 Hnew2 H5 H10); intros H'.
subst l.
tauto.
split.
intros (Hnew1, Hnew2).
split.
intros HOl.

generalize (a1_unique N O l l1 H9 Hnew1 HOl H5 H10); intros H'.
subst l.
tauto.
intros HRl.
generalize (a1_unique Q R l l2 H11 Hnew2 HRl H7 H12) ; intros H'.
subst l.
tauto.

split.
intros (Hnew1,Hnew2).
split.
intros HQl.
generalize (a1_unique Q R l l2 H11 HQl Hnew2 H7 H12) ; intros H'.
subst l.
tauto.
intros HOl.
generalize (a1_unique N O l l1 H9 Hnew1 HOl H5 H10); intros H'.
subst l.
tauto.
 
split.
intros (Hnew1, Hnew2).
split.
intros HNl.
generalize (a1_unique N O l l1 H9 HNl Hnew2 H5 H10); intros H'.
subst l.
tauto.
intros HRl.
generalize (a1_unique Q R l l2 H11 Hnew1 HRl H7 H12) ; intros H'.
subst l.
tauto.

split.
intros (Hnew1,Hnew2).
split.
intros HQl.
generalize (a1_unique Q R l l2 H11 HQl Hnew1 H7 H12) ; intros H'.
subst l.
tauto.
intros HNl.
generalize (a1_unique N O l l1 H9 HNl Hnew2 H5 H10); intros H'.
subst l.
tauto.
intros (Hnew1, Hnew2).
generalize (a1_unique Q R l l2 H11 Hnew1 Hnew2 H7 H12) ; intros H'.
subst l.
tauto.
Qed.

Lemma case2 : forall M N O P Q R : Point, forall l1 l2 : Line, 
  l1 <> l2 -> 
  dist3 M N O /\ Incid M l1 /\ Incid N l1 /\ Incid O l1 ->
  dist3 P Q R /\ Incid P l2 /\ Incid Q l2 /\ Incid R l2 ->
  Incid M l2 -> ~Incid P l1 -> ~Incid Q l1 -> ~Incid R l1 -> 
  {A : Point & {B : Point & {C : Point & {D : Point |
          forall l : Line,
            dist4 A B C D /\
            (Incid A l /\ Incid B l -> ~ Incid C l /\ ~ Incid D l) /\
            (Incid A l /\ Incid C l -> ~ Incid B l /\ ~ Incid D l) /\
            (Incid A l /\ Incid D l -> ~ Incid C l /\ ~ Incid B l) /\
            (Incid C l /\ Incid B l -> ~ Incid A l /\ ~ Incid D l) /\
            (Incid D l /\ Incid B l -> ~ Incid C l /\ ~ Incid A l) /\
            (Incid C l /\ Incid D l -> ~ Incid B l /\ ~ Incid A l)}}}}.
intros M N O P Q R l1 l2 H1 H2 H3 HMl2 HPl1 HQl1 HRl1.
unfold dist3 in H2,H3.
intuition.
assert (~Incid N l2).
intro HNl2.
generalize (a2_unique l1 l2 M N H1 H HMl2 H5 HNl2); intros H'.
subst M.
apply H3; trivial.
assert (~Incid O l2).
intro HOl2.
generalize (a2_unique l1 l2 M O H1 H HMl2 H10 HOl2); intros H'.
subst M.
apply H4; trivial.
exists N.
exists R.
exists Q.
exists O.
intros l.
split.
unfold dist4.
split.
intros HNR; subst N; tauto.
split.
intros HNR; subst N; tauto.
split.
assumption.
split.
intros HRQ; apply H11.
symmetry;trivial.
split.
intros HRO; subst R.
tauto.
intros HQO; subst Q.
tauto.
split.
intros (Hnew1,Hnew2).  
split.
intros HQl.
generalize (a1_unique Q R l l2 H11 HQl Hnew2 H7 H12); intros H'.
subst l.
tauto.
intros HOl.
generalize (a1_unique N O l l1 H9 Hnew1 HOl H5 H10); intros H'. 
subst l.
tauto.
split.
intros (Hnew1, Hnew2).
split.
intros HRl.
generalize (a1_unique Q R l l2 H11 Hnew2 HRl H7 H12); intros H'.
subst l.
tauto.
intros HOl.
generalize (a1_unique N O l l1 H9 Hnew1 HOl H5 H10); intros H'. 
subst l.
tauto.
split.
intros (Hnew1, Hnew2).
generalize (a1_unique N O l l1 H9 Hnew1 Hnew2 H5 H10); intros H'. 
subst l.
tauto.
split.
intros (Hnew1, Hnew2).
generalize (a1_unique Q R l l2 H11 Hnew1 Hnew2 H7 H12); intros H'.
subst l.
tauto.
split.
intros (Hnew1, Hnew2).
split.
intros HQl.
generalize (a1_unique Q R l l2 H11 HQl Hnew2 H7 H12); intros H'.
subst l.
tauto.
intros HNl.
generalize (a1_unique N O l l1 H9 HNl Hnew1 H5 H10); intros H'. 
subst l.
tauto.
intros (Hnew1, Hnew2).
split.
intros HRl.
generalize (a1_unique Q R l l2 H11 Hnew1 HRl H7 H12); intros H'.
subst l.
tauto.
intros HNl.
generalize (a1_unique N O l l1 H9 HNl Hnew2 H5 H10); intros H'. 
subst l.
tauto.
Qed.

(** case2 with l1 and l2 inverted *)
Lemma case3 : forall M N O P Q R : Point, forall l1 l2 : Line, 
  l1 <> l2 -> 
  dist3 M N O /\ Incid M l1 /\ Incid N l1 /\ Incid O l1 ->
  dist3 P Q R /\ Incid P l2 /\ Incid Q l2 /\ Incid R l2 ->
  Incid P l1 -> ~Incid M l2 -> ~Incid N l2 -> ~Incid O l2 -> 
  {A : Point & {B : Point & {C : Point & {D : Point |
          forall l : Line,
            dist4 A B C D /\
            (Incid A l /\ Incid B l -> ~ Incid C l /\ ~ Incid D l) /\
            (Incid A l /\ Incid C l -> ~ Incid B l /\ ~ Incid D l) /\
            (Incid A l /\ Incid D l -> ~ Incid C l /\ ~ Incid B l) /\
            (Incid C l /\ Incid B l -> ~ Incid A l /\ ~ Incid D l) /\
            (Incid D l /\ Incid B l -> ~ Incid C l /\ ~ Incid A l) /\
            (Incid C l /\ Incid D l -> ~ Incid B l /\ ~ Incid A l)}}}}.
intros M N O P Q R l1 l2 H1 H2 H3 HPl1 HMl2 HNl2 HOl2.
eapply case2 with (l1:=l2) (l2:=l1);eauto.
Qed.

(** none of M, N, O, P, Q, and R are at the meeting point of l1 and l2 *)
Lemma case4 : forall M N O P Q R : Point, forall l1 l2 : Line, 
  l1 <> l2 -> 
  dist3 M N O /\ Incid M l1 /\ Incid N l1 /\ Incid O l1 ->
  dist3 P Q R /\ Incid P l2 /\ Incid Q l2 /\ Incid R l2 ->
  ~Incid P l1 -> ~Incid Q l1 -> ~Incid R l1 -> ~Incid M l2 -> ~Incid N l2 -> ~Incid O l2 -> 
  {A : Point & {B : Point & {C : Point & {D : Point |
          forall l : Line,
            dist4 A B C D /\
            (Incid A l /\ Incid B l -> ~ Incid C l /\ ~ Incid D l) /\
            (Incid A l /\ Incid C l -> ~ Incid B l /\ ~ Incid D l) /\
            (Incid A l /\ Incid D l -> ~ Incid C l /\ ~ Incid B l) /\
            (Incid C l /\ Incid B l -> ~ Incid A l /\ ~ Incid D l) /\
            (Incid D l /\ Incid B l -> ~ Incid C l /\ ~ Incid A l) /\
            (Incid C l /\ Incid D l -> ~ Incid B l /\ ~ Incid A l)}}}}.
intros M N O P Q R l1 l2 H1 H2 H3 HPl1 HQl1 HRl1 HMl2 HNl2 HOl2.
unfold dist3 in H2,H3.
intuition.
exists N.
exists R.
exists Q.
exists O.
intros l.
split.
unfold dist4.
split.
intros HNR; subst N; tauto.
split.
intros HNR; subst N; tauto.
split.
assumption.
split.
intros HRQ; apply H11.
symmetry;trivial.
split.
intros HRO; subst R.
tauto.
intros HQO; subst Q.
tauto.
split.
intros (Hnew1,Hnew2).  
split.
intros HQl.
generalize (a1_unique Q R l l2 H11 HQl Hnew2 H7 H12); intros H'.
subst l.
tauto.
intros HOl.
generalize (a1_unique N O l l1 H9 Hnew1 HOl H5 H10); intros H'. 
subst l.
tauto.
split.
intros (Hnew1, Hnew2).
split.
intros HRl.
generalize (a1_unique Q R l l2 H11 Hnew2 HRl H7 H12); intros H'.
subst l.
tauto.
intros HOl.
generalize (a1_unique N O l l1 H9 Hnew1 HOl H5 H10); intros H'. 
subst l.
tauto.
split.
intros (Hnew1, Hnew2).
generalize (a1_unique N O l l1 H9 Hnew1 Hnew2 H5 H10); intros H'. 
subst l.
tauto.
split.
intros (Hnew1, Hnew2).
generalize (a1_unique Q R l l2 H11 Hnew1 Hnew2 H7 H12); intros H'.
subst l.
tauto.
split.
intros (Hnew1, Hnew2).
split.
intros HQl.
generalize (a1_unique Q R l l2 H11 HQl Hnew2 H7 H12); intros H'.
subst l.
tauto.
intros HNl.
generalize (a1_unique N O l l1 H9 HNl Hnew1 H5 H10); intros H'. 
subst l.
tauto.
intros (Hnew1, Hnew2).
split.
intros HRl.
generalize (a1_unique Q R l l2 H11 Hnew1 HRl H7 H12); intros H'.
subst l.
tauto.
intros HNl.
generalize (a1_unique N O l l1 H9 HNl Hnew2 H5 H10); intros H'. 
subst l.
tauto.
Qed.

Definition a3 : {A:Point & {B :Point & {C:Point & {D :Point |
  (forall l :Line, dist4 A B C D/\ 
    (Incid A l /\ Incid B l -> ~Incid C l /\ ~Incid D l)
    /\ (Incid A l /\ Incid C l -> ~Incid B l /\ ~Incid D l)
    /\  (Incid A l /\ Incid D l -> ~Incid C l /\ ~Incid B l)
    /\  (Incid C l /\ Incid B l -> ~Incid A l /\ ~Incid D l)
    /\ (Incid D l /\ Incid B l -> ~Incid C l /\ ~Incid A l)
    /\  (Incid C l /\ Incid D l -> ~Incid B l /\ ~Incid A l))}}}}.
generalize M.a3_1 M.a3_2.
intros H1 H2.
elim H2; clear H2; intros l1 Hl1.
elim Hl1; clear Hl1; intros l2 HdistL.
generalize (H1 l1); intros Hl1.
generalize (H1 l2); intros Hl2.
clear H1.
elim Hl1; clear Hl1; intros A1 HA1.
elim HA1; clear HA1; intros B1 HB1.
elim HB1; clear HB1; intros C1 H1.
elim Hl2; clear Hl2; intros A2 HA2.
elim HA2; clear HA2; intros B2 HB2.
elim HB2; clear HB2; intros C2 H2.
elim (incid_dec A1 l2).
elim (incid_dec A2 l1).
intros Ha Hb.
eapply case1;eauto.
intros Ha Hb.
elim (incid_dec B1 l2).
intros Hc.
assert (~Incid B1 l2).
intuition.
generalize (a2_unique l1 l2 A1 B1 HdistL H2 Hb H4 Hc); intros H'.
subst A1.
unfold dist3 in H0.
tauto.
tauto.
intros Hc.
elim (incid_dec C1 l2).
intros Hd.
assert (~Incid C1 l2).
intuition.
generalize (a2_unique l1 l2 A1 C1 HdistL H2 Hb H7 Hd); intros H'.
subst A1.
unfold dist3 in H0.
tauto.
tauto.
intros Hd.
elim (incid_dec B2 l1).
intros H.
eapply case1 with (M:=A1) (N:=B1) (O:=C1) (P:=B2) (Q:=A2) (R:=C2);eauto;unfold dist3 in *;intuition.
intros He.
elim (incid_dec C2 l1).
intros H.
eapply case1 with (M:=A1) (N:=B1) (O:=C1) (P:=C2) (Q:=A2) (R:=B2);eauto;unfold dist3 in *;intuition.
intros Hf.
eapply case2;eauto.
intros Ha.
elim (incid_dec B1 l2).
intros Hb.
elim (incid_dec A2 l1).
intros Hc.
eapply case1 with (M:=B1) (N:=A1) (O:=C1) (P:=A2) (Q:=B2) (R:=C2);eauto;unfold dist3 in *;intuition.
intros Hc.
elim (incid_dec B2 l1).
intros Hd.
eapply case1 with (M:=B1) (N:=A1) (O:=C1) (P:=B2) (Q:=A2) (R:=C2);eauto;unfold dist3 in *;intuition.
intros He.
elim (incid_dec C2 l1).
intros Hf.
eapply case1 with (M:=B1) (N:=A1) (O:=C1) (P:=C2) (Q:=A2) (R:=B2);eauto;unfold dist3 in *;intuition.
intros Hf.
eapply case2 with (M:=B1) (N:=A1) (O:=C1) (P:=A2) (Q:=B2) (R:=C2);eauto;unfold dist3 in *;intuition.
intros Hb.
elim (incid_dec C1 l2).
intros Hc.
elim (incid_dec A2 l1).
intros Hd.
eapply case1 with (M:=C1) (N:=A1) (O:=B1) (P:=A2) (Q:=B2) (R:=C2);eauto;unfold dist3 in *;intuition.
intros Hd.
elim (incid_dec B2 l1).
intros He.
eapply case1 with (M:=C1) (N:=A1) (O:=B1) (P:=B2) (Q:=A2) (R:=C2);eauto;unfold dist3 in *;intuition.
intros He.
elim (incid_dec C2 l1).
intros Hf.
eapply case1 with (M:=C1) (N:=A1) (O:=B1) (P:=C2) (Q:=A2) (R:=B2);eauto;unfold dist3 in *;intuition.
intros Hf.
eapply case2 with (M:=C1) (N:=A1) (O:=B1) (P:=A2) (Q:=B2) (R:=C2);eauto;unfold dist3 in *;intuition.
intros Hc.
elim (incid_dec A2 l1).
intros Hd.
eapply case3 with (M:=A1) (N:=B1) (O:=C1) (P:=A2) (Q:=B2) (R:=C2);eauto;unfold dist3 in *;intuition.
intros Hd.
elim (incid_dec B2 l1).
intros He.
eapply case3 with (M:=A1) (N:=B1) (O:=C1) (P:=B2) (Q:=A2) (R:=C2);eauto;unfold dist3 in *;intuition.
intros He.
elim (incid_dec C2 l1).
intros Hf.
eapply case3 with (M:=A1) (N:=B1) (O:=C1) (P:=C2) (Q:=A2) (R:=B2);eauto;unfold dist3 in *;intuition.
intros Hf.
eapply case4;eauto.
Qed.


End back.
