Require Export basic_facts_plane.

Module forth (M: ProjectivePlane) : ProjectivePlane'
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

Module Export uniq := uniqueness_axioms M.

(*
Cas 1 : 2 points sont sur L, 2 points n'y sont pas. Dans ce cas, on construit l'intersection de la ligne engendree
par les 2 points qui ne sont pas sur L. Cela donne 3 points alignes sur L. Ce point d'intersection ne peut pas etre
confondu avec un des 2 points deja  presents sur L, sinon on aura trois points alignes, ce qui est impossible par hypothese.
*)

Lemma cas1:forall (A B C D : Point)(l:Line),
  dist4 A B C D/\ Incid A l /\Incid B l /\ ~Incid C l /\ ~Incid D l  -> 
  (forall m : Line,
       dist4 A B C D /\
       (Incid A m /\ Incid B m -> ~ Incid C m /\ ~ Incid D m) /\
       (Incid A m /\ Incid C m -> ~ Incid B m /\ ~ Incid D m) /\
       (Incid A m /\ Incid D m -> ~ Incid C m /\ ~ Incid B m) /\
       (Incid C m /\ Incid B m -> ~ Incid A m /\ ~ Incid D m) /\
       (Incid D m /\ Incid B m -> ~ Incid C m /\ ~ Incid A m) /\
       (Incid C m /\ Incid D m -> ~ Incid B m /\ ~ Incid A m)) -> 
  {E:Point |dist3 A B E/\Incid E l}.
intros A B C D l H HIncid.
elim (a1_exist C D).
intros l1 Hl1.
assert(C <> D) by (unfold dist4 in H; tauto).

elim (a2_exist l l1).
intros E HE.
exists E.
split.

unfold dist3.
split.
unfold dist4 in H; tauto.

split.
intros HAE.
subst E.
generalize (HIncid l1); intros H'.
tauto.

intros HBE.
subst E.
generalize (HIncid l1); intros H'.
tauto.

tauto.

Qed.
(* Cas 2 : 1 point sur L, 3 points n'y sont pas. Il faut construire 2 points de L 
   par intersection avec des lignes engendrees par les points n'appartenant pas a  L. 
   Il faut faire des cas sur les points choisis et les risques d'alignement. 
*)

Lemma cas2:forall (A B C D : Point)(l:Line),
  dist4 A B C D /\ Incid A l /\ ~Incid B l /\ ~Incid C l /\ ~Incid D l ->
  (forall m : Line,
       dist4 A B C D /\
       (Incid A m /\ Incid B m -> ~ Incid C m /\ ~ Incid D m) /\
       (Incid A m /\ Incid C m -> ~ Incid B m /\ ~ Incid D m) /\
       (Incid A m /\ Incid D m -> ~ Incid C m /\ ~ Incid B m) /\
       (Incid C m /\ Incid B m -> ~ Incid A m /\ ~ Incid D m) /\
       (Incid D m /\ Incid B m -> ~ Incid C m /\ ~ Incid A m) /\
       (Incid C m /\ Incid D m -> ~ Incid B m /\ ~ Incid A m)) ->
  {E:Point &{F:Point |
    dist3 A E F/\Incid E l /\ Incid F l}}.
intros A B C D l H Hincid.
elim (a1_exist B C).
intros d1 Hd1.
assert (B<>C).
unfold dist4 in H; tauto.
elim (a2_exist l d1).
intros IBC HIBC.
elim (incid_dec A d1).
intros HAd1.

elim (Hincid d1).
tauto.
intros HAd1.

elim (a1_exist B D).
intros d2 Hd2.
assert (B<>D) by (unfold dist4 in H; tauto).
elim (a2_exist l d2).
intros IBD HIBD.
elim (incid_dec A d2).
intros HAd2.
elim (Hincid d2).
tauto.
intros HAd2.
exists IBC. 
exists IBD.
split.
unfold dist3.
split.
intros HAIBC.
subst.
apply HAd1.
tauto.
split.
intros HAIBD.
subst.
apply HAd1.
tauto.
assert (d1 <> d2).
intros Hd1d2.
subst.
elim (Hincid d2); tauto.

elim Hd1; intros Hd1B Hd1C.
elim Hd2; intros Hd2B Hd2D.
elim HIBC; intros HIBCl HIBCd1.
elim (incid_dec IBC d2).
intros HIBCd2.

generalize (a2_unique d1 d2 B IBC H2 Hd1B Hd2B HIBCd1 HIBCd2).
intros HBIBC.
subst.
assert (IBD<>IBC).
intuition.
eapply incidABl with (l:=l). 
tauto.
intros HIBDd2.

intros H'.
subst.
apply HIBDd2.
tauto.
split.
tauto.
tauto.
Qed.
(* Cas 3 : 0 point sur L, 4 points n'y sont pas. On doit mener le meme raisonnement 
   que pour le cas 2, mais avec un plus grand nombre de sous-cas. 
*)


Lemma cas3:forall (A B C D : Point)(l:Line),
  dist4 A B C D/\ ~Incid A l /\~Incid B l /\ ~Incid C l /\ ~Incid D l ->
  (forall m : Line,
    dist4  A B C D /\
    (Incid A m /\ Incid B m -> ~ Incid C m /\ ~ Incid D m) /\
    (Incid A m /\ Incid C m -> ~ Incid B m /\ ~ Incid D m) /\
    (Incid A m /\ Incid D m -> ~ Incid C m /\ ~ Incid B m) /\
    (Incid C m /\ Incid B m -> ~ Incid A m /\ ~ Incid D m) /\
    (Incid D m /\ Incid B m -> ~ Incid C m /\ ~ Incid A m) /\
    (Incid C m /\ Incid D m -> ~ Incid B m /\ ~ Incid A m)) ->
  {E:Point & {F:Point & {G:Point |
    dist3 E F G/\Incid E l/\Incid F l/\Incid G l}}}.
intros A B C D l H Hincid.
elim(a1_exist A B).
intros l1 Hl1.

elim(a1_exist A C).
intros l2 Hl2.

elim(a1_exist A D).
intros l3 Hl3.

elim (a2_exist l l1).
intros I HI.
elim (a2_exist l l2).
intros J HJ.
elim (a2_exist l l3).
intros K HK.

elim HI; intros HIl HIl1.
elim HJ; intros HJl HJl2.
(* 1 *)
elim (incid_dec I l2).
intros HIl2.
assert (Hl1l2 : l<>l2).
intros Hl1l2.
subst.
elim (Hincid l2); tauto.
generalize (a2_unique l l2 I J Hl1l2 HIl HIl2 HJl HJl2).
intros HIJ.
subst.
assert (A<>J).
eapply incidABl with (l:=l).
tauto.
elim Hl1 ; intros HAl1 HBl1.
elim Hl2; intros HAl2 HCl2.
generalize (a1_unique A J l1 l2 H0 HAl1 HIl1 HAl2 HIl2).
intros H'; subst.
elim (Hincid l2); tauto.
(* 1 *)
intros HIl2.
elim (incid_dec I l3).
intros HIl3.
assert (Hl1l3 : l<>l3).
intros Hl1l3.
subst.
elim (Hincid l3); tauto.
elim HK; intros HKl HKl3.
generalize (a2_unique l l3 I K Hl1l3 HIl HIl3 HKl HKl3).
intros HIK.
subst.
assert (A<>K).
eapply incidABl with (l:=l).
tauto.
elim Hl1 ; intros HAl1 HBl1.
elim Hl2; intros HAl2 HCl2.
elim Hl3; intros HAl3 HDl3.
generalize (a1_unique A K l1 l3 H0 HAl1 HIl1 HAl3 HIl3).
intros H'; subst.
elim (Hincid l3); tauto.
intros HIl3.

elim (incid_dec J l1).
intros HJl1.
assert (Hll1 : l<>l1).
intros Hll1.
subst.
elim (Hincid l1); tauto.
generalize (a2_unique l l1 I J Hll1 HIl HIl1 HJl HJl1).
intros HIJ.
subst.
assert (Hf:False).
apply HIl2.
assumption.
elim Hf.
intros HJl1.
elim (incid_dec K l2).
intros HKl2.
assert (Hll2 : l<>l2).
intros Hll2.
subst.
elim (Hincid l3); tauto.
elim HK; intros HKl HKl3.
generalize (a2_unique l l2 J K Hll2 HJl HJl2 HKl HKl2).
intros HJK.
subst.
assert (A<>K).
eapply incidABl with (l:=l).
tauto.
elim Hl1 ; intros HAl1 HBl1.
elim Hl2; intros HAl2 HCl2.
elim Hl3; intros HAl3 HDl3.
generalize (a1_unique A K l2 l3 H0 HAl2 HJl2 HAl3 HKl3).
intros H'; subst.
elim (Hincid l3); tauto.
intros HKl2.
exists I.
exists J.
exists K.
split.
unfold dist3.
split.
eapply incidABl with (l:=l2).
tauto.
split.
eapply incidABl with (l:=l3).
tauto.
assert (K<>J).
eapply incidABl with (l:=l2).
tauto.
intuition.
tauto.
Qed.


(* A3s :  each line has at least three points and there are at least two lines *)

Definition a3_1 : 
  (forall l:Line,{A:Point & {B:Point & {C:Point | (dist3 A B C/\Incid A l /\Incid B l /\ Incid C l)}}}).
generalize M.a3.
intros H.
intros l.
elim H; clear H; intros A HA.
elim HA; clear HA; intros B HB.
elim HB; clear HB; intros C HC.
elim HC; clear HC; intros D HD.
elim (HD l).
intros Hdist Hincid.
elim (incid_dec A l).
intros HAl.
elim (incid_dec B l).
intros HBl.
elim (incid_dec C l).
intros HCl.
assert False by tauto.
tauto.
intros HCl.
elim (incid_dec D l).
intros HDl.
assert False by tauto.
tauto.
intros HDl.
assert ( H' : dist4 A B C D /\ Incid A l /\ Incid B l /\ ~ Incid C l /\ ~ Incid D l).
tauto.

elim (cas1 A B C D l H' HD).
intros E HE.
exists A.
exists B.
exists E.
tauto.

intros HBl.
elim (incid_dec C l).
intros HCl.
elim (incid_dec D l).
intros HDl.
assert ( H' : dist4 A B C D /\ Incid A l /\ ~ Incid B l /\ ~ Incid C l /\ ~ Incid D l).
tauto.
elim (cas2 A B C D l H' HD).
intros E HE.
elim HE; intros F HF.
exists A.
exists E.
exists F.
tauto.
intros HDl.
assert (H' : dist4 A C B D /\ Incid A l /\ Incid C l /\ ~ Incid B l /\ ~ Incid D l).
unfold dist4 in * ;intuition.
assert (HD' : forall m : Line,
  dist4 A C B D /\
  (Incid A m /\ Incid C m -> ~ Incid B m /\ ~ Incid D m) /\
  (Incid A m /\ Incid B m -> ~ Incid C m /\ ~ Incid D m) /\
  (Incid A m /\ Incid D m -> ~ Incid B m /\ ~ Incid C m) /\
  (Incid B m /\ Incid C m -> ~ Incid A m /\ ~ Incid D m) /\
  (Incid D m /\ Incid C m -> ~ Incid B m /\ ~ Incid A m) /\
  (Incid B m /\ Incid D m -> ~ Incid C m /\ ~ Incid A m)).
intros m; elim (HD m); clear HD.
intuition.
generalize (cas1 A C B D l H' HD').
intros H'' ; elim H''; intros E HE.
exists A.
exists C.
exists E.
intuition.
intros HCl.
elim (incid_dec D l).
intros HDl.
assert (H' :(dist4 A D B C /\ Incid A l /\ Incid D l /\ ~ Incid B l /\ ~ Incid C l)).
unfold dist4 in *; intuition.
assert (HD' : (forall m : Line,
     dist4 A D B C /\
     (Incid A m /\ Incid D m -> ~ Incid B m /\ ~ Incid C m) /\
     (Incid A m /\ Incid B m -> ~ Incid D m /\ ~ Incid C m) /\
     (Incid A m /\ Incid C m -> ~ Incid B m /\ ~ Incid D m) /\
     (Incid B m /\ Incid D m -> ~ Incid A m /\ ~ Incid C m) /\
     (Incid C m /\ Incid D m -> ~ Incid B m /\ ~ Incid A m) /\
     (Incid B m /\ Incid C m -> ~ Incid D m /\ ~ Incid A m))).
intros m; elim (HD m); clear HD.
unfold dist4; intuition.
elim (cas1 A D B C l H' HD').
intros E HE.
exists A.
exists D.
exists E.
tauto.
intros HDl.
assert ( H' : dist4 A B C D /\ Incid A l /\ ~ Incid B l /\ ~ Incid C l /\ ~ Incid D l).
intuition.
elim (cas2 A B C D l H' HD).
intros E HE.
elim HE; intros F HF.
exists A.
exists E.
exists F.
tauto.
intros HAl.
elim (incid_dec B l).
intros HBl.
elim (incid_dec C l).
intros HCl.
elim (incid_dec D l).
intros HDl.
assert False by tauto.
tauto.
intros HDl.
assert (H' : dist4 B C A D /\ Incid B l /\ Incid C l /\ ~ Incid A l /\ ~ Incid D l).
unfold dist4 in *; intuition.
assert (HD' : (forall m : Line,
     dist4  B C A D /\
     (Incid B m /\ Incid C m -> ~ Incid A m /\ ~ Incid D m) /\
     (Incid B m /\ Incid A m -> ~ Incid C m /\ ~ Incid D m) /\
     (Incid B m /\ Incid D m -> ~ Incid A m /\ ~ Incid C m) /\
     (Incid A m /\ Incid C m -> ~ Incid B m /\ ~ Incid D m) /\
     (Incid D m /\ Incid C m -> ~ Incid A m /\ ~ Incid B m) /\
     (Incid A m /\ Incid D m -> ~ Incid C m /\ ~ Incid B m))).
intros m; elim (HD m); clear HD.
unfold dist4; intuition.
elim (cas1 B C A D l H' HD').
intros E HE.
exists B.
exists C.
exists E.
tauto.
intros HCl.
elim (incid_dec D l).
intros HDl.
assert (H' : dist4 B D A C /\ Incid B l /\ Incid D l /\ ~ Incid A l /\ ~ Incid C l).
unfold dist4 in *; intuition.
assert (HD' : (forall m : Line,
     dist4 B D A C /\
     (Incid B m /\ Incid D m -> ~ Incid A m /\ ~ Incid C m) /\
     (Incid B m /\ Incid A m -> ~ Incid D m /\ ~ Incid C m) /\
     (Incid B m /\ Incid C m -> ~ Incid A m /\ ~ Incid D m) /\
     (Incid A m /\ Incid D m -> ~ Incid B m /\ ~ Incid C m) /\
     (Incid C m /\ Incid D m -> ~ Incid A m /\ ~ Incid B m) /\
     (Incid A m /\ Incid C m -> ~ Incid D m /\ ~ Incid B m))).
intros m; elim (HD m); clear HD.
unfold dist4 in *; intuition.
elim (cas1 B D A C l H' HD').
intros E HE.
exists B.
exists D.
exists E.
tauto.
intros HDl.
assert (H' : dist4 B A C D /\ Incid B l /\ ~ Incid A l /\ ~ Incid C l /\ ~ Incid D l).
unfold dist4 in *; intuition.
assert (HD'  :  (forall m : Line,
     dist4 B A C D /\
     (Incid B m /\ Incid A m -> ~ Incid C m /\ ~ Incid D m) /\
     (Incid B m /\ Incid C m -> ~ Incid A m /\ ~ Incid D m) /\
     (Incid B m /\ Incid D m -> ~ Incid C m /\ ~ Incid A m) /\
     (Incid C m /\ Incid A m -> ~ Incid B m /\ ~ Incid D m) /\
     (Incid D m /\ Incid A m -> ~ Incid C m /\ ~ Incid B m) /\
     (Incid C m /\ Incid D m -> ~ Incid A m /\ ~ Incid B m))).
intros m; elim (HD m); clear HD.
unfold dist4 in *; intuition.
elim (cas2 B A C D l H' HD').  
intros E HE.
elim HE; intros F HF.
exists B.
exists E.
exists F.
tauto.
intros HBl.
elim (incid_dec C l).
intros HCl.
elim (incid_dec D l).
intros HDl.
assert (H' : dist4 C D A B /\ Incid C l /\ Incid D l /\ ~ Incid A l /\ ~ Incid B l).
unfold dist4 in *; intuition.
assert (HD' : (forall m : Line,
     dist4 C D A B /\
     (Incid C m /\ Incid D m -> ~ Incid A m /\ ~ Incid B m) /\
     (Incid C m /\ Incid A m -> ~ Incid D m /\ ~ Incid B m) /\
     (Incid C m /\ Incid B m -> ~ Incid A m /\ ~ Incid D m) /\
     (Incid A m /\ Incid D m -> ~ Incid C m /\ ~ Incid B m) /\
     (Incid B m /\ Incid D m -> ~ Incid A m /\ ~ Incid C m) /\
     (Incid A m /\ Incid B m -> ~ Incid D m /\ ~ Incid C m))).
intros m; elim (HD m); clear HD.
unfold dist4 in *; intuition.
elim (cas1 C D A B l H' HD').
intros E HE.
exists C.
exists D.
exists E.
tauto.
intros HDl.
assert (H' : (dist4 C A B D /\ Incid C l /\ ~ Incid A l /\ ~ Incid B l /\ ~ Incid D l)).
unfold dist4 in *; intuition.
assert (HD' : (forall m : Line,
     dist4 C A B D /\
     (Incid C m /\ Incid A m -> ~ Incid B m /\ ~ Incid D m) /\
     (Incid C m /\ Incid B m -> ~ Incid A m /\ ~ Incid D m) /\
     (Incid C m /\ Incid D m -> ~ Incid B m /\ ~ Incid A m) /\
     (Incid B m /\ Incid A m -> ~ Incid C m /\ ~ Incid D m) /\
     (Incid D m /\ Incid A m -> ~ Incid B m /\ ~ Incid C m) /\
     (Incid B m /\ Incid D m -> ~ Incid A m /\ ~ Incid C m))).
intros m; elim (HD m); clear HD.
unfold dist4; intuition.
elim (cas2 C A B D l H' HD').
intros E HE.
elim HE; intros F HF.
exists C.
exists E.
exists F.
tauto.
intros HCl.
elim (incid_dec D l).
intros HDl.
assert (H' : dist4 D A B C /\ Incid D l /\ ~ Incid A l /\ ~ Incid B l /\ ~ Incid C l).
unfold dist4 in *; intuition.
assert (HD' : (forall m : Line,
     dist4 D A B C /\
     (Incid D m /\ Incid A m -> ~ Incid B m /\ ~ Incid C m) /\
     (Incid D m /\ Incid B m -> ~ Incid A m /\ ~ Incid C m) /\
     (Incid D m /\ Incid C m -> ~ Incid B m /\ ~ Incid A m) /\
     (Incid B m /\ Incid A m -> ~ Incid D m /\ ~ Incid C m) /\
     (Incid C m /\ Incid A m -> ~ Incid B m /\ ~ Incid D m) /\
     (Incid B m /\ Incid C m -> ~ Incid A m /\ ~ Incid D m))).
intros m; elim (HD m); clear HD.
unfold dist4 in *; intuition.
elim (cas2 D A B C l H' HD').
intros E HE.
elim HE; intros F HF.
exists D.
exists E.
exists F.
tauto.
intros HDl.
assert (H' : dist4 A B C D /\ ~ Incid A l /\ ~ Incid B l /\ ~ Incid C l /\ ~ Incid D l).
unfold dist4 in *; intuition.
elim (cas3 A B C D l H' HD).
intros E HE.
elim HE; intros F HF.
elim HF; intros G HG.
exists E.
exists F.
exists G.
tauto.
Qed.

Definition a3_2 : {l1:Line & {l2:Line | l1 <> l2}}.
generalize M.a3.
intros H.
elim H;clear H.
intros A.
intros Ha.
elim Ha;clear Ha.
intros B.
intros Hb.
elim Hb ; clear Hb.
intros C.
intros Hc.
elim Hc ;clear Hc.
intros D.
intros Hd.
generalize (a1_exist A B ).
intros Hex.
elim Hex.
intros L.
intros H1.
assert (A <> B).
elim (Hd L).
intros.
unfold dist4 in H.
tauto.

generalize (a1_exist C D).
intros Hex2.
elim Hex2.
intros L2.
intros H2.
assert( C <> D).
elim (Hd L2).
intros.
unfold dist4 in H0.
tauto.
exists L.
exists L2.

intro HLL2.
subst L2.
elim (Hd L).
tauto.
Qed.

End forth.
