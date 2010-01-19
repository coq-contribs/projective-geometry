Require Export projective_plane_inst.
Require Export FSets.

Module Export uniq := (uniqueness_axioms AbstractProjectivePlane).
Module uniqdec := (decidability AbstractProjectivePlane).

Definition line A B := (proj1_sig (a1_exist A B)).
Definition inter l m := (proj1_sig (a2_exist l m)).

Definition on_inter A P Q R S := Incid A (line P Q) /\ Incid A (line R S).
Definition on_inter' A P Q R S := A = inter (line P Q) (line R S).

Definition Col A B C := 
 exists l : Line, 
 Incid A l /\ Incid B l /\ Incid C l.

Definition Meet l1 l2 l3 := 
 exists P : Point, Incid P l1 /\ Incid P l2 /\ Incid P l3.

Definition is_transverse A' B' C' A B C :=
Col A' B' C' /\ Col A B' C /\ Col A C' B /\ Col B A' C.

Definition is_on_inter P A B C D :=
Col P A B /\ Col P C D.

Definition is_on_proper_inter P A B C D :=
Col P A B /\ Col P C D /\ A<>B /\ C<>D /\ line A B <> line C D.

Definition is_hexamy A B C D E F := 
  (A<>B /\ A<>C /\ A<>D /\ A<>E /\ A<>F /\
  B<>C /\ B<>D /\ B<>E /\ B<>F /\
  C<>D /\ C<>E /\ C<>F /\
  D<>E /\ D<>F /\
  E<>F) /\
  let a:= inter (line B C) (line E F) in
  let b:= inter (line C D) (line F A) in 
  let c:= inter (line A B) (line D E) in
Col a b c.

Definition hexamy := forall A B C D E F, 
is_hexamy A B C D E F -> 
is_hexamy B A C D E F.


Ltac apply_unicity_hyps := match goal with
H1: ?A <> ?B, 
H2: ?Incid ?A ?l, 
H3: ?Incid ?B ?l, 
H4 : ?Incid ?A ?m, 
H5: ?Incid ?B ?m |- _ =>
let id:= fresh in assert (id: l=m); try apply (uniq.a1_unique A B l m H1 H2 H3 H4 H5);idtac "we have " l " = " m;subst l
| H1: ?l <> ?m, 
  H2: ?Incid ?A ?l, 
  H3: ?Incid ?A ?m, 
  H4 : ?Incid ?B ?l, 
  H5: ?Incid ?B ?m |- _ =>
let id:= fresh in assert (id: A=B); try apply (uniq.a2_unique l m A B H1 H2 H3 H4 H5);idtac "we have : " A " = " B;subst A
end.

Ltac collapse_hyps :=  progress (repeat (apply_unicity_hyps; CleanDuplicatedHyps)).

Ltac solve_eq := solve [intro; repeat subst; try collapse_hyps;intuition].

Ltac apply_unicity_no_hyps := match goal with
HAl: ?Incid ?A ?l, 
HBl: ?Incid ?B ?l, 
HAm: ?Incid ?A ?m, 
HBm: ?Incid ?B ?m |- _ =>
let id:= fresh in assert (id: l=m) 
by ( apply (uniq.a1_unique A B l m);
[solve_eq| apply HAl | apply HBl| apply HAm| apply HBm]);
idtac "we have " l " = " m;subst l
|
HAl: ?Incid ?A ?l, 
HBl: ?Incid ?B ?l, 
HAm: ?Incid ?A ?m, 
HBm: ?Incid ?B ?m |- _ =>
let id:= fresh in assert (id: A=B)
by ( apply (uniq.a2_unique l m A B);
[solve_eq| apply HAl | apply HAm| apply HBl| apply HBm]);
idtac "we have " A " = " B;subst A
end.

Ltac aide :=
 match goal with
H2: ?Incid ?A ?l, 
H3: ?Incid ?B ?l, 
H4: ?Incid ?A ?m, 
H5: ?Incid ?B ?m |- _ => idtac A " = " B " ou " l "=" m
end.

Ltac collapse_no_hyps := progress (repeat (apply_unicity_no_hyps; CleanDuplicatedHyps)).

Ltac collapse := progress ( try collapse_hyps; try collapse_no_hyps).

Ltac not_eq A B:= assert (A<>B) by solve_eq.

Definition Col_on A B C l := Incid A l /\ Incid B l /\ Incid C l.

Ltac geo_norm := 
 unfold Col_on, 
            is_on_inter, is_on_proper_inter,
            dist3, dist4, dist6, 
            Col in * |-; use_all.

Ltac cases_line l m := 
   elim (uniqdec.eq_line_dec l m); intro;
   [subst;try collapse|idtac].

Ltac cases_point A B := 
   elim (uniqdec.eq_point_dec A B); intro;
   [subst;try collapse|idtac].

Lemma line_wd : forall A B l,
 Incid A l ->
 Incid B l ->
 A<>B ->
 line A B = l.
Proof.
intros.
unfold line.
elim a1_exist;simpl.
intros.
use_all.
collapse.
trivial.
Qed.

Lemma line_wd_sym : forall A B l,
 Incid A l ->
 Incid B l ->
 B<>A ->
 line A B = l.
Proof.
intros.
unfold line.
elim a1_exist;simpl.
intros.
use_all.
collapse.
trivial.
Qed.

Ltac create_line A B l := elim (a1_exist A B);intros l Hl;decompose[and] Hl;clear Hl.

Ltac create_point l m P := elim (a2_exist l m);intros P HP;decompose[and] HP;clear HP.

Ltac create_inter A B C D P := 
  let AB:=fresh "l" in 
  let CD:= fresh "l" in
  create_line A B AB; create_line C D CD; create_point AB CD P.

Ltac create_non_existing_line A B := progress first [ (match goal with
 HA : Incid A ?l , HB : Incid B ?l |- _ => idtac 
end) | (let id:= fresh "l" in create_line A B id) ].


Ltac add_non_existing_lines := repeat (match goal with
_: context[line ?A ?B] |- _ => create_non_existing_line A B
| _: _ |- context[line ?A ?B] => create_non_existing_line A B
end).

Ltac remove_line_occ := repeat ( match goal with
 HAB: ?A<>?B, HA: Incid ?A ?l, HB: Incid ?B ?l, 
 H: context[line ?A ?B] |- _ => rewrite (line_wd A B l) in * by assumption
| HAB: ?B<>?A, HA: Incid ?A ?l, HB: Incid ?B ?l, 
 H: context[line ?A ?B] |- _ => rewrite (line_wd_sym A B l) in * by assumption
| HAB: ?A<>?B, HA: Incid ?A ?l, HB: Incid ?B ?l 
 |- context[line ?A ?B] => rewrite (line_wd A B l) in * by assumption
| HAB: ?B<>?A, HA: Incid ?A ?l, HB: Incid ?B ?l 
 |- context[line ?A ?B] => rewrite (line_wd_sym A B l) in * by assumption
end).

Lemma test2 : forall A B  C D l , line A B = l -> line C D = l -> True.
Proof.
intros.
add_non_existing_lines.
auto.
Qed.

Lemma on_inter_points_wd : forall A B C D P l m,
 Incid A l ->
 Incid B l ->
 Incid C m ->
 Incid D m ->
 Incid P l ->
 Incid P m ->
 l <> m ->
 A <> B ->
 C <> D ->
 P = inter (line A B) (line C D).
Proof.
intros.
remove_line_occ.
unfold inter.
elim a2_exist.
intros.
simpl in *.
use_all.
collapse.
Qed.

Lemma on_inter_points_wd_spec_1 : forall A B C D l m,
 Incid A l ->
 Incid B l ->
 Incid C m ->
 Incid D m ->
 Incid A m ->
 l <> m ->
 A <> B ->
 C <> D ->
 A = inter (line A B) (line C D).
Proof.
intros.
eapply on_inter_points_wd.
apply H.
apply H0.
apply H1.
apply H2.
auto.
auto.
auto.
auto.
auto.
Qed.

Lemma on_inter_points_wd_spec_2 : forall A B C D l m,
 Incid A l ->
 Incid B l ->
 Incid C m ->
 Incid D m ->
 Incid B m ->
 l <> m ->
 A <> B ->
 C <> D ->
 B = inter (line A B) (line C D).
Proof.
intros.
eapply on_inter_points_wd.
apply H.
apply H0.
apply H1.
apply H2.
auto.
auto.
auto.
auto.
auto.
Qed.

Lemma on_inter_points_wd_spec_3 : forall A B C D l m,
 Incid A l ->
 Incid B l ->
 Incid C m ->
 Incid D m ->
 Incid C l ->
 l <> m ->
 A <> B ->
 C <> D ->
 C = inter (line A B) (line C D).
Proof.
intros.
eapply on_inter_points_wd.
apply H.
apply H0.
apply H1.
apply H2.
auto.
auto.
auto.
auto.
auto.
Qed.

Lemma on_inter_points_wd_spec_4 : forall A B C D l m,
 Incid A l ->
 Incid B l ->
 Incid C m ->
 Incid D m ->
 Incid D l ->
 l <> m ->
 A <> B ->
 C <> D ->
 D = inter (line A B) (line C D).
Proof.
intros.
eapply on_inter_points_wd.
apply H.
apply H0.
apply H1.
apply H2.
auto.
auto.
auto.
auto.
auto.
Qed.

Lemma not_eq_sym_point : forall A B : Point, A<>B -> B<>A.
Proof.
 auto.
Qed.

Lemma not_eq_sym_line : forall A B : Line, A<>B -> B<>A.
Proof.
 auto.
Qed.

Ltac assumption_or_sym := 
  assumption || 
  (apply not_eq_sym_point;assumption) || 
  (apply not_eq_sym_line;assumption).

Ltac assumptions_or_sym := repeat split;try assumption_or_sym.

Ltac remove_inter_points_occ := repeat (match goal with

HA: Incid ?A ?l, 
HB: Incid ?B ?l, 
HC: Incid ?C ?m, 
HD: Incid ?D ?m,
HP1 : Incid ?P ?l,
HP2 : Incid ?P ?m |- context[inter (line ?A ?B) (line ?C ?D)] =>
rewrite <- (on_inter_points_wd A B C D P l m) in *; try assumption_or_sym

| HA: Incid ?A ?l, 
HB: Incid ?B ?l, 
HC: Incid ?C ?m, 
HD: Incid ?D ?m,
HP2 : Incid ?A ?m |- context[inter (line ?A ?B) (line ?C ?D)] =>
rewrite <- (on_inter_points_wd_spec_1 A B C D l m) in *; try assumption_or_sym

| HA: Incid ?A ?l, 
HB: Incid ?B ?l, 
HC: Incid ?C ?m, 
HD: Incid ?D ?m,
HP2 : Incid ?B ?m |- context[inter (line ?A ?B) (line ?C ?D)] =>
rewrite <- (on_inter_points_wd_spec_2 A B C D l m) in *; try assumption_or_sym

| HA: Incid ?A ?l, 
HB: Incid ?B ?l, 
HC: Incid ?C ?m, 
HD: Incid ?D ?m,
HP2 : Incid ?C ?l |- context[inter (line ?A ?B) (line ?C ?D)] =>
rewrite <- (on_inter_points_wd_spec_3 A B C D l m) in *; try assumption_or_sym

| HA: Incid ?A ?l, 
HB: Incid ?B ?l, 
HC: Incid ?C ?m, 
HD: Incid ?D ?m,
HP2 : Incid ?D ?l |- context[inter (line ?A ?B) (line ?C ?D)] =>
rewrite <- (on_inter_points_wd_spec_4 A B C D l m) in *; try assumption_or_sym

| 

HA: Incid ?A ?l, 
HB: Incid ?B ?l, 
HC: Incid ?C ?m, 
HD: Incid ?D ?m,
HP1 : Incid ?P ?l,
HP2 : Incid ?P ?m , 
H: context[inter (line ?A ?B) (line ?C ?D)] |- _ =>
rewrite <- (on_inter_points_wd A B C D P l m) in H; try assumption_or_sym

| HA: Incid ?A ?l, 
HB: Incid ?B ?l, 
HC: Incid ?C ?m, 
HD: Incid ?D ?m,
HP2 : Incid ?A ?m, 
H: context[inter (line ?A ?B) (line ?C ?D)]|- _ =>
rewrite <- (on_inter_points_wd_spec_1 A B C D l m) in H; try assumption_or_sym

| HA: Incid ?A ?l, 
HB: Incid ?B ?l, 
HC: Incid ?C ?m, 
HD: Incid ?D ?m,
HP2 : Incid ?B ?m, 
H: context[inter (line ?A ?B) (line ?C ?D)] |- _ =>
rewrite <- (on_inter_points_wd_spec_2 A B C D l m) in H; try assumption_or_sym

| HA: Incid ?A ?l, 
HB: Incid ?B ?l, 
HC: Incid ?C ?m, 
HD: Incid ?D ?m,
HP2 : Incid ?C ?l, 
H: context[inter (line ?A ?B) (line ?C ?D)] |- _ =>
rewrite <- (on_inter_points_wd_spec_3 A B C D l m) in H; try assumption_or_sym

| HA: Incid ?A ?l, 
HB: Incid ?B ?l, 
HC: Incid ?C ?m, 
HD: Incid ?D ?m,
HP2 : Incid ?D ?l, 
H: context[inter (line ?A ?B) (line ?C ?D)] |- _ =>
rewrite <- (on_inter_points_wd_spec_4 A B C D l m) in H; try assumption_or_sym


end).


Lemma on_inter_wd : forall P l m,
 Incid P l ->
 Incid P m ->
 l <> m ->
 inter l m = P.
Proof.
intros.
unfold inter.
elim a2_exist.
simpl.
intros.
use_all.
collapse.
trivial.
Qed.

Lemma on_inter_wd_sym : forall P l m,
 Incid P l ->
 Incid P m ->
 l <> m ->
 inter m l = P.
Proof.
intros.
unfold inter.
elim a2_exist.
simpl.
intros.
use_all.
collapse.
trivial.
Qed.


Ltac remove_inter_occ := 
first [erewrite on_inter_wd_sym in * by eassumption | 
       erewrite on_inter_wd     in * by eassumption].


Lemma col_col_on_inter : forall A B C D I,
 Col A B I -> Col C D I -> 
 A<>B -> C<>D -> (line A B) <> (line C D) ->
 I = inter (line A B) (line C D).
Proof.
intros.
geo_norm.
remove_line_occ.
remove_inter_occ.
trivial.
Qed.



Lemma incid_line_left : forall A B, Incid A (line A B).
Proof.
intros.
intros; unfold line.
repeat (elim a1_exist); simpl; intuition.
Qed.

Lemma incid_line_right : forall A B, Incid B (line A B).
intros; unfold line.
repeat (elim a1_exist); simpl; intuition.
Qed.

Hint Resolve incid_line_left incid_line_right.

Lemma col_incid : forall A B C, B<>C -> Col A B C -> Incid A (line B C).
intros.
geo_norm.
remove_line_occ.
auto.
Qed.

Lemma col_comm : forall A B C, Col A B C -> Col B A C.
Proof.
intros; firstorder.
Qed.

Lemma col_comm2 : forall A B C, Col A B C -> Col A C B.
Proof with (intros; firstorder).
intros...
Qed.

Lemma col_comm3 : forall A B C, Col A B C -> Col B C A.
Proof.
intros; firstorder.
Qed.

Lemma col_comm4 : forall A B C, Col A B C -> Col C A B.
Proof.
intros; firstorder.
Qed.

Lemma col_comm5 : forall A B C, Col A B C -> Col C B A.
Proof.
intros; firstorder.
Qed.

Lemma inter_comm : forall l m, inter l m = inter m l.
Proof.
intros; 
elim (uniqdec.eq_line_dec l m).
intro;subst.
trivial.
intros.

intros; unfold inter;firstorder.
repeat (elim a2_exist); simpl;intros.
use_all.
collapse.
Qed.

Lemma line_comm : forall A B, (line A B)=(line B A).
Proof.
intros; elim (uniqdec.eq_point_dec A B).
intros; subst; auto.
intros ; unfold line; repeat (elim a1_exist); simpl; intros; use_all.
collapse.
Qed.

Hint Resolve inter_comm line_comm 
                          col_comm col_comm2 col_comm3 col_comm4 col_comm5.

Lemma  line_neq_neq :
 forall A B C D, forall l m, A<>B -> C<>D -> 
 Incid A l -> Incid B l -> Incid C m -> Incid D m -> (line A B) <> (line C D) -> l<>m.
Proof.
intros.
unfold line in *; revert H5.
repeat (elim a1_exist); simpl;firstorder.
collapse.
auto.
Qed.

Lemma incid_inter_left :
forall A B C D, Incid (inter (line A B) (line C D)) (line A B).
Proof.
intros; unfold inter; repeat (elim a2_exist); simpl; firstorder.
Qed.

Lemma incid_inter_right :
forall A B C D, Incid (inter (line A B) (line C D)) (line C D).
Proof.
intros; unfold inter; repeat (elim a2_exist); simpl; firstorder.
Qed.

Hint Resolve incid_inter_left incid_inter_right.

(* Invariance by permutation of hexamy property *)

Lemma hexamy_rot_left : forall A B C D E F, 
 is_hexamy A B C D E F ->  is_hexamy B C D E F A.
Proof.
intros; unfold is_hexamy in *.
unfold Col in *; firstorder.
exists x; firstorder.
rewrite inter_comm; auto.
Qed.

Lemma hexamy_rot_right : forall A B C D E F, 
 is_hexamy A B C D E F ->  is_hexamy F A B C D E.
Proof.
intros; unfold is_hexamy in *.
unfold Col in *; firstorder.
exists x; firstorder.
rewrite inter_comm; auto.
Qed.

Hint Resolve hexamy_rot_left hexamy_rot_right : permut.

Lemma hexamy_swap_2_3 :  hexamy -> forall A B C D E F, 
 is_hexamy A B C D E F ->  is_hexamy A C B D E F.
Proof.
intros; apply hexamy_rot_right; apply H;
       apply hexamy_rot_left; exact H0.
Qed.

Lemma hexamy_swap_2_4 :  hexamy -> forall A B C D E F, 
 is_hexamy A B C D E F ->  is_hexamy A D C B E F.
Proof.
intros;
apply hexamy_rot_right; apply H;
apply hexamy_rot_right; apply H;
apply hexamy_rot_left; apply H;
apply hexamy_rot_left; exact H0.
Qed.

Lemma hexamy_swap_2_5 :  hexamy -> forall A B C D E F, 
 is_hexamy A B C D E F ->  is_hexamy A E C D B F.
Proof.
intros;
apply H; apply hexamy_rot_left; apply H;
apply hexamy_rot_left; apply H;
apply hexamy_rot_right; apply H;
apply hexamy_rot_right; apply H; exact H0.
Qed.

Lemma hexamy_swap_2_6 :  hexamy -> forall A B C D E F, 
 is_hexamy A B C D E F ->  is_hexamy A F C D E B.
Proof.
intros;
apply H; apply hexamy_rot_left; apply H;
apply hexamy_rot_right; apply H; exact H0.
Qed.

Lemma hexamy_swap_3_4 :  hexamy -> forall A B C D E F, 
 is_hexamy A B C D E F ->  is_hexamy A B D C E F.
Proof.
intros;
do 2 apply hexamy_rot_right;
apply H; apply hexamy_rot_left;
apply hexamy_rot_left; exact H0.
Qed.

Lemma hexamy_swap_3_5 :  hexamy -> forall A B C D E F, 
 is_hexamy A B C D E F ->  is_hexamy A B E D C F.
Proof.
intro H; intro A; intro B; intro C; intro D; intro E; intro F; intro H0;
       apply hexamy_rot_right; apply hexamy_rot_right;
       apply H; apply hexamy_rot_right; apply H;
       apply hexamy_rot_left; apply H;
       apply hexamy_rot_left; apply hexamy_rot_left; exact H0.
Qed.

Lemma hexamy_swap_3_6 :  hexamy -> forall A B C D E F, 
 is_hexamy A B C D E F ->  is_hexamy A B F D E C.
Proof.
intros.
do 2 apply hexamy_rot_right;
apply H.
apply hexamy_rot_right.
apply H.
do 2 apply hexamy_rot_right.
apply H;
apply hexamy_rot_right; apply H;
apply hexamy_rot_left; exact H0.
Qed.

Lemma hexamy_swap_4_5 :  hexamy -> forall A B C D E F, 
 is_hexamy A B C D E F ->  is_hexamy A B C E D F.
Proof.
intros.
do 3 apply hexamy_rot_left;
apply H; 
do 3 apply hexamy_rot_left;
exact H0.
Qed.

Lemma hexamy_swap_4_6 :  hexamy -> forall A B C D E F, 
 is_hexamy A B C D E F ->  is_hexamy A B C F E D.
Proof.
intros.
do 3 apply hexamy_rot_right.
apply H.
apply hexamy_rot_right.
apply H.
apply hexamy_rot_left.
apply H.
do 3 apply hexamy_rot_left;
exact H0.
Qed.

Lemma hexamy_swap_5_6 :  hexamy -> forall A B C D E F, 
 is_hexamy A B C D E F ->  is_hexamy A B C D F E.
Proof.
intros;
do 2 apply hexamy_rot_left;
apply H;
do 2 apply hexamy_rot_right;
exact H0.
Qed.

Ltac put_in_front P := repeat (match goal with
 H:_ |- is_hexamy P ?B ?C ?D ?E ?F => idtac
|H:_ |- is_hexamy ?A ?B ?C ?D ?E ?F => apply hexamy_rot_left
|H:_ |- _ => fail "goal must be hexamy" 
end).

Ltac hexamy_permut_1:= match goal with
| HH: hexamy, H: is_hexamy ?A ?B ?C ?D ?E ?F |- is_hexamy _ _ _ _ _ _  => put_in_front A
end.

Ltac hexamy_permut_2 := match goal with
| HH: hexamy, H: is_hexamy ?A ?B ?C ?D ?E ?F |- is_hexamy ?A ?B _ _ _ _  => idtac 
| HH: hexamy, H: is_hexamy ?A ?B ?C ?D ?E ?F |- is_hexamy ?A ?X ?B ?Y ?Z ?T  => cut (is_hexamy A B X Y Z T) ; [apply (hexamy_swap_2_3 HH) | idtac ]
| HH: hexamy, H: is_hexamy ?A ?B ?C ?D ?E ?F |- is_hexamy ?A ?X ?Y ?B ?Z ?T  => cut (is_hexamy A B Y X Z T) ; [apply (hexamy_swap_2_4 HH) | idtac]
| HH: hexamy, H: is_hexamy ?A ?B ?C ?D ?E ?F |- is_hexamy ?A ?X ?Y ?Z ?B ?T  => cut (is_hexamy A B Y Z X T) ; [apply (hexamy_swap_2_5 HH)|idtac]
| HH: hexamy, H: is_hexamy ?A ?B ?C ?D ?E ?F |- is_hexamy ?A ?X ?Y ?Z ?T ?B  => cut (is_hexamy A B Y Z T X) ; [apply (hexamy_swap_2_6 HH)| idtac]
end.

Ltac hexamy_permut_3 := match goal with
| HH: hexamy, H: is_hexamy ?A ?B ?C ?D ?E ?F |- is_hexamy ?A ?B ?C _ _ _  => idtac 
| HH: hexamy, H: is_hexamy ?A ?B ?C ?D ?E ?F |- is_hexamy ?A ?B ?X ?C ?Y ?Z  => cut (is_hexamy A B C X Y Z) ; [apply (hexamy_swap_3_4 HH) | idtac ]
| HH: hexamy, H: is_hexamy ?A ?B ?C ?D ?E ?F |- is_hexamy ?A ?B ?X ?Y ?C ?Z  => cut (is_hexamy A B C Y X Z) ; [apply (hexamy_swap_3_5 HH) | idtac]
| HH: hexamy, H: is_hexamy ?A ?B ?C ?D ?E ?F |- is_hexamy ?A ?B ?X ?Y ?Z ?C  => cut (is_hexamy A B C Y Z X) ; [apply (hexamy_swap_3_6 HH)|idtac]
end.

Ltac hexamy_permut_4 := match goal with
| HH: hexamy, H: is_hexamy ?A ?B ?C ?D ?E ?F |- is_hexamy ?A ?B ?C ?D _ _  => idtac
| HH: hexamy, H: is_hexamy ?A ?B ?C ?D ?E ?F |- is_hexamy ?A ?B ?C ?X ?D ?Y  => cut (is_hexamy A B C D X Y) ; [apply (hexamy_swap_4_5 HH) | idtac ]
| HH: hexamy, H: is_hexamy ?A ?B ?C ?D ?E ?F |- is_hexamy ?A ?B ?C ?X ?Y ?D  => cut (is_hexamy A B C D Y X) ; [apply (hexamy_swap_4_6 HH) | idtac]
end.

Ltac hexamy_permut_5 := match goal with
| HH: hexamy, H: is_hexamy ?A ?B ?C ?D ?E ?F |- is_hexamy ?A ?B ?C ?D ?E _  => idtac 
| HH: hexamy, H: is_hexamy ?A ?B ?C ?D ?E ?F |- is_hexamy ?A ?B ?C ?D ?X ?E  => cut (is_hexamy A B C D E X) ; [apply (hexamy_swap_5_6 HH) | idtac ]
end.

Ltac hexamy_permut := hexamy_permut_1 ; hexamy_permut_2 ; hexamy_permut_3 ; hexamy_permut_4 ; hexamy_permut_5 ; assumption.

Lemma test4  : forall A C J A' C' K, hexamy -> is_hexamy A C J A' C' K -> is_hexamy A A' J C C' K.
Proof.
intros; hexamy_permut.
Qed.


Lemma test5 : forall P M L Q N H, hexamy ->
is_hexamy P M L Q N H -> is_hexamy P Q L M N H.
Proof.
intros; hexamy_permut.
Qed.


Lemma test3 : forall A B C D E F, hexamy -> is_hexamy B F D A E C ->
is_hexamy A B C D E F. 
Proof.
intros.
hexamy_permut.
Qed.

Lemma test : forall A B C D E F, hexamy ->
is_hexamy A B C D E F -> is_hexamy B A C E D F.
Proof.
intros.
hexamy_permut.
Qed.

Lemma test3' : forall A B C D E F, hexamy -> is_hexamy B F D A E C ->
is_hexamy A B C D E F. 
Proof.
intros.
hexamy_permut.
Qed.

Lemma hexamy_swap_right : hexamy ->
forall A B C D E F, 
 is_hexamy A B C D E F ->  is_hexamy A B C D F E.
Proof.
intros.
hexamy_permut.
Qed.

Lemma col_line_eq : forall A B C, 
 Col A B C -> A<>B -> A<>C ->
 line A B = line A C.
Proof.
intros.
unfold line.
repeat elim a1_exist;intros.
simpl.
unfold Col in H.
use H.
use p.
use p0.
assert (x=x1).
eapply a1_unique;eauto.
subst.
assert (x1=x0).
eapply a1_unique; try apply H0;auto.
subst.
auto.
Qed.

Lemma col_trivial_1: forall A B, Col A A B.
Proof.
intros.
create_line A B lAB.
exists lAB.
auto.
Qed.

Lemma col_trivial_2: forall A B, Col A B B.
Proof.
intros.
create_line A B lAB.
exists lAB.
auto.
Qed.

Lemma col_trivial_3: forall A B, Col A B A.
Proof.
intros.
create_line A B lAB.
exists lAB.
auto.
Qed.

Hint Resolve col_trivial_1 col_trivial_2 col_trivial_3.

Ltac solve_col := match goal with
 HA: Incid ?A ?l, HB: Incid ?B ?l, HC : Incid ?C ?l |- Col ?A ?B ?C => exists l; auto
| H:_ |- Col ?A ?A ?B => auto
| H:_ |- Col ?A ?B ?B => auto
| H:_ |- Col ?A ?B ?A => auto
end.

 Ltac revert_all_inter T := (match goal with
H: context[inter (line _ _) (line _ _)] |- _ => revert H
end;revert_all_inter T;intro) || T.

Ltac remove_inter_points_occ_all := revert_all_inter remove_inter_points_occ.

Ltac remove_inter_points_occ_assum := do 3  (match goal with

|HA: Incid ?A ?l, 
HB: Incid ?B ?l, 
HC: Incid ?C ?m, 
HD: Incid ?D ?m,
HP1 : Incid ?P ?l,
HP2 : Incid ?P ?m , 
H: context[inter (line ?A ?B) (line ?C ?D)] |- _ => 
rewrite <- (on_inter_points_wd A B C D P l m) in H; try assumption_or_sym

| HA: Incid ?A ?l, 
HB: Incid ?B ?l, 
HC: Incid ?C ?m, 
HD: Incid ?D ?m,
HP2 : Incid ?A ?m, 
H: context[inter (line ?A ?B) (line ?C ?D)]|- _ =>
rewrite <- (on_inter_points_wd_spec_1 A B C D l m) in H; try assumption_or_sym

| HA: Incid ?A ?l, 
HB: Incid ?B ?l, 
HC: Incid ?C ?m, 
HD: Incid ?D ?m,
HP2 : Incid ?B ?m, 
H: context[inter (line ?A ?B) (line ?C ?D)] |- _ =>
rewrite <- (on_inter_points_wd_spec_2 A B C D l m) in H; try assumption_or_sym

| HA: Incid ?A ?l, 
HB: Incid ?B ?l, 
HC: Incid ?C ?m, 
HD: Incid ?D ?m,
HP2 : Incid ?C ?l, 
H: context[inter (line ?A ?B) (line ?C ?D)] |- _ =>
rewrite <- (on_inter_points_wd_spec_3 A B C D l m) in H; try assumption_or_sym

| HA: Incid ?A ?l, 
HB: Incid ?B ?l, 
HC: Incid ?C ?m, 
HD: Incid ?D ?m,
HP2 : Incid ?D ?l, 
H: context[inter (line ?A ?B) (line ?C ?D)] |- _ =>
rewrite <- (on_inter_points_wd_spec_4 A B C D l m) in H; try assumption_or_sym

end).

Ltac hexamy_proof_1  A B C D E F := 
  let T := fresh "hexa" in
 assert (T:is_hexamy A B C D E F); 
  [unfold is_hexamy;split;[assumptions_or_sym|
                                        remove_inter_points_occ; remove_line_occ; try solve [solve_col]]|
   idtac].

Ltac print_goal := match goal with
H:_ |- ?X => idtac X
end.

Ltac hexamy_proof A B C D E F A' B' C' D' E' F' :=
  let T := fresh "hexa" in
  let U := fresh "hexa" in
  assert (T:is_hexamy A B C D E F); 
  [unfold is_hexamy;split;[assumptions_or_sym|
                                        remove_inter_points_occ; remove_line_occ; try solve [solve_col];print_goal]|
   assert (U:is_hexamy A' B' C' D' E' F') by hexamy_permut;
   unfold is_hexamy in U;use U;
     remove_inter_points_occ_assum;auto].

(* This first definition of Pappus is the most general one. *)

Definition pappus_strong := 
 forall A B C A' B' C' P Q R,
 (dist6 A B C A' B' C' \/ 
 (line A B' <> line A' B /\ A<>B' /\ A'<>B /\ 
  line B C' <> line B' C /\ B<>C' /\ B'<>C /\ 
  line A C' <> line A' C /\ A<>C' /\ A'<>C) ) ->
 Col A B C -> Col A' B' C' ->
 is_on_inter P A B' A' B ->
 is_on_inter Q B C' B' C ->
 is_on_inter R A C' A' C ->
 Col P Q R.

(* This second definition of Pappus' configuration assumes that all the 6 points are distincts
and that the intersection are all well defined. This implies also that the line AB and A'B'
are distinct. This is the figure without any particular case. *)

Definition pappus_weak := 
 forall A B C A' B' C' P Q R,
 Col A B C -> Col A' B' C' ->
 dist6 A B C A' B' C' -> 
 is_on_proper_inter P A B' A' B ->
 is_on_proper_inter Q B C' B' C ->
 is_on_proper_inter R A C' A' C ->
 Col P Q R.

Lemma is_on_proper_inter_is_on_inter : forall P A B C D,
 is_on_proper_inter P A B C D -> is_on_inter P A B C D.
Proof.
intros.
unfold is_on_proper_inter, is_on_inter in *.
intuition.
Qed.

Lemma pappus_pappus_strong : pappus_weak <-> pappus_strong.
Proof.
unfold pappus_weak, pappus_strong.
split;intros.

2:apply (H  A B C A' B' C');auto using  is_on_proper_inter_is_on_inter.


decompose [or] H0;clear H0.

  elim (uniqdec.eq_line_dec (line A' B) (line A B')).
  intros.  
  geo_norm.
  subst.
  remove_line_occ.
  subst.
  rename  x5 into l.
  rename x6 into m.
  rename x3 into lAB'.
  rename x2 into lB'C.
  rename x1 into lBC'.
  rename x0 into lA'C.
  rename x into lAC'.
  collapse.
  solve_col.
  
  intro.

  elim (uniqdec.eq_line_dec (line B' C) (line B C')).
  intros.  
  geo_norm.
  subst.
  remove_line_occ.
  subst.
  collapse.
  solve_col.
  
  intro.

  elim (uniqdec.eq_line_dec (line A' C) (line A C')).
  intros.  
  geo_norm.
  subst.
  remove_line_occ.
  subst.
  collapse.
  solve_col.
  
  intro.

  apply (H  A B C A' B' C'); auto;
 
  unfold is_on_inter, is_on_proper_inter, dist6 in *;use_all;auto.


use H6.


cases_point A B.
geo_norm.
remove_line_occ.
collapse.
solve_col.

cases_point A C.
geo_norm.
remove_line_occ.
collapse.
solve_col.

cases_point B C.
geo_norm.
remove_line_occ.
collapse.
solve_col.

cases_point A' B'.
geo_norm.
remove_line_occ.
collapse.
solve_col.

cases_point A' C'.
geo_norm.
remove_line_occ.
collapse.
solve_col.

cases_point B' C'.
geo_norm.
remove_line_occ.
collapse.
solve_col.

cases_point A A'.
geo_norm.
remove_line_occ.
collapse.
solve_col.

cases_point A B'.
geo_norm.
remove_line_occ.
collapse.
solve_col.

cases_point A C'.
geo_norm.
remove_line_occ.
collapse.
solve_col.

cases_point B A'.
geo_norm.
remove_line_occ.
collapse.
solve_col.

cases_point B B'.
geo_norm.
remove_line_occ.
collapse.
solve_col.

cases_point B C'.
geo_norm.
remove_line_occ.
collapse.
solve_col.

cases_point C A'.
geo_norm.
remove_line_occ.
collapse.
solve_col.

cases_point C B'.
geo_norm.
remove_line_occ.
collapse.
solve_col.

cases_point C C'.
geo_norm.
remove_line_occ.
collapse.
solve_col.


apply (H  A B C A' B' C'); try assumption.
unfold dist6;intuition.

unfold is_on_proper_inter, is_on_inter in *; use_all;auto.
unfold is_on_proper_inter, is_on_inter in *; use_all;auto.
unfold is_on_proper_inter, is_on_inter in *; use_all;auto.
Qed.

Ltac not_eq_pt_all := match goal with
| A:Point,B:Point |- _ => assert_if_not_exist (A<>B);[ solve_eq | idtac]
end.

Ltac not_eq_li_all := match goal with
 | L:Line,M:Line |- _ => assert_if_not_exist (L<>M);[ solve_eq | idtac] 
end.

Lemma essai : forall A B C:Point, A<>B -> True.
intros.
not_eq_pt_all.
auto.
Qed.


Ltac collapse_all n := do n (not_eq_pt_all; not_eq_li_all); collapse.

Lemma hexamy_special_case :  forall A B C D E F,
 dist6 A B C D E F ->
 Col A B C -> Col D E F -> is_hexamy A B C D E F.
Proof.
intros.
unfold is_hexamy.
split.
solve [auto].
geo_norm;remove_line_occ;solve_col.
Qed.

(* This theorem shows that Pappus property implies the Hexamys property *)


Lemma hexamy_prop: pappus_strong -> forall A B C D E F,
 (line C D) <> (line A F) -> 
 (line B C) <> (line E F) ->
 (line A B) <> (line D E) -> 

 (line A C) <> (line E F) ->
 (line B F) <> (line C D) ->
 is_hexamy A B C D E F -> is_hexamy B A C D E F.
Proof.
intro HPappus.
intros.
unfold is_hexamy in *.
use H4.
split;[repeat split;auto|idtac].
create_line A B lAB.
create_line A C lAC.
create_line A D lAD.
create_line A E lAE.
create_line A F lAF.

create_line B C lBC.
create_line B D lBD.
create_line B E lBE.
create_line B F lBF.

create_line C D lCD.
create_line C E lCE.
create_line C F lCF.

create_line D E lDE.
create_line D F lDF.

create_line E F lEF.

create_inter B C E F a.
create_inter C D F A b.
create_inter A B D E c.
collapse.

replace (line A B) with l3 in * by (rewrite (line_wd A B l3) by assumption;trivial).
replace (line B C) with l  in * by (rewrite (line_wd B C l)  by assumption;trivial).
replace (line E F) with l0 in * by (rewrite (line_wd E F l0) by assumption;trivial).
replace (line C D) with l1 in * by (rewrite (line_wd C D l1) by assumption;trivial).
replace (line A F) with l2 in * by (rewrite (line_wd A F l2) by assumption;trivial).
replace (line D E) with l4 in * by (rewrite (line_wd D E l4) by assumption;trivial).
replace (line A C) with lAC in * by (rewrite (line_wd A C lAC) by assumption;trivial).
replace (line B F) with lBF in * by (rewrite (line_wd B F lBF) by assumption;trivial).
replace (line A D) with lAD in * by (rewrite (line_wd A D lAD) by assumption;trivial).
replace (line C E) with lCE in * by (rewrite (line_wd C E lCE) by assumption;trivial).
replace (line F B) with lBF in * by (rewrite (line_wd_sym F B lBF) by assumption;trivial).
replace (line A E) with lAE in * by (rewrite (line_wd A E lAE) by assumption;trivial).
replace (line E C) with lCE in * by (rewrite (line_wd_sym E C lCE) by assumption;trivial).
replace (line F A) with l2 in * by (rewrite (line_wd_sym F A l2) by assumption;trivial).
replace (line B A) with l3 in * by (rewrite (line_wd_sym B A l3) by assumption;trivial).
create_point lAC l0 b'.

revert H6;repeat remove_inter_occ;intro.

geo_norm.

cases_line lAD l2.
cases_point c D.
remove_inter_occ.
auto.
collapse.
cases_point a E.

create_inter B F C D w.
collapse.
remove_inter_occ.

cut (Col w b' c).
auto.
apply (HPappus D F A B C E w b' c).
left.
unfold dist6;repeat split;auto.
solve_col.
solve_col.
unfold is_on_inter;split;solve_col.
unfold is_on_inter;split;solve_col.
unfold is_on_inter;split;solve_col.

collapse.
auto.

cases_line l3 lAE.
cases_point a c.
auto.
collapse.
cases_point b F.
remove_inter_occ.
solve_col.
collapse.
remove_inter_occ.
solve_col.

cases_line l0 l2.
replace (inter l1 lBF) with B.
solve_col.
unfold inter;elim a2_exist; intros; simpl;geo_norm;solve [collapse].

cases_line lCE l0.
cases_point c C.
solve [auto].
exists x.
repeat split;auto.
unfold inter;elim a2_exist;simpl;intros;use_all;solve [auto].

cases_line lAD l4.
cases_point b' A.
solve[auto].
cases_point b A.
cases_point a A.
intuition.
exists l4.
repeat split; auto.
unfold inter;elim a2_exist;simpl;intros;use_all;solve [auto].

collapse.
replace (inter l1 l) with C.
solve_col.
unfold inter;elim a2_exist;simpl;intros;use_all;collapse.

cases_line l1 l4.
not_eq a b.
not_eq a c.

cases_point b c.

replace (inter l4 l2) with c.
solve [auto].
unfold inter; elim a2_exist; simpl;intros; geo_norm; collapse.
collapse;remove_inter_occ;solve [auto].

cases_line l1 l0.
remove_inter_occ.
solve [solve_col].

cases_line l4 l0.
cases_point b c.
intuition.
cases_point b' c.
auto.
collapse.
remove_inter_occ.
solve_col.

cases_line lAC l2.
cases_point c B.
exists lBF.
repeat split;auto.
unfold inter; elim a2_exist;simpl;intros;use p;solve [auto].
collapse.
exists x.
repeat split;auto.
unfold inter; elim a2_exist;simpl;intros;use p;solve [auto].

cases_line lAC l.
replace (inter x lBF) with B.
solve [solve_col].
unfold inter; elim a2_exist;simpl;intros;use p;solve [collapse].

cases_line lAC l1.
remove_inter_occ.
solve [solve_col].

not_eq a b.

not_eq a c.
not_eq a b'.
not_eq A a.
not_eq b' a.
not_eq C a.

not_eq b c.
not_eq b b'.
not_eq C b.
not_eq A b.

not_eq A c.
not_eq c b'.
not_eq C c.

not_eq A b'. 
not_eq A C.

not_eq b' C.

assert (dist6 a b c A b' C) 
  by (unfold dist6;assumptions_or_sym).

assert (Col A b' C) by solve_col.

assert (is_on_inter F a b' A b) by (unfold is_on_inter;split;solve_col).
assert (is_on_inter B a C A c) by (unfold is_on_inter;split;solve_col).

create_line c b' lcb'.
create_point l1 lcb' P.

assert (is_on_inter (inter l1 lcb') b C b' c).
  unfold is_on_inter;split.

  exists l1;
  repeat split;auto;
  unfold inter;
  elim (a2_exist);intro;
  simpl;intuition.

  exists lcb';
  repeat split;auto;
  unfold inter;
  elim (a2_exist);intro;
  simpl;intuition.

assert (Col F (inter l1 lcb') B)
  by (apply (HPappus a b c A b' C F (inter l1 lcb') B);auto || solve_col).

replace (inter l1 lcb') with (inter l1 lBF) in *.

geo_norm.
collapse.

solve_col.

geo_norm.
collapse.

unfold inter at 1.
elim a2_exist;intro;simpl.
intros;use p;collapse.
Qed.



