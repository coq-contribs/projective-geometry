Require Export hexamys.

(* Hexamy implies Desargues *)

Lemma hexamy_desargues_gen_case : 
  hexamy ->
  forall O A B C A' B' C' I J K P Q,
  line A B <> line B C ->
  line A' B' <>  line B' C' ->
  line A' B' <> line A B ->
  line B' C' <> line B C ->
  line O A <> line O C ->
  line A' C' <> line A C ->
  O<>A -> O<>B -> O<>C ->
  O<>A' -> O<>B' -> O<>C' ->
  O<>I -> O<>J -> O<>K ->
  A<>B -> A<>C ->
  A<>A' -> A<>B' -> A<>C' ->
  A<>I -> A<>J -> A<>K ->
  B<>C ->
  B<>A' -> B<>B' -> B<>C' ->
  B<>I -> B<>J -> B<>K ->
  C<>A' -> C<>B' -> C<>C' ->
  C<>I -> C<>J -> C<>K ->
  A'<>B' -> A'<>C' ->
  A'<>I -> A'<>J -> A'<>K ->
  B'<>C' ->
  B'<>I -> B'<>J -> B'<>K ->
  C'<>I -> C'<>J -> C'<>K ->
  I<>J -> I<>K ->
  J<>K ->
  
  P<>C -> A<>Q -> 
  P<>C'-> A'<>Q ->
  Q<>C'-> A'<>P ->

  Col P B C ->
  Col P A' B' ->
  Col Q A B ->
  Col Q B' C' ->

  Col O A A' ->
  Col O B B' ->
  Col O C C' ->
  Col A' C' I ->
  Col A C I ->
  Col A B J ->
  Col A' B' J ->
  Col B C K ->
  Col B' C' K -> 
  Col I J K.
Proof.
intros.

geo_norm.
remove_line_occ.
collapse.
not_eq P Q.
not_eq A P.
not_eq C Q.

hexamy_proof  A A' P C C' Q A Q C' A' P C.
Qed.

Ltac not_eq_4pt A B C D := match goal with
H1: ?Incid A ?l,
H2: ?Incid B ?l,
H3: ?Incid C ?m,
H4: ?Incid D ?m|- _ => not_eq l m
end.


Lemma desargues_cevian_case :
 hexamy ->
 forall O A B C A' B' C' P Q R PI,
  line  A B <> line B C ->
  line A' B' <>  line B' C' ->
  line A' B' <> line A B ->
  line B' C' <> line B C ->
  line O A <> line O C ->
  line A' C' <> line A C ->
  A<>B   -> B<>C -> A<>C ->
  A'<>B'  -> B'<>C' -> A'<>C' ->
  A <> A' -> B <> B' -> C<>C' -> 
  O <> A -> O<> B -> O<>C ->
  O <> A' -> O<> B' -> O<> C' ->
  PI = inter (line O B) (line P Q) ->
  A' <> inter (line A' C') (line A PI) ->
  Col O A A' ->
  Col O B B' ->
  Col O C C' ->
  Col A' C' Q ->
  Col A C Q ->
  Col A B P ->
  Col A' B' P ->
  Col B C R ->
  Col B' C' R -> 
  Col A' B C ->
  Col B' A C ->
  Col C' A B -> 
  forall II, Col O B II -> Col P Q II -> O<>II -> 
  Col P Q R.
Proof.
intro hexa;
intros.
geo_norm.
remove_line_occ.
elim (uniqdec.eq_point_dec P Q);intros.
subst Q;create_line P R lPR;firstorder.

create_inter P Q B C R1.
create_inter P Q B' C' R2.
assert (R1 = R2).

create_inter A' C' A II L.
not_eq L B'.
create_inter A B L B' N.
not_eq A L.
create_inter A L C C' M.
collapse.
remove_line_occ.
assert (Col L N B') by firstorder.

not_eq II A.

not_eq P A'.
not_eq l8 l7.
not_eq A P.
not_eq B' II.

not_eq P II.
not_eq l0 l3.

not_eq Q C.

not_eq II Q.
not_eq A B.

not_eq O Q.
not_eq l2 l3.

not_eq B' Q.
not_eq II L.


not_eq_4pt L B' A P.
not_eq_4pt B' II P A'.
not_eq_4pt II A A' L.

not_eq_4pt P II L A'.
not_eq_4pt II B' A' A.


not_eq A II.
not_eq A' II.
not_eq L P.
not_eq B' P.
not_eq B' A.

not_eq A' L.

assert (Col O N Q) by
 hexamy_proof A' L B' II A P A' A P II B' L.

geo_norm;collapse.

not_eq x l7.
not_eq x l5.
not_eq x x0.
not_eq C II.
not_eq B II.
not_eq B Q.
not_eq A Q.

not_eq_4pt C B O II.
not_eq_4pt B A II Q.
not_eq_4pt A O Q C.

not_eq_4pt C O II A.
not_eq_4pt O Q A B.
not_eq_4pt Q II B C.


assert (Col R1 M N) by
  hexamy_proof C B A O II Q C O Q II A B.

geo_norm.

not_eq C' Q.
not_eq C' II.
not_eq Q L.
not_eq O L.

not_eq_4pt C' B' O II.
not_eq_4pt B' Q II L.
not_eq_4pt Q O L C'.
not_eq_4pt C' O II L.
not_eq_4pt O Q L B'.
not_eq_4pt Q II B' C'.
not_eq L C'.

assert (Col R2 M N) by
  hexamy_proof C' B' Q O II L C' O Q II L B'.

geo_norm.

cases_line x1 x2.
auto.

collapse.
intuition.

subst R2.
geo_norm;collapse;solve_col.
Qed.
