Require Export hexamys.

Definition cevian_in A B C A' B' C' O :=
Col A' B C /\ Col B' A C /\ Col C' A B /\ 
Col O A A' /\ Col O B B' /\ Col O C C'.

Lemma cevian_lines : hexamy -> forall A B C A' B' C' P Q O,
  dist6 A B C A' B' C' ->
  dist6 P Q O A' B' C' ->
  dist6 P Q O A B C ->
  line P C <> line Q B ->
  Col Q C A' ->
  Col B P A' ->
  Col C P B' ->
  Col A Q B' ->
  Col B Q C' ->
  Col A P C' ->
  Col B B' O ->
  Col C C' O ->
  Col A A' O.
Proof.
intros.
unfold dist6 in *.
geo_norm.

create_inter B' P C' Q X.
remove_line_occ.
collapse.

not_eq x x0.
not_eq x6 x5.
not_eq x3 x1.

hexamy_proof B B' P C C' Q B B' Q C C' P.
Qed.



