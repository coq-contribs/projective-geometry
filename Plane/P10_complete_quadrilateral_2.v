Require Export hexamys.

Lemma complete_quadrilateral_2 : hexamy ->
forall A B C A' B' C' II J P Q,
  dist6 B C B' C' II J ->
 dist6 A B C A' B' C' ->
 line A' B' <> line B C ->
 is_transverse A' B' C' A B C ->
 Col II C C' -> 
 Col J B B' ->
 is_on_inter P B' II C' J ->
 is_on_inter Q B II C J ->
 Col A P Q.
Proof.
intros.
unfold is_transverse, is_on_inter, dist6 in *.
geo_norm.
remove_line_occ.

create_inter B J C' II X.
collapse.

not_eq l l0.
not_eq x x0.
not_eq x1 x2.
not_eq x4 x5.

hexamy_proof C B J B' C' II  B C' J C B' II.
Qed.
