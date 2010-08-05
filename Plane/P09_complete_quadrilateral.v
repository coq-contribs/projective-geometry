Require Export hexamys.

Lemma complete_quadrilateral : hexamy -> 
  forall A B C A' B' C' A'' B'' C'' P Q R,
  A<>B -> A<>C -> B<>C ->
  dist6 A' B' C' A'' B'' C'' ->
  line A'' B'' <> line A' B' ->
  is_transverse A' B' C' A B C ->
  is_transverse A'' B'' C'' A B C ->
  is_on_inter P A' C'' A C ->
  is_on_inter Q B' A'' A B ->
  is_on_inter R C' B'' B C ->
  Col P Q R.
Proof.
intros.
unfold is_transverse, is_on_inter, dist6 in *.
geo_norm.

create_inter A'' B'' A' B' X.
collapse.
remove_line_occ.

create_line A' A'' lA'A''  .
create_line B' B'' lB'B''  .
create_line C' C'' lC'C''  .

not_eq x12 x11.
not_eq x1 x11.
not_eq x x12.
not_eq x10 x3.

hexamy_proof  A' A'' B'' C'' C' B' A'' B' B'' C' C'' A'.
Qed.
