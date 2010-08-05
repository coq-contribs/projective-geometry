Require Export hexamys.
Require Export P07_cevian_lines.

Lemma cevian_lines_2 : hexamy -> forall A B C A' B' C' A'' B'' C'' O' O'' P,
dist6 A B C A' B' C' ->
dist6 A B C A'' B'' C'' ->
dist6 A' B' C' A'' B'' C'' ->
line A' B'' <> line A'' B' ->
cevian_in A B C A' B' C' O' ->
cevian_in A B C A'' B'' C'' O'' ->
Col P A' B'' ->
Col P B' A'' ->
Col P O' O''.
Proof.
intros.
unfold dist6 in *.
unfold cevian_in in *.
geo_norm.
remove_line_occ.
collapse.
not_eq x11 x12.
not_eq x6 x5.
not_eq x9 x8.
not_eq x3 x2.
hexamy_proof A' B'' A B' A'' B  A' B'' B B' A'' A.
Qed.
