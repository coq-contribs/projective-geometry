Require Export hexamys.

Lemma almost_pappus : hexamy -> forall P S Q O O' A A' X M,
dist6 P O S O' Q M ->
line Q M <> line O S ->
Col O O' S ->
Col M P Q ->
Col A S P ->
Col A O M ->
Col A' S Q ->
Col A' O' M ->
Col X O Q ->
Col X P O' ->
Col X A A'.
Proof.

intros.
unfold dist6 in *.
geo_norm.
create_inter O S Q M Y.
collapse.
remove_line_occ.

not_eq x x0.
not_eq x1 x2.
not_eq x3 x4.

hexamy_proof  P O S O' Q M  P O' M O Q S.

Qed.