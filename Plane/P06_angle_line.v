Require Export hexamys.

Lemma angle_line : hexamy -> forall O S O' A A' R M X Y,
  dist6 O S O' A A' R ->
  line A R <> line O S ->
  Col O O' S ->
  Col R A A' ->
  Col M O A ->
  Col M O' A' ->
  Col X S A ->
  Col X R O' ->
  Col Y S A' ->
  Col Y R O ->
  Col M X Y.
Proof.
intros.
unfold dist6 in *.
geo_norm.

create_inter A R O' S Z.
collapse.
remove_line_occ.
not_eq x3 x4.
not_eq x x0.
not_eq x1 x2.

hexamy_proof O A R A' O' S O A S A' O' R.
Qed.
