Require Export hexamys.

Lemma a_chasles_th : forall A B C P Q II J K I' K' J' X, hexamy -> 
dist6 II I' Q K K' P ->
line B K <> line B II ->
B<> P -> B<> Q -> P<> C -> Q<> C ->
B<> K -> B <> II -> Q<>A -> P<>A ->
is_on_inter II P B Q C ->
is_on_inter I' P C Q B ->
is_on_inter J P C Q A ->
is_on_inter J' P A Q C ->
is_on_inter K P A Q B ->
is_on_inter K' P B Q A ->
is_on_inter X II I' K K' ->
Col X J J'.
Proof.
intros.
unfold is_transverse, is_on_inter, dist6 in *.
geo_norm.
remove_line_occ.
collapse.
not_eq x x0.
not_eq x5 x12.
not_eq x8 x9.

hexamy_proof  II I' Q  K K' P II I' P K K' Q .
Qed.
