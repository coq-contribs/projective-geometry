Require Export hexamys.

Lemma eolien : hexamy -> forall A B C A' B' C' A'' B'' C'', 
A<>B -> A<>C -> A<>A' -> A<>B' -> A<> C' ->
A<>A'' -> A<>B'' -> A<>C'' ->
B<>C -> B<>A' -> B<>B' -> B<> C' ->
B<>A'' -> B<>B'' -> B<>C'' ->
C<>A' -> C<>B' -> C<> C' ->
C<>A'' -> C<>B'' -> C<>C'' ->
A'<>B' -> A'<> C' ->
A'<>A'' -> A'<>B'' -> A'<>C'' ->
B'<> C' ->
B'<>A'' -> B'<>B'' -> B'<>C'' ->
C'<>A'' -> C'<>B'' -> C'<>C'' ->
A''<>B'' -> A''<>C'' ->
B''<>C'' ->
Col A' B C -> Col B' A C -> Col C' A B ->
Col A'' B' C' -> Col B'' A' C' -> Col C'' A' B' ->
Col B A'' C'' -> Col C A'' B'' -> Col A C'' B''.
Proof.
intros.
geo_norm.

elim (uniqdec.eq_line_dec x6 x3).
intro;subst;collapse;firstorder.
intro.

elim (uniqdec.eq_line_dec x1 x0).
intro;subst;collapse;firstorder.
intro.

remove_line_occ.

not_eq x x2.
not_eq x4 x5.

hexamy_proof B' A' C B A'' C' C A'' B C' A' B'.
Qed.
