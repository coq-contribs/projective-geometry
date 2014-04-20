Require Export hexamys.

Lemma pseudo_midpoint : hexamy -> forall II J K A B P Q H M L N O,
  dist6 P M L Q N H -> 
  dist6 A B II J O Q ->
  A<>K -> B<>K ->
  is_on_inter P II B J A ->
  is_on_inter Q II A J B ->
  is_on_inter O M N P Q ->
  is_on_inter H II B A K ->
  is_on_inter M B K J A ->
  is_on_inter N A K J B ->
  is_on_inter L A II K B ->
  Col II J K ->  
  Col O A B.
Proof.
intro Hhex;intros.
geo_norm.

create_line M L lML.
create_line H N lHN.
create_line L Q lLQ.
create_line H P lHP.
create_line P M lPM.
create_line Q N lQN.

cases_line lML lHN.
solve_col.

not_eq x12 x11.
not_eq x12 x10.
not_eq lLQ x11.
not_eq x3 x11.
not_eq lLQ lHN.
not_eq A B.
not_eq x8 x7.

collapse.

hexamy_proof P M L Q N H P Q L M N H.
Qed.
