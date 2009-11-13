(*
   Grands entiers.
   Les algorithmes sont ceux qu'on apprend a l'ecole primaire.
*)

(*********************************************************************** 
   1. Entiers naturels 
*)

(* liste de chiffres en base base (= plus grande puissance de 10 < racine de max_int),
   un chiffre etant un int *)

type nat = int list

(* recherche de la base *)

let calc_base () =
  let r = truncate (sqrt (float max_int)) in
  let b=ref 1 in
  let n = ref 0 in
    while !b<r do b:=(!b)*10; n:=(!n)+1; done;
    ((!b)/10, (!n)-1)

let (base,logbase) = calc_base ()

let string_of_nat x =
  match x with
    |[]->"0"
    |_ -> let rec f x = match x with
	 |[]-> ""
	 |c::y -> let s = ref (string_of_int c) in
	     if y<>[]
	     then (for i=1 to (logbase - (String.length (!s))) do s:="0"^(!s); done);
	     (f y)^(!s)
       in f x

let nat_of_string s =
  let n = String.length s in
  let q = n/logbase in
  let r = n mod logbase in
  let x = ref [] in
    if r<>0 then x:=[int_of_string (String.sub s 0 r)];
    for i = 0 to q-1 do
      let c = int_of_string (String.sub s (r+i*logbase) logbase) in
	x:=c::(!x);
    done;
  !x

(* enleve les zeros de poids fort *)
let rec norm_nat x =
  match x with
    |[] -> x
    |cx::x1 -> let y = norm_nat x1 in
	if y<>[]
	then cx::y
	else if cx=0 then [] else [cx]

(* les operations suivantes rendent un nat normalise si les arguments le sont *)
(* x + y + c *)
let rec add_natc x y c =
  match (x,y) with
    |[],[] -> if c=0 then [] else [c]
    |cx::x1, [] | [], cx::x1 ->
       let s = cx+c in
	 if s>base
	 then let q=s/base and r=s mod base in
	   r::(add_natc x1 [] q)
	 else s::x1
    |cx::x1, cy::y1 ->
       let s = cx+cy+c in (* la base est assez grande: 3base < base^2 *)
       let q=s/base and r=s mod base in
	 r::(add_natc x1 y1 q)

let add_nat x y = add_natc x y 0
      
(* k*x + c *)
let rec mult_int_nat k x c=
  match x with
    |[]-> if c=0 then [] else [c]
    |cx::x1 -> let p=k*cx+c in
      let q=p/base and r=p mod base in
	r::(mult_int_nat k x1 q)

let rec mult_nat x y =
  match (x,y) with
    |[],_ |_,[] -> []
    |cx::x1, y ->
       add_nat (mult_int_nat cx y 0) (0::(mult_nat x1 y))

(* arguments normalises *)
let rec compare_nat x y =
  match (x,y) with
    |[],[] -> 0
    |[],_ -> -1
    |_,[] -> 1
    |cx::x1,cy::y1 ->
       (match compare_nat x1 y1 with
	  |0 -> compare cx cy
	  |a->a)
       
let lt_nat x y = (compare_nat x y)=(-1)
let le_nat x y = (compare_nat x y)<=0
let gt_nat x y = (compare_nat x y)=1
let ge_nat x y = (compare_nat x y)>=0

(* soustraction x-y dans le cas ou x>=y *)

(* x - (y+c) *)
let rec moins_natc x y c =
  match (x,y) with
    |[],_ -> x
    |_,[]->  if c=1 then moins_natc x [1] 0 else x
    |cx::x1,cy::y1 ->
       let cyc = cy+c in
	 if cyc<=cx
	 then (let r = moins_natc x1 y1 0 in
	       let a = cx-cyc in
	      if r=[] && a=0
	      then []
	      else a::r)
	 else (let r = moins_natc x1 y1 1 in
	       let a = (base+cx)-cyc in
	      if r=[] && a=0
	      then []
	      else a::r)

let moins_nat x y =
  moins_natc x y 0
    
(* division euclidienne *)

let hdn l n =
  let r = ref [] in
  let l1= ref l in
    for i=1 to n do
      r:=(List.hd (!l1))::(!r);
      l1:=List.tl (!l1);
    done;
    List.rev (!r)

let tln l n =
  let l1= ref l in
    for i=1 to n do
      l1:=List.tl (!l1);
    done;
    !l1

(* chiffres forts en tete pour x,y en queue pour xr,yr *)
(* quotient, par dichotomie:
   q tel q*y <= x < (q+1)*y
*)

let div2 x y xr yr =
  let q = (match (x,y) with
	     |cx1::_,cy1::_ -> cx1/cy1
	     |_-> assert false) in
  let q1 = ref 0 in
  let p1 = ref [] in
  let q2 = ref base in
  let p = mult_nat [q] yr in
    if (le_nat p xr)
    then (q1:=q;
	  p1:=p)
    else q2:=q;
    while ((!q2)>(!q1)+1) do
      let q = ((!q2)+(!q1))/2 in
      let p = mult_nat [q] yr in
	if (le_nat p xr)
	then (q1:=q;p1:=p)
	else q2:=q;
    done;
    let q= !q1 in
    let r = moins_nat xr (!p1) in
      (q,r)
      

let rec div3 x1 x1r x2 y yr =
  let (q,r) = div2 x1 y x1r yr in 
    match x2 with
      |[] -> ([q],r)
      |a::x3 -> let (q1,r1)=(div3 (List.rev (a::r)) (a::r) x3 y yr) in
	  (q1@[q], r1)
	  
(* rend (q,r) , chiffres forts en tete pour x,y *)
let rec div1 x y =
  match (x,y) with
    |[],_ -> ([],[])
    |_,[]-> failwith " division par zero"
    |[cx],[cy] -> ([cx/cy],[cx mod cy])
    |[cx],_ -> ([],x)       (* x<y *)
    |_ ->
       let yr = List.rev y in
       let ny = List.length y in
       let x1 = hdn x ny in
       let x2 = tln x ny in
       let x1r = List.rev x1 in
	 div3 x1 x1r x2 y yr

let div_eucl x y =
  let (q,r) = div1 (List.rev x) (List.rev y) in
  let q = norm_nat q in
  let r = norm_nat r in
    (q,r)

(*********************************************************************** 
     2. Entiers relatifs
*)
	
type entiers = P of nat | N of nat | Z

let norm_ent x =
  match x with
    |P n -> let m = norm_nat n in
	 if m=[] then Z else P m
    |N n -> let m = norm_nat n in
	 if m=[] then Z else N m
    |Z -> Z

let string_of_ent x =
  match x with
    |Z -> "0"
    |P n -> string_of_nat n
    |N n -> "-"^(string_of_nat n)

let ent_of_string s =
  if s="0"
  then Z
  else if (String.sub s 0 1)="-"
  then N (nat_of_string (String.sub s 1 ((String.length s)-1)))
  else P (nat_of_string s)

let add_ent x y =
  match (x,y) with
    |Z,_ -> y
    |_,Z -> x
    |P x1, P y1 -> P (add_nat x1 y1)
    |N x1, N y1 -> N (add_nat x1 y1)
    |P x1, N y1 -> (match compare_nat x1 y1 with
		      |0 -> Z
		      |(-1) -> N (moins_nat y1 x1)
		      |1|_ -> P (moins_nat x1 y1))
    |N x1, P y1 -> (match compare_nat x1 y1 with
		      |0 -> Z
		      |(-1) -> P (moins_nat y1 x1)
		      |1|_ -> N (moins_nat x1 y1))

  
let opp_ent x =
  match x with
    |Z -> Z
    |P n -> N n
    |N n -> P n

let moins_ent x y =
  add_ent x (opp_ent y)
    

let mult_ent x y =
  match (x,y) with
    |Z,_ -> Z
    |_,Z -> Z
    |P x1, P y1 |N x1, N y1 -> P (mult_nat x1 y1)
    
    |P x1, N y1  |N x1, P y1 -> N (mult_nat x1 y1)

let div_ent x y =
  match (x,y) with
    |Z,_ -> Z
    |_,Z -> failwith "division par zero"
    |P x1, P y1 |N x1, N y1 -> let r = fst (div_eucl x1 y1) in
	 if r=[] then Z else P r    
    |P x1, N y1  |N x1, P y1 -> let r = fst (div_eucl x1 y1) in
	 if r=[] then Z else N r 

let mod_ent x y =
  match (x,y) with
    |Z,_ -> Z
    |_,Z -> failwith "modulo zero"
    |P x1, P y1 |N x1, N y1 -> let r = snd (div_eucl x1 y1) in
	 if r=[] then Z else P r    
    |P x1, N y1  |N x1, P y1 -> let r = snd (div_eucl x1 y1) in
	 if r=[] then Z else N r 

let ent_of_int x =
  if x=0 then Z
  else if x<0 then N [-x]
  else P [x]

let eq_ent = (=)

let lt_ent x y =
  match (x,y) with
    |Z,Z -> false
    |Z,P _ -> true
    |Z,N _ -> false
    |P _,Z -> false
    |N _,Z -> true
    |P x1, P y1 -> lt_nat x1 y1
    |N x1, N y1 -> lt_nat y1 x1   
    |P _, N _  -> false
    |N _, P _ -> true

let le_ent x y = (eq_ent x y) || (lt_ent x y)

let abs_ent x =
  match x with
    |Z ->Z
    |P n -> P n
    |N n -> P n

let ent0 = Z
let ent1 = P [1]

let int_of_ent x =
  match x with
    |Z->0
    |P [n] -> n
    |N [n] -> -n
    |P [n;m] -> n+base*m
    |N [n;m] -> -(n+base*m)
    |_ -> failwith ("int_of_ent: "^(string_of_ent x))

let hash_ent x =
  match x with
    |Z->0
    |P (n::m::_) ->  n+base*m
    |N (n::m::_) ->  -(n+base*m)
    |P n -> List.hd n
    |N n -> -(List.hd n)

let signe_ent x =
  match x with
    |P _ -> 1
    |N _ -> -1
    |Z -> 0
