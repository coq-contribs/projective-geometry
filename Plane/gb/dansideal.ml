(* 
      Calcul de bases de Grobner.

On utilise une representation creuse des polynomes:
un monome est un tableau d'exposants (un par variable), avec son degre en tete.
un polynome est une liste de (coefficient,monome).

L'algorithme de Buchberger a proprement parler est tire du code caml 
extrait du code Coq ecrit par L.Thery.

*)

(* Utile pour les operations sur les coefficients qui sont des entiers non bornes. *)
open Polynomes2

(***********************************************************************

    Monomials.

*)

let hmon = Hashtbl.create 1000;;

type mon = int array;;

(* pour le moment d représente le nb de variable du monome *)

(* Multiplication de monomes ayant le meme nb de variables = d *)
let mult_mon d m m' =
  let m'' = Array.create (d+1) 0 in
  for i=0 to d do
     m''.(i)<- (m.(i)+m'.(i));
  done;
  m''
;;
(* Degré d'un monome *)
let deg m = m.(0)
;;

(* Comparaison de monomes avec ordre lexicographique = on commence par regarder la 1ere variable*)
let compare_mon d m m' =
  let res=ref 0 in
  let i=ref 1 in
    while (!res=0) && (!i<=d) do
      res:= (compare m.(!i) m'.(!i));
      i:=!i+1;
    done;
    !res
;;

(* Division de monome ayant le meme nb de variables *)
let div_mon d m m' =
  let m'' = Array.create (d+1) 0 in
  for i=0 to d do
     m''.(i)<- (m.(i)-m'.(i));
  done;
  m''
;;

(* m' divise m  *)
let div_mon_test d m m' =
        let res=ref true in
        let i=ref 1 in
        while (!res) && (!i<=d) do
            res:= (m.(!i) >= m'.(!i));
            i:=succ !i;
        done;
        !res
;;

(* Mise en place du 'vrai' degré du monome *)
let set_deg d m =
  m.(0)<-0;
  for i=1 to d do
     m.(0)<-  m.(i)+m.(0);
  done;
  m
;;

(* ppcm de monomes *)
let ppcm_mon d m m' =
  let m'' = Array.create (d+1) 0 in
  for i=1 to d do
     m''.(i)<- (max m.(i) m'.(i));
  done;
  set_deg d m''
;;


(**********************************************************************

    Terms and polynomials.

*)

(*
    A pretty printer for polynomials, with Maple-like syntax.
*)

open Format;;

let print_pol zeroP hdP tlP coefterm monterm string_of_coef
              dimmon string_of_exp lvar p =

   let rec print_mon m coefone =
      let s=ref [] in
      for i=1 to (dimmon m) do
        (match (string_of_exp m i) with
          "0" -> ()
        | "1" -> s:= (!s) @ [(List.nth !lvar (i-1))]
        | e -> s:= (!s) @ [((List.nth !lvar (i-1)) ^ "^" ^ e)]);
      done;
      (match !s with
         [] -> if coefone 
               then print_string "1"
               else ()
       | l -> if coefone 
              then print_string (String.concat "*" l)
              else (print_string "*"; 
                    print_string (String.concat "*" l)))
   and print_term t start = let a = coefterm t and m = monterm t in
         match (string_of_coef a) with
                  "0" -> ()
                | "1" ->(match start with
                          true -> print_mon m true
                         |false -> (print_string "+ ";
                                    print_mon m true))
                | "-1" ->(print_string "-";print_space();print_mon m true)
                | c -> if (String.get c 0)='-'
                       then (print_string "- ";
                             print_string (String.sub c 1 
                                              ((String.length c)-1));
                             print_mon m false)
                       else (match start with
                              true -> (print_string c;print_mon m false)
                             |false -> (print_string "+ ";
                                        print_string c;print_mon m false))
   and printP p start = 
      if (zeroP p)
      then (if start 
            then print_string("0")
            else ())
      else (print_term (hdP p) start;
            if start then open_hovbox 0;
            print_space();
            print_cut();
            printP (tlP p) false)
   in open_hovbox 3;
      printP p true;
      print_flush()
;;

let name_var= ref []
;;

let printP = print_pol 
    (fun p -> match p with [] -> true | _ -> false)
    (fun p -> match p with (t::p) -> t |_ -> failwith "print_pol dans dansideal")
    (fun p -> match p with (t::p) -> p |_ -> failwith "print_pol dans dansideal")
    (fun (a,m) -> a)
    (fun (a,m) -> m)
    string_of_coef
    (fun m -> (Array.length m)-1)
    (fun m i -> (string_of_int (m.(i))))
    name_var
;;

let rec lprintP l =
  match l with
    [] -> ()
   |p::l -> printP p;print_string "\n"; lprintP l
;;

(* somme de polynomes= liste de couples (int,monomes) *)
let plusP d p q =
 let rec plusP p q =
  match p with
   [] -> q
  |t::p' -> 
     match q with
       [] -> p
      |t'::q' ->
          match compare_mon d (snd t) (snd t') with
            1 -> t::(plusP p' q)
           |(-1) -> t'::(plusP p q')
           |_ -> let c=plus_coef (fst t) (fst t') in
                 match eq_coef c coef0 with
                   true -> (plusP p' q')
                  |false -> (c,(snd t))::(plusP p' q')
 in plusP p q
;;

(* multiplication d'un polynome par (a,monome) *)
let mult_t_pol d a m p =
  let rec mult_t_pol p =
    match p with
      [] -> []
     |(b,m')::p -> ((mult_coef a b),(mult_mon d m m'))::(mult_t_pol p)
  in mult_t_pol p
;;

(* Retourne un polynome de l dont le monome de tete divise m,  [] si rien *)
let rec selectdiv d m l =
  match l with
    [] -> []
   |q::r -> let m'= snd (List.hd q) in
            match (div_mon_test d m m') with
               true -> q
              |false -> selectdiv d m r
;;

(* Retourne un polynome générateur 'i' à d variables *)
let gen d i =
  let m = Array.create (d+1) 0 in
  m.(i) <- 1;
    let m = set_deg d m in 
  [((coef_of_int 1),m)]
;;

(* multiplication d'un polynome par un coefficient par 'a' *)
let emultP d a p =
  let rec emultP p =
    match p with
      [] -> []
     |(b,m')::p -> ((mult_coef a b),m')::(emultP p)
  in emultP p
;;

let pgcd a b  = Polynomes2.pgcd (abs_coef a) (abs_coef b)

(* contenu d'un polynome = pgcd des coefs *)
let rec content p =
  match p with
    [] -> (coef_of_int 1)
   |(a,m)::[] -> a
   |(a,m)::p -> (pgcd a (content p))
;;

(* normalisation d'un polynome *)
let normalize d p =
  let c = content p in
  let rec norm p =
     match p with
      [] -> []
     |(a,m)::p' -> ((div_coef a c),m)::(norm p')
  in norm p
;;

(* divise p par q: rend le reste.
on a lt(p) = -a*m*lt(q)
*)

let ndiv = ref 0;;

let infodiv s =
(*     print_string s;flush stdout; *)
    ndiv:=!ndiv+1
;;

let div_pol d p q a b m = infodiv ".";
                         plusP d (emultP d a p) (mult_t_pol d b m q)
;;

(*
let div_pol d p q a m = infodiv ".";
                         plusP d p (mult_t_pol d a m q)
;;
*)
(* reste de la division de p par les polynomes de l *)


let reduce2 d p l =
  let rec reduce p =
   match p with
    [] -> (coef1,[])
   |t::p' -> let (a,m)=t in
             let q = (try Hashtbl.find hmon m 
                            with Not_found -> 
                             let q = selectdiv d m l in
                             match q with 
                               t'::q' -> (Hashtbl.add hmon m q;q)
                              |[] -> q) in
             match q with
                  [] -> let (c,r)=(reduce p') in
                        (c,((mult_coef a c,m)::r))
                 |(b,m')::q' -> 
                     let c=(pgcd a b) in
                     let a'= (div_coef b c) in
                     let b'=(opp_coef (div_coef a c)) in
                     let (e,r)=reduce (div_pol d p' q' a' b'
                                         (div_mon d m m')) in
                     (mult_coef a' e,r)
  in let (c,r) = reduce p in
     r
;;

let reduce d p l =
  let rec reduce p =
   match p with
    [] -> (coef1,[])
   |t::p' -> let (a,m)=t in
             let q = selectdiv d m l in
             match q with
                  [] -> let (c,r)=(reduce p') in
                        (c,((mult_coef a c,m)::r))
                 |(b,m')::q' -> 
                     let c=(pgcd a b) in
                     let a'= (div_coef b c) in
                     let b'=(opp_coef (div_coef a c)) in
                     let (e,r)=reduce (div_pol d p' q' a' b'
                                         (div_mon d m m')) in
                     (mult_coef a' e,r)
  in let (c,r) = reduce p in
     r
;;

(*
let reduce2 d p l =
  let rec reduce p =
   match p with
    [] -> []
   |t::p' -> let (a,m)=t in
             let q = (try Hashtbl.find hmon m 
                            with Not_found -> 
                             let q = selectdiv d m l in
                             match q with 
                               t'::q' -> (Hashtbl.add hmon m q;q)
                              |[] -> q) in
             match q with
                  [] -> t::(reduce p')
                 |(b,m')::q' -> (reduce (div_pol d p' q'
                                         (oppcoef
                                           (divcoef a b))
                                         (div_mon d m m')))
  in reduce p
;;

let reduce d p l =
  let rec reduce p =
   match p with
    [] -> []
   |t::p' -> let (a,m)=t in
             let q = selectdiv d m l in
             match q with
                  [] -> t::(reduce p')
                 |(b,m')::q' -> (reduce (div_pol d p' q'
                                         (oppcoef
                                           (divcoef a b))
                                         (div_mon d m m')))
  in reduce p
;;
*)
(* m'' = ppcm des monomes de tete de p et q *)

let spol d p q=
   let m = snd (List.hd p) in
   let m'= snd (List.hd q) in
   let a = fst (List.hd p) in
   let b = fst (List.hd q) in
   let p'= List.tl p in
   let q'= List.tl q in
   let c=(pgcd a b) in
   let m''=(ppcm_mon d m m') in
   plusP d (mult_t_pol d (div_coef b c) (div_mon d m'' m) p')
           (mult_t_pol d (opp_coef (div_coef a c))
                         (div_mon d m'' m') q')
;;
(*
let spol d p q=
   let (a,m)::p' = p in
   let (b,m')::q' = q in
   let m''=(ppcm_mon d m m') in
   plusP d (mult_t_pol d (invcoef a) (div_mon d m'' m) p')
           (mult_t_pol d (oppcoef (invcoef b)) (div_mon d m'' m') q')
;;
*)
(* spolynomes provoques par l'ajout d'un polynome *)

type 'poly cpRes =
    Keep of ('poly list)
  | DontKeep of ('poly list)
;;



let foreigner d p p'=
        let m = snd (List.hd p) in
        let m'= snd (List.hd p') in
        let res=ref true in
        let i=ref 1 in
        while (!res) && (!i<=d) do
            res:= (m.(!i) = 0) || (m'.(!i)=0);
            i:=!i+1;
        done;
        !res
;;

let list_rec f0 f1 =
  let rec f2 = function
    [] -> f0
  | a0::l0 -> f1 a0 l0 (f2 l0)
  in f2
;;

let div_ppcm d p p' p'' =
  let m = snd (List.hd p) in
  let m'= snd (List.hd p') in
  let m''= snd (List.hd p'') in
  let res=ref true in
  let i=ref 1 in
    while (!res) && (!i<=d) do
      res:= ((max m.(!i) m'.(!i)) >= m''.(!i));
      i:=!i+1;
    done;
    !res
;;

let addRes i = function
    Keep h'0 -> Keep (i::h'0)
  | DontKeep h'0 -> DontKeep (i::h'0)
;;


let npairelim = ref 0;;

let infoelim s =
(*    print_string s;flush stdout;*)
    npairelim:=!npairelim+1
;;

let slice d i a q =
  list_rec
    (match foreigner d i a with
       true -> infoelim "*";DontKeep []
     | false -> Keep [])
  (fun b q1 rec_ren ->
    match div_ppcm d i a b with
      true ->  infoelim "+";DontKeep (b::q1)
    | false ->
        (match div_ppcm d i b a with
           true -> infoelim "#";rec_ren
         | false -> addRes b rec_ren)) q
;;

let slice2 d i a q =
   let rec slice1 q =
     match q with
       [] ->  []
      |b::q1 -> match div_ppcm d i b a with
                          true -> infoelim "#"; slice1 q1
                        | false -> b::(slice1 q1)
   in let rec slice2 q =
        match q with
          [] ->  Keep []
         |b::q1 ->
            match div_ppcm d i a b with
              true -> infoelim "+"; DontKeep (b::(slice1 q1))
            | false -> (match div_ppcm d i b a with
                          true -> infoelim "#"; slice2 q1
                        | false -> addRes b (slice2 q1))
   in match foreigner d i a with
       true -> infoelim "*"; DontKeep (slice1 q)
     | false -> (slice2 q)
;;
(* 
slice:
Paires eliminees: 2136
Divisions: 1648
Paires reduites a zero: 75
Paires donnant un nouveau polynome: 37
temps natif: 3.54s user

slice2:
Paires eliminees: 745
Divisions: 1724
Paires reduites a zero: 79
Paires donnant un nouveau polynome: 37
temps natif: 3.51s user
*)
let rec addS x l = l @[x]
;;

let genPcPf d i aP q =
  (let rec genPc aP0 =
    match aP0 with
      [] -> (fun r -> r)
    | a::l1 -> 
	(fun l ->
        (match slice d i a l1 with
          Keep l2 -> addS (spol d i a) (genPc l2 l)
        | DontKeep l2 -> genPc l2 l))
 in genPc aP) q
;;

let genOCPf d h' =
  list_rec [] (fun a l rec_ren ->
    genPcPf d a l rec_ren) h'
;;

let rec redd d l l2 =
  match l with 
|  [] -> []
| (a::p) -> let l22= l2@p in
                  let pol = normalize d (reduce d a l22) in
                 ( match pol with 
                  [] -> redd d p l2 
                 | _ -> (pol::(redd d p (pol::l2))))
;;




(* buchberger *)


let prod_rec f = function
  (x0, x) -> f x0 x
;;

let npairzero = ref 0;;

let infonpairzero s =
(*    print_string s;flush stdout;*)
    npairzero:=!npairzero+1
;;

let npairnew = ref 0;;

let infonpairnew s =
(*    print_string s;flush stdout;*)
    npairnew:=!npairnew+1
;;

let step = ref 0;;

let infobuch p q =
   if !step = 0 
      then (print_string ("[" ^ (string_of_int (List.length p))
                          ^ "," ^  (string_of_int (List.length q))
                          ^ "]\n");flush stdout)
;;
(***********************************************************************)
let pbuchf d pq =
  step:=0;
  Hashtbl.clear hmon;
  let rec pbuchf x = 
    prod_rec (fun p q ->
(*      infobuch p q; 
      step:=(!step+1)mod 10;*)
      match q with
        [] -> p
      | (a::q2) ->
          let a0=normalize d (reduce2 d a p) in
            match a0 with
              [] -> infonpairzero "0";pbuchf (p, q2)
            | _ ->  (* printP a0;*)
                infonpairnew "n";
                 pbuchf
                  (((addS a0 p),
                         (genPcPf d a0 p q2)))) x
  in pbuchf pq 
;;

let buch d p =
  npairelim:= 0;
  ndiv:= 0;
  npairzero:= 0;
  npairnew:= 0;
  let r = redd d (pbuchf d (p, (genOCPf d p))) [] in
  (*print_string "\nPaires eliminees: ";print_int !npairelim;
  print_string "\nDivisions: ";print_int !ndiv;
  print_string "\nPaires reduites a zero: ";print_int !npairzero;
  print_string "\nPaires donnant un nouveau polynome: ";print_int !npairnew;
  print_string "\n";*)
  r     
;;

(* Multiplication de polynomes *)
let rec multP d p q =
  match p with 
    [] -> []
   |(a,m)::p' -> (plusP d (mult_t_pol d a m q) (multP d p' q))
;;

(* Retourne un polynome p^n *)
let rec powerP d p n =
  match n with
      0 -> [(coef1,Array.create (d+1) 0 )]
    |_ -> multP d p (powerP d p (n-1))

(* Retourne un monome transformé en polynome dans lequel on a substitué la variable v par le polynome q *) 
let substM d m v q =
  let m1 = Array.copy m in
  let n = m1.(v) in
  let qn=powerP d q n in
    m1.(v)<-0;
    multP d [(coef1,m1)] qn

(* Retourne polynome p dans lequel on a substitué à la variable v le polynome q *)
let substP d p v q =
  List.fold_left (fun r (c,m) ->
                    (plusP d r (emultP d c (substM d m v q))))
    [] p

(* Substition monome spéciale pour deg_nullstellensatz *)
let specialsubstP d p v cte =
  List.map (fun (ci,mi) ->
              if false (* mi.(v) = 0 *) then
                mi.(v) <- 0
              else
                mi.(v) <- cte - mi.(v);
              (ci,mi))
    (*  (ci,snd (List.nth (substM d mi v (powerP d q (cte - mi.(v)))) 0))) *)
    p
