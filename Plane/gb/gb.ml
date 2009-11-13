(*


*)



(*
 * Xml Light, an small Xml parser/printer with DTD support.
 * Copyright (C) 2003 Nicolas Cannasse (ncannasse@motion-twin.com)
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

open Xml
open Dtd
open Num
open Unix
open Utile
open Entiers
open Polynomes2

let num_0 = Int 0
and num_1 = Int 1
and num_2 = Int 2
and num_10 = Int 10;;

let numdom r =
  let r' = Ratio.normalize_ratio (ratio_of_num r) in
  num_of_big_int(Ratio.numerator_ratio r'),
  num_of_big_int(Ratio.denominator_ratio r');;

(* ------------------------------------------------------------------------- *)
(*  term??                                                                   *)
(* ------------------------------------------------------------------------- *)

type vname = string;;

type term =
| Zero
| Const of Num.num
| Var of vname
| Opp of term
| Add of (term * term)
| Sub of (term * term)
| Mul of (term * term)
| Pow of (term * int);;

let mc = "MUTCONSTRUCT";;
let nc = "noConstr";;
let nu = "uri";;
let ma = "APPLY";;

let turi="cic:/gbtypes/term.ind";;
let tzero = "1";;  (* Zero: term *)
let tconst = "2";; (* Const: Z -> positive -> term *)

let tvar = "3";;   (* Var: positive -> term *)
let topp = "4";;   (* Opp: term *)
let tadd = "5";;   (* Add: term -> term -> term *)
let tsub = "6";;   (* Sub: term -> term -> term *)
let tmul = "7";;   (* Mul: term -> term -> term *)
let tpow = "8";;  (* Pow: term -> positive -> term *)

let luri (* uri *) ="cic:/gbtypes/lineq.ind";;
let lnil = "1";; (* lnil: lineq *)
let lceq = "2";; (* lceq: term -> lineq -> lineq *)


let zuri="cic:/Coq/ZArith/BinInt/Z.ind";;
let z0 = "1";; (* Z0: Z *)
let zpos = "2";; (* xO: positive ->  positive *)
let zneg = "3";; (* xH: positive *)


let puri="cic:/Coq/NArith/BinPos/positive.ind";;
let pxI = "1";; (* xI: positive ->  positive *)
let pxO = "2";; (* xO: positive ->  positive *)
let pxH = "3";; (* xH: positive *)

let mk_elt uri name l = Element(mc, [nu, uri; "noType", "0"; nc, name], l);;

let mk_app uri name l = 
  Element(ma, [], Element(mc, [nu, uri; "noType", "0"; nc, name], [])::l);;

let rec mk_pos n = 
  if n =/ num_1 then  mk_elt puri pxH []
  else if mod_num n num_2 =/ num_0 then
          mk_app puri pxO [mk_pos (quo_num n num_2)]
        else
          mk_app puri pxI [mk_pos (quo_num n num_2)];;

let mk_z z  = 
  if z =/ num_0 then  mk_elt zuri z0 []
  else if z >/ num_0 then
          mk_app zuri zpos [mk_pos z]
        else
          mk_app zuri zneg [mk_pos ((Int 0) -/ z)];;

let rec mk_term t  =  match t with
| Zero -> mk_elt turi tzero []
| Const r -> let (n,d) = numdom r in
               mk_app turi tconst [mk_z n; mk_pos d]     
| Var v -> mk_app turi tvar [mk_pos (num_of_string v)]     
| Opp t1 -> mk_app turi topp [mk_term t1]
| Add (t1,t2) -> mk_app turi tadd [mk_term t1; mk_term t2]
| Sub (t1,t2) -> mk_app turi tsub [mk_term t1; mk_term t2]
| Mul (t1,t2) -> mk_app turi tmul [mk_term t1; mk_term t2]
| Pow (t1,n) ->  if (n = 0) then 
                   mk_app turi tconst [mk_z num_1; mk_pos num_1]     
                 else
                   mk_app turi tpow [mk_term t1; mk_pos (num_of_int n)]
;;

let rec parse_pos p = match p with
| Element (_,_,[p1;p2]) ->
  let a = attrib p1 nc in
  if a = pxO then num_2 */ (parse_pos p2)
             else num_1 +/ (num_2 */ (parse_pos p2))
| _ -> num_1;;

let parse_z z = match z with
| Element (_,_,[p1;p2]) ->
  let a = attrib p1 nc in
  if a = zpos then parse_pos p2 else (num_0 -/ (parse_pos p2))
| _ -> num_0;;

 
let rec parse_term p = match p with
| Element (_,_,[p1;p2]) ->
    let a = attrib p1 nc in
    if a = tvar then Var (string_of_num (parse_pos p2))
    else if a = topp then Opp (parse_term p2)
    else Zero
| Element (_,_,[p1;p2;p3]) ->
    let a = attrib p1 nc in
    if a = tconst then Const ((parse_z p2) // (parse_pos p3))
    else if a = tadd then Add (parse_term p2, parse_term p3)
    else if a = tsub then Sub (parse_term p2, parse_term p3)
    else if a = tmul then Mul (parse_term p2, parse_term p3)
    else if a = tpow then Pow (parse_term p2, int_of_num (parse_pos p3))
    else Zero
| _ -> Zero;;


let rec parse_lineq l1 l2 l3 p = match p with
| Element (_,_,[]) -> ([],[],[])
| Element (_,_,[p1;p2;p3]) ->
  let (l4,l5,l6) = parse_lineq l1 l2 l3 p3 in
  let r = parse_term p2 in
  let a = attrib p1 nc in
  if a = lceq then (r::l4,l5,l6) else
  (l1,l2,l3)
| _ -> (l1,l2,l3);;

let rec parse_request p = match p with
| Element (_,_,[p1]) -> parse_lineq [] [] [] p1
| _ -> ([],[],[]);;

let rec parse_request2 p = match p with
| Element (_,_,[p1]) -> p1


(***********************************************************************)
(* Polynomes a coefficients fractionnaires *)
(* un polynome est represent'e par un polynome `a coefficient entiers 
   et un entier (par lequel on divise tous les coefficients *)

type polyf = coef * poly (* denominateur, polynome *)
;;

(* normalise c et les coef de p, rend c positif *)
let norm_polyf (c,p) =
  let a = content p in
  let b = pgcd (abs_coef a) (abs_coef c) in
  let b = if (lt_coef c coef0) then opp_coef b else b in
    (div_coef c b, div_int p b)
;;

let plusPf (c1,p1) (c2,p2) =
  norm_polyf
    (mult_coef c1 c2,
     plusP (multP (Pint c2) p1) (multP (Pint c1) p2))
;;
let moinsPf (c1,p1) (c2,p2) =
  norm_polyf
    (mult_coef c1 c2,
     moinsP (multP (Pint c2) p1) (multP (Pint c1) p2))
;;

let multPf (c1,p1) (c2,p2) =
  norm_polyf
    (mult_coef c1 c2,
     multP p1 p2)
;;

let oppPf (c,p) =
  norm_polyf (c, oppP p)
;;

let puisPf (c,p) n =
 let rec aux n =
   if n=0
  then (coef1, (cf 1))
  else if n=1
  then (c,p)
  else multPf (c,p) (aux (n-1))
  in aux n
;;

let nvars = ref 0;;


(* terme vers couple (c,p) representant le polynome p/c *)

let rec term_polyf t  =  match t with
| Zero -> (coef1, (cf 0))
| Const r -> let (n,d) = numdom r in
   let d = ent_of_string (string_of_num d) in
   let n = ent_of_string (string_of_num n) in
               (d, Pint n)
| Var v -> let n = int_of_string v in
           nvars:= max (!nvars) n;
           (coef1,(x n))
| Opp t1 ->  oppPf (term_polyf t1)
| Add (t1,t2) -> plusPf (term_polyf t1) (term_polyf t2)
| Sub (t1,t2) -> moinsPf (term_polyf t1) (term_polyf t2)
| Mul (t1,t2) -> multPf (term_polyf t1) (term_polyf t2)
| Pow (t1,n) ->  puisPf (term_polyf t1) n
;;

let poly_term p =
  let rec aux p =
  match p with
   |Pint n -> Const (num_of_string (string_of_ent n))
   |Prec (v,coefs) ->
     let res = ref Zero in
     Array.iteri
      (fun i c ->
	 res:=Add(!res, Mul(aux c,
			    Pow (Var (string_of_int v),
				 i))))
      coefs;
     !res
  in aux p;;

(******************************************************************************

  La tactique Gb
*)

let rec pol_rec_to_sparse p v1 v2 =  (* v1 et v2 indices de début et de fin *)
  let d = v2-v1+1 in
    match p with
        Pint a ->
          if a= coef0
          then []
          else [a, Array.create (d+1) 0]
      |Prec(v,coefs)->
         let vp=Dansideal.gen d (v2-v+1) in (*j'aurais dit v2-v-1*)
         let res=ref [] in
           for i=(Array.length coefs)-1 downto 0 do
             res:= (Dansideal.plusP d
                      (Dansideal.multP d vp (!res))
                      (pol_rec_to_sparse coefs.(i) v1 v2));
           done;
           !res
;;

(* on inverse l'ordre des variables *)       
let rec pol_sparse_to_rec n1 n2 p =
  List.fold_left (fun r (c,m)->
                    let mp = ref (Pint coef1) in
                      Array.iteri (fun i e ->
                                     if i>0 then
                                       mp:=(multP (!mp) (monome (n2-i+1) e)))
                        m;
                      plusP r (multP (Pint c) (!mp)))
    (Pint coef0)
    p
;;  

(* liste de polynomes lpol=p1,...,pn, 
   echoue ou rend q1,...,qn,q tq 1=q1*p1+...+qn*pn+q*(1-zp)

   
   en general (B.Mourrain):
   exprimer 1=q1p1+...qnpn+q(1-zp)
   calculer la base de grobner de 

   t-e,t*(1-zp)-e0 t*p1-e1,...,t*pn-en,ei*ej

   avec t>>e>>x1,...,xm,z=x(m+1)>>e0,e1,...,en
   et recuperer dedans un polynome
   e-q*e0-q1*e1-...-qn*en
   Voila.

*)
let prt s =
(*   Unix.system ("echo \""^(s)^"\" >> inputgbtest");*)
   ();;

let deg_nullstellensatz lpol p =

  prt "deg_nullstellensatz"; prt "lpol =";
  List.iter (fun p -> prt (string_of_P p)) lpol;
  prt "-----------------";
  prt "p =";
  prt (string_of_P p);
  prt "-----------------";

  (* lpol = p1, ..., pn *)
  let n = List.length lpol in
  let i = ref 0 in
  let m= (!nvars) in
    (*  t=m+3 e=m+2 ei=-i z=m+1*)
    
  (* lpol1 = t*p1-e1, ..., t*pn-en *)
  let lpol1 = List.map (fun pi ->
                          i:=!i+1;
                          plusP (multP (x (m+3)) pi) (oppP (x (-(!i)))))
                lpol in
    (* polsup = t*(1-z*p) + e0 *)
  let polsup=(plusP (multP (x (m+3)) (plusP cf1 (oppP (multP (x (m+1)) p)))) (oppP (x 0))) in
  let lpol1=polsup::lpol1 in 
    (* t - e *)
  let lpol1=(plusP (x (m+3)) (oppP (x (m+2))))::lpol1 in
  let leiej=ref [] in
   (* ei*ej *)
    for j=0 to n-1 do
      for k=j+1 to n do
        leiej:=(multP (x (-j)) (x (-k)))::(!leiej);
      done;
    done;
    (* e*ei *)
    for j=0 to n do
      leiej:=(multP (x (-j)) (x (m+2)))::(!leiej);
    done;
    let lpol1=(!leiej)@lpol1 in
(*      List.iter (fun p -> print_string ((string_of_P p)^"\n")) lpol1;
      print_string ("----------------------"^"\n");flush(stdout);*)
      let lvar=ref [] in
	for i=0 to n do lvar:=(!lvar)@["e["^(string_of_int i)^"]"]; done;
	for i=1 to m do lvar:=["x["^(string_of_int i)^"]"]@(!lvar); done;
	lvar:=["t";"e";"z"]@(!lvar);
	Dansideal.name_var:=!lvar;
	let lpol1=List.map (fun p -> pol_rec_to_sparse p (-n-1) (m+3)) lpol1 in
(*          Dansideal.lprintP lpol1; print_string
            ("\n----------------------"^"\n");flush(stdout);*)
	  let gb = Dansideal.buch (m+n+4) lpol1 in
          prt "";
(*         print_string ("------------------base calculee---"^"\n");flush(stdout);*)
          (*Dansideal.lprintP gb;*)
          (* si on ecrit [q] =.. en fait il faut que q soit de longueur 1 *)
	  let q = (List.filter (fun p -> match p with  (*la*)
                                    [] -> false
				  |(_,mon)::_ -> mon.(2)=1) (*c'est koi ce 2 !!!*)
                     gb) in
            (* si j'ai bien compris, on cherche les polynomes de la base dont les
               monomes de tete contiennent la variable 'e'*)
            (*print_string ("\n-------------poly principal---"^"\n");flush(stdout);
              Dansideal.lprintP q;*)
            (* la base est reduite donc q est de longueur 1 ,
	       soit q' son polynome de tete*)
	  let q'=List.nth q 0 in 
	  let lq = ref [] in
	  let degz = ref 0 in           
            for i=1 to n+1 do
              let i0=n+m+5-i in
		(* on cherche les monomes qui sont construits a
		   l'aide des ei *)
              let qi=List.filter (fun p -> match p with
                                      (_,mon) ->  mon.(i0)>0 
					(* |[] -> false*)) 
                       q' in 
		(*je multiplie les monomes precedents par le coeff de "e" *)
		(*attention je suppose que ce coeff est 1 ou -1*)
		(*je viens de trouver un exemple ou c'est diff de 1 ou -1*)
		(*on peut pas diviser par le coeff car les futurs coeff sont dans Z*)
              let qi = List.map (fun p -> match p with 
                                     (a,mon) -> 
                                       ((mult_coef a 
					   (opp_coef
					      (coef_of_int
						 (signe_coef (fst (List.nth q' 0)))))),mon))
			 qi in
              let qqi = List.map (fun p ->
                                    let mon =snd p in
                                    let c = fst p in
                                    let mon1=Array.copy mon in
                                      mon1.(i0)<-mon.(i0)-1;
                                      (c,mon1)) qi in
		List.iter (fun qi ->
                             let deg' = (snd qi).(3) in
                               (if (compare deg' !degz)=1 then 
				  degz:=deg'))
		  qqi;
		lq:=[qqi]@(!lq);
		(*prt "\nles qqi"; Dansideal.lprintP [qqi];prt "\n";*)
		(*lq:=[qqi]@(!lq);*)
            done;
            prt "--------degré de z----------";
            prt (string_of_int (!degz));
            prt "";
            let pi=pol_rec_to_sparse p (-n-1) (m+3) in
              lq := List.map (fun hi ->
				let gi = Dansideal.specialsubstP (m+4) hi 3 !degz in 
				  Dansideal.substP (m+4) gi 3 pi) !lq;
              (*print_string ("\n---------coef calcules---"^"\n");flush(stdout);
	      Dansideal.lprintP (!lq);*)
              let lqr=List.map (fun p->pol_sparse_to_rec (-n-1) (m+3) p) !lq in

(*		print_string
		  ("----------convertis:------------"^"\n");flush(stdout);*)
(*		List.iter (fun p -> print_string ((string_of_P p)^"\n"))
		  lqr; prt""; prt"fin des calculs"; prt"";*)
		let specialcoef = fst (List.nth q' 0) in
		  (specialcoef,(lqr,!degz))
;;                

let comb_lin1 lp =
  nvars:=0;(* mise a jour par term_polyf *)
  let lp0 = List.map term_polyf lp in

  let lp = List.map snd lp0 in
  let p::lp1 = List.rev lp in
  let lpol = List.rev lp1 in
(* montrer lp = 0 => p=0 *)
  let (c,(_::lq,d))=  deg_nullstellensatz lpol p in
  let c = abs_ent c in
(* on a
         (-c)*p^d = sum lq*lp
*)
  let lc = (Pint c)::lq in
  (Pow ((poly_term p),d))::(List.map poly_term lc)
;;

let buf = ref "" in
try

	while true do
		match read_line() with
		| s -> 
			buf := !buf ^ s ^ "\n"
	done
with
	End_of_file ->
(*	  Unix.system ("echo \""^(!buf)^"\" > inputgbtest");*)

	  (* la on calcule la base de grobner *)

          let (lp,_,_)= parse_request (Xml.parse_string !buf) in
          let lc = comb_lin1 lp in
          let lc = List.map mk_term lc in
          let termxml =
	    List.fold_right
	      (fun t r ->
		  mk_app luri lceq [t;r])
               lc
               (mk_elt luri lnil []) in
	  
(*          Unix.system ("echo \""^(Xml.to_string_fmt termxml)^"\" > outputgbtest");*)
          print_string "<TERM>"; print_newline();
          print_string (Xml.to_string_fmt termxml);
          print_string "</TERM>"; print_newline();
          print_newline();
;;


