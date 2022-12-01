(* Funciones ap_of_gic y traza_ap por Nicolas Vazquez Cancela. *)

#directory "ocaml-talf/src";;
#load "ocaml-talf/src/talf.cma";;
open Conj;;
open Auto;;
open Ergo;;
open Graf;;

(*1*)
let map_conj f (Conjunto l) = Conjunto (List.map f l);;

let ap_of_gic =
	let (e0, e1, e2) = Estado "q1", Estado "q2", Estado "q3" 
	and e = Terminal "" and z = No_terminal "" in
	let ce = Conjunto [e0; e1; e2]
	in fun (Gic (csn, cst, cr, sni)) ->
		let a01 = Arco_ap (e0, e1, e, z, [sni; z])
		and a12 = Arco_ap (e1, e2, e, z, [z])
		in Ap (
			ce, cst, agregar (z) (union csn cst),
			e0, union (union (Conjunto [a01; a12]) (
				map_conj (fun (Regla_gic (sn, ls)) -> 
					Arco_ap (e1, e1, e, sn, ls)
				) cr
			)) (map_conj (fun st ->
					Arco_ap (e1, e1, st, st, [])
			) cst), z, Conjunto [e2]
		);;

(*2*)
let print_simbolo = function 
	| Terminal "" -> print_char 'e'
	| No_terminal "" -> print_char 'Z'
	| Terminal ss | No_terminal ss -> print_string ss;;

let print_regla (Regla_gic (st, lsp)) =
	print_simbolo st; print_string " -> ";
	if lsp = [] then print_string "e"
	else List.iter print_simbolo lsp;;

let print_estado (Estado se) = print_string se;;

let print_list print_x l = 
	let rec aux = function
		| [] -> print_char ']'
		| (h::[]) -> print_x h; print_char ']'
		| (h::t) -> print_x h; print_string "; "; aux t
	in print_char '['; aux l;;

let print_conf (ea,lsc,lsp) =
	print_char '('; print_estado ea; print_string ", ";
	print_list print_simbolo lsc; print_string ", ";
 	print_list print_simbolo lsp; print_string ")";;

let print_transicion sc lst confo confd =
	(match sc with
		| No_terminal "" -> print_char '*'
		| No_terminal _ -> print_regla (Regla_gic (sc, lst))
		| _ -> print_char '*'
	);
	print_string ": "; print_conf confo; print_string " |- ";
	print_conf confd; print_newline ();;


let avanza_ap (Conjunto lt) (ea, lsc, lsp as confo) =
	let rec aux cconfd = function
		| [] -> cconfd
		| (Arco_ap (eo, ed, st, sc, lst))::ts -> if eo = ea &&
			(st = Terminal "" || (lsc != [] && st = List.hd lsc)) &&
			(sc = Terminal "" || (lsp != [] && sc = List.hd lsp))
			then
				let confd = ed, (if st = Terminal "" 
					then lsc else List.tl lsc),
					lst@(List.tl lsp)
				in
					print_transicion sc lst confo confd;
					aux (agregar confd cconfd) ts
			else 
				aux cconfd ts
	in aux (Conjunto []) lt;;

let traza_ap lsc (Ap(_,_,_,ei,ct,si,cef)) =
	let rec aux = function
		| Conjunto [] -> false
		| Conjunto ((ea,lsc,_ as conf)::ts) ->
			pertenece ea cef && lsc = [] ||
			aux (union (Conjunto ts) (avanza_ap ct conf))
	in aux (Conjunto [ei, lsc, [si]]);;


let ap1 = ap_of_gic (gic_of_string "S A B; a b; S; S -> a A | a B; A -> a | b; B -> a | b;");;
dibuja_ap ap1;;
traza_ap (cadena_of_string "a a") ap1;;
traza_ap (cadena_of_string "a b") ap1;;

traza_ap (cadena_of_string "a") ap1;;
traza_ap (cadena_of_string "b") ap1;;
traza_ap (cadena_of_string "b a") ap1;;
traza_ap (cadena_of_string "b b") ap1;;
traza_ap (cadena_of_string "a a a") ap1;;
traza_ap (cadena_of_string "a b b") ap1;;

let ap2 = ap_of_gic (gic_of_string "S; a b; S; S -> a S a | b S b | a | b | epsilon;");;
dibuja_ap ap2;;
traza_ap (cadena_of_string "a") ap2;;
traza_ap (cadena_of_string "a a") ap2;;
traza_ap (cadena_of_string "a a a") ap2;;
traza_ap (cadena_of_string "b") ap2;;
traza_ap (cadena_of_string "b b") ap2;;
traza_ap (cadena_of_string "b b b") ap2;;
traza_ap (cadena_of_string "a b a") ap2;;
traza_ap (cadena_of_string "b a b") ap2;;
traza_ap (cadena_of_string "a a a a") ap2;;
traza_ap (cadena_of_string "b b b b") ap2;;
traza_ap (cadena_of_string "a b b a") ap2;;
traza_ap (cadena_of_string "b a a b") ap2;;

traza_ap (cadena_of_string "a b") ap2;;
traza_ap (cadena_of_string "b a") ap2;;
traza_ap (cadena_of_string "a b a b") ap2;;
traza_ap (cadena_of_string "b a b a") ap2;;
traza_ap (cadena_of_string "a a b") ap2;;
traza_ap (cadena_of_string "b b a") ap2;;

let ap3 = ap_of_gic (gic_of_string "S; a b; S; S -> a S b | epsilon;");;
dibuja_ap ap3;;
traza_ap (cadena_of_string "") ap3;;
traza_ap (cadena_of_string "a b") ap3;;
traza_ap (cadena_of_string "a a b b") ap3;;
traza_ap (cadena_of_string "a a a b b b") ap3;;

traza_ap (cadena_of_string "a") ap3;;
traza_ap (cadena_of_string "a a") ap3;;
traza_ap (cadena_of_string "b") ap3;;
traza_ap (cadena_of_string "b b") ap3;;
traza_ap (cadena_of_string "b a") ap3;;
traza_ap (cadena_of_string "a a b") ap3;;
traza_ap (cadena_of_string "a a a b") ap3;;
traza_ap (cadena_of_string "a b b") ap3;;
traza_ap (cadena_of_string "a b b b") ap3;;

let ap4 = ap_of_gic (gic_of_string "S A B C; a b c; S; S -> a A | C c | epsilon; A -> a A | a A c | B; C -> C c  | a C c | B; B -> b B | epsilon;");;
dibuja_ap ap4;;
traza_ap (cadena_of_string "") ap4;;
traza_ap (cadena_of_string "a a c") ap4;;
traza_ap (cadena_of_string "a a b c") ap4;;
traza_ap (cadena_of_string "a a b b c") ap4;;
traza_ap (cadena_of_string "a a b b b c") ap4;;
traza_ap (cadena_of_string "a c c") ap4;;
traza_ap (cadena_of_string "a b c c") ap4;;
traza_ap (cadena_of_string "a b b c c") ap4;;
traza_ap (cadena_of_string "a b b b c c") ap4;;
traza_ap (cadena_of_string "a a a c") ap4;;
traza_ap (cadena_of_string "a a a b c") ap4;;
traza_ap (cadena_of_string "a a a b b c") ap4;;
traza_ap (cadena_of_string "a a a b b b c") ap4;;
traza_ap (cadena_of_string "a a a b b b b c") ap4;;
traza_ap (cadena_of_string "a c c c") ap4;;
traza_ap (cadena_of_string "a b c c c") ap4;;
traza_ap (cadena_of_string "a b b c c c") ap4;;
traza_ap (cadena_of_string "a b b b c c c") ap4;;
traza_ap (cadena_of_string "a b b b b c c c") ap4;;

traza_ap (cadena_of_string "b") ap4;;
traza_ap (cadena_of_string "b b") ap4;;
traza_ap (cadena_of_string "a c") ap4;;
traza_ap (cadena_of_string "a b c") ap4;;
traza_ap (cadena_of_string "a b b c") ap4;;
traza_ap (cadena_of_string "a a c c") ap4;;
traza_ap (cadena_of_string "a a b c c") ap4;;
traza_ap (cadena_of_string "a a b b c c") ap4;;
traza_ap (cadena_of_string "a a b b b c c") ap4;;
traza_ap (cadena_of_string "a a a c c c") ap4;;
traza_ap (cadena_of_string "a a a b c c c") ap4;;
traza_ap (cadena_of_string "a a a b b c c c") ap4;;
traza_ap (cadena_of_string "a a a b b b c c c") ap4;;
traza_ap (cadena_of_string "a a a b b b b c c c") ap4;;