type variable = Var of string
type symbol = Sym of string
type term = V of variable | Node of symbol * (term list)
let b_sig = [(Sym("shubham"),0);(Sym("sangnie"),2);(Sym("kandu"),0);(Sym("ankur"),0);(Sym("sangnie"),1);(Sym("lol"),-1)]
let g_sig = [(Sym("shubham"),0);(Sym("sangnie"),2);(Sym("kandu"),0);(Sym("ankur"),0)]
type substitution = (variable* term)list
let rec does_not_appear a xs = match xs with
	|[]-> true
	|(Sym(ax),bx)::xss-> if(ax=a) then false else does_not_appear a xss

let rec check_sig (l: (symbol*int) list) = match l with
	|[]->true
	| (Sym(a),b)::[] -> true;
	| (Sym(a),b)::xs -> (*a is a string b is a int and xs contains*) if(b>=0&& does_not_appear a xs) then check_sig xs else false

let rec variable_exists_in_sig a_variable a_signature = match (a_variable,a_signature) with
	|(Var(a),[])-> false
	|(Var(a),(Sym(head),the_integer)::tail) -> if(head=a) then true else variable_exists_in_sig a_variable tail
let rec node_exists_in_sig a_node a_signature = match(a_node,a_signature) with
	|(Sym(a_symbol),the_sigg) -> if(does_not_appear a_symbol the_sigg) then false else true

let term_exists_in_signature this_term the_signature = match this_term with
	| V(a_variable)-> variable_exists_in_sig a_variable the_signature
	| Node(a_node,term_list)-> node_exists_in_sig a_node the_signature

let wfterm my_term signature = match signature with
	|(Sym(a),b)::xs-> ((term_exists_in_signature my_term signature)&&check_sig(signature))
	|[]-> false

let max_of_two_ints a b = if(a>b) then a else b

let rec height_of_a_term_list(the_term_list) = match the_term_list with
|[]->0
|Node(a_node,term_list)::another_term_list -> 1+ max_of_two_ints (height_of_a_term_list term_list) (height_of_a_term_list another_term_list)
|V(a_variable)::another_term_list-> max_of_two_ints 1 (height_of_a_term_list another_term_list)

let ht (my_term : term) = match my_term with
| Node(a_node,term_list) -> height_of_a_term_list(term_list)
| _-> 0

let rec size_of_a_term_list a_term_list = match a_term_list with
| []->0
| Node(a_node,term_list)::another_term_list -> 1+ size_of_a_term_list term_list + size_of_a_term_list another_term_list
| V(a_variable)::another_term_list->1


let size (my_term: term) = (*returns size of the term*)match my_term with
| Node(a_node,term_list) -> size_of_a_term_list(term_list)
| _-> 1


let rec vars term =
  let rec aux list term = match term with
  | V var -> var::list
  | Node (my_symbol, []) -> list
  | Node (my_symbol, l) -> (List.fold_left (fun list el-> (aux list el)) list l)  in
  aux [] term;;
let compare_var var1 var2 = match (var1,var2) with
|(Var(a),Var(b))->if(a=b) then true else false

let compare_term term1 term2 = match (term1,term2) with
|(V(a),Node(b,c))-> false
|(Node(b,c),V(a))->false
|_-> true
;;
let check_if_same (x:substitution) (v:variable) : bool = match x with	|(var,term)::list_hu -> if var = v then true else false;;

(*
let rec subst (input_term,input_substitution) = match (input_term,input_substitution) with(*look for term and replace with terms in subst*)
|(a,[])->a::[]
|(V(output_variable),(matched_var,matched_term)::tail_list)-> if(compare_var output_variable matched_var) then matched_term else []
|(Node(a_node,term_list),the_input_list_of_substees)->List.map subst (term_list,the_input_list_of_substees)
 *)(*let mgu term_1 term_2 = (*create a substitution that makes the related variables to a *)
*)
