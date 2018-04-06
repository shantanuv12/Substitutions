type symbol=Sym of string*int;;
type signat=Signat of symbol list;;
type variable=string;;
type term=V of variable | Node of symbol*(term list);;
exception NOT_UNIFIABLE;;

let rec filter l x=match l with
[]->[]
| Sym(s,n)::t-> if (x=s) then Sym(s,n)::(filter t x) else filter t x;;

let rec check_dup l=match l with
[]->false                                                   (*Checking duplicates in a list*)
|(Sym(s,n)::t)->let x= filter t s in
if(x==[]) then
check_dup t
else
true;;

let rec symbol_exist (l: symbol list)=match l with              (*Checking if a 0 arity symbol exits*)
[]->false
|(Sym(s,n)::t)-> if (n==0) then true else symbol_exist t;;

let rec check_arity l=match l with
[]->true                                                                    (*checking arity>=0*)
|Sym(s,n)::t-> if (n>=0) then check_arity t else false;;

let rec foldr f e l=match l with   (* e=true for bool operations since it acts as no-operation when applied and the result
                                        is only the result of and(all booleans in the list) *)
[]->e
| h::t->f h (foldr f e t);;

let rec map f l=match l with        (*List mapping function*)
[]->[]
|h::t->(f h)::(map f t);;

let and_bool (a: bool) (b:bool)=a&&b;;

let max a b=if a>b then a else b;;

let l=[Sym("a",-1);Sym("b",0);Sym("c",1)];;
let li=[Sym("a", 1);Sym("b",2)];;
let lis=[Sym("a",1);Sym("b",2);Sym("b",3);Sym("d",4)];;

let rec check_sig (l: symbol list)= (check_arity l)&&(not(check_dup l)&&(l<>[])&&(symbol_exist l));;
 (*Checks if a given signature is valid or not*)

let rec wfterm ter=match ter with
(V a)->true
|Node (Sym(s,0),[])->true                   (*Checking if term is well formed or not i.e length of term list=arity of symbol*)
|Node (Sym(s,n),l)-> if (n=(List.length l)) then (foldr and_bool true (map wfterm l)) else false;;

let term_1=Node(Sym("Sum",2),[Node(Sym("Sub",2),[V "x";Node(Sym("One",0),[])]);V "y"]);;

let max a b=if a>b then a else b;;

let sum a b=a+b;;

let append l1 l2=l1@l2;;  (*add two list*)

let rec ht ter=match ter with
(V a)->0                    (*To find out the height of the expressions*)
| Node(Sym(s,0),[])->0
| Node(Sym(s,n),l)-> 1+ (foldr max 0 (map ht l));;


let rec size ter =match ter with        (*Find out size/ Number of nodes in an expressions*)
(V a)->0
| Node(Sym(s,0),[])->1
| Node(Sym(s,n),l)-> 1+(foldr sum 0 (map size l));;

let rec vars_1 ter=match ter with
(V a)->[a]                            (*Retreieve all the variables present in the given term*)
| Node(Sym(s,0),[])-> []
| Node(Sym(s,n),l)-> foldr append [] (map vars_1 l);;

let uniq lst =
  let unique = Hashtbl.create (List.length lst) in          (*Removing duplicates in a list using a hashtable*)
  List.iter (fun x -> Hashtbl.replace unique x ()) lst;
  Hashtbl.fold (fun x () xs -> x :: xs) unique [];;

let vars ter=uniq(vars_1 ter);;             (*Final list obtained by Removing dupli*)


(* Composition of substitution is represented by
    (rho1 o rho2)(x)={
                    rho1(rho2(x)) if x==dom(rho2)   (== is used for belongs to)
                    rho1 if x==dom(rho1) and x!=dom(rho2)
                   undefined if x!=dom(rho1) U dom(rho2)
                    }
*)
type substitution= (variable * term) list;;
                                            (* Some test cases for checking the function*)
let sigma=[("x",(Node(Sym ("f",1),[Node(Sym("a",0),[])])));("y",(Node(Sym ("g",2),[(Node(Sym("b",0),[]));V "z"])));("z",V "x")];;
let rho=[("x",(Node(Sym("w",0),[])));("y",(Node(Sym("h",1),[V "z"])));("z",(Node(Sym("a",0),[])))];;
let p=Node(Sym("P",3),[V "x";V "y";V "z"]);;
let term1=Node(Sym("P",3),[(Node(Sym("a",0),[]));V "x";Node(Sym("f",1),[(Node(Sym("g",1),[V "y"]))])]);;
let term2=Node(Sym("P",3),[V "z";Node(Sym("f",1),[V "z"]);(Node(Sym("f",1),[V "w"]))]);;
exception Error;;

let rec contains x l=match (l,x) with
([],_)->false                           (*To check if a given list contains a given element*)
|((s,t)::tl,Node(Sym(sy,n),l))->contains x tl
|((s,t)::tl,V a)->if (a=s) then true else contains x tl;;

let rec contains_var x l=match l with       (*To check if the given list/term contains a given variable*)
[]->false
|((s,t)::tl)->if (x=s) then true else contains_var x tl;;

 let rec replace x l=match (l,x) with           (*To replace an element in the list*)
((s,t)::tl,V a) -> if (a=s) then t else replace x tl
| (_,_)->raise Error;;

let rec subst sigma (t:term)=match t with           (*Substitutuion function*)
V a-> if (contains_var a sigma) then (replace (V a) sigma) else (V a)
| Node(Sym(a,0),[])->Node(Sym(a,0),[])
| Node(Sym(s,n),l)-> Node(Sym(s,n), map (subst sigma) l);;

let rec compose1 sigma rho l=match sigma with   (*To find out sigma(rho(x))*)
(s,t)::tl-> if ((V s)<>(subst rho t)) then compose1 tl rho (l@[s,subst rho t]) else compose1 tl rho l
|[]->l;;

let rec compose2 sigma rho l=match rho with         (*To find all x !==! (belongs)rho and does not belong to sigma *)
[]->l
|((s,t)::tl)-> if not(contains_var s sigma) then compose2 sigma tl (l@[(s,t)]) else compose2 sigma tl l;;

let rec compose sigma rho= (compose1 sigma rho [])@(compose2 sigma rho []);; (*Appened above two together to get the composition*)

let rec create_mgu l1 l2 lis f=match (l1,l2) with       (*To carry out recursive call for sigma(k)(sigma(k-1)((((....))))*)
(x::xs,h::tl)-> let sigi=f (subst lis x)(subst lis h) lis in
                    create_mgu xs tl (compose lis sigi) f
|([],[])->lis
| (_,_)->raise Error;;

let rec mgu (t:term) (u:term) l=match (t,u) with            (*find out the mgu of two terms*)
(V x,V y)-> if x=y then l else l@[(x, V y)]
|(V x, Node(Sym(s,n),lis))->l@[(x,Node(Sym(s,n),lis))]
|(Node(Sym(s,n),lis),V x)->l@[(x,Node(Sym(s,n),lis))]
|(Node(Sym(a,0),[]),Node(Sym(b,0),[]))->if a=b then l else raise NOT_UNIFIABLE
|(Node(Sym(a,m),l1),Node(Sym(b,n),l2))->if ((n=m)&&(a=b)) then create_mgu l1 l2 [] mgu else raise NOT_UNIFIABLE;;


mgu term1 term2 [];; (*Finds mgu of term2 and term1*)
subst sigma term1;;
compose sigma rho;;
compose rho sigma;;
subst sigma p;;
subst rho p;;
subst sigma (subst rho p);;
subst rho (subst sigma p);;
subst (compose sigma rho) p;;
subst (compose rho sigma) p;;
ht term1;;
ht term2;;
ht p;;
size term1;;
size term2;;
size p;;
wfterm term1;;
wfterm term2;;
wfterm p;;
check_sig l;;
check_sig li;;
check_sig lis;;

let sig1 = [Sym("X",0);Sym("Y",0);Sym("f",1);Sym("g",2);Sym("h",3);Sym("*",2)];;
let sig2 = [Sym("X",0);Sym("Y",0);Sym("Z",0);Sym("f",1);Sym("g",2);Sym("f",3);Sym("*",2)];;
let sig3 = [Sym("f",1)];;
let sig4 = [Sym("X",0);Sym("Y",0);Sym("Z",0)];;

let term1 = (Node (Sym ("f",1),[V "X"]));;
let term2 = (Node (Sym ("g",2),[V "X";Node(Sym ("h",2),[Node(Sym ("f",1),[V "X"]);V "Y"])]));;
let term3 = (Node (Sym ("g",2),[V "X";Node(Sym ("*",2),[V "Y";Node (Sym ("*",2),[V "X";V "Y"])])]));;
let term4 = (Node (Sym ("g",2),[V "X";Node(Sym ("*",2),[V "Y";V "X"])]));;
let term5 = (Node (Sym ("g",2),[V "Z";Node(Sym ("*",2),[V "X";V "Z"])]));;
let term6 = (Node (Sym ("g",2),[V "Z";Node(Sym ("g",2),[V "X";V "Z"])]));;
let term7 = (V "X");;
let term8 = (Node (Sym ("K",0),[]));;
let term9 = (Node (Sym ("X",0),[]));;
let term10 = (Node (Sym ("g",4),[V "X";Node(Sym ("h",3),[Node(Sym ("f",1),[V "X"]);V "Y";Node (Sym ("X",0),[])])]));;
let term11 = (Node (Sym ("g",4),[V "X";Node(Sym ("h",1),[Node(Sym ("f",1),[V "X"]);V "Y";Node (Sym ("f",1),[V "X"])])]));;
let term12 = (Node (Sym ("g",2),[V "Z";Node(Sym ("*",2),[V "Z";Node (Sym ("*",2),[V "X";V "Y"])])]));;
let term13 = (Node (Sym ("$",2),[V "P";V"Q"]));;
let term14 = (Node (Sym ("$",2),[Node (Sym ("2",0),[]); Node (Sym ("4",0),[])]));;
let term15 = (Node (Sym ("$",2),[Node (Sym ("2",0),[]); Node (Sym ("3",0),[])]));;




Printf.printf "(1)check_sig sig1 : %B\n" (check_sig sig1);;
Printf.printf "(2)check_sig sig2 : %B\n" (check_sig sig2);;
Printf.printf "(3)check_sig sig3 : %B\n" (check_sig sig3);;
Printf.printf "(4)check_sig sig4 : %B\n\n" (check_sig sig4);;
(*
Printf.printf "(5)wfterm term1 sig1 : %B\n" (wfterm term1 sig1);;
Printf.printf "(6)wfterm term2 sig1 : %B\n" (wfterm term2 sig1);;
Printf.printf "(7)wfterm term7 sig4 : %B\n" (wfterm term7 sig4);;
Printf.printf "(8)wfterm term8 sig4 : %B\n" (wfterm term8 sig4);;
Printf.printf "(9)wfterm term9 sig4 : %B\n\n" (wfterm term9 sig4);;
*)
Printf.printf "(10)ht term9 : %d\n" (ht term9);;
Printf.printf "(11)ht term7 : %d\n" (ht term7);;
Printf.printf "(12)ht term4 : %d\n" (ht term4);;
Printf.printf "(13)ht term10 : %d\n" (ht term10);;
Printf.printf "(14)ht term11 : %d\n\n" (ht term11);;

Printf.printf "(15)size term9 : %d\n" (size term9);;
Printf.printf "(16)size term7 : %d\n" (size term7);;
Printf.printf "(17)size term4 : %d\n" (size term4);;
Printf.printf "(18)size term10 : %d\n" (size term10);;
Printf.printf "(19)size term11 : %d\n\n" (size term11);;

Printf.printf "(20)vars term9 : ";; (vars term9);; Printf.printf("\n");;
Printf.printf "(21)vars term7 : ";; (vars term7);; Printf.printf("\n");;
Printf.printf "(22)vars term4 : ";; (vars term4);; Printf.printf("\n");;
Printf.printf "(23)vars term10 : ";; (vars term10);; Printf.printf("\n");;
Printf.printf "(24)vars term11 : ";; (vars term11);; Printf.printf("\n\n");;


Printf.printf "(31)mgu term14 term13 : ";; (mgu term14 term13);; Printf.printf("\n");;
Printf.printf "(33)mgu term3  term12 : ";; ((mgu term3 term12));; Printf.printf("\n");;
Printf.printf "(34)mgu term12 term3  : ";; ((mgu term12 term3));; Printf.printf("\n\n");;

Printf.printf "(33.1)subst term12 (mgu term3 term12)  : ";; (subst (mgu term3 term12 []) term12);; Printf.printf("\n");;
Printf.printf "(33.2)subst term3  (mgu term3 term12)  : ";; (subst (mgu term3 term12 []) term3);; Printf.printf("\n\n");;

Printf.printf "(34.1)subst term12 (mgu term12 term3)  : ";; (subst (mgu term12 term3 []) term12);; Printf.printf("\n");;
Printf.printf "(34.2)subst term3  (mgu term12 term3)  : ";; (subst (mgu term12 term3 []) term3);; Printf.printf("\n\n");;
