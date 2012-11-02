type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f0 = function
| Some a -> Some (f0 a)
| None -> None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x0, y) -> x0

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (x0, y) -> y

type comparison =
| Eq
| Lt
| Gt

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (y, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m0 =
  match l with
  | Nil -> m0
  | Cons (a, l1) -> Cons (a, (app l1 m0))

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type 'a sumor =
| Inleft of 'a
| Inright

(** val plus : nat -> nat -> nat **)

let rec plus n m0 =
  match n with
  | O -> m0
  | S p0 -> S (plus p0 m0)

(** val eq_nat_dec : nat -> nat -> sumbool **)

let rec eq_nat_dec n m0 =
  match n with
  | O ->
    (match m0 with
     | O -> Left
     | S m1 -> Right)
  | S n0 ->
    (match m0 with
     | O -> Right
     | S m1 -> eq_nat_dec n0 m1)

(** val beq_nat : nat -> nat -> bool **)

let rec beq_nat n m0 =
  match n with
  | O ->
    (match m0 with
     | O -> True
     | S n0 -> False)
  | S n1 ->
    (match m0 with
     | O -> False
     | S m1 -> beq_nat n1 m1)

type positive =
| XI of positive
| XO of positive
| XH

(** val psucc : positive -> positive **)

let rec psucc = function
| XI p0 -> XO (psucc p0)
| XO p0 -> XI p0
| XH -> XO XH

(** val pmult_nat : positive -> nat -> nat **)

let rec pmult_nat x0 pow2 =
  match x0 with
  | XI p0 -> plus pow2 (pmult_nat p0 (plus pow2 pow2))
  | XO p0 -> pmult_nat p0 (plus pow2 pow2)
  | XH -> pow2

(** val nat_of_P : positive -> nat **)

let nat_of_P x0 =
  pmult_nat x0 (S O)

(** val p_of_succ_nat : nat -> positive **)

let rec p_of_succ_nat = function
| O -> XH
| S x0 -> psucc (p_of_succ_nat x0)

(** val pcompare : positive -> positive -> comparison -> comparison **)

let rec pcompare x0 y r =
  match x0 with
  | XI p0 ->
    (match y with
     | XI q -> pcompare p0 q r
     | XO q -> pcompare p0 q Gt
     | XH -> Gt)
  | XO p0 ->
    (match y with
     | XI q -> pcompare p0 q Lt
     | XO q -> pcompare p0 q r
     | XH -> Gt)
  | XH ->
    (match y with
     | XH -> r
     | _ -> Lt)

(** val positive_eq_dec : positive -> positive -> sumbool **)

let rec positive_eq_dec p0 y0 =
  match p0 with
  | XI p1 ->
    (match y0 with
     | XI p2 -> positive_eq_dec p1 p2
     | _ -> Right)
  | XO p1 ->
    (match y0 with
     | XO p2 -> positive_eq_dec p1 p2
     | _ -> Right)
  | XH ->
    (match y0 with
     | XH -> Left
     | _ -> Right)

module type TotalOrder' = 
 sig 
  type t 
 end

module MakeOrderTac = 
 functor (O:TotalOrder') ->
 struct 
  
 end

(** val max : nat -> nat -> nat **)

let rec max n m0 =
  match n with
  | O -> m0
  | S n' ->
    (match m0 with
     | O -> n
     | S m' -> S (max n' m'))

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  match b1 with
  | True ->
    (match b2 with
     | True -> Left
     | False -> Right)
  | False ->
    (match b2 with
     | True -> Right
     | False -> Left)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x0, l') -> app (rev l') (Cons (x0, Nil))

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f0 = function
| Nil -> Nil
| Cons (a, t1) -> Cons ((f0 a), (map f0 t1))

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f0 l a0 =
  match l with
  | Nil -> a0
  | Cons (b, t1) -> fold_left f0 t1 (f0 a0 b)

(** val split : ('a1, 'a2) prod list -> ('a1 list, 'a2 list) prod **)

let rec split = function
| Nil -> Pair (Nil, Nil)
| Cons (p0, tl) ->
  let Pair (x0, y) = p0 in
  let Pair (g, d) = split tl in Pair ((Cons (x0, g)), (Cons (y, d)))

(** val combine : 'a1 list -> 'a2 list -> ('a1, 'a2) prod list **)

let rec combine l l' =
  match l with
  | Nil -> Nil
  | Cons (x0, tl) ->
    (match l' with
     | Nil -> Nil
     | Cons (y, tl') -> Cons ((Pair (x0, y)), (combine tl tl')))

(** val firstn : nat -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  match n with
  | O -> Nil
  | S n0 ->
    (match l with
     | Nil -> Nil
     | Cons (a, l0) -> Cons (a, (firstn n0 l0)))

(** val skipn : nat -> 'a1 list -> 'a1 list **)

let rec skipn n l =
  match n with
  | O -> l
  | S n0 ->
    (match l with
     | Nil -> Nil
     | Cons (a, l0) -> skipn n0 l0)

type 'x compare =
| LT
| EQ
| GT

module type OrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> t compare
  
  val eq_dec : t -> t -> sumbool
 end

module OrderedTypeFacts = 
 functor (O:OrderedType) ->
 struct 
  module OrderElts = 
   struct 
    type t = O.t
   end
  
  module OrderTac = MakeOrderTac(OrderElts)
  
  (** val eq_dec : O.t -> O.t -> sumbool **)
  
  let eq_dec =
    O.eq_dec
  
  (** val lt_dec : O.t -> O.t -> sumbool **)
  
  let lt_dec x0 y =
    match O.compare x0 y with
    | LT -> Left
    | _ -> Right
  
  (** val eqb : O.t -> O.t -> bool **)
  
  let eqb x0 y =
    match eq_dec x0 y with
    | Left -> True
    | Right -> False
 end

module KeyOrderedType = 
 functor (O:OrderedType) ->
 struct 
  module MO = OrderedTypeFacts(O)
 end

module PositiveOrderedTypeBits = 
 struct 
  type t = positive
  
  (** val compare : t -> t -> positive compare **)
  
  let rec compare p0 y =
    match p0 with
    | XI p1 ->
      (match y with
       | XI y0 -> compare p1 y0
       | _ -> GT)
    | XO p1 ->
      (match y with
       | XO y0 -> compare p1 y0
       | _ -> LT)
    | XH ->
      (match y with
       | XI y0 -> LT
       | XO y0 -> GT
       | XH -> EQ)
  
  (** val eq_dec : positive -> positive -> sumbool **)
  
  let eq_dec x0 y =
    match pcompare x0 y Eq with
    | Eq -> Left
    | _ -> Right
 end

(** val append : positive -> positive -> positive **)

let rec append i j =
  match i with
  | XI ii -> XI (append ii j)
  | XO ii -> XO (append ii j)
  | XH -> j

module PositiveMap = 
 struct 
  module E = PositiveOrderedTypeBits
  
  module ME = KeyOrderedType(E)
  
  type key = positive
  
  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree
  
  type 'a t = 'a tree
  
  (** val empty : 'a1 t **)
  
  let empty =
    Leaf
  
  (** val is_empty : 'a1 t -> bool **)
  
  let rec is_empty = function
  | Leaf -> True
  | Node (l, o, r) ->
    (match o with
     | Some a -> False
     | None ->
       (match is_empty l with
        | True -> is_empty r
        | False -> False))
  
  (** val find : positive -> 'a1 t -> 'a1 option **)
  
  let rec find i = function
  | Leaf -> None
  | Node (l, o, r) ->
    (match i with
     | XI ii -> find ii r
     | XO ii -> find ii l
     | XH -> o)
  
  (** val mem : positive -> 'a1 t -> bool **)
  
  let rec mem i = function
  | Leaf -> False
  | Node (l, o, r) ->
    (match i with
     | XI ii -> mem ii r
     | XO ii -> mem ii l
     | XH ->
       (match o with
        | Some a -> True
        | None -> False))
  
  (** val add : positive -> 'a1 -> 'a1 t -> 'a1 t **)
  
  let rec add i v0 = function
  | Leaf ->
    (match i with
     | XI ii -> Node (Leaf, None, (add ii v0 Leaf))
     | XO ii -> Node ((add ii v0 Leaf), None, Leaf)
     | XH -> Node (Leaf, (Some v0), Leaf))
  | Node (l, o, r) ->
    (match i with
     | XI ii -> Node (l, o, (add ii v0 r))
     | XO ii -> Node ((add ii v0 l), o, r)
     | XH -> Node (l, (Some v0), r))
  
  (** val remove : positive -> 'a1 t -> 'a1 t **)
  
  let rec remove i m0 =
    match i with
    | XI ii ->
      (match m0 with
       | Leaf -> Leaf
       | Node (l, o, r) ->
         (match l with
          | Leaf ->
            (match o with
             | Some a -> Node (l, o, (remove ii r))
             | None ->
               (match remove ii r with
                | Leaf -> Leaf
                | Node (t1, o0, t2) -> Node (Leaf, None, (Node (t1, o0, t2)))))
          | Node (t1, o0, t2) -> Node (l, o, (remove ii r))))
    | XO ii ->
      (match m0 with
       | Leaf -> Leaf
       | Node (l, o, r) ->
         (match o with
          | Some a -> Node ((remove ii l), o, r)
          | None ->
            (match r with
             | Leaf ->
               (match remove ii l with
                | Leaf -> Leaf
                | Node (t1, o0, t2) -> Node ((Node (t1, o0, t2)), None, Leaf))
             | Node (t1, o0, t2) -> Node ((remove ii l), o, r))))
    | XH ->
      (match m0 with
       | Leaf -> Leaf
       | Node (l, o, r) ->
         (match l with
          | Leaf ->
            (match r with
             | Leaf -> Leaf
             | Node (t1, o0, t2) -> Node (l, None, r))
          | Node (t1, o0, t2) -> Node (l, None, r)))
  
  (** val xelements : 'a1 t -> positive -> (positive, 'a1) prod list **)
  
  let rec xelements m0 i =
    match m0 with
    | Leaf -> Nil
    | Node (l, o, r) ->
      (match o with
       | Some x0 ->
         app (xelements l (append i (XO XH))) (Cons ((Pair (i, x0)),
           (xelements r (append i (XI XH)))))
       | None ->
         app (xelements l (append i (XO XH)))
           (xelements r (append i (XI XH))))
  
  (** val elements : 'a1 t -> (positive, 'a1) prod list **)
  
  let elements m0 =
    xelements m0 XH
  
  (** val cardinal : 'a1 t -> nat **)
  
  let rec cardinal = function
  | Leaf -> O
  | Node (l, o, r) ->
    (match o with
     | Some a -> S (plus (cardinal l) (cardinal r))
     | None -> plus (cardinal l) (cardinal r))
  
  (** val xfind : positive -> positive -> 'a1 t -> 'a1 option **)
  
  let rec xfind i j m0 =
    match i with
    | XI ii ->
      (match j with
       | XI jj -> xfind ii jj m0
       | XO p0 -> None
       | XH -> find i m0)
    | XO ii ->
      (match j with
       | XI p0 -> None
       | XO jj -> xfind ii jj m0
       | XH -> find i m0)
    | XH ->
      (match j with
       | XH -> find i m0
       | _ -> None)
  
  (** val xmapi : (positive -> 'a1 -> 'a2) -> 'a1 t -> positive -> 'a2 t **)
  
  let rec xmapi f0 m0 i =
    match m0 with
    | Leaf -> Leaf
    | Node (l, o, r) ->
      Node ((xmapi f0 l (append i (XO XH))), (option_map (f0 i) o),
        (xmapi f0 r (append i (XI XH))))
  
  (** val mapi : (positive -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let mapi f0 m0 =
    xmapi f0 m0 XH
  
  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let map f0 m0 =
    mapi (fun x0 -> f0) m0
  
  (** val xmap2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)
  
  let rec xmap2_l f0 = function
  | Leaf -> Leaf
  | Node (l, o, r) -> Node ((xmap2_l f0 l), (f0 o None), (xmap2_l f0 r))
  
  (** val xmap2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)
  
  let rec xmap2_r f0 = function
  | Leaf -> Leaf
  | Node (l, o, r) -> Node ((xmap2_r f0 l), (f0 None o), (xmap2_r f0 r))
  
  (** val _map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)
  
  let rec _map2 f0 m1 m2 =
    match m1 with
    | Leaf -> xmap2_r f0 m2
    | Node (l1, o1, r1) ->
      (match m2 with
       | Leaf -> xmap2_l f0 m1
       | Node (l2, o2, r2) ->
         Node ((_map2 f0 l1 l2), (f0 o1 o2), (_map2 f0 r1 r2)))
  
  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)
  
  let map2 f0 =
    _map2 (fun o1 o2 ->
      match o1 with
      | Some y -> f0 o1 o2
      | None ->
        (match o2 with
         | Some y -> f0 o1 o2
         | None -> None))
  
  (** val xfoldi :
      (positive -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> positive -> 'a2 **)
  
  let rec xfoldi f0 m0 v0 i =
    match m0 with
    | Leaf -> v0
    | Node (l, o, r) ->
      (match o with
       | Some x0 ->
         xfoldi f0 r (f0 i x0 (xfoldi f0 l v0 (append i (XO XH))))
           (append i (XI XH))
       | None ->
         xfoldi f0 r (xfoldi f0 l v0 (append i (XO XH))) (append i (XI XH)))
  
  (** val fold : (positive -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)
  
  let fold f0 m0 i =
    xfoldi f0 m0 i XH
  
  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let rec equal cmp m1 m2 =
    match m1 with
    | Leaf -> is_empty m2
    | Node (l1, o1, r1) ->
      (match m2 with
       | Leaf -> is_empty m1
       | Node (l2, o2, r2) ->
         (match match match o1 with
                      | Some v1 ->
                        (match o2 with
                         | Some v2 -> cmp v1 v2
                         | None -> False)
                      | None ->
                        (match o2 with
                         | Some a -> False
                         | None -> True) with
                | True -> equal cmp l1 l2
                | False -> False with
          | True -> equal cmp r1 r2
          | False -> False))
 end

type id = positive

type f = id

type m = id

type c =
  id
  (* singleton inductive, whose constructor was SomeClass *)

type boolean = bool

type t0 =
| T_Bool
| T_Unit
| T_Class of c

type x =
| This
| SomeId of id

type location = nat

type pointer =
| Addr of location * c
| Null

type v =
| V_Pointer of pointer
| V_Bool of boolean
| V_Error
| V_Unit

type variableDeclaration =
| VarDec of id * t0

type expression =
| Expr_X of x
| Expr_V of v
| NewClass of c
| FieldRef of expression * f
| MethodInvocation of expression * m * x list
| Raw of pointer * m * v list
| Equality of expression * expression
| Cast of c * expression
| InstanceOf of expression * c
| VarAssign of x * expression
| FieldAssign of x * f * expression
| IfExpr of expression * expression * expression
| VarDecExp of variableDeclaration * expression * expression
| VoidExp
| SeqExp of expression * expression

type argumentList = variableDeclaration list

type method0 =
| AMethod of m * t0 * argumentList * expression

module HashMap = PositiveMap

type fieldTypeMap = t0 HashMap.t

type fieldValueMap = v HashMap.t

type methodMap = method0 HashMap.t

type cL =
| ClassDecl of c * cL option * fieldTypeMap * methodMap

type mu = cL HashMap.t

type programEntryPoint =
| EntryPoint of c * m

type p =
| Program of mu * programEntryPoint

type fieldLocationMap = location HashMap.t

type classToFieldLocationsMap = fieldLocationMap HashMap.t

type heapObject =
  classToFieldLocationsMap
  (* singleton inductive, whose constructor was HeapObj *)

type hv =
| Hv_v of v
| Hv_object of heapObject

type h = hv HashMap.t

type eta =
| Eta_mt
| Eta_NotMt of eta * x * location

type continuation =
| K_Return
| K_FieldAccess of f * continuation
| K_MethodInvocation of m * x list * continuation
| K_EqualityLeftOperand of expression * continuation
| K_EqualityRightOperand of v * continuation
| K_Cast of c * continuation
| K_InstanceOf of c * continuation
| K_VarAssign of x * continuation
| K_FieldAssign of x * f * continuation
| K_If of expression * expression * continuation
| K_VarAssignIn of t0 * x * expression * continuation
| K_Seq of expression * continuation
| K_Pop of eta * continuation

type state =
| StateCons of mu * h * eta * expression * continuation

(** val hv_To_V : location -> hv -> v **)

let hv_To_V loc = function
| Hv_v v0 -> v0
| Hv_object heapobj -> V_Error

(** val get_variable_name : variableDeclaration -> id **)

let get_variable_name = function
| VarDec (someid, t1) -> someid

type cList = c list

type cLList = cL list

type idList = id list

type locationList = location list

(** val id_eq_dec : positive -> positive -> sumbool **)

let id_eq_dec =
  positive_eq_dec

(** val x_eq_dec : x -> x -> sumbool **)

let x_eq_dec x0 y =
  match x0 with
  | This ->
    (match y with
     | This -> Left
     | SomeId i -> Right)
  | SomeId x1 ->
    (match y with
     | This -> Right
     | SomeId i0 -> id_eq_dec x1 i0)

(** val c_eq_dec : c -> c -> sumbool **)

let c_eq_dec x0 y =
  id_eq_dec x0 y

(** val pointer_eq_dec : pointer -> pointer -> sumbool **)

let pointer_eq_dec x0 y =
  match x0 with
  | Addr (x1, x2) ->
    (match y with
     | Addr (l0, c0) ->
       (match eq_nat_dec x1 l0 with
        | Left -> c_eq_dec x2 c0
        | Right -> Right)
     | Null -> Right)
  | Null ->
    (match y with
     | Addr (l, c0) -> Right
     | Null -> Left)

(** val v_eq_dec : v -> v -> sumbool **)

let v_eq_dec x0 y =
  match x0 with
  | V_Pointer x1 ->
    (match y with
     | V_Pointer p0 -> pointer_eq_dec x1 p0
     | _ -> Right)
  | V_Bool x1 ->
    (match y with
     | V_Bool b0 -> bool_dec x1 b0
     | _ -> Right)
  | V_Error ->
    (match y with
     | V_Error -> Left
     | _ -> Right)
  | V_Unit ->
    (match y with
     | V_Unit -> Left
     | _ -> Right)

(** val location_to_key : nat -> positive **)

let location_to_key =
  p_of_succ_nat

(** val h_lookup : h -> location -> hv option **)

let h_lookup h0 loc =
  HashMap.find (location_to_key loc) h0

(** val h_lookup_optional_loc : h -> location option -> v option **)

let h_lookup_optional_loc h0 = function
| Some loc0 ->
  let res = HashMap.find (location_to_key loc0) h0 in
  (match res with
   | Some hv0 -> Some (hv_To_V loc0 hv0)
   | None -> None)
| None -> None

(** val eta_lookup : eta -> x -> location option **)

let rec eta_lookup eta0 x0 =
  match eta0 with
  | Eta_mt -> None
  | Eta_NotMt (eta', x', loc) ->
    (match x_eq_dec x0 x' with
     | Left -> Some loc
     | Right -> eta_lookup eta' x0)

(** val lookup_argument_locations : eta -> x list -> location option list **)

let lookup_argument_locations eta0 args =
  map (eta_lookup eta0) args

(** val lookup_arguments_option : h -> eta -> x list -> v option list **)

let lookup_arguments_option h0 eta0 args =
  map (h_lookup_optional_loc h0) (lookup_argument_locations eta0 args)

(** val remove_optional_v : v option -> v **)

let remove_optional_v = function
| Some v0 -> v0
| None -> V_Error

(** val lookup_arguments : h -> eta -> x list -> v list **)

let lookup_arguments h0 eta0 args =
  map remove_optional_v (lookup_arguments_option h0 eta0 args)

(** val convert_C_to_CL : c -> mu -> cL option **)

let convert_C_to_CL c0 mu0 =
  HashMap.find c0 mu0

(** val convert_CL_to_C : cL -> c **)

let convert_CL_to_C = function
| ClassDecl (classname, o, f0, m0) -> classname

(** val convert_CLList_to_CList : cL list -> c list **)

let convert_CLList_to_CList =
  map convert_CL_to_C

(** val get_parent_of_CL_as_CL : cL -> cL option **)

let get_parent_of_CL_as_CL = function
| ClassDecl (c0, superclass, f0, m0) -> superclass

(** val get_id_from_C : c -> id **)

let get_id_from_C c0 =
  c0

(** val get_class_hierarchy_gas_CL_to_CLList :
    nat -> cL option -> mu -> cLList option **)

let rec get_class_hierarchy_gas_CL_to_CLList n cl mu0 =
  match n with
  | O -> None
  | S n' ->
    (match cl with
     | Some cl0 ->
       let ClassDecl (class0, superclass, f0, m0) = cl0 in
       (match superclass with
        | Some cl1 ->
          option_map (fun x0 -> app x0 (Cons (cl1, Nil)))
            (get_class_hierarchy_gas_CL_to_CLList n'
              (get_parent_of_CL_as_CL cl1) mu0)
        | None -> Some (Cons (cl0, Nil)))
     | None -> None)

(** val get_class_hierarchy_CL_to_CLList : nat -> cL -> mu -> cLList **)

let get_class_hierarchy_CL_to_CLList n cl mu0 =
  match get_class_hierarchy_gas_CL_to_CLList n (Some cl) mu0 with
  | Some cllist -> cllist
  | None -> Cons (cl, Nil)

(** val get_reversed_class_hierarchy_CL_to_CLList :
    nat -> cL -> mu -> cLList **)

let get_reversed_class_hierarchy_CL_to_CLList n cl mu0 =
  match get_class_hierarchy_gas_CL_to_CLList n (Some cl) mu0 with
  | Some cllist -> rev cllist
  | None -> Cons (cl, Nil)

(** val classes_of_parents_and_self : c -> mu -> cList option **)

let classes_of_parents_and_self c0 mu0 =
  match convert_C_to_CL c0 mu0 with
  | Some cl ->
    Some
      (convert_CLList_to_CList
        (get_class_hierarchy_CL_to_CLList (HashMap.cardinal mu0) cl mu0))
  | None -> Some (Cons (c0, Nil))

(** val class_decls_of_parents_and_self : c -> mu -> cLList option **)

let class_decls_of_parents_and_self c0 mu0 =
  match convert_C_to_CL c0 mu0 with
  | Some cl ->
    Some (get_class_hierarchy_CL_to_CLList (HashMap.cardinal mu0) cl mu0)
  | None -> None

(** val hierarchical_field_lookup_from_list :
    f -> cLList -> classToFieldLocationsMap -> location option **)

let rec hierarchical_field_lookup_from_list f0 cllist c2flm =
  match cllist with
  | Nil -> None
  | Cons (cl, t1) ->
    (match HashMap.find (get_id_from_C (convert_CL_to_C cl)) c2flm with
     | Some fls ->
       (match HashMap.find f0 fls with
        | Some loc -> Some loc
        | None -> hierarchical_field_lookup_from_list f0 t1 c2flm)
     | None -> hierarchical_field_lookup_from_list f0 t1 c2flm)

(** val hierarchical_field_lookup :
    f -> c -> classToFieldLocationsMap -> mu -> location option **)

let hierarchical_field_lookup f0 c0 c2flm mu0 =
  match convert_C_to_CL c0 mu0 with
  | Some cl ->
    (match get_reversed_class_hierarchy_CL_to_CLList (HashMap.cardinal c2flm)
             cl mu0 with
     | Nil -> None
     | Cons (cl0, t1) ->
       hierarchical_field_lookup_from_list f0 (Cons (cl0, t1)) c2flm)
  | None -> None

(** val field_lookup : heapObject -> c -> f -> mu -> location option **)

let field_lookup object0 c0 f0 mu0 =
  hierarchical_field_lookup f0 c0 object0 mu0

(** val contains_entry_for_class : c -> classToFieldLocationsMap -> bool **)

let contains_entry_for_class c0 c2flm =
  HashMap.mem (get_id_from_C c0) c2flm

(** val can_cast : heapObject -> c -> bool **)

let can_cast object0 c0 =
  contains_entry_for_class c0 object0

(** val cast : heapObject -> c -> heapObject option **)

let cast object0 c0 =
  match can_cast object0 c0 with
  | True -> Some object0
  | False -> None

(** val h_max : h -> location **)

let rec h_max h0 =
  fold_left max (map (fun el -> nat_of_P (fst el)) (HashMap.elements h0)) O

(** val h_malloc : h -> location **)

let h_malloc h0 =
  S (h_max h0)

(** val generate_n_numbers : nat -> nat -> locationList **)

let rec generate_n_numbers start base =
  match start with
  | O -> Nil
  | S n -> Cons ((plus start base), (generate_n_numbers n base))

(** val h_malloc_n : h -> nat -> locationList **)

let h_malloc_n h0 number = match number with
| O -> Nil
| S n -> generate_n_numbers number (h_max h0)

(** val convert_to_boolean_expr : boolean -> expression **)

let convert_to_boolean_expr b =
  Expr_V (V_Bool b)

(** val convert_pointer_to_expr : pointer -> expression **)

let convert_pointer_to_expr p0 =
  Expr_V (V_Pointer p0)

(** val v_equals : v -> v -> boolean **)

let v_equals v0 v1 =
  match v_eq_dec v0 v1 with
  | Left -> True
  | Right -> False

(** val h_extend : h -> location -> hv -> h **)

let h_extend h0 loc hv0 =
  HashMap.add (location_to_key loc) hv0 h0

(** val h_extend_star : h -> locationList -> v list -> h option **)

let rec h_extend_star h0 loclist varlist =
  match loclist with
  | Nil ->
    (match varlist with
     | Nil -> Some h0
     | Cons (v0, l) -> None)
  | Cons (loc, t1) ->
    (match varlist with
     | Nil -> None
     | Cons (var, t') -> h_extend_star (h_extend h0 loc (Hv_v var)) t1 t')

(** val assign_field_locations :
    locationList -> (f, v) prod list -> location HashMap.t **)

let rec assign_field_locations loclist fieldvaluelist =
  match loclist with
  | Nil -> HashMap.empty
  | Cons (loc, t1) ->
    (match fieldvaluelist with
     | Nil -> HashMap.empty
     | Cons (p0, t') ->
       let Pair (field, val0) = p0 in
       HashMap.add field loc (assign_field_locations t1 t'))

(** val create_hierarchical_field_location_map :
    locationList list -> fieldValueMap list -> fieldLocationMap list **)

let rec create_hierarchical_field_location_map hl dvs =
  match hl with
  | Nil -> Nil
  | Cons (loclist, t1) ->
    (match dvs with
     | Nil -> Nil
     | Cons (fvm, t') ->
       Cons ((assign_field_locations loclist (HashMap.elements fvm)),
         (create_hierarchical_field_location_map t1 t')))

(** val create_location_value_list_helper :
    (f, v) prod list -> fieldLocationMap -> (location, v) prod list **)

let rec create_location_value_list_helper fieldvalues flm =
  match fieldvalues with
  | Nil -> Nil
  | Cons (h0, t1) ->
    (match HashMap.find (fst h0) flm with
     | Some loc ->
       Cons ((Pair (loc, (snd h0))),
         (create_location_value_list_helper t1 flm))
     | None -> Nil)

(** val create_location_value_list :
    fieldLocationMap -> fieldValueMap -> (location, v) prod list **)

let create_location_value_list flm fvm =
  create_location_value_list_helper (HashMap.elements fvm) flm

(** val h_extend_star_hierarchical_map :
    h -> fieldLocationMap list -> fieldValueMap list -> h option **)

let rec h_extend_star_hierarchical_map h0 hl dvs =
  match hl with
  | Nil -> Some h0
  | Cons (flm, t1) ->
    (match dvs with
     | Nil -> Some h0
     | Cons (fvm, t') ->
       (match create_location_value_list flm fvm with
        | Nil -> h_extend_star_hierarchical_map h0 t1 t'
        | Cons (p0, tl) ->
          let Pair (loc, v0) = p0 in
          let Pair (loclist, vlist) = split tl in
          (match h_extend_star (h_extend h0 loc (Hv_v v0)) loclist vlist with
           | Some h' -> h_extend_star_hierarchical_map h' t1 t'
           | None -> None)))

(** val eta_extend : eta -> x -> location -> eta **)

let eta_extend eta0 x0 loc =
  Eta_NotMt (eta0, x0, loc)

(** val eta_extend_star : eta -> idList -> locationList -> eta option **)

let rec eta_extend_star eta0 xlist = function
| Nil ->
  (match xlist with
   | Nil -> Some eta0
   | Cons (i, l) -> None)
| Cons (loc, t1) ->
  (match xlist with
   | Nil -> None
   | Cons (var, t') ->
     eta_extend_star (Eta_NotMt (eta0, (SomeId var), loc)) t' t1)

(** val eval_if_then_else :
    boolean -> expression -> expression -> expression **)

let eval_if_then_else v1 e_t e_f =
  match v1 with
  | True -> e_t
  | False -> e_f

(** val get_method_list : cL -> methodMap **)

let get_method_list = function
| ClassDecl (c0, o, f0, methodlist) -> methodlist

(** val get_field_list : cL -> fieldTypeMap **)

let get_field_list = function
| ClassDecl (c0, o, fieldlist, m0) -> fieldlist

(** val method_lookup : m -> cL -> method0 option **)

let method_lookup m0 cl =
  HashMap.find m0 (get_method_list cl)

(** val get_class_with_virtual_method : m -> cL list -> cL option **)

let rec get_class_with_virtual_method m0 = function
| Nil -> None
| Cons (cl, t1) ->
  (match method_lookup m0 cl with
   | Some method1 -> Some cl
   | None -> get_class_with_virtual_method m0 t1)

(** val get_fields_of_parents_and_self_from_list :
    cL list -> fieldTypeMap list **)

let get_fields_of_parents_and_self_from_list cllist =
  map (fun cl -> get_field_list cl) cllist

(** val get_fields_of_parents_and_self_from_CL :
    cL -> mu -> fieldTypeMap list **)

let get_fields_of_parents_and_self_from_CL cl mu0 =
  get_fields_of_parents_and_self_from_list
    (get_class_hierarchy_CL_to_CLList (HashMap.cardinal mu0) cl mu0)

(** val get_fields_of_parents_and_self_C : c -> mu -> fieldTypeMap list **)

let get_fields_of_parents_and_self_C c0 mu0 =
  match convert_C_to_CL c0 mu0 with
  | Some cl -> get_fields_of_parents_and_self_from_CL cl mu0
  | None -> Nil

(** val get_hierarchical_type_map :
    fieldTypeMap list -> fieldTypeMap list **)

let get_hierarchical_type_map hfm =
  hfm

(** val get_default_value : t0 -> v **)

let get_default_value = function
| T_Bool -> V_Bool False
| T_Unit -> V_Unit
| T_Class c0 -> V_Pointer Null

(** val create_default_values_hash_map :
    (positive, t0) prod list -> v HashMap.t **)

let rec create_default_values_hash_map = function
| Nil -> HashMap.empty
| Cons (h0, t1) ->
  let Pair (field, type0) = h0 in
  HashMap.add field (get_default_value type0)
    (create_default_values_hash_map t1)

(** val get_default_values : fieldTypeMap -> fieldValueMap **)

let get_default_values ftm =
  create_default_values_hash_map (HashMap.elements ftm)

(** val get_hierarchical_default_values :
    fieldTypeMap list -> fieldValueMap list **)

let get_hierarchical_default_values htl =
  map (fun tm -> get_default_values tm) htl

(** val make_heap_pointer : location -> c -> hv **)

let make_heap_pointer loc c0 =
  Hv_v (V_Pointer (Addr (loc, c0)))

(** val argument_list_to_XList : argumentList -> idList **)

let argument_list_to_XList arglist =
  map (fun vardec -> get_variable_name vardec) arglist

(** val get_field_ids : fieldTypeMap -> id list **)

let get_field_ids ftm =
  map (fun el -> fst el) (HashMap.elements ftm)

(** val create_field_location_pairs :
    fieldTypeMap -> locationList -> (id, location) prod list **)

let create_field_location_pairs ftm loclist =
  combine
    (get_field_ids
      ftm)
    loclist

(** val create_field_location_map :
    (id,
    location)
    prod
    list
    ->
    fieldLocationMap **)

let rec create_field_location_map = function
| Nil ->
  HashMap.empty
| Cons
    (p0,
     t1) ->
  let Pair
    (x0,
     loc) =
    p0
  in
  HashMap.add
    x0
    loc
    (create_field_location_map
      t1)

(** val build_class_loc_lists_helper :
    (c,
    (fieldTypeMap,
    locationList)
    prod)
    prod
    list
    ->
    classToFieldLocationsMap **)

let rec build_class_loc_lists_helper = function
| Nil ->
  HashMap.empty
| Cons
    (p0,
     t1) ->
  let Pair
    (c0,
     p1) =
    p0
  in
  let Pair
    (ftm,
     loclist) =
    p1
  in
  HashMap.add
    c0
    (create_field_location_map
      (create_field_location_pairs
        ftm
        loclist))
    (build_class_loc_lists_helper
      t1)

(** val build_class_loc_lists :
    cList
    ->
    fieldTypeMap
    list
    ->
    locationList
    list
    ->
    classToFieldLocationsMap **)

let build_class_loc_lists hcl hfl hl =
  match beq_nat
          (length
            hfl)
          (length
            hl) with
  | True ->
    let fields_and_locations =
      combine
        hfl
        hl
    in
    (match beq_nat
             (length
               hcl)
             (length
               fields_and_locations) with
     | True ->
       build_class_loc_lists_helper
         (combine
           hcl
           fields_and_locations)
     | False ->
       HashMap.empty)
  | False ->
    HashMap.empty

(** val get_required_heap_space :
    nat
    list
    ->
    nat **)

let get_required_heap_space l =
  fold_left
    plus
    l
    O

(** val partition_list :
    location
    list
    ->
    nat
    list
    ->
    locationList
    list **)

let rec partition_list the_list element_lengths =
  match beq_nat
          (length
            the_list)
          (get_required_heap_space
            element_lengths) with
  | True ->
    (match element_lengths with
     | Nil ->
       Nil
     | Cons
         (len,
          t1) ->
       (match the_list with
        | Nil ->
          Nil
        | Cons
            (h0,
             t') ->
          Cons
            ((firstn
               len
               the_list),
            (partition_list
              (skipn
                len
                the_list)
              t1))))
  | False ->
    Nil

(** val h_malloc_n_star :
    h
    ->
    nat
    list
    ->
    locationList
    list **)

let h_malloc_n_star h0 l = match l with
| Nil ->
  Nil
| Cons
    (n,
     l0) ->
  partition_list
    (h_malloc_n
      h0
      (get_required_heap_space
        l))
    l

(** val get_value_lengths :
    fieldValueMap
    list
    ->
    nat
    list **)

let get_value_lengths hfvm =
  map
    (fun fvm ->
    HashMap.cardinal
      fvm)
    hfvm

(** val inject :
    p
    ->
    state **)

let inject = function
| Program
    (mu0,
     entrypoint) ->
  let EntryPoint
    (c0,
     m0) =
    entrypoint
  in
  StateCons
  (mu0,
  HashMap.empty,
  Eta_mt,
  (MethodInvocation
  ((NewClass
  c0),
  m0,
  Nil)),
  K_Return)

(** val inject_with_state :
    state
    ->
    m
    ->
    state **)

let inject_with_state s m0 =
  let StateCons
    (mu0,
     h0,
     eta0,
     e,
     k) =
    s
  in
  StateCons
  (mu0,
  h0,
  eta0,
  (MethodInvocation
  (e,
  m0,
  Nil)),
  K_Return)

(** val exprReduces_dec :
    state
    ->
    state
    sumor **)

let exprReduces_dec = function
| StateCons
    (m0,
     h0,
     e,
     e0,
     c0) ->
  (match e0 with
   | Expr_X
       x0 ->
     let eta_lookup_e_x =
       eta_lookup
         e
         x0
     in
     (match eta_lookup_e_x with
      | Some
          l ->
        let h_lookup_h_l =
          h_lookup
            h0
            l
        in
        (match h_lookup_h_l with
         | Some
             h1 ->
           Inleft
             (StateCons
             (m0,
             h0,
             e,
             (Expr_V
             (hv_To_V
               l
               h1)),
             c0))
         | None ->
           Inright)
      | None ->
        Inright)
   | Expr_V
       v0 ->
     (match c0 with
      | K_Return ->
        Inright
      | K_FieldAccess
          (f0,
           c1) ->
        (match v0 with
         | V_Pointer
             p0 ->
           (match p0 with
            | Addr
                (loc,
                 c2) ->
              let h_lookup_h_loc =
                h_lookup
                  h0
                  loc
              in
              (match h_lookup_h_loc with
               | Some
                   h1 ->
                 (match h1 with
                  | Hv_v
                      hv0 ->
                    Inright
                  | Hv_object
                      obj ->
                    let cast_obj_c0 =
                      cast
                        obj
                        c2
                    in
                    (match cast_obj_c0 with
                     | Some
                         object0 ->
                       let field_lookup_object_f_mu =
                         field_lookup
                           object0
                           c2
                           f0
                           m0
                       in
                       (match field_lookup_object_f_mu with
                        | Some
                            loc_0 ->
                          let h_lookup_h_loc_0 =
                            h_lookup
                              h0
                              loc_0
                          in
                          (match h_lookup_h_loc_0 with
                           | Some
                               hv0 ->
                             (match hv0 with
                              | Hv_v
                                  v1 ->
                                Inleft
                                  (StateCons
                                  (m0,
                                  h0,
                                  e,
                                  (Expr_V
                                  v1),
                                  c1))
                              | Hv_object
                                  h2 ->
                                Inright)
                           | None ->
                             Inright)
                        | None ->
                          Inright)
                     | None ->
                       Inright))
               | None ->
                 Inright)
            | Null ->
              Inright)
         | _ ->
           Inright)
      | K_MethodInvocation
          (m1,
           l,
           c1) ->
        (match v0 with
         | V_Pointer
             p0 ->
           Inleft
             (StateCons
             (m0,
             h0,
             e,
             (Raw
             (p0,
             m1,
             (lookup_arguments
               h0
               e
               l))),
             c1))
         | _ ->
           Inright)
      | K_EqualityLeftOperand
          (e1,
           c1) ->
        Inleft
          (StateCons
          (m0,
          h0,
          e,
          e1,
          (K_EqualityRightOperand
          (v0,
          c1))))
      | K_EqualityRightOperand
          (v1,
           c1) ->
        Inleft
          (StateCons
          (m0,
          h0,
          e,
          (convert_to_boolean_expr
            (v_equals
              v0
              v1)),
          c1))
      | K_Cast
          (c1,
           c2) ->
        (match v0 with
         | V_Pointer
             p0 ->
           (match p0 with
            | Addr
                (loc,
                 c3) ->
              let h_lookup_h_loc =
                h_lookup
                  h0
                  loc
              in
              (match h_lookup_h_loc with
               | Some
                   hl ->
                 (match hl with
                  | Hv_v
                      hv0 ->
                    Inright
                  | Hv_object
                      object0 ->
                    let can_cast0 =
                      can_cast
                        object0
                        c1
                    in
                    (match can_cast0 with
                     | True ->
                       Inleft
                         (StateCons
                         (m0,
                         h0,
                         e,
                         (Expr_V
                         (V_Pointer
                         (Addr
                         (loc,
                         c1)))),
                         c2))
                     | False ->
                       Inright))
               | None ->
                 Inright)
            | Null ->
              Inright)
         | _ ->
           Inright)
      | K_InstanceOf
          (c1,
           c2) ->
        (match v0 with
         | V_Pointer
             p0 ->
           (match p0 with
            | Addr
                (loc,
                 c3) ->
              let h_lookup_h_loc =
                h_lookup
                  h0
                  loc
              in
              (match h_lookup_h_loc with
               | Some
                   hl ->
                 (match hl with
                  | Hv_v
                      hv0 ->
                    Inright
                  | Hv_object
                      object0 ->
                    let can_cast_object =
                      can_cast
                        object0
                        c1
                    in
                    Inleft
                    (StateCons
                    (m0,
                    h0,
                    e,
                    (convert_to_boolean_expr
                      can_cast_object),
                    c2)))
               | None ->
                 Inright)
            | Null ->
              Inright)
         | _ ->
           Inright)
      | K_VarAssign
          (x0,
           c1) ->
        let elex =
          eta_lookup
            e
            x0
        in
        (match elex with
         | Some
             loc ->
           let extendedH =
             h_extend
               h0
               loc
               (Hv_v
               v0)
           in
           Inleft
           (StateCons
           (m0,
           extendedH,
           e,
           (Expr_V
           v0),
           c1))
         | None ->
           Inright)
      | K_FieldAssign
          (x0,
           f0,
           c1) ->
        let elex =
          eta_lookup
            e
            x0
        in
        (match elex with
         | Some
             loc_0 ->
           let hlhl0 =
             h_lookup
               h0
               loc_0
           in
           (match hlhl0 with
            | Some
                heapthing ->
              (match heapthing with
               | Hv_v
                   hv0 ->
                 (match hv0 with
                  | V_Pointer
                      p0 ->
                    (match p0 with
                     | Addr
                         (loc_1,
                          c2) ->
                       let hlhl1 =
                         h_lookup
                           h0
                           loc_1
                       in
                       (match hlhl1 with
                        | Some
                            heapthing0 ->
                          (match heapthing0 with
                           | Hv_v
                               hv1 ->
                             Inright
                           | Hv_object
                               obj ->
                             let cast_obj_c =
                               cast
                                 obj
                                 c2
                             in
                             (match cast_obj_c with
                              | Some
                                  object0 ->
                                let flofm =
                                  field_lookup
                                    object0
                                    c2
                                    f0
                                    m0
                                in
                                (match flofm with
                                 | Some
                                     loc_2 ->
                                   let h_0 =
                                     h_extend
                                       h0
                                       loc_2
                                       (Hv_v
                                       v0)
                                   in
                                   Inleft
                                   (StateCons
                                   (m0,
                                   h_0,
                                   e,
                                   (Expr_V
                                   v0),
                                   c1))
                                 | None ->
                                   Inright)
                              | None ->
                                Inright))
                        | None ->
                          Inright)
                     | Null ->
                       Inright)
                  | _ ->
                    Inright)
               | Hv_object
                   heapobj ->
                 Inright)
            | None ->
              Inright)
         | None ->
           Inright)
      | K_If
          (e1,
           e2,
           c1) ->
        (match v0 with
         | V_Bool
             b ->
           Inleft
             (StateCons
             (m0,
             h0,
             e,
             (eval_if_then_else
               b
               e1
               e2),
             c1))
         | _ ->
           Inright)
      | K_VarAssignIn
          (t1,
           x0,
           e1,
           c1) ->
        let loc_x =
          h_malloc
            h0
        in
        let h_0 =
          h_extend
            h0
            loc_x
            (Hv_v
            v0)
        in
        (match x0 with
         | This ->
           Inright
         | SomeId
             x1 ->
           let eta_0 =
             eta_extend
               e
               (SomeId
               x1)
               loc_x
           in
           Inleft
           (StateCons
           (m0,
           h_0,
           eta_0,
           e1,
           (K_Pop
           (e,
           c1)))))
      | K_Seq
          (e1,
           c1) ->
        Inleft
          (StateCons
          (m0,
          h0,
          e,
          e1,
          c1))
      | K_Pop
          (e1,
           c1) ->
        Inleft
          (StateCons
          (m0,
          h0,
          e1,
          (Expr_V
          v0),
          c1)))
   | NewClass
       c1 ->
     let option_classlist =
       classes_of_parents_and_self
         c1
         m0
     in
     (match option_classlist with
      | Some
          classlist ->
        let hierarchicalfieldlist =
          get_fields_of_parents_and_self_C
            c1
            m0
        in
        let hierarchicaltypelist =
          get_hierarchical_type_map
            hierarchicalfieldlist
        in
        let defaultvalues =
          get_hierarchical_default_values
            hierarchicaltypelist
        in
        let hierarchicallocations =
          h_malloc_n_star
            h0
            (get_value_lengths
              defaultvalues)
        in
        let hierarchicalfieldlocmap =
          create_hierarchical_field_location_map
            hierarchicallocations
            defaultvalues
        in
        let option_h_0 =
          h_extend_star_hierarchical_map
            h0
            hierarchicalfieldlocmap
            defaultvalues
        in
        (match option_h_0 with
         | Some
             h_0 ->
           let loc_1 =
             h_malloc
               h_0
           in
           let listofclassfieldloclists =
             build_class_loc_lists
               classlist
               hierarchicalfieldlist
               hierarchicallocations
           in
           let h_1 =
             h_extend
               h_0
               loc_1
               (Hv_object
               listofclassfieldloclists)
           in
           let nonempty_classlist =
             beq_nat
               O
               (length
                 classlist)
           in
           (match nonempty_classlist with
            | True ->
              Inright
            | False ->
              Inleft
                (StateCons
                (m0,
                h_1,
                e,
                (convert_pointer_to_expr
                  (Addr
                  (loc_1,
                  c1))),
                c0)))
         | None ->
           Inright)
      | None ->
        Inright)
   | FieldRef
       (e1,
        f0) ->
     Inleft
       (StateCons
       (m0,
       h0,
       e,
       e1,
       (K_FieldAccess
       (f0,
       c0))))
   | MethodInvocation
       (e1,
        m1,
        l) ->
     Inleft
       (StateCons
       (m0,
       h0,
       e,
       e1,
       (K_MethodInvocation
       (m1,
       l,
       c0))))
   | Raw
       (p0,
        m1,
        l) ->
     (match p0 with
      | Addr
          (loc,
           c1) ->
        let hlhl =
          h_lookup
            h0
            loc
        in
        (match hlhl with
         | Some
             heapthing ->
           (match heapthing with
            | Hv_v
                hv0 ->
              Inright
            | Hv_object
                obj1 ->
              let optionclasslist =
                class_decls_of_parents_and_self
                  c1
                  m0
              in
              (match optionclasslist with
               | Some
                   classlist ->
                 let optionCL_t =
                   get_class_with_virtual_method
                     m1
                     classlist
                 in
                 (match optionCL_t with
                  | Some
                      cL_t ->
                    let c_t =
                      convert_CL_to_C
                        cL_t
                    in
                    let optionAMethod =
                      method_lookup
                        m1
                        cL_t
                    in
                    (match optionAMethod with
                     | Some
                         someAMethod ->
                       let AMethod
                         (m2,
                          t1,
                          a,
                          e1) =
                         someAMethod
                       in
                       let methodvars =
                         argument_list_to_XList
                           a
                       in
                       let loclist =
                         h_malloc_n
                           h0
                           (S
                           (length
                             l))
                       in
                       (match loclist with
                        | Nil ->
                          Inright
                        | Cons
                            (loc_o,
                             loclist0) ->
                          let h_tmp =
                            h_extend
                              h0
                              loc_o
                              (make_heap_pointer
                                loc
                                c_t)
                          in
                          let optionH_0 =
                            h_extend_star
                              h_tmp
                              loclist0
                              l
                          in
                          (match optionH_0 with
                           | Some
                               h_0 ->
                             let optionEta_0 =
                               eta_extend_star
                                 (eta_extend
                                   e
                                   This
                                   loc_o)
                                 methodvars
                                 loclist0
                             in
                             (match optionEta_0 with
                              | Some
                                  eta_0 ->
                                Inleft
                                  (StateCons
                                  (m0,
                                  h_0,
                                  eta_0,
                                  e1,
                                  (K_Pop
                                  (e,
                                  c0))))
                              | None ->
                                Inright)
                           | None ->
                             Inright))
                     | None ->
                       Inright)
                  | None ->
                    Inright)
               | None ->
                 Inright))
         | None ->
           Inright)
      | Null ->
        Inright)
   | Equality
       (e1,
        e2) ->
     Inleft
       (StateCons
       (m0,
       h0,
       e,
       e1,
       (K_EqualityLeftOperand
       (e2,
       c0))))
   | Cast
       (c1,
        e1) ->
     Inleft
       (StateCons
       (m0,
       h0,
       e,
       e1,
       (K_Cast
       (c1,
       c0))))
   | InstanceOf
       (e1,
        c1) ->
     Inleft
       (StateCons
       (m0,
       h0,
       e,
       e1,
       (K_InstanceOf
       (c1,
       c0))))
   | VarAssign
       (x0,
        e1) ->
     Inleft
       (StateCons
       (m0,
       h0,
       e,
       e1,
       (K_VarAssign
       (x0,
       c0))))
   | FieldAssign
       (x0,
        f0,
        e1) ->
     Inleft
       (StateCons
       (m0,
       h0,
       e,
       e1,
       (K_FieldAssign
       (x0,
       f0,
       c0))))
   | IfExpr
       (e1,
        e2,
        e3) ->
     Inleft
       (StateCons
       (m0,
       h0,
       e,
       e1,
       (K_If
       (e2,
       e3,
       c0))))
   | VarDecExp
       (v0,
        e1,
        e2) ->
     Inleft
       (let VarDec
          (name,
           t1) =
          v0
        in
       StateCons
       (m0,
       h0,
       e,
       e1,
       (K_VarAssignIn
       (t1,
       (SomeId
       name),
       e2,
       c0))))
   | VoidExp ->
     Inleft
       (StateCons
       (m0,
       h0,
       e,
       (Expr_V
       V_Unit),
       c0))
   | SeqExp
       (e1,
        e2) ->
     Inleft
       (StateCons
       (m0,
       h0,
       e,
       e1,
       (K_Seq
       (e2,
       c0)))))

(** val cLASS_Object :
    cL
    option **)

let cLASS_Object =
  None

(** val __class__Swap :
    positive **)

let __class__Swap =
  p_of_succ_nat
    (S
    O)

(** val __class__SwapTest :
    positive **)

let __class__SwapTest =
  p_of_succ_nat
    (S
    (S
    O))

(** val __field__Swap__a :
    positive **)

let __field__Swap__a =
  p_of_succ_nat
    (S
    (S
    (S
    O)))

(** val __field__Swap__b :
    positive **)

let __field__Swap__b =
  p_of_succ_nat
    (S
    (S
    (S
    (S
    O))))

(** val __field__SwapTest__instance :
    positive **)

let __field__SwapTest__instance =
  p_of_succ_nat
    (S
    (S
    (S
    (S
    (S
    O)))))

(** val __method__Swap__construct :
    positive **)

let __method__Swap__construct =
  p_of_succ_nat
    (S
    (S
    (S
    (S
    (S
    (S
    O))))))

(** val __method__Swap__swap :
    positive **)

let __method__Swap__swap =
  p_of_succ_nat
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    O)))))))

(** val __method__SwapTest__construct :
    positive **)

let __method__SwapTest__construct =
  p_of_succ_nat
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    O))))))))

(** val __method__SwapTest__testSwap :
    positive **)

let __method__SwapTest__testSwap =
  p_of_succ_nat
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    O)))))))))

(** val __local__Swap__construct__tmp :
    positive **)

let __local__Swap__construct__tmp =
  p_of_succ_nat
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    O))))))))))

(** val __local__SwapTest__construct__v :
    positive **)

let __local__SwapTest__construct__v =
  p_of_succ_nat
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    O)))))))))))

(** val __local__SwapTest__testSwap__c :
    positive **)

let __local__SwapTest__testSwap__c =
  p_of_succ_nat
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    (S
    O))))))))))))

(** val c_Swap :
    c **)

let c_Swap =
  __class__Swap

(** val c_SwapTest :
    c **)

let c_SwapTest =
  __class__SwapTest

(** val mETHOD_Swap__construct :
    method0 **)

let mETHOD_Swap__construct =
  AMethod
    (__method__Swap__construct,
    (T_Class
    c_Swap),
    Nil,
    (SeqExp
    ((FieldAssign
    (This,
    __field__Swap__a,
    (Expr_V
    (V_Bool
    False)))),
    (SeqExp
    ((FieldAssign
    (This,
    __field__Swap__b,
    (Expr_V
    (V_Bool
    True)))),
    (Expr_X
    This))))))

(** val mETHOD_Swap__swap :
    method0 **)

let mETHOD_Swap__swap =
  AMethod
    (__method__Swap__construct,
    (T_Class
    c_Swap),
    Nil,
    (VarDecExp
    ((VarDec
    (__local__Swap__construct__tmp,
    T_Bool)),
    (FieldRef
    ((Expr_X
    This),
    __field__Swap__b)),
    (SeqExp
    ((FieldAssign
    (This,
    __field__Swap__b,
    (FieldRef
    ((Expr_X
    This),
    __field__Swap__a)))),
    (FieldAssign
    (This,
    __field__Swap__a,
    (Expr_X
    (SomeId
    __local__Swap__construct__tmp)))))))))

(** val mETHOD_SwapTest__construct :
    method0 **)

let mETHOD_SwapTest__construct =
  AMethod
    (__method__SwapTest__construct,
    (T_Class
    c_SwapTest),
    Nil,
    (VarDecExp
    ((VarDec
    (__local__SwapTest__construct__v,
    (T_Class
    c_Swap))),
    (MethodInvocation
    ((NewClass
    c_Swap),
    __method__Swap__construct,
    Nil)),
    (SeqExp
    ((FieldAssign
    (This,
    __field__SwapTest__instance,
    (Expr_X
    (SomeId
    __local__SwapTest__construct__v)))),
    (Expr_X
    This))))))

(** val mETHOD_SwapTest__testSwap :
    method0 **)

let mETHOD_SwapTest__testSwap =
  AMethod
    (__method__SwapTest__testSwap,
    T_Bool,
    Nil,
    (VarDecExp
    ((VarDec
    (__local__SwapTest__testSwap__c,
    (T_Class
    c_Swap))),
    (FieldRef
    ((Expr_X
    This),
    __field__SwapTest__instance)),
    (SeqExp
    ((MethodInvocation
    ((Expr_X
    (SomeId
    __local__SwapTest__testSwap__c)),
    __method__Swap__swap,
    Nil)),
    (IfExpr
    ((FieldRef
    ((Expr_X
    (SomeId
    __local__SwapTest__testSwap__c)),
    __field__Swap__a)),
    (IfExpr
    ((FieldRef
    ((Expr_X
    (SomeId
    __local__SwapTest__testSwap__c)),
    __field__Swap__b)),
    (Expr_V
    (V_Bool
    False)),
    (Expr_V
    (V_Bool
    True)))),
    (Expr_V
    (V_Bool
    False)))))))))

(** val cLASS_Swap :
    cL **)

let cLASS_Swap =
  ClassDecl
    (c_Swap,
    cLASS_Object,
    (HashMap.add
      __field__Swap__a
      T_Bool
      (HashMap.add
        __field__Swap__b
        T_Bool
        HashMap.empty)),
    (HashMap.add
      __method__Swap__construct
      mETHOD_Swap__construct
      (HashMap.add
        __method__Swap__swap
        mETHOD_Swap__swap
        HashMap.empty)))

(** val cLASS_SwapTest :
    cL **)

let cLASS_SwapTest =
  ClassDecl
    (c_SwapTest,
    cLASS_Object,
    (HashMap.add
      __field__SwapTest__instance
      (T_Class
      c_Swap)
      HashMap.empty),
    (HashMap.add
      __method__SwapTest__construct
      mETHOD_SwapTest__construct
      (HashMap.add
        __method__SwapTest__testSwap
        mETHOD_SwapTest__testSwap
        HashMap.empty)))

(** val mu_Swap :
    mu **)

let mu_Swap =
  HashMap.add
    __class__Swap
    cLASS_Swap
    (HashMap.add
      __class__SwapTest
      cLASS_SwapTest
      HashMap.empty)

(** val swapTestProgram :
    p **)

let swapTestProgram =
  Program
    (mu_Swap,
    (EntryPoint
    (c_SwapTest,
    __method__SwapTest__construct)))

(** val initialState_Swap :
    state **)

let initialState_Swap =
  inject
    swapTestProgram

(** val testSwap :
    state **)

let testSwap =
  inject_with_state
    initialState_Swap
    __method__SwapTest__testSwap

(** val mlProgram_Swap :
    state
    sumor **)

let mlProgram_Swap =
  exprReduces_dec
    testSwap

