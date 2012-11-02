Require Import Arith Bool List.
Require Import FMaps.
Require Import Coq.NArith.BinPos.

(* (id variable-not-otherwise-mentioned) *)
Definition id := positive.

(* (f id) *)
Definition F := id.

(* (m id) *)
Definition M := id.

(* (C Object
      id)

Drop "Object" from this definition since it is not necessary (it only serves
to mark the upper bounderaries of class hierarchies for field lookups, etc, in
the PLT Redex model.
 *)
Inductive C : Set :=
 | SomeClass : id -> C.

Definition Boolean := bool.

(* (T bool
      unit
      C)
 *)
Inductive T : Set :=
 | T_Bool
 | T_Unit
 | T_Class: C -> T.

(* (x this
      id)
 *)
Inductive X : Set :=
 | This
 | SomeId : id -> X.

(* (loc number) *)
Definition Location := nat.

(* (pointer (addr loc C)
            null)
 *)
Inductive Pointer : Set :=
 | Addr : Location -> C -> Pointer
 | Null.

(* (v pointer
     true
     false
     unit
     error)
 *)
Inductive V : Set :=
 | V_Pointer : Pointer -> V
 | V_Bool    : Boolean -> V
 | V_Error
 | V_Unit.

Inductive VariableDeclaration : Set :=
 | VarDec : id -> T -> VariableDeclaration.

(*
  (e x
     v
     (new C)
     (e $ f)
     (e @ m (e ...))
     (raw v @ m (v ...))
     (e == e)
     (C e)
     (e instanceof C)
     (x := e)
     (x $ f := e)
     (if e e else e)
     (var T x := e in e)
     (begin e ...))
*)
Inductive Expression : Set :=
 | Expr_X           : X -> Expression
 | Expr_V           : V -> Expression
 | NewClass         : C -> Expression
 | FieldRef         : Expression -> F -> Expression
 | MethodInvocation : Expression -> M -> list X -> Expression
 | Raw              : Pointer -> M -> list V -> Expression
 | Equality         : Expression -> Expression -> Expression
 | Cast             : C -> Expression -> Expression
 | InstanceOf       : Expression -> C -> Expression
 | VarAssign        : X -> Expression -> Expression
 | FieldAssign      : X -> F -> Expression -> Expression
 | IfExpr           : Expression -> Expression -> Expression -> Expression
 | VarDecExp        : VariableDeclaration -> Expression -> Expression -> Expression
 | VoidExp          : Expression
 | SeqExp           : Expression -> Expression -> Expression.

Definition ArgumentList := list VariableDeclaration.

(* (M (T m ([T x] ...) e))
 *)
Inductive Method : Set :=
 | AMethod : M -> T -> ArgumentList -> Expression -> Method.

Module HashMap := PositiveMap.

Definition FieldTypeMap  := HashMap.t T.
Definition FieldValueMap := HashMap.t V.
Definition MethodMap     := HashMap.t Method.

(* (CL (class C extends C ([T f] ...) (M ...)))
 *)
Inductive CL : Set :=
 | ClassDecl : C -> option CL -> FieldTypeMap -> MethodMap -> CL.

(* (Mu (CL ...))
 *)
Definition Mu := HashMap.t CL.

Inductive ProgramEntryPoint : Set :=
 | EntryPoint : C -> M -> ProgramEntryPoint.

(* (P (mu (C m)))
 *)
Inductive P : Set :=
 | Program: Mu -> ProgramEntryPoint -> P.

Definition FieldLocationMap := HashMap.t Location.
Definition ClassToFieldLocationsMap := HashMap.t FieldLocationMap.

(* (object ((C [f loc] ...) ...))
 *)
Inductive HeapObject : Set :=
 | HeapObj : ClassToFieldLocationsMap -> HeapObject.

(* (hv v
       object)
 *)
Inductive Hv : Set :=
 | Hv_v      : V -> Hv
 | Hv_object : HeapObject -> Hv.

(* (h mt
      (h [loc -> hv]))
 *)
Definition H := HashMap.t Hv.

(* (eta mt
      (eta [x -> loc]))
 *)
Inductive Eta : Set :=
 | Eta_mt    : Eta
 | Eta_NotMt : Eta -> X -> Location -> Eta.

(* (k ret
      ( * $ f -> k)
      ( * @ m (e ...) -> k)
      (v @ m (v ...) * (e ...) -> k)
      ( * == e -> k)
      (v == * -> k)
      (C * -> k)
      ( * instanceof C -> k)
      (x := * -> k)
      (x $ f := * -> k)
      (if * e else e -> k)
      (var T x := * in e -> k)
      (begin * (e ...) -> k)
      (pop eta k))
 *)
Inductive Continuation : Set :=
 | K_Return               : Continuation
 | K_FieldAccess          : F -> Continuation -> Continuation
 | K_MethodInvocation     : M -> list X -> Continuation -> Continuation
 | K_EqualityLeftOperand  : Expression -> Continuation -> Continuation
 | K_EqualityRightOperand : V -> Continuation -> Continuation
 | K_Cast                 : C -> Continuation -> Continuation
 | K_InstanceOf           : C -> Continuation -> Continuation
 | K_VarAssign            : X -> Continuation -> Continuation
 | K_FieldAssign          : X -> F -> Continuation -> Continuation
 | K_If                   : Expression -> Expression -> Continuation -> Continuation
 | K_VarAssignIn          : T -> X -> Expression -> Continuation -> Continuation
 | K_Seq                  : Expression -> Continuation -> Continuation
 | K_Pop                  : Eta -> Continuation -> Continuation.

Inductive State : Set :=
 | StateCons : Mu -> H -> Eta -> Expression -> Continuation -> State.

Inductive ThreadState : Set :=
 | ThreadStateCons : Eta -> Expression -> Continuation -> ThreadState.

Inductive GState : Set :=
 | GStateCons : Mu -> H -> list ThreadState -> GState.

Definition Hv_To_V (loc:Location) (hv:Hv) : V :=
 match hv with
 | Hv_v v            => v
 | Hv_object heapobj => V_Error
 end.

Definition get_variable_name (vardec:VariableDeclaration) :=
 match vardec with
 | VarDec someid _ => someid
 end.

(* -------------------------------------------------------------------------- *)
(* ------------------------- Additional Definitions ------------------------- *)
(* -------------------------------------------------------------------------- *)
Definition CList        := list C.
Definition CLList       := list CL.
Definition IdList       := list id.
Definition XList        := list X.
Definition LocationList := list Location.

Definition id_eq_dec := positive_eq_dec.
Definition F_eq_dec := id_eq_dec.
Definition M_eq_dec := id_eq_dec.

(* -------------------------------------------------------------------------- *)
(* -------------------------- Decidability Proofs --------------------------- *)
(* -------------------------------------------------------------------------- *)
Theorem X_eq_dec:
 forall (x y:X), {x = y} + {x <> y}.
Proof.
 decide equality.
 apply id_eq_dec.
Qed.

Theorem C_eq_dec:
 forall (x y:C), {x = y} + {x <> y}.
Proof.
 decide equality.
 apply id_eq_dec.
Qed.

Theorem Pointer_eq_dec:
 forall (x y:Pointer), {x = y} + {x <> y}.
Proof.
 decide equality.
 apply C_eq_dec.
 apply eq_nat_dec.
Qed.

(*
 We don't need a "Boolean_eq_dec" theorem since we have aliased Boolean
 to bool. Therefore, "bool_dec" will suffice.
*)

Theorem V_eq_dec:
 forall (x y:V), {x = y} + {x <> y}.
Proof.
 decide equality.
 apply Pointer_eq_dec.
 apply bool_dec.
Qed.

(*
Theorem SimpleType_eq_dec:
 forall (x y:SimpleType), {x=y} + {x <> y}.
Proof.
 decide equality.
 apply bool_dec.
Qed.
*)

Theorem T_eq_dec:
 forall (x y:T), {x=y} + {x <> y}.
Proof.
 decide equality.
 apply C_eq_dec.
Qed.

Theorem VariableDeclaration_eq_dec:
 forall (x y:VariableDeclaration), {x = y} + {x <> y}.
Proof.
 decide equality.
 apply T_eq_dec.
 apply id_eq_dec.
Qed.

Theorem ValueList_eq_dec:
 forall (x y:list V), {x=y} + {x <> y}.
Proof.
 decide equality.
 apply V_eq_dec.
Qed.

Theorem Expression_eq_dec:
 forall (x y: Expression), {x=y} + {x <> y}.
Proof.
 decide equality.
 apply X_eq_dec.
 apply V_eq_dec.
 apply C_eq_dec.
 apply F_eq_dec.
 apply list_eq_dec.
 apply X_eq_dec.
 apply M_eq_dec.
 apply list_eq_dec.
 apply V_eq_dec.
 apply M_eq_dec.
 apply Pointer_eq_dec.
 apply C_eq_dec.
 apply C_eq_dec.
 apply X_eq_dec.
 apply F_eq_dec.
 apply X_eq_dec.
 apply VariableDeclaration_eq_dec.
Qed.

Theorem Method_eq_dec:
 forall (x y:Method), {x = y} + {x <> y}.
Proof.
 decide equality.
 apply Expression_eq_dec.
 apply list_eq_dec.
 apply VariableDeclaration_eq_dec.
 apply T_eq_dec.
 apply M_eq_dec.
Qed.

Theorem Eta_eq_dec:
 forall (x y:Eta), {x=y} + {x <> y}.
Proof.
 decide equality.
 apply eq_nat_dec.
 apply X_eq_dec.
Qed.

Theorem Continuation_eq_dec:
 forall (x y:Continuation), {x=y} + {x <> y}.
Proof.
 decide equality.
 apply F_eq_dec.
 apply list_eq_dec.
 apply X_eq_dec.
 apply M_eq_dec.
 apply Expression_eq_dec.
 apply V_eq_dec.
 apply C_eq_dec.
 apply C_eq_dec.
 apply X_eq_dec.
 apply F_eq_dec.
 apply X_eq_dec.
 apply Expression_eq_dec.
 apply Expression_eq_dec.
 apply Expression_eq_dec.
 apply X_eq_dec.
 apply T_eq_dec.
 apply Expression_eq_dec.
 apply Eta_eq_dec.
Qed.

(* -------------------------------------------------------------------------- *)
(* ---------------------------- Helper Functions ---------------------------- *)
(* -------------------------------------------------------------------------- *)

Definition location_to_key := P_of_succ_nat.
Definition h_lookup (h: H) (loc : Location) : option Hv := HashMap.find (location_to_key loc) h.
Definition h_lookup_optional_loc (h: H) (loc : option Location) : option V :=
 match loc with
 | None => None
 | Some loc => let res := HashMap.find (location_to_key loc) h in
               match res with
               | None => None
               | Some hv => Some (Hv_To_V loc hv)
               end
 end.

Fixpoint eta_lookup (eta: Eta) (x : X) : option Location :=
 match eta with
 | Eta_mt                => None
 | Eta_NotMt eta' x' loc => if X_eq_dec x x' then Some loc else eta_lookup eta' x
 end.

Definition lookup_argument_locations (eta:Eta) (args:list X) : list (option Location) :=
 map (eta_lookup eta) args.

Definition lookup_arguments_option (h:H) (eta:Eta) (args:list X) : list (option V) :=
 map (h_lookup_optional_loc h) (lookup_argument_locations eta args).

Definition remove_optional_v optionv :=
 match optionv with
 | Some v => v
 | _ => V_Error
 end.

Definition lookup_arguments (h:H) (eta:Eta) (args:list X) : list V :=
 map remove_optional_v (lookup_arguments_option h eta args).

(* Look up the class "c" in the registry "mu" *)

Definition convert_C_to_CL (c:C) (mu:Mu) : option CL :=
 match c with
 | SomeClass id => HashMap.find id mu
 end.

Definition convert_CL_to_C (cl:CL) : C :=
 match cl with
 | ClassDecl classname _ _ _ => classname
 end.

Definition class_lookup                   := convert_C_to_CL.
Definition convert_CList_to_CLList (mu:Mu):= map (fun c => convert_C_to_CL c mu).
Definition convert_CLList_to_CList        := map convert_CL_to_C.
Definition convert_CLList_to_CList_option := option_map convert_CL_to_C.

Definition get_parent_of_CL_as_CL (cl:CL) : option CL :=
 match cl with
 | ClassDecl _ superclass _ _ => superclass
 end.

Definition get_parent_of_C_as_CL (c:C) (mu:Mu) : option CL :=
 match (convert_C_to_CL c mu) with
 | None  => None
 | Some cl => get_parent_of_CL_as_CL cl
 end.

Definition get_parent_of_cl_as_C (cl:CL) : option C :=
 match (get_parent_of_CL_as_CL cl) with
 | None     => None
 | Some cl' => Some (convert_CL_to_C cl')
 end.

Definition get_parent_of_c_as_C (c:C) (mu:Mu) : option C :=
 match (convert_C_to_CL c mu) with
 | None    => None
 | Some cl => get_parent_of_cl_as_C cl
 end.

Definition get_id_from_C (c:C) : id :=
 match c with
 | SomeClass someid => someid
 end.

Definition get_C_from_id (someid:id) : C := SomeClass someid.
Definition get_CL_from_id (someid:id) (mu:Mu) : option CL := convert_C_to_CL (get_C_from_id someid) mu.

Fixpoint get_class_hierarchy_gas_CL_to_CLList (n:nat) (cl: option CL) (mu:Mu) : option CLList :=
 match n with
 | O    => None
 | S n' => match cl with
           | None    => None
           | Some cl => match cl with
                        | ClassDecl class superclass _ _ =>
                                    match superclass with
                                    | None    => Some (cl::nil) (* Important! Do not return nil *)
                                    | Some cl => option_map (fun x => (x ++ (cl :: nil)))
                                                 (get_class_hierarchy_gas_CL_to_CLList n' (get_parent_of_CL_as_CL cl) mu)
                                    end
                        end
           end
 end.

Definition get_class_hierarchy_CL_to_CLList (n:nat) (cl:CL) (mu:Mu) : CLList :=
 match get_class_hierarchy_gas_CL_to_CLList n (Some cl) mu with
 | None        => cl :: nil
 | Some cllist => cllist
 end.

Definition get_reversed_class_hierarchy_CL_to_CLList (n:nat) (cl:CL) (mu:Mu) : CLList :=
 match get_class_hierarchy_gas_CL_to_CLList n (Some cl) mu with
 | None        => cl :: nil
 | Some cllist => rev cllist
 end.

Definition class_list_from_class_to_field_locations_map (c2flm:ClassToFieldLocationsMap) : CList :=
 map (fun p => (get_C_from_id (fst p))) (HashMap.elements c2flm).

(* Not Useful
Definition class_list_from_object (object:HeapObject) : CList :=
 match object with
 | HeapObj c2flm => class_list_from_class_to_field_locations_map c2flm
 end.
*)

Definition classes_of_parents_and_self (c:C) (mu:Mu) : option CList :=
 match (convert_C_to_CL c mu) with
 | None    => Some (c :: nil)
 | Some cl => Some (convert_CLList_to_CList (get_class_hierarchy_CL_to_CLList (HashMap.cardinal mu) cl mu))
 end.

Definition class_decls_of_parents_and_self (c:C) (mu:Mu) : option CLList :=
 match (convert_C_to_CL c mu) with
 | None    => None
 | Some cl => Some (get_class_hierarchy_CL_to_CLList (HashMap.cardinal mu) cl mu)
 end.

Fixpoint hierarchical_field_lookup_from_list (f:F) (cllist:CLList) (c2flm:ClassToFieldLocationsMap) : option Location :=
 match cllist with
 | nil     => None
 | cl :: t => match HashMap.find (get_id_from_C (convert_CL_to_C cl)) c2flm with
              | None     => (hierarchical_field_lookup_from_list f t c2flm)
              | Some fls => match HashMap.find f fls with
                            | Some loc => Some loc
                            | None     => (hierarchical_field_lookup_from_list f t c2flm)
                            end
              end
 end.

Definition hierarchical_field_lookup (f:F) (c:C) (c2flm:ClassToFieldLocationsMap) (mu:Mu) : option Location :=
 match (convert_C_to_CL c mu) with
 | None    => None
 | Some cl => match get_reversed_class_hierarchy_CL_to_CLList (HashMap.cardinal c2flm) cl mu with
              | nil   => None
              | cl::t => (hierarchical_field_lookup_from_list f (cl::t) c2flm)
              end
 end.

Definition field_lookup (object:HeapObject) (c:C) (f:F) (mu:Mu) : option Location :=
 match object with
 | HeapObj c2flm => (hierarchical_field_lookup f c c2flm mu)
 end.

Definition contains_entry_for_class (c:C) (c2flm:ClassToFieldLocationsMap) : bool :=
 HashMap.mem (get_id_from_C c) c2flm.

Definition can_cast (object:HeapObject) (c:C) : bool :=
 match object with
 | HeapObj cfll => contains_entry_for_class c cfll
 end.

(* Only needs to ensure that the cast type is in the hierarchy *)
Definition cast (object:HeapObject) (c:C) : option HeapObject :=
 match object with
 | HeapObj cfll => if (can_cast object c) then Some object else None
 end.

Fixpoint h_max (h:H) : Location :=
 fold_left MinMax.max (map (fun el => nat_of_P (fst(el))) (HashMap.elements h)) O.

Definition h_malloc (h:H) : Location := S (h_max h).

(* Generate a list of numbers from [base .. start+base] (happens to be in reverse) *)

Fixpoint generate_n_numbers (start base:nat) : LocationList :=
 match start with
 | O   => nil
 | S n => (start + base) :: (generate_n_numbers n base)
 end.

Definition h_malloc_n (h:H) (number:nat) : LocationList :=
 match number with
 | O => nil
 | _ => generate_n_numbers number (h_max h)
 end.

Definition convert_to_boolean_expr (b:Boolean) : Expression := Expr_V (V_Bool b).
Definition convert_pointer_to_expr (p:Pointer) : Expression := Expr_V (V_Pointer p).
Definition Boolean_equals := eqb.

(*
   XXX How does casting affect pointer equality?
       Should we verify that two pointers pointing to the same location are of related types
       as is done by Java (which gives the "Incompatible operand types ? and ?" message)
   This method considers two pointers equal if and only if
   1. They're both Null
   2. They're both non-Null and both point to the same heap location
   3. Are both of the exact same type (not related but exact!)
*)
Definition Pointer_equals (p0 p1: Pointer) : Boolean :=
 match Pointer_eq_dec p0 p1 with
 | left _ => true
 | _ => false
 end.

Definition V_equals (v0 v1:V) : Boolean :=
 match V_eq_dec v0 v1 with
 | left _ => true
 | _ => false
 end.

Definition h_extend (h:H) (loc:Location) (hv:Hv) : H := HashMap.add (location_to_key loc) hv h.

(*
(* Use a hashmap for this (replace h_extend_star usage with it *)
Definition alloc_and_write_this_and_args (h:H) (varlist:ValueList) : H :=
.
   (* allocate locations for "this" and the arguments *)
   (h_malloc_n h (S (length varlist)))        = (loc_o::loclist)
*)

Fixpoint h_extend_star (h:H) (loclist:LocationList) (varlist:list V) : option H :=
  match loclist, varlist with
  | nil,    nil     => Some h
  | loc::t, var::t' => h_extend_star (h_extend h loc (Hv_v var)) t t'
  | _, _            => None
  end.

Theorem eq_lengths_means_some_h:
 forall (loclist:LocationList) (varlist:list V) h h',
  (length loclist) = (length varlist) -> (h_extend_star h loclist varlist = Some h').
Proof.
 intros.
 Admitted.

Fixpoint h_extend_star_hierarchical_list (h:H) (hl:list LocationList) (dvs:list (list V)) : option H :=
 match hl, dvs with
 | nil,   nil  => Some h
 | l::t, v::t' => match (h_extend_star h l v) with
                  | None    => None
                  | Some h' => h_extend_star_hierarchical_list h' t t'
                  end
 | _,       _  => None
 end.

Fixpoint assign_field_locations (loclist:LocationList) (fieldvaluelist:list (F * V)) : HashMap.t Location :=
 match loclist, fieldvaluelist with
 | loc::t, (field, val)::t' => HashMap.add field loc (assign_field_locations t t')
 | _, _ => HashMap.empty Location
 end.

Fixpoint create_hierarchical_field_location_map (hl:list LocationList) (dvs:list FieldValueMap) : list FieldLocationMap :=
 match hl, dvs with
 | loclist::t, fvm::t' => (assign_field_locations loclist (HashMap.elements fvm)) :: (create_hierarchical_field_location_map t t')
 | _, _ => nil
 end.

Fixpoint create_location_value_list_helper (fieldvalues:list (F*V)) (flm:FieldLocationMap) : list (Location*V) :=
 match fieldvalues with
 | h::t => match (HashMap.find (fst h) flm) with
           | Some loc => (loc, (snd h)) :: (create_location_value_list_helper t flm)
           | None => nil
           end
 | _  => nil
 end.

Definition create_location_value_list (flm:FieldLocationMap) (fvm:FieldValueMap) : list (Location*V) :=
 create_location_value_list_helper (HashMap.elements fvm) flm.

Definition create_hierarchical_location_value_list (hl:list FieldLocationMap) (dvs:list FieldValueMap) :=
 map (fun hl_dvs => create_location_value_list (fst hl_dvs) (snd hl_dvs)) (combine hl dvs).

Fixpoint h_extend_star_hierarchical_map (h:H) (hl:list FieldLocationMap) (dvs:list FieldValueMap) : option H :=
 match hl, dvs with
 | flm::t, fvm::t' => match create_location_value_list flm fvm with
                      | nil => h_extend_star_hierarchical_map h t t'
                      | (loc, v)::tl => let (loclist, vlist) := (split tl) in
                                        match (h_extend_star (h_extend h loc (Hv_v v)) loclist vlist) with
                                        | None => None
                                        | Some h' => (h_extend_star_hierarchical_map h' t t')
                                        end
                      end
 | _, _ => Some h
 end.

Definition eta_extend (eta:Eta) (x:X) (loc:Location) := (Eta_NotMt eta x loc).

(*
XXX Ignores invalid arguments such as mismatched lengths for loclist & varlist
Check for extending with something that already exists - a hashmap would easily
handle these scenarios
*)
Fixpoint eta_extend_star (eta:Eta) (xlist:IdList) (loclist:LocationList) : option Eta :=
 match loclist, xlist with
 | nil, nil        => Some eta
 | loc::t, var::t' => eta_extend_star (Eta_NotMt eta (SomeId var) loc) t' t
 | _, _            => None
 end.

Definition eval_if_then_else (v1:Boolean) (e_t e_f:Expression) :=
 match v1 with
 | true  => e_t
 | false => e_f
 end.

Definition get_method_list (cl:CL) : MethodMap :=
 match cl with
 | ClassDecl _ _ _ methodlist => methodlist
 end.

Definition get_field_list (cl:CL) : FieldTypeMap :=
 match cl with
 | ClassDecl _ _ fieldlist _ => fieldlist
 end.

Definition method_lookup (m:M) (cl:CL) : option Method := HashMap.find m (get_method_list cl).

Fixpoint get_class_with_virtual_method (m:M) (classlist:list CL) : option CL :=
 match classlist with
 | nil   => None
 | cl::t => match method_lookup m cl with
            | Some method => Some cl
            | None        => get_class_with_virtual_method m t
            end
 end.

Fixpoint get_virtual_method (m:M) (classlist:list CL) : option Method :=
 match (get_class_with_virtual_method m classlist) with
 | None    => None
 | Some cl => method_lookup m cl
 end.

Definition get_fields_of_parents_and_self_from_list (cllist:list CL) : list FieldTypeMap :=
 map (fun cl => (get_field_list cl)) cllist.

Definition get_fields_of_parents_and_self_from_CL (cl:CL) (mu:Mu) : list FieldTypeMap :=
 get_fields_of_parents_and_self_from_list (get_class_hierarchy_CL_to_CLList (HashMap.cardinal mu) cl mu).

Definition get_fields_of_parents_and_self_C (c:C) (mu:Mu) : list FieldTypeMap :=
 match (convert_C_to_CL c mu) with
 | None    => nil
 | Some cl => get_fields_of_parents_and_self_from_CL cl mu
 end.

Definition get_type_list_unordered (fl:FieldTypeMap) : list T :=
 map (fun fl => snd fl) (HashMap.elements fl).

Definition get_hierarchical_type_map (hfm:list FieldTypeMap) : list FieldTypeMap := hfm.

Definition get_default_value (t:T) : V :=
 match t with
 | T_Class _ => V_Pointer Null
 | T_Unit    => V_Unit
 | T_Bool    => V_Bool false
 end.

Fixpoint create_default_values_hash_map elems : HashMap.t V :=
 match elems with
 | nil  => HashMap.empty V
 | h::t => match h with
           | (field, type) => HashMap.add field (get_default_value type) (create_default_values_hash_map t)
           end
 end.

Definition get_default_values (ftm:FieldTypeMap) : FieldValueMap :=
 create_default_values_hash_map (HashMap.elements ftm).

Definition get_hierarchical_default_values (htl:list FieldTypeMap) : list FieldValueMap :=
 map (fun tm => (get_default_values tm)) htl.

Definition make_heap_pointer (loc:Location) (c:C) := (Hv_v (V_Pointer (Addr loc c))).

Definition argument_list_to_XList (arglist:ArgumentList) : IdList :=
 map (fun vardec => get_variable_name vardec) arglist.

Definition get_field_ids (ftm:FieldTypeMap) : list id :=
 map (fun el => fst el) (HashMap.elements ftm).

Definition create_field_location_pairs (ftm:FieldTypeMap)
                                       (loclist:LocationList) : list (id * Location) :=
 (combine (get_field_ids ftm) loclist).

Fixpoint create_field_location_map (pairs: list(id * Location)) : FieldLocationMap :=
 match pairs with
 | nil => HashMap.empty Location
 | (x, loc)::t => HashMap.add x loc (create_field_location_map t)
 end.

Fixpoint build_class_loc_lists_helper (arg:list (C * (FieldTypeMap * LocationList)))
 : ClassToFieldLocationsMap :=
 match arg with
 | nil  => HashMap.empty FieldLocationMap
 | ((SomeClass c), (ftm, loclist))::t => HashMap.add c
                                         (create_field_location_map (create_field_location_pairs ftm loclist))
                                         (build_class_loc_lists_helper t)
 end.

(* "New" helpers *)
Definition build_class_loc_lists (hcl:CList)
                                 (hfl:list FieldTypeMap)
                                 (hl:list LocationList) : ClassToFieldLocationsMap :=
 if (beq_nat (length hfl) (length hl)) then
     let fields_and_locations := (combine hfl hl) in
       (if (beq_nat (length hcl) (length fields_and_locations)) then
           build_class_loc_lists_helper (combine hcl fields_and_locations)
        else HashMap.empty FieldLocationMap)
 else
     HashMap.empty FieldLocationMap.

Definition get_required_heap_space (l:list nat) : nat := fold_left plus l 0.

Fixpoint partition_list (the_list:list Location) (element_lengths: list nat) : list LocationList :=
 if beq_nat (length the_list) (get_required_heap_space element_lengths) then
  match element_lengths, the_list with
  | len::t, h::t' => (firstn len the_list) :: partition_list (skipn len the_list) t
  | _, _ => nil
  end
 else nil.

Definition h_malloc_n_star (h:H) (l:list nat) : list LocationList :=
 match l with
 | nil  => nil
 | _    => partition_list (h_malloc_n h (get_required_heap_space l)) l
 end.

Definition get_value_lengths (hfvm:list FieldValueMap) : list nat :=
 map (fun fvm => HashMap.cardinal fvm) hfvm.

Definition inject (prog : P) : State :=
 match prog with
 | Program mu entrypoint =>
    match entrypoint with
    | EntryPoint c m => (StateCons mu (HashMap.empty Hv) Eta_mt (MethodInvocation (NewClass c) m nil) K_Return)
    end
 end.

Definition inject_with_state (s:State) (m:M) : State :=
 match s with
 | StateCons mu h eta e k => (StateCons mu h eta (MethodInvocation e m nil) K_Return)
 end.

(* -------------------------------------------------------------------------- *)
(* ------------------------- Expression Reductions -------------------------- *)
(* -------------------------------------------------------------------------- *)

(* TODO Verify/cross-check all these rules, including ensuring eta has no double entries *)
Inductive ExprReduces : State -> State -> Prop :=

 (* ------------------------------------------------------------------------- *)
 (* Variable Access *)

 | ER_VariableAccess :
  forall (x:X) (mu:Mu) (h:H) (eta:Eta) (k:Continuation) (l:Location) (hv:Hv),
   (eta_lookup eta x) = Some l ->
   (h_lookup h l)     = Some hv ->
   ExprReduces (StateCons mu h eta (Expr_X x) k)
               (StateCons mu h eta (Expr_V (Hv_To_V l hv)) k)

 (* ------------------------------------------------------------------------- *)
 (* Field Access - Object Eval *)

 | ER_FieldAccess1 :
  forall (mu:Mu) (h:H) (eta:Eta) (e:Expression) (f:F) (k:Continuation),
   ExprReduces (StateCons mu h eta (FieldRef e f) k)
               (StateCons mu h eta e (K_FieldAccess f k))

 (* Field access *)

 | ER_FieldAccess2 :
  forall mu h eta loc C f1 k v1 object obj loc_0,
   (h_lookup h loc)            = Some (Hv_object obj) ->
   (cast obj C)                = Some object          ->
   (field_lookup object C f1 mu) = Some loc_0           ->
   (h_lookup h loc_0)          = Some (Hv_v v1)       ->
   ExprReduces (StateCons mu h eta (Expr_V (V_Pointer (Addr loc C))) (K_FieldAccess f1 k))
               (StateCons mu h eta (Expr_V v1) k)

 (* ------------------------------------------------------------------------- *)
 (* Equals '==': l-operand eval *)

 | ER_Equals1 :
  forall (mu:Mu) (h:H) (eta:Eta) (e_0 e:Expression) (k:Continuation),
   ExprReduces (StateCons mu h eta (Equality e_0 e) k)
               (StateCons mu h eta e_0 (K_EqualityLeftOperand e k))

 (* Equals '==': r-operand eval *)

 | ER_Equals2 :
  forall (mu:Mu) (h:H) (eta:Eta) (e:Expression) (v:V) (k:Continuation),
   ExprReduces (StateCons mu h eta (Expr_V v) (K_EqualityLeftOperand e k))
               (StateCons mu h eta e (K_EqualityRightOperand v k))

 (* Equals '==': equals *)

 | ER_Equals3 :
  forall (mu:Mu) (h:H) (eta:Eta) (v_0 v_1:V) (k:Continuation),
   ExprReduces (StateCons mu h eta (Expr_V v_0) (K_EqualityRightOperand v_1 k))
               (StateCons mu h eta (convert_to_boolean_expr (V_equals v_0 v_1)) k)

 (* ------------------------------------------------------------------------- *)
 (* Typecast - Object eval *)

 | ER_Typecast1 :
  forall (mu:Mu) (h:H) (eta:Eta) (e:Expression) (c:C) (k:Continuation),
   ExprReduces (StateCons mu h eta (Cast c e) k)
               (StateCons mu h eta e (K_Cast c k))

 (* Typecast *)

 | ER_Typecast2 :
  forall (mu:Mu) (h:H) (eta:Eta) (c_0 c_1:C) (loc:Location) (object:HeapObject) (k:Continuation),
   (h_lookup h loc)      = Some (Hv_object object) ->
   (can_cast object c_1) = true ->
   ExprReduces (StateCons mu h eta (convert_pointer_to_expr (Addr loc c_0)) (K_Cast c_1 k))
               (StateCons mu h eta (convert_pointer_to_expr (Addr loc c_1)) k)

 (* ------------------------------------------------------------------------- *)
 (* Assign - Object eval *)

 | ER_Assign1 :
  forall (mu:Mu) (h:H) (eta:Eta) (e:Expression) (x:X) (k:Continuation),
   ExprReduces (StateCons mu h eta (VarAssign x e) k)
               (StateCons mu h eta e (K_VarAssign x k))

 (* Assign *)

 | ER_Assign2 :
  forall (mu:Mu) (h h_0:H) (eta:Eta) (v:V) (loc:Location) (x:X) (k:Continuation),
   (eta_lookup eta x)        = Some loc ->
   (h_extend h loc (Hv_v v)) = h_0 ->
   ExprReduces (StateCons mu h eta (Expr_V v) (K_VarAssign x k))
               (StateCons mu h_0 eta (Expr_V v) k)

 (* ------------------------------------------------------------------------- *)
 (* Assign Field - Object eval *)

 | ER_AssignField1 :
  forall (mu:Mu) (h:H) (eta:Eta) (e:Expression) (x:X) (f:F) (k:Continuation),
   ExprReduces (StateCons mu h eta (FieldAssign x f e) k)
               (StateCons mu h eta e (K_FieldAssign x f k))

 (* Assign Field *)

 | ER_AssignField2 :
  forall (mu:Mu) (h h_0:H) (eta:Eta) (x:X) (f:F) (c:C) (v:V)
         (loc_0 loc_1 loc_2:Location) (obj object:HeapObject) (k:Continuation),
   (eta_lookup eta x)                = Some loc_0  ->
   (h_lookup h loc_0)                = Some (Hv_v (V_Pointer (Addr loc_1 c))) ->
   (h_lookup h loc_1)                = Some (Hv_object obj) ->
   (cast obj c)                      = Some object ->
   (field_lookup object c f mu)      = Some loc_2  ->
   (h_extend h loc_2 (Hv_v v))       = h_0 ->
   ExprReduces (StateCons mu h eta (Expr_V v) (K_FieldAssign x f k))
               (StateCons mu h_0 eta (Expr_V v) k)

 (* ------------------------------------------------------------------------- *)
 (* Pop eta (close scope) *)

 | ER_PopEta :
  forall (mu:Mu) (h:H) (eta eta_0:Eta) (v:V) (k:Continuation),
   ExprReduces (StateCons mu h eta (Expr_V v) (K_Pop eta_0 k))
               (StateCons mu h eta_0 (Expr_V v) k)

 (* ------------------------------------------------------------------------- *)
 (* Begin - Empty expression list *)

 | ER_BeginEmptyExpList :
  forall (mu:Mu) (h:H) (eta:Eta) (k:Continuation),
   ExprReduces (StateCons mu h eta VoidExp k)
               (StateCons mu h eta (Expr_V V_Unit) k)

 (* Begin - e_0 evaluation *)

 | ER_Begin_e_0_evaluation :
  forall (mu:Mu) (h:H) (eta:Eta) (k:Continuation) (e_0 e_1:Expression),
   ExprReduces (StateCons mu h eta (SeqExp e_0 e_1) k)
               (StateCons mu h eta e_0 (K_Seq e_1 k))

 (* Begin - e_1 evaluation *)

 | ER_Begin_e_1_evaluation :
  forall (mu:Mu) (h:H) (eta:Eta) (v:V) (k:Continuation) (e_1:Expression),
   ExprReduces (StateCons mu h eta (Expr_V v) (K_Seq e_1 k))
               (StateCons mu h eta e_1 k)

 (* ------------------------------------------------------------------------- *)
 (* Instanceof - object eval *)

 | ER_InstanceOf1 :
  forall (mu:Mu) (h:H) (eta:Eta) (e:Expression) (c:C) (k:Continuation),
   ExprReduces (StateCons mu h eta (InstanceOf e c) k)
               (StateCons mu h eta e (K_InstanceOf c k))

 (* Instanceof *)

 | ER_InstanceOf2 :
  forall (mu:Mu) (h:H) (eta:Eta) (c_0 c_1:C) (v_res:Boolean) (k:Continuation)
         (loc:Location) (object:HeapObject),
   (h_lookup h loc)      = Some (Hv_object object) ->
   (can_cast object c_1) = v_res ->
   ExprReduces (StateCons mu h eta (convert_pointer_to_expr (Addr loc c_0)) (K_InstanceOf c_1 k))
               (StateCons mu h eta (convert_to_boolean_expr v_res) k)

 (* ------------------------------------------------------------------------- *)
 (* Variable declaration - object eval *)

 | ER_VarDec1 :
  forall (mu:Mu) (h:H) (eta:Eta) (e_0 e_1:Expression) (x1:id) (t:T) (k:Continuation),
   ExprReduces (StateCons mu h eta (VarDecExp (VarDec x1 t) e_0 e_1) k)
               (StateCons mu h eta e_0 (K_VarAssignIn t (SomeId x1) e_1 k))

 (* Variable declaration *)

 | ER_VarDec2 :
  forall (mu:Mu) (h h_0:H) (eta eta_0:Eta) (v:V) (e_1:Expression) (x1:id) (t:T) (k:Continuation) (loc_x:Location),
   (h_malloc h)                            = loc_x ->
   (h_extend h loc_x (Hv_v v))             = h_0   ->
   (eta_extend eta (SomeId x1) loc_x)      = eta_0 ->
   ExprReduces (StateCons mu h eta (Expr_V v) (K_VarAssignIn t (SomeId x1) e_1 k))
               (StateCons mu h_0 eta_0 e_1 (K_Pop eta k))

 (* ------------------------------------------------------------------------- *)
 (* If-then-else - object eval *)

 | ER_IfThenElseObjectEval :
  forall (mu:Mu) (h:H) (eta:Eta) (e_p e_t e_f:Expression) (k:Continuation),
   ExprReduces (StateCons mu h eta (IfExpr e_p e_t e_f) k)
               (StateCons mu h eta e_p (K_If e_t e_f k))

 (* If-then-else *)

 | ER_IfThenElse :
  forall (mu:Mu) (h:H) (eta:Eta) (v1:Boolean) (e_t e_f:Expression) (k:Continuation),
   ExprReduces (StateCons mu h eta (convert_to_boolean_expr v1) (K_If e_t e_f k))
               (StateCons mu h eta (eval_if_then_else v1 e_t e_f) k)

 (* ------------------------------------------------------------------------- *)
 (* Method invocation - object eval *)

 | ER_MethodInvocationObjectEval :
  forall (mu:Mu) (h:H) (eta:Eta) (e_0:Expression) (args:list X) (m:M) (k:Continuation),
   ExprReduces (StateCons mu h eta (MethodInvocation e_0 m args) k)
               (StateCons mu h eta e_0 (K_MethodInvocation m args k))

 (* Method invocation *)

 | ER_MethodInvocation :
  forall (mu:Mu) (h:H) (eta:Eta) (pv_o:Pointer) (m:M) (k:Continuation) (args:list X) (primitive_args:list V),
   (lookup_arguments h eta args) = primitive_args ->
   ExprReduces (StateCons mu h eta (Expr_V (V_Pointer pv_o)) (K_MethodInvocation m args k))
               (StateCons mu h eta (Raw pv_o m primitive_args) k)

 (* Raw method invocation - there are a couple of Redex tests that can easily break this like setting
    only Object as the rv from class-list-from-object *)

 | ER_MethodInvocationRaw :
  forall (mu:Mu) (h h_0 h_tmp:H) (eta eta_0:Eta) (e_m:Expression) (k:Continuation)
         (m:M) (varlist:list V) (c C_t:C) (loc loc_o:Location) (loclist:LocationList)
         (methodvars:IdList) (obj1:HeapObject) (arglist:ArgumentList) (t:T)
         (classlist:CLList) (CL_t:CL),
   (h_lookup h loc)                 = Some (Hv_object obj1) ->
   (class_decls_of_parents_and_self c mu)      = Some classlist ->

   (get_class_with_virtual_method m classlist) = Some CL_t ->
   (convert_CL_to_C CL_t)                      = C_t       ->
   (method_lookup m CL_t)                      = Some (AMethod m t arglist e_m) ->
   (argument_list_to_XList arglist)            = methodvars ->

   (* allocate locations for "this" and the arguments *)
   (h_malloc_n h (S (length varlist)))         = (loc_o::loclist) ->

   (* write "this" and the args into the heap. loclist and varlist must be the same length. *)
   (h_extend h loc_o (make_heap_pointer loc C_t)) = h_tmp   ->
   (h_extend_star h_tmp loclist varlist)          = Some h_0 ->

   (* create a new local environment with the bindings for "this" and args *)
   (eta_extend_star (eta_extend eta This loc_o) methodvars loclist) = Some eta_0 ->

   ExprReduces (StateCons mu h eta (Raw (Addr loc c) m varlist) k)
               (StateCons mu h_0 eta_0 e_m (K_Pop eta k))

 (* ------------------------------------------------------------------------- *)
 (* New *)

 | ER_New :
  forall (mu:Mu) (h h_0 h_1:H) (eta:Eta) (c:C) (loc_1:Location)
         (k                        : Continuation)
         (classlist                : CList)
         (defaultvalues            : list FieldValueMap)
         (hierarchicalfieldlist    : list FieldTypeMap)
         (hierarchicaltypelist     : list FieldTypeMap)
         (hierarchicallocations    : list LocationList)
         (listofclassfieldloclists : ClassToFieldLocationsMap)
         (hierarchicalfieldlocmap  : list FieldLocationMap),

   (classes_of_parents_and_self c mu)                     = Some classlist        -> (* Must be hierarchical *)
   (beq_nat O (length classlist))                         = false                 -> (* XXX Check Redex Model for this case *)
   (get_fields_of_parents_and_self_C c mu)                = hierarchicalfieldlist ->
   (get_hierarchical_type_map hierarchicalfieldlist)      = hierarchicaltypelist  ->
   (get_hierarchical_default_values hierarchicaltypelist) = defaultvalues         ->

   (h_malloc_n_star h (get_value_lengths defaultvalues))  = hierarchicallocations ->
   (create_hierarchical_field_location_map hierarchicallocations defaultvalues)  = hierarchicalfieldlocmap  ->
   (h_extend_star_hierarchical_map h hierarchicalfieldlocmap defaultvalues)      = Some h_0 -> (* XXX Ensure h_0 != nil *)

   (h_malloc h_0)                                                                = loc_1  ->
   (build_class_loc_lists classlist hierarchicalfieldlist hierarchicallocations) = listofclassfieldloclists ->
   (h_extend h_0 loc_1 (Hv_object (HeapObj listofclassfieldloclists)))           = h_1 ->

   ExprReduces (StateCons mu h eta (NewClass c) k)
               (StateCons mu h_1 eta (convert_pointer_to_expr (Addr loc_1 c)) k).

Hint Constructors ExprReduces.

Require Import Coq.Sets.Relations_1.
Definition ExprReducesTransitive := Transitive ExprReduces.

Theorem ExprReduces_fun:
 forall (s s' s'':State),
  ExprReduces s s' ->
  ExprReduces s s'' ->
  s' = s''.
Proof.
 intros.
 destruct s.

 inversion H0; inversion H1; try congruence || (subst; discriminate).

 subst.
 inversion H14.
 inversion H15.
 reflexivity.

 subst.
 inversion H15.
 inversion H14.
 congruence.

 subst.
 inversion H12.
 inversion H13.
 reflexivity.
Qed.

Axiom MethodLookupSoundness:
 forall (cl:CL) (e:Expression) (arglist:ArgumentList) (t:T) (m1 m2:M),
  (method_lookup m1 cl) = Some (AMethod m2 t arglist e) -> m1 = m2.

(* Might not need ExprReduces_fun *)
Theorem ExprReduces_dec:
 forall (s:State),
  { s' | ExprReduces s s' } + { forall s', ~ ExprReduces s s' }.
Proof.
 intros. destruct s. generalize m h e c. clear m h e c.
 rename e0 into x.

 Ltac dispatch_invalid_state := right; intuition; inversion_clear H0.
 Ltac dispatch_invalid_state_with_congruence := right; intuition; inversion_clear H0; congruence.

 induction x.

 (* Expr_X *)
 intros.
 remember (eta_lookup e x) as eta_lookup_e_x.
 destruct eta_lookup_e_x.
 remember (h_lookup h l) as h_lookup_h_l.
 destruct h_lookup_h_l.

 left.
 exists (StateCons m h e (Expr_V (Hv_To_V l h0)) c).
 apply (ER_VariableAccess x m h e c l h0); symmetry; assumption.

 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.

 (* Expr_V *)
 intros.
 destruct c.

 (** K_Return is not a valid continuation *)
 dispatch_invalid_state.

 (** K_FieldAccess *)
 destruct v.
 destruct p as [loc|].
 remember (h_lookup h loc) as h_lookup_h_loc.
 destruct h_lookup_h_loc.
 destruct h0 as [hv|obj].

 (** h_lookup h loc must return an object *)
 dispatch_invalid_state_with_congruence.

 remember (cast obj c0) as cast_obj_c0.
 destruct cast_obj_c0 as [object|].
 remember (field_lookup object c0 f m) as field_lookup_object_f_mu.
 destruct field_lookup_object_f_mu as [loc_0|].
 remember (h_lookup h loc_0) as h_lookup_h_loc_0.
 destruct h_lookup_h_loc_0 as [hv|].
 destruct hv.

 left.
 exists (StateCons m h e (Expr_V v) c).
 apply (ER_FieldAccess2 m h e loc c0 f c v object obj loc_0); symmetry; assumption.

 (** (h_lookup h loc_0) must be (Hv_v v) *)
 dispatch_invalid_state_with_congruence.

 (** (h_lookup h loc_0) must be (Hv_v v) *)
 dispatch_invalid_state_with_congruence.

 (** (field_lookup object f1 mu) must be (Some loc_0) *)
 dispatch_invalid_state_with_congruence.

 (** (cast obj C) must be Some object *)
 dispatch_invalid_state_with_congruence.

 (** (h_lookup h loc) must be Some ... *)
 dispatch_invalid_state_with_congruence.

 (** Null pointers can't be used for field access *)
 dispatch_invalid_state_with_congruence.

 (** Only pointers can be used for field access *)
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.

 (** K_MethodInvocation *)
 destruct v.
 left.
 exists (StateCons m h e (Raw p m0 (lookup_arguments h e l)) c).
 apply ER_MethodInvocation.
 reflexivity.

 (** Only pointers can be used for method invocation *)
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.

 (** K_EqualityLeftOperand *)
 left.
 exists (StateCons m h e e0 (K_EqualityRightOperand v c)).
 apply ER_Equals2.

 (** K_EqualityRightOperand *)
 left.
 exists (StateCons m h e (convert_to_boolean_expr (V_equals v v0)) c).
 apply ER_Equals3.

 (** K_Cast *)
 destruct v.
 destruct p as [loc|].
 remember (h_lookup h loc) as h_lookup_h_loc.
 destruct h_lookup_h_loc as [hl|].
 destruct hl as [hv|object].

 (*** h_lookup h loc must be Some heap object *)
 dispatch_invalid_state_with_congruence.

 remember (can_cast object c) as can_cast.
 destruct can_cast.
 left.
 exists (StateCons m h e (Expr_V (V_Pointer (Addr loc c))) c0).
 apply ER_Typecast2 with object.
 symmetry. apply Heqh_lookup_h_loc.
 symmetry. apply Heqcan_cast.

 (*** can_cast should be true *)
 dispatch_invalid_state_with_congruence.

 (*** h_lookup should be Some ... *)
 dispatch_invalid_state_with_congruence.

 (*** XXX Null pointer cannot be used for casting - do we need to allow this? *)
 dispatch_invalid_state_with_congruence.

 (*** Only pointers can be used for casting *)
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.

 (** K_InstanceOf *)
 destruct v.
 destruct p as [loc|].
 remember (h_lookup h loc) as h_lookup_h_loc.
 destruct h_lookup_h_loc as [hl|].
 destruct hl as [hv|object].

 (*** h_lookup h loc must be Some heap object *)
 dispatch_invalid_state_with_congruence.

 remember (can_cast object c) as can_cast_object.
 left.
 exists (StateCons m h e (convert_to_boolean_expr can_cast_object) c0).
 apply ER_InstanceOf2 with object.
 symmetry. apply Heqh_lookup_h_loc.
 symmetry. apply Heqcan_cast_object.

 (*** h_lookup h loc must be Some heap object *)
 dispatch_invalid_state_with_congruence.

 (*** XXX Null pointer cannot be used for instanceof - do we need to allow this? *)
 dispatch_invalid_state_with_congruence.

 (*** Only pointers can be used for instanceof *)
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.

 (** K_VarAssign *)
 remember (eta_lookup e x) as elex.
 destruct elex as [loc|].
 remember (h_extend h loc (Hv_v v)) as extendedH.

 left.
 exists (StateCons m extendedH e (Expr_V v) c).
 apply ER_Assign2 with loc.
 symmetry. apply Heqelex.
 symmetry. apply HeqextendedH.

 (*** eta_lookup must be Some ... *)
 dispatch_invalid_state_with_congruence.

 (** K_FieldAssign *)
 remember (eta_lookup e x) as elex.
 destruct elex as [loc_0|].
 remember (h_lookup h loc_0) as hlhl0.
 destruct hlhl0 as [heapthing|].
 destruct heapthing as [hv|heapobj].
 destruct hv.
 destruct p as [loc_1|].
 remember (h_lookup h loc_1) as hlhl1.
 destruct hlhl1 as [heapthing|].
 destruct heapthing as [hv|obj].

 (*** h_lookup h loc must be Some heap object *)
 dispatch_invalid_state_with_congruence.

 remember (cast obj c0) as cast_obj_c.
 destruct cast_obj_c as [object|].
 remember (field_lookup object c0 f m) as flofm.
 destruct flofm as [loc_2|].
 remember (h_extend h loc_2 (Hv_v v)) as h_0.

 left.
 exists (StateCons m h_0 e (Expr_V v) c).
 apply (ER_AssignField2 m h h_0 e x f c0 v loc_0 loc_1 loc_2 obj object); symmetry; assumption.

 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.

 (** K_If *)
 destruct v.
 dispatch_invalid_state_with_congruence.
 left.
 exists (StateCons m h e (eval_if_then_else b e0 e1) c).
 apply ER_IfThenElse.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.

 (** K_VarAssignIn *)
 remember (h_malloc h) as loc_x.
 remember (h_extend h loc_x (Hv_v v)) as h_0.
 destruct x as [|x1].
 dispatch_invalid_state_with_congruence.
 remember (eta_extend e (SomeId x1) loc_x) as eta_0.

 left.
 exists (StateCons m h_0 eta_0 e0 (K_Pop e c)).
 apply ER_VarDec2 with loc_x.
 symmetry. apply Heqloc_x.
 symmetry. apply Heqh_0.
 symmetry. apply Heqeta_0.

 (** K_Seq *)
 left.
 exists (StateCons m h e e0 c).
 apply ER_Begin_e_1_evaluation.

 (** K_Pop *)
 left.
 exists (StateCons m h e0 (Expr_V v) c).
 apply ER_PopEta.

 (* NewClass *)
 intros.
 remember (classes_of_parents_and_self c m) as option_classlist.
 destruct option_classlist as [classlist|].
 remember (get_fields_of_parents_and_self_C c m) as hierarchicalfieldlist.
 remember (get_hierarchical_type_map hierarchicalfieldlist) as hierarchicaltypelist.
 remember (get_hierarchical_default_values hierarchicaltypelist) as defaultvalues.
 remember (h_malloc_n_star h (get_value_lengths defaultvalues)) as hierarchicallocations.
 remember (create_hierarchical_field_location_map hierarchicallocations defaultvalues) as hierarchicalfieldlocmap.
 remember (h_extend_star_hierarchical_map h hierarchicalfieldlocmap defaultvalues) as option_h_0.
 destruct option_h_0 as [h_0|].
 remember (h_malloc h_0) as loc_1.
 remember (build_class_loc_lists classlist hierarchicalfieldlist hierarchicallocations) as listofclassfieldloclists.
 remember (h_extend h_0 loc_1 (Hv_object (HeapObj listofclassfieldloclists))) as h_1.
 remember (beq_nat O (length classlist)) as nonempty_classlist.
 destruct nonempty_classlist.
 dispatch_invalid_state_with_congruence.

 left.
 exists (StateCons m h_1 e (convert_pointer_to_expr (Addr loc_1 c)) c0).
 apply (ER_New m h h_0 h_1 e c loc_1 c0 classlist
               defaultvalues hierarchicalfieldlist hierarchicaltypelist hierarchicallocations
               listofclassfieldloclists hierarchicalfieldlocmap); symmetry; assumption.

 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.

 (* FieldRef *)
 left.
 exists (StateCons m h e x (K_FieldAccess f c)).
 apply ER_FieldAccess1.

 (* MethodInvocation *)
 left.
 exists (StateCons m0 h e x (K_MethodInvocation m l c)).
 apply ER_MethodInvocationObjectEval.

 (* Raw *)
 intros.
 destruct p as [loc|].
 remember (h_lookup h loc) as hlhl.
 destruct hlhl as [heapthing|].
 destruct heapthing as [hv|obj1].

 dispatch_invalid_state_with_congruence.

 remember (class_decls_of_parents_and_self c0 m0) as optionclasslist.
 destruct optionclasslist as [classlist|].
 remember (get_class_with_virtual_method m classlist) as optionCL_t.

 destruct optionCL_t as [CL_t|].
 remember (convert_CL_to_C CL_t) as C_t.
 remember (method_lookup m CL_t) as optionAMethod.

 destruct optionAMethod as [someAMethod|].
 destruct someAMethod.
 remember (argument_list_to_XList a) as methodvars.
 remember (h_malloc_n h (S (length l))) as loclist.

 destruct loclist as [|loc_o].
 dispatch_invalid_state_with_congruence.

 remember (h_extend h loc_o (make_heap_pointer loc C_t)) as h_tmp.
 remember (h_extend_star h_tmp loclist l) as optionH_0.

 destruct optionH_0 as [h_0|].
 remember (eta_extend_star (eta_extend e This loc_o) methodvars loclist) as optionEta_0.

 destruct optionEta_0 as [eta_0|].

 left.
 exists (StateCons m0 h_0 eta_0 e0 (K_Pop e c)).
 apply (ER_MethodInvocationRaw m0 h h_0 h_tmp e eta_0 e0 c m l c0 C_t
                               loc loc_o loclist methodvars obj1 a t
                               classlist CL_t); try congruence.

 symmetry in HeqoptionAMethod.
 assert (m = m1) as H_same_method.
 apply MethodLookupSoundness in HeqoptionAMethod.
 exact HeqoptionAMethod.
 rewrite <- H_same_method in HeqoptionAMethod.
 apply HeqoptionAMethod.

 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.
 dispatch_invalid_state_with_congruence.

 (* Equality *)
 left.
 exists (StateCons m h e x1 (K_EqualityLeftOperand x2 c)).
 apply ER_Equals1.

 (* Cast *)
 left.
 exists (StateCons m h e x (K_Cast c c0)).
 apply ER_Typecast1.

 (* InstanceOf *)
 left.
 exists (StateCons m h e x (K_InstanceOf c c0)).
 apply ER_InstanceOf1.

 (* VarAssign *)
 left.
 exists (StateCons m h e x0 (K_VarAssign x c)).
 apply ER_Assign1.

 (* FieldAssign *)
 left.
 exists (StateCons m h e x0 (K_FieldAssign x f c)).
 apply ER_AssignField1.

 (* IfExpr *)
 left.
 exists (StateCons m h e x1 (K_If x2 x3 c)).
 apply ER_IfThenElseObjectEval.

 (* VarDecExp *)
 left.
 destruct v as [name t].
 exists (StateCons m h e x1 (K_VarAssignIn t (SomeId name) x2 c)).
 apply ER_VarDec1.

 (* VoidExp *)
 left.
 exists (StateCons m h e (Expr_V V_Unit) c).
 apply ER_BeginEmptyExpList.

 (* SeqExp *)
 left.
 exists (StateCons m h e x1 (K_Seq x2 c)).
 apply ER_Begin_e_0_evaluation.
Qed.

Extraction "javalite.ml" ExprReduces_dec.

Theorem ExprReduces_not_reflexive:
 forall (s:State),
  ~ ExprReduces s s.
Proof.
 intuition.
 destruct s.
 induction e0; inversion H0; try congruence.

 absurd (k = k); eauto. rewrite H8 at 1.
 clear - k. induction k; intros H; inversion H.
 eapply IHk. rewrite H1. exact H2.

 absurd (k = k); eauto. rewrite H8 at 1.
 clear - k. induction k; eauto; intros H; inversion H.
 eapply IHk. rewrite H1. exact H2.

 absurd (k = k); eauto. rewrite H8 at 1.
 clear - k. induction k; eauto; intros H; inversion H.
 eapply IHk. rewrite H1. exact H2.

 absurd (k = k); eauto. rewrite H8 at 1.
 clear - k. induction k; eauto; intros H; inversion H.
 eapply IHk. rewrite H1. exact H2.

 absurd (k = k); eauto. rewrite H7 at 1.
 clear - k. induction k; eauto; intros H; inversion H.
 eapply IHk. rewrite H1. rewrite H2. exact H3.

 absurd (k = k); eauto. rewrite H8 at 1.
 clear - k. induction k; eauto; intros H; inversion H.
 eapply IHk. rewrite H1. exact H2.

 absurd (k = k); eauto. rewrite H8 at 1.
 clear - k. induction k; eauto; intros H; inversion H.
 eapply IHk. rewrite H1. rewrite <- H1. exact H2.

 absurd (k = k); eauto. rewrite H8 at 1.
 clear - k. induction k; eauto; intros H; inversion H.
 eapply IHk. rewrite H1. rewrite H2. exact H3.

 absurd (k = k); eauto. rewrite <- H7 in H11. rewrite <- H11 at 1.
 clear - k. induction k; eauto; intros H; inversion H.
 eapply IHk. rewrite H1. exact H2.
Qed.

(*
TODO:

1. Use an infinite stream (http://coq.inria.fr/stdlib/Coq.Lists.Streams.html) for
   proving properties about the "runner".

2. Create a program for converting S-Expressions to runnable ML Javalite expressions
*)

(* ========================================================================== *)
(* The Church numerals example *)

(* Note: There is a bug/syntax error in the generation of the last member of a sequence expression, VoidExp must not be included *)

(* Classes *)
Definition __class__LambdaTerm        := (P_of_succ_nat 1).
Definition __class__Function          := (P_of_succ_nat 2).
Definition __class__Abstraction       := (P_of_succ_nat 3).
Definition __class__Application       := (P_of_succ_nat 4).
Definition __class__SetIfNotZero      := (P_of_succ_nat 5).
Definition __class__Variable          := (P_of_succ_nat 6).
Definition __class__Church            := (P_of_succ_nat 7).
Definition __class__ChurchTest        := (P_of_succ_nat 8).

(* Fields *)
Definition __field__Abstraction__t    := (P_of_succ_nat 10).
Definition __field__Abstraction__f    := (P_of_succ_nat 11).
Definition __field__Abstraction__x    := (P_of_succ_nat 12).

Definition __field__Application__s    := (P_of_succ_nat 13).
Definition __field__Application__t    := (P_of_succ_nat 14).

Definition __field__SetIfNotZero__x   := (P_of_succ_nat 15).
Definition __field__SetIfNotZero__y   := (P_of_succ_nat 16).
Definition __field__SetIfNotZero__bam := (P_of_succ_nat 17).
Definition __field__Variable__fix     := (P_of_succ_nat 18).

Definition __field__Church__x         := (P_of_succ_nat 19).
Definition __field__Church__f         := (P_of_succ_nat 20).
Definition __field__Church__m         := (P_of_succ_nat 21).
Definition __field__Church__n         := (P_of_succ_nat 22).
Definition __field__Church__g         := (P_of_succ_nat 23).
Definition __field__Church__h         := (P_of_succ_nat 24).
Definition __field__Church__u         := (P_of_succ_nat 25).
Definition __field__Church__zero      := (P_of_succ_nat 26).
Definition __field__Church__one       := (P_of_succ_nat 27).
Definition __field__Church__two       := (P_of_succ_nat 28).
Definition __field__Church__plus      := (P_of_succ_nat 29).
Definition __field__Church__succ      := (P_of_succ_nat 30).
Definition __field__Church__mult      := (P_of_succ_nat 31).
Definition __field__Church__exp       := (P_of_succ_nat 32).

Definition __field__ChurchTest__instance := (P_of_succ_nat 33).
Definition __field__ChurchTest__two   := (P_of_succ_nat 34).
Definition __field__ChurchTest__three := (P_of_succ_nat 35).
Definition __field__ChurchTest__five  := (P_of_succ_nat 36).
Definition __field__ChurchTest__sinz  := (P_of_succ_nat 37).

(* Methods *)
(* XXX These methods should be defined in LambdaTerm (in the Redex model) since
       we implement virtual methods
*)
Definition __method__LambdaTerm__ar        := (P_of_succ_nat 40).
Definition __method__LambdaTerm__cas       := (P_of_succ_nat 41).
Definition __method__LambdaTerm__eval      := (P_of_succ_nat 42).
Definition __method__LambdaTerm__isAe      := (P_of_succ_nat 43).
Definition __method__LambdaTerm__isFree    := (P_of_succ_nat 44).
Definition __method__Function__eval        := (P_of_succ_nat 45).

Definition __method__Abstraction__construct_x_t   := (P_of_succ_nat 50).
Definition __method__Abstraction__construct_x_f   := (P_of_succ_nat 51).
Definition __method__Abstraction__construct_x_t_f := (P_of_succ_nat 52).
Definition __method__Abstraction__ar              := __method__LambdaTerm__ar.
Definition __method__Abstraction__cas             := __method__LambdaTerm__cas.
Definition __method__Abstraction__eval            := __method__LambdaTerm__eval.
Definition __method__Abstraction__isAe            := __method__LambdaTerm__isAe.
Definition __method__Abstraction__isFree          := __method__LambdaTerm__isFree.
Definition __method__Abstraction__ar_abstraction  := (P_of_succ_nat 53).
Definition __method__Abstraction__br              := (P_of_succ_nat 54).

Definition __method__Application__construct       := (P_of_succ_nat 55).
Definition __method__Application__ar              := __method__LambdaTerm__ar.
Definition __method__Application__cas             := __method__LambdaTerm__cas.
Definition __method__Application__eval            := __method__LambdaTerm__eval.
Definition __method__Application__isAe            := __method__LambdaTerm__isAe.
Definition __method__Application__isFree          := __method__LambdaTerm__isFree.

Definition __method__SetIfNotZero__construct      := (P_of_succ_nat 56).
Definition __method__SetIfNotZero__doEval         := (P_of_succ_nat 57).
Definition __method__SetIfNotZero__eval           := __method__Function__eval.

Definition __method__Variable__ar                 := __method__LambdaTerm__ar.
Definition __method__Variable__cas                := __method__LambdaTerm__cas.
Definition __method__Variable__isAe               := __method__LambdaTerm__isAe.
Definition __method__Variable__isFree             := __method__LambdaTerm__isFree.
Definition __method__Variable__eval               := __method__LambdaTerm__eval.

Definition __method__Church__construct            := (P_of_succ_nat 60).
Definition __method__Church__zero                 := (P_of_succ_nat 61).
Definition __method__Church__one                  := (P_of_succ_nat 62).
Definition __method__Church__plus                 := (P_of_succ_nat 63).
Definition __method__Church__succ                 := (P_of_succ_nat 64).
Definition __method__Church__mult                 := (P_of_succ_nat 65).
Definition __method__Church__exp                  := (P_of_succ_nat 66).
Definition __method__Church__pred                 := (P_of_succ_nat 67).
Definition __method__Church__minus                := (P_of_succ_nat 68).

Definition __method__ChurchTest__m                := (P_of_succ_nat 70).
Definition __method__ChurchTest__n                := (P_of_succ_nat 71).
Definition __method__ChurchTest__methodInvokeTest := (P_of_succ_nat 72).
Definition __method__ChurchTest__construct        := (P_of_succ_nat 73).
Definition __method__ChurchTest__testZeroJavalite := (P_of_succ_nat 74).
Definition __method__ChurchTest__testNotZeroJavalite              := (P_of_succ_nat 75).
Definition __method__ChurchTest__testJavaliteVariableEquivalence  := (P_of_succ_nat 76).
Definition __method__ChurchTest__testJavaliteVariableEquivalence2 := (P_of_succ_nat 77).

(* Arguments *)
Definition __arg__Abstraction__construct_x_t__x   := (P_of_succ_nat 80).
Definition __arg__Abstraction__construct_x_t__t   := (P_of_succ_nat 81).
Definition __arg__Abstraction__construct_x_f__x   := (P_of_succ_nat 82).
Definition __arg__Abstraction__construct_x_f__f   := (P_of_succ_nat 83).
Definition __arg__Abstraction__construct_x_t_f__x := (P_of_succ_nat 84).
Definition __arg__Abstraction__construct_x_t_f__t := (P_of_succ_nat 85).
Definition __arg__Abstraction__construct_x_t_f__f := (P_of_succ_nat 86).
Definition __arg__Abstraction__cas__x             := (P_of_succ_nat 87).
Definition __arg__Abstraction__cas__r             := (P_of_succ_nat 88).
Definition __arg__Abstraction__isFree__x          := (P_of_succ_nat 89).
Definition __arg__Abstraction__br__s              := (P_of_succ_nat 90).
Definition __arg__Abstraction__ar_abstraction__x  := (P_of_succ_nat 91).
Definition __arg__Abstraction__ar__oldVar         := (P_of_succ_nat 92).
Definition __arg__Abstraction__ar__newVar         := (P_of_succ_nat 93).
Definition __arg__Abstraction__isAe__x            := (P_of_succ_nat 94).

Definition __arg__Application__construct__s       := (P_of_succ_nat 95).
Definition __arg__Application__construct__t       := (P_of_succ_nat 96).
Definition __arg__Application__cas__x             := (P_of_succ_nat 97).
Definition __arg__Application__cas__r             := (P_of_succ_nat 98).
Definition __arg__Application__isFree__x          := (P_of_succ_nat 99).
Definition __arg__Application__ar__oldVar         := (P_of_succ_nat 100).
Definition __arg__Application__ar__newVar         := (P_of_succ_nat 101).
Definition __arg__Application__isAe__x            := (P_of_succ_nat 102).

Definition __arg__SetIfNotZero__doEval__c         := (P_of_succ_nat 103).

Definition __arg__Variable__cas__x                := (P_of_succ_nat 104).
Definition __arg__Variable__cas__r                := (P_of_succ_nat 105).
Definition __arg__Variable__isFree__x             := (P_of_succ_nat 106).
Definition __arg__Variable__ar__oldVar            := (P_of_succ_nat 107).
Definition __arg__Variable__ar__newVar            := (P_of_succ_nat 108).
Definition __arg__Variable__isAe__x               := (P_of_succ_nat 109).

Definition __arg__Church__plus__m                 := (P_of_succ_nat 110).
Definition __arg__Church__plus__n                 := (P_of_succ_nat 111).
Definition __arg__Church__succ__n                 := (P_of_succ_nat 112).
Definition __arg__Church__mult__m                 := (P_of_succ_nat 113).
Definition __arg__Church__mult__n                 := (P_of_succ_nat 114).
Definition __arg__Church__exp__m                  := (P_of_succ_nat 115).
Definition __arg__Church__exp__n                  := (P_of_succ_nat 116).
Definition __arg__Church__pred__n                 := (P_of_succ_nat 117).
Definition __arg__Church__minus__m                := (P_of_succ_nat 118).
Definition __arg__Church__minus__n                := (P_of_succ_nat 119).

Definition __arg__ChurchTest__m__x                := (P_of_succ_nat 120).

(* Locals *)
Definition __local__Abstraction__cas__v             := (P_of_succ_nat 121).
Definition __local__Abstraction__cas__y             := (P_of_succ_nat 122).
Definition __local__Abstraction__cas__z             := (P_of_succ_nat 123).
Definition __local__Abstraction__isFree__v          := (P_of_succ_nat 124).
Definition __local__Abstraction__br__v              := (P_of_succ_nat 125).
Definition __local__Abstraction__ar_abstraction__y  := (P_of_succ_nat 126).
Definition __local__Abstraction__ar__v              := (P_of_succ_nat 127).
Definition __local__Abstraction__ar__y              := (P_of_succ_nat 128).
Definition __local__Abstraction__ar__z              := (P_of_succ_nat 129).
Definition __local__Abstraction__isAe__v            := (P_of_succ_nat 130).
Definition __local__Abstraction__isAe__a            := (P_of_succ_nat 131).

Definition __local__Application__cas__lop           := (P_of_succ_nat 132).
Definition __local__Application__cas__rop           := (P_of_succ_nat 133).
Definition __local__Application__cas__v             := (P_of_succ_nat 134).
Definition __local__Application__isFree__v          := (P_of_succ_nat 135).
Definition __local__Application__isAe__v            := (P_of_succ_nat 136).
Definition __local__Application__isAe__a            := (P_of_succ_nat 137).
Definition __local__Application__eval__lop          := (P_of_succ_nat 138).
Definition __local__Application__eval__rop          := (P_of_succ_nat 139).
Definition __local__Application__eval__v            := (P_of_succ_nat 140).
Definition __local__Application__eval__a            := (P_of_succ_nat 141).

Definition __local__Variable__cas__v                := (P_of_succ_nat 142).
Definition __local__Variable__isFree__v             := (P_of_succ_nat 143).
Definition __local__Variable__ar__v                 := (P_of_succ_nat 144).

Definition __local__ChurchTest__construct__v                        := (P_of_succ_nat 145).
Definition __local__ChurchTest__testZeroJavalite__c                 := (P_of_succ_nat 146).
Definition __local__ChurchTest__testZeroJavalite__s                 := (P_of_succ_nat 147).
Definition __local__ChurchTest__testNotZeroJavalite__c              := (P_of_succ_nat 148).
Definition __local__ChurchTest__testNotZeroJavalite__s              := (P_of_succ_nat 149).
Definition __local__ChurchTest__testJavaliteVariableEquivalence__x  := (P_of_succ_nat 150).
Definition __local__ChurchTest__testJavaliteVariableEquivalence__y  := (P_of_succ_nat 151).
Definition __local__ChurchTest__testJavaliteVariableEquivalence2__x := (P_of_succ_nat 152).
Definition __local__ChurchTest__testJavaliteVariableEquivalence2__y := (P_of_succ_nat 153).

(* Artificial locals - created when converting method invocations to use ANF *)
Definition __local__Abstraction__cas__arg2 := (P_of_succ_nat 154).
Definition __local__Abstraction__cas__arg3 := (P_of_succ_nat 155).
Definition __local__Abstraction__cas__arg4 := __local__Abstraction__cas__arg2.
Definition __local__Abstraction__cas__arg5 := __local__Abstraction__cas__arg3.
Definition __local__Abstraction__br__arg1 := (P_of_succ_nat 156).
Definition __local__Abstraction__ar_abstraction__arg1 := (P_of_succ_nat 157).
Definition __local__Abstraction__ar_abstraction__arg2 := (P_of_succ_nat 158).
Definition __local__Abstraction__ar__arg1   := (P_of_succ_nat 159).
Definition __local__Abstraction__ar__arg2   := (P_of_succ_nat 160).
Definition __local__Abstraction__ar__arg3   := (P_of_succ_nat 161).
Definition __local__Abstraction__isAe__arg1 := (P_of_succ_nat 162).
Definition __local__Abstraction__isAe__arg2 := (P_of_succ_nat 163).
Definition __local__Abstraction__isAe__arg3 := (P_of_succ_nat 164).

Definition __local__Application__ar__t1   := (P_of_succ_nat 165).
Definition __local__Application__ar__t2   := (P_of_succ_nat 166).
Definition __local__Application__isAe__t1 := (P_of_succ_nat 167).
Definition __local__Application__isAe__t2 := (P_of_succ_nat 168).

Definition __local__ChurchTest__methodInvokeTest__arg   := (P_of_succ_nat 169).
Definition __local__ChurchTest__testZeroJavalite__t1    := (P_of_succ_nat 170).
Definition __local__ChurchTest__testNotZeroJavalite__t1 := (P_of_succ_nat 171).

Definition __local__Church__construct__t1    := (P_of_succ_nat 172).
Definition __local__Church__construct__t2    := (P_of_succ_nat 173).
Definition __local__Church__construct__arg1  := (P_of_succ_nat 174).
Definition __local__Church__construct__arg2  := (P_of_succ_nat 175).
Definition __local__Church__construct__arg3  := (P_of_succ_nat 176).
Definition __local__Church__construct__arg4  := (P_of_succ_nat 177).
Definition __local__Church__construct__arg5  := (P_of_succ_nat 178).
Definition __local__Church__construct__arg6  := (P_of_succ_nat 179).
Definition __local__Church__construct__arg7  := (P_of_succ_nat 180).
Definition __local__Church__construct__arg8  := (P_of_succ_nat 181).
Definition __local__Church__construct__arg9  := (P_of_succ_nat 182).
Definition __local__Church__construct__arg10 := (P_of_succ_nat 183).
Definition __local__Church__construct__arg11 := (P_of_succ_nat 184).
Definition __local__Church__construct__arg12 := (P_of_succ_nat 185).
Definition __local__Church__construct__arg13 := (P_of_succ_nat 186).
Definition __local__Church__construct__arg14 := (P_of_succ_nat 187).
Definition __local__Church__construct__arg15 := (P_of_succ_nat 188).
Definition __local__Church__construct__arg16 := (P_of_succ_nat 189).

Definition __local__SetIfNotZero__doEval__t1   := (P_of_succ_nat 190).
Definition __local__SetIfNotZero__doEval__t2   := (P_of_succ_nat 191).
Definition __local__SetIfNotZero__doEval__t3   := (P_of_succ_nat 192).
Definition __local__SetIfNotZero__doEval__arg1 := (P_of_succ_nat 193).
Definition __local__SetIfNotZero__doEval__arg3 := (P_of_succ_nat 194).
Definition __local__SetIfNotZero__doEval__arg4 := (P_of_succ_nat 195).

(* Classes *)
Definition C_Abstraction := (SomeClass __class__Abstraction).
Definition C_Application := (SomeClass __class__Application).
Definition C_Church      := (SomeClass __class__Church).
Definition C_ChurchTest  := (SomeClass __class__ChurchTest).
Definition C_Function    := (SomeClass __class__Function).
Definition C_LambdaTerm  := (SomeClass __class__LambdaTerm).
Definition C_SetIfNotZero:= (SomeClass __class__SetIfNotZero).
Definition C_Variable    := (SomeClass __class__Variable).

Definition METHOD_Abstraction__construct_x_t :=
 (AMethod __method__Abstraction__construct_x_t
          (T_Class C_Abstraction)
          ((VarDec __arg__Abstraction__construct_x_t__x (T_Class C_Variable))::
           (VarDec __arg__Abstraction__construct_x_t__t (T_Class C_LambdaTerm))::
           nil)
          (SeqExp (FieldAssign (This) __field__Abstraction__t (Expr_X (SomeId __arg__Abstraction__construct_x_t__t)))
                  (SeqExp (FieldAssign (This) __field__Abstraction__x (Expr_X (SomeId __arg__Abstraction__construct_x_t__x)))
                          (SeqExp (FieldAssign (This) __field__Abstraction__f (Expr_V (V_Pointer Null)))
                                  (Expr_X (This)))))).

Definition METHOD_Abstraction__construct_x_f :=
 (AMethod __method__Abstraction__construct_x_f
          (T_Class C_Abstraction)
          ((VarDec __arg__Abstraction__construct_x_f__x (T_Class C_Variable))::
           (VarDec __arg__Abstraction__construct_x_f__f (T_Class C_Function))::
           nil)
          (SeqExp (FieldAssign (This) __field__Abstraction__t (Expr_X (SomeId __arg__Abstraction__construct_x_f__x)))
                  (SeqExp (FieldAssign (This) __field__Abstraction__x (Expr_X (SomeId __arg__Abstraction__construct_x_f__x)))
                          (SeqExp (FieldAssign (This) __field__Abstraction__f (Expr_X (SomeId __arg__Abstraction__construct_x_f__f)))
                                  (Expr_X (This)))))).

Definition METHOD_Abstraction__construct_x_t_f :=
 (AMethod __method__Abstraction__construct_x_t_f
          (T_Class C_Abstraction)
          ((VarDec __arg__Abstraction__construct_x_t_f__x (T_Class C_Variable))::
           (VarDec __arg__Abstraction__construct_x_t_f__t (T_Class C_LambdaTerm))::
           (VarDec __arg__Abstraction__construct_x_t_f__f (T_Class C_Function))::
           nil)
          (SeqExp (FieldAssign (This) __field__Abstraction__t (Expr_X (SomeId __arg__Abstraction__construct_x_t_f__t)))
                  (SeqExp (FieldAssign (This) __field__Abstraction__x (Expr_X (SomeId __arg__Abstraction__construct_x_t_f__x)))
                          (SeqExp (FieldAssign (This) __field__Abstraction__f (Expr_X (SomeId __arg__Abstraction__construct_x_t_f__f)))
                                  (Expr_X (This)))))).

Definition METHOD_Abstraction__cas :=
 (AMethod __method__Abstraction__cas
          (T_Class C_LambdaTerm)
          ((VarDec __arg__Abstraction__cas__x (T_Class C_Variable))::
           (VarDec __arg__Abstraction__cas__r (T_Class C_LambdaTerm))::
           nil)
          (VarDecExp (VarDec __local__Abstraction__cas__v (T_Class C_LambdaTerm)) (Expr_V (V_Pointer Null))
           (VarDecExp (VarDec __local__Abstraction__cas__y (T_Class C_Variable)) (FieldRef (Expr_X (This)) __field__Abstraction__x)
            (VarDecExp (VarDec __local__Abstraction__cas__z (T_Class C_Variable)) (Expr_V (V_Pointer Null))
             (SeqExp (IfExpr (Equality (Expr_X (SomeId __arg__Abstraction__cas__x))
                                       (Expr_X (SomeId __local__Abstraction__cas__y)))
                             (VarAssign (SomeId __local__Abstraction__cas__v) (Expr_X (This)))
(* which method are we invoking here? *)
                             (IfExpr (Equality (MethodInvocation (Expr_X (SomeId __arg__Abstraction__cas__r))
                                                                 __method__LambdaTerm__isFree
                                                                 ((SomeId __local__Abstraction__cas__y)::nil))
                                               (Expr_V (V_Bool false)))
                                     (VarDecExp (VarDec __local__Abstraction__cas__arg2 (T_Class C_LambdaTerm))
                                                (MethodInvocation (FieldRef (Expr_X (This)) __field__Abstraction__t)
                                                                  __method__Abstraction__cas
                                                                  ((SomeId __arg__Abstraction__cas__x)::(SomeId __arg__Abstraction__cas__r)::nil))
                                                (VarDecExp (VarDec __local__Abstraction__cas__arg2 (T_Class C_Function))
                                                           (FieldRef (Expr_X (This)) __field__Abstraction__f)
                                                           (VarAssign (SomeId __local__Abstraction__cas__v)
                                                                      (MethodInvocation (NewClass C_Abstraction)
                                                                                        __method__Abstraction__construct_x_t_f
                                                                                        ((SomeId __local__Abstraction__cas__y)::
                                                                                         (SomeId __local__Abstraction__cas__arg2)::
                                                                                         (SomeId __local__Abstraction__cas__arg3)::nil)))))
                                     (SeqExp (VarAssign (SomeId __local__Abstraction__cas__z)
                                                        (NewClass C_Variable))
                                             (*(var LambdaTerm arg2 := (((this $ t) @ ar (y z)) @ cas (x r)) in
                                                    (var Function arg3 := (this $ f) in
                                                        (v := ((new Abstraction) @ construct-x-t-f (z arg2 arg3))))) *)
                                             (VarDecExp (VarDec __local__Abstraction__cas__arg4 (T_Class C_LambdaTerm))
                                                        (MethodInvocation (MethodInvocation (FieldRef (Expr_X (This)) __field__Abstraction__t)
                                                                                            __method__LambdaTerm__ar
                                                                                            ((SomeId __local__Abstraction__cas__y)::(SomeId __local__Abstraction__cas__z)::nil))
                                                                          __method__LambdaTerm__cas
                                                                          ((SomeId __arg__Abstraction__cas__x)::(SomeId __arg__Abstraction__cas__r)::nil))
                                                        (VarDecExp (VarDec __local__Abstraction__cas__arg5 (T_Class C_Function))
                                                                   (FieldRef (Expr_X (This)) __field__Abstraction__f)
                                                                   (VarAssign (SomeId __local__Abstraction__cas__v)
                                                                              (MethodInvocation (NewClass C_Abstraction)
                                                                                                __method__Abstraction__construct_x_t_f
                                                                                                ((SomeId __local__Abstraction__cas__z)::
                                                                                                 (SomeId __local__Abstraction__cas__arg4)::
                                                                                                 (SomeId __local__Abstraction__cas__arg5)::nil))))))))
                     (Expr_X (SomeId __local__Abstraction__cas__v))))))).

(*
           (bool isFree ([Variable x])
                 (var bool v := false in
                      (begin
                        (if ((x == (this $ x)) == false)
                            (if (((this $ t) @ isFree (x)) == true)
                                (v := true)
                                else
                                (v := false))
                            else
                            (v := false))
                        v)))
*)
Definition METHOD_Abstraction__isFree :=
 (AMethod __method__Abstraction__isFree
          T_Bool
          ((VarDec __arg__Abstraction__isFree__x (T_Class C_Variable))::nil)
          (VarDecExp (VarDec __local__Abstraction__isFree__v T_Bool)
                     (Expr_V (V_Bool false))
                     (SeqExp (IfExpr (Equality (Equality (Expr_X (SomeId __arg__Abstraction__isFree__x))
                                                         (FieldRef (Expr_X (This)) __field__Abstraction__x))
                                               (Expr_V (V_Bool false)))
                                     (IfExpr (Equality (MethodInvocation (FieldRef (Expr_X (This)) __field__Abstraction__t)
                                                                         __method__LambdaTerm__isFree
                                                                         ((SomeId __arg__Abstraction__isFree__x)::nil))
                                                       (Expr_V (V_Bool true)))
                                             (VarAssign (SomeId __local__Abstraction__isFree__v) (Expr_V (V_Bool true)))
                                             (VarAssign (SomeId __local__Abstraction__isFree__v) (Expr_V (V_Bool false))))
                                     (VarAssign (SomeId __local__Abstraction__isFree__v) (Expr_V (V_Bool false))))
                             (Expr_X (SomeId __local__Abstraction__isFree__v))))).

(* (LambdaTerm br([LambdaTerm s])
                       (var LambdaTerm v := ((this $ t) @ cas ((this $ x) s)) in
                            (begin
                              (if (((this $ f) == null) == false)
                                  ((this $ f) @ eval ())
                                  else
                                  unit)
                              v)))
*)

Definition METHOD_Abstraction__br :=
 (AMethod __method__Abstraction__br
          (T_Class C_LambdaTerm)
          ((VarDec __arg__Abstraction__br__s (T_Class C_LambdaTerm))::nil)
          (VarDecExp (VarDec __local__Abstraction__br__arg1 (T_Class C_LambdaTerm))
                     (FieldRef (Expr_X This) __field__Abstraction__x)
                     (VarDecExp (VarDec __local__Abstraction__br__v (T_Class C_LambdaTerm))
                                (MethodInvocation (FieldRef (Expr_X (This)) __field__Abstraction__t)
                                                  __method__LambdaTerm__cas
                                                  (nil))
                                (SeqExp (IfExpr (Equality (Equality (FieldRef (Expr_X This) __field__Abstraction__f)
                                                                    (Expr_V (V_Pointer Null)))
                                                          (Expr_V (V_Bool false)))
                                                (MethodInvocation (FieldRef (Expr_X (This)) __field__Abstraction__f)
                                                                  __method__Function__eval
                                                                  (nil))
                                                (Expr_V (V_Unit)))
                                        (Expr_X (SomeId __local__Abstraction__br__v)))))).

(*
(LambdaTerm ar-abstraction([Variable x])
               (var Variable y := (this $ x) in
                    (var arg1 := ((this $ t) @ ar(y x)) in
                        (var arg2 := (this $ f) in
                            ((new Abstraction) @ construct-x-t-f (x arg1 arg2))))))
*)

Definition METHOD_Abstraction__ar_abstraction :=
 (AMethod __method__Abstraction__ar_abstraction
          (T_Class C_LambdaTerm)
          ((VarDec __arg__Abstraction__ar_abstraction__x (T_Class C_Variable))::nil)

          (VarDecExp (VarDec __local__Abstraction__ar_abstraction__y (T_Class C_Variable))
                     (FieldRef (Expr_X This) __field__Abstraction__x)
                     (VarDecExp (VarDec __local__Abstraction__ar_abstraction__arg1 (T_Class C_LambdaTerm))
                                (MethodInvocation (FieldRef (Expr_X This) __field__Abstraction__t)
                                                  __method__LambdaTerm__ar
                                                  ((SomeId __local__Abstraction__ar_abstraction__y)::
                                                   (SomeId __arg__Abstraction__ar_abstraction__x)::nil))
                                (VarDecExp (VarDec __local__Abstraction__ar_abstraction__arg2 (T_Class C_Function))
                                           (FieldRef (Expr_X This) __field__Abstraction__f)
                                           (MethodInvocation (NewClass C_Abstraction)
                                                             __method__Abstraction__construct_x_t_f
                                                             ((SomeId __arg__Abstraction__isFree__x)::nil)))))).

(*
(LambdaTerm ar([Variable oldVar] [Variable newVar])
                         (var LambdaTerm v := null in
                              (var Variable y := (this $ x) in
                                   (var Variable z := null in
                                        (begin
                                          (if (y == oldVar)
                                              (v := this)
                                              else
                                              (if (y == newVar)
                                                  (begin
                                                    (z := (new Variable))
                                                    (v := ((this @ ar-abstraction (z)) @ ar (oldVar newVar))))
                                                  else
                                                  (var arg1 := (this $ x) in
                                                    (var arg2 := ((this $ t) @ ar (oldVar newVar)) in
                                                     (var arg3 := (this $ f) in
                                                       (v := ((new Abstraction) @ construct-x-t-f (arg1 arg2 arg3))))))))
                                        v)))))
*)

Definition METHOD_Abstraction__ar :=
 (AMethod __method__Abstraction__ar
          (T_Class C_LambdaTerm)
          ((VarDec __arg__Abstraction__ar__oldVar (T_Class C_Variable))::
           (VarDec __arg__Abstraction__ar__newVar (T_Class C_Variable))::nil)

          (VarDecExp (VarDec __local__Abstraction__ar__v (T_Class C_LambdaTerm))
                     (Expr_V (V_Pointer Null))
                     (VarDecExp (VarDec __local__Abstraction__ar__y (T_Class C_Variable))
                                (FieldRef (Expr_X (This)) __field__Abstraction__x)
                                (VarDecExp (VarDec __local__Abstraction__ar__z (T_Class C_Variable))
                                           (Expr_V (V_Pointer Null))
                                           (SeqExp (IfExpr (Equality (Expr_X (SomeId __local__Abstraction__ar__y))
                                                                     (Expr_X (SomeId __arg__Abstraction__ar__oldVar)))
                                                           (VarAssign (SomeId __local__Abstraction__ar__v)
                                                                      (Expr_X This))
                                                           (IfExpr (Equality (Expr_X (SomeId __local__Abstraction__ar__y))
                                                                             (Expr_X (SomeId __arg__Abstraction__ar__newVar)))
                                                                   (SeqExp (VarAssign (SomeId __local__Abstraction__ar__z)
                                                                                      (NewClass C_Variable))
                                                                           (VarAssign (SomeId __local__Abstraction__ar__v)
                                                                                      (MethodInvocation (MethodInvocation (Expr_X This) __method__Abstraction__ar_abstraction ((SomeId __local__Abstraction__ar__z)::nil))
                                                                                                        __method__LambdaTerm__ar
                                                                                                        ((SomeId __arg__Abstraction__ar__oldVar)::
                                                                                                         (SomeId __arg__Abstraction__ar__newVar)::
                                                                                                         nil))))
                                                                   (VarDecExp (VarDec __local__Abstraction__ar__arg1 (T_Class C_Variable))
                                                                                      (FieldRef (Expr_X This) __field__Abstraction__x)
                                                                                      (VarDecExp (VarDec __local__Abstraction__ar__arg2 (T_Class C_LambdaTerm))
                                                                                                 (MethodInvocation (FieldRef (Expr_X This) __field__Abstraction__t)
                                                                                                                   __method__LambdaTerm__ar
                                                                                                                   ((SomeId __arg__Abstraction__ar__oldVar)::
                                                                                                                    (SomeId __arg__Abstraction__ar__newVar)::
                                                                                                                    nil))
                                                                                                 (VarDecExp (VarDec __local__Abstraction__ar__arg3 (T_Class C_Function))
                                                                                                            (FieldRef (Expr_X This) __field__Abstraction__f)
                                                                                                            (VarAssign (SomeId __local__Abstraction__ar__v)
                                                                                                                       (MethodInvocation (NewClass C_Abstraction)
                                                                                                                                         __method__Abstraction__construct_x_t_f
                                                                                                                                         ((SomeId __local__Abstraction__ar__arg1)::
                                                                                                                                          (SomeId __local__Abstraction__ar__arg2)::
                                                                                                                                          (SomeId __local__Abstraction__ar__arg3)::nil))))))))
                                                   (Expr_X (SomeId __local__Abstraction__br__v))))))).

(*
(bool isAe ([LambdaTerm x])
                (var bool v := false in
                     (var Abstraction a := null in
                          (begin
                            (if (x instanceof Abstraction)
                                (begin
                                  (a := (Abstraction x))
                                  (var LambdaTerm arg1 := (a $ x) in
                                    (if (((this $ x) @ isAe (arg1)) == false)
                                      (var Variable arg2 := (this $ x) in
                                      (a := (Abstraction (a @ ar-abstraction (arg2)))))
                                      else
                                      unit))
                                  (var arg3 := (a $ t) in
                                  (v := ((this $ t) @ isAe (arg3)))))
                                else
                                unit)
                            v))))
*)

Definition METHOD_Abstraction__isAe :=
 (AMethod __method__Abstraction__isAe
          T_Bool
          ((VarDec __arg__Abstraction__isAe__x (T_Class C_LambdaTerm))::nil)

          (VarDecExp (VarDec __local__Abstraction__isAe__v T_Bool)
                     (Expr_V (V_Bool false))
                     (VarDecExp (VarDec __local__Abstraction__isAe__a (T_Class C_Abstraction))
                                (Expr_V (V_Pointer Null))
                                (SeqExp (IfExpr (InstanceOf (Expr_X (SomeId __arg__Abstraction__isAe__x)) C_Abstraction)
                                                (SeqExp (VarAssign (SomeId __local__Abstraction__isAe__a)
                                                                   (Cast C_Abstraction (Expr_X (SomeId __arg__Abstraction__isAe__x))))
                                                        (SeqExp
                                                                (* (var LambdaTerm arg1 := (a $ x) in
                                                                                                    (if (((this $ x) @ isAe (arg1)) == false)
                                                                                                      (var Variable arg2 := (this $ x) in
                                                                                                      (a := (Abstraction (a @ ar-abstraction (arg2)))))
                                                                                                      else
                                                                                                      unit))
                                                                *)
                                                                  (VarDecExp (VarDec __local__Abstraction__isAe__arg1 (T_Class C_LambdaTerm))
                                                                             (FieldRef (Expr_X (SomeId __local__Abstraction__isAe__a)) __field__Abstraction__x)
                                                                             (IfExpr (Equality (MethodInvocation (FieldRef (Expr_X This) __field__Abstraction__x)
                                                                                                                 __method__Variable__isAe
                                                                                                                 ((SomeId __local__Abstraction__isAe__arg1)::nil))
                                                                                               (Expr_V (V_Bool false)))
                                                                                     (VarDecExp (VarDec __local__Abstraction__isAe__arg2 (T_Class C_Variable))
                                                                                                (FieldRef (Expr_X This) __field__Abstraction__x)
                                                                                                (VarAssign (SomeId __local__Abstraction__isAe__a)
                                                                                                           (Cast C_Abstraction (MethodInvocation (Expr_X (SomeId __local__Abstraction__isAe__a))
                                                                                                                                                 __method__Abstraction__ar_abstraction
                                                                                                                                                 ((SomeId __local__Abstraction__isAe__arg2)::nil)))))
                                                                                     (Expr_V V_Unit)))
                                                                (*
                                                                (var LambdaTerm arg3 := (a $ t) in
                                                                     (v := ((this $ t) @ isAe (arg3))))
                                                                *)
                                                                  (VarDecExp (VarDec __local__Abstraction__isAe__arg3 (T_Class C_LambdaTerm))
                                                                             (FieldRef (Expr_X (SomeId __local__Abstraction__isAe__a)) __field__Abstraction__t)
                                                                             (VarAssign (SomeId __local__Abstraction__isAe__v)
                                                                                        (MethodInvocation (FieldRef (Expr_X This) __field__Abstraction__t)
                                                                                                          __method__LambdaTerm__isAe (nil))))))
                                                 (Expr_V V_Unit))
                                        (Expr_X (SomeId __local__Abstraction__isAe__v)))))).

Definition METHOD_Abstraction__eval :=
 (AMethod __method__Abstraction__eval
          (T_Class C_LambdaTerm)
          (nil)
          (Expr_X (This))).

(*
(Application construct ([LambdaTerm t] [LambdaTerm s])
                        (begin (this $ t := t )
                               (this $ s := s)
                               this))
*)
Definition METHOD_Application__construct :=
 (AMethod __method__Application__construct
          (T_Class C_Application)
          ((VarDec __arg__Application__construct__t (T_Class C_LambdaTerm))::(VarDec __arg__Application__construct__s (T_Class C_LambdaTerm))::nil)

          (SeqExp (FieldAssign (This) __field__Application__t (Expr_X (SomeId __arg__Application__construct__t)))
                  (SeqExp (FieldAssign (This) __field__Application__s (Expr_X (SomeId __arg__Application__construct__s)))
                          (Expr_X This)))).

(*
(LambdaTerm cas ([Variable x] [LambdaTerm r])
                       (var LambdaTerm lop := null in
                            (var LambdaTerm rop := null in
                                 (var LambdaTerm v := null in
                                      (begin
                                        (lop := ((this $ t) @ cas (x r)))
                                        (rop := ((this $ s) @ cas (x r)))
                                        (v := ((new Application) @ construct (lop rop)))
                                        v)))))
*)
Definition METHOD_Application__cas :=
 (AMethod __method__Application__cas
          (T_Class C_LambdaTerm)
          ((VarDec __arg__Application__cas__x (T_Class C_Variable))::(VarDec __arg__Application__cas__r (T_Class C_LambdaTerm))::nil)

          (VarDecExp (VarDec __local__Application__cas__lop (T_Class C_LambdaTerm))
                     (Expr_V (V_Pointer Null))
                     (VarDecExp (VarDec __local__Application__cas__rop (T_Class C_LambdaTerm))
                                (Expr_V (V_Pointer Null))
                                (VarDecExp (VarDec __local__Application__cas__v (T_Class C_LambdaTerm))
                                           (Expr_V (V_Pointer Null))
                                           (SeqExp (VarAssign (SomeId __local__Application__cas__lop)
                                                              (MethodInvocation (FieldRef (Expr_X This) __field__Application__t)
                                                                                __method__LambdaTerm__cas
                                                                                ((SomeId __arg__Application__cas__x)::(SomeId __arg__Application__cas__r)::nil)))
                                                   (SeqExp (VarAssign (SomeId __local__Application__cas__rop)
                                                                      (MethodInvocation (FieldRef (Expr_X This) __field__Application__s)
                                                                                         __method__LambdaTerm__cas
                                                                                           ((SomeId __arg__Application__cas__x)::(SomeId __arg__Application__cas__r)::nil)))
                                                           (SeqExp (VarAssign (SomeId __local__Application__cas__v)
                                                                                (MethodInvocation (NewClass C_Application) __method__Application__construct
                                                                                                    ((SomeId __local__Application__cas__lop)::(SomeId __local__Application__cas__rop)::nil)))
                                                                    (Expr_X (SomeId __local__Application__cas__v))))))))).

(*
(bool isFree ([Variable x])
                 (var bool v := ((this $ t) @ isFree(x)) in
                      (begin
                        (if ((this $ s) @ isFree(x))
                            (v := true)
                            else
                            unit)
                        v)))
*)
Definition METHOD_Application__isFree :=
 (AMethod __method__Application__isFree
          T_Bool
          ((VarDec __arg__Application__isFree__x T_Bool)::nil)
          (VarDecExp (VarDec __local__Application__isFree__v T_Bool)
                     (MethodInvocation (FieldRef (Expr_X This) __field__Application__t) __method__LambdaTerm__isFree ((SomeId __arg__Application__isFree__x)::nil))
                     (SeqExp (IfExpr (MethodInvocation (FieldRef (Expr_X This) __field__Application__s) __method__LambdaTerm__isFree ((SomeId __arg__Application__isFree__x)::nil))
                                     (VarAssign (SomeId __local__Application__isFree__v) (Expr_V (V_Bool true)))
                                     (Expr_V V_Unit))
                             (Expr_X (SomeId __local__Application__isFree__v))))).

(*
(LambdaTerm ar ([Variable oldVar] [Variable newVar])
  (var LambdaTerm t1 := ((this $ t) @ ar(oldVar newVar)) in
    (var LambdaTerm t2 := ((this $ s) @ ar(oldVar newVar)) in
           ((new Application) @ construct (t1 t2)))))
*)

Definition METHOD_Application__ar :=
 (AMethod __method__Application__ar
          (T_Class C_LambdaTerm)
          ((VarDec __arg__Application__ar__oldVar (T_Class C_Variable))::(VarDec __arg__Application__ar__newVar (T_Class C_Variable))::nil)

          (VarDecExp (VarDec __local__Application__ar__t1 (T_Class C_LambdaTerm))
                     (MethodInvocation (FieldRef (Expr_X This) __field__Application__t) __method__LambdaTerm__ar
                                       ((SomeId __arg__Application__ar__oldVar)::(SomeId __arg__Application__ar__newVar)::nil))
                     (VarDecExp (VarDec __local__Application__ar__t2 (T_Class C_LambdaTerm))
                                (MethodInvocation (FieldRef (Expr_X This) __field__Application__s) __method__LambdaTerm__ar
                                                  ((SomeId __arg__Application__ar__oldVar)::(SomeId __arg__Application__ar__newVar)::nil))
                                (MethodInvocation (NewClass C_Application) __method__Application__construct
                                                  ((SomeId __local__Application__ar__t1)::(SomeId __local__Application__ar__t2)::nil))))).

(*
(bool isAe ([LambdaTerm x])
                 (var bool v := false in
                      (begin
                        (if (x instanceof Application)
                            (var Application a := (Application x) in
                             (var LambdaTerm t1 := (a $ t) in
                              (var LambdaTerm t2 := (a $ s) in
                                 (v := (if ((this $ t) @ isAe (t1))
                                           ((this $ s) @ isAe (t2))
                                           else
                                           false)))))
                            else
                            unit)
                        v)))
*)

Definition METHOD_Application__isAe :=
 (AMethod __method__Application__isAe
          T_Bool ((VarDec __arg__Application__isAe__x (T_Class C_LambdaTerm))::nil)

          (VarDecExp (VarDec __local__Application__isAe__v T_Bool)
                     (Expr_V (V_Bool false))
                     (SeqExp (IfExpr (InstanceOf (Expr_X (SomeId __arg__Application__isAe__x)) C_Application)
                                      (VarDecExp (VarDec __local__Application__isAe__a (T_Class C_Application))
                                                (Cast C_Application (Expr_X (SomeId __arg__Application__isAe__x)))
                                                (VarDecExp (VarDec __local__Application__isAe__t1 (T_Class C_LambdaTerm))
                                                           (FieldRef (Expr_X (SomeId __local__Application__isAe__a)) __field__Application__t)
                                                           (VarDecExp (VarDec __local__Application__isAe__t2 (T_Class C_LambdaTerm))
                                                                      (FieldRef (Expr_X (SomeId __local__Application__isAe__a)) __field__Application__s)
                                                                      (VarAssign (SomeId __local__Application__isAe__v)
                                                                                 (IfExpr (MethodInvocation (FieldRef (Expr_X This) __field__Application__t)
                                                                                                           __method__LambdaTerm__isAe
                                                                                                           ((SomeId __local__Application__isAe__t1)::nil))
                                                                                         (MethodInvocation (FieldRef (Expr_X This) __field__Application__s)
                                                                                                           __method__LambdaTerm__isAe
                                                                                                           ((SomeId __local__Application__isAe__t2)::nil))
                                                                                         (Expr_V (V_Bool false)))))))
                                     (Expr_V V_Unit))
                             (Expr_X (SomeId __local__Application__isAe__v))))).

(*
(LambdaTerm eval ()
                       (var LambdaTerm lop := ((this $ t) @ eval ()) in
                            (var LambdaTerm rop := ((this $ s) @ eval ()) in
                                 (var LambdaTerm v := null in
                                      (begin
                                        (if (lop instanceof Abstraction)
                                            (var Abstraction a := (Abstraction lop) in
                                                 (v := ((a @ br (rop)) @ eval ())))
                                            else
                                            (v := ((new Application) @ construct (lop rop))))
                                        v)))))
*)

Definition METHOD_Application__eval :=
 (AMethod __method__Application__eval
          (T_Class C_LambdaTerm) (nil)

          (VarDecExp (VarDec __local__Application__eval__lop (T_Class C_LambdaTerm))
                     (MethodInvocation (FieldRef (Expr_X This) __field__Application__t) __method__LambdaTerm__eval nil)
                     (VarDecExp (VarDec __local__Application__eval__rop (T_Class C_LambdaTerm))
                                (MethodInvocation (FieldRef (Expr_X This) __field__Application__s) __method__LambdaTerm__eval nil)
                                (VarDecExp (VarDec __local__Application__eval__v (T_Class C_LambdaTerm))
                                           (Expr_V (V_Pointer Null))
                                           (SeqExp (IfExpr (InstanceOf (Expr_X (SomeId __local__Application__eval__lop)) C_Abstraction)
                                                           (VarDecExp (VarDec __local__Application__eval__a (T_Class C_Abstraction))
                                                                      (Cast C_Abstraction (Expr_X (SomeId __local__Application__eval__lop)))
                                                                      (VarAssign (SomeId __local__Application__eval__v)
                                                                                 (MethodInvocation (MethodInvocation (Expr_X (SomeId __local__Application__eval__a)) __method__Abstraction__br ((SomeId __local__Application__eval__rop)::nil))
                                                                                                      __method__LambdaTerm__eval nil)))
                                                            (VarAssign (SomeId __local__Application__eval__v)
                                                                       (MethodInvocation (NewClass C_Application)
                                                                                         __method__Application__construct
                                                                                         ((SomeId __local__Application__eval__lop)::(SomeId __local__Application__eval__rop)::nil))))
                                                   (Expr_X (SomeId __local__Application__eval__v))))))).



(*
(bool m ([bool x])
      x)
*)
Definition METHOD_ChurchTest__m :=
 (AMethod __method__ChurchTest__m
          T_Bool ((VarDec __arg__ChurchTest__m__x T_Bool)::nil) (Expr_X (SomeId __arg__ChurchTest__m__x))).

(*
(bool n () true)
*)
Definition METHOD_ChurchTest__n :=
 (AMethod __method__ChurchTest__n
          T_Bool (nil) (Expr_V (V_Bool true))).

(*
(bool methodInvokeTest ()
  (var bool arg :=(this @ n ()) in
                 (this @ m (arg))))
*)

Definition METHOD_ChurchTest__methodInvokeTest :=
 (AMethod __method__ChurchTest__methodInvokeTest
          T_Bool (nil)
          (VarDecExp (VarDec __local__ChurchTest__methodInvokeTest__arg T_Bool)
                     (MethodInvocation (Expr_X This) __method__ChurchTest__n (nil))
                     (MethodInvocation (Expr_X This) __method__ChurchTest__m ((SomeId __local__ChurchTest__methodInvokeTest__arg)::nil)))).

(*
ChurchTest construct ()
                       (var Church v := ((new Church) @ construct ()) in
                            (begin
                              (this $ instance := v)
                              (this $ sinz := ((new SetIfNotZero) @ construct ()))
                              this)))
*)
Definition METHOD_ChurchTest__construct :=
 (AMethod __method__ChurchTest__construct
          (T_Class C_ChurchTest) (nil)

          (VarDecExp (VarDec __local__ChurchTest__construct__v (T_Class C_Church))
                     (MethodInvocation (NewClass C_Church) __method__Church__construct (nil))
                     (SeqExp (FieldAssign This __field__ChurchTest__instance (Expr_X (SomeId __local__ChurchTest__construct__v)))
                             (SeqExp (FieldAssign This __field__ChurchTest__sinz (MethodInvocation (NewClass C_SetIfNotZero) __method__SetIfNotZero__construct (nil)))
                                     (Expr_X This))))).

(*
(bool testZeroJavalite ()
                 (var Church c := (this $ instance) in
                      (var SetIfNotZero s := (this $ sinz) in
                           (begin
                             (s $ bam := false)
                             (var LambdaTerm t1 := (c @ zero ()) in
                              (s @ doEval (t1)))
                             (s $ bam)))))
*)

Definition METHOD_ChurchTest__testZeroJavalite :=
 (AMethod __method__ChurchTest__testZeroJavalite
          T_Bool (nil)

          (VarDecExp (VarDec __local__ChurchTest__testZeroJavalite__c (T_Class C_Church))
                     (FieldRef (Expr_X This) __field__ChurchTest__instance)
                     (VarDecExp (VarDec __local__ChurchTest__testZeroJavalite__s (T_Class C_SetIfNotZero))
                                (FieldRef (Expr_X This) __field__ChurchTest__sinz)
                                (SeqExp (FieldAssign (SomeId __local__ChurchTest__testZeroJavalite__s) __field__SetIfNotZero__bam (Expr_V (V_Bool false)))
                                        (SeqExp (VarDecExp (VarDec __local__ChurchTest__testZeroJavalite__t1 (T_Class C_LambdaTerm))
                                                           (MethodInvocation (Expr_X (SomeId __local__ChurchTest__testZeroJavalite__c)) __method__Church__zero nil)
                                                           (MethodInvocation (Expr_X (SomeId __local__ChurchTest__testZeroJavalite__s)) __method__SetIfNotZero__doEval ((SomeId __local__ChurchTest__testZeroJavalite__t1)::nil)))
                                                (FieldRef (Expr_X (SomeId __local__ChurchTest__testZeroJavalite__s)) __field__SetIfNotZero__bam)))))).

(*
(bool testNotZeroJavalite ()
                (var Church c := (this $ instance) in
                      (var SetIfNotZero s := (this $ sinz) in
                           (begin
                             (s $ bam := false)
                             (var LambdaTerm t1 := (c @ one ()) in
                             (s @ doEval (t1)))
                             (s $ bam)))))
*)

Definition METHOD_ChurchTest__testNotZeroJavalite :=
 (AMethod __method__ChurchTest__testNotZeroJavalite
          T_Bool (nil)

          (VarDecExp (VarDec __local__ChurchTest__testNotZeroJavalite__c (T_Class C_Church))
                     (FieldRef (Expr_X This) __field__ChurchTest__instance)
                     (VarDecExp (VarDec __local__ChurchTest__testNotZeroJavalite__s (T_Class C_SetIfNotZero))
                                (FieldRef (Expr_X This) __field__ChurchTest__sinz)
                                (SeqExp (FieldAssign (SomeId __local__ChurchTest__testNotZeroJavalite__s) __field__SetIfNotZero__bam (Expr_V (V_Bool false)))
                                        (SeqExp (VarDecExp (VarDec __local__ChurchTest__testNotZeroJavalite__t1 (T_Class C_LambdaTerm))
                                                           (MethodInvocation (Expr_X (SomeId __local__ChurchTest__testNotZeroJavalite__c)) __method__Church__one nil)
                                                           (MethodInvocation (Expr_X (SomeId __local__ChurchTest__testNotZeroJavalite__s)) __method__SetIfNotZero__doEval ((SomeId __local__ChurchTest__testNotZeroJavalite__t1)::nil)))
                                                (FieldRef (Expr_X (SomeId __local__ChurchTest__testNotZeroJavalite__s)) __field__SetIfNotZero__bam)))))).

(*
(bool testJavaliteVariableEquivalence ()
                  (var Variable x := (new Variable) in
                       (var Variable y := (new Variable) in
                            (x == y))))
*)
Definition METHOD_ChurchTest__testJavaliteVariableEquivalence :=
 (AMethod __method__ChurchTest__testJavaliteVariableEquivalence
          T_Bool (nil)
          (VarDecExp (VarDec __local__ChurchTest__testJavaliteVariableEquivalence__x (T_Class C_Variable))
                     (NewClass C_Variable)
                     (VarDecExp (VarDec __local__ChurchTest__testJavaliteVariableEquivalence__y (T_Class C_Variable))
                                (NewClass C_Variable)
                                (Equality (Expr_X (SomeId __local__ChurchTest__testJavaliteVariableEquivalence__x)) (Expr_X (SomeId __local__ChurchTest__testJavaliteVariableEquivalence__x)))))).

(*
(bool testJavaliteVariableEquivalence2 ()
                  (var SetIfNotZero x := (new SetIfNotZero) in
                       (var SetIfNotZero y := (new SetIfNotZero) in
                            (begin
                              (x $ bam := true)
                              (x == y)))))
*)
Definition METHOD_ChurchTest__testJavaliteVariableEquivalence2 :=
 (AMethod __method__ChurchTest__testJavaliteVariableEquivalence2
          T_Bool (nil)
          (VarDecExp (VarDec __local__ChurchTest__testJavaliteVariableEquivalence__x (T_Class C_Variable))
                     (NewClass C_Variable)
                     (VarDecExp (VarDec __local__ChurchTest__testJavaliteVariableEquivalence__y (T_Class C_Variable))
                                (NewClass C_Variable)
                                (Equality (Expr_X (SomeId __local__ChurchTest__testJavaliteVariableEquivalence__x)) (Expr_X (SomeId __local__ChurchTest__testJavaliteVariableEquivalence__x)))))).



(*
(Church construct()
                   (begin
                     (this $ x := (new Variable))
                     (this $ f := (new Variable))
                     (this $ n := (new Variable))

                     (* What types should t1 and t2 be? *)
                     (var Variable arg1 := (this $ f) in
                      (var Variable t1 := (this $ x) in
                       (var LambdaTerm t2 := (this $ x) in
                        (var LambdaTerm arg2 := ((new Abstraction) @ construct-x-t (t1 t2)) in
                         (this $ zero := ((new Abstraction) @ construct-x-t (arg1 arg2)))))))

                     (var Variable arg3 := (this $ n) in
                      (var Variable arg5 := (this $ f) in
                       (var Variable arg7 := (this $ x) in
                        (var LambdaTerm arg9 := (this $ f) in
                         (var LambdaTerm arg13 := (this $ n) in
                          (var LambdaTerm arg14 := (this $ f) in
                           (var LambdaTerm arg11 := ((new Application) @ construct (arg13 arg14)) in
                            (var LambdaTerm arg12 := (this $ x) in
                             (var LambdaTerm arg10 := ((new Application) @ construct (arg11 arg12)) in
                              (var LambdaTerm arg8 := ((new Application) @ construct (arg9 arg10)) in
                               (var Variable arg6 := ((new Abstraction) @ construct-x-t (arg7 arg8)) in
                                (var LambdaTerm arg4 := ((new Abstraction) @ construct-x-t ( arg5 arg6)) in
                                 (this $ succ := ((new Abstraction) @ construct-x-t (arg3 arg4)))))))))))))))

                     (var LambdaTerm arg15 := (this $ succ) in
                      (var LambdaTerm arg16 := (this $ zero) in
                       (this $ one := ((new Application) @ construct (arg15 arg16)))))

                     this
                     ))
*)

Definition METHOD_Church__construct :=
 (AMethod __method__Church__construct
          (T_Class C_Church)
          (nil)

          (SeqExp (FieldAssign This __field__Church__x (NewClass C_Variable))
                  (SeqExp (FieldAssign This __field__Church__f (NewClass C_Variable))
                          (SeqExp (FieldAssign This __field__Church__n (NewClass C_Variable))
                                  (SeqExp
(*
                     (var Variable arg1 := (this $ f) in
                      (var Variable t1 := (this $ x) in
                       (var LambdaTerm t2 := (this $ x) in
                        (var LambdaTerm arg2 := ((new Abstraction) @ construct-x-t (t1 t2)) in
                         (this $ zero := ((new Abstraction) @ construct-x-t (arg1 arg2)))))))
*)
(VarDecExp (VarDec __local__Church__construct__arg1 (T_Class C_Variable))
           (FieldRef (Expr_X This) __field__Church__f)
           (VarDecExp (VarDec __local__Church__construct__t1 (T_Class C_Variable))
                      (FieldRef (Expr_X This) __field__Church__x)
                      (VarDecExp (VarDec __local__Church__construct__t2 (T_Class C_LambdaTerm))
                                 (FieldRef (Expr_X This) __field__Church__x)
                                 (VarDecExp (VarDec __local__Church__construct__arg2 (T_Class C_LambdaTerm))
                                            (MethodInvocation (NewClass C_Abstraction)
                                                              __method__Abstraction__construct_x_t
                                                              ((SomeId __local__Church__construct__t1)::(SomeId __local__Church__construct__t2)::nil))
                                            (FieldAssign This __field__Church__zero
                                                         (MethodInvocation (NewClass C_Abstraction)
                                                                           __method__Abstraction__construct_x_t
((SomeId __local__Church__construct__arg1)::(SomeId __local__Church__construct__arg2)::nil)))))))


(*
                    (var Variable arg3 := (this $ n) in
                      (var Variable arg5 := (this $ f) in
                       (var Variable arg7 := (this $ x) in
                        (var LambdaTerm arg9 := (this $ f) in
                         (var LambdaTerm arg13 := (this $ n) in
                          (var LambdaTerm arg14 := (this $ f) in
                           (var LambdaTerm arg11 := ((new Application) @ construct (arg13 arg14)) in
                            (var LambdaTerm arg12 := (this $ x) in
                             (var LambdaTerm arg10 := ((new Application) @ construct (arg11 arg12))
                              (var LambdaTerm arg8 := ((new Application) @ construct (arg9 arg10)) in
                               (var Variable arg6 := ((new Abstraction) @ construct-x-t (arg7 arg8))
                                (var LambdaTerm arg4 := ((new Abstraction) @ construct-x-t ( arg5 arg6)) in
                                 (this $ succ := ((new Abstraction) @ construct-x-t (arg3 arg4)))))))))))))))
*)
(SeqExp
(VarDecExp (VarDec __local__Church__construct__arg3 (T_Class C_Variable))
 (FieldRef (Expr_X This) __field__Church__n)
 (VarDecExp (VarDec __local__Church__construct__arg5 (T_Class C_Variable))
  (FieldRef (Expr_X This) __field__Church__f)
  (VarDecExp (VarDec __local__Church__construct__arg7 (T_Class C_Variable))
   (FieldRef (Expr_X This) __field__Church__x)
   (VarDecExp (VarDec __local__Church__construct__arg9 (T_Class C_LambdaTerm))
    (FieldRef (Expr_X This) __field__Church__f)
    (VarDecExp (VarDec __local__Church__construct__arg13 (T_Class C_LambdaTerm))
     (FieldRef (Expr_X This) __field__Church__n)
     (VarDecExp (VarDec __local__Church__construct__arg14 (T_Class C_LambdaTerm))
      (FieldRef (Expr_X This) __field__Church__f)
      (VarDecExp (VarDec __local__Church__construct__arg11 (T_Class C_LambdaTerm))
       (MethodInvocation (NewClass C_Application) __method__Application__construct
                         ((SomeId __local__Church__construct__arg13)::(SomeId __local__Church__construct__arg14)::nil))
         (VarDecExp (VarDec __local__Church__construct__arg12 (T_Class C_LambdaTerm))
          (FieldRef (Expr_X This) __field__Church__x)
           (VarDecExp (VarDec __local__Church__construct__arg10 (T_Class C_LambdaTerm))
             (MethodInvocation (NewClass C_Application) __method__Application__construct
                               ((SomeId __local__Church__construct__arg11)::(SomeId __local__Church__construct__arg12)::nil))
             (VarDecExp (VarDec __local__Church__construct__arg8 (T_Class C_LambdaTerm))
               (MethodInvocation (NewClass C_Application) __method__Application__construct
                               ((SomeId __local__Church__construct__arg9)::(SomeId __local__Church__construct__arg10)::nil))
             (VarDecExp (VarDec __local__Church__construct__arg6 (T_Class C_Variable))
               (MethodInvocation (NewClass C_Abstraction) __method__Abstraction__construct_x_t
                               ((SomeId __local__Church__construct__arg7)::(SomeId __local__Church__construct__arg8)::nil))
               (VarDecExp (VarDec __local__Church__construct__arg4 (T_Class C_LambdaTerm))
                 (MethodInvocation (NewClass C_Abstraction) __method__Abstraction__construct_x_t
                                 ((SomeId __local__Church__construct__arg5)::(SomeId __local__Church__construct__arg6)::nil))
                 (FieldAssign This __field__Church__succ
                              (MethodInvocation (NewClass C_Abstraction) __method__Abstraction__construct_x_t
                                 ((SomeId __local__Church__construct__arg3)::(SomeId __local__Church__construct__arg4)::nil)))))))))))))))

(*
 (var arg15 := (this $ succ) in
  (var arg16 := (this $ zero) in
   (this $ one := ((new Application) @ construct (arg15 arg16)))))
this
*)
(SeqExp
 (VarDecExp (VarDec __local__Church__construct__arg15 (T_Class C_LambdaTerm))
  (FieldRef (Expr_X This) __field__Church__succ)
   (VarDecExp (VarDec __local__Church__construct__arg16 (T_Class C_LambdaTerm))
     (FieldRef (Expr_X This) __field__Church__zero)
     (FieldAssign This __field__Church__one
       (MethodInvocation (NewClass C_Application) __method__Application__construct
                         ((SomeId __local__Church__construct__arg15)::(SomeId __local__Church__construct__arg16)::nil)))))
 (Expr_X This)))))))).
(*
(Abstraction zero ()
     (this $ zero))
*)
Definition METHOD_Church__zero :=
 (AMethod __method__Church__zero
          (T_Class C_Abstraction)
          (nil)
          (FieldRef (Expr_X This) __field__Church__zero)).

(*
(Abstraction one ()
     (this $ one))
*)
Definition METHOD_Church__one :=
 (AMethod __method__Church__one
          (T_Class C_Abstraction)
          (nil)
          (FieldRef (Expr_X This) __field__Church__one)).


(*
((Function construct ()
                     (begin
                       (this $ x := (new Variable))
                       (this $ y := (new Variable))
                       (this $ bam := false)
                       this))
*)
Definition METHOD_SetIfNotZero__construct :=
 (AMethod __method__SetIfNotZero__construct
          (T_Class C_Function)
          (nil)

          (SeqExp (FieldAssign (This) __field__SetIfNotZero__x (NewClass C_Variable))
                  (SeqExp (FieldAssign (This) __field__SetIfNotZero__y (NewClass C_Variable))
                          (SeqExp (FieldAssign (This) __field__SetIfNotZero__bam (Expr_V (V_Bool false)))
                                  (Expr_X This))))).
(*
(unit eval ()
                 (this $ bam := true))
*)
Definition METHOD_SetIfNotZero__eval :=
 (AMethod __method__SetIfNotZero__eval
          T_Unit
          (nil)
          (FieldAssign (This) __field__SetIfNotZero__bam (Expr_V (V_Bool true)))).

(*
(unit doEval ([LambdaTerm c])
  (var Variable arg1 := (this $ x) in
   (var LambdaTerm t1 := ((new Abstraction) @ construct-x-f (arg1 this)) in
    (var LambdaTerm t2 := ((new Application) @ construct (c t1)) in
     (var Variable arg3 := (this $ y) in
      (var Variable arg4 := (this $ y) in
       (var LambdaTerm t3 := ((new Abstraction) @ construct-x-t (arg3 arg4)) in
         (((new Application) @ construct (t2 t3)) @ eval ()))))))))
*)

Definition METHOD_SetIfNotZero__doEval :=
 (AMethod __method__SetIfNotZero__doEval
          T_Unit ((VarDec __arg__SetIfNotZero__doEval__c (T_Class C_LambdaTerm))::nil)

          (VarDecExp (VarDec __local__SetIfNotZero__doEval__arg1 (T_Class C_Variable))
                     (FieldRef (Expr_X This) __field__SetIfNotZero__x)
                     (VarDecExp (VarDec __local__SetIfNotZero__doEval__t1 (T_Class C_LambdaTerm))
                                (MethodInvocation (NewClass C_Abstraction)
                                                  __method__Abstraction__construct_x_f
                                                  ((SomeId __local__SetIfNotZero__doEval__arg1)::
                                                   This::nil))
                                (VarDecExp (VarDec __local__SetIfNotZero__doEval__t2 (T_Class C_LambdaTerm))
                                           (MethodInvocation (NewClass C_Application)
                                                  __method__Application__construct
                                                  ((SomeId __arg__SetIfNotZero__doEval__c)::
                                                   (SomeId __local__SetIfNotZero__doEval__t1)::nil))
                                            (VarDecExp (VarDec __local__SetIfNotZero__doEval__arg3 (T_Class C_Variable))
                                                       (FieldRef (Expr_X This) __field__SetIfNotZero__y)
                                                       (VarDecExp (VarDec __local__SetIfNotZero__doEval__arg4 (T_Class C_Variable))
                                                                  (FieldRef (Expr_X This) __field__SetIfNotZero__y)
                                                                  (VarDecExp (VarDec __local__SetIfNotZero__doEval__t3 (T_Class C_LambdaTerm))
                                                                            (MethodInvocation (NewClass C_Abstraction)
                                                                                                __method__Abstraction__construct_x_t
                                                                                                ((SomeId __local__SetIfNotZero__doEval__arg3)::
                                                                                                (SomeId __local__SetIfNotZero__doEval__arg4)::nil))
                                                                            (MethodInvocation (NewClass C_Application)
                                                                                            __method__Application__construct
                                                                                            ((SomeId __local__SetIfNotZero__doEval__t2)::
                                                                                             (SomeId __local__SetIfNotZero__doEval__t3)::nil))))))))).



(*
(LambdaTerm cas ([Variable x] [LambdaTerm r])
                       (var Variable v := this in
                            (begin
                              (if (this == x)
                                  (v := r)
                                  else
                                  unit)
                              v)))
*)
Definition METHOD_Variable__cas :=
 (AMethod __method__Variable__cas
        (T_Class C_LambdaTerm)
        ((VarDec __arg__Variable__cas__x (T_Class C_Variable))::(VarDec __arg__Variable__cas__r (T_Class C_LambdaTerm))::nil)

        (VarDecExp (VarDec __local__Variable__cas__v (T_Class C_Variable))
                   (Expr_X This)
                   (SeqExp (IfExpr (Equality (Expr_X This) (Expr_X (SomeId __arg__Variable__cas__x)))
                                   (VarAssign (SomeId __local__Variable__cas__v) (Expr_X (SomeId __arg__Variable__cas__r)))
                                   (Expr_V (V_Unit)))
                           (Expr_X (SomeId __local__Variable__cas__v))))).

(*
(bool isFree ([Variable x])
                 (var bool v := false in
                      (begin
                        (if (x == this)
                            (v := true)
                            else
                            unit)
                        v)))
*)
Definition METHOD_Variable__isFree :=
 (AMethod __method__Variable__isFree
        T_Bool
        ((VarDec __arg__Variable__isFree__x (T_Class C_Variable))::nil)

        (VarDecExp (VarDec __local__Variable__isFree__v T_Bool)
                   (Expr_V (V_Bool false))
                   (SeqExp (IfExpr (Equality (Expr_X (SomeId __arg__Variable__isFree__x)) (Expr_X This))
                                   (VarAssign (SomeId __local__Variable__isFree__v) (Expr_V (V_Bool true)))
                                   (Expr_V V_Unit))
                           (Expr_X (SomeId __local__Variable__isFree__v))))).

(*
(LambdaTerm ar ([Variable oldVar] [Variable newVar])
                       (var LambdaTerm v := this in
                            (begin
                              (if (oldVar == this)
                                  (v := newVar)
                                  else
                                  unit)
                              v)))
*)
Definition METHOD_Variable__ar :=
 (AMethod __method__Variable__ar
          (T_Class C_LambdaTerm)
          ((VarDec __arg__Variable__ar__oldVar (T_Class C_Variable))::(VarDec __arg__Variable__ar__newVar (T_Class C_Variable))::nil)

          (VarDecExp (VarDec __local__Variable__ar__v (T_Class C_LambdaTerm))
                     (Expr_X (This))
                     (SeqExp (IfExpr (Equality (Expr_X (SomeId __arg__Variable__ar__oldVar)) (Expr_X This))
                                     (VarAssign (SomeId __local__Variable__ar__v) (Expr_X (SomeId __arg__Variable__ar__newVar)))
                                     (Expr_V V_Unit))
                             (Expr_X (SomeId __local__Variable__ar__v))))).

(*
(bool isAe ([LambdaTerm x])
                 (x == this))
*)
Definition METHOD_Variable__isAe :=
 (AMethod __method__Variable__isAe
          T_Bool
          ((VarDec __arg__Variable__isAe__x (T_Class C_LambdaTerm)::nil))
          (Equality (Expr_X (SomeId __arg__Variable__isAe__x)) (Expr_X This))).

(*
(LambdaTerm eval ()
        this)
*)
Definition METHOD_Variable__eval :=
 (AMethod __method__Variable__eval
          (T_Class C_LambdaTerm) (nil) (Expr_X This)).

Definition CLASS_Object : option CL := None.


Definition CLASS_Function :=
 (ClassDecl C_Function CLASS_Object (HashMap.empty T) (HashMap.empty Method)).


Definition CLASS_LambdaTerm :=
 (ClassDecl C_LambdaTerm CLASS_Object (HashMap.empty T) (HashMap.empty Method)).

Definition CLASS_Abstraction :=
 (ClassDecl C_Abstraction (Some CLASS_LambdaTerm)
            (HashMap.add __field__Abstraction__t (T_Class C_LambdaTerm)
             (HashMap.add __field__Abstraction__x (T_Class C_Variable)
             (HashMap.add __field__Abstraction__f (T_Class C_Function)
             (HashMap.empty T))))
            (HashMap.add  __method__Abstraction__construct_x_t   METHOD_Abstraction__construct_x_t
             (HashMap.add __method__Abstraction__construct_x_f   METHOD_Abstraction__construct_x_f
             (HashMap.add __method__Abstraction__construct_x_t_f METHOD_Abstraction__construct_x_t_f
             (HashMap.add __method__Abstraction__cas             METHOD_Abstraction__cas
             (HashMap.add __method__Abstraction__isFree          METHOD_Abstraction__isFree
             (HashMap.add __method__Abstraction__br              METHOD_Abstraction__br
             (HashMap.add __method__Abstraction__ar_abstraction  METHOD_Abstraction__ar_abstraction
             (HashMap.add __method__Abstraction__ar              METHOD_Abstraction__ar
             (HashMap.add __method__Abstraction__isAe            METHOD_Abstraction__isAe
             (HashMap.add __method__Abstraction__eval            METHOD_Abstraction__eval
             (HashMap.empty Method)))))))))))).

Definition CLASS_Application :=
 (ClassDecl C_Application (Some CLASS_LambdaTerm)
            (HashMap.add __field__Application__s (T_Class C_LambdaTerm)
             (HashMap.add __field__Application__t (T_Class C_LambdaTerm)
             (HashMap.empty T)))
            (HashMap.add  __method__Application__construct METHOD_Application__construct
             (HashMap.add __method__Application__cas       METHOD_Application__cas
             (HashMap.add __method__Application__isFree    METHOD_Application__isFree
             (HashMap.add __method__Application__ar        METHOD_Application__ar
             (HashMap.add __method__Application__isAe      METHOD_Application__isAe
             (HashMap.add __method__Application__eval      METHOD_Application__eval
             (HashMap.empty Method)))))))).

Definition CLASS_ChurchTest :=
 (ClassDecl C_ChurchTest CLASS_Object
            (HashMap.add __field__ChurchTest__instance (T_Class C_Church)
             (HashMap.add __field__ChurchTest__two   (T_Class C_LambdaTerm)
             (HashMap.add __field__ChurchTest__three (T_Class C_LambdaTerm)
             (HashMap.add __field__ChurchTest__five  (T_Class C_LambdaTerm)
             (HashMap.add __field__ChurchTest__sinz  (T_Class C_SetIfNotZero)
             (HashMap.empty T))))))
            (HashMap.add  __method__ChurchTest__m                                METHOD_ChurchTest__m
             (HashMap.add  __method__ChurchTest__n                               METHOD_ChurchTest__n
             (HashMap.add __method__ChurchTest__methodInvokeTest                 METHOD_ChurchTest__methodInvokeTest
             (HashMap.add __method__ChurchTest__construct                        METHOD_ChurchTest__construct
             (HashMap.add __method__ChurchTest__testZeroJavalite                 METHOD_ChurchTest__testZeroJavalite
             (HashMap.add __method__ChurchTest__testNotZeroJavalite              METHOD_ChurchTest__testNotZeroJavalite
             (HashMap.add __method__ChurchTest__testJavaliteVariableEquivalence  METHOD_ChurchTest__testJavaliteVariableEquivalence
             (HashMap.add __method__ChurchTest__testJavaliteVariableEquivalence2 METHOD_ChurchTest__testJavaliteVariableEquivalence2
             (HashMap.empty Method)))))))))).

Definition CLASS_Variable :=
 (ClassDecl C_Variable (Some CLASS_LambdaTerm)
            (HashMap.add  __field__Variable__fix T_Bool
             (HashMap.empty T))
            (HashMap.add  __method__Variable__cas       METHOD_Variable__cas
             (HashMap.add __method__Variable__isFree    METHOD_Variable__isFree
             (HashMap.add __method__Variable__ar        METHOD_Variable__ar
             (HashMap.add __method__Variable__isAe      METHOD_Variable__isAe
             (HashMap.add __method__Variable__eval      METHOD_Variable__eval
             (HashMap.empty Method))))))).

Definition CLASS_Church :=
 (ClassDecl C_Church CLASS_Object
            (HashMap.add  __field__Church__x    (T_Class C_Variable)
             (HashMap.add __field__Church__f    (T_Class C_Variable)
             (HashMap.add __field__Church__m    (T_Class C_Variable)
             (HashMap.add __field__Church__n    (T_Class C_Variable)
             (HashMap.add __field__Church__g    (T_Class C_Variable)
             (HashMap.add __field__Church__h    (T_Class C_Variable)
             (HashMap.add __field__Church__u    (T_Class C_Variable)
             (HashMap.add __field__Church__zero (T_Class C_Abstraction)
             (HashMap.add __field__Church__one  (T_Class C_Abstraction)
             (HashMap.add __field__Church__two  (T_Class C_Abstraction)
             (HashMap.add __field__Church__plus (T_Class C_Abstraction)
             (HashMap.add __field__Church__succ (T_Class C_Abstraction)
             (HashMap.add __field__Church__mult (T_Class C_Abstraction)
             (HashMap.add __field__Church__exp  (T_Class C_Abstraction)
             (HashMap.empty T)))))))))))))))
            (HashMap.add  __method__Church__construct METHOD_Church__construct
             (HashMap.add __method__Church__zero      METHOD_Church__zero
             (HashMap.add __method__Church__one       METHOD_Church__one
(*
             (HashMap.add __method__Church__plus      METHOD_Church__plus
             (HashMap.add __method__Church__succ      METHOD_Church__succ
             (HashMap.add __method__Church__mult      METHOD_Church__mult
             (HashMap.add __method__Church__exp       METHOD_Church__exp
             (HashMap.add __method__Church__pred      METHOD_Church__pred
             (HashMap.add __method__Church__minus     METHOD_Church__minus
*)
             (HashMap.empty Method))))).

Definition CLASS_SetIfNotZero :=
 (ClassDecl C_SetIfNotZero CLASS_Object
            (HashMap.add   __field__SetIfNotZero__x   (T_Class C_Variable)
             (HashMap.add  __field__SetIfNotZero__y   (T_Class C_Variable)
             (HashMap.add  __field__SetIfNotZero__bam T_Bool
             (HashMap.empty T))))
            (HashMap.add  __method__SetIfNotZero__construct METHOD_SetIfNotZero__construct
             (HashMap.add __method__SetIfNotZero__eval      METHOD_SetIfNotZero__eval
             (HashMap.add __method__SetIfNotZero__doEval    METHOD_SetIfNotZero__doEval
             (HashMap.empty Method))))).

Definition mu_Church : Mu :=
 (HashMap.add __class__Abstraction  CLASS_Abstraction
 (HashMap.add __class__Application  CLASS_Application
 (HashMap.add __class__Church       CLASS_Church
 (HashMap.add __class__ChurchTest   CLASS_ChurchTest
 (HashMap.add __class__Function     CLASS_Function
 (HashMap.add __class__LambdaTerm   CLASS_LambdaTerm
 (HashMap.add __class__SetIfNotZero CLASS_SetIfNotZero
 (HashMap.add __class__Variable     CLASS_Variable
 (HashMap.empty CL))))))))).

Definition ChurchTestProgram : P := (Program mu_Church (EntryPoint C_ChurchTest __method__ChurchTest__construct)).

Definition initialState := inject ChurchTestProgram.
Definition testNotZeroJavalite := inject_with_state initialState __method__ChurchTest__testNotZeroJavalite.
Definition mlProgram := (ExprReduces_dec testNotZeroJavalite).

Extraction "javalite.ml" mlProgram.

(* ========================================================================== *)
(* The Swap program *)

Definition __class__Swap     := (P_of_succ_nat 1).
Definition __class__SwapTest := (P_of_succ_nat 2).

Definition __field__Swap__a            := (P_of_succ_nat 3).
Definition __field__Swap__b            := (P_of_succ_nat 4).
Definition __field__SwapTest__instance := (P_of_succ_nat 5).

Definition __method__Swap__construct   := (P_of_succ_nat 6).
Definition __method__Swap__swap        := (P_of_succ_nat 7).

Definition __method__SwapTest__construct  := (P_of_succ_nat 8).
Definition __method__SwapTest__testSwap   := (P_of_succ_nat 9).

Definition __local__Swap__construct__tmp   := (P_of_succ_nat 10).
Definition __local__SwapTest__construct__v := (P_of_succ_nat 11).
Definition __local__SwapTest__testSwap__c  := (P_of_succ_nat 12).

Definition C_Swap     := (SomeClass __class__Swap).
Definition C_SwapTest := (SomeClass __class__SwapTest).

Definition METHOD_Swap__construct :=
 (AMethod __method__Swap__construct
          (T_Class C_Swap)
          nil
          (SeqExp (FieldAssign This __field__Swap__a (Expr_V (V_Bool false)))
                  (SeqExp (FieldAssign This __field__Swap__b (Expr_V (V_Bool true)))
                          (Expr_X (This))))).

Definition METHOD_Swap__swap :=
 (AMethod __method__Swap__construct
          (T_Class C_Swap)
          nil
          (VarDecExp (VarDec __local__Swap__construct__tmp T_Bool)
                     (FieldRef (Expr_X This) __field__Swap__b)
                     (SeqExp (FieldAssign This __field__Swap__b (FieldRef (Expr_X This) __field__Swap__a))
                             (FieldAssign This __field__Swap__a (Expr_X (SomeId __local__Swap__construct__tmp)))))).

Definition METHOD_SwapTest__construct :=
 (AMethod __method__SwapTest__construct
          (T_Class C_SwapTest)
          nil
          (VarDecExp (VarDec __local__SwapTest__construct__v (T_Class C_Swap))
                     (MethodInvocation (NewClass C_Swap) __method__Swap__construct nil)
                     (SeqExp (FieldAssign This __field__SwapTest__instance (Expr_X (SomeId __local__SwapTest__construct__v)))
                             (Expr_X This)))).

(*
(bool testSwap ()
                (var Swap c := (this $ instance) in
                     (begin
                       (c @ swap ())
                       (if (c $ a)
                           (if (c $ b)
                               false
                               else
                               true)
                           else
                           false))
                       ))
*)
Definition METHOD_SwapTest__testSwap :=
 (AMethod __method__SwapTest__testSwap
          T_Bool
          nil
          (VarDecExp (VarDec __local__SwapTest__testSwap__c (T_Class C_Swap))
                     (FieldRef (Expr_X This) __field__SwapTest__instance)
                     (SeqExp (MethodInvocation (Expr_X (SomeId __local__SwapTest__testSwap__c))
                                               __method__Swap__swap nil)
                             (IfExpr (FieldRef (Expr_X (SomeId __local__SwapTest__testSwap__c)) __field__Swap__a)
                                     (IfExpr (FieldRef (Expr_X (SomeId __local__SwapTest__testSwap__c)) __field__Swap__b)
                                             (Expr_V (V_Bool false))
                                             (Expr_V (V_Bool true)))
                                     (Expr_V (V_Bool false)))))).

Definition CLASS_Swap :=
 (ClassDecl C_Swap CLASS_Object
            (HashMap.add   __field__Swap__a T_Bool
             (HashMap.add  __field__Swap__b T_Bool
             (HashMap.empty T)))
            (HashMap.add   __method__Swap__construct METHOD_Swap__construct
             (HashMap.add  __method__Swap__swap METHOD_Swap__swap
             (HashMap.empty Method)))).

Definition CLASS_SwapTest :=
 (ClassDecl C_SwapTest CLASS_Object
            (HashMap.add  __field__SwapTest__instance (T_Class C_Swap) (HashMap.empty T)))
            (HashMap.add   __method__SwapTest__construct METHOD_SwapTest__construct
             (HashMap.add  __method__SwapTest__testSwap METHOD_SwapTest__testSwap
             (HashMap.empty Method))).

Definition mu_Swap : Mu :=
 (HashMap.add __class__Swap     CLASS_Swap
 (HashMap.add __class__SwapTest CLASS_SwapTest
 (HashMap.empty CL))).

Definition SwapTestProgram : P := (Program mu_Swap (EntryPoint C_SwapTest __method__SwapTest__construct)).

Definition initialState_Swap := inject SwapTestProgram.
Definition testSwap          := inject_with_state initialState_Swap __method__SwapTest__testSwap.
Definition mlProgram_Swap    := (ExprReduces_dec testSwap).

Extraction "javalite_swap.ml" mlProgram_Swap.
