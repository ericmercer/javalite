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
 | T_Bool : Boolean -> T
 | T_Unit
 | T_Class : C -> T.

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

(* (μ (CL ...))
 *)
Definition Mu := HashMap.t CL.

Inductive ProgramEntryPoint : Set :=
 | Entrypoint : C -> M -> ProgramEntryPoint.

(* (P (μ (C m)))
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

(* (η mt
      (η [x -> loc]))
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
      (pop \u03b7 k))
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
 apply bool_dec.
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
                                    | None    => Some nil
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

Definition class_list_from_object (object:HeapObject) : CList :=
 match object with
 | HeapObj c2flm => class_list_from_class_to_field_locations_map c2flm
 end.

Definition classes_of_parents_and_self (c:C) (mu:Mu) : option CList :=
 match (convert_C_to_CL c mu) with
 | None    => Some (c :: nil)
 | Some cl => Some (convert_CLList_to_CList (get_class_hierarchy_CL_to_CLList (HashMap.cardinal mu) cl mu))
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

Check create_hierarchical_location_value_list.
(*
XXX
Definition combine_list_of_lists (l:list (list (Location * V))) :=
 fold_left app l nil.
*)

Fixpoint h_extend_star_hierarchical_map (h:H) (hl:list FieldLocationMap) (dvs:list FieldValueMap) : option H :=
 match hl, dvs with
 | flm::t, fvm::t' => match create_location_value_list flm fvm with
                      | nil => h_extend_star_hierarchical_map h t t'
                      | (loc, v)::tl => let (loclist, vlist) := (split tl) in
                                        match (h_extend_star h loclist vlist) with
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

Fixpoint get_class_with_virtual_method (m:M) (classlist:list (option CL)) : option CL :=
 match classlist with
 | nil        => None
 | None::t    => None (* since classlist should be a hierarchy list *)
 | Some cl::t => match method_lookup m cl with
                 | Some method => Some cl
                 | None        => get_class_with_virtual_method m t
                 end
 end.

Fixpoint get_virtual_method (m:M) (classlist:list (option CL)) : option Method :=
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
 | T_Class c => V_Pointer Null
 | T_Unit    => V_Unit
 | T_Bool _  => V_Bool false
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

(* "New" helpers *)
Definition build_class_loc_lists (hcl:CList)
                                 (hfl:list FieldTypeMap)
                                 (hl:list LocationList) : ClassToFieldLocationsMap := HashMap.empty FieldLocationMap.

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
 (* Pop \u03b7 (close scope) *)

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
         (m:M) (varlist:list V) (c c_0 c_p C_t:C) (loc loc_o:Location) (loclist:LocationList)
         (methodvars:IdList) (obj1:HeapObject) (arglist:ArgumentList) (t:T)
         (clist:CList) (classlist:list (option CL)) (CL_t:CL),
   (h_lookup h loc)                 = Some (Hv_object obj1) ->
   (class_list_from_object obj1)    = (c_0 :: c_p :: clist) ->

   (*
   Ignore C_0 which is always object and look up the method starting in C_p
   Find the last M declaration before the zero or more trailing "error"s
   *)
   (convert_CList_to_CLList mu (c_p::clist))   = classlist ->
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

   (classes_of_parents_and_self c mu)                     = Some classlist        ->
   (get_fields_of_parents_and_self_C c mu)                = hierarchicalfieldlist ->
   (get_hierarchical_type_map hierarchicalfieldlist)      = hierarchicaltypelist  ->
   (get_hierarchical_default_values hierarchicaltypelist) = defaultvalues         ->

   (h_malloc_n_star h (get_value_lengths defaultvalues))  = hierarchicallocations ->
   (create_hierarchical_field_location_map hierarchicallocations defaultvalues)  = hierarchicalfieldlocmap  ->
   (h_extend_star_hierarchical_map h hierarchicalfieldlocmap defaultvalues)      = Some h_0 ->

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

 remember (class_list_from_object obj1) as clist.
 destruct clist.

 dispatch_invalid_state_with_congruence.

 destruct clist.
 dispatch_invalid_state_with_congruence.

 remember (convert_CList_to_CLList m0 (c2::clist)) as classlist.
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
 apply (ER_MethodInvocationRaw m0 h h_0 h_tmp e eta_0 e0 c m l c0 c1 c2 C_t
                               loc loc_o loclist methodvars obj1 a t clist
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
