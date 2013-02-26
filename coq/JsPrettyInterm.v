Set Implicit Arguments.
Require Export JsSyntax JsSyntaxAux JsPreliminary.

(**************************************************************)
(** ** Implicit Types -- copied from JsPreliminary *)

Implicit Type b : bool.
Implicit Type n : number.
Implicit Type k : int.
Implicit Type s : string.
Implicit Type i : literal.
Implicit Type l : object_loc.
Implicit Type w : prim.
Implicit Type v : value.
Implicit Type r : ref.
Implicit Type B : builtin.
Implicit Type T : type.

Implicit Type rt : restype.
Implicit Type rv : resvalue.
Implicit Type lab : label.
Implicit Type labs : label_set.
Implicit Type R : res.
Implicit Type o : out.

Implicit Type x : prop_name.
Implicit Type str : strictness_flag.
Implicit Type m : mutability.
Implicit Type Ad : attributes_data.
Implicit Type Aa : attributes_accessor.
Implicit Type A : attributes.
Implicit Type Desc : descriptor.
Implicit Type D : full_descriptor.

Implicit Type L : env_loc.
Implicit Type E : env_record.
Implicit Type Ed : decl_env_record.
Implicit Type X : lexical_env.
Implicit Type O : object.
Implicit Type S : state.
Implicit Type C : execution_ctx.
Implicit Type P : object_properties_type.

Implicit Type e : expr.
Implicit Type p : prog.
Implicit Type t : stat.


(****************************************************************)
(** ** Intermediate expression for the Pretty-Big-Step semantic *)

(** Grammar of extended expressions *)

Inductive ext_expr :=

  (** Extended expressions include expressions *)

  | expr_basic : expr -> ext_expr

  (** Extended expressions for lists of expressions *)

  | expr_list_then : (list value -> ext_expr) -> list expr -> ext_expr (* [expr_list_then k es] evaluates all the expressions of [es], then call [k] on the generated list of value. *)
  | expr_list_then_1 : (list value -> ext_expr) -> list value -> list expr -> ext_expr (* [expr_list_then_1 k vs es] has already computed all the values [vs], and starts executing [es]. *)
  | expr_list_then_2 : (list value -> ext_expr) -> list value -> out -> list expr -> ext_expr (* [expr_list_then_2 k vs o es] has evaluated the first of the expressions left, that has returned [o]. *)

  (** Extended expressions associated with primitive expressions *)

  | expr_object_0 : out -> propdefs -> ext_expr
  | expr_object_1 : object_loc -> propdefs -> ext_expr
  | expr_object_2 : object_loc -> string -> propbody -> propdefs -> ext_expr (* TODO: check the type! *)
  | expr_object_3 : object_loc -> string -> out -> propdefs -> ext_expr
  | expr_object_3_val : object_loc -> string -> out -> propdefs -> ext_expr
  | expr_object_3_get : object_loc -> string -> out -> propdefs -> ext_expr
  | expr_object_3_set : object_loc -> string -> out -> propdefs -> ext_expr
  | expr_object_4 : object_loc -> string -> attributes -> propdefs -> ext_expr
  | expr_object_5 : object_loc -> propdefs -> out -> ext_expr
  
  | expr_function_1 : string -> list string -> funcbody -> env_loc -> lexical_env -> out -> ext_expr
  | expr_function_2 : string -> env_loc -> out -> ext_expr
  | expr_function_3 : object_loc -> out -> ext_expr
  
  | expr_access_1 : out -> expr -> ext_expr (* The left expression has been executed *)
  | expr_access_2 : value -> out -> ext_expr (* The right expression is executed. *)
  | expr_access_3 : value -> out -> value -> ext_expr
  | expr_access_4 : value -> out -> ext_expr

  | expr_new_1 : out -> list expr -> ext_expr (* The function has been evaluated. *)
  | expr_new_2 : object_loc -> funccode -> list value -> ext_expr (* The arguments too. *)
  | expr_new_3 : object_loc -> out -> ext_expr (* The call has been executed. *)
  
  | expr_call_1 : out -> list expr -> ext_expr (* The function has been evaluated. *)
  | expr_call_2 : res -> list expr -> out -> ext_expr 
  | expr_call_3 : res -> value -> list value -> ext_expr (* The arguments have been executed. *)
  | expr_call_4 : object_loc -> list value -> out -> ext_expr (* The call has been executed. *)

  | expr_unary_op_1 : unary_op -> out -> ext_expr (* The argument have been executed. *)
  | expr_unary_op_2 : unary_op -> value -> ext_expr (* The argument is a value. *)
  | expr_delete_1 : out -> ext_expr
  | expr_delete_2 : ref -> out -> ext_expr
  | expr_typeof_1 : out -> ext_expr
  | expr_typeof_2 : out -> ext_expr
  | expr_prepost_1 : unary_op -> out -> ext_expr
  | expr_prepost_2 : unary_op -> res -> out -> ext_expr
  | expr_prepost_3 : unary_op -> res -> out -> ext_expr
  | expr_prepost_4 : value -> out -> ext_expr
  | expr_unary_op_neg_1 : out -> ext_expr
  | expr_unary_op_bitwise_not_1 : int -> ext_expr
  | expr_unary_op_not_1 : out -> ext_expr
  | expr_conditional_1 : out -> expr -> expr -> ext_expr
  | expr_conditional_1': out -> expr -> expr -> ext_expr

  | expr_binary_op_1 : binary_op -> out -> expr -> ext_expr
  | expr_binary_op_2 : binary_op -> value -> out -> ext_expr
  | expr_binary_op_3 : binary_op -> value -> value -> ext_expr
  | expr_binary_op_add_1 : value -> value -> ext_expr
  | expr_binary_op_add_string_1 : value -> value -> ext_expr
  | expr_puremath_op_1 : (number -> number -> number) -> value -> value -> ext_expr
  | expr_shift_op_1 : (int -> int -> int) -> value -> int -> ext_expr
  | expr_shift_op_2 : (int -> int -> int) -> int -> int -> ext_expr
  | expr_inequality_op_1 : bool -> bool -> value -> value -> ext_expr
  | expr_inequality_op_2 : bool -> bool -> value -> value -> ext_expr
  | expr_binary_op_in_1 : object_loc -> out -> ext_expr
  | expr_binary_op_disequal_1 : out -> ext_expr
  | spec_equal : value -> value -> ext_expr
  | spec_equal_1 : type -> type -> value -> value -> ext_expr
  | spec_equal_2 : bool -> ext_expr
  | spec_equal_3 : value -> (value -> ext_expr) -> value -> ext_expr
  | spec_equal_4 : value -> out -> ext_expr
  | expr_bitwise_op_1 : (int -> int -> int) -> value -> int -> ext_expr
  | expr_bitwise_op_2 : (int -> int -> int) -> int -> int -> ext_expr
  | expr_lazy_op_1 : bool -> out -> expr -> ext_expr
  | expr_lazy_op_2 : bool -> value -> out -> expr -> ext_expr

  | expr_assign_1 : out -> option binary_op -> expr -> ext_expr
  | expr_assign_2 : res -> out -> binary_op -> expr -> ext_expr
  | expr_assign_3 : res -> value -> binary_op -> out -> ext_expr
  | expr_assign_4 : res -> out -> ext_expr
  | expr_assign_5 : value -> out -> ext_expr

(* TODO: we could separate ext_spec from ext_expr,
   and separate red_spec from red_expr *)

  (** Extended expressions for conversions *)

  | spec_to_primitive : value -> option preftype -> ext_expr
  | spec_to_boolean : value -> ext_expr
  | spec_to_number : value -> ext_expr
  | spec_to_number_1 : out -> ext_expr
  | spec_to_integer : value -> ext_expr
  | spec_to_integer_1 : out -> ext_expr
  | spec_to_string : value -> ext_expr
  | spec_to_string_1 : out -> ext_expr
  | spec_to_object : value -> ext_expr

  | spec_to_int32 : value -> (int -> ext_expr) -> ext_expr
  | spec_to_int32_1 : out -> (int -> ext_expr) -> ext_expr
  | spec_to_uint32 : value -> (int -> ext_expr) -> ext_expr
  | spec_to_uint32_1 : out -> (int -> ext_expr) -> ext_expr
  | spec_check_object_coercible : value -> ext_expr

  | spec_convert_twice : ext_expr -> ext_expr -> (value -> value -> ext_expr) -> ext_expr
  | spec_convert_twice_1 : out -> ext_expr -> (value -> value -> ext_expr) -> ext_expr
  | spec_convert_twice_2 : out -> (value -> ext_expr) -> ext_expr

  (** Extended expressions for comparison *)

  | spec_eq : value -> value -> ext_expr
  | spec_eq0 : value -> value -> ext_expr
  | spec_eq1 : value -> value -> ext_expr
  | spec_eq2 : ext_expr -> value -> value -> ext_expr

  (** Extended expressions for operations on objects *)

  (* todo *)
  | spec_object_get_own_prop : object_loc -> prop_name -> (full_descriptor -> ext_expr) -> ext_expr
  | spec_object_get_own_prop_1 : builtin -> object_loc -> prop_name -> (full_descriptor -> ext_expr) -> ext_expr
  | spec_object_get_own_prop_2 : object_loc -> prop_name -> (full_descriptor -> ext_expr) -> option attributes -> ext_expr
  | spec_object_get_prop : object_loc -> prop_name -> (full_descriptor -> ext_expr) -> ext_expr
  | spec_object_get_prop_1 : builtin -> object_loc -> prop_name -> (full_descriptor -> ext_expr) -> ext_expr
  | spec_object_get_prop_2 : object_loc -> prop_name -> (full_descriptor -> ext_expr) -> full_descriptor -> ext_expr
  | spec_object_get_prop_3 : object_loc -> prop_name -> (full_descriptor -> ext_expr) -> value -> ext_expr
  | spec_object_get : value -> prop_name -> ext_expr
  | spec_object_get_1 : builtin -> value -> object_loc -> prop_name -> ext_expr
  | spec_object_get_2 : object_loc -> object_loc -> full_descriptor -> ext_expr
  | spec_object_get_3 : object_loc -> object_loc -> value -> ext_expr

  | spec_object_can_put : object_loc -> prop_name -> ext_expr
  | spec_object_can_put_1 : builtin -> object_loc -> prop_name -> ext_expr
  | spec_object_can_put_2 : object_loc -> prop_name -> full_descriptor -> ext_expr
  (* Daiva: Not needed? *)
  (*| spec_object_can_put_3 : object_loc -> prop_name -> bool -> ext_expr*)
  | spec_object_can_put_4 : object_loc -> prop_name -> value -> ext_expr
  | spec_object_can_put_5 : object_loc -> full_descriptor -> ext_expr
  | spec_object_can_put_6 : attributes_data -> bool -> ext_expr

  | spec_object_put : value -> prop_name -> value -> bool -> ext_expr
  | spec_object_put_1 : builtin -> value -> object_loc -> prop_name -> value -> bool -> ext_expr
  | spec_object_put_2 : value -> object_loc -> prop_name -> value -> bool -> out -> ext_expr
  | spec_object_put_3 : value -> object_loc -> prop_name -> value -> bool -> full_descriptor -> ext_expr
  | spec_object_put_4 : value -> object_loc -> prop_name -> value -> bool -> full_descriptor -> ext_expr
  | spec_object_put_5 : out -> ext_expr

  | spec_object_has_prop : object_loc -> prop_name -> ext_expr
  | spec_object_has_prop_1 : builtin -> object_loc -> prop_name -> ext_expr
  | spec_object_has_prop_2 : full_descriptor -> ext_expr

  | spec_object_delete : object_loc -> prop_name -> bool -> ext_expr
  | spec_object_delete_1 : builtin -> object_loc -> prop_name -> bool -> ext_expr
  | spec_object_delete_2 : object_loc -> prop_name -> bool -> full_descriptor -> ext_expr
  | spec_object_delete_3 : object_loc -> prop_name -> bool -> bool -> ext_expr

  | spec_object_default_value : object_loc -> option preftype -> ext_expr
  | spec_object_default_value_1 : builtin -> object_loc -> option preftype -> ext_expr
  | spec_object_default_value_2 : object_loc -> preftype -> preftype -> ext_expr
  | spec_object_default_value_3 : object_loc -> preftype -> ext_expr
  | spec_object_default_value_4 : ext_expr
  | spec_object_default_value_sub_1 : object_loc -> string -> ext_expr -> ext_expr
  | spec_object_default_value_sub_2 : object_loc -> out -> ext_expr -> ext_expr
  | spec_object_default_value_sub_3 : out -> ext_expr -> ext_expr

  | spec_object_define_own_prop : object_loc -> prop_name -> descriptor -> bool -> ext_expr
  | spec_object_define_own_prop_1 : builtin -> object_loc -> prop_name -> descriptor -> bool -> ext_expr
  | spec_object_define_own_prop_2 : object_loc -> prop_name -> descriptor -> bool -> full_descriptor -> ext_expr
  | spec_object_define_own_prop_3 : object_loc -> prop_name -> descriptor -> bool -> full_descriptor -> bool -> ext_expr
  | spec_object_define_own_prop_4 : object_loc -> prop_name -> attributes -> descriptor -> bool -> ext_expr
  | spec_object_define_own_prop_5 : object_loc -> prop_name -> attributes -> descriptor -> bool -> ext_expr
  | spec_object_define_own_prop_6a : object_loc -> prop_name -> attributes -> descriptor -> bool -> ext_expr
  | spec_object_define_own_prop_6b : object_loc -> prop_name -> attributes -> descriptor -> bool -> ext_expr
  | spec_object_define_own_prop_6c : object_loc -> prop_name -> attributes -> descriptor -> bool -> ext_expr  
  | spec_object_define_own_prop_reject : bool -> ext_expr
  | spec_object_define_own_prop_write : object_loc -> prop_name -> attributes -> descriptor -> bool -> ext_expr
(* Daniele: FIX                                                                                
  | spec_object_iter_own_prop : object_loc -> (prop_name -> full_descriptor -> ext_expr -> ext_expr) -> ext_expr -> ext_expr
  | spec_object_iter_own_prop_1 : list (prop_name * attributes) -> ext_expr -> ext_expr -> ext_expr
*)
  | spec_prim_value_get : value -> prop_name -> ext_expr
  | spec_prim_value_get_1 : value -> prop_name -> out -> ext_expr
  
  | spec_prim_value_put : value -> prop_name -> value -> bool -> ext_expr
  | spec_prim_value_put_1 : prim -> prop_name -> value -> bool -> out -> ext_expr

  (*
  | spec_object_put_special : value -> prop_name -> value -> bool -> ext_expr

  | spec_object_object_get : object_loc -> prop_name -> ext_expr
  | spec_object_object_get_1 : object_loc -> full_descriptor -> ext_expr
  | spec_object_object_get_2 : object_loc -> option value -> ext_expr
  | spec_object_function_get : object_loc -> prop_name -> ext_expr
  | spec_object_function_get_1 : object_loc -> prop_name -> out -> ext_expr
  *)


  (** Extended expressions for operations on references *)

  | spec_get_value : resvalue -> ext_expr
  | spec_put_value : resvalue -> value -> ext_expr

  (** Shorthand for calling [red_expr] then [ref_get_value] *)

  | spec_expr_get_value : expr -> ext_expr 
  | spec_expr_get_value_1 : out -> ext_expr
  | spec_expr_get_value_conv : (value -> ext_expr) -> expr -> ext_expr 
  | spec_expr_get_value_conv_1 : (value -> ext_expr) -> out -> ext_expr 

  (** Extended expressions for operations on environment records *)

  | spec_env_record_has_binding : env_loc -> prop_name -> ext_expr
  | spec_env_record_has_binding_1 : env_loc -> prop_name -> env_record -> ext_expr
  | spec_env_record_get_binding_value : env_loc -> prop_name -> bool -> ext_expr
  | spec_env_record_get_binding_value_1 : env_loc -> prop_name -> bool -> env_record -> ext_expr
  | spec_env_record_get_binding_value_2 : prop_name -> bool -> object_loc -> out -> ext_expr
  (* TODO: is it just a leftover form the renaming? *)
  | spec_env_record_set_binding_value : env_loc -> prop_name -> value -> bool -> ext_expr

  | spec_env_record_create_immutable_binding : env_loc -> prop_name -> ext_expr
  | spec_env_record_initialize_immutable_binding : env_loc -> prop_name -> value -> ext_expr
  | spec_env_record_create_mutable_binding : env_loc -> prop_name -> option bool -> ext_expr
  | spec_env_record_create_mutable_binding_1 : env_loc -> prop_name -> bool -> env_record -> ext_expr
  | spec_env_record_create_mutable_binding_2 : env_loc -> prop_name -> bool -> object_loc -> out -> ext_expr
  | spec_env_record_create_mutable_binding_3 : out -> ext_expr
  | spec_env_record_set_mutable_binding : env_loc -> prop_name -> value -> bool -> ext_expr
  | spec_env_record_set_mutable_binding_1 : env_loc -> prop_name -> value -> bool -> env_record -> ext_expr
  | spec_env_record_delete_binding : env_loc -> prop_name -> ext_expr
  | spec_env_record_delete_binding_1 : env_loc -> prop_name -> env_record -> ext_expr

  | spec_env_record_create_set_mutable_binding : env_loc -> prop_name -> option bool -> value -> bool -> ext_expr
  | spec_env_record_create_set_mutable_binding_1 : out -> env_loc -> prop_name -> value -> bool -> ext_expr

  | spec_env_record_implicit_this_value : env_loc -> ext_expr
  | spec_env_record_implicit_this_value_1 : env_loc -> env_record -> ext_expr

  (** Extended expressions for operations on lexical environments *)

  | spec_lexical_env_get_identifier_ref : lexical_env -> prop_name -> bool -> ext_expr
  | spec_lexical_env_get_identifier_ref_1 : env_loc -> lexical_env -> prop_name -> bool -> ext_expr
  | spec_lexical_env_get_identifier_ref_2 : env_loc -> lexical_env -> prop_name -> bool -> out -> ext_expr

  (** Extented expressions for eval *)
  
  | spec_entering_eval_code : funcbody -> ext_expr
  
  | spec_call_global_eval_1 : value -> ext_expr
  | spec_call_global_eval_1_2 : prog -> ext_expr
  | spec_call_global_eval_1_3 : out -> ext_expr

  (** Extended expressions for function calls *)

  | spec_entering_func_code : object_loc -> value -> list value -> ext_expr
  | spec_entering_func_code_1 : object_loc -> list value -> funcbody -> value -> strictness_flag -> ext_expr
  | spec_entering_func_code_2 : object_loc -> list value -> funcbody -> out -> ext_expr
  | spec_entering_func_code_3 : object_loc -> list value -> strictness_flag -> funcbody -> value -> ext_expr
  
  | spec_binding_instantiation_formal_params : (list value -> env_loc -> ext_expr) -> list value -> env_loc -> list string -> ext_expr
  | spec_binding_instantiation_formal_params_1 : (list value -> env_loc -> ext_expr) -> list value -> env_loc -> string -> list string -> value -> out -> ext_expr
  | spec_binding_instantiation_formal_params_2 : (list value -> env_loc -> ext_expr) -> list value -> env_loc -> list string -> out -> ext_expr
  | spec_binding_instantiation_function_decls : (env_loc -> ext_expr) -> list value -> env_loc -> list funcdecl -> bool -> out -> ext_expr
  | spec_binding_instantiation_function_decls_1 : (env_loc -> ext_expr) -> list value -> env_loc -> funcdecl -> list funcdecl -> strictness_flag -> bool -> out -> ext_expr
  | spec_binding_instantiation_function_decls_2 : (env_loc -> ext_expr) -> list value -> env_loc -> funcdecl -> list funcdecl -> strictness_flag -> object_loc -> bool -> out -> ext_expr
  | spec_binding_instantiation_function_decls_3 : (env_loc -> ext_expr) -> list value -> funcdecl -> list funcdecl -> strictness_flag -> object_loc -> bool -> bool -> full_descriptor -> ext_expr
  | spec_binding_instantiation_function_decls_4 : (env_loc -> ext_expr) -> list value -> env_loc -> funcdecl -> list funcdecl -> strictness_flag -> object_loc -> bool -> out -> ext_expr
  | spec_binding_instantiation_arg_obj : (out -> ext_expr) -> codetype -> option object_loc -> prog -> list string -> list value -> env_loc -> out -> ext_expr
  | spec_binding_instantiation_arg_obj_1 : (out -> ext_expr) -> prog -> env_loc -> strictness_flag -> out -> ext_expr
  | spec_binding_instantiation_arg_obj_2 : (out -> ext_expr) -> prog -> env_loc -> object_loc -> out -> ext_expr
  | spec_binding_instantiation_var_decls : env_loc -> list string -> bool -> out -> ext_expr
  | spec_binding_instantiation_var_decls_1 : env_loc -> string -> list string -> bool -> out -> ext_expr
  | spec_execution_ctx_binding_instantiation : codetype -> option object_loc -> prog -> list value -> ext_expr
  | spec_execution_ctx_binding_instantiation_1 : codetype -> option object_loc -> prog -> list value -> env_loc -> ext_expr 
  | spec_execution_ctx_binding_instantiation_2 : codetype -> option object_loc -> prog -> list string -> list value -> env_loc -> ext_expr
  | spec_execution_ctx_binding_instantiation_3 : codetype -> option object_loc -> prog -> list string -> list value -> bool -> env_loc -> ext_expr
  | spec_execution_ctx_binding_instantiation_4 : prog -> bool -> env_loc -> out -> ext_expr
  
  | spec_create_arguments_object : object_loc -> list string -> list value -> env_loc -> strictness_flag -> ext_expr
  
  (* Execution of "has_instance" *)

  | spec_object_has_instance : builtin -> object_loc -> value -> ext_expr
  | spec_object_has_instance_1 : object_loc -> out -> ext_expr

  (* Throwing of errors *)

  | spec_error : builtin -> ext_expr (* todo: reduction rules *)
  | spec_error_or_cst : bool -> builtin -> value -> ext_expr (* todo: reduction rules *)
  | spec_error_or_void : bool -> builtin -> ext_expr (* todo: reduction rules *)
  
  | spec_init_throw_type_error : ext_expr
  | spec_init_throw_type_error_1 : out -> ext_expr

  (* Object creation and calling continuation with object address *)

  | spec_new_object : (object_loc -> ext_expr) -> ext_expr
  | spec_new_object_1 : out -> (object_loc -> ext_expr) -> ext_expr
  
  | spec_prim_new_object : prim -> ext_expr

  (* Auxiliary reduction for creating function object steps 16 - 18 *) 
  | spec_creating_function_object_proto : (out -> ext_expr) -> object_loc -> out -> ext_expr
  | spec_creating_function_object_proto_1 : (out -> ext_expr) -> object_loc -> out -> ext_expr
  | spec_creating_function_object_proto_2 : (out -> ext_expr) -> object_loc -> object_loc -> out -> ext_expr

  | spec_creating_function_object : list string -> funcbody -> lexical_env -> strictness_flag -> ext_expr
  | spec_creating_function_object_1 : strictness_flag -> object_loc -> out -> ext_expr
  | spec_creating_function_object_2 : object_loc -> out -> ext_expr
  | spec_creating_function_object_3 : object_loc -> out -> ext_expr
  
  (* Function creation in give execution context*)
  | spec_create_new_function_in :  execution_ctx -> list string -> funcbody -> ext_expr

  (* TODO: Check if object_loc or value could be None *)
  (* TODO: get rid of this: | spec_call : builtin -> option object_loc -> option value -> list value -> ext_expr *)
  | spec_call : object_loc -> value -> list value -> ext_expr (* object with the call method, this value, arguments *)
  | spec_call_1 : builtin -> object_loc -> value -> list value -> ext_expr
  
  | spec_call_builtin : builtin -> list value -> ext_expr
  
  | spec_op_function_call : object_loc -> value -> list value -> ext_expr
  | spec_op_function_call_1 : object_loc -> out -> ext_expr
  | spec_op_function_call_2 : out -> ext_expr
  
  | spec_constructor : builtin -> option object_loc -> list value -> ext_expr
  
  | spec_constructor_builtin : builtin -> list value -> ext_expr
  
  | spec_function_constructor : object_loc -> list value -> ext_expr
  | spec_function_constructor_1 : object_loc -> list value -> out -> ext_expr
  | spec_function_constructor_2 : object_loc -> out -> ext_expr

  (** Extended expressions for calling global object builtin functions *)
  (* TODO: rename all the spec_call into spec_builtin *)
  
  | spec_call_global_is_nan_1 : out -> ext_expr
  | spec_call_global_is_finite_1 : out -> ext_expr
 
  | spec_call_object_call_1 : value -> ext_expr
  | spec_call_object_new_1 : value -> ext_expr
  | spec_call_object_get_prototype_of_1 : value -> ext_expr
  | spec_call_object_is_extensible_1 : value -> ext_expr
  | spec_call_object_is_sealed_1 : value -> ext_expr
  | spec_call_object_is_sealed_2 : prop_name -> full_descriptor -> ext_expr -> ext_expr
  | spec_call_object_is_sealed_3 : object_loc -> ext_expr
  | spec_call_object_prevent_extensions_1 : value -> ext_expr

  | spec_call_object_proto_to_string_1 : value -> ext_expr
  | spec_call_object_proto_to_string_2 : out -> ext_expr
  | spec_call_object_proto_is_prototype_of_2_1 : value -> ext_expr
  | spec_call_object_proto_is_prototype_of_2_2 : out -> object_loc -> ext_expr
  | spec_call_object_proto_is_prototype_of_2_3 : object_loc -> object_loc -> ext_expr 
  | spec_call_object_proto_is_prototype_of_2_4 : object_loc -> value -> ext_expr 
 
  | spec_call_object_proto_prop_is_enumerable_1 : value -> ext_expr
  | spec_call_object_proto_prop_is_enumerable_2 : out -> ext_expr
  | spec_call_object_proto_prop_is_enumerable_3 : out -> string -> ext_expr
  | spec_call_object_proto_prop_is_enumerable_4 : full_descriptor -> ext_expr
      
  | spec_call_bool_new_1 : out -> ext_expr 
  | spec_call_bool_proto_to_string_1 : out -> ext_expr
  | spec_call_bool_proto_value_of_1 : value -> ext_expr
  | spec_call_bool_proto_value_of_2 : value -> ext_expr
 
  | spec_call_number_proto_to_string_1 : value -> list value -> ext_expr
  | spec_call_number_proto_to_string_2 : value -> out -> ext_expr
  | spec_call_number_new_1 : out -> ext_expr
  | spec_call_number_proto_value_of_1 : value -> ext_expr
 

  (** Special state for returning an outcome *)   

  | spec_returns : out -> ext_expr

(** Grammar of extended statements *)

with ext_stat :=

  (** Extended expressions include statements *)

  | stat_basic : stat -> ext_stat

  (** Extended statements associated with primitive statements *)

  | stat_block_1 : resvalue -> list stat -> ext_stat 
  | stat_block_2 : resvalue -> out -> list stat -> ext_stat
  | stat_block_3 : out -> list stat -> ext_stat

  | stat_label_1 : label -> out -> ext_stat

  | stat_var_decl_1 : out -> list (string * option expr) -> ext_stat
  | stat_var_decl_item : (string * option expr) -> ext_stat
  | stat_var_decl_item_1 : string -> out -> expr -> ext_stat
  | stat_var_decl_item_2 : string -> ref -> out -> ext_stat
  | stat_var_decl_item_3 : string -> out -> ext_stat

  | stat_if_1 : value -> stat -> option stat -> ext_stat

  | stat_while_1 : label_set -> expr -> stat -> resvalue -> ext_stat 
  | stat_while_2 : label_set -> expr -> stat -> resvalue -> value -> ext_stat 
  | stat_while_3 : label_set -> expr -> stat -> resvalue -> out -> ext_stat 
  | stat_while_4 : label_set -> expr -> stat -> resvalue -> res -> ext_stat 
  
  | stat_do_while_1 : label_set -> stat ->  expr -> resvalue -> ext_stat 
  | stat_do_while_2 : label_set -> stat ->  expr -> resvalue -> out -> ext_stat
  | stat_do_while_3 : label_set -> stat ->  expr -> resvalue -> res -> ext_stat 
  | stat_do_while_4 : label_set -> stat ->  expr -> resvalue -> ext_stat
  | stat_do_while_5 : label_set -> stat ->  expr -> resvalue -> value -> ext_stat

(* LATER
  | stat_for_in_1 : expr -> stat -> out -> ext_stat
  | stat_for_in_2 : expr -> stat -> out -> ext_stat
  | stat_for_in_3 : expr -> stat -> out -> ext_stat
  | stat_for_in_4 : expr -> stat -> object_loc -> option res -> option out -> set prop_name -> set prop_name -> ext_stat (* TODO: define prop_names for [set prop_name] *)
  | stat_for_in_5 : expr -> stat -> object_loc -> option res -> option out -> set prop_name -> set prop_name -> prop_name -> ext_stat
  | stat_for_in_6 : expr -> stat -> object_loc -> option res -> option out -> set prop_name -> set prop_name -> prop_name -> ext_stat
  | stat_for_in_7 : expr -> stat -> object_loc -> option res -> option out -> set prop_name -> set prop_name -> out -> ext_stat
  | stat_for_in_8 : expr -> stat -> object_loc -> option res -> option out -> set prop_name -> set prop_name -> out -> ext_stat
  | stat_for_in_9 : expr -> stat -> object_loc -> option res -> option out -> set prop_name -> set prop_name -> res -> ext_stat
*)

  | stat_with_1 : stat -> value -> ext_stat (* The expression have been executed. *)

  | stat_throw_1 : out -> ext_stat (* The expression have been executed. *)

  | stat_return_1 : out -> ext_stat (* The expression have been executed. *)

  | stat_try_1 : out -> option (string*stat) -> option stat -> ext_stat (* The try block has been executed. *)
  | stat_try_2 : out -> lexical_env -> stat -> option stat -> ext_stat (* The catch block is actived and will be executed. *)
  | stat_try_3 : out -> option stat -> ext_stat (* The try catch block has been executed:  there only stay an optional finally. *)
  | stat_try_4 : res -> option stat -> ext_stat (* The try catch block has been executed:  there only stay an optional finally. *)
  | stat_try_5 : res -> out -> ext_stat (* The finally has been executed. *)
  
  (* Auxiliary forms for performing [red_expr] then [ref_get_value] and a conversion *)

  | spec_expr_get_value_conv_stat : expr -> (value -> ext_expr) -> (value -> ext_stat) -> ext_stat
  | spec_expr_get_value_conv_stat_1 : out -> (value -> ext_expr) -> (value -> ext_stat) -> ext_stat
  | spec_expr_get_value_conv_stat_2 : out -> (value -> ext_stat) -> ext_stat
 

(** Grammar of extended programs *)

with ext_prog :=
 
  | prog_basic : prog -> ext_prog
  | prog_1 : resvalue -> elements -> ext_prog
  | prog_2 : resvalue -> out -> elements -> ext_prog
  | prog_3 : out -> elements -> ext_prog
.


(** Coercions *)

Coercion expr_basic : expr >-> ext_expr.
Coercion stat_basic : stat >-> ext_stat.
Coercion prog_basic : prog >-> ext_prog.


(** Shorthand for calling toPrimitive without prefered type *)

Definition spec_to_primitive_auto v :=
  spec_to_primitive v None.


(**************************************************************)
(** ** Extracting outcome from an extended expression. *)

(** The [out_of_ext_*] family of definitions is used by
    the generic abort rule, which propagates exceptions,
    and divergence, break and continues. *)

Definition out_of_ext_expr (e : ext_expr) : option out :=
  match e with
  (* TODO: update later
  | expr_basic _ => None
  | expr_list_then _ _ => None
  | expr_list_then_1 _ _ _ => None
  | expr_list_then_2 _ _ o _ => Some o
  | expr_object_1 _ _ _ => None
  | expr_access_1 o _ => Some o
  | expr_access_2 _ o => Some o
  | expr_new_1 o _ => Some o
  | expr_new_2 _ _ _ => None
  | expr_new_3 _ o => Some o
  | expr_call_1 o _ => Some o
  | expr_call_2 _ _ _ => None
  | expr_call_3 _ _ _ => None
  | expr_call_4 o => Some o
  | expr_unary_op_1 _ o => Some o
  | expr_unary_op_2 _ _ => None
  | expr_binary_op_1 o _ _ => Some o
  | expr_binary_op_2 _ _ _ _ => None
     (* TODO (Arthur does not understand this comment:
        If the `option out' is not `None' then the `out' is returned anyway,
        independently of wheither it aborts or not. *)
        (*
  | expr_binary_op_3 _ _ _ => None
  | expr_binary_op_add_1 _ _ => None
  *)
  | expr_assign_1 o _ _ => Some o
  | expr_assign_2 _ o => Some o
  | expr_assign_2_op _ _ _ o => Some o
  | spec_to_number_1 o => Some o
  | spec_to_integer_1 o => Some o
  | spec_to_string_1 o => Some o
  | spec_object_default_value_1 _ _ _ => None
  | spec_object_default_value_3 _ _ => None
  | spec_object_default_value_4 => None
  | spec_object_default_value_sub_1 _ _ _ => None
  | spec_object_default_value_sub_2 _ _ _ => None
  | spec_convert_twice _ _ _ => None
  | spec_convert_twice_1 o _ _ => Some o
  | spec_convert_twice_2 o _ => Some o
  (* TODO: missing new extended forms here *)
  *)
  | _ => None
  (* TODO: remove the line above to ensure that nothing forgotten *)
  end.

Definition out_of_ext_stat (p : ext_stat) : option out :=
  match p with
  (* TODO: update later
  | stat_basic _ => None
  | stat_seq_1 o _ => Some o
  | stat_var_decl_1 o => Some o
  | stat_if_1 o _ _ => Some o
  | stat_if_2 o _ _ => out_some_out o
  | stat_if_3 o _ _ => out_some_out o
  | stat_while_1 _ o _ => Some o
  | stat_while_2 _ _ _ => None
  | stat_while_3 _ _ o => Some o
  | stat_throw_1 o => Some o
  | stat_try_1 o _ _=> Some o
  | stat_try_2 _ _ _ => None
  | stat_try_3 o _ => Some o
  | stat_try_4 _ o => Some o
  | stat_with_1 o _ => Some o
  *)
  | _ => None
  end.

Definition out_of_ext_prog (p : ext_prog) : option out :=
  match p with
  (* TODO update later
  | elements_1 _ => None
  | elements_2 _ o _ => Some o
  *)
  | _ => None
  end.


(**************************************************************)
(** ** Rules for propagating aborting expressions *)

(** Definition of a result of type normal *)

Definition res_is_normal R := 
  res_type R = restype_normal.

(** Definition of aborting outcomes: diverging outcomes,
    and terminating outcomes that are not of type "normal". *)

Inductive abort : out -> Prop :=
  | abort_div :
      abort out_div
  | abort_not_normal : forall S R,
      ~ res_is_normal R ->
      abort (out_ter S R).

(** Definition of the behaviors caught by an exception handler,
    and thus not propagated by the generic abort rule *)

Inductive abort_intercepted_prog : ext_prog -> Prop :=
  | abort_intercepted_prog_block_2 : forall lab S R rv els,
      res_type R <> restype_throw ->
      abort_intercepted_prog (prog_2 rv (out_ter S R) els).

Inductive abort_intercepted_stat : ext_stat -> Prop :=
  | abort_intercepted_stat_block_2 : forall lab S R rv ts,
      res_type R <> restype_throw ->
      abort_intercepted_stat (stat_block_2 rv (out_ter S R) ts)
  | abort_intercepted_stat_label_1 : forall lab S R,
      res_type R = restype_break ->
      abort_intercepted_stat (stat_label_1 lab (out_ter S R))
  | abort_intercepted_do_while_3 : forall labs e1 t2 rv S R,
      res_label_in R labs ->
      (res_type R = restype_continue \/ res_type R = restype_break) ->
      abort_intercepted_stat (stat_do_while_2 labs t2 e1 rv (out_ter S R)) 
  | abort_intercepted_while_3 : forall labs e1 t2 rv S R,
      res_label_in R labs ->
      (res_type R = restype_continue \/ res_type R = restype_break) ->
      abort_intercepted_stat (stat_while_3 labs e1 t2 rv (out_ter S R)) 
  | abort_intercepted_stat_try_1 : forall S R cb fo,
      res_type R = restype_throw ->
      abort_intercepted_stat (stat_try_1 (out_ter S R) (Some cb) fo)
  | abort_intercepted_stat_try_3 : forall S R fo,
      abort_intercepted_stat (stat_try_3 (out_ter S R) fo).



  (* TODO: abort_intercepted check whether we need to add this:
  | abort_intercepted_stat_try_3 : forall S r fio o,
      abort_intercepted (stat_try_3 o fio) (out_ter S r).
  *)


(**************************************************************)
(** ** Auxiliary definition used in identifier resolution *)

(** [spec_identifier_resolution C x] returns the extended expression
    which needs to be evaluated in order to perform the lookup
    of name [x] in the execution context [C]. Typically, a
    reduction rule that performs such a lookup would have a
    premise of the form [red_expr S C (identifier_resolution C x) o1]. *)

Definition spec_identifier_resolution C x :=
  let lex := execution_ctx_lexical_env C in
  let strict := execution_ctx_strict C in
  spec_lexical_env_get_identifier_ref lex x strict.


(**************************************************************)
(** ** Instantiation of arguments in function calls *)

Inductive arguments_from : list value -> list value -> Prop :=
 | arguments_from_nil : forall Vs,
      arguments_from Vs nil
 | arguments_from_undef : forall Vs: list value,
      arguments_from nil Vs ->
      arguments_from nil (undef::Vs)
 | arguments_from_cons : forall Vs1 Vs2 v,
      arguments_from Vs1 Vs2 ->
      arguments_from (v::Vs1) (v::Vs2).
