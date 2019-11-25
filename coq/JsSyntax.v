Set Implicit Arguments.
Require Export Ascii String.
Require JsNumber.
Notation "'number'" := (JsNumber.number).



(************************************************************)
(************************************************************)
(************************************************************)
(************************************************************)
(** * Javascript: Syntax *)

(**************************************************************)
(** ** Representation of syntax (11, 12, 13 and 14) *)

(* Unary operator *)

Inductive unary_op :=
  | unary_op_delete
  | unary_op_void
  | unary_op_typeof
  | unary_op_post_incr
  | unary_op_post_decr
  | unary_op_pre_incr
  | unary_op_pre_decr
  | unary_op_add
  | unary_op_neg
  | unary_op_bitwise_not
  | unary_op_not.

(** Binary operators *)

Inductive binary_op :=
  | binary_op_mult
  | binary_op_div
  | binary_op_mod
  | binary_op_add
  | binary_op_sub
  | binary_op_left_shift
  | binary_op_right_shift
  | binary_op_unsigned_right_shift
  | binary_op_lt
  | binary_op_gt
  | binary_op_le
  | binary_op_ge
  | binary_op_instanceof
  | binary_op_in
  | binary_op_equal
  | binary_op_disequal
  | binary_op_strict_equal
  | binary_op_strict_disequal
  | binary_op_bitwise_and
  | binary_op_bitwise_or
  | binary_op_bitwise_xor
  | binary_op_and
  | binary_op_or
  | binary_op_coma.

(** Grammar of literals *)

Inductive literal :=
  | literal_null : literal
  | literal_bool : bool -> literal
  | literal_number : number -> literal
  | literal_string : string -> literal.

(** Labels literals used by break and continue keywords,
    including the special "empty" label. *)

Inductive label :=
   | label_empty : label
   | label_string : string -> label.

(** A set of labels, possibly including the empty label. *)

Definition label_set := list label.

(** Strictness flag *)

Definition strictness_flag := bool.
Definition strictness_true : strictness_flag := true.
Definition strictness_false : strictness_flag := false.

(** Property name in source code *)

Inductive propname :=
  | propname_identifier : string -> propname
  | propname_string : string -> propname
  | propname_number : number -> propname.

(** Grammar of expressions *)

Inductive expr :=
  | expr_this : expr
  | expr_identifier : string -> expr
  | expr_literal : literal -> expr
  | expr_object : list (propname * propbody) -> expr

  (* _ARRAYS_ : support for processing arrays, based on parser_syntax.ml *)
  | expr_array : list (option expr) -> expr

  | expr_function : option string -> list string -> funcbody -> expr
  | expr_access : expr -> expr -> expr
  | expr_member : expr -> string -> expr
  | expr_new : expr -> list expr -> expr
  | expr_call : expr -> list expr -> expr
  | expr_unary_op : unary_op -> expr -> expr
  | expr_binary_op : expr -> binary_op -> expr -> expr
  | expr_conditional : expr -> expr -> expr -> expr
  | expr_assign : expr -> option binary_op -> expr -> expr

(** Grammar of object properties *)

with propbody :=
  | propbody_val : expr -> propbody
  | propbody_get : funcbody -> propbody
  | propbody_set : list string -> funcbody -> propbody

(** Grammar of function bodies *)

with funcbody :=
  | funcbody_intro : prog -> string -> funcbody

(** Grammar of statements *)
(* LATER: An explanation of these additionnal [label_set] would be welcomed. *)

with stat := 
  | stat_expr : expr -> stat
  | stat_label : string -> stat -> stat
  | stat_block : list stat -> stat
  | stat_var_decl : list (string * option expr) -> stat
  | stat_let_decl : list (string * option expr) -> stat
  | stat_if : expr -> stat -> option stat -> stat
  | stat_do_while : label_set -> stat -> expr -> stat
  | stat_while : label_set -> expr -> stat -> stat
  | stat_with : expr -> stat -> stat
  | stat_throw : expr -> stat
  | stat_return : option expr -> stat
  | stat_break : label -> stat
  | stat_continue : label ->  stat
  | stat_try : stat -> option (string * stat) -> option stat -> stat (* Note: try s1 [catch (x) s2] [finally s3] *)
  | stat_for : label_set -> option expr -> option expr -> option expr -> stat -> stat (* Note: for (e1; e2; e3) stat *)
  | stat_for_var : label_set -> list (string * option expr) -> option expr -> option expr -> stat -> stat (* Note: for (var ...; e2; e3) stat *)
  | stat_for_let : label_set -> list (string * option expr) -> option expr -> option expr -> stat -> stat (* Note: for (let ...; e2; e3) stat *)
  | stat_for_in : label_set -> expr -> expr -> stat -> stat (* Note: for (e1 in e2) stat *)
  | stat_for_in_var : label_set -> string -> option expr -> expr -> stat -> stat (*  Note: for (var x [= e1] in e2) stat *)
  | stat_for_in_let : label_set -> string -> option expr -> expr -> stat -> stat (*  Note: for (let x [= e1] in e2) stat *)
  | stat_debugger : stat
  | stat_switch : label_set -> expr -> switchbody -> stat

with switchbody :=
  | switchbody_nodefault : list switchclause -> switchbody
  | switchbody_withdefault : list switchclause -> list stat -> list switchclause -> switchbody

with switchclause :=
  | switchclause_intro : expr -> list stat -> switchclause

(** Grammar of programs *)

with prog :=
  | prog_intro : strictness_flag -> list element -> prog

(** Grammar of program elements *)

with element :=
  | element_stat : stat -> element
  | element_func_decl : string -> list string -> funcbody -> element.

(** Short names for lists *)

Definition propdefs := list (propname * propbody).

Definition elements := list element.

(** Representation of a function declaration
    (used only for the description of the semantics) *)

Record funcdecl := funcdecl_intro {
   funcdecl_name : string;
   funcdecl_parameters : list string;
   funcdecl_body : funcbody }.

(** Coercions for grammars *)

Coercion stat_expr : expr >-> stat.
Coercion label_string : string >-> label.


