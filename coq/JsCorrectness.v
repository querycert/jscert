Set Implicit Arguments.
Require Import Shared.
Require Import LibFix LibList.
Require Import JsSyntax JsSyntaxAux JsPreliminary JsPreliminaryAux.
Require Import JsInterpreter JsPrettyInterm JsPrettyRules.


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
Implicit Type T : type.

Implicit Type rt : restype.
Implicit Type rv : resvalue.
Implicit Type lab : label.
Implicit Type labs : label_set.
Implicit Type R : res.
Implicit Type o : out.
Implicit Type ct : codetype.

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
Implicit Type W : result.

Implicit Type e : expr.
Implicit Type p : prog.
Implicit Type t : stat.


(**************************************************************)
(** Correctness Properties *)

Definition follow_spec {T Te : Type}
    (conv : T -> Te)
    (red : state -> execution_ctx -> Te -> out -> Prop)
    (run : state -> execution_ctx -> T -> result) := forall S C (e : T) S' res,
  run S C e = out_ter S' res ->
  red S C (conv e) (out_ter S' res).

(* Waiting for the rules to be updated.
Inductive passing_output {Te A : Type}
    (K : A -> Te) (red : state -> execution_ctx -> Te -> out -> Prop) C
    : passing A -> result -> Prop :=
  | passing_output_normal : forall S a o,
    red S C (K a) o ->
    passing_output K red C (passing_normal S a) o
  | passing_output_abort : forall o,
    passing_output K red C (passing_abort o) o.

Definition follow_spec_passing {T Te A : Type}
    (conv : T -> (A -> Te) -> Te)
    (red : state -> execution_ctx -> Te -> out -> Prop)
    (run : state -> execution_ctx -> T -> passing A) := forall S C (x : T) (p : passing A),
  run S C x = p -> forall K S' R',
  passing_output K red C p (out_ter S' R') ->
  red S C (conv x K) (out_ter S' R') /\
    (p = passing_abort (out_ter S' R') -> abort (out_ter S' R')).

Definition follow_spec_inject {A : Type}
    (conv : A -> value)
    (red : out -> Prop)
    (run : passing A) : Prop := (forall S a,
  run = passing_normal S a ->
  red (out_ter S (conv a))) /\ (forall S R,
    run = passing_abort (out_ter S R) ->
    red (out_ter S R) /\
    abort (out_ter S R)).
*)

Definition follow_expr := follow_spec expr_basic red_expr.
Definition follow_stat := follow_spec stat_basic red_stat.
Definition follow_prog := follow_spec prog_basic red_prog.
Definition follow_elements rv :=
  follow_spec (prog_1 rv) red_prog.
Definition follow_call l vs (run : state -> execution_ctx -> value -> result) :=
  forall S C v S' R,
    run S C v = out_ter S' R ->
    red_expr S C (spec_call l v vs) (out_ter S' R).
Definition follow_function_has_instance (run : state -> object_loc -> value -> result) :=
  forall S C lo lv S' R,
    run S lv (lo : object_loc) = out_ter S' R ->
    (* Note that this function is related to [spec_function_has_instance_2] instead of
      [spec_function_has_instance_1] as it's much more closer to the specification and
      thus much easier to prove. *)
    red_expr S C (spec_function_has_instance_2 lo lv) (out_ter S' R).
Definition follow_stat_while ls e t :=
  follow_spec
    (stat_while_1 ls e t)
    red_stat.
Definition follow_object_get_own_prop (_ : state -> execution_ctx -> object_loc -> prop_name -> result_special full_descriptor) :=
  True. (* TODO *)
(* OLD:
Definition follow_object_get_own_prop l :=
  follow_spec_passing (spec_object_get_own_prop l) red_expr. *)
Definition follow_object_get_prop (_ : state -> execution_ctx -> object_loc -> prop_name -> result_special full_descriptor) :=
  True. (* TODO *)
(* OLD:
Definition follow_object_get_prop l :=
  follow_spec_passing (spec_object_get_prop l) red_expr. *)
Definition follow_object_proto_is_prototype_of (_ : state -> object_loc -> object_loc -> result) :=
  True. (* TODO *)
Definition follow_equal (_ : state -> (state -> value -> result) -> (state -> value -> result) -> value -> value -> result) :=
  True. (* TODO *)

Record runs_type_correct runs :=
  make_runs_type_correct {
    runs_type_correct_expr : follow_expr (runs_type_expr runs);
    runs_type_correct_stat : follow_stat (runs_type_stat runs);
    runs_type_correct_prog : follow_prog (runs_type_prog runs);
    runs_type_correct_call : forall l vs,
      follow_call l vs (fun S C vthis =>
        runs_type_call runs S C l vthis vs);
    runs_type_correct_function_has_instance :
      follow_function_has_instance (runs_type_function_has_instance runs);
    runs_type_correct_stat_while : forall ls e t,
      follow_stat_while ls e t (fun S C rv =>
        runs_type_stat_while runs S C rv ls e t);
    runs_type_correct_object_get_own_prop :
      follow_object_get_own_prop (runs_type_object_get_own_prop runs)
    (* OLD: forall l,
      follow_object_get_own_prop l (fun S C =>
        runs_type_object_get_own_prop runs S C l) *);
    runs_type_correct_object_get_prop :
      follow_object_get_prop (runs_type_object_get_prop runs)
      (* OLD: forall l,
      follow_object_get_prop l (fun S C => runs_type_object_get_prop runs S C l)*);
    runs_type_correct_object_proto_is_prototype_of :
      follow_object_proto_is_prototype_of (runs_type_object_proto_is_prototype_of runs);
    runs_type_correct_equal :
      follow_equal (runs_type_equal runs)
  }.


(**************************************************************)
(** Useful Tactics *)

Ltac absurd_neg :=
  let H := fresh in
  introv H; inverts H; tryfalse.

Hint Constructors abort.


(**************************************************************)
(** General Lemmas *)

Lemma res_overwrite_value_if_empty_empty : forall R,
  res_overwrite_value_if_empty resvalue_empty R = R.
Proof. introv. unfolds. cases_if~. destruct R; simpls; inverts~ e. Qed.

Lemma res_type_res_overwrite_value_if_empty : forall rv R,
  res_type R = res_type (res_overwrite_value_if_empty rv R).
Proof.
  introv. destruct R. unfold res_overwrite_value_if_empty. simpl.
  cases_if; reflexivity.
Qed.

Lemma res_label_res_overwrite_value_if_empty : forall rv R,
  res_label R = res_label (res_overwrite_value_if_empty rv R).
Proof.
  introv. destruct R. unfold res_overwrite_value_if_empty. simpl.
  cases_if; reflexivity.
Qed.

Lemma res_overwrite_value_if_empty_resvalue : forall rv1 rv2, exists rv3,
  res_normal rv3 = res_overwrite_value_if_empty rv1 rv2 /\ (rv3 = rv1 \/ rv3 = rv2).
Proof. introv. unfolds res_overwrite_value_if_empty. cases_if*. Qed.

Lemma or_idempotent : forall A : Prop, A \/ A -> A.
(* This probably already exists, but I didn't found it. *)
Proof. introv [?|?]; auto. Qed.


Lemma get_arg_correct : forall args vs,
  arguments_from args vs ->
  forall num,
    num < length vs ->
    get_arg num args = LibList.nth num vs.
Proof.
  introv A. induction~ A.
   introv I. false I. lets (I'&_): (rm I). inverts~ I'.
   introv I. destruct* num. simpl. rewrite <- IHA.
    unfolds. repeat rewrite~ get_nth_nil.
    rewrite length_cons in I. nat_math.
   introv I. destruct* num. simpl. rewrite <- IHA.
    unfolds. repeat rewrite~ get_nth_cons.
    rewrite length_cons in I. nat_math.
Qed.

Lemma and_impl_left : forall P1 P2 P3 : Prop,
  (P1 -> P2) ->
  P1 /\ P3 ->
  P2 /\ P3.
Proof. auto*. Qed.

Ltac applys_and_base L :=
  applys~ and_impl_left; [applys~ L|]; try reflexivity.

Tactic Notation "applys_and" constr(E) :=
  applys_and_base (>> E).

Tactic Notation "applys_and" constr(E) constr(A1) :=
  applys_and_base (>> E A1).

Tactic Notation "applys_and" constr(E) constr(A1) constr(A2) :=
  applys_and_base (>> E A1 A2).

Tactic Notation "applys_and" constr(E) constr(A1) constr(A2) constr(A3) :=
  applys_and_base (>> E A1 A2 A3).

Ltac constructors_and :=
  let H := fresh in
  eapply and_impl_left; [ intro H; constructors; exact H |].


(**************************************************************)
(** Monadic Constructors, Lemmas *)

(* Shared defs *)

(** [eqabort o1 o] assert that [o1] and [o] are equal
    and satisfy the [abort] predicate. *)

Definition eqabort o1 o :=
  o = o1 /\ abort o.

(** [isout W Pred] asserts that [W] is in fact
    an outcome that satisfies [Pred]. *)

Definition isout W (Pred:out->Prop) :=
  exists o1, W = result_some o1 /\ Pred o1.

(* Generic *)

Lemma if_some_out : forall (A : Type) (oa : option A) K o,
  if_some oa K = o ->
  exists (a:A), oa = Some a /\ K a = o.
Proof. introv E. destruct* oa; tryfalse. Qed.

Lemma if_some_or_default_out : forall (A : Type) (oa : option A) d K b,
  if_some_or_default oa d K = b ->
     (oa = None /\ d = b)
  \/ (exists a, oa = Some a /\ K a = b).
Proof. introv E. destruct* oa; tryfalse. Qed.

Lemma if_empty_label_out : forall K S R o,
  if_empty_label S R K = o ->
  res_label R = label_empty /\ K tt = o.
Proof. introv H. unfolds in H. cases_if; tryfalse. eexists; auto*. Qed.

(* Results *)

Definition if_ter_post K o o1 :=
     (o1 = out_div /\ o = o1)
  \/ (exists S R, o1 = out_ter S R /\ K S R = result_some o).

Lemma if_ter_out : forall W K o,
  if_ter W K = o ->
  isout W (if_ter_post K o).
Proof.
  introv H. destruct W as [o1 | | | ]; simpls; tryfalse.
  exists o1. splits~. unfolds. destruct o1 as [|S R].
   inverts* H.
   jauto.
Qed.

Definition if_success_post K o o1 :=
  eqabort o1 o \/
  exists S rv, o1 = out_ter S (res_normal rv) /\ K S rv = result_some o.

Lemma if_success_out : forall W K o,
  if_success W K = o ->
  isout W (if_success_post K o).
Admitted.

(* with unfolding:
Lemma if_success_out : forall W K o,
  if_success W K = o ->
  exists o1, W = result_some o1 /\
   (   (o = o1 /\ abort o)
    \/ (exists S rv, o1 = out_ter S rv /\ K S rv = o)).
*)

Definition if_value_post K o o1 :=
  eqabort o1 o \/
  exists S v, o1 = out_ter S (res_val v) /\ K S v = result_some o.

Lemma if_value_out : forall W K o,
  if_value W K = o ->
  isout W (if_value_post K o).
Admitted.

Definition if_void_post K o o1 :=
  eqabort o1 o \/
  exists S, o1 = out_void S /\ K S = result_some o.

Lemma if_void_out : forall W K o,
  if_void W K = o ->
  isout W (if_void_post K o).
Admitted.

(* Results and deconstruction (we don't factorize the defs below for readability) *)

Definition if_object_post K o o1 :=
  eqabort o1 o \/
  exists S l, o1 = out_ter S (res_val (value_object l)) /\ K S l = result_some o.

Lemma if_object_out : forall W K o,
  if_object W K = o ->
  isout W (if_object_post K o).
Admitted.

Definition if_bool_post K o o1 :=
  eqabort o1 o \/
  exists S z, o1 = out_ter S (res_val (prim_bool z)) /\ K S z = result_some o.

Lemma if_bool_out : forall W K o,
  if_bool W K = o ->
  isout W (if_bool_post K o).
Admitted.

Definition if_string_post K o o1 :=
  eqabort o1 o \/
  exists S s, o1 = out_ter S (res_val (prim_string s)) /\ K S s = result_some o.

Lemma if_string_out : forall W K o,
  if_string W K = o ->
  isout W (if_string_post K o).
Admitted.

Definition if_number_post K o o1 :=
  eqabort o1 o \/
  exists S n, o1 = out_ter S (res_val (prim_number n)) /\ K S n = result_some o.

Lemma if_number_out : forall W K o,
  if_number W K = o ->
  isout W (if_number_post K o).
Admitted.


(* proofs of old monadic lemmas, might be useful
Lemma if_success_out : forall res K S R,
  if_success res K = out_ter S R ->
  if_regular_lemma res S R (fun S' R' => exists rv,
    R' = res_normal rv /\
    K S' rv = out_ter S R).
Proof.
  introv H. deal_with_ter H; substs.
  sets_eq t Et: (res_type R0). repeat eexists.
  rewrite~ res_overwrite_value_if_empty_empty in HE.
  destruct t; try solve [ left; inverts HE; rewrite <- Et; splits~; discriminate ].
  forwards~ (E1&E2): if_empty_label_out (rm HE).
  right. destruct R0. simpls. substs. repeat eexists. auto*.
Qed.

Lemma if_value_out : forall res K S R,
  if_value res K = out_ter S R ->
  if_regular_lemma res S R (fun S' R' => exists v,
    R' = res_val v /\
    K S' v = out_ter S R).
Proof.
  introv H. deal_with_regular_lemma H if_success_out; substs.
   repeat eexists. left~.
   destruct~ rv; tryfalse. repeat eexists. right. eexists. auto*.
Qed.

Lemma if_object_out : forall res K S R,
  if_object res K = out_ter S R ->
  if_regular_lemma res S R (fun S' R' => exists l,
    R' = res_val (value_object l) /\
    K S' l = out_ter S R).
Proof.
  introv H. deal_with_regular_lemma H if_value_out; substs.
   repeat eexists. left~.
   destruct~ v; tryfalse. repeat eexists. right. eexists. auto*.
Qed.

Lemma if_string_out : forall res K S R,
  if_string res K = out_ter S R ->
  if_regular_lemma res S R (fun S' R' => exists s,
    R' = res_val (prim_string s) /\
    K S' s = out_ter S R).
Proof.
  introv H. deal_with_regular_lemma H if_value_out; substs.
   repeat eexists. left~.
   destruct~ v; tryfalse. destruct~ p; tryfalse. repeat eexists. right. eexists. auto*.
Qed.

Lemma if_success_primitive_out : forall res K S R,
  if_success_primitive res K = out_ter S R ->
  if_regular_lemma res S R (fun S' R' => exists p,
    R' = res_val (p : prim) /\
    K S' p = out_ter S R).
Proof.
  introv H. deal_with_regular_lemma H if_value_out; substs.
   repeat eexists. left~.
   destruct~ v; tryfalse. repeat eexists. right. eexists. auto*.
Qed.

Lemma if_not_throw_out : forall res K S R,
  if_not_throw res K = out_ter S R ->
  exists S0 R0, res = out_ter S0 R0 /\
    ((res_type R0 = restype_throw /\ S = S0 /\ R = R0) \/
     (res_type R0 <> restype_throw /\ K S0 R0 = out_ter S R)).
Proof.
  introv H. deal_with_ter H. substs. destruct R0 as [rt rv rl]; simpls.
  tests: (rt = restype_throw).
   repeat eexists. left. inverts~ HE.
   destruct rt; tryfalse; repeat eexists; right; inverts~ HE.
Qed.
*)

(* Passing *)

(*
Inductive passing_terminates {A : Type} : passing A -> Prop :=
  | passing_terminates_normal : forall S a,
    passing_terminates (passing_normal S a)
  | passing_terminates_abort : forall S R,
    abort (out_ter S R) ->
    passing_terminates (passing_abort (out_ter S R)).

Lemma passing_def_out : forall (A B : Type) bo (K : B -> passing A) (p : passing A),
  passing_def bo K = p ->
  (exists b, bo = Some b /\ K b = p) \/
  (exists res, bo = None /\ p = passing_abort res /\ forall o, result_out o <> res).
Proof. introv E. destruct* bo. right. eexists. splits*. discriminate. Qed.

Lemma passing_defined_out : forall (A B : Type) (p : passing B) K (pr : passing A),
  passing_defined p K = pr ->
  (exists S0 b, p = passing_normal S0 b /\ K S0 b = pr) \/
  (exists res, p = passing_abort res /\ pr = passing_abort res).
Proof. introv E. destruct* p. Qed.

Lemma passing_success_out : forall (A : Type) res K (p : passing A),
  passing_success res K = p ->
  (exists S0 rv, res = out_ter S0 (rv : resvalue) /\
                 K S0 rv = p) \/
  (exists res' S0 rv ls, p = passing_abort res' /\ (forall o, result_out o <> res') /\
                      res = out_ter S0 (res_intro restype_normal rv ls) /\
                      ls <> label_empty) \/
  (exists o, res = result_out o /\ p = passing_abort res /\ abort o) \/
  (p = passing_abort res /\ forall o, res <> o).
Proof.
  introv E. destruct~ res; try solve [branch 4; splits~; discriminate].
  destruct~ o.
   branch 3. eexists. splits~.
  destruct r as [T R L]. destruct~ T; try solve [ branch 3;
    eexists; splits~; constructors; absurd_neg ]. simpls.
  cases_if.
   branch 1. substs. repeat eexists.
   branch 2. substs. repeat eexists; auto*. discriminate.
Qed.

Lemma passing_value_out : forall (A : Type) res K (p : passing A),
  passing_value res K = p ->
  (exists S0 v, res = out_ter S0 (v : value) /\
                 K S0 v = p) \/
  (exists res' S0 rv ls, p = passing_abort res' /\ (forall o, result_out o <> res') /\
                      res = out_ter S0 (res_intro restype_normal rv ls) /\
                      (ls <> label_empty \/ forall v, rv <> v)) \/
  (exists o, res = result_out o /\ p = passing_abort res /\ abort o) \/
  (p = passing_abort res /\ forall o, res <> o).
Proof.
  introv E. destruct~ res; try solve [branch 4; splits~; discriminate].
  destruct~ o.
   branch 3. eexists. splits~.
  destruct r as [T R L]. destruct~ T; try solve [ branch 3;
    eexists; splits~; constructors; absurd_neg ]. simpls.
  cases_if; destruct R; subst; try (
    branch 2; repeat eexists;
    [ discriminate | solve [left*] || solve [try right; discriminate] ]).
  branch 1. repeat eexists.
Qed.
*)


(************************************************************)
(* ** Correctness tactics *)

(** [prove_not_intercept] proves a goal of
    the form "~ abort_intercepted_* _" *)

Ltac prove_not_intercept :=
let H := fresh in intros H; try solve [ inversion H; false~ ].

Hint Extern 1 (~ abort_intercepted_expr _) => prove_not_intercept.
Hint Extern 1 (~ abort_intercepted_stat _) => prove_not_intercept.
Hint Extern 1 (~ abort_intercepted_prog _) => prove_not_intercept.

Ltac prove_abort :=
  solve [ assumption | (constructor; absurd_neg) ].

Ltac abort_tactic L :=
  apply L;
  [ simpl; congruence
  | try prove_abort
  | try prove_not_intercept ].

Tactic Notation "abort_expr" :=
    abort_tactic red_expr_abort.
Tactic Notation "abort_stat" :=
    abort_tactic red_stat_abort.
Tactic Notation "abort_prog" :=
    abort_tactic red_prog_abort.
Tactic Notation "abort" :=
  match goal with
  | |- red_expr _ _ _ _ => abort_expr
  | |- red_stat _ _ _ _ => abort_stat
  | |- red_prog _ _ _ _ => abort_prog
  end.

(** [run_select_ifres] selects the appropriate "out" lemma *)

Ltac run_select_ifres H :=
  match type of H with
  | context [ if_ter ] => constr:(if_ter_out)
  | context [ if_success ] => constr:(if_success_out)
  | context [ if_value ] => constr:(if_value_out)
  | context [ if_void ] => constr:(if_void_out)
  | context [ if_object ] => constr:(if_object_out)
  | context [ if_bool ] => constr:(if_bool_out)
  | context [ if_string ] => constr:(if_string_out)
  | context [ if_number ] => constr:(if_number_out)
  end.

(** [run_select_proj] is used to obtain automatically
    the right correctness lemma out of the correctness record *)

Ltac run_select_proj H :=
  match type of H with
  | ?T = _ =>
  match T with
  | runs_type_expr _ _ _ _ = _ => constr:(runs_type_correct_expr)
  | runs_type_stat _ _ _ _ = _ => constr:(runs_type_correct_stat)
  | runs_type_prog _ _ _ _ = _ => constr:(runs_type_correct_prog)
  end end.

(** [run_select_lemma] is used to obtain automatically
    the right correctness lemma for an auxiliary function *)

Ltac run_select_lemma_run_expr_get_value T := fail.
Ltac run_select_lemma_if_to_string T := fail.

Ltac run_select_lemma H :=
  match type of H with
  | ?T = _ =>
    match constr:(tt) with
    | ?x => run_select_lemma_run_expr_get_value T
    | ?x => run_select_lemma_if_to_string T
    end
  end.

(** [run_hyp_select_ind_hyp] returns the induction hypothesis
    on [runs_type_correct] *)

Ltac run_hyp_select_ind_hyp tt :=
  match goal with IH: runs_type_correct _ |- _ => constr:(IH) end.

(* [run_hyp H] exploits the induction hypothesis
   on [runs_type_correct] to the hypothesis [H] *)

Tactic Notation "run_hyp" hyp(H) "as" simple_intropattern(R) :=
  let T := fresh in rename H into T;
  let IH := run_hyp_select_ind_hyp tt in
  let Proj := run_select_proj T in
  lets R: Proj IH (rm T).

Tactic Notation "run_hyp" hyp(H) :=
  let T := fresh in rename H into T;
  run_hyp T as H.

(** [prove_runs_type_correct] discharges the trivial goal
    that consists in invoking the induction hypothesis*)

Ltac prove_runs_type_correct :=
  match goal with |- runs_type_correct _ => assumption end.

(* [run_pre] exploits the appropriate "out" lemma, whether it comes
   from the correctness record or it is an auxiliary lemma. *)

Ltac run_pre_ifres H o1 R1 K :=
   let L := run_select_ifres H in
   let O1 := fresh "O1" in
   lets (o1&O1&K): L (rm H); (* deconstruction of [isout]. *)
   try run_hyp O1 as R1.

Ltac run_pre_lemma H o1 R1 K :=
  let L := run_select_lemma H in
  let T := fresh in rename H into T;
  lets (o1&R1&K): L (rm T);
  try prove_runs_type_correct.

Ltac run_pre_core H o1 R1 K :=
  first
  [ let L := run_select_lemma H in (* test if it's a lemma *)
    first [ run_pre_lemma H o1 R1 K | fail 1 ]
  | let L := run_select_ifres H in (* test if it's a proj *)
    first [ run_pre_ifres H o1 R1 K | fail 1 ]
  ].

Tactic Notation "run_pre" hyp(H) "as" ident(o1) ident(R1) ident(K) :=
  let T := fresh in rename H into T;
  run_pre_core T o1 R1 K.

Tactic Notation "run_pre" "as" ident(o1) ident(R1) :=
  unfold result_some_out in * |- *; (* I added this for it does not work, but any better solution is welcomed! -- Martin *)
  match goal with H: _ = result_some _ |- _ =>
    let T := fresh in rename H into T;
    run_pre_core T o1 R1 H end.

Tactic Notation "run_pre" "as" ident(o1) :=
  let R1 := fresh "R1" o1 in
  run_pre as o1 R1.

Tactic Notation "run_pre" :=
  let o1 := fresh "o1" in let R1 := fresh "R1" in
  run_pre as o1 R1.

(** [run_apply Red o1 R1] applys a reduction rule on a given
    [o1] or reduction reaching [o1]. *)

Tactic Notation "run_apply" constr(Red) constr(o1orR1) :=
  applys Red o1orR1.

Tactic Notation "run_apply" constr(Red) constr(o1) constr(R1) :=
  first [ applys Red (rm R1)
        | applys Red o1 ].

(** [run_post] decomposes the conclusion of the "out"
    lemma *)

Ltac run_post_extra := fail.

Ltac run_post_core :=
  let Er := fresh "Er" in
  let Ab := fresh "Ab" in
  let S := fresh "S" in
  let O1 := fresh "O1" in
  let go H X :=
    destruct H as [(Er&Ab)|(S&X&O1&H)];
    [ try subst_hyp Er | try subst_hyp O1 ] in
  match goal with
  | H: if_ter_post _ _ _ |- _ =>
    let R := fresh "R" in go H R
  | H: if_success_post _ _ _ |- _ =>
    let rv := fresh "rv" in go H rv
  | H: if_value_post _ _ _ |- _ =>
    let v := fresh "v" in go H v
  | H: if_void_post _ _ _ |- _ =>
    destruct H as [(Er&Ab)|(S&O1&H)];
    [ try subst_hyp Er | try subst_hyp O1 ]
  | H: if_object_post _ _ _ |- _ =>
    let l := fresh "l" in go H l
  | H: if_bool_post _ _ _ |- _ =>
    let b := fresh "b" in go H b
  | H: if_string_post _ _ _ |- _ =>
    let s := fresh "s" in go H s
  | H: if_number_post _ _ _ |- _ =>
    let m := fresh "m" in go H m
  | |- _ => run_post_extra (* TODO: create one tactic for each lemma, like for the "select" tactic *)
  end.

Tactic Notation "run_post" :=
  run_post_core.

(** [run_inv] simplifies equalities in goals
    by performing inversions on equalities. *)

Ltac run_inv :=
  unfold result_some_out in * |- *; (* I added this for it does not work, but any better solution is welcomed! -- Martin *)
  repeat
  match goal with
  | H: result_some ?o = result_some ?o |- _ => clear H
  | H: result_some _ = result_some _ |- _ => inverts H
  | H: out_ter ?S ?R = out_ter ?S ?R |- _ => clear H
  | H: out_ter _ _ = out_ter _ _ |- _ => inverts H
  | H: res_intro ?t ?v ?l = res_intro ?t ?v ?l |- _ => clear H
  | H: res_intro _ _ _ = res_intro _ _ _ |- _ => inverts H
  | H: special_val ?S ?R = special_val ?S ?R |- _ => clear H
  | H: special_val _ _ = special_val _ _ |- _ => inverts H
  | H: special_out ?o = special_out ?o |- _ => clear H
  | H: special_out _ = special_out _ |- _ => inverts H
  end.

(** [runs_inv] is the same as [run_inv] followed by subst. *)

Ltac runs_inv :=
  run_inv; subst.

(** Auxiliary tactics to select/check the current "out" *)

Ltac run_get_current_out tt :=
  match goal with
  | |- red_expr _ _ _ ?o => o
  | |- red_stat _ _ _ ?o => o
  | |- red_prog _ _ _ ?o => o
  (* TODO:  Complete *)
  end.

Ltac run_check_current_out o :=
  match goal with
  | |- red_expr _ _ _ o => idtac
  | |- red_stat _ _ _ o => idtac
  | |- red_prog _ _ _ o => idtac
  (* TODO:  Complete *)
  end.

(** [run_step L] combines [run_pre], [run_apply L] and calls
    [run_post] on the main reduction subgoal, followed
    with a cleanup using [run_inv] *)

Ltac run_step Red :=
  let o1 := fresh "o1" in let R1 := fresh "R1" in
  run_pre as o1 R1;
  let o := run_get_current_out tt in
  run_apply Red o1 R1;
  try (run_check_current_out o; run_post; run_inv).

(** [run_simpl] is intended for simplyfing simple monads
    that do not match over a result, then run
    [run_inv] to clean up the goal. *)



Axiom run_error_correct' : forall S ne S' R' C, (* TODO *)
  run_error S ne = out_ter S' R' ->
  red_expr S C (spec_error ne) (out_ter S' R') /\
    ~ res_is_normal R'.


Ltac run_simpl_base H K :=
  let E := fresh "E" in
  match type of H with ?T = _ => match T with
  | if_some _ _ =>
     let x := fresh "x" in
     lets (x&E&K): if_some_out (rm H)
  | if_some_or_default _ _ _ =>
     let x := fresh "x" in
     let E1 := fresh "E" in let E2 := fresh "E" in
     lets [(E1&E2)|(n&E&K)]: if_some_or_default_out (rm H)
  | if_empty_label _ _ _ =>
     lets (E&K): if_empty_label_out (rm H)
  | run_error _ _ =>
     let N := fresh "N" in
     let C := match goal with |- _ _ ?C _ _ => constr:(C) end in
     lets (K&N): run_error_correct' C (rm H)
  end end.

Ltac run_simpl_core H K :=
  run_simpl_base H K; run_inv.

Tactic Notation "run_simpl" ident(H) "as" ident(K) :=
  run_simpl_core H K.

Tactic Notation "run_simpl" :=
  unfold result_some_out in * |- *; (* I added this for it does not work, but any better solution is welcomed! -- Martin *)
  match goal with H: _ = result_some _ |- _ =>
    let H' := fresh in rename H into H';
    run_simpl_core H' H
  end.

(** [run Red] is the same as [run_step Red].
    [run] without arguments is the same as [run_simpl].
    [runs] is same as [run] followed with [subst]. *)

Tactic Notation "run" constr(Red) :=
  run_step Red.

Tactic Notation "run" "*" constr(Red) :=
  run Red; auto*.

Tactic Notation "runs" constr(Red) :=
  run Red; subst.

Tactic Notation "runs" "*" constr(Red) :=
  run Red; subst; auto*.

Tactic Notation "run" :=
  run_simpl.

Tactic Notation "run" "*" :=
  run; auto*.

Tactic Notation "runs" :=
  run; subst.

Tactic Notation "runs" "*" :=
  runs; auto*.


(* debugging of [run Red]:
  run_pre as o1 R1.
    or: run_pre H as o1 R1 K. (* where H is the hypothesis *)
    or: run_pre_core H o1 R1 K. (* where H is the hypothesis *)
    or: run_pre_lemma H o1 R1 K. (* where H is the hypothesis *)
    or: run_pre_ifres H o1 R1 K. (* where H is the hypothesis *)
  run_apply __my_red_lemma__ R1. (* where R1 is the red hypothesis *)
  run_post.
  run_inv.
*)


(************************************************************)
(* ** Correctness Lemmas *)

Lemma run_error_correct : forall S ne S' R' C,
  run_error S ne = out_ter S' R' ->
  red_expr S C (spec_error ne) (out_ter S' R') /\
    ~ res_is_normal R'.
Admitted. (* OLD
  introv E. deal_with_regular_lemma E if_object_out; substs.
  unfolds build_error. destruct S as [E L [l S]]. simpls. cases_if; tryfalse.
   inverts HE. false~ Hnn.
  unfolds build_error. destruct S as [E L [l' S]]. simpls.
   split; [|discriminate]. introv. apply~ red_spec_error; [|apply~ red_spec_error_1].
   apply~ red_spec_build_error. reflexivity.
   cases_if. inverts HE.
   apply~ red_spec_build_error_1_no_msg.
Qed. *)

Lemma out_error_or_cst_correct : forall S C str ne v S' R',
  out_error_or_cst S str (ne : native_error) v = out_ter S' R' ->
  red_expr S C (spec_error_or_cst str ne v) (out_ter S' R') /\
    (res_is_normal R' -> R' = v).
Proof.
  introv E. unfolds in E. cases_if.
   applys_and red_spec_error_or_cst_true. forwards~ (RC&Cr): run_error_correct E. splits*.
   inverts E. splits~. apply~ red_spec_error_or_cst_false.
Qed.

Lemma run_object_method_correct : forall Z (meth : _ -> Z) S l (z : Z),
  run_object_method meth S l = Some z ->
  object_method meth S l z.
Proof.
  introv B. unfolds. forwards (O&Bi&E): option_map_some_back B.
  forwards: @pick_option_correct Bi. exists* O.
Qed.

(*
Lemma object_has_prop_correct : forall runs,
  runs_type_correct runs -> forall S C l x (p : passing bool),
  object_has_prop runs S C l x = p ->
  follow_spec_inject (fun b => b) (red_expr S C (spec_object_has_prop l x)) p.
Admitted. (* OLD
  introv RC E. unfolds in E. name_object_method.
  destruct B as [B|]; simpls.
   forwards~ BC: run_object_method_correct (rm EQB).
    destruct B. forwards [(S'&?&?&E')|(?&Ep&?)]: @passing_defined_out (rm E);
      simpl_after_regular_lemma.
     inverts E'. splits; introv Eq; inverts Eq.
      applys red_spec_object_has_prop BC.
      apply red_spec_object_has_prop_1_default. apply~ RC.
      rewrite H. constructors. apply~ red_spec_object_has_prop_2.
       rewrite decide_spec. cases_if~; rew_refl.
        rewrite~ isTrue_true.
        rewrite~ isTrue_false.
     substs. splits; introv Eq; inverts Eq. apply RC in Ep. splits.
      applys red_spec_object_has_prop BC.
       apply red_spec_object_has_prop_1_default. apply Ep.
       constructors.
      applys~ Ep spec_object_has_prop_2. constructors.
   substs. splits; introv Eq; inverts Eq.
Qed. *)
*)

Lemma run_object_get_correct : forall runs,
  runs_type_correct runs -> forall S0 C0 l x S R,
  run_object_get runs S0 C0 l x = out_ter S R ->
  red_expr S0 C0 (spec_object_get l x) (out_ter S R) /\
    (res_is_normal R -> exists v, R = res_val v).
Admitted. (* OLD
  introv RC E.
  unfolds in E.
  name_object_method.
  destruct B as [B|]; simpls; tryfalse.
  forwards OM: run_object_method_correct (rm EQB).
  lets [_ _ _ _ _ _ _ RCo _ _] : RC.
  forwards H: (rm RCo) l.
  unfolds follow_object_get_prop.
  unfolds follow_spec_passing.
  destruct B; simpls; tryfalse.
  sets_eq p: (runs_type_object_get_prop runs S0 C0 l x).
  splits.
    applys~ red_spec_object_get (rm OM).
     destruct p.
      apply red_spec_object_get_1_default.
      applys~ H.
      rewrite <- EQp. simpls. clear EQp. apply passing_output_normal.
      destruct f; simpls; inverts E.
        apply red_spec_object_get_2_undef.
        destruct a; simpls.
          inverts H1. applys~ red_spec_object_get_2_data.
          applys red_spec_object_get_2_accessor.
           destruct (attributes_accessor_get a).
             destruct p; inverts H1.
              apply red_spec_object_get_3_accessor_undef.
             apply red_spec_object_get_3_accessor_object.
              lets [_ _ _ RCa _ _ _ _ _ _] : RC.
              specialize (RCa o nil).
              unfolds follow_call.
              applys~ RCa.
      apply red_spec_object_get_1_default.
       applys~ H.
       rewrite <- EQp. simpls.
       deal_with_regular_lemma E if_success_out; substs.
        apply (passing_output_abort (spec_object_get_2 l l)).
        cases_if; false.
    introv Hrn; destruct p.
      destruct f; simpls; inverts* E.
      destruct a; simpls; invert H1.
        introv _ _; auto*.
        introv H1; destruct (attributes_accessor_get a).
          destruct p; inverts* H1.
          lets [_ _ _ RCa _ _ _ _ _ _] : RC.
           specialize (RCa o nil).
           unfolds follow_call. applys~ RCa s C0 l S.
      simpls.
       false.
       asserts Hab : (abort (out_ter S R)).
       symmetry in EQp.
       deal_with_regular_lemma E if_success_out; substs; tryfalse.
       cases_if; false.
      inverts~ Hab.
Qed. *)

Lemma env_record_get_binding_value_correct : forall runs,
  runs_type_correct runs -> forall S0 S C0 L rn rs R,
  env_record_get_binding_value runs S0 C0 L rn rs = out_ter S R ->
  red_expr S0 C0 (spec_env_record_get_binding_value L rn rs) (out_ter S R) /\
    (res_is_normal R -> exists v, R = res_val v).
Admitted. (* OLD
  introv RC E. do 2 unfolds in E. rewrite_morph_option; simpls; tryfalse.
  rewrite <- Heap.binds_equiv_read_option in EQx.
   applys_and red_spec_env_record_get_binding_value EQx. destruct e; simpls.
    rewrite_morph_option; tryfalse. simpls.
     rewrite <- Heap.binds_equiv_read_option in EQx0. destruct p.
     applys_and red_spec_env_record_get_binding_value_1_decl EQx0.
     do 2 cases_if; tryfalse.
      forwards~ (RCe&Cre): out_error_or_cst_correct C0 E. splits*.
      inverts E. splits*. apply~ red_spec_returns.
    rewrite_morph_option; simpls.
     forwards~ (HCn&HCa): object_has_prop_correct (rm EQp0).
      applys_and red_spec_env_record_get_binding_value_1_object HCn. cases_if.
       applys_and red_spec_env_record_get_binding_value_obj_2_true.
        forwards*: run_object_get_correct E.
       applys_and red_spec_env_record_get_binding_value_obj_2_false.
        forwards*: out_error_or_cst_correct E.
     deal_with_regular_lemma E if_success_out; substs; tryfalse.
      forwards~ (HCn&HCa): object_has_prop_correct (rm EQp0). forwards~ (RH&A): HCa.
       applys_and red_spec_env_record_get_binding_value_1_object RH.
       applys_and red_expr_abort A. splits~. absurd_neg.
      cases_if; false.
Qed. *)

Lemma ref_get_value_correct : forall runs,
  runs_type_correct runs -> forall S0 C0 rv S R,
  ref_get_value runs S0 C0 rv = out_ter S R ->
  red_expr S0 C0 (spec_get_value rv) (out_ter S R) /\
    (res_is_normal R -> exists v, R = res_val v).
Proof.
  introv RC E. destruct rv; tryfalse.
   inverts E. splits. apply~ red_spec_ref_get_value_value. intros. auto*.
   tests: (ref_is_property r).
    destruct r as [rb rn rs]; destruct rb as [v|?]; try solve [inverts C; false].
      split.
       apply~ red_spec_ref_get_value_ref_b. reflexivity.
        cases_if; destruct v as [()|l]; simpls; try (solve [inverts C; false]);
         cases_if; first [ applys~ prim_value_get_correct RC | applys~ run_object_get_correct RC ].
       intro Rn. destruct v. destruct p; simpls; tryfalse;
         try solve [ forwards~ (_&?): run_error_correct C0 E; false ]; cases_if; tryfalse.
        simpls. cases_if. forwards~ (_&?): run_object_get_correct RC E.
    destruct r as [rb rn rs]; destruct rb as [[()|l]|?]; simpls; tryfalse;
      try (false C; first [ solve [left~] | solve [right~] ]); split.
     apply~ red_spec_ref_get_value_ref_a. constructors. apply~ run_error_correct.
     introv Eq. forwards~ (_&?): run_error_correct C0 E. false.
     apply~ red_spec_ref_get_value_ref_c. reflexivity.
      applys~ env_record_get_binding_value_correct RC.
     intros. forwards~ (_&?): env_record_get_binding_value_correct E.
Qed.

Lemma run_callable_correct : forall S v co,
  run_callable S v = Some co ->
  callable S v co.
Admitted. (* OLD
  introv E. destruct v; simpls~.
   inverts~ E.
   rewrite_morph_option; simpls; tryfalse.
    exists o0. splits~. forwards~: @pick_option_correct EQx. inverts~ E.
Qed. *)

Lemma object_default_value_correct : forall runs,
  runs_type_correct runs -> forall S S' R' C l pref,
  object_default_value runs S C l pref = out_ter S' R' ->
  red_expr S C (spec_object_default_value l pref) (out_ter S' R').
Admitted. (* OLD
  introv RC E. unfolds in E. rewrite_morph_option; simpls; tryfalse.
  forwards~ OM: run_object_method_correct (rm EQx).
  applys~ red_spec_object_default_value OM. destruct~ b.
   apply~ red_spec_object_default_value_1_default.
    apply~ red_spec_object_default_value_2.
    deal_with_regular_lemma E if_value_out; substs.
     forwards~ (E&_): run_object_get_correct RC (rm HE).
      applys~ red_spec_object_default_value_sub_1 E.
      apply~ red_expr_abort.
     forwards~ (E&?): run_object_get_correct RC (rm HE).
      applys~ red_spec_object_default_value_sub_1 E.
      rewrite_morph_option; simpls; tryfalse.
      forwards~ RCa: run_callable_correct (rm EQx). destruct o.
       forwards~ (E1&E2): if_empty_label_out (rm H0).
        rewrite res_overwrite_value_if_empty_empty in E2. destruct v; simpls; tryfalse.
        deal_with_regular_lemma E2 if_value_out; substs.
         apply RC in HE. applys~ red_spec_object_default_value_sub_2_callable HE.
          apply* RCa. apply~ red_expr_abort.
         apply RC in HE. applys~ red_spec_object_default_value_sub_2_callable HE.
          apply* RCa. destruct v.
           inverts H1. apply~ red_spec_object_default_value_sub_3_prim.
           apply~ red_spec_object_default_value_sub_3_object.
            apply~ red_spec_object_default_value_3.
            (* This part is a big copy-paste of the previous *)
            deal_with_regular_lemma H1 if_value_out; substs.
             forwards~ (E0&_): run_object_get_correct RC (rm HE0).
              applys~ red_spec_object_default_value_sub_1 E0.
              apply~ red_expr_abort.
             forwards~ (E0&?): run_object_get_correct RC (rm HE0).
              applys~ red_spec_object_default_value_sub_1 E0.
              rewrite_morph_option; simpls; tryfalse.
              forwards~ RCa0: run_callable_correct (rm EQx). destruct o1.
               forwards~ (E3&E4): if_empty_label_out (rm H1).
                rewrite res_overwrite_value_if_empty_empty in E4.
                destruct v; simpls; tryfalse.
                deal_with_regular_lemma E4 if_value_out; substs.
                 apply RC in HE. applys~ red_spec_object_default_value_sub_2_callable HE.
                  apply* RCa0. apply~ red_expr_abort.
                 apply RC in HE. applys~ red_spec_object_default_value_sub_2_callable HE.
                  apply* RCa0. destruct v.
                   inverts H4. apply~ red_spec_object_default_value_sub_3_prim.
                   apply~ red_spec_object_default_value_sub_3_object.
                     forwards~ (?&?): run_error_correct (rm H4).
                     apply~ red_spec_object_default_value_4.
               forwards~ (?&?): run_error_correct (rm H1).
                apply~ red_spec_object_default_value_sub_2_not_callable.
                 apply~ red_spec_object_default_value_4.
       apply~ red_spec_object_default_value_sub_2_not_callable.
        (* This part is a big copy-paste of the previous *)
        apply~ red_spec_object_default_value_3.
        deal_with_regular_lemma H0 if_value_out; substs.
         forwards~ (E0&_): run_object_get_correct RC (rm HE).
          applys~ red_spec_object_default_value_sub_1 E0.
          apply~ red_expr_abort.
         forwards~ (E0&?): run_object_get_correct RC (rm HE).
          applys~ red_spec_object_default_value_sub_1 E0.
          rewrite_morph_option; simpls; tryfalse.
          forwards~ RCa0: run_callable_correct (rm EQx). destruct o.
           forwards~ (E3&E4): if_empty_label_out (rm H1).
            rewrite res_overwrite_value_if_empty_empty in E4.
            destruct v0; simpls; tryfalse.
            deal_with_regular_lemma E4 if_value_out; substs.
             apply RC in HE. applys~ red_spec_object_default_value_sub_2_callable HE.
              apply* RCa0. apply~ red_expr_abort.
             apply RC in HE. applys~ red_spec_object_default_value_sub_2_callable HE.
              apply* RCa0. destruct v0.
               inverts H2. apply~ red_spec_object_default_value_sub_3_prim.
               apply~ red_spec_object_default_value_sub_3_object.
                 forwards~ (?&?): run_error_correct (rm H2).
                 apply~ red_spec_object_default_value_4.
           forwards~ (?&?): run_error_correct (rm H1).
            apply~ red_spec_object_default_value_sub_2_not_callable.
             apply~ red_spec_object_default_value_4.
Qed. *)


(** Conversions *)

Definition if_to_primitive_post K o o1 :=
  (eqabort o1 o \/
    exists S, exists (w : prim), o1 = out_ter S w /\
      K S w = result_some o).

Lemma if_to_primitive_correct : forall runs,
  runs_type_correct runs -> forall S C v prefo K o,
  if_primitive (to_primitive runs S C v prefo) K = o -> exists o1,
    red_expr S C (spec_to_primitive v prefo) o1 /\
      if_to_primitive_post K o o1.
Admitted.

Definition if_to_string_post K o o1 :=
  (eqabort o1 o \/
    exists S, exists (s : string), o1 = out_ter S s /\
      K S s = result_some o).

Lemma if_to_string_correct : forall runs,
  runs_type_correct runs -> forall S C v K o,
  if_string (to_string runs S C v) K = o -> exists o1,
    red_expr S C (spec_to_string v) o1 /\
      if_to_string_post K o o1.
Admitted. (* OLD
  introv RC E. destruct v; simpls.
   inverts E. splits*. apply~ red_spec_to_string_prim.
   deal_with_regular_lemma E if_success_primitive_out; substs.
    forwards~ DV: object_default_value_correct HE.
     splits; [| intros; false ]. apply~ red_spec_to_string_object.
       applys~ red_spec_to_primitive_pref_object DV.
     apply~ red_expr_abort.
    forwards~ DV: object_default_value_correct HE.
     applys_and red_spec_to_string_object.
      applys~ red_spec_to_primitive_pref_object DV.
     splits*. apply~ red_spec_to_string_1.
Qed. *)

Definition run_expr_get_value_post K o o1 :=
  (eqabort o1 o \/
    exists S1, exists (v1 : value), o1 = out_ter S1 v1 /\
      K S1 v1 = result_some o).

Lemma run_expr_get_value_correct : forall runs,
  runs_type_correct runs -> forall S C e K o,
  run_expr_get_value runs S C e K = o -> exists o1,
    red_expr S C (spec_expr_get_value e) o1 /\
      run_expr_get_value_post K o o1.
Admitted.


Ltac run_select_lemma_run_expr_get_value T ::=
  match T with run_expr_get_value _ _ _ _ _ => constr:(run_expr_get_value_correct) end.

Ltac run_select_lemma_if_to_string T ::=
  match T with if_string (to_string _ _ _ _) _ => constr:(if_to_string_correct) end.

Ltac run_post_extra ::=
  let Er := fresh "Er" in
  let Ab := fresh "Ab" in
  match goal with
  | H: run_expr_get_value_post _ _ _ |- _ =>
    let O1 := fresh "O1" in
    let S1 := fresh "S" in
    let v1 := fresh "v" in
    destruct H as [(Er&Ab)|(S1&v1&O1&H)];
    [ try abort_expr | try subst_hyp O1 ]
  | H: if_to_string_post _ _ _ |- _ =>
    let O1 := fresh "O1" in
    let S1 := fresh "S" in
    let s := fresh "s" in
    destruct H as [(Er&Ab)|(S1&s&O1&H)];
    [ try abort_expr | try subst_hyp O1 ]
  end.


(* OLD
Ltac unmonad_passing :=
  let Ep := fresh "Ep" in
  let No := fresh "No" in
  let deal_with_fail_case :=
    try match goal with
    | H : passing_output ?K ?red ?C ?p ?res |- _ =>
      first [ solve [ rewrite Ep in H; inverts H; false* No ]
            | solve [ substs; inverts H; constructors~ ] ]
    end
  in try match goal with
  (* TODO:  Factorize the following tactics. *)
  | H : passing_def ?bo ?K = ?p |- _ =>
    let E := fresh "E" in
    forwards [(?&?&E)|(?&?&Ep&No)]: @passing_def_out (rm H);
    deal_with_fail_case;
    simpl_after_regular_lemma
  | H : passing_defined ?p ?K = ?p0 |- _ =>
    let S := fresh "S" in
    let p := fresh "p" in
    let E := fresh "E" in
    forwards [(S&?&?&E)|(?&Ep&?)]: @passing_defined_out (rm H);
    deal_with_fail_case;
    simpl_after_regular_lemma
  | H : passing_success ?p ?K = ?p0 |- _ =>
    let S := fresh "S" in
    let rv := fresh "rv" in
    let E := fresh "E" in
    let Eo := fresh "Eo" in
    forwards [(S&rv&Eo&E)|[(?&S&rv&?&Ep&No&?&?)|[(?&?&E&?)|(E&No)]]]: @passing_success_out (rm H);
    deal_with_fail_case;
    simpl_after_regular_lemma
  | H : passing_value ?p ?K = ?p0 |- _ =>
    let S := fresh "S" in
    let v := fresh "v" in
    let E := fresh "E" in
    let Eo := fresh "Eo" in
    forwards [(S&v&Eo&E)|[(?&S&rv&?&Ep&No&?&?)|[(?&?&E&?)|(E&No)]]]: @passing_value_out (rm H);
    deal_with_fail_case;
    simpl_after_regular_lemma
  end;
  dealing_follows;
  other_follows.
*)


(**************************************************************)
(** ** Main theorem *)

Lemma run_elements_correct : forall runs,
  runs_type_correct runs -> forall rv,
  follow_elements rv (fun S C => run_elements runs S C rv).
Admitted. (* OLD
  intros runs [IHe IHs IHp IHc IHhi IHw IHowp IHop IHpo] rv S C es S' res R.
  gen rv S C S' res R. induction es; simpls; introv R.
   unmonad. apply~ red_prog_1_nil.
   destruct a.
    (* stat *)
    unmonad.
     (* Throw case *)
     forwards~ RC: IHs (rm E). applys~ red_prog_1_cons_stat RC. abort_prog.
     (* Other cases *)
     forwards~ RC: IHs (rm E). applys~ red_prog_1_cons_stat RC. apply~ red_prog_2.
     rewrite <- res_type_res_overwrite_value_if_empty in HE.
     tests N: (res_type R0 = restype_normal).
      rewrite N in HE. forwards~ (E1&E2): if_empty_label_out (rm HE).
       rewrite <- res_label_res_overwrite_value_if_empty in E1.
       destruct R0 as [rt0 rv0 rl0]. simpls. substs. fold (res_normal rv0) in *.
       forwards~ (rv'&Erv'&?): res_overwrite_value_if_empty_resvalue.
       rewrite <- Erv' in *. applys~ red_prog_3.
       rewrite res_overwrite_value_if_empty_empty in E2. forwards~: IHes E2.
      rewrite res_overwrite_value_if_empty_empty in *.
       asserts H: (out_ter S0 (res_overwrite_value_if_empty rv R0) = out_ter S' res).
         destruct R0 as [rt0 rv0 rl0]. destruct rt0; simpls; tryfalse; inverts~ HE.
       clear HE. inverts H. destruct R0 as [rt0 rv0 rl0]. simpls.
       unfold res_overwrite_value_if_empty in *. cases_if; simpls; substs;
        abort_prog; constructors; intro H; unfolds in H; simpls; false.
    (* func_decl *)
    forwards RC: IHes (rm R). apply~ red_prog_1_cons_funcdecl.
Qed. *)

Lemma run_expr_correct : forall runs,
  runs_type_correct runs ->
   follow_expr (run_expr runs).
Proof.
  introv RC. intros S C e S' res R. unfolds in R. destruct e.

  (* this *)
  run_inv. apply~ red_expr_this.
  (* identifier *)
  (* apply~ red_expr_identifier. *)
  skip. (* FIXME:  [spec_identifier_resolution] needs rules! *)
  (* literal *)
  run_inv. apply~ red_expr_literal.
  (* object *)
  skip. (* OLD:
  unfold call_object_new in R. destruct S as [SH SE [fl SF]]. unmonad; simpls.
   (* Abort case *)
   inverts HE. false~ Hnn.
   (* Normal case *)
   unmonad. skip. (* TODO:  Needs an intermediate lemma for [init_object]. *) *)
  (* function *)
  skip. (* TODO *)
  (* Access *)
  unfolds in R.
  run red_expr_access. run red_expr_access_1. cases_if.
    lets (R2&N): run_error_correct R.
     applys red_expr_access_2.
       applys* red_spec_check_object_coercible_undef_or_null.
     abort_expr.
    applys red_expr_access_2.
      applys* red_spec_check_object_coercible_return.
     run red_expr_access_3. applys* red_expr_access_4.
  (* member *)
  skip. (* OLD:  forwards~ ?: IHe (rm R). apply~ red_expr_member. *)

Admitted. (* OLD:
   intros S C e S' res R. destruct e; simpl in R; dealing_follows.
    (* this *)
    unmonad. apply~ red_expr_this.
    (* identifier *)
    apply~ red_expr_identifier.
    skip. (* FIXME:  [spec_identifier_resolution] needs rules! *)
    (* literal *)
    unmonad. apply~ red_expr_literal.
    (* object *)
    unfold call_object_new in R. destruct S as [SH SE [fl SF]]. unmonad; simpls.
     (* Abort case *)
     inverts HE. false~ Hnn.
     (* Normal case *)
     unmonad. skip. (* TODO:  Needs an intermediate lemma for [init_object]. *)
    (* function *)
    skip. (* TODO *)
    (* access *)
    unmonad.
     (* Abort case *)
     forwards~ RC: IHe (rm HE). apply~ red_expr_access.
      applys~ red_spec_expr_get_value RC. skip. skip. (* Old [abort_expr], two times *)
     (* Normal case *)
     forwards~ RC: IHe (rm HE).
      inverts HM as HM; simpl_after_regular_lemma; rm_variables.
       apply~ red_expr_access.
         applys~ red_spec_expr_get_value RC. applys~ red_spec_expr_get_value_1 H0.
        abort_expr.
       apply~ red_expr_access.
         applys~ red_spec_expr_get_value RC. applys~ red_spec_expr_get_value_1 H0.
        unmonad.
         forwards~ RC': IHe (rm HE). apply~ red_expr_access_1.
          applys~ red_spec_expr_get_value RC'. skip. skip. (* Old [abort_expr], two times *)
         forwards~ RC': IHe (rm HE).
          inverts HM as HM; simpl_after_regular_lemma; rm_variables.
           apply~ red_expr_access_1.
             applys~ red_spec_expr_get_value RC'. applys~ red_spec_expr_get_value_1 H1.
            abort_expr.
           apply~ red_expr_access_1.
             applys~ red_spec_expr_get_value RC'. applys~ red_spec_expr_get_value_1 H1.
            cases_if.
             forwards~ (RCer&?): run_error_correct H2.
              applys~ red_expr_access_2.
                applys~ red_spec_check_object_coercible_undef_or_null.
              abort_expr.
             apply~ red_expr_access_2. applys~ red_spec_check_object_coercible_return n.
              unmonad.
               forwards~ (TS&?): to_string_correct (rm HE). constructors~.
                applys~ red_expr_access_3 TS. abort_expr.
               forwards~ (TS&?): to_string_correct (rm HE). constructors~.
                applys~ red_expr_access_3 TS. apply~ red_expr_access_4.
    (* member *)
    forwards~ ?: IHe (rm R). apply~ red_expr_member.
    (* new *)
    skip. (* TODO *)
    (* call *)
    unmonad.
     (* Abort case *)
     forwards~ RC: IHe (rm HE). applys~ red_expr_call RC. abort_expr.
     (* Normal case *)
     forwards~ RC: IHe (rm HE). applys~ red_expr_call RC.
     skip. (* TODO *)
    (* unary_op *)
    destruct~ u; simpls; cases_if; try solve [false~ n].
     (* Delete *)
     unmonad.
      (* Abort case *)
      forwards~ RC: IHe (rm HE). applys~ red_expr_delete RC. abort_expr.
      (* Normal case *)
      forwards~ RC: IHe (rm HE). applys~ red_expr_delete RC.
      destruct rv; try solve [ inverts H0; apply~ red_expr_delete_1_not_ref; absurd_neg ].
      cases_if.
       inverts H0. apply* red_expr_delete_1_ref_unresolvable.
       destruct r as [[rbv|rbel] rn rs]; simpls.
        skip. (* TODO:  check in the interpreter that the reference base is neither null nor undefined. *)
        apply~ red_expr_delete_1_ref_env_record. reflexivity.
         skip. (* TODO:  Needs a lemma [env_record_delete_binding_correct]. *)
     (* Void *)
     unmonad.
      (* Abort case *)
      forwards~ RC: IHe (rm HE). apply~ red_expr_unary_op.
       simpl. cases_if~; tryfalse.
       applys~ red_spec_expr_get_value RC. skip. skip. (* Old [abort_expr], two times *)
      (* Normal case *)
      forwards~ RC: IHe (rm HE).
       inverts HM as HM; simpl_after_regular_lemma; rm_variables.
        apply~ red_expr_unary_op.
         simpl. cases_if~; tryfalse.
         applys~ red_spec_expr_get_value RC. applys~ red_spec_expr_get_value_1 H0.
         abort_expr.
        apply~ red_expr_unary_op. simpl. cases_if~; tryfalse.
         applys~ red_spec_expr_get_value RC. applys~ red_spec_expr_get_value_1 H0.
         apply~ red_expr_unary_op_1. apply~ red_expr_unary_op_void.
     (* TypeOf *)
     skip. (* TODO *)
     (* Post Incr *)
     skip. (* TODO *)
     (* Post Decr *)
     skip. (* TODO *)
     (* Pre Incr *)
     skip. (* TODO *)
     (* Pre Decr *)
     skip. (* TODO *)
     (* Add *)
     skip. (* TODO *)
     (* Neg *)
     skip. (* TODO *)
     (* Bitwise *)
     skip. (* TODO *)
     (* Not *)
     skip. (* TODO *)
    (* binary_op *)
    unfolds in R. destruct~ b; simpls.
     (* Mult *)
     skip. (* TODO *)
     (* Div *)
     skip. (* TODO *)
     (* Mod *)
     skip. (* TODO *)
     (* Add *)
     skip. (* TODO *)
     (* Sub *)
     skip. (* TODO *)
     (* Left shift *)
     skip. (* TODO *)
     (* Right shift *)
     skip. (* TODO *)
     (* Unsigned right shift *)
     skip. (* TODO *)
     (* Lesser *)
     skip. (* TODO *)
     (* Greater *)
     skip. (* TODO *)
     (* Lesser or equal *)
     skip. (* TODO *)
     (* Greater or equal *)
     skip. (* TODO *)
     (* Instance of *)
     unmonad.
      (* Abort case *)
      forwards~ RC: IHe (rm HE). apply~ red_expr_binary_op.
       applys~ red_spec_expr_get_value RC. skip. skip. (* Old [abort_expr], two times *)
      (* Normal case *)
      forwards~ RC1: IHe (rm HE).
       inverts HM as HM; simpl_after_regular_lemma; rm_variables.
        apply~ red_expr_binary_op.
         applys~ red_spec_expr_get_value RC1. applys~ red_spec_expr_get_value_1 H0.
         abort_expr.
        apply~ red_expr_binary_op.
          applys~ red_spec_expr_get_value RC1. applys~ red_spec_expr_get_value_1 H0.
         unmonad.
          (* Abort case *)
          forwards~ RC2: IHe (rm HE).
           applys~ red_expr_binary_op_1.
             applys~ red_spec_expr_get_value RC2. skip. skip. (* Old [abort_expr], two times *)
          (* Normal case *)
          forwards~ RC2: IHe (rm HE).
           inverts HM as HM; simpl_after_regular_lemma; rm_variables.
            apply~ red_expr_binary_op_1.
              applys~ red_spec_expr_get_value RC2. applys~ red_spec_expr_get_value_1 H1.
             abort_expr.
            apply~ red_expr_binary_op_1.
              applys~ red_spec_expr_get_value RC2. applys~ red_spec_expr_get_value_1 H1.
            apply~ red_expr_binary_op_2. destruct v0.
             forwards~ (RE&A): run_error_correct H2.
              apply~ red_expr_binary_op_instanceof_non_object.
              destruct p; discriminate.
             rewrite_morph_option; tryfalse. simpls. rewrite_morph_option; simpls.
              substs. apply~ red_expr_binary_op_instanceof_normal.
               skip. (* TODO *)
              substs. forwards~ (RE&A): run_error_correct H2.
               unmonad. applys~ red_expr_binary_op_instanceof_non_instance R.
     (* In *)
     skip. (* TODO *)
     (* Equal *)
     skip. (* TODO *)

     (* Disequal *)
     skip. (* TODO *)
     (* Strict equal *)
     skip. (* TODO *)
     (* Strict disequal *)
     skip. (* TODO *)
     (* Bitwise and *)
     skip. (* TODO *)
     (* Bitwise or *)
     skip. (* TODO *)
     (* Bitwise xor *)
     skip. (* TODO *)
     (* And *)
     skip. (* TODO *)
     (* Or *)
     skip. (* TODO *)
     (* Comma *)
     skip. (* TODO *)
    (* conditionnal *)
    skip. (* TODO *)
    (* assign *)
    skip. (* TODO *)
*)

Lemma run_stat_correct : forall runs,
  runs_type_correct runs ->
   follow_stat (run_stat runs).
Proof.
  introv RC. intros S C t S' res R. unfolds in R. destruct t.
Admitted. (* OLD:
   intros S C t S' res R. destruct t; simpl in R; dealing_follows.
    (* Expression *)
    apply~ red_stat_expr. unmonad.
     (* Abort case *)
     forwards~ RC: IHe (rm HE). applys~ red_spec_expr_get_value RC.
      abort_expr.
     (* Normal case *)
     forwards~ RC: IHe (rm HE). applys~ red_spec_expr_get_value RC.
      inverts HM as HM; simpl_after_regular_lemma; rm_variables;
       apply~ red_spec_expr_get_value_1.
    (* Label *)
    skip. (* TODO *)
    (* Block *)
    skip. (* TODO *)
    (* Variable declaration *)
    skip. (* TODO *)
    (* If *)
    unfolds in R. unmonad.
     forwards~ RC: IHe (rm HE). apply~ red_stat_if.
      apply~ red_spec_expr_get_value_conv_stat.
       applys~ red_spec_expr_get_value RC. skip. skip. (* Old [abort_expr/stat], two times *)
     forwards~ RC: IHe (rm HE). apply~ red_stat_if.
      inverts HM as HM; simpl_after_regular_lemma; rm_variables.
       apply~ red_spec_expr_get_value_conv_stat.
        applys~ red_spec_expr_get_value RC.
         applys~ red_spec_expr_get_value_1 H0.
        abort_stat.
       apply~ red_spec_expr_get_value_conv_stat.
        applys~ red_spec_expr_get_value RC.
         applys~ red_spec_expr_get_value_1 H0.
        apply~ red_spec_expr_get_value_conv_stat_1. apply~ red_spec_to_boolean.
         apply~ red_spec_expr_get_value_conv_stat_2.
         cases_if.
          forwards~ RCt: IHs (rm H1).
           apply~ red_stat_if_1_true.
          destruct o; unmonad.
           forwards~ RCt: IHs (rm H1).
            apply~ red_stat_if_1_false.
           apply~ red_stat_if_1_false_implicit.
    (* Do-while *)
    false.
    (* While *)
    forwards~ RC: IHw R. apply~ red_stat_while.
    (* With *)
    skip. (* TODO *)
    (* Throw *)
    unfolds in R. unmonad.
     forwards~ RC: IHe (rm HE). apply~ red_stat_throw.
      applys~ red_spec_expr_get_value RC. skip. skip. (* Old [abort_expr/stat], two times *)
     forwards~ RC: IHe (rm HE).
      inverts HM as HM; simpl_after_regular_lemma; rm_variables.
       apply~ red_stat_throw.
        applys~ red_spec_expr_get_value RC.
         applys~ red_spec_expr_get_value_1 H0.
        abort_stat.
       apply~ red_stat_throw.
        applys~ red_spec_expr_get_value RC.
         applys~ red_spec_expr_get_value_1 H0.
        apply~ red_stat_throw_1.
    (* Return *)
    destruct o; simpls; unmonad.
     forwards~ RC: IHe (rm HE). apply~ red_stat_return_some.
      applys~ red_spec_expr_get_value RC. skip. skip. (* Old [abort_expr/stat], two times *)
     forwards~ RC: IHe (rm HE).
      inverts HM as HM; simpl_after_regular_lemma; rm_variables.
       apply~ red_stat_return_some.
        applys~ red_spec_expr_get_value RC.
         applys~ red_spec_expr_get_value_1 H0.
        abort_stat.
       apply~ red_stat_return_some.
        applys~ red_spec_expr_get_value RC.
         applys~ red_spec_expr_get_value_1 H0.
        apply~ red_stat_return_1.
     apply~ red_stat_return_none.
    (* Break *)
    unmonad. apply~ red_stat_break.
    (* Continue *)
    unmonad. apply~ red_stat_continue.
    (* Try *)
    skip. (* TODO *)
    (* For-in *)
    skip. (* TODO *)
    (* For-in-var *)
    skip. (* TODO *)
    (* Debugger *)
    unmonad. apply~ res_stat_debugger.
    (* switch *)
    skip. (* TODO *)
*)

Lemma run_prog_correct : forall runs,
  runs_type_correct runs ->
   follow_prog (run_prog runs).
Proof.
  introv RC. intros S C p S' res R. unfolds in R. destruct p.
  apply~ red_prog_prog. applys~ run_elements_correct R.
Qed.

Lemma run_call_correct : forall runs,
  runs_type_correct runs -> forall l (vs : list value),
  follow_call l vs
    (fun S C (vthis : value) =>
      run_call runs S C l vthis vs).
Proof.
   introv RC. intros l vs S C v S' res R. unfolds in R.
Admitted. (* OLD:
   intros l vs S C v S' res R. simpls. unfolds in R. unmonad.
   name_object_method. do 2 (destruct B as [B|]; tryfalse). destruct B; tryfalse.
    (* Call Default *)
    skip. (* TODO *)
    (* Call Prealloc *)
    splits.
     apply~ red_spec_call. applys run_object_method_correct EQB.
      apply~ red_spec_call_1_prealloc. unmonad.
      skip. (* TODO *)
     skip. (* TODO *)
*)

Lemma run_function_has_instance_correct : forall runs,
  runs_type_correct runs ->
  follow_function_has_instance (run_function_has_instance runs).
Admitted. (* OLD:
   intros S C lo lv S' res R. simpls. rewrite_morph_option; tryfalse.
    simpls. unmonad. applys_and red_spec_function_has_instance_2 R0. destruct v; tryfalse.
     destruct p; inverts R. splits*.
      apply~ red_spec_function_has_instance_3_null.
     cases_if.
      substs. inverts R. splits*. apply~ red_spec_function_has_instance_3_eq.
      applys_and red_spec_function_has_instance_3_neq n.
       forwards~: IHhi C R.
*)

Lemma run_stat_while_correct : forall runs,
  runs_type_correct runs -> forall (ls : label_set) e t,
  follow_stat_while ls e t
    (fun S C rv => run_stat_while runs S C rv ls e t).
Admitted. (* OLD:
   intros ls e t S C v S' res R. simpls. unfolds in R. apply~ red_stat_while_1.
   unmonad.
    forwards~ RC: IHe (rm HE).
     apply~ red_spec_expr_get_value_conv_stat.
      applys~ red_spec_expr_get_value RC. skip. skip. (* Old [abort_expr/stat], two times *)
    forwards~ RC: IHe (rm HE).
     inverts HM as HM; simpl_after_regular_lemma; rm_variables.
     apply~ red_spec_expr_get_value_conv_stat. applys~ red_spec_expr_get_value RC.
       applys~ red_spec_expr_get_value_1 H0.
      abort_stat.
     apply~ red_spec_expr_get_value_conv_stat. applys~ red_spec_expr_get_value RC.
       applys~ red_spec_expr_get_value_1 H0.
      apply~ red_spec_expr_get_value_conv_stat_1. apply* red_spec_to_boolean.
      apply~ red_spec_expr_get_value_conv_stat_2.
      cases_if.
       unmonad. forwards~ RCs: IHs (rm HR). applys~ red_stat_while_2_true RCs.
        apply~ red_stat_while_3. destruct R as [Rt Rv Rl]; simpls.
        tests: (Rt = restype_break).
         cases_if in HE; inverts HE.
          do 2 cases_if; apply~ red_stat_while_4_break.
          apply~ red_stat_while_4_abrupt; try absurd_neg.
        tests: (Rt = restype_continue).
         cases_if in HE; inverts HE.
          forwards~ RCw: IHw (rm H3).
           do 2 cases_if; applys~ red_stat_while_4_continue RCw.
          apply~ red_stat_while_4_abrupt; try absurd_neg.
        tests: (Rt = restype_normal).
         forwards~ (E1&E2): if_empty_label_out (rm HE). simpls. substs.
         forwards~ RCw: IHw (rm E2).
         do 2 cases_if; apply~ red_stat_while_4_continue.
        destruct Rt; tryfalse; inverts HE; apply~ red_stat_while_4_abrupt; absurd_neg.
       unmonad. apply~ red_stat_while_2_false.
*)

(*
Lemma run_object_get_own_prop_correct : forall runs,
  runs_type_correct runs -> forall l,
  follow_object_get_own_prop l
    (fun S C => run_object_get_own_prop runs S C l).
Admitted. (* OLD:
   introv E R. simpls. unfolds in E. unmonad_passing.
    applys_and red_spec_object_get_own_prop R0. name_passing_def.
    asserts Co: (forall K o,
        passing_output K red_expr C p0 o ->
        red_expr S C (spec_object_get_own_prop_1 builtin_get_own_prop_default l x K) o /\
          (p0 = passing_abort o -> abort o)).
      introv R1. unmonad_passing.
      applys_and red_spec_object_get_own_prop_1_default R2.
      rewrite <- E in R1. sets_eq Ao: (Heap.read_option x1 x). destruct Ao; inverts R1.
       splits. apply~ red_spec_object_get_own_prop_2_some_data. absurd_neg.
       splits. apply~ red_spec_object_get_own_prop_2_none. absurd_neg.
    destruct x0.
     inverts E0. apply* Co.
     applys_and red_spec_object_get_own_prop_args_obj. applys_and Co. clear EQp0.
      unmonad_passing. destruct x0.
       substs. inverts R. splits.
        constructors. apply~ red_spec_object_get_own_prop_args_obj_1_undef.
        absurd_neg.
       rewrite H. constructors_and. unmonad_passing.
        destruct x0; simpls; try solve [ substs; inverts R ].
        applys_and red_spec_object_get_own_prop_args_obj_1_attrs R1.
        unmonad_passing.
         applys_and RC. constructors_and. destruct x0.
          applys_and red_spec_object_get_own_prop_args_obj_2_undef.
           applys_and red_spec_object_get_own_prop_args_obj_4.
           inverts~ R; tryfalse. inverts~ H0. splits~. absurd_neg.
          unmonad_passing.
           forwards~ G: run_object_get_correct Eo. constructors~.
            applys_and red_spec_object_get_own_prop_args_obj_2_attrs G. destruct a.
             applys_and red_spec_object_get_own_prop_args_obj_3.
              applys_and red_spec_object_get_own_prop_args_obj_4.
              inverts~ R; tryfalse. splits. inverts~ H0. absurd_neg.
             subst p. inverts R.
           subst p. inverts R. symmetry in H3. rewrite H3 in H0. inverts H0.
            forwards~ G: run_object_get_correct H3. constructors~.
            applys_and red_spec_object_get_own_prop_args_obj_2_attrs G. splits~.
            apply~ red_expr_abort.
           subst p. inverts R. false* No.
         applys_and RC. rewrite H0 in R. inverts R. splits. constructors.
          forwards*: RC K. constructors.
       substs. inverts R. splits. constructors.
        forwards*: Co K. constructors.
*)
*)

(*
Lemma run_object_get_prop_correct : forall runs,
  runs_type_correct runs -> forall l,
  follow_object_get_prop l
    (fun S C => run_object_get_prop runs S C l).
Admitted. (* OLD:
   introv E R. simpls. unfolds in E. unmonad_passing.
   applys_and red_spec_object_get_prop R0. destruct x0.
    applys_and red_spec_object_get_prop_1_default. unmonad_passing.
     applys_and RC. cases_if.
      subst x0. constructors_and. unmonad_passing.
       applys_and red_spec_object_get_prop_2_undef R1. destruct x0; tryfalse.
        destruct p0; subst p; inverts R. splits.
         apply~ red_spec_object_get_prop_3_null.
         absurd_neg.
        unmonad. splits.
         apply~ red_spec_object_get_prop_3_not_null. apply* RC0.
         apply* RC0.
      destruct x0; tryfalse. subst p. inverts R. constructors_and.
       splits. apply~ red_spec_object_get_prop_2_not_undef. absurd_neg.
     subst p. inverts R. applys_and RC.  splits. constructors.
      forwards*: RC K. constructors.
*)
*)

Lemma object_proto_is_prototype_of_correct : forall runs,
  runs_type_correct runs ->
  follow_object_proto_is_prototype_of
    (object_proto_is_prototype_of runs).
Admitted.

Lemma run_equal_correct : forall runs,
  runs_type_correct runs ->
  follow_equal (run_equal runs).
Admitted.


Theorem runs_correct : forall num,
  runs_type_correct (runs num).
Proof.
  induction num.
   constructors; try solve [unfolds~ (* Temporary, to remove [True] properties *)];
     introv H; inverts H; introv P; inverts P.
   (* lets [IHe IHs IHp IHc IHhi IHw IHowp IHop IHpo IHeq]: (rm IHnum). *)
   constructors.
     apply~ run_expr_correct.
     apply~ run_stat_correct.
     apply~ run_prog_correct.
     apply~ run_call_correct.
     apply~ run_function_has_instance_correct.
     apply~ run_stat_while_correct.
     solve [unfolds*]. (* apply~ run_object_get_own_prop_correct. *)
     solve [unfolds*]. (* apply~ run_object_get_prop_correct. *)
     apply~ object_proto_is_prototype_of_correct.
     apply~ run_equal_correct.
Qed.


