Require Flocq.Appli.Fappli_IEEE Flocq.Appli.Fappli_IEEE_bits.

(**************************************************************)
(** ** Type for number (IEEE floats) *)

Definition number : Set :=
  Fappli_IEEE_bits.binary64.


(**************************************************************)
(** ** Particular values of numbers *)

(** !!! B755_zero false = +0 ; B755_zero true = -0 *)

Definition nan : number :=
  let (sign,nan) := Fappli_IEEE_bits.default_nan_pl64 in
  Fappli_IEEE.B754_nan _ _ sign nan.
Definition zero : number :=
  Fappli_IEEE.B754_zero _ _ false.
Definition neg_zero : number :=
  Fappli_IEEE.B754_zero _ _ true.
Definition one :=
  Fappli_IEEE.binary_normalize 53 1024 eq_refl eq_refl Fappli_IEEE.mode_NE 1 0 false.
Definition neg_one :=
  Fappli_IEEE.binary_normalize 53 1024 eq_refl eq_refl Fappli_IEEE.mode_NE 1 0 true.
Definition infinity : number :=
  Fappli_IEEE.B754_infinity _ _ false.
Definition neg_infinity : number :=
  Fappli_IEEE.B754_infinity _ _ true.

Require Import BinPos.
Require Import Zpower.
Require Import ZArith.

Definition max_value : number :=
  Fappli_IEEE.B754_finite 53 1024 false ((shift_pos 53 1)-1)%positive (1024-53)%Z (eq_refl true). (* *)
Definition min_value : number :=
   Fappli_IEEE.B754_finite 53 1024 false 1 (-1074) (eq_refl true). (* 1x2e1-1074 *)

(**************************************************************)
(** ** Conversions on numbers *)

Require Import String.
Definition float_triple : Set := (bool * positive * Z).
Definition float_triple_to_b64 (ft:float_triple) : number :=
  let '(sign, m, e) := ft in
  match e with
  | Z0 => Fappli_IEEE.B754_zero _ _ false
  | Zneg e =>
    let my :=
        match Zpower_pos 10 e with
        | Zpos p => p
        | _ => xH
        end
    in
    Fappli_IEEE.FF2B
      53 1024 _
      (proj1
         (Fappli_IEEE.Bdiv_correct_aux
            53 1024
            (eq_refl Lt) (eq_refl Lt)
            Fappli_IEEE.mode_NE
            sign m 0
            false my 0))
  | Zpos e =>
    Fappli_IEEE.B754_zero _ _ false
  end.

Parameter from_string : string -> number.
Parameter to_string : number -> string.

(**************************************************************)
(** ** Unary operations on numbers *)

(* LATER: find definitions in Flocq *)

Definition number_neg : number -> number :=
  Fappli_IEEE_bits.b64_opp.
Parameter number_floor : number -> number.  (** Note: not in flocq maybe in the longer future *)
Definition number_b64_abs : number -> number :=
  Fappli_IEEE.Babs 53 1024 pair.
Definition number_absolute : number -> number := number_b64_abs.

(* This sign function is consistent with Math.sign in JavaScript *)
Definition number_sign : number -> number :=
  fun x => match x with
  | Fappli_IEEE.B754_nan _ _ s _ => x
  | Fappli_IEEE.B754_zero _ _ s => x
  | Fappli_IEEE.B754_infinity _ _ s => x
  | Fappli_IEEE.B754_finite _ _ s _ _ _ =>
    if s
    then neg_one
    else one
  end.

(**************************************************************)
(** ** Binary operations on numbers *)

Definition number_add : number -> number -> number :=
  Fappli_IEEE_bits.b64_plus Fappli_IEEE.mode_NE.

Definition number_sub : number -> number -> number :=
  Fappli_IEEE_bits.b64_minus Fappli_IEEE.mode_NE.

Parameter number_mod : number -> number -> number. (** Note: may come in next version of Flocq *)

Definition number_mult : number -> number -> number :=
  Fappli_IEEE_bits.b64_mult Fappli_IEEE.mode_NE.

Definition number_div : number -> number -> number :=
  Fappli_IEEE_bits.b64_div Fappli_IEEE.mode_NE.

Require Import List.
(** Defines additional operations on FLOATs *)
(** Unary operations *)

Parameter number_sqrt : number -> number. (** In Flocq *)
Parameter number_exp : number -> number.
Parameter number_log : number -> number.
Parameter number_log10 : number -> number.
Parameter number_ceil : number -> number.
Parameter number_eq : number -> number -> bool. (* TODO by Jerome pattern matching on B754 *)

Conjecture number_eq_correct :
  forall f1 f2, (number_eq f1 f2 = true <-> f1 = f2).

Require Import EquivDec.
Lemma number_eq_dec : EqDec number eq.
Proof.
  unfold EqDec.
  intros x y.
  case_eq (number_eq x y); intros eqq.
  + left.
    f_equal.
    apply number_eq_correct in eqq.
    trivial.
  + right; intros eqq2.
    red in eqq2.
    apply number_eq_correct in eqq2.
    congruence.
Defined.
  
Parameter number_pow : number -> number -> number.
Parameter number_min : number -> number -> number. (** Check in JS spec what happens for min/max *)
Parameter number_max : number -> number -> number.
Parameter number_ne : number -> number -> bool.
Definition number_lt (n1 n2 : number) :=
  match Fappli_IEEE.Bcompare _ _ n1 n2 with
  | Some Lt => true
  | Some _ => false
  | None => false (**r None is for nan, always false, except for not equal *)
  end.
Parameter number_le : number -> number -> bool.
Parameter number_gt : number -> number -> bool.
Parameter number_ge : number -> number -> bool.

Require Import ZArith.
Parameter number_of_int : Z -> number. (** Binary normalize *)
Parameter number_truncate : number -> Z. (** Do like parsing ... *)

Definition number_list_min (l:list number) : number :=
  fold_right (fun x y => number_min x y) infinity l.

Definition number_list_max (l:list number) : number :=
  fold_right (fun x y => number_max x y) neg_infinity l.

Definition number_list_sum (l:list number) : number :=
  fold_right (fun x y => number_add x y) zero l.

Definition number_list_arithmean (l:list number) : number :=
  let ll := List.length l in
  match ll with
  | O => zero
  | _ => number_div (number_list_sum l) (number_of_int (Z_of_nat ll))
  end.

