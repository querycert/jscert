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
Parameter ocaml_float : Set.
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

Parameter from_float : ocaml_float -> number.
Parameter to_float : number -> ocaml_float.

(**************************************************************)
(** ** Unary operations on numbers *)

(* LATER: find definitions in Flocq *)

Definition neg : number -> number :=
  Fappli_IEEE_bits.b64_opp.
Parameter floor : number -> number.  (** NOT IN FLOCQ maybe in the longer future *)
Definition b64_abs : number -> number :=
  Fappli_IEEE.Babs 53 1024 pair.
Definition absolute : number -> number := b64_abs.

Definition lt_bool (n1 n2 : number) :=
  match Fappli_IEEE.Bcompare _ _ n1 n2 with
  | Some Lt => true
  | Some _ => false
  | None => false (**r None is for nan, always false, except for not equal *)
  end.

(* This sign function is consistent with Math.sign in JavaScript *)
Definition sign : number -> number :=
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

Definition add : number -> number -> number :=
  Fappli_IEEE_bits.b64_plus Fappli_IEEE.mode_NE.

Definition sub : number -> number -> number :=
  Fappli_IEEE_bits.b64_minus Fappli_IEEE.mode_NE.

Parameter fmod : number -> number -> number. (* todo: bind *)
(** Note: may come in next version of Flocq *)

Definition mult : number -> number -> number :=
  Fappli_IEEE_bits.b64_mult Fappli_IEEE.mode_NE.

Definition div : number -> number -> number :=
  Fappli_IEEE_bits.b64_div Fappli_IEEE.mode_NE.

