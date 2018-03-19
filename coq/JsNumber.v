(* Set Implicit Arguments. *)
(* Require Export Shared. *)
Require Flocq.Appli.Fappli_IEEE Flocq.Appli.Fappli_IEEE_bits.
Require Import BinPos Zpower ZArith.
Require Import String.


(**************************************************************)
(** ** Type for number (IEEE floats) *)

Definition number : Set := (* XXX Changed from Type, this may be significant for JsCert -JS *)
  Fappli_IEEE_bits.binary64.


(**************************************************************)
(** ** Particular values of numbers *)

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
Definition max_value : number :=
  Fappli_IEEE.B754_finite 53 1024 false ((shift_pos 53 1)-1)%positive (1024-53)%Z (eq_refl true).
Definition min_value : number :=
   Fappli_IEEE.B754_finite 53 1024 false 1 (-1074) (eq_refl true). (* 1x2e1-1074 *)
Parameter pi : number.
Parameter e : number.
Parameter ln2 : number.

(**************************************************************)
(** ** Conversions on numbers *)

(* LATER: implement definitions *)
Parameter from_string : string -> number.
Parameter to_string : number -> string.

(**************************************************************)
(** ** Unary operations on numbers *)

Definition neg : number -> number :=
  Fappli_IEEE_bits.b64_opp.
Parameter floor : number -> number.  (* Note: not in flocq maybe in the future *)
Definition absolute : number -> number :=
  Fappli_IEEE.Babs 53 1024 pair.
Definition sign : number -> number := (* Note: This sign function is consistent with Math.sign in JavaScript *)
  fun x => match x with
  | Fappli_IEEE.B754_nan _ _ s _ => x
  | Fappli_IEEE.B754_zero _ _ s => x
  | Fappli_IEEE.B754_infinity _ _ s => x
  | Fappli_IEEE.B754_finite _ _ s _ _ _ =>
    if s
    then neg_one
    else one
  end.
Definition lt_bool (n1 n2 : number) : bool :=
  match Fappli_IEEE.Bcompare _ _ n1 n2 with
  | Some Lt => true
  | Some _ => false
  | None => false (* Note: This is for nan, always false, except for not equal *)
  end.


(**************************************************************)
(** ** Binary operations on numbers *)

Definition add : number -> number -> number :=
  Fappli_IEEE_bits.b64_plus Fappli_IEEE.mode_NE.

Definition sub : number -> number -> number :=
  Fappli_IEEE_bits.b64_minus Fappli_IEEE.mode_NE.

Parameter fmod : number -> number -> number. (* Note: may come in next version of Flocq *)

Definition mult : number -> number -> number :=
  Fappli_IEEE_bits.b64_mult Fappli_IEEE.mode_NE.

Definition div : number -> number -> number :=
  Fappli_IEEE_bits.b64_div Fappli_IEEE.mode_NE.

(* Todo: find comparison operator *)
(* Global Instance number_comparable : Comparable number.
Proof. Admitted. *)

(**************************************************************)
(** ** Conversions with Int32 *)

(* Parameter of_int : int -> number. (* LATER: this is quite complex. Should we make it precise? *) *)

(* Parameter to_int32 : number -> int. (* Remark: extracted code could, for efficiency reasons, use Ocaml Int32 *)  *)

(* Parameter to_uint32 : number -> int. *)

(* Parameter to_int16 : number -> int. (* currently not used *) *)

(* LATER: Check that the OCaml extraction is correct. *)


(**************************************************************)

(** Implements the operation that masks all but the 5 least significant bits
   of a non-negative number (obtained as the result of to_uint32 *)

(* Parameter modulo_32 : int -> int. *)

(** Implements int32 operation *)

(* Parameter int32_bitwise_not : int -> int. *)

(* Parameter int32_bitwise_and : int -> int -> int. *)
(* Parameter int32_bitwise_or : int -> int -> int. *)
(* Parameter int32_bitwise_xor : int -> int -> int. *)

(* Parameter int32_left_shift : int -> int -> int. *)
(* Parameter int32_right_shift : int -> int -> int. *)
(* Parameter uint32_right_shift : int -> int -> int. *)




(**************************************************************)
(** ** Int32 related conversion *)
