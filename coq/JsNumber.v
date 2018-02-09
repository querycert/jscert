Require Flocq.Appli.Fappli_IEEE Flocq.Appli.Fappli_IEEE_bits.

(**************************************************************)
(** ** Type for number (IEEE floats) *)

Definition number : Set :=
  Fappli_IEEE_bits.binary64.


(**************************************************************)
(** ** Particular values of numbers *)

(* LATER: find definitions in Flocq *)
Parameter nan : number.
Parameter zero : number.
Parameter neg_zero : number.
Definition one := Fappli_IEEE.binary_normalize 53 1024 eq_refl eq_refl Fappli_IEEE.mode_NE 1 0 false.
Parameter infinity : number.
Parameter neg_infinity : number.
Parameter max_value : number.
Parameter min_value : number.
Parameter pi : number.
Parameter e : number.
Parameter ln2 : number.

(**************************************************************)
(** ** Conversions on numbers *)

(* LATER: implement definitions *)
Require Import String.
Parameter from_string : string -> number.
Parameter to_string : number -> string.

(**************************************************************)
(** ** Unary operations on numbers *)

(* LATER: find definitions in Flocq *)

Parameter neg : number -> number.
Parameter floor : number -> number.
Parameter absolute : number -> number.
Parameter sign : number -> number. (* returns arbitrary when x is zero or nan *)
Parameter lt_bool : number -> number -> bool.


(**************************************************************)
(** ** Binary operations on numbers *)

Definition add : number -> number -> number :=
  Fappli_IEEE_bits.b64_plus Fappli_IEEE.mode_NE.

Parameter sub : number -> number -> number. (* todo: bind *)

Parameter fmod : number -> number -> number. (* todo: bind *)

Definition mult : number -> number -> number :=
  Fappli_IEEE_bits.b64_mult Fappli_IEEE.mode_NE.

Definition div : number -> number -> number :=
  Fappli_IEEE_bits.b64_div Fappli_IEEE.mode_NE.

(* Todo: find comparison operator *)
(*
Global Instance number_comparable : Comparable number.
Proof. Admitted.
*)


