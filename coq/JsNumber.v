(* Set Implicit Arguments. *)
(* Require Export Shared. *)
Require Floats PrimFloat.
Require Import BinPos Zpower ZArith.
Require Import String.


(**************************************************************)
(** ** Type for number (IEEE floats) *)

Definition number : Set := (* XXX Changed from Type, this may be significant for JsCert -JS *)
  PrimFloat.float.


(**************************************************************)
(** ** Particular values of numbers *)

Definition nan : number := PrimFloat.nan.
Definition zero : number := PrimFloat.zero.
Definition neg_zero : number := PrimFloat.neg_zero.
Definition one := PrimFloat.one.
Definition neg_one := Eval compute in (PrimFloat.opp PrimFloat.one).
Definition infinity : number := PrimFloat.infinity.
Definition neg_infinity : number := PrimFloat.neg_infinity.

(*
Definition max_value : number :=
  Fappli_IEEE.B754_finite 53 1024 false ((shift_pos 53 1)-1)%positive (1024-53)%Z (eq_refl true).
Definition min_value : number :=
   Fappli_IEEE.B754_finite 53 1024 false 1 (-1074) (eq_refl true). (* 1x2e1-1074 *)
 *)

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

Definition neg : number -> number := PrimFloat.opp.
Parameter floor : number -> number.  (* Note: not in flocq maybe in the future *)
Definition absolute : number -> number :=  PrimFloat.abs.

Definition sign : number -> number := (* Note: This sign function is consistent with Math.sign in JavaScript *)
  fun x => match PrimFloat.classify x with
        | FloatClass.PNormal => one
        | FloatClass.NNormal => neg_one
        | _ => x
        end.

Definition lt_bool : number -> number -> bool := PrimFloat.ltb.

(**************************************************************)
(** ** Binary operations on numbers *)

Definition add : number -> number -> number := PrimFloat.add.

Definition sub : number -> number -> number := PrimFloat.sub.

Parameter fmod : number -> number -> number. (* Note: may come in next version of float *)

Definition mult : number -> number -> number := PrimFloat.mul.

Definition div : number -> number -> number := PrimFloat.div.

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
