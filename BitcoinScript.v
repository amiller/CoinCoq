(* 
 * Author: Andrew Miller, Jan 2012
 *
 * This Source Code Form is subject to the 
 * terms of the Mozilla Public License, v. 
 * 2.0. If a copy of the MPL was not 
 * distributed with this file, You can 
 * obtain one at http://mozilla.org/MPL/2.0/.
 *)

Require Import List Program Omega ZArith Ascii.

(* Utility functions for ByteStrings (and thus bitcoin data stacks) *)
Parameter ByteString : Set.
(*Definition nthWithin (n:nat) : ByteString -> option {x: nat | x < n} := 
  fun s => let z := asInt s in if z < 0 then None else
                                             if asNat z.*)

Parameter bytes_of_Z : Z -> ByteString.
Parameter bytes_of_bool : bool -> ByteString.
Parameter bytes_of_nat : nat -> ByteString.
Parameter Z_of_bytes : ByteString -> Z.
Parameter bool_of_bytes : ByteString -> bool.
Parameter nat_of_bytes : ByteString -> nat.
Parameter length_bytes : ByteString -> nat.
Parameter beq_bytes : ByteString -> ByteString -> bool.


(* Bitcoin transaction datastructure *)
(* UNUSED FOR NOW *)
Record BitcoinTransaction := {
  tx_inputs: list (ByteString * Z * Z);
  tx_outputs: list (ByteString * Z * Z)
}.

(* The internal state of the bitcoin validation machine is a pair of stacks
   of ByteStrings, guarded by an Option.
   pair of ByteString stacks. *)
Definition BtcState := option (prod (list ByteString) (list ByteString)).

(* List of all the OP_CODES *)
Inductive BitcoinOp :=
  (* Constants *)
  | OP_PUSHDATA (data:ByteString) (* all of OP_0-OP_16, and all the OP_PUSHDATA into one *)

  (* Flow Control *)
  | OP_NOP | OP_VERIFY | OP_RETURN
  | OP_IF (stmtsThen stmtsElse:list BitcoinOp) (* If statements are handled by
                                                  the parser ahead of time. *)

  (* Stack *)
  | OP_TOALTSTACK | OP_FROMALTSTACK | OP_IFDUP | OP_DEPTH | OP_DROP
  | OP_DUP | OP_NIP | OP_OVER | OP_PICK | OP_ROLL | OP_ROT | OP_SWAP | OP_TUCK
  | OP_2DROP | OP_2DUP | OP_3DUP | OP_2OVER | OP_2ROT | OP_2SWAP

  (* Splice *)
  (* OP_CAT | OP_SUBSTR | OP_LEFT | OP_RIGHT | Marked disabled *)
  | OP_SIZE

  (* Bitwise Logic *)
  (* OP_INVERT | OP_AND | OP_AND | OP_XOR | Marked disabled *)
  | OP_EQUAL | OP_EQUALVERIFY

  (* Arithmetic (4-byte-integers) *)
  (* OP_2MUL | OP_2DIV | OP_MUL | OP_DIV | OP_MOD | 
     OP_LSHIFT | OP_RSHIFT | Marked disabled *)
  | OP_1ADD | OP_1SUB | OP_NEGATE | OP_ABS | OP_NOT | OP_0NOTEQUAL | OP_ADD
  | OP_SUB | OP_BOOLAND | OP_BOOLOR | OP_NUMEQUAL | OP_NUMEQUALVERIFY
  | OP_NUMNOTEQUAL | OP_LESSTHAN | OP_GREATERTHAN | OP_LESSTHANOREQUAL 
  | OP_GREATERTHANOREQUAL | OP_MIN | OP_MAX | OP_WITHIN.


(* Helper functions, would probably be easier just to use monads *)
Definition binOpZZZ (f: Z -> Z -> Z) : BtcState -> BtcState :=
  fun os => match os with Some (x2::x1::s, alt) =>
                          Some (bytes_of_Z (f (Z_of_bytes x1) 
                                              (Z_of_bytes x2))::s, alt)
                   | _ => None end.

Definition binOpBBB (f: bool -> bool -> bool) : BtcState -> BtcState :=
  fun os => match os with Some (x2::x1::s, alt) =>
                          Some (bytes_of_bool (f (bool_of_bytes x1) 
                                                 (bool_of_bytes x2))::s, alt)
                   | _ => None end.

Definition binOpZZB (f: Z -> Z -> bool) : BtcState -> BtcState :=
  fun os => match os with Some (x1::x2::s, alt) =>
                          Some (bytes_of_bool (f (Z_of_bytes x1) 
                                                 (Z_of_bytes x2))::s, alt)
                   | _ => None end.

Definition unaryOpZB (f: Z -> bool) : BtcState -> BtcState :=
  fun os => match os with Some (x1::s, alt) =>
                          Some (bytes_of_bool (f (Z_of_bytes x1))::s, alt)
                        | _ => None end.

Definition unaryOpBB (f: bool -> bool) : BtcState -> BtcState :=
  fun os => match os with Some (x1::s, alt) =>
                          Some (bytes_of_bool (f (bool_of_bytes x1))::s, alt)
                        | _ => None end.

Definition unaryOpZZ (f: Z -> Z) : BtcState -> BtcState :=
  fun os => match os with Some (x1::s, alt) =>
                          Some (bytes_of_Z (f (Z_of_bytes x1))::s, alt)
                        | _ => None end.

Section BitcoinTxValidate.
Parameter tx : BitcoinTransaction.

(* Denotational semantics for each OP_CODE *)
Fixpoint BitcoinOpDenote (os : BtcState) (i:BitcoinOp) : BtcState :=
  match i with 

  (* Constants *)
  | OP_PUSHDATA data => match os with Some (s', alt) => 
                                      Some (data::s', alt) 
                                    | _ => None end

  (* Flow Control *)
  | OP_NOP => os

  | OP_VERIFY => match os with Some (x1::s', alt) =>
      if bool_of_bytes x1 then Some (s', alt) else None 
                        | _ => None end

  | OP_RETURN => None

  | OP_IF stmtsThen stmtsElse => 
                match os with Some (x1::s', alt) =>
     if bool_of_bytes x1 then fold_left BitcoinOpDenote stmtsThen (Some (s', alt))
                         else fold_left BitcoinOpDenote stmtsElse (Some (s', alt))
                       | _ => None end

  (* Stack *)
  | OP_TOALTSTACK => match os with Some (x1::s, alt) =>
                                   Some (s, x1::alt) | _ => None end

  | OP_FROMALTSTACK => match os with Some (s, x1::alt) =>
                                     Some (x1::s, alt) | _ => None end

  | OP_IFDUP => match os with Some (e::s, alt) =>
      if bool_of_bytes e then Some (e::e::s, alt) 
                         else Some (e::s, alt)
                       | _ => None end

  | OP_DEPTH => match os with Some (s, alt) =>
                              Some (bytes_of_nat (length s)::s, alt) | _ => None end

  | OP_DROP => match os with Some (x1::s, alt) => 
                             Some (s, alt) | _ => None end

  | OP_DUP => match os with Some (x1::s, alt) => 
                            Some (x1::x1::s, alt) | _ => None end

  | OP_NIP => match os with Some (x1::x2::s, alt) =>
                            Some (x1::s, alt) | _ => None end

  | OP_OVER => match os with Some (x2::x1::s, alt) =>
                             Some (x1::x2::x1::s, alt) | _ => None end

  | OP_PICK => None 
  | OP_ROLL => None
 (*match os with Some (ns::s, alt) => let n := asInt ns in
                                                  if n < 0 or n > k
                                                  
                                                  Exists s x,  (asInt ns) s 
                             
                           | _ => None end*)
  | OP_ROT => match os with Some (x3::x2::x1::s, alt) =>
                            Some (x1::x3::x2::s, alt) | _ => None end

  | OP_SWAP => match os with Some (x2::x1::s, alt) =>
                             Some (x1::x2::s, alt) | _ => None end

  | OP_TUCK => match os with Some (x2::x1::s, alt) =>
                             Some (x2::x1::x2::s, alt) | _ => None end

  | OP_2DROP => match os with Some (x2::x1::s, alt) =>
                              Some (s, alt) | _ => None end

  | OP_2DUP => match os with Some (x2::x1::s, alt) => 
                             Some (x2::x1::x2::x1::s, alt) | _ => None end

  | OP_3DUP => match os with Some (x3::x2::x1::s, alt) =>
                             Some (x3::x2::x1::x3::x2::x1::s, alt) | _ => None end

  | OP_2OVER => match os with Some (x4::x3::x2::x1::s, alt) =>
                              Some (x2::x1::x4::x3::x2::x1::s, alt) | _ => None end

  | OP_2ROT => match os with Some (x6::x5::x4::x3::x2::x1::s, alt) =>
                             Some (x2::x1::x6::x5::x4::x3::s, alt) | _ => None end

  | OP_2SWAP => match os with Some (x4::x3::x2::x1::s, alt) =>
                              Some (x2::x1::x4::x3::s, alt) | _ => None end

  (* Splice *)
  | OP_SIZE => match os with Some (x1::s, alt) =>
                             Some (bytes_of_nat (length_bytes x1)::x1::s, alt) | _ => None end
  
  (* Bitwise Logic *)
  | OP_EQUAL => match os with Some (x2::x1::s, alt) =>
                              Some (bytes_of_bool (beq_bytes x1 x2)::s, alt) | _ => None end

  | OP_EQUALVERIFY => match os with Some (x2::x1::s, alt) =>
           if (beq_bytes x1 x2) then Some (s, alt) else None | _ => None end

  (* Arithmetic (4-byte-integers) *)
  (* OP_2MUL | OP_2DIV | OP_MUL | OP_DIV | OP_MOD | 
     OP_LSHIFT | OP_RSHIFT | Marked disabled *)
  | OP_1ADD => unaryOpZZ (Zplus 1) os
  | OP_1SUB => unaryOpZZ (fun x => Zminus x 1) os
  | OP_NEGATE => unaryOpZZ Zopp os
  | OP_ABS => unaryOpZZ Zabs os

  | OP_NOT => match os with Some (x1::s, alt) =>
                            Some (bytes_of_bool (negb (bool_of_bytes x1))::s, alt) 
                     | _ => None end

  | OP_0NOTEQUAL => match os with Some (x1::s, alt) =>
                                  Some (bytes_of_bool 
                                       (Zneq_bool 0%Z 
                                       (Z_of_bytes x1))::s, alt)
                           | _ => None end

  | OP_ADD => binOpZZZ Zplus os
  | OP_SUB => binOpZZZ Zminus os
  | OP_BOOLAND => binOpBBB andb os
  | OP_BOOLOR => binOpBBB orb os
  | OP_NUMEQUAL => binOpZZB Zeq_bool os
  | OP_NUMEQUALVERIFY => match os with Some (x2::x1::s, alt) => 
                                    if Zeq_bool (Z_of_bytes x1) (Z_of_bytes x2)
                                    then Some (s, alt) else None | _ => None end
  | OP_NUMNOTEQUAL => binOpZZB Zneq_bool os
  | OP_LESSTHAN => binOpZZB Zlt_bool os
  | OP_GREATERTHAN => binOpZZB Zgt_bool os
  | OP_LESSTHANOREQUAL => binOpZZB Zle_bool os
  | OP_GREATERTHANOREQUAL => binOpZZB Zge_bool os
  | OP_MIN => binOpZZZ (fun a b => if Zlt_bool a b then a else b) os
  | OP_MAX => binOpZZZ (fun a b => if Zgt_bool a b then a else b) os
  | OP_WITHIN => match os with Some (x::min::max::s, alt) =>
                       let x := Z_of_bytes x in
                       Some (bytes_of_bool (andb (Zge_bool x (Z_of_bytes min))
                                                 (Zlt_bool x (Z_of_bytes max)))::s, alt)
                                      | _ => None end
  end.

End BitcoinTxValidate.


(* Aliases *)
Definition OP_0 := OP_PUSHDATA (bytes_of_Z 0).
Definition OP_1 := OP_PUSHDATA (bytes_of_Z 1).
Definition OP_2 := OP_PUSHDATA (bytes_of_Z 2).
Definition OP_3 := OP_PUSHDATA (bytes_of_Z 3).
Definition OP_4 := OP_PUSHDATA (bytes_of_Z 4).
Definition OP_5 := OP_PUSHDATA (bytes_of_Z 5).
Definition OP_6 := OP_PUSHDATA (bytes_of_Z 6).
Definition OP_7 := OP_PUSHDATA (bytes_of_Z 7).
Definition OP_8 := OP_PUSHDATA (bytes_of_Z 8).
Definition OP_9 := OP_PUSHDATA (bytes_of_Z 9).
Definition OP_10 := OP_PUSHDATA (bytes_of_Z 10).
Definition OP_11 := OP_PUSHDATA (bytes_of_Z 11).
Definition OP_12 := OP_PUSHDATA (bytes_of_Z 12).
Definition OP_13 := OP_PUSHDATA (bytes_of_Z 13).
Definition OP_14 := OP_PUSHDATA (bytes_of_Z 14).
Definition OP_15 := OP_PUSHDATA (bytes_of_Z 15).
Definition OP_16 := OP_PUSHDATA (bytes_of_Z 16).

(* Execution *)
Definition InitialState : BtcState := Some ([], []).

Program Definition EvalScript fragment s := 
  fold_left BitcoinOpDenote fragment s.

Program Definition EvalScriptInit fragment := EvalScript fragment InitialState.
