(* 
 * Author: Andrew Miller, Jan 2012
 *
 * This Source Code Form is subject to the 
 * terms of the Mozilla Public License, v. 
 * 2.0. If a copy of the MPL was not 
 * distributed with this file, You can 
 * obtain one at http://mozilla.org/MPL/2.0/.
 *)

(* Import the specification for the BitcoinScript machine. *)
Require Import BitcoinScript.
Require Import List Program Ascii.

(* Simple computation examples. Scripts can be evaluated to 
   produce results, i.e. a simulator/interpreter. *)
Eval compute in EvalScriptInit [OP_1; OP_IFDUP; OP_DUP; OP_IFDUP].
Eval compute in EvalScriptInit [OP_0; OP_IFDUP].
Eval compute in EvalScriptInit [OP_0; OP_IF [OP_DUP] []].

(* Universal quantification over scripts and states *)

(* The error state is preserved regardless of the operation *)
Lemma none_stays : forall fragment, EvalScript fragment None = None.
Proof.
induction fragment; auto.
induction a; auto. Qed.

(* An entire family of scripts can be shown to fail *)
Example testA : forall x, EvalScriptInit (OP_DUP::x) = None.
Proof. 
intros. unfold EvalScriptInit. simpl. apply none_stays. Qed.

(* Two fragments of a script can be shown equivalent by 
   quantifying over all possible input states *)
Example eq_ifdup : forall s, EvalScript [OP_IFDUP] s = 
                             EvalScript [OP_DUP; OP_IF [OP_DUP] []] s.
intros.
unfold EvalScript. 
destruct s.
destruct p as (main, alt). destruct main; auto.
auto. Qed.