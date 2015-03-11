Require Import Prog.
Require Import SepAuto.
Require Import Hoare.
Require Import Word.
Require Import Pred.
Require Import List.
Require Import BasicProg.
Require Import Arith.
Require Import Omega.
Require Import Array.
Require Import Psatz.
Require Import MemLog.
Require Import Bool.
Require Import GenSep.

Import ListNotations.

Set Implicit Arguments.

Parameter maxlen : addr. (* Number of entries on disk *)

Definition kv_pointer := addr.
Definition empty_value : valu := $0.
Definition empty_valuset : valuset := ($0, @nil valu).
Definition entry : Type := (addr * valu).
Definition empty_entry : entry := ($0, $0).

Definition kBase : addr := $0.
Definition vBase : addr := $1.

Definition list_prefix A (p l : list A) :=
  firstn (length p) l = p.

Lemma list_prefix_length: forall T (a b : list T), list_prefix a b
  -> length a <= length b.
Proof.
  unfold list_prefix; intros.
  rewrite <- H.
  rewrite firstn_length.
  lia.
Qed.

(* Abstract representation of list of (key, value) puts. *)
Definition rep l (kv_p : kv_pointer) := (exists diskl,
  array kBase (map (fun e => addr2valu (fst e)) diskl) $2 *
  array vBase (map snd diskl) $2 *
  [[ length l = wordToNat kv_p ]] *
  [[ length diskl = wordToNat maxlen ]] *
  [[ list_prefix l diskl ]])%pred.


(* Key k isn't in the current store. *)
Definition no_such_put (l : list entry) (k : addr) : Prop :=
  ~ exists v, In (k, v) l.

(* Key k has value v in the current store. *)
(* Q: Changed from Fixpoint so that I could assert that is_last_put is true
      for empty_value. Better way to do that? *)
Inductive is_last_put : (list entry) -> addr -> valu -> Prop :=
  | KV_no_put : forall k,
    is_last_put nil k empty_value
  | KV_key_eq : forall k v tl,
    is_last_put (tl ++ [(k, v)]) k v
  | KV_key_neq : forall k v k' v' tl,
    k <> k' -> is_last_put tl k v -> is_last_put (tl ++ [(k', v')]) k v.


(* Return `value` for the last instance of `key`. *)
Definition get T (kv_p : kv_pointer) (key : addr) xp mscs rx : prog T :=
  mscs <- MEMLOG.begin xp mscs;
  let^ (mscs, final_value) <- For i < kv_p
    Ghost [ F l mbase m ]
    Loopvar [ mscs current_value ]
    Continuation lrx
    Invariant
      MEMLOG.rep xp F (ActiveTxn mbase m) mscs *
      [[ rep l kv_p (list2mem m) ]] *
      [[ is_last_put (firstn #i l) key current_value ]]
    OnCrash
      MEMLOG.rep xp F (ActiveTxn mbase m) mscs
    Begin
      let^ (mscs, memory_key) <- MEMLOG.read_array xp $0 i $2 mscs;
      If (weq memory_key (addr2valu key)) {
        let^ (mscs, memory_value) <- MEMLOG.read_array xp $1 i $2 mscs;
        lrx ^(mscs, memory_value)
      } else {
        lrx ^(mscs, current_value)
      }
  Rof ^(mscs, empty_value);
  let^ (mscs, ok) <- MEMLOG.commit xp mscs;
  rx ^(mscs, final_value).


Theorem get_ok: forall kv_p key xp mscs,
  {< mbase MF l,
  PRE                   MEMLOG.rep xp MF (NoTransaction mbase) mscs *
                        [[ (rep l kv_p)%pred (list2mem mbase) ]]

  POST RET:^(mscs', rvalue)
                        MEMLOG.rep xp MF (NoTransaction mbase) mscs' *
                        [[ is_last_put l key rvalue ]]

  CRASH                 MEMLOG.would_recover_old xp MF mbase
  >} get kv_p key xp mscs.
Proof.
  unfold get. unfold rep.
  step.
  step.
  constructor.


Admitted.

Definition put T (kv_p : kv_pointer) (key : addr) (value : valu) xp mscs rx : prog T :=
  mscs <- MEMLOG.begin xp mscs;
    mscs <- MEMLOG.write_array xp $0 kv_p $2 (addr2valu key) mscs;
    mscs <- MEMLOG.write_array xp $1 kv_p $2 value mscs;
    let^ (mscs, ok) <- MEMLOG.commit xp mscs;
    If (bool_dec ok true) {
      rx ^(mscs, ok)
    } else {
      rx ^(mscs, false)
    }.

Theorem put_ok: forall kv_p key value xp mscs,
  {< mbase F l,
  PRE               MEMLOG.rep xp F (NoTransaction mbase) mscs *
                    [[ (rep l kv_p)%pred (list2mem mbase) ]] *
                    [[ (kv_p < maxlen)%word ]]

  (* Q: Does separation logic account for all the is_last_put and rep stuff, or is that necessary here? *)
  POST RET:^(mscs', ok)  ([[ ok = true ]] *
                     exists m', MEMLOG.rep xp F (NoTransaction m') mscs' *
                     [[ (rep (l ++ [(key, value)]) (kv_p ^+ $1))%pred (list2mem m') ]]) \/
                    ([[ ok = false ]] *
                     MEMLOG.rep xp F (NoTransaction mbase) mscs')

  CRASH             MEMLOG.would_recover_old xp F mbase
                    \/
                    (exists m', MEMLOG.would_recover_either xp F mbase m' *
                     [[ (rep (l ++ [(key, value)]) (kv_p ^+ $1))%pred (list2mem m') ]])
  >} put kv_p key value xp mscs.
Proof.
  unfold put, rep.
  step.
  step.
  rewrite map_length. rewrite H8. apply wlt_lt in H4. assumption.
  step.
  rewrite map_length. rewrite H8. apply wlt_lt in H4. assumption.
  step.
  step.
  step.

  apply pimpl_or_r. left. cancel.
  instantiate (a := upd l kv_p (key, value)).
  repeat rewrite map_upd.
  cancel.
  rewrite app_length. rewrite H9. rewrite wplus_alt. unfold wplusN, wordBinN.
  erewrite wordToNat_natToWord_bound with (bound:=maxlen). simpl. omega. simpl. apply wlt_lt in H4. omega.

  rewrite length_upd. auto.
  unfold upd. rewrite <- H9.

  admit.

  step.
  step.
  step.

  unfold MEMLOG.log_intact.
  cancel.
(*  apply pimpl_or_r. right. cancel. *)
  admit.

  unfold MEMLOG.would_recover_old. cancel.
  unfold MEMLOG.would_recover_old. cancel.
  unfold MEMLOG.would_recover_old. cancel.
  unfold MEMLOG.would_recover_old. cancel.


  cancel.


Admitted.