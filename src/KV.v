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


Definition empty_value : valu := $0.
Definition empty_valuset : valuset := ($0, @nil valu).
Definition entry : Type := (addr * valu).
Definition empty_entry : entry := ($0, $0).

Definition kv_pointer : addr := $0.
Definition kBase : addr := $1.
Definition vBase : addr := $2.

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


Lemma list_prefix_append : forall T (a b : list T) (x : T),
  list_prefix a b ->
  length a < # (maxlen) ->
  length b > length a ->
  list_prefix (a ++ [x]) (upd b (natToWord _ (length a)) x).
Proof.
  intros.
  unfold list_prefix.
  rewrite app_length. simpl.
  unfold upd.
  erewrite wordToNat_natToWord_bound with (bound:=maxlen); try omega.
  rewrite <- firstn_app_updN_eq; auto.
  unfold list_prefix in H.
  rewrite H. reflexivity.
Qed.


(* Abstract representation of list of (key, value) puts. *)
Definition rep l := (exists diskl,
  kv_pointer |-> addr2valu $ (length l) *
  array kBase (map (fun e => addr2valu (fst e)) diskl) $2 *
  array vBase (map snd diskl) $2 *
  [[ length diskl = wordToNat maxlen ]] *
  [[ list_prefix l diskl ]])%pred.


(* Key k isn't in the current store. *)
Definition no_such_put (l : list entry) (k : addr) : Prop :=
  ~ exists v, In (k, v) l.

(* Key k has value v in the current store. *)
Inductive is_last_put : (list entry) -> addr -> valu -> Prop :=
  | KV_no_put : forall k,
    is_last_put nil k empty_value
  | KV_key_eq : forall k v tl,
    is_last_put (tl ++ [(k, v)]) k v
  | KV_key_neq : forall k v k' v' tl,
    k <> k' -> is_last_put tl k v -> is_last_put (tl ++ [(k', v')]) k v.


(* Return `value` for the last instance of `key`. *)
Definition get T (key : addr) xp mscs rx : prog T :=
  mscs <- MEMLOG.begin xp mscs;
  let^ (mscs, kv_p) <- MEMLOG.read xp kv_pointer mscs;
  let^ (mscs, final_value) <- For i < valu2addr kv_p
    Ghost [ F l mbase m ]
    Loopvar [ mscs current_value ]
    Continuation lrx
    Invariant
      MEMLOG.rep xp F (ActiveTxn mbase m) mscs *
      [[ rep l (list2mem m) ]] *
      [[ is_last_put (firstn #i l) key current_value ]]
    OnCrash
      MEMLOG.rep xp F (ActiveTxn mbase m) mscs
    Begin
      let^ (mscs, memory_key) <- MEMLOG.read_array xp kBase i $2 mscs;
      If (weq memory_key (addr2valu key)) {
        let^ (mscs, memory_value) <- MEMLOG.read_array xp vBase i $2 mscs;
        lrx ^(mscs, memory_value)
      } else {
        lrx ^(mscs, current_value)
      }
  Rof ^(mscs, empty_value);
  let^ (mscs, ok) <- MEMLOG.commit xp mscs;
  rx ^(mscs, final_value).


Theorem get_ok: forall key xp mscs,
  {< mbase MF l,
  PRE                   MEMLOG.rep xp MF (NoTransaction mbase) mscs *
                        [[ (rep l)%pred (list2mem mbase) ]]

  POST RET:^(mscs', rvalue)
                        MEMLOG.rep xp MF (NoTransaction mbase) mscs' *
                        [[ is_last_put l key rvalue ]]

  CRASH                 MEMLOG.would_recover_old xp MF mbase
  >} get key xp mscs.
Proof.
  (*unfold get. unfold rep.
  step.
  step.
  constructor.*)


Admitted.


Definition put T (key : addr) (value : valu) xp mscs rx : prog T :=
  mscs <- MEMLOG.begin xp mscs;
  let^ (mscs, kv_p) <- MEMLOG.read xp kv_pointer mscs;
    mscs <- MEMLOG.write xp (kv_pointer) (addr2valu (valu2addr kv_p ^+ $1)) mscs;
    mscs <- MEMLOG.write_array xp kBase (valu2addr kv_p) $2 (addr2valu key) mscs;
    mscs <- MEMLOG.write_array xp vBase (valu2addr kv_p) $2 value mscs;
    let^ (mscs, ok) <- MEMLOG.commit xp mscs;
    If (bool_dec ok true) {
      rx ^(mscs, ok)
    } else {
      rx ^(mscs, false)
    }.

Theorem put_ok: forall key value xp mscs,
  {< mbase F l,
  PRE               MEMLOG.rep xp F (NoTransaction mbase) mscs *
                    [[ (rep l)%pred (list2mem mbase) ]] *
                    [[ length l < # (maxlen) ]]

  (* Q: Does separation logic account for all the is_last_put and rep stuff, or is that necessary here? *)
  POST RET:^(mscs', ok)  ([[ ok = true ]] *
                     exists m', MEMLOG.rep xp F (NoTransaction m') mscs' *
                     [[ (rep (l ++ [(key, value)]))%pred (list2mem m') ]]) \/
                    ([[ ok = false ]] *
                     MEMLOG.rep xp F (NoTransaction mbase) mscs')

  CRASH             MEMLOG.would_recover_old xp F mbase
                    \/
                    (exists m', MEMLOG.would_recover_either xp F mbase m' *
                     [[ (rep (l ++ [(key, value)]))%pred (list2mem m') ]])
  >} put key value xp mscs.
Proof.
  unfold put, rep.
  step.
  step.
  step.
  step.
  rewrite map_length. rewrite H8. rewrite addr2valu2addr.
  erewrite wordToNat_natToWord_bound with (bound:=maxlen). omega. omega.
  step.
  rewrite map_length. rewrite H8. rewrite addr2valu2addr.
  erewrite wordToNat_natToWord_bound with (bound:=maxlen). omega. omega.
  step.
  step.
  step.
  apply pimpl_or_r. left. cancel.
  instantiate (a := upd l $ (length l0) (key, value)).
  repeat rewrite map_upd. rewrite addr2valu2addr.
  cancel.
  (* Need theorem about addr2valu being equal to valu *)
  rewrite app_length. simpl.
  rewrite natToWord_plus. cancel.

  rewrite length_upd. auto. apply list_prefix_append; try (auto; rewrite H8; omega).
  step.
  step.
  step.

  unfold MEMLOG.log_intact.
  cancel.
  apply pimpl_or_r. right. cancel.
  instantiate (a := upd l $ (length l0) (key, value)).
  repeat rewrite map_upd. rewrite addr2valu2addr.
  cancel.

  rewrite app_length. simpl.
  rewrite natToWord_plus. cancel.
  rewrite length_upd. auto. apply list_prefix_append; try (auto; rewrite H8; omega).

  unfold MEMLOG.would_recover_old. cancel.
  unfold MEMLOG.would_recover_old. cancel.
  unfold MEMLOG.would_recover_old. cancel.
  unfold MEMLOG.would_recover_old. cancel.
  unfold MEMLOG.would_recover_old. cancel.
  unfold MEMLOG.would_recover_old. cancel.

Qed.
