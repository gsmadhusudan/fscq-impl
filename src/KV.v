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
  array $0 (map (fun e => addr2valu (fst e)) diskl) $2 *
  array $1 (map snd diskl) $2 *
  [[ length diskl = wordToNat maxlen / 2 ]] *
  [[ length l = wordToNat kv_p ]] *
  [[ list_prefix l diskl ]])%pred.


(* Key k isn't in the current store. *)
Definition no_such_put (l : list entry) (k : addr) : Prop :=
  ~ exists v, In (k, v) l.

(*
Fixpoint is_last_put (l : list entry) (k : addr) (v : valu) :=
  match l with
  | nil => False
  | (k', v') :: tl =>
    (k = k' /\ v = v' /\ no_such_put l k) \/
    (is_last_put tl k v)
  end.
*)

(* Key k has value v in the current store. *)
(* Q: Changed from Fixpoint so that I could assert that is_last_put is true
      for empty_value. Better way to do that? *)
Inductive is_last_put : (list entry) -> addr -> valu -> Prop :=
  | KV_no_put : forall k,
    is_last_put nil k empty_value
  | KV_key_eq : forall k v tl,
    no_such_put tl k -> is_last_put ((k, v) :: tl) k v
  | KV_key_neq : forall k v k' v' tl,
    ~(k = k') \/ v = v' -> is_last_put tl k v -> is_last_put ((k', v') :: tl) k v.


(* Return `value` for the last instance of `key`. *)
Definition get T (kv_p : kv_pointer) (key : addr) xp cs rx : prog T :=
  mscs <- MEMLOG.begin xp cs;
  let2 (mscs, final_value) <- For i < kv_p
    Ghost F
    Loopvar current_value <- (mscs, empty_value)
    Continuation lrx
    Invariant
      F
    OnCrash
      F
    Begin
      let2 (mscs, memory_key) <- MEMLOG.read xp i mscs;
      if (weq memory_key (addr2valu key)) then
        let2 (mscs, memory_value) <- MEMLOG.read xp (i ^+ $1) mscs;
        lrx (mscs, memory_value)
      else
        lrx current_value
  Rof;
  let2 (mscs, ok) <- MEMLOG.commit xp mscs;
  If (bool_dec ok true) {
    rx (mscs, final_value)
  } else {
    rx (mscs, empty_value)
  }.

Hint Rewrite map_length.


Theorem get_ok: forall kv_p key xp cs,
  {< mbase F l value,
  PRE                   MEMLOG.rep xp (NoTransaction mbase) (ms_empty, cs) *
                        [[ is_last_put l key value ]] *
                        [[ (rep l kv_p * F)%pred (list2mem mbase) ]]

  POST:(mscs', rvalue)  MEMLOG.rep xp (NoTransaction mbase) mscs' *
                        [[ value = rvalue ]] *
                        [[ is_last_put l key value ]] *
                        [[ (rep l kv_p * F)%pred (list2mem mbase) ]]

  CRASH                 MEMLOG.would_recover_old xp mbase \/
                        (exists m', MEMLOG.might_recover_cur xp mbase m' *
                        [[ (rep l kv_p * F)%pred (list2mem m') ]])
  >} get kv_p key xp cs.
Proof.
  unfold get. unfold rep.
Admitted.

Definition put T (kv_p : kv_pointer) (key : addr) (value : valu) xp cs rx : prog T :=
  mscs <- MEMLOG.begin xp cs;
  If (weq kv_p maxlen) {
    let2 (mscs, ok) <- MEMLOG.commit xp mscs;
    rx (mscs, false)
  } else {
    mscs <- MEMLOG.write xp kv_p (addr2valu key) mscs;
    mscs <- MEMLOG.write xp (kv_p ^+ $1) value mscs;
    let2 (mscs, ok) <- MEMLOG.commit xp mscs;
    If (bool_dec ok true) {
      rx (mscs, ok)
    } else {
      rx (mscs, false)
    }
  }.

Theorem put_ok: forall kv_p key value xp cs,
  {< mbase F l old_value,
  PRE               MEMLOG.rep xp (NoTransaction mbase) (ms_empty, cs) *
                    [[ is_last_put l key old_value ]] *
                    [[ (rep l kv_p * F)%pred (list2mem mbase) ]]

  (* Q: Does separation logic account for all the is_last_put and rep stuff, or is that necessary here? *)
  POST:(mscs', ok)  ([[ ok = true /\ is_last_put ((key, value) :: l) key value ]] *
                     exists m', MEMLOG.rep xp (NoTransaction m') mscs' *
                     [[ (rep ((key, value) :: l) (kv_p ^+ $2) * F)%pred (list2mem m') ]]) \/
                    ([[ ok = false /\ is_last_put l key old_value ]] *
                     ((MEMLOG.rep xp (NoTransaction mbase) mscs' *
                       [[ (rep l kv_p * F)%pred (list2mem mbase) ]]) \/
                      (exists m', MEMLOG.rep xp (NoTransaction m') mscs' *
                       [[ (rep l kv_p * F)%pred (list2mem m') ]])
                     )
                    )

  CRASH             MEMLOG.would_recover_old xp mbase
                    \/
                    (exists m', MEMLOG.might_recover_cur xp mbase m' *
                     (* Q: Even in this case, rep might not hold for (key, value) :: l because
                           the disk might be full...How to state that here? *)
                     [[ (rep l kv_p * F)%pred (list2mem m') ]])
  >} put kv_p key value xp cs.
Proof.
Admitted.