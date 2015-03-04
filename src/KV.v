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

Import ListNotations.

Set Implicit Arguments.

Parameter maxlen : addr. (* Number of entries on disk *)

Definition kv_pointer := addr.
Definition empty_value : valu := $0.
Definition empty_valuset : valuset := ($0, @nil valu).
Definition entry := (valuset * valuset)%type.
Definition empty_entry : entry := (empty_valuset, empty_valuset).

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

(* representation on memory? *)
Definition rep l (kv_p : kv_pointer) xp st mscs := (exists diskl,
  array $0 (map fst diskl) $2 *
  array $1 (map snd diskl) $2 *
  (* 2*len(diskl)? *)
  [[ length diskl = wordToNat maxlen ]] *
  [[ list_prefix l diskl ]] *
  MEMLOG.rep xp st mscs)%pred.

Definition rep' l (kv_p : kv_pointer) := (exists (diskl : list entry),
  array $0 (map (fun e => fst (fst e)) diskl) $2 *
  array $1 (map (fun e => fst (snd e)) diskl) $2 *
  [[ length diskl = wordToNat maxlen ]] *
  [[ list_prefix l diskl ]])%pred.


(*
Definition rep l := (exists diskl,
   array $1  (kv_p : kv_pointer)(map (fun e => add
  (*(weq (natToWord addrlen (length l)) kv_p) **)
   $0 |-> addr2valu $ (length l) *r2valu (fst e)) diskl) $2 *
   array $2 (map snd diskl) $2 *
   [[ length diskl = wordToNat maxlen ]] *
   [[ list_prefix l diskl ]])%pred.
*)

Definition no_such_put (l : list entry) (k : valu) : Prop :=
  ~ exists v cs_k cs_v, In ((k, cs_k), (v, cs_v)) l.

Fixpoint is_last_put (l : list entry) (k : valu) (v : valu) :=
  match l with
  | nil => False
  | (k', v') :: tl =>
    (k = fst k' /\ v = fst v' /\ no_such_put l k) \/
    (is_last_put tl k v)
  end.

Definition get T (kv_p : kv_pointer) key rx : prog T :=
final_value <- For i < kv_p
    Loopvar current_value <- empty_value
    Continuation lrx
    Invariant
      any
    OnCrash
      any
    Begin
      disk_key <- Read i;
      if (weq disk_key key) then
        disk_value <- Read (i ^+ $1);
        lrx disk_value
      else
        lrx current_value
  Rof;
rx final_value.

Check rep nil.

Hint Rewrite map_length.

Theorem get_ok: forall kv_p k,
  {< l xp st mscs,
  PRE    rep l kv_p xp st mscs
  POST:r rep l kv_p xp st mscs * [[ is_last_put l k r ]]
  CRASH  rep l kv_p xp st mscs
  >} get kv_p k.
Pro kv_p xp st mscsof.
  unfold ge kv_p xp st mscs * [[ is_last_put l k r ]]t, rep.
  hoare kv_p xp st mscs.

  simpl_list.
  eapply lt_le_trans; [| apply list_prefix_length; eauto ].
  wordcmp.
  eapply le_trans; [ apply list_prefix_length; eauto |].
  wordcmp.

  simpl_list.
  eapply lt_le_trans; [| apply list_prefix_length; eauto ].
  wordcmp.
  eapply le_trans; [ apply list_prefix_length; eauto |].
  wordcmp.

  admit.
Qed.

Definition put T (kv_p : kv_pointer) (key value : valu) rx : prog T :=
  Write kv_p key;;
  Write (kv_p ^+ $1) value;;
  rx (kv_p ^+ $2).

Definition put T k v (rx : bool -> prog T) :=
  l <- Read $0;
  If (weq (valu2addr l) maxlen) {
    rx false
  } else {
    ArrayWrite $1 (valu2addr l) $2 (addr2valu k);;
    ArrayWrite $2 (valu2addr l) $2 v;;
    Write ($0) (l ^+ $1);;
    rx true
  }.

Theorem put_ok: forall k v,
  {< l,
  PRE    rep l
  POST:r [[ r = false ]] * rep l \/
         [[ r = true ]] * rep (l ++ [(k, v)])
  CRASH  rep l \/ rep (l ++ [(k, v)])
  >} put k v.
Proof.
  unfold put, rep.
  hoare.

  admit.
  admit.

  apply pimpl_or_r. right. cancel.
  instantiate (a := (upd l0 $ (length l) (k, v))).
  autorewrite_fast.
  rewrite addr2valu2addr. rewrite app_length. rewrite natToWord_plus. cancel.
  admit.

  autorewrite_fast; auto.
  admit.

  apply pimpl_or_r. left. cancel.
  instantiate (a := (upd l0 $ (length l) (k, v))).
  rewrite addr2valu2addr. autorewrite_fast. cancel.
  autorewrite_fast; auto.
  admit.

  admit.

  apply pimpl_or_r. left. cancel.
  instantiate (a := (upd l0 $ (length l) (k, v))).
  rewrite addr2valu2addr. autorewrite_fast. cancel.
  autorewrite_fast; auto.
  admit.

  admit.
Qed.
