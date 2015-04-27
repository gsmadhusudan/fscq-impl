Require Import Array.
Require Import BasicProg.
Require Import Hoare.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import GenSep.
Require Import KV.
Require Import List.
Require Import MemLog.
Require Import Pred.
Require Import Prog.
Require Import SepAuto.
Require Import Word.
Require Import Omega.


Module Map := FMapAVL.Make(Addr_as_OT).
Module MapFacts := WFacts_fun Addr_as_OT Map.
Module MapProperties := WProperties_fun Addr_as_OT Map.

Definition kvstate := Map.t valu.
Definition kv_empty := Map.empty valu.

Import ListNotations.
Set Implicit Arguments.

Parameter h: addr -> addr.
Parameter maxlen : nat. (* Number of entries on disk *)
Axiom hGood : forall a, # (h a) < maxlen.

Definition kvBase : addr := $0.


(* Eventual representation should look more like a map
Definition hashmap_rep (diskl : mem) (kv : kvstate) :=
        forall k v, Map.MapsTo k v kv ->
        @ptsto addr (@weq addrlen) valu (h k) (addr2valu k) diskl *
        @ptsto addr (@weq addrlen) valu ((h k) ^+ $1) v diskl.

Lemma hash_rep_elm diskl :
  forall l k v,
    In (k, v) l ->
    @ptsto addr (@weq addrlen) valu (h k) (addr2valu k) diskl.
*)


Fixpoint hash_rep l diskl : Prop :=
  match l with
  | nil => True
  | elm :: l' => sel diskl (h (fst elm)) empty_entry = elm /\
                    hash_rep l' diskl
  end.

Definition filter_empty l : (list entry) := filter (fun e => negb (beq_entry e empty_entry)) l.

Definition rep l := (exists diskl,
  [[ hash_rep l diskl ]] *
  array kBase (map (fun e => addr2valu (fst e)) diskl) $2 *
  array vBase (map snd diskl) $2 *
  [[ length diskl = maxlen ]] *
  [[ filter_empty diskl = l ]])%pred.


(* Is it enough to just be In the list? *)
Inductive is_last_put : (list entry) -> addr -> valu -> Prop :=
  | KV_no_put : forall k l,
                is_last_put l k empty_value
  | KV_key : forall k v tl,
             is_last_put ((k, v) :: tl) k v.


Definition get T (key : addr) xp mscs rx : prog T :=
  mscs <- MEMLOG.begin xp mscs;
  let^ (mscs, memory_key) <- MEMLOG.read xp (kBase ^+ (h key) ^* $2) mscs;
  let^ (mscs, rvalue) <- MEMLOG.read xp (vBase ^+ (h key) ^* $2) mscs;
  let^ (mscs, ok) <- MEMLOG.commit xp mscs;
  If (weq memory_key (addr2valu key)) {
    rx ^(mscs, rvalue)
  } else {
    rx ^(mscs, empty_value)
  }.


Definition put T (key : addr) (value : valu) xp mscs rx : prog T :=
  mscs <- MEMLOG.begin xp mscs;
  let^ (mscs, memory_key) <- MEMLOG.read xp (kBase ^+ (h key) ^* $2) mscs;
  If (weq memory_key (addr2valu key)) {
    mscs <- MEMLOG.write xp (vBase ^+ (h key) ^* $2) value mscs;
    let^ (mscs, ok) <- MEMLOG.commit xp mscs;
    rx ^(mscs, ok)
  } else {
    If (weq memory_key empty_value) {
      mscs <- MEMLOG.write xp (kBase ^+ (h key) ^* $2) (addr2valu key) mscs;
      mscs <- MEMLOG.write xp (vBase ^+ (h key) ^* $2) value mscs;
      let^ (mscs, ok) <- MEMLOG.commit xp mscs;
      rx ^(mscs, ok)
    } else {
      let^ (mscs, ok) <- MEMLOG.commit xp mscs;
      rx ^(mscs, false)
    }
  }.


Ltac solve_key_bound H := try (rewrite H; apply hGood).

(* For any disk and key, if the key is on the disk, then the key and
    corresponding value are also in the current store (the non-empty entries
    on disk). *)
Lemma hash_rep_In : forall diskl key,
    length diskl = maxlen ->
    key <> empty_addr ->
    sel (map (fun e : addr * valu => addr2valu (fst e)) diskl) (h key) empty_value = addr2valu key ->
    In (key, sel (map snd diskl) (h key) empty_value) (filter_empty diskl).
Proof.
  intros.
  erewrite sel_map in H1; solve_key_bound H.
  apply addr2valu_inj in H1.
  rewrite <- H1 at 1.
  erewrite sel_map; solve_key_bound H.
  rewrite <- surjective_pairing.
  eapply filter_In.
  split.
  eapply in_sel; solve_key_bound H.
  apply negb_true_iff.
  unfold beq_entry.
  apply andb_false_iff; left.
  rewrite H1. simpl. apply weqb_false_iff. auto.
  (* Shelved goal? *)
Qed.

(* For any (key, value) in the store, the key is stored at index h(key) on
    disk. *)
Lemma hash_rep_key_index :
  forall l key value diskl,
    hash_rep l diskl ->
    In (key, value) l ->
    key = fst (sel diskl (h key) empty_entry).
Proof.
  intros l. induction l. intros. inversion H0.
  intros.
  destruct (beq_entry a (key, value)) eqn:aEq.

  apply beq_entry_true in aEq.
  rewrite aEq in H.
  simpl in H.
  destruct H.
  rewrite H. auto.

  eapply IHl; auto.
  simpl in H.
  (* How to get rid of let-binder in hypothesis? *)
  intuition.
  simpl in H0.
  apply beq_entry_false in aEq.
  intuition.
  eauto.
Qed.


(* If the key is already in the store, ensure that it gets updated. *)
Theorem put_ok1: forall key value xp mscs,
  {< mbase MF l i,
  PRE                   MEMLOG.rep xp MF (NoTransaction mbase) mscs *
                        [[ (rep l)%pred (list2mem mbase) ]] *
                        [[ key = selN (map fst l) i empty_addr ]]

  POST RET:^(mscs', ok)
                        ([[ ok = true ]] *
                         exists m', MEMLOG.rep xp MF (NoTransaction m') mscs' *
                         [[ (rep (updN l i (key, value)))%pred (list2mem m') ]]) \/
                        ([[ ok = false ]] *
                         MEMLOG.rep xp MF (NoTransaction mbase) mscs')

  CRASH
                        MEMLOG.would_recover_old xp MF mbase
                        \/
                        (exists m', MEMLOG.would_recover_either xp MF mbase m' *
                         [[ (rep (updN l i (key, value)))%pred (list2mem m') ]])
  >} put key value xp mscs.
Proof.
Admitted.

(* If the key is not already in the store, ensure that it gets inserted. *)
Theorem put_ok2: forall key value xp mscs,
  {< mbase MF l,
  PRE                   MEMLOG.rep xp MF (NoTransaction mbase) mscs *
                        [[ (rep l)%pred (list2mem mbase) ]] *
                        [[ forall i, i < length l -> selN (map fst l) i empty_addr <> key ]]

  POST RET:^(mscs', ok)
                        ([[ ok = true ]] *
                         exists m', MEMLOG.rep xp MF (NoTransaction m') mscs' *
                         [[ exists i, (rep (insN l i (key, value)))%pred (list2mem m') ]]) \/
                        ([[ ok = false ]] *
                         MEMLOG.rep xp MF (NoTransaction mbase) mscs')

  CRASH
                        MEMLOG.would_recover_old xp MF mbase
                        \/
                        (exists m', MEMLOG.would_recover_either xp MF mbase m' *
                         [[ exists i, (rep (insN l i (key, value)))%pred (list2mem m') ]])
  >} put key value xp mscs.
Proof.
Admitted.

Theorem get_ok: forall key xp mscs,
  {< mbase MF l,
  PRE                   MEMLOG.rep xp MF (NoTransaction mbase) mscs *
                        [[ (rep l)%pred (list2mem mbase) ]] *
                        [[ key <> empty_addr ]]

  POST RET:^(mscs', rvalue)
                        MEMLOG.rep xp MF (NoTransaction mbase) mscs' *
                        [[ In (key, rvalue) l \/
                          (rvalue = empty_value /\ ~exists r', In (key, r') l) ]]

  CRASH                 MEMLOG.would_recover_old xp MF mbase \/
                        MEMLOG.would_recover_either xp MF mbase mbase
  >} get key xp mscs.
Proof.
  unfold get. unfold rep.
  step.
  step.
  (* h k = empty, key, or some other key k' where h k' = h k *)
  rewrite isolate_fwd. cancel. rewrite map_length. unfold entry in *. rewrite H8. apply hGood.
  step.
  rewrite isolate_fwd with (a:=vBase). cancel. rewrite map_length. unfold entry in *. rewrite H8. apply hGood.

  step.
  step.
  step.

  left.
  apply hash_rep_In; eauto.

  step.
  admit.
  admit.
  step.
  right.
  intuition. apply H9. destruct H0.
  rewrite sel_map with (default':=empty_entry); solve_key_bound H8.
  replace (fst (l $[ h key])) with key; auto.
  eapply hash_rep_key_index; eauto.
  unfold MEMLOG.would_recover_old. cancel.
  unfold MEMLOG.would_recover_old. cancel.
  unfold MEMLOG.would_recover_old. cancel.
  unfold MEMLOG.would_recover_old. cancel.
Qed.


Theorem collision_map_ok cmap : pred :=
  forall (k, _) in cmap, for each block from h(k) to cmap(k), exists k' such that the block = cmap(k').*)
