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
Require Import Permutation.
Require Import Array.


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
Axiom hEmpty : forall k, h empty_addr = h k -> False.

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

(*Inductive no_dup : (list entry) -> Prop :=
  | ND_nil : no_dup nil
  | ND_cons : forall l a,
    no_dup l ->
    ~In a l ->
    no_dup (a :: l).*)

Inductive no_dup : (list entry) -> Prop :=
  | ND_nil : no_dup nil
  | ND_cons : forall l key value,
    no_dup l ->
    ~In key (map fst l) ->
     key <> empty_addr ->
    no_dup ((key, value) :: l)
  | ND_empty : forall l,
    no_dup l ->
    no_dup (empty_entry :: l).

Lemma no_dup_updN :
  forall diskl n default key value,
    no_dup diskl ->
    fst (selN diskl n default) = key ->
    selN diskl n default <> empty_entry ->
    no_dup (updN diskl n (key, value)).
Proof.
  induction diskl; intros.
  auto.
  destruct n; simpl in *; subst; inversion H.
  constructor; auto.
  simpl.
  symmetry in H0. apply H1 in H0. inversion H0.
  constructor; auto.
  eapply IHdiskl; eauto.
  rewrite map_updN. simpl.
  rewrite <- map_updN. rewrite updN_selN_eq.
  auto.
  apply ND_empty.
  eapply IHdiskl; auto.
Qed.

Lemma no_dup_upd:
  forall diskl i default key value,
    no_dup diskl ->
    fst (sel diskl i default) = key ->
    sel diskl i default <> empty_entry ->
    no_dup (upd diskl i (key, value)).
Proof.
  intros. unfold sel, upd in *. eapply no_dup_updN; eauto.
Qed.

Lemma no_dup_selN :
  forall diskl i j default,
    no_dup diskl ->
    i < length diskl ->
    j < length diskl ->
    selN diskl i default = selN diskl j default ->
    selN diskl i default <> empty_entry ->
    i = j.
Proof.
  induction diskl; intros.
  inversion H0.
  destruct i; destruct j; simpl in *; inversion H; auto.
  - apply lt_S_n in H1.
    eapply in_selN in H1.
    assert (Ha: key = fst (selN diskl j default)).
      rewrite <- H2. rewrite <- H4. auto.
    rewrite Ha in H7.
    eapply in_map in H1.
    apply H7 in H1. inversion H1.
  - intuition. symmetry in H4. apply H3 in H4. inversion H4.
  - apply lt_S_n in H0.
    eapply in_selN in H0.
    assert (Ha: key = fst (selN diskl i default)).
      rewrite H2. rewrite <- H4. auto.
    rewrite Ha in H7.
    eapply in_map in H0.
    apply H7 in H0. inversion H0.
  - intuition. subst. symmetry in H4. apply H3 in H4. inversion H4.
  - replace i with j; auto.
    eapply IHdiskl; eauto; try omega. rewrite <- H2. auto.
  - replace i with j; auto.
    eapply IHdiskl; eauto; try omega. rewrite <- H2. auto.
Qed.

Lemma no_dup_cons : forall diskl a,
  no_dup (a :: diskl) ->
  no_dup diskl.
Proof.
  induction diskl; simpl; intros; inversion H.
  constructor. constructor.
  destruct (beq_entry a a0) eqn:Heq.
  - apply beq_entry_true in Heq.
    subst.
    auto.
  - apply beq_entry_false in Heq.
    inversion H2.
    constructor.
    eapply IHdiskl. eauto. auto. auto.
    apply ND_empty; auto.
  - auto.
Qed.

Definition hash_rep' l diskl := exists l',
  hash_rep l diskl /\
  filter_empty diskl = l' /\
  Permutation l' l /\
  no_dup diskl.

Definition rep l := (exists diskl,
  [[ hash_rep' l diskl ]] *
  array kBase (map (fun e => addr2valu (fst e)) diskl) $2 *
  array vBase (map snd diskl) $2 *
  [[ length diskl = maxlen ]]
  )%pred.


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


Fixpoint insert_l (l : list entry) (key : addr) (value : valu) : list entry :=
  match l with
  | nil => (key, value) :: nil
  | (k, v) :: l' => if (weqb k key)
                        then (k, value) :: insert_l l' key value
                        else (k, v) :: insert_l l' key value
  end.

Definition insert_diskl
  (diskl : list entry) (key : addr) (value : valu) : list entry :=
  upd diskl (h key) (key, value).

Lemma insert_diskl_length : forall diskl key value,
  length (insert_diskl diskl key value) = length diskl.
Proof.
  intros.
  unfold insert_diskl. rewrite length_upd. reflexivity.
Qed.


Lemma insert_diskl_filter_empty : forall l diskl key value,
  Permutation l (filter_empty diskl) ->
  Permutation (insert_l l key value) (filter_empty (insert_diskl diskl key value)).
Proof.
Admitted.

Ltac solve_key_bound H :=
  try rewrite map_length;
  try rewrite insert_diskl_length;
  try (rewrite H; apply hGood); auto.

Ltac solve_diskl_equal :=
  unfold insert_diskl;
  try rewrite map_upd;
  try rewrite skipn_upd;
  try rewrite firstn_upd; auto.


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
Lemma hash_rep_index :
  forall l key value diskl,
    hash_rep l diskl ->
    In (key, value) l ->
    (key, value) = sel diskl (h key) empty_entry.
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
  intuition.
  simpl in H0.
  apply beq_entry_false in aEq.
  intuition.
Qed.

Lemma in_filter_empty_N:
  forall diskl hkn,
    empty_entry <> selN diskl hkn empty_entry ->
    In (selN diskl hkn empty_entry) (filter_empty diskl).
Proof.
  induction diskl; simpl; intros.
  - auto.
  - destruct hkn.
    + destruct (beq_entry a empty_entry) eqn:H'.
      apply beq_entry_true in H'.
      intuition.
      symmetry in H'.
      apply H in H'.
      inversion H'.
      simpl. intuition.
    + destruct (negb (beq_entry a empty_entry)).
      simpl.
      right.
      auto.
      auto.
Qed.

Lemma in_filter_empty:
  forall diskl hk,
    empty_entry <> sel diskl hk empty_entry ->
    In (sel diskl hk empty_entry) (filter_empty diskl).
Proof.
  unfold sel.
  intros.
  apply in_filter_empty_N.
  auto.
Qed.

Lemma hash_rep'_well_formed_N :
  forall diskl l hkn k v,
    hash_rep' l diskl ->
    selN diskl hkn empty_entry = (k, v) ->
    (k, v) <> empty_entry ->
    length diskl = maxlen ->
    hkn < length diskl ->
    hkn = # (h k).
Proof.
  unfold hash_rep'.
  intros.
  destruct H. intuition.
  assert (In (selN diskl hkn empty_entry) l).
    eapply Permutation_in. eauto.
    rewrite <- H.
    apply in_filter_empty_N.
    congruence.

  clear H H5.

  induction l.
  - inversion H6.
  - inversion H4.
    inversion H6.
    + subst.
      eapply no_dup_selN in H.
      rewrite H0 in H. auto.
      inversion H7.
      constructor.
      constructor; auto.
      apply ND_empty. auto.
      solve_key_bound H2. auto.
      assert (Hd: selN diskl hkn empty_entry <> empty_entry).
        intuition. apply H1. rewrite <- H0. auto.
      unfold sel in H. rewrite H. auto.
    + apply IHl; auto.
Qed.

Lemma hash_rep'_well_formed :
  forall diskl l hk k v,
    hash_rep' l diskl ->
    sel diskl hk empty_entry = (k, v) ->
    (k, v) <> empty_entry ->
    length diskl = maxlen ->
    # (hk) < length diskl ->
    hk = h k.
Proof.
  intros.
  rewrite <- natToWord_wordToNat.
  erewrite <- hash_rep'_well_formed_N; eauto.
  symmetry. apply natToWord_wordToNat.
Qed.


Lemma hash_rep_empty_index :
  forall l key diskl,
    hash_rep' l diskl ->
    (forall key', h key = h key' -> forall v, ~In (key', v) l) ->
    length diskl = maxlen ->
    (*(~exists v, In (key, v) l) ->*)
    empty_entry = sel diskl (h key) empty_entry.
Proof.
  intros.
  inversion H.
  intuition.

  remember (sel diskl (h key) empty_entry) as foo.

  destruct (beq_entry empty_entry foo) eqn:Hempty.
  - apply beq_entry_true in Hempty.
    auto.
  - apply beq_entry_false in Hempty as HinL.
    rewrite Heqfoo in HinL.
    apply in_filter_empty in HinL.
    assert (In foo l).
      eapply Permutation_in. eauto. rewrite <- H2. rewrite Heqfoo. auto.
    destruct foo as [k v].
    exfalso.
    eapply H0.
      + apply beq_entry_false in Hempty.
        eapply hash_rep'_well_formed; eauto.
        solve_key_bound H1.
      + eauto.
Qed.

Lemma hash_rep_empty_index' :
  forall l key diskl,
    hash_rep' l diskl ->
    length diskl = maxlen ->
    (*(~exists v, In (key, v) l) ->*)
    empty_entry = sel diskl (h key) empty_entry ->
    (forall key', h key = h key' -> forall v, ~In (key', v) l).
Proof.
  intros.
  intuition.
  unfold hash_rep' in H. inversion H. intuition.
  eapply hash_rep_index in H5.
  assert (Hempty: (key', v) <> empty_entry).
    apply Permutation_in with (l':=x) in H3.
    subst. unfold filter_empty in H3.
    apply filter_In in H3.
    inversion H3.
    apply negb_true_iff in H7.
    apply beq_entry_false in H7.
    auto.
  apply Permutation_sym. auto.
  apply Hempty. rewrite H1. rewrite H2. rewrite <- H5. auto.
  auto.
Qed.

Lemma hash_rep_empty_index'' :
  forall l key diskl,
    hash_rep' l diskl ->
    length diskl = maxlen ->
    (*(~exists v, In (key, v) l) ->*)
    empty_entry = sel diskl (h key) empty_entry ->
    key <> empty_addr ->
    (forall key', key' <> empty_addr -> h key = h key' -> ~In key' (map fst diskl)).
Proof.
  intros. inversion H.
  assert (Hl': ~In key' (map fst l)).
    intuition.
    apply in_map_iff in H6.
    destruct H6. inversion H6.
    eapply hash_rep_index with (value:=snd x0) in H7.
    rewrite <- H4 in H7.
    rewrite <- H1 in H7.
    inversion H7. contradict H3. auto.
    rewrite <- H9. rewrite <- surjective_pairing. auto.
  intuition.
  eapply Hl'.
  eapply in_map_iff in H6.
  destruct H6. inversion H6.
  assert (Hfilter: In x0 diskl /\ (fun e => negb (beq_entry e empty_entry)) x0 = true).
    split; auto.
    apply negb_true_iff.
    apply beq_entry_false_kv. left.
    destruct x0. subst. auto.
  eapply filter_In in Hfilter.
  assert (Hfilter': In x0 (filter_empty diskl)). auto.
  rewrite H5 in Hfilter'.
  eapply Permutation_in in Hfilter'; eauto.
  rewrite surjective_pairing with (p:=x0) in Hfilter'.
  rewrite H9 in Hfilter'.
  eapply hash_rep_empty_index' in H as Hl; eauto. instantiate (v:=snd x0).
  apply Hl in Hfilter'. inversion Hfilter'.
Qed.

Lemma values_firstn_equal : forall l key value,
  array vBase (firstn # (h key) (map snd l)) $ (2) =
  array vBase (firstn # (h key) (map snd (insert_diskl l key value)))
  $ (2).
Proof.
  intros. solve_diskl_equal.
Qed.

Lemma values_skipn_equal : forall l key value,
array (vBase ^+ (h key ^+ $ (1)) ^* $ (2))
  match map snd l with
  | [] => []
  | _ :: l0 => skipn # (h key) l0
  end $ (2) =
array (vBase ^+ (h key ^+ $ (1)) ^* $ (2))
  match map snd (insert_diskl l key value) with
  | [] => []
  | _ :: l0 => skipn # (h key) l0
  end $ (2).
Proof.
  intros. solve_diskl_equal.
Qed.

Lemma hkey_equal : forall l key value,
  length l = maxlen ->
  sel (insert_diskl l key value) (h key) (empty_entry) = (key, value).
Proof.
  intros. solve_diskl_equal.
  eapply sel_upd_eq. solve_key_bound H.
Qed.

Lemma values_hkey_equal : forall l key value,
  length l = maxlen ->
  value = sel (map snd (insert_diskl l key value)) (h key) (empty_value).
Proof.
  intros.
  erewrite sel_map.
  rewrite hkey_equal; auto.
  solve_key_bound H.
Qed.

Lemma keys_firstn_equal : forall l key value,
  array kBase (firstn # (h key) (map (fun e : addr * valu => addr2valu (fst e)) l)) $ (2) =
  array kBase
    (firstn # (h key) (map (fun e : addr * valu => addr2valu (fst e)) (insert_diskl l key value)))
    $ (2).
Proof.
  intros. solve_diskl_equal.
Qed.

Lemma keys_skipn_equal : forall l key value,
  array (kBase ^+ (h key ^+ $ (1)) ^* $ (2))
    match map (fun e : addr * valu => addr2valu (fst e)) l with
    | [] => []
    | _ :: l0 => skipn # (h key) l0
    end $ (2) =
  array (kBase ^+ (h key ^+ $ (1)) ^* $ (2))
    match map (fun e : addr * valu => addr2valu (fst e)) (insert_diskl l key value) with
    | [] => []
    | _ :: l0 => skipn # (h key) l0
    end $ (2).
Proof.
  intros. solve_diskl_equal.
Qed.

Lemma keys_hkey_equal : forall l key value,
  length l = maxlen ->
  addr2valu key = sel
    (map (fun e : addr * valu => addr2valu (fst e))
    (insert_diskl l key value)) (h key) (empty_value).
Proof.
  intros.
  erewrite sel_map.
  rewrite hkey_equal; auto.
  solve_key_bound H.
Qed.


Lemma insert_hash_rep : forall l diskl key value,
  length diskl = maxlen ->
  hash_rep l diskl ->
  fst (sel diskl (h key) empty_entry) = key ->
  hash_rep (insert_l l key value) (insert_diskl diskl key value).
Proof.
  unfold insert_diskl. induction l; intros; simpl.
  split; auto.
  apply sel_upd_eq. solve_key_bound H.

  destruct a as [k v].
  destruct (weqb k key) eqn:kEq; simpl; split.
  - rewrite weqb_true_iff in kEq.
    rewrite kEq.
    rewrite sel_upd_eq. auto. solve_key_bound H.
  - simpl in H0. destruct H0.
    apply IHl; auto.
  - rewrite weqb_false_iff in kEq.
    rewrite sel_upd_ne. symmetry.
    eapply hash_rep_index.
    + apply H0.
    + simpl. auto.
    + unfold not; intros. apply kEq.
      rewrite <- H1. rewrite H2.
      simpl in H0. destruct H0. rewrite H0. auto.
  - simpl in H0. destruct H0.
    apply IHl; auto.
Qed.


Lemma insert_hash_rep' : forall l diskl key value,
  length diskl = maxlen ->
  hash_rep' l diskl ->
  fst (sel diskl (h key) empty_entry) = key ->
  sel diskl (h key) empty_entry <> empty_entry ->
  hash_rep' (insert_l l key value) (insert_diskl diskl key value).
Proof.
  unfold hash_rep'.
  intros. inversion H0. intuition.
  eexists.
  intuition.
  - apply insert_hash_rep; auto.
  - apply Permutation_sym.
    eapply insert_diskl_filter_empty.
    apply Permutation_sym. congruence.
  - unfold insert_diskl.
    eapply no_dup_upd; eauto.
Qed.


Lemma no_dup_empty_updN : forall diskl key value n,
  ~ In key (map fst diskl) ->
  no_dup diskl ->
  key <> empty_addr ->
  no_dup (updN diskl n (key, value)).
Proof.
  induction diskl; intros.
  constructor.
  inversion H0.
  - destruct n.
    + simpl. constructor; auto. intuition.
      apply H. simpl. right. auto.
    + simpl. constructor.
      * apply IHdiskl; auto.
        intuition.
        apply H. simpl. right. auto.
      * intuition.
        destruct (weqb key key0) eqn:Hkeykey0.
        apply weqb_true_iff in Hkeykey0. subst.
        apply H. simpl. auto.
        apply H5.
        apply weqb_false_iff in Hkeykey0.
        contradict H5.
        rewrite map_updN in H7. apply in_updN in H7.
        destruct H7. auto.
        simpl in H5. congruence.
      * auto.
  - destruct n.
    + simpl. constructor; auto. intuition.
      apply H. simpl. right. auto.
    + simpl. apply ND_empty.
      apply IHdiskl; auto.
      intuition.
      apply H. simpl. right. auto.
Qed.

Lemma insert_empty_no_dup : forall l diskl key value,
  length diskl = maxlen ->
  hash_rep' l diskl ->
  sel diskl (h key) empty_entry = empty_entry ->
  key <> empty_addr ->
  no_dup (insert_diskl diskl key value).
Proof.
  intros l.
  induction diskl; intros; inversion H0; intuition.
  unfold insert_diskl, upd.
  destruct # (h key) eqn:Hhkey.
  - simpl.
    inversion H7; try (
      inversion H1;
      unfold sel in H1; rewrite Hhkey in H1; simpl in H1;
      subst; intuition;
      constructor; auto;
      eapply hash_rep_empty_index'' with (key:=key) in H0 as HIn; auto;
      intuition;
      apply HIn;
      unfold In; simpl; right; apply H1).
  - simpl. destruct a as [k v].
    inversion H7.
    destruct (weqb k key) eqn:HkeysEq.
    + rewrite weqb_true_iff in HkeysEq. subst.
      assert (Hcontra: (key, v) = sel ((key, v) :: diskl) (h key) empty_entry).
          eapply hash_rep_index; eauto.
        eapply Permutation_in in H5; eauto.
        unfold filter_empty.
        apply filter_In. split.
        simpl. auto.
        rewrite negb_true_iff.
        apply beq_entry_false_kv. left. auto.
      assert (HKey: (key, v) = empty_entry).
        rewrite <- H1. auto.
      inversion HKey. contradict H12. auto.
    + subst. constructor.
      eapply hash_rep_empty_index'' with (key:=key) in H0 as HIn; auto.
      assert (HNoDupUpd: no_dup (updN diskl n (key, value))).
        apply no_dup_empty_updN; auto.
        intuition. apply HIn.
        simpl. right. auto.
      apply HNoDupUpd.
      intuition. intuition. apply H11.
      rewrite map_updN in H3. apply in_updN in H3.
      inversion H3. auto.
      apply weqb_false_iff in HkeysEq.
      contradict HkeysEq. auto.
      auto.
    + apply ND_empty. apply no_dup_empty_updN; auto.
      eapply hash_rep_empty_index'' with (key:=key) in H0; eauto.
      intuition. apply H0.
      simpl. right. auto.
Qed.


Lemma insert_empty_hash_rep : forall l diskl key value,
  length diskl = maxlen ->
  hash_rep l diskl ->
  sel diskl (h key) empty_entry = empty_entry ->
  key <> empty_addr ->
  fst (selN l 0 empty_entry) <> key ->
  h (fst (selN l 0 empty_entry)) <> h key ->
  hash_rep (insert_l l key value) (insert_diskl diskl key value).
Proof.
  unfold insert_l, insert_diskl.
  induction l; intros; simpl; intuition.
  apply sel_upd_eq. solve_key_bound H.

  destruct a as [k v].
  destruct (weqb k key) eqn:HkEq; simpl.
  + apply weqb_true_iff in HkEq.
    contradict H3.
    auto.
  + apply weqb_false_iff in HkEq.
    destruct (weqb (h k) (h key)) eqn:HhkEq; simpl.
    - apply weqb_true_iff in HhkEq.
      contradict H4.
      auto.
    - apply weqb_false_iff in HhkEq.
      intuition.
      replace (k, v) with (sel diskl (h k) empty_entry).
      apply sel_upd_ne.
      auto.
      apply hash_rep_index with (key:=k) (value:=v) in H0.
      auto.
      simpl. auto.
      inversion H0.
      apply IHl; auto.
      * intros.
        apply hash_rep_index with (key:=key) (value:=snd (selN l 0 empty_entry)) in H6.
        rewrite H1 in H6.
        inversion H6.
        apply H2 in H9. inversion H9.
        rewrite <- H7.
        rewrite <- surjective_pairing.
        apply in_selN.
        destruct l.
          simpl in H7. symmetry in H7. apply H2 in H7. inversion H7.
          simpl. omega.
      * intros.
        apply hash_rep_index with (key:=fst (selN l 0 empty_entry)) (value:=snd (selN l 0 empty_entry)) in H6.
        rewrite H7 in H6.
        rewrite H1 in H6.
        inversion H6.
        rewrite H9 in H7. apply hEmpty in H7. inversion H7.
        rewrite <- surjective_pairing. apply in_selN.
        destruct l. simpl in H7. apply hEmpty in H7. inversion H7.
        simpl. omega.
Qed.

Lemma insert_empty_hash_rep' : forall l diskl key value,
  length diskl = maxlen ->
  hash_rep' l diskl ->
  sel diskl (h key) empty_entry = empty_entry ->
  key <> empty_addr ->
  hash_rep (insert_l l key value) (insert_diskl diskl key value).
Proof.
  (* Prove
      - ~In key l -> hash_rep (key, value) :: l diskl -> hash_rep (insert_l l (key, value)) diskl
      - hash_rep l diskl -> sel diskl (h key) empty_entry = empty_entry -> ~In key l
      - induction on l
        prove every other element of l hashes to a different index from (h key) 
        then insert_diskl updates some other index *)
  induction l; intros. (*simpl; intuition.*)
  unfold insert_l, insert_diskl.
  simpl. intuition. apply sel_upd_eq. solve_key_bound H.

  destruct a as [k v].
  destruct (weqb k key) eqn:HkEq.
  + unfold insert_l, insert_diskl.
    simpl. apply weqb_true_iff in HkEq.
    assert (Hcontra: ~In k (map fst diskl)).
      eapply hash_rep_empty_index''; eauto.
      rewrite HkEq. auto.
    contradict Hcontra.
    unfold hash_rep' in *.
    inversion H0. intuition.
    assert (HIn: In (k, v) x).
      eapply Permutation_in.
      apply Permutation_sym.
      eauto.
      simpl. auto.
    apply in_map_iff. exists (k, v). intuition.
    eapply filter_In.
    rewrite <- H3 in HIn. unfold filter_empty in HIn.
    eauto.
  + apply weqb_false_iff in HkEq.
    destruct (weqb (h k) (h key)) eqn:HhkEq.
    - unfold insert_l, insert_diskl. apply weqb_true_iff in HhkEq.
      unfold hash_rep' in *.
      inversion H0.
      inversion H3.
      apply hash_rep_index with (key:=k) (value:=v) in H4.
      rewrite HhkEq in H4.
      rewrite H1 in H4.
      inversion H5.
      inversion H7. clear H0 H3 H5 H7.
      assert (Hcontra: In empty_entry x).
        eapply Permutation_in.
        apply Permutation_sym. eauto.
        rewrite H4. simpl. auto.
      unfold filter_empty in *.
      rewrite <- H6 in Hcontra.
      apply filter_In in Hcontra.
      inversion Hcontra.
      apply negb_true_iff in H3.
      unfold beq_entry in H3.
      inversion H3.
      apply weqb_false_iff in H7.
      contradict H7. auto.
      simpl. auto.
    - apply weqb_false_iff in HhkEq.
      unfold hash_rep' in *.
      inversion H0.
      intuition.
      eapply insert_empty_hash_rep; auto.
Qed.


Lemma insert_empty_hash_rep'' : forall l diskl key value,
  length diskl = maxlen ->
  hash_rep' l diskl ->
  sel diskl (h key) empty_entry = empty_entry ->
  key <> empty_addr ->
  hash_rep' (insert_l l key value) (insert_diskl diskl key value).
Proof.
  unfold hash_rep'.
  intros.
  eexists.
  inversion H0.
  intuition.
  + apply insert_empty_hash_rep'; auto.
  + symmetry.
    apply insert_diskl_filter_empty.
    symmetry. rewrite H3. auto.
  + eapply insert_empty_no_dup; eauto.
Qed.

(* If the key is already in the store, ensure that it gets updated. *)
Theorem put_ok: forall key value xp mscs,
  {< mbase MF l,
  PRE                   MEMLOG.rep xp MF (NoTransaction mbase) mscs *
                        [[ (rep l)%pred (list2mem mbase) ]] *
                        [[ length l < maxlen ]] *
                        [[ key <> empty_addr ]]

  POST RET:^(mscs', ok)
                        ([[ ok = true ]] *
                         exists m', MEMLOG.rep xp MF (NoTransaction m') mscs' *
                         [[ (rep (insert_l l key value))%pred (list2mem m') ]]) \/
                        ([[ ok = false ]] *
                         MEMLOG.rep xp MF (NoTransaction mbase) mscs')

  CRASH
                        MEMLOG.would_recover_old xp MF mbase \/
                        MEMLOG.would_recover_either xp MF mbase mbase \/
                        (exists m', MEMLOG.would_recover_either xp MF mbase m' *
                         [[ (rep (insert_l l key value))%pred (list2mem m') ]])
  >} put key value xp mscs.
Proof.
  unfold put. unfold rep.
  step.
  step.
  rewrite isolate_fwd. cancel. unfold entry in *. solve_key_bound H8.
  step.
  step.
  rewrite isolate_fwd with (a:=vBase). cancel. unfold entry in *. solve_key_bound H8.
  step.
  step.
  apply pimpl_or_r. left. norm. cancel.
  intuition.
  exists (insert_diskl l key value).
  pred_apply. cancel.
  (* diskl array matches disk after insert *)
  (*erewrite keys_equal. cancel.*)
  rewrite <- isolate_bwd with (vs:=(map snd (insert_diskl l key value))).
  cancel.
  erewrite values_firstn_equal. erewrite values_skipn_equal. erewrite values_hkey_equal at 1.
  cancel.
  assert (Hkeys: array kBase (map (fun e : addr * valu => addr2valu (fst e)) (insert_diskl l key value)) $ (2) =
                 array kBase (map (fun e : addr * valu => addr2valu (fst e)) l) $ (2)).
    admit.
  rewrite Hkeys. cancel.

  auto.
  solve_key_bound H8.
  apply insert_hash_rep'; auto.
  erewrite sel_map in H10.
  apply addr2valu_inj in H10.
  eauto.
  admit. (* Why this bug? "solve_key_bound H7" should work *)
  intuition.
  rewrite sel_map with (default':=empty_entry) in H10.
  apply addr2valu_inj in H10.
  rewrite H in H10.
  rewrite <- H10 in H4. contradict H4. auto.
  solve_key_bound H8. solve_key_bound H8.

  admit.
  admit.

  step.
  step.
  rewrite isolate_fwd. cancel. unfold entry in *. solve_key_bound H8.
  step.
  rewrite isolate_fwd with (a:=vBase). cancel. unfold entry in *. solve_key_bound H8.
  step.
  step.
  apply pimpl_or_r. left. norm. cancel.
  intuition.
  exists (insert_diskl l key value).
  pred_apply. cancel.
  (* diskl array matches disk after insert *)
  rewrite <- isolate_bwd with (vs:=(map snd (insert_diskl l key value))).
  erewrite values_firstn_equal. erewrite values_skipn_equal. erewrite values_hkey_equal at 1.
  cancel.
  rewrite <- isolate_bwd with (vs:=(map (fun e : addr * valu => addr2valu (fst e)) (insert_diskl l key value))).
  erewrite keys_firstn_equal. erewrite keys_skipn_equal. erewrite keys_hkey_equal. cancel.

  auto.
  solve_key_bound H8.
  auto.
  solve_key_bound H8.
  apply insert_empty_hash_rep''; auto. admit.
  solve_key_bound H9; assumption.

  admit.
  admit.

  unfold MEMLOG.would_recover_old. cancel.
  step.
  step.
  unfold MEMLOG.log_intact. cancel.

  (* A bunch of MEMLOG things that I'm not sure about *)
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
  rewrite isolate_fwd. cancel. rewrite map_length. unfold entry in *. solve_key_bound H9.
  step.
  rewrite isolate_fwd with (a:=vBase). cancel. rewrite map_length. unfold entry in *. solve_key_bound H9.

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
  eapply hash_rep_index; eauto.
  unfold MEMLOG.would_recover_old. cancel.
  unfold MEMLOG.would_recover_old. cancel.
  unfold MEMLOG.would_recover_old. cancel.
  unfold MEMLOG.would_recover_old. cancel.
Qed.


Theorem collision_map_ok cmap : pred :=
  forall (k, _) in cmap, for each block from h(k) to cmap(k), exists k' such that the block = cmap(k').*)
