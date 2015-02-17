Require Import Arith.
Require Import Pred.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Array.
Require Import List.
Require Import Bool.
Require Import Nomega.
Require Import Idempotent.
Require Import Psatz.
Require Import AddrMap.
Require Import Rec.
Require Import NArith.
Require Import MemLog.
Require Import RecArray.
Require Import ListPred.
Require Import GenSep.
Require Import WordAuto.


Set Implicit Arguments.


(* Block allocator *)

Record xparams := {
  BmapStart : addr;
  BmapNBlocks : addr
}.

Module BALLOC.

  Definition itemtype := Rec.WordF 1.
  Definition items_per_valu : addr := natToWord addrlen valulen.

  Theorem blocksz : valulen = Rec.len (RecArray.blocktype itemtype items_per_valu).
  Proof.
    unfold blocktype, items_per_valu.
    rewrite wordToNat_natToWord_idempotent.
    simpl. ring.
    rewrite valulen_is. compute. auto.
  Qed.

  Definition rep_block := RecArray.rep_block blocksz.
  Definition valu_to_block := RecArray.valu_to_block itemtype items_per_valu blocksz.
  Definition rep_valu_id := RecArray.rep_valu_id blocksz.


  Inductive alloc_state :=
  | Avail
  | InUse.

  Definition alloc_state_dec : forall (a b : alloc_state), {a = b} + {a <> b}.
    destruct a; destruct b; try (left; constructor); right; discriminate.
  Defined.

  Definition alloc_state_to_bit a : word 1 :=
    match a with
    | Avail => $0
    | InUse => $1
    end.

  Definition bit_to_alloc_state (b : word 1) : alloc_state :=
    if weq b $0 then Avail else InUse.

  Lemma bit_alloc_state_id : forall a, bit_to_alloc_state (alloc_state_to_bit a) = a.
  Proof.
    destruct a; auto.
  Qed.
  Hint Rewrite bit_alloc_state_id.

  Definition valid_block xp bn := (bn < BmapNBlocks xp ^* $ valulen)%word.

  Definition bmap_bits xp (bmap : addr -> alloc_state) :=
     map (fun i => alloc_state_to_bit (bmap $ (i)))
          (seq 0 (wordToNat (BmapNBlocks xp) * valulen)).

  Definition xp_to_raxp xp :=
    RecArray.Build_xparams (BmapStart xp) (BmapNBlocks xp).

  Definition rep' xp (bmap : addr -> alloc_state) :=
    ([[ goodSize addrlen (wordToNat (BmapNBlocks xp) * valulen) ]] *
     RecArray.array_item itemtype items_per_valu blocksz (xp_to_raxp xp)
       (bmap_bits xp bmap))%pred.

  Definition free' T lxp xp bn ms rx : prog T :=
    ms' <- RecArray.put itemtype items_per_valu blocksz
      lxp (xp_to_raxp xp) bn (alloc_state_to_bit Avail) ms;
    rx ms'.

  Lemma selN_seq : forall a b c, c < b -> selN (seq a b) c = a + c.
  Proof.
    intros. rewrite nth_selN_eq with (z:=0). apply seq_nth; assumption.
    rewrite seq_length; auto.
  Qed.

  (* The third hypothesis isn't necessary but makes things simpler *)
  Lemma upd_bmap_bits : forall xp a bn b state,
    b = alloc_state_to_bit state ->
    goodSize addrlen (wordToNat (BmapNBlocks xp) * valulen) ->
    wordToNat bn < wordToNat (BmapNBlocks xp) * valulen ->
    upd (bmap_bits xp a) bn b = bmap_bits xp (fupd a bn state).
  Proof.
    intros. rewrite H. unfold bmap_bits, upd.
    rewrite updN_map_seq by assumption.
    eapply list_selN_ext.
    repeat rewrite map_length; trivial.
    intros pos Hl.
    rewrite map_length in Hl. rewrite seq_length in Hl.
    repeat erewrite selN_map by (rewrite seq_length; assumption).
    rewrite selN_seq by assumption. simpl.
    destruct (Nat.eq_dec pos (wordToNat bn)).
    rewrite e. rewrite natToWord_wordToNat. rewrite fupd_same; trivial.
    rewrite fupd_other. trivial.
    eapply f_neq.
    rewrite wordToNat_natToWord_idempotent'.
    auto.
    eapply Nat.lt_trans. apply Hl.
    assumption.
  Qed.

  Theorem free'_ok : forall lxp xp ms bn,
    {< Fm mbase m bmap,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ (Fm * rep' xp bmap)%pred (list2mem m) ]] *
             [[ (bn < BmapNBlocks xp ^* $ valulen)%word ]]
    POST:ms' exists m', MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
             [[ (Fm * rep' xp (fupd bmap bn Avail))%pred (list2mem m') ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} free' lxp xp bn ms.
  Proof.
    unfold free', rep', valid_block, MEMLOG.log_intact.
    hoare.
    erewrite upd_bmap_bits; try trivial.
    cancel.
    auto.
    word2nat_auto.
  Qed.

  Hint Extern 1 ({{_}} progseq (free' _ _ _ _) _) => apply free'_ok : prog.

  Definition alloc' T lxp xp ms rx : prog T :=
    For i < (BmapNBlocks xp ^* $ (valulen))
      Ghost mbase m
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        MEMLOG.rep lxp (ActiveTxn mbase m) ms
      OnCrash
        MEMLOG.log_intact lxp mbase
      Begin
        bit <- RecArray.get itemtype items_per_valu blocksz
          lxp (xp_to_raxp xp) i ms;
        let state := bit_to_alloc_state bit in
        If (alloc_state_dec state Avail) {
          ms' <- RecArray.put itemtype items_per_valu blocksz
            lxp (xp_to_raxp xp) i (alloc_state_to_bit InUse) ms;
          rx (Some i, ms')
        } else {
          lrx tt
        }
      Rof;;
    rx (None, ms).

  Hint Rewrite natToWord_wordToNat selN_map_seq.



  Theorem alloc'_ok: forall lxp xp ms,
    {< Fm mbase m bmap,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) ms * [[ (Fm * rep' xp bmap)%pred (list2mem m) ]]
    POST:p exists r ms', [[ p = (r, ms') ]] *
           ([[ r = None ]] * MEMLOG.rep lxp (ActiveTxn mbase m) ms' \/
            exists bn m', [[ r = Some bn ]] * [[ bmap bn = Avail ]] *
            MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
            [[ (Fm * rep' xp (fupd bmap bn InUse))%pred (list2mem m') ]] *
            [[ valid_block xp bn ]] )
    CRASH  MEMLOG.log_intact lxp mbase
    >} alloc' lxp xp ms.
  Proof.
    unfold alloc', rep'.
    hoare.
    apply pimpl_or_r; right.
    cancel.
    rewrite <- H9. unfold bmap_bits, sel.
    autorewrite with core; auto.
    word2nat_auto.
    erewrite upd_bmap_bits; trivial.
    cancel.
    auto.
    word2nat_auto.
  Qed.


  Hint Extern 1 ({{_}} progseq (alloc' _ _ _) _) => apply alloc'_ok : prog.

  (* Different names just so that we can state another theorem about them *)
  Definition alloc := alloc'.
  Definition free := free'.

  Definition rep xp (freeblocks : list addr) :=
    (exists bmap,
     rep' xp bmap *
     [[ forall a, In a freeblocks <-> bmap a = Avail ]] *
     listpred (fun a => a |->?) freeblocks)%pred.

  Theorem alloc_ok : forall lxp xp ms,
    {< Fm mbase m freeblocks,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) ms * [[ (Fm * rep xp freeblocks)%pred (list2mem m) ]]
    POST:p exists r ms', [[ p = (r, ms') ]] *
           ([[ r = None ]] * MEMLOG.rep lxp (ActiveTxn mbase m) ms' \/
            exists bn m' freeblocks', [[ r = Some bn ]] *
            MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
            [[ (Fm * bn |->? * rep xp freeblocks')%pred (list2mem m') ]] *
            [[ valid_block xp bn ]])
    CRASH  MEMLOG.log_intact lxp mbase
    >} alloc lxp xp ms.
  Proof.
    unfold alloc.
    intros.
    eapply pimpl_ok2. apply alloc'_ok.
    unfold rep, rep'.
    cancel.
    step.
    inversion H.
    cancel.
    apply pimpl_or_r. right.
    norm. (* We can't just [cancel] here because it introduces evars too early *)
    inversion H.
    cancel.
    intuition.
    inversion H; eauto.

    pred_apply.
    (* instantiate (a1 := remove (@weq addrlen) a0 l). *)
    erewrite listpred_remove with (dec := @weq addrlen). cancel.
    assert (a a3 = Avail) as Ha.
    apply H8.
    eapply remove_still_In; eauto.
    rewrite <- Ha.
    apply fupd_other.
    eapply remove_still_In_ne; eauto.
    assert (a1 <> a3).
    intro He. subst. rewrite fupd_same in *. discriminate. trivial.
    rewrite fupd_other in * by assumption.
    apply remove_other_In. assumption.
    rewrite H8; assumption.
    apply ptsto_conflict.
    rewrite H8; assumption.
    auto.
  Qed.



  Theorem free_ok : forall lxp xp bn ms,
    {< Fm mbase m freeblocks,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ (Fm * rep xp freeblocks * bn |->?)%pred (list2mem m) ]] *
             [[ (bn < BmapNBlocks xp ^* $ valulen)%word ]]
    POST:ms' exists m', MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
             [[ (Fm * rep xp (bn :: freeblocks))%pred (list2mem m') ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} free lxp xp bn ms.
  Proof.
    unfold free.
    intros.
    eapply pimpl_ok2. apply free'_ok.
    unfold rep, rep'.
    cancel.
    step.
    subst; apply fupd_same; trivial.
    rewrite H10 in H3.
    destruct (weq bn a0).
    subst; apply fupd_same; trivial.
    rewrite <- H3; apply fupd_other; assumption.
    destruct (weq bn a0).
    left. auto.
    right. rewrite fupd_other in H0 by assumption. apply H10; assumption.
  Qed.


  Hint Extern 0 (okToUnify (rep _ _) (rep _ _)) => constructor : okToUnify.

  Hint Extern 1 ({{_}} progseq (BALLOC.alloc _ _ _) _) => apply BALLOC.alloc_ok : prog.
  Hint Extern 1 ({{_}} progseq (BALLOC.free _ _ _ _) _) => apply BALLOC.free_ok : prog.


End BALLOC.
