Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
Require Import Hashmap.   (* must go before basicprog, because notation using hashmap *)
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DiskSet.
Require Import DirTree.
Require Import Pred.
Require Import String.
Require Import List.
Require Import BFile.
Require Import Inode.
Require Import Hoare.
Require Import GenSepN.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import AsyncDisk.
Require Import Array.
Require Import ListUtils.
Require Import DirTree.
Require Import DirSep.
Require Import Arith.
Require Import SepAuto.
Require Import Omega.
Require Import SuperBlock.
Require Import FSLayout.
Require Import AsyncFS.
Require Import Arith.
Require Import Errno.
Require Import List ListUtils.
Require Import GenSepAuto.



Import DIRTREE.
Import ListNotations.


Module TREESEQ.

  (* a layer over AFS that provides the same functions but with treeseq and dirsep specs *)

  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.

  Record treeseq_one := mk_tree {
    TStree  : DIRTREE.dirtree;
    TSilist : list INODE.inode;
    TSfree  : list addr * list addr
  }.

  Definition treeseq_one_safe t1 t2 mscs :=
    DIRTREE.dirtree_safe (TSilist t1) (BFILE.pick_balloc (TSfree t1) (MSAlloc mscs)) (TStree t1)
                         (TSilist t2) (BFILE.pick_balloc (TSfree t2) (MSAlloc mscs)) (TStree t2).

  Theorem treeseq_one_safe_refl : forall t mscs,
    treeseq_one_safe t t mscs.
  Proof.
    intros.
    apply DIRTREE.dirtree_safe_refl.
  Qed.

  Theorem treeseq_one_safe_trans : forall t1 t2 t3 mscs,
    treeseq_one_safe t1 t2 mscs ->
    treeseq_one_safe t2 t3 mscs ->
    treeseq_one_safe t1 t3 mscs.
  Proof.
    unfold treeseq_one_safe; intros.
    eapply DIRTREE.dirtree_safe_trans; eauto.
  Qed.

  Definition treeseq := nelist treeseq_one.

  Definition tree_rep F Ftop fsxp t :=
    (F * DIRTREE.rep fsxp Ftop (TStree t) (TSilist t) (TSfree t))%pred.

  Definition treeseq_in_ds F Ftop fsxp mscs (ts : treeseq) (ds : diskset) :=
    NEforall2
      (fun t d => tree_rep F Ftop fsxp t (list2nmem d) /\
                  treeseq_one_safe t (latest ts) mscs)
      ts ds.

  Definition treeseq_pred (p : treeseq_one -> Prop) (ts : treeseq) := NEforall p ts.

  Lemma treeseq_in_ds_eq: forall Fm Ftop fsxp mscs a ts ds,
    MSAlloc a = MSAlloc mscs ->
    treeseq_in_ds Fm Ftop fsxp mscs ts ds <->
    treeseq_in_ds Fm Ftop fsxp a ts ds.
  Proof.
    intros.
    unfold treeseq_in_ds in *.
    unfold treeseq_one_safe in *.
    rewrite H.
    split.
    intro.
    apply H0.
    intro.
    apply H0.
  Qed.

  Theorem treeseq_in_ds_pushd : forall F Ftop fsxp mscs ts ds t mscs' d,
    treeseq_in_ds F Ftop fsxp mscs ts ds ->
    tree_rep F Ftop fsxp t (list2nmem d) ->
    treeseq_one_safe (latest ts) t mscs ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs ->
    treeseq_in_ds F Ftop fsxp mscs' (pushd t ts) (pushd d ds).
  Proof.
    unfold treeseq_in_ds; simpl; intuition.
    apply NEforall2_pushd; intuition.
    rewrite latest_pushd.
    eapply NEforall2_impl; eauto.
    intuition.
    intuition.
    unfold treeseq_one_safe in *; intuition.
    rewrite H2 in *.
    eapply DIRTREE.dirtree_safe_trans; eauto.
    eapply DIRTREE.dirtree_safe_refl.
  Qed.

  Definition treeseq_one_upd (t: treeseq_one) pathname off v :=
    match find_subtree pathname (TStree t) with
    | None => t
    | Some (TreeFile inum f) => mk_tree (update_subtree pathname 
                                  (TreeFile inum (BFILE.mk_bfile (updN (BFILE.BFData f) off v) (BFILE.BFAttr f))) (TStree t))
                           (TSilist t) (TSfree t)
    | Some (TreeDir inum d) => t
    end.

  Definition tsupd (ts: treeseq) pathname off v :=
    d_map (fun t => treeseq_one_upd t pathname off v) ts.

  Lemma tsupd_latest: forall (ts: treeseq) pathname off v,
    (tsupd ts pathname off v) !! = treeseq_one_upd (ts !!) pathname off v.
  Proof.
    intros.
    unfold tsupd.
    rewrite d_map_latest; eauto.
  Qed.

  (**
   * [treeseq_safe] helps applications prove their own correctness properties, at
   * the cost of placing some restrictions on how the file system interface should
   * be used by the application.
   *
   * The two nice things about [treeseq_safe] is that, first, it names files by
   * pathnames (and, in particular, [treeseq_safe] for a file does not hold after
   * that file has been renamed).  Second, [treeseq_safe] avoids the shrink-and-regrow
   * problem that might arise if we were to [fdatasync] a file that has been shrunk
   * and re-grown.  Without [treeseq_safe], [fdatasync] on a shrunk-and-regrown file
   * would fail to sync the blocks that were shrunk and regrown, because the current
   * inode no longer points to those old blocks.  As a result, the contents of the
   * file on disk remains unsynced; this makes the spec of [fdatasync] complicated
   * in the general case when the on-disk inode block pointers differ from the in-memory
   * inode block pointers.
   *
   * [treeseq_safe] solves shrink-and-regrow by requiring that files monotonically
   * grow (or, otherwise, [treeseq_safe] does not hold).  When [treeseq_safe] stops
   * holding, the application can invoke [fsync] to flush metadata and, trivially,
   * re-establish [treeseq_safe] because there is only one tree in the sequence now.
   *
   * [treeseq_safe] is defined with respect to a specific pathname.  What it means for
   * [treeseq_safe] to hold for a pathname is that, in all previous trees, that pathname
   * must refer to a file that has all the same blocks as the current file (modulo being
   * shorter), or that pathname does not exist.  If, in some previous tree, the file does
   * not exist or is shorter, then the "leftover" blocks must be unused.
   *
   * The reason why [treeseq_safe] is defined per pathname is that we imagine that some
   * application may want to violate these rules for other pathnames.  For example, other
   * files might shrink and re-grow over time, without calling [tree_sync] before re-growing.
   * Or, the application might rename a file and continue writing to it using [update_fblock_d],
   * which (below) will be not supported unless the caller can prove [treeseq_safe] for the
   * current pathname of the file being modified.  The other behavior prohibited by [treeseq_safe]
   * is re-using a pathname without [tree_sync].
   *
   * The per-pathname aspect of [treeseq_safe] might also come in handy for concurrency,
   * where one thread does not know if other threads have already issued their [tree_sync]
   * or not for other pathnames.
   *)

  (**
   * [treeseq_safe] is defined as an if-and-only-if implication.  This captures two
   * important properties.  First, the file is monotonically growing: if the file existed
   * and some block belonged to it in the past, then the file must continue to exist and
   * the block must continue to belong to the file at the same offset.  The forward
   * implication captures this.  Second, we also need to know that all blocks used by
   * the current file were never used by other files.  The reverse implication captures
   * this part (the currently-used blocks were either free or used for the same file at
   * the same pathname).
   *)

 Definition treeseq_safe_fwd pathname (tnewest tolder : treeseq_one) :=
    forall inum off bn,
    (exists f, find_subtree pathname (TStree tolder) = Some (TreeFile inum f) /\
      BFILE.block_belong_to_file (TSilist tolder) bn inum off)
   ->
    (exists f', find_subtree pathname (TStree tnewest) = Some (TreeFile inum f') /\
     BFILE.block_belong_to_file (TSilist tnewest) bn inum off).

  Definition treeseq_safe_bwd pathname flag (tnewest tolder : treeseq_one) :=
    forall inum off bn,
    (exists f', find_subtree pathname (TStree tnewest) = Some (TreeFile inum f') /\
     BFILE.block_belong_to_file (TSilist tnewest) bn inum off) ->
    ((exists f, find_subtree pathname (TStree tolder) = Some (TreeFile inum f) /\
      BFILE.block_belong_to_file (TSilist tolder) bn inum off) \/
     BFILE.block_is_unused (BFILE.pick_balloc (TSfree tolder) flag) bn).

  Definition treeseq_safe pathname flag (tnewest tolder : treeseq_one) :=
    treeseq_safe_fwd pathname tnewest tolder /\
    treeseq_safe_bwd pathname flag tnewest tolder /\
    BFILE.ilist_safe (TSilist tolder)  (BFILE.pick_balloc (TSfree tolder)  flag)
                     (TSilist tnewest) (BFILE.pick_balloc (TSfree tnewest) flag).

  Theorem treeseq_safe_trans: forall pathname flag t0 t1 t2,
    treeseq_safe pathname flag t0 t1 ->
    treeseq_safe pathname flag t1 t2 ->
    treeseq_safe pathname flag t0 t2.
  Proof.
    unfold treeseq_safe; intuition.
    - unfold treeseq_safe_fwd in *; intuition.
    - unfold treeseq_safe_bwd in *; intuition.
      specialize (H0 _ _ _ H3).
      inversion H0; eauto.
      right.
      unfold BFILE.ilist_safe in H5; destruct H5.
      eapply In_incl.
      apply H6.
      eauto.
    - eapply BFILE.ilist_safe_trans; eauto.
  Qed.

  Lemma tree_file_flist: forall F Ftop flist tree pathname inum f,
    find_subtree pathname tree = Some (TreeFile inum f) ->
    (F * tree_pred Ftop tree)%pred (list2nmem flist) ->
    tree_names_distinct tree ->
    selN flist inum BFILE.bfile0 = f.
  Proof.
    intros.
    rewrite subtree_extract with (fnlist := pathname) (subtree := (TreeFile inum f)) in H0; eauto.
    unfold tree_pred in H0.
    destruct_lift H0.
    eapply list2nmem_sel in H0; eauto.
  Qed.


  Ltac distinct_names :=
    match goal with
      [ H: (_ * DIRTREE.rep _ _ ?tree _ _)%pred (list2nmem _) |- DIRTREE.tree_names_distinct ?tree ] => 
        eapply DIRTREE.rep_tree_names_distinct; eapply H
    end.

  Ltac distinct_inodes :=
    match goal with
      [ H: (_ * DIRTREE.rep _ _ ?tree _ _)%pred (list2nmem _) |- DIRTREE.tree_inodes_distinct ?tree ] => 
        eapply DIRTREE.rep_tree_inodes_distinct; eapply H
    end.

  Lemma tree_file_length_ok: forall F Ftop fsxp ilist frees d tree pathname off bn inum f,
      (F * rep Ftop fsxp tree ilist frees)%pred d ->
      find_subtree pathname tree = Some (TreeFile inum f) ->
      BFILE.block_belong_to_file ilist bn inum off ->
      off < Datatypes.length (BFILE.BFData f).
  Proof.
    intros.
    eapply DIRTREE.rep_tree_names_distinct in H as Hdistinct.
    apply BFILE.block_belong_to_file_inum_ok in H1 as H1'.

    unfold rep in H.
    unfold BFILE.rep in H.
    destruct_lift H.

    eapply sep_star_assoc_1 in H3.
    setoid_rewrite sep_star_comm in H3.
    eapply sep_star_assoc_2 in H3.
    eapply tree_file_flist with (pathname := pathname) in H3 as H3'; eauto.

    erewrite listmatch_extract with (i := inum) in H.
    unfold BFILE.file_match at 2 in H.
    rewrite listmatch_length_pimpl with (a := BFILE.BFData _) in H.
    destruct_lift H.
    rewrite map_length in *.
    rewrite H14; eauto.
    unfold BFILE.block_belong_to_file in H1.
    intuition.
    eassumption.

    rewrite listmatch_length_pimpl in H.
    destruct_lift H.
    rewrite H11. eauto.
  Qed.


  Lemma treeseq_in_ds_tree_pred_latest: forall Fm Ftop fsxp mscs ts ds,
   treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
   (Fm ✶ rep fsxp Ftop (TStree ts !!) (TSilist ts!!) (TSfree ts!!))%pred (list2nmem ds !!).
  Proof.
    intros.
    unfold treeseq_in_ds in H.
    intuition.
    unfold tree_rep in H.
    eapply NEforall2_d_in with (x := ts !!) in H as H'.
    intuition.
    eassumption.
    instantiate (1 := (Datatypes.length (snd ts))).
    rewrite latest_nthd; auto.
    eapply NEforall2_length in H as Hl.
    rewrite Hl.
    rewrite latest_nthd; auto.
  Qed.


  Lemma treeseq_safe_refl : forall pathname flag tree,
   treeseq_safe pathname flag tree tree.
  Proof.
    intros.
    unfold treeseq_safe, treeseq_safe_fwd, treeseq_safe_bwd.
    intuition.
    apply BFILE.ilist_safe_refl.
  Qed.

  Lemma treeseq_safe_pushd: forall ts pathname flag tree',
    treeseq_pred (treeseq_safe pathname flag tree') ts ->
    treeseq_pred (treeseq_safe pathname flag tree') (pushd tree' ts).
  Proof.
    intros.
    eapply NEforall_d_in'; intros.
    eapply d_in_pushd in H0.
    intuition.
    rewrite H1.
    eapply treeseq_safe_refl.
    eapply NEforall_d_in; eauto.
  Qed.


  Ltac distinct_names' :=
    repeat match goal with
      | [ H: treeseq_in_ds _ _ _ _ ?ts _ |- DIRTREE.tree_names_distinct (TStree ?ts !!) ] => 
        idtac "treeseq"; eapply treeseq_in_ds_tree_pred_latest in H as Hpred;
        eapply DIRTREE.rep_tree_names_distinct; eapply Hpred
    end.

  Theorem treeseq_file_getattr_ok : forall fsxp inum mscs,
  {< ds ts pathname Fm Ftop Ftree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ (Ftree * pathname |-> Some (inum, f))%pred  (dir2flatmem2 (TStree ts!!)) ]] 
  POST:hm' RET:^(mscs',r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
         [[ r = BFILE.BFAttr f /\ MSAlloc mscs' = MSAlloc mscs ]]
  CRASH:hm'
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
  >} AFS.file_get_attr fsxp inum mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.file_getattr_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H6 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
  Qed.

  Theorem treeseq_lookup_ok: forall fsxp dnum fnlist mscs,
    {< ds ts Fm Ftop,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ DIRTREE.dirtree_inum (TStree ts !!) = dnum ]] *
      [[ DIRTREE.dirtree_isdir (TStree ts !!) = true ]]
    POST:hm' RET:^(mscs', r)
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
      [[ (isError r /\ None = DIRTREE.find_name fnlist (TStree ts !!)) \/
         (exists v, r = OK v /\ Some v = DIRTREE.find_name fnlist (TStree ts !!))%type ]] *
      [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
     >} AFS.lookup fsxp dnum fnlist mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.lookup_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
  Qed.

  Theorem treeseq_read_fblock_ok : forall fsxp inum off mscs,
    {< ds ts Fm Ftop Ftree pathname f Fd vs,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ (Ftree * pathname |-> Some (inum, f))%pred  (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs', r)
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
           [[ r = fst vs /\ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} AFS.read_fblock fsxp inum off mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.read_fblock_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
    eassumption.
  Qed.

  (* XXX kill? *)
  Lemma dirtree_extract_file: forall Fm fsxp Ftree Ftop pathname d tree ilist frees inum f,
  (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)%pred (list2nmem d) ->
  (Ftree * pathname |-> Some(inum, f))%pred (dir2flatmem2 tree) ->
  exists Fi flist, (Fi * inum |-> f)%pred (list2nmem flist).
  Proof.
    intros.
    eapply rep_tree_names_distinct in H as Hdistinct.
    unfold rep in H.
    destruct_lift H.
    rewrite subtree_extract with (fnlist := pathname) (subtree := TreeFile inum f) in H2; eauto.
    eexists.
    eexists dummy.
    pred_apply.
    cancel.
    eapply dir2flatmem2_find_subtree_ptsto in H0; eauto.
  Qed.

  (* XXX kill? *)
  Lemma dirtree_block_belong_to_file_ok : forall Fm fsxp Ftop Ftree Fd pathname d tree ilist frees inum off f vs,
    (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)%pred (list2nmem d) ->
    (Ftree * pathname |-> Some(inum, f))%pred (dir2flatmem2 tree) ->
    (Fd * off |-> vs)%pred (list2nmem (BFILE.BFData f)) ->
    exists bn, BFILE.block_belong_to_file ilist bn inum off.
  Proof.
    intros.
    exists # (selN (INODE.IBlocks (selN ilist inum INODE.inode0)) off $0).
    eapply rep_tree_names_distinct in H as Hdistinct.
    unfold rep in H.
    destruct_lift H.
    eapply BFILE.block_belong_to_file_ok; eauto.
    instantiate (1 := (list2nmem d)).
    pred_apply.
    cancel.
    rewrite subtree_extract with (fnlist := pathname) (subtree := TreeFile inum f) in H3; eauto.
    pred_apply.
    cancel.
    eapply dir2flatmem2_find_subtree_ptsto in H0; eauto.
  Qed.

  Lemma treeseq_block_belong_to_file: forall F Ftop fsxp t d pathname inum f off, 
    tree_rep F Ftop fsxp t (list2nmem d) ->
    find_subtree pathname (TStree t) = Some (TreeFile inum f)  ->
    off < Datatypes.length (BFILE.BFData f) ->
    exists bn, BFILE.block_belong_to_file (TSilist t) bn inum off.
  Proof.
    unfold BFILE.block_belong_to_file.
    intros.
    eexists; intuition.
    unfold tree_rep, rep in H.
    eapply rep_tree_names_distinct in H as Hdistinct.
    destruct_lift H.

    rewrite subtree_extract in H3; eauto.
    simpl in H3.
    assert (inum < Datatypes.length dummy).
    eapply list2nmem_inbound. pred_apply; cancel.

    erewrite list2nmem_sel with (x := f) (i := inum) (l := dummy) in H1.
    2: pred_apply; cancel.

    clear H3.
    unfold BFILE.rep in H.
    rewrite listmatch_extract in H; eauto.

    unfold BFILE.file_match at 2 in H.
    erewrite listmatch_length_pimpl with (a := (BFILE.BFData dummy ⟦ inum ⟧)) in H.
    destruct_lift H.

    rewrite H14 in H1.
    rewrite map_length in H1.
    eauto.

  Grab Existential Variables.
    eauto.
  Qed.

  (* BFILE *)
  Fact block_belong_to_file_bn_eq: forall tree bn bn0 inum off,
    BFILE.block_belong_to_file tree bn inum off ->
    BFILE.block_belong_to_file tree bn0 inum off ->
    bn = bn0.
  Proof.
    intros;
    unfold BFILE.block_belong_to_file in *.
    intuition.
  Qed.

  (* BFILE XXX kill *)
  Lemma block_belong_to_file_setattr_fwd: forall Fi ilist ilist' attr bn inum off ino,
    (Fi * inum |-> ino)%pred (list2nmem ilist) ->
    (Fi * inum |-> INODE.mk_inode (INODE.IBlocks ino) attr)%pred (list2nmem ilist') ->
    BFILE.block_belong_to_file ilist bn inum off ->
    BFILE.block_belong_to_file ilist' bn inum off.
  Proof.
    intros.
    eapply list2nmem_sel in H.
    eapply list2nmem_sel in H0.
    unfold BFILE.block_belong_to_file in *.
    intuition.
    rewrite <- H0; simpl.
    rewrite H; eauto.
    rewrite <- H0; simpl.
    rewrite H; eauto.
  Qed.

  (* BFILE XXX kill *)
  Lemma block_belong_to_file_setattr_bwd: forall Fi ilist ilist' attr bn inum off ino,
    (Fi * inum |-> ino)%pred (list2nmem ilist) ->
    (Fi * inum |-> INODE.mk_inode (INODE.IBlocks ino) attr)%pred (list2nmem ilist') ->
    BFILE.block_belong_to_file ilist' bn inum off ->
    BFILE.block_belong_to_file ilist bn inum off.
  Proof.
    intros.
    eapply list2nmem_sel in H.
    eapply list2nmem_sel in H0.
    unfold BFILE.block_belong_to_file in *.
    intuition.
    rewrite <- H0 in H2.
    simpl in H2.
    rewrite H in H2; eauto.
    rewrite <- H0 in H3.
    simpl in H3.
    rewrite H in H3; eauto.
  Qed.

  Lemma treeseq_safe_pushd_update_subtree : forall Ftree ts pathname ilist' f f' inum  mscs pathname' free2,
    let tree' := {|
        TStree := update_subtree pathname
                    (TreeFile inum f') 
                    (TStree ts !!);
        TSilist := ilist';
        TSfree := free2 |} in
    tree_names_distinct (TStree ts !!) ->
    tree_inodes_distinct (TStree ts !!) ->
    Datatypes.length ilist' = Datatypes.length (TSilist ts!!) ->
    (Ftree * pathname |-> Some(inum, f))%pred (dir2flatmem2 (TStree ts !!)) ->
    BFILE.ilist_safe (TSilist ts!!) (BFILE.pick_balloc (TSfree ts!!) (MSAlloc mscs))
                     ilist' (BFILE.pick_balloc free2 (MSAlloc mscs)) ->
    BFILE.treeseq_ilist_safe inum (TSilist ts!!) ilist' ->
    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) ts !!) ts ->
    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (pushd tree' ts) !!) (pushd tree' ts).
  Proof.
    intros.
    subst tree'.
    eapply dir2flatmem2_find_subtree_ptsto in H as Hfind; eauto.
    eapply treeseq_safe_pushd; eauto.
    eapply NEforall_d_in'; intros.
    eapply NEforall_d_in in H5.
    2: instantiate (1 := x); eauto.
    destruct (list_eq_dec string_dec pathname pathname'); simpl.
    - rewrite e in *; simpl.
      unfold treeseq_safe in *.
      intuition; simpl.
      * unfold treeseq_safe_fwd in *.
        intros; simpl.
        specialize (H7 inum0 off bn).
        destruct H7.
        destruct H8.
        eexists x0.
        intuition.
        intuition.
        exists f'.
        erewrite find_update_subtree; eauto.
        rewrite Hfind in H10.
        inversion H10.
        unfold BFILE.treeseq_ilist_safe in *.
        intuition.
        specialize (H7 off bn).
        destruct H7.
        subst.
        eauto.
        subst.
        split; eauto.
      * unfold treeseq_safe_bwd in *; intros.
        destruct (BFILE.block_is_unused_dec (BFILE.pick_balloc (TSfree ts!!) (MSAlloc mscs)) bn).
        ++ deex.
           right.
           unfold BFILE.ilist_safe in H9; intuition.
           eapply In_incl.
           apply b.
           eauto.

        ++ 
        specialize (H5 inum off bn).
        destruct H5.
        ** eexists f.
        split; eauto.
        simpl in *.
        subst.
        erewrite find_update_subtree in H8 by eauto.
        deex.
        inversion H8.
        unfold BFILE.ilist_safe in H3.
        intuition.
        specialize (H13 inum off bn).
        subst.
        destruct H13; eauto.

        exfalso. eauto.

        ** 
        destruct H5.
        simpl in *.
        erewrite find_update_subtree in H8.
        intuition. deex.
        inversion H8; eauto.
        subst.
        left.
        eauto.
        eauto.
        **
        right; eauto.

     * eapply BFILE.ilist_safe_trans; eauto.

     - unfold treeseq_safe in *.
      intuition; simpl.
      (* we updated pathname, but pathname' is still safe, if it was safe. *)
      * unfold treeseq_safe_fwd in *; simpl.
        erewrite find_subtree_update_subtree_ne_path; eauto.
        intros.
        specialize (H7 inum0 off bn H8).
        repeat deex.
        eexists.
        intuition. eauto.
        destruct (addr_eq_dec inum inum0).
        ** subst.
          exfalso. apply n.
          eapply find_subtree_inode_pathname_unique; eauto.

        **
        unfold BFILE.treeseq_ilist_safe in H4; intuition.
        unfold BFILE.block_belong_to_file.
        rewrite <- H13.
        apply H12.
        intuition.
        eapply BFILE.block_belong_to_file_inum_ok; eauto.

      * unfold treeseq_safe_bwd in *; simpl; intros.
        deex; intuition.
        erewrite find_subtree_update_subtree_ne_path in *; eauto.

        destruct (addr_eq_dec inum inum0).
        ** subst.
          exfalso. apply n.
          eapply find_subtree_inode_pathname_unique; eauto.
        **

        eapply H5.
        eexists. intuition eauto.

        unfold BFILE.treeseq_ilist_safe in H4; intuition.
        unfold BFILE.block_belong_to_file.
        rewrite H12.
        apply H11.
        intuition.
        rewrite <- H1.
        eapply BFILE.block_belong_to_file_inum_ok; eauto.

      * eapply BFILE.ilist_safe_trans; eauto.
  Qed.

  Theorem treeseq_file_set_attr_ok : forall fsxp inum attr mscs,
  {< ds ts pathname Fm Ftop Ftree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
     [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
     [[ (Ftree * pathname |-> Some (inum, f))%pred (dir2flatmem2 (TStree ts!!)) ]] 
  POST:hm' RET:^(mscs', ok)
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     ([[ ok = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' \/
      [[ ok = true  ]] * exists d ds' ts' tree' ilist' f',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
        [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
        [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' (TSfree ts !!)) ]]] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') (TStree ts!!) ]] *
        [[ ts' = pushd (mk_tree tree' ilist' (TSfree ts !!)) ts ]] *
        [[ f' = BFILE.mk_bfile (BFILE.BFData f) attr ]] *
        [[ (Ftree * pathname |-> Some (inum, f'))%pred (dir2flatmem2 tree') ]])
  XCRASH:hm'
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
  >} AFS.file_set_attr fsxp inum attr mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.file_set_attr_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H6 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
    step.
    or_r.
    cancel.
    eapply treeseq_in_ds_pushd; eauto.
    unfold tree_rep.
    unfold treeseq_one_safe.
    simpl.
    rewrite H4 in H12.
    eassumption.
    rewrite H4 in *.
    eapply treeseq_in_ds_tree_pred_latest in H6 as Hpred.
    eapply treeseq_safe_pushd_update_subtree; eauto.
    distinct_names.
    distinct_inodes.
    rewrite DIRTREE.rep_length in Hpred; destruct_lift Hpred.
    rewrite DIRTREE.rep_length in H10; destruct_lift H10.
    congruence.

    unfold dirtree_safe in *.
    intuition.

    eapply dir2flatmem2_update_subtree.
    distinct_names'.
    eassumption.
  Qed.

  Theorem treeseq_file_grow_ok : forall fsxp inum newlen mscs,
  {< ds ts pathname Fm Ftop Ftree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
     [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
     [[ (Ftree * pathname |-> Some (inum, f))%pred  (dir2flatmem2 (TStree ts!!)) ]] *
     [[ newlen >= Datatypes.length (BFILE.BFData f) ]]
  POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
     ([[ isError ok ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' \/
      [[ ok = OK tt ]] * exists d ds' ts' ilist' frees' tree' f',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
        [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
        [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees')]]] *
        [[ f' = BFILE.mk_bfile (setlen (BFILE.BFData f) newlen ($0, nil)) (BFILE.BFAttr f) ]] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') (TStree ts !!) ]] *
        [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
        [[ (Ftree * pathname |-> Some (inum, f'))%pred (dir2flatmem2 tree') ]])
  XCRASH:hm'
    LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
  >} AFS.file_truncate fsxp inum newlen mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.file_truncate_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
    step.
    or_r.
    cancel.
    eapply treeseq_in_ds_pushd; eauto.
    unfold tree_rep.
    unfold treeseq_one_safe.
    simpl in *.
    rewrite H4 in H14.
    eassumption.
    eapply treeseq_safe_pushd_update_subtree; eauto.
    distinct_names'.
    eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred.
    distinct_inodes.
    eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred.
    rewrite DIRTREE.rep_length in Hpred; destruct_lift Hpred.
    rewrite DIRTREE.rep_length in H12; destruct_lift H12.
    congruence. 

    unfold dirtree_safe in *.
    intuition.
    rewrite H4 in H10; eauto.

    eapply dir2flatmem2_update_subtree; eauto.
    distinct_names'.
  Qed.

  Lemma block_is_unused_xor_belong_to_file : forall F Ftop fsxp t m flag bn inum off,
    tree_rep F Ftop fsxp t m ->
    BFILE.block_is_unused (BFILE.pick_balloc (TSfree t) flag) bn ->
    BFILE.block_belong_to_file (TSilist t) bn inum off ->
    False.
  Proof.
    unfold tree_rep; intros.
    destruct t; simpl in *.
    unfold rep in H; destruct_lift H.
    eapply BFILE.block_is_unused_xor_belong_to_file with (m := m); eauto.
    pred_apply.
    cancel.
  Qed.

  Lemma tree_rep_nth_upd: forall F Ftop fsxp mscs ts ds n pathname bn off v inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file (TSilist (ts !!)) bn inum off ->
    treeseq_in_ds F Ftop fsxp mscs ts ds ->
    tree_rep F Ftop fsxp (nthd n ts) (list2nmem (nthd n ds)) ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    tree_rep F Ftop fsxp (treeseq_one_upd (nthd n ts) pathname off v) (list2nmem (nthd n ds) ⟦ bn := v ⟧).
  Proof.
    intros.
    eapply NEforall_d_in in H3 as H3'; [ | apply nthd_in_ds with (n := n) ].
    unfold treeseq_safe in H3'.
    intuition.
    unfold treeseq_one_upd.
    unfold treeseq_safe_bwd in *.
    edestruct H6; eauto.
    - repeat deex.
      rewrite H8.
      unfold tree_rep; simpl.
      eapply dirtree_update_block with (bn := bn) (m := (nthd n ds)) (v := v) in H2 as H2'; eauto.
      pred_apply.
      erewrite dirtree_update_inode_update_subtree; eauto.
      eapply rep_tree_inodes_distinct; eauto.
      eapply rep_tree_names_distinct; eauto.
      eapply tree_file_length_ok.
      eapply H2.
      eauto.
      eauto.
    - eapply dirtree_update_free with (bn := bn) (v := v) in H2 as H2'; eauto.
      case_eq (find_subtree pathname (TStree (nthd n ts))); intros; [ destruct d | ]; eauto.
      rewrite updN_oob.
      erewrite update_subtree_same; eauto.
      eapply rep_tree_names_distinct; eauto.
      destruct b; eauto.

      destruct (lt_dec off (Datatypes.length (BFILE.BFData b))); try omega.
      exfalso.
      edestruct treeseq_block_belong_to_file; eauto.

      unfold treeseq_safe_fwd in H4.
      edestruct H4; eauto; intuition.
      rewrite H11 in H; inversion H; subst.
      eapply block_belong_to_file_bn_eq in H0; [ | apply H12 ].
      subst.
      eapply block_is_unused_xor_belong_to_file; eauto.
  Qed.

  Lemma treeseq_one_upd_alternative : forall t pathname off v,
    treeseq_one_upd t pathname off v =
    mk_tree (match find_subtree pathname (TStree t) with
             | Some (TreeFile inum f) => update_subtree pathname (TreeFile inum (BFILE.mk_bfile (updN (BFILE.BFData f) off v) (BFILE.BFAttr f))) (TStree t)
             | Some (TreeDir _ _) => TStree t
             | None => TStree t
             end) (TSilist t) (TSfree t).
  Proof.
    intros.
    unfold treeseq_one_upd.
    case_eq (find_subtree pathname (TStree t)); intros.
    destruct d; auto.
    destruct t; auto.
    destruct t; auto.
  Qed.

  Lemma treeseq_one_safe_dsupd_1 : forall tolder tnewest mscs mscs' pathname off v inum f,
    treeseq_one_safe tolder tnewest mscs ->
    find_subtree pathname (TStree tnewest) = Some (TreeFile inum f) ->
    MSAlloc mscs' = MSAlloc mscs ->
    treeseq_one_safe (treeseq_one_upd tolder pathname off v) tnewest mscs'.
  Proof.
    unfold treeseq_one_safe; intros.
    repeat rewrite treeseq_one_upd_alternative; simpl.
    rewrite H1; clear H1 mscs'.
    unfold dirtree_safe in *; intuition.
    destruct (list_eq_dec string_dec pathname0 pathname); subst.
    - edestruct H2; eauto.
      left.
      intuition.
      repeat deex.
      exists pathname'.
      case_eq (find_subtree pathname (TStree tolder)); intros; eauto.
      destruct d; eauto.
      destruct (list_eq_dec string_dec pathname' pathname); subst.
      + erewrite find_update_subtree; eauto.
        rewrite H4 in H6; inversion H6. eauto.
      + rewrite find_subtree_update_subtree_ne_path by auto; eauto.
    - edestruct H2; eauto.
      left.
      intuition.
      repeat deex.
      exists pathname'.
      case_eq (find_subtree pathname (TStree tolder)); intros; eauto.
      destruct d; eauto.
      destruct (list_eq_dec string_dec pathname' pathname); subst.
      + erewrite find_update_subtree; eauto.
        rewrite H4 in H6; inversion H6. eauto.
      + rewrite find_subtree_update_subtree_ne_path by auto; eauto.
  Qed.

  Lemma treeseq_one_safe_dsupd_2 : forall tolder tnewest mscs mscs' pathname off v inum f,
    treeseq_one_safe tolder tnewest mscs ->
    find_subtree pathname (TStree tnewest) = Some (TreeFile inum f) ->
    MSAlloc mscs' = MSAlloc mscs ->
    treeseq_one_safe tolder (treeseq_one_upd tnewest pathname off v) mscs'.
  Proof.
    unfold treeseq_one_safe; intros.
    repeat rewrite treeseq_one_upd_alternative; simpl.
    rewrite H0; simpl.
    rewrite H1; clear H1 mscs'.
    unfold dirtree_safe in *; intuition.
    destruct (list_eq_dec string_dec pathname0 pathname); subst.
    - erewrite find_update_subtree in H; eauto.
      inversion H; subst.
      edestruct H2; eauto.
    - rewrite find_subtree_update_subtree_ne_path in H by auto.
      edestruct H2; eauto.
  Qed.

  Lemma treeseq_one_safe_dsupd : forall tolder tnewest mscs mscs' pathname off v inum f,
    treeseq_one_safe tolder tnewest mscs ->
    find_subtree pathname (TStree tnewest) = Some (TreeFile inum f) ->
    MSAlloc mscs' = MSAlloc mscs ->
    treeseq_one_safe (treeseq_one_upd tolder pathname off v)
      (treeseq_one_upd tnewest pathname off v) mscs'.
  Proof.
    intros.
    eapply treeseq_one_safe_trans.
    eapply treeseq_one_safe_dsupd_1; eauto.
    eapply treeseq_one_safe_dsupd_2; eauto.
    eapply treeseq_one_safe_refl.
  Qed.

  Theorem treeseq_in_ds_upd : forall F Ftop fsxp mscs ts ds mscs' pathname bn off v inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file (TSilist (ts !!)) bn inum off ->
    treeseq_in_ds F Ftop fsxp mscs ts ds ->
    treeseq_pred (treeseq_safe pathname  (BFILE.MSAlloc mscs) (ts !!)) ts ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs ->
    treeseq_in_ds F Ftop fsxp mscs' (tsupd ts pathname off v) (dsupd ds bn v).
  Proof.
    unfold treeseq_in_ds.
    intros.
    simpl; intuition.
    unfold tsupd.
    unfold dsupd.
    eapply NEforall2_d_map; eauto.
    simpl; intros.
    intuition; subst.
    eapply tree_rep_nth_upd; eauto.
    rewrite d_map_latest.
    eapply treeseq_one_safe_dsupd; eauto.
  Qed.

  Lemma treeseq_upd_safe_upd: forall Fm fsxp Ftop mscs Ftree ts ds n pathname pathname' f f' off v inum bn,
    (Fm ✶ rep fsxp Ftop (update_subtree pathname (TreeFile inum f') (TStree ts !!)) (TSilist ts !!)
         (fst (TSfree ts !!), snd (TSfree ts !!)))%pred (list2nmem (dsupd ds bn v) !!) ->
    (Ftree ✶ pathname |-> Some (inum, f))%pred (dir2flatmem2 (TStree ts !!)) -> 
    True ->
    True ->
    BFILE.block_belong_to_file (TSilist ts !!) bn inum off ->
    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) ts !!) ts ->
    treeseq_safe pathname (MSAlloc mscs) ts !! (nthd n ts) ->
    tree_names_distinct (TStree ts !!) ->
    tree_inodes_distinct (TStree ts !!) ->
    tree_rep Fm Ftop fsxp (nthd n ts) (list2nmem (nthd n ds)) ->
    treeseq_safe pathname' (MSAlloc mscs)
      (treeseq_one_upd ts !! pathname off v)
      (treeseq_one_upd (nthd n ts) pathname off v).
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as H0'; eauto.
    repeat rewrite treeseq_one_upd_alternative; simpl.
    rewrite H0' in *; simpl.
    destruct (list_eq_dec string_dec pathname' pathname); subst; simpl in *.
    - unfold treeseq_safe in *.
      intuition.
      + unfold treeseq_safe_fwd in *; intros; simpl in *.
        erewrite find_update_subtree in *; eauto.
        exists {|
             BFILE.BFData := (BFILE.BFData f) ⟦ off := v ⟧;
             BFILE.BFAttr := BFILE.BFAttr f |}.
        specialize (H9 inum0 off0 bn0).
        case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
        destruct d.
        -- rewrite H12 in *; simpl in *.
          erewrite find_update_subtree in *; eauto.
          destruct H10.
          intuition.
          inversion H13; subst. clear H13.
          edestruct H9.
          eexists b.
          split; eauto.
          intuition.
          rewrite H0' in H13.
          inversion H13; subst; eauto.
          edestruct H9.
          eexists b.
          intuition.
          inversion H13; subst; eauto.
          intuition.
        -- (* a directory *)
          rewrite H12 in *; subst; simpl in *.
          exfalso.
          edestruct H10.
          intuition.
          rewrite H12 in H14; inversion H14.
        -- (* None *)
          rewrite H12 in *; subst; simpl in *.
          exfalso.
          edestruct H10.
          intuition.
          rewrite H12 in H14; inversion H14.
      + unfold treeseq_safe_bwd in *. intros; simpl in *.
        erewrite find_update_subtree in *; eauto.
        destruct H10.
        intuition.
        inversion H12.
        subst.
        clear H12.
        case_eq (find_subtree pathname (TStree (nthd n ts))).
        intros.
        destruct d.
        -- (* a file *)
          specialize (H5 inum0 off0 bn0).
          destruct H5.
          eexists f.
          intuition.
 
          destruct H5.
          unfold BFILE.ilist_safe in H11.
          intuition.
          specialize (H14 inum0 off0 bn0).
          destruct H14; auto.

          left.
          eexists.
          split.
          intuition.
          rewrite H10 in H11.
          inversion H11; subst.
          eauto.
          intuition.

          right; eauto.

        -- (* a directory *)
        destruct (BFILE.block_is_unused_dec (BFILE.pick_balloc (TSfree ts!!) (MSAlloc mscs)) bn0).
        ++ right.
          unfold BFILE.ilist_safe in H11; intuition.
          eapply In_incl.
          apply b.
          eauto.
        ++ 
          specialize (H5 inum0 off0 bn0).
          destruct H5.
          eexists.
          split; eauto.
          destruct H5.
          intuition.
          rewrite H10 in H12.
          exfalso; inversion H12.
          right; eauto.

        -- (* None *)
          intros.
          right.
          specialize (H5 inum0 off0 bn0).
          edestruct H5.
          exists f; eauto.
          deex.
          exfalso.
          rewrite H10 in H14; congruence.
          eassumption.
   - (* different pathnames, but pathname' is still safe, if it was safe. *)
     unfold treeseq_safe in *.
     unfold treeseq_pred in H4.
     eapply NEforall_d_in with (x := (nthd n ts)) in H4 as H4'.  
     2: eapply nthd_in_ds.
     intuition; simpl.
      * unfold treeseq_safe_fwd in *; simpl in *; eauto.
        intros.
        erewrite find_subtree_update_subtree_ne_path; eauto.
        case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
        destruct d.
        (* a file *)
        rewrite H15 in H11.
        erewrite find_subtree_update_subtree_ne_path in H11; eauto.
        destruct H11.
        (* a directory *)
        rewrite H15 in H11; eauto.
        (* None *)
        rewrite H15 in H11; eauto.
      * unfold treeseq_safe_bwd in *; simpl; intros.
        deex; intuition.
        rewrite find_subtree_update_subtree_ne_path in *; eauto.
        case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
        destruct d.
        erewrite find_subtree_update_subtree_ne_path; eauto.
        specialize (H10 inum0 off0 bn0).
        edestruct H10.
        exists f'0.
        split; eauto.
        destruct (addr_eq_dec inum inum0).
        ** subst.
          exfalso.
          eapply find_subtree_inode_pathname_unique in H0'; eauto.
        ** destruct H17.
          left.
          exists x; eauto.
        ** right; eauto.
        **
          specialize (H10 inum0 off0 bn0).
          edestruct H10.
          exists f'0.
          split; eauto.
          destruct H17.
          intuition.
          left.
          exists x.
          split; eauto.
          right; eauto.
  Qed.

  Theorem treeseq_update_fblock_d_ok : forall fsxp inum off v mscs,
    {< ds ts Fm Ftop Ftree pathname f Fd vs,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
      [[ (Ftree * pathname |-> Some (inum, f))%pred  (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs')
      exists ts' f' ds' bn,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
        [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
       [[ ts' = tsupd ts pathname off (v, vsmerge vs) ]] *
       [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ (Ftree * pathname |-> Some (inum, f'))%pred (dir2flatmem2 (TStree ts' !!)) ]] *
       [[[ (BFILE.BFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
       [[ BFILE.BFAttr f' = BFILE.BFAttr f ]]
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
       exists ds' ts' mscs' bn,
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
         [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
         [[ MSAlloc mscs' = MSAlloc mscs ]] *
         [[ ts' = tsupd ts pathname off (v, vsmerge vs) ]] *
         [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
         [[ BFILE.block_belong_to_file (TSilist ts !!) bn inum off ]]
   >} AFS.update_fblock_d fsxp inum off v mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.update_fblock_d_ok.
    safecancel.
    eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.


    pose proof (list2nmem_array (BFILE.BFData f)).
    pred_apply.
    erewrite arrayN_except with (i := off).
    cancel.

    eapply list2nmem_inbound; eauto.

    safestep.


    eapply treeseq_in_ds_upd; eauto.

    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.

    eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred; eauto.
    eapply NEforall_d_in'; intros.
    apply d_in_d_map in H6; deex; intuition.
    eapply NEforall_d_in in H7 as H7'; try eassumption.
    unfold tsupd; rewrite d_map_latest.
    unfold treeseq_in_ds in H8.
    eapply d_in_nthd in H9 as H9'; deex.
    eapply NEforall2_d_in  with (x := (nthd n ts)) in H8 as Hd'; eauto.
    intuition.
    eapply treeseq_upd_safe_upd; eauto.

    distinct_names.
    distinct_inodes.

    unfold tsupd.
    unfold treeseq_one_upd.
    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'; eauto.
 
    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'; eauto.
    3: eassumption.

    unfold tsupd.
    erewrite d_map_latest; eauto.
    unfold treeseq_one_upd.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as H0'.
    rewrite H0'; simpl.

    eapply list2nmem_sel in H5 as H5'.
    rewrite <- H5'.

    assert( f' = {|
           BFILE.BFData := (BFILE.BFData f) ⟦ off := (v, vsmerge vs) ⟧;
           BFILE.BFAttr := BFILE.BFAttr f |}).
    destruct f'.
    f_equal.
    simpl in H14.
    eapply list2nmem_array_updN in H14.
    rewrite H14.
    subst; eauto.
    eapply list2nmem_ptsto_bound in H5 as H5''; eauto.
    eauto.
    rewrite H6.
    eapply dir2flatmem2_update_subtree; eauto.
    distinct_names'.
    distinct_names'.

    pred_apply.
    rewrite arrayN_ex_frame_pimpl; eauto.
    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'.
    cancel.

    xcrash_rewrite.
    xcrash_rewrite.
    xform_norm.
    cancel.
    or_r.
    eapply pimpl_exists_r; eexists.
    repeat (xform_deex_r).
    xform_norm; safecancel.
    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'; eauto.
    eauto.

    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'; eauto.
    eapply treeseq_in_ds_upd; eauto.

    eapply dir2flatmem2_find_subtree_ptsto; eauto.
    distinct_names'.
    eassumption.

  Grab Existential Variables.
    exact ($0, nil).
  Qed.

  (* XXX maybe inum should be an argument and the TreeFile case should be split into two cases. *)
  Definition treeseq_one_file_sync (t: treeseq_one) pathname :=
      match find_subtree pathname (TStree t) with
      | None => t
      | Some (TreeFile inum f) => 
        mk_tree (update_subtree pathname (TreeFile inum (BFILE.synced_file f)) (TStree t)) (TSilist t) (TSfree t)
      | Some (TreeDir _ _) => t
      end.

  Definition ts_file_sync pathname (ts: treeseq) :=
    d_map (fun t => treeseq_one_file_sync t pathname) ts.

  Theorem dirtree_update_safe_pathname_vssync_vecs_file:
    forall pathname f tree fsxp F F0 ilist freeblocks inum m al,
    let tree_newest := update_subtree pathname (TreeFile inum (BFILE.synced_file f)) tree in
    find_subtree pathname tree = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (BFILE.BFData f) ->
    (length al = length (BFILE.BFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file ilist (selN al i 0) inum i) ->
    (F0 * rep fsxp F tree ilist freeblocks)%pred (list2nmem m) ->
    (F0 * rep fsxp F tree_newest ilist freeblocks)%pred (list2nmem (vssync_vecs m al)).
  Proof.
    induction al using rev_ind; simpl; intros.
    - intuition. simpl. pred_apply.
      (* H3 implies length of BFILE.sync_file is also 0 *)
      admit.
    - Search vssync_vecs.
  Admitted.

  Lemma tree_rep_nth_file_sync: forall Fm Ftop fsxp mscs ds ts n al pathname inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (BFILE.BFData f) ->
    (length al = length (BFILE.BFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
    tree_rep Fm Ftop fsxp (nthd n ts) (list2nmem (nthd n ds)) ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    tree_rep Fm Ftop fsxp (treeseq_one_file_sync (nthd n ts) pathname) (list2nmem (vssync_vecs (nthd n ds) al)).
  Proof.
    intros.
    eapply NEforall_d_in in H4 as H4'; [ | apply nthd_in_ds with (n := n) ].
    unfold treeseq_safe in H4'.
    unfold treeseq_one_file_sync.
    case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
    destruct d.
    - (* a file *)
      unfold tree_rep; simpl.
      (* XXX the al for this lemma should be the one corresponding to BFData b *)
      eapply dirtree_update_safe_pathname_vssync_vecs_file; eauto.
  Admitted.

  Fixpoint synced_up_to_n n (vsl : list valuset) : list valuset :=
    match n with
    | O => vsl
    | S n' =>
      match vsl with
      | nil => nil
      | vs :: vsl' => (fst vs, nil) :: (synced_up_to_n n' vsl')
      end
    end.

  Theorem synced_list_up_to_n : forall vsl,
    synced_list (map fst vsl) = synced_up_to_n (length vsl) vsl.
  Proof.
    induction vsl; eauto.
    simpl.
    unfold synced_list; simpl.
    f_equal.
    eauto.
  Qed.

  Lemma length_synced_up_to_n : forall n vsl,
    length vsl = length (synced_up_to_n n vsl).
  Proof.
    induction n; simpl; eauto; intros.
    destruct vsl; eauto.
    simpl; eauto.
  Qed.

  Lemma synced_up_to_n_nil : forall n, synced_up_to_n n nil = nil.
  Proof.
    induction n; eauto.
  Qed.

  Lemma synced_up_to_n_too_long : forall vsl n,
    n >= Datatypes.length vsl ->
    synced_up_to_n n vsl = synced_up_to_n (Datatypes.length vsl) vsl.
  Proof.
    induction vsl; simpl; intros; eauto.
    rewrite synced_up_to_n_nil; eauto.
    destruct n; try omega.
    simpl; f_equal.
    eapply IHvsl.
    omega.
  Qed.

  Lemma cons_synced_up_to_n' : forall synclen d l default,
    synclen <= Datatypes.length l ->
    (fst d, []) :: synced_up_to_n synclen l =
    synced_up_to_n synclen (d :: l) ⟦ synclen := (fst (selN (d :: l) synclen default), nil) ⟧.
  Proof.
    induction synclen; simpl; intros; eauto.
    f_equal.
    destruct l; simpl.
    rewrite synced_up_to_n_nil; eauto.
    erewrite IHsynclen; simpl in *; eauto.
    omega.
  Qed.

  Lemma cons_synced_up_to_n : forall synclen d l default,
    (fst d, []) :: synced_up_to_n synclen l =
    synced_up_to_n synclen (d :: l) ⟦ synclen := (fst (selN (d :: l) synclen default), nil) ⟧.
  Proof.
    intros.
    destruct (le_dec synclen (Datatypes.length l)).
    eapply cons_synced_up_to_n'; eauto.
    rewrite updN_oob by (simpl; omega).
    rewrite synced_up_to_n_too_long by omega. rewrite <- synced_list_up_to_n.
    rewrite synced_up_to_n_too_long by (simpl; omega). rewrite <- synced_list_up_to_n.
    firstorder.
  Qed.

  Fixpoint synced_file_alt_helper f off :=
    match off with
    | O => f
    | S off' =>
      let f' := BFILE.mk_bfile (updN (BFILE.BFData f) off' (fst (selN (BFILE.BFData f) off' ($0, nil)), nil)) (BFILE.BFAttr f) in
      synced_file_alt_helper f' off'
    end.

  Definition synced_file_alt f :=
    synced_file_alt_helper f (Datatypes.length (BFILE.BFData f)).

  Theorem synced_file_alt_equiv : forall f,
    BFILE.synced_file f = synced_file_alt f.
  Proof.
    unfold BFILE.synced_file, synced_file_alt; intros.
    rewrite synced_list_up_to_n.
    unfold BFILE.datatype.
    remember (@Datatypes.length valuset (BFILE.BFData f)) as synclen.
    assert (synclen <= Datatypes.length (BFILE.BFData f)) by simplen.
    clear Heqsynclen.
    generalize dependent f.
    induction synclen; simpl; intros.
    - destruct f; eauto.
    - rewrite <- IHsynclen; simpl.
      f_equal.
      destruct (BFILE.BFData f).
      simpl in *; omega.
      eapply cons_synced_up_to_n.
      rewrite length_updN. omega.
  Qed.

  Lemma treeseq_one_upd_noop : forall t pathname off v inum f def,
    tree_names_distinct (TStree t) ->
    find_subtree pathname (TStree t) = Some (TreeFile inum f) ->
    off < Datatypes.length (BFILE.BFData f) ->
    selN (BFILE.BFData f) off def = v ->
    t = treeseq_one_upd t pathname off v.
  Proof.
    unfold treeseq_one_upd; intros.
    rewrite H0.
    destruct t; simpl in *; f_equal.
    rewrite update_subtree_same; eauto.
    rewrite H0.
    f_equal.
    f_equal.
    destruct f; simpl in *.
    f_equal.
    rewrite <- H2.
    rewrite updN_selN_eq; eauto.
  Qed.

  Fixpoint treeseq_one_file_sync_alt_helper (t : treeseq_one) (pathname : list string) off fdata :=
    match off with
    | O => t
    | S off' =>
      let t' := treeseq_one_upd t pathname off' (selN fdata off' $0, nil) in
      treeseq_one_file_sync_alt_helper t' pathname off' fdata
    end.

  Definition treeseq_one_file_sync_alt (t : treeseq_one) (pathname : list string) :=
    match find_subtree pathname (TStree t) with
    | None => t
    | Some (TreeDir _ _) => t
    | Some (TreeFile inum f) =>
      treeseq_one_file_sync_alt_helper t pathname (length (BFILE.BFData f)) (map fst (BFILE.BFData f))
    end.

  Lemma treeseq_one_file_sync_alt_equiv : forall t pathname,
    tree_names_distinct (TStree t) ->
    treeseq_one_file_sync t pathname = treeseq_one_file_sync_alt t pathname.
  Proof.
    unfold treeseq_one_file_sync, treeseq_one_file_sync_alt; intros.
    case_eq (find_subtree pathname (TStree t)); eauto.
    destruct d; eauto.
    intros.
    rewrite synced_file_alt_equiv. unfold synced_file_alt.
    remember (@Datatypes.length BFILE.datatype (BFILE.BFData b)) as synclen; intros.
    assert (synclen <= Datatypes.length (BFILE.BFData b)) by simplen.
    clear Heqsynclen.

    remember (map fst (BFILE.BFData b)) as synced_blocks.
    generalize dependent synced_blocks.
    generalize dependent t.
    generalize dependent b.
    induction synclen; intros.
    - simpl.
      destruct t; destruct b; simpl in *; f_equal.
      eapply update_subtree_same; eauto.
    - simpl.
      erewrite <- IHsynclen.
      f_equal.
      + unfold treeseq_one_upd. rewrite H0; simpl.
        rewrite update_update_subtree_same. reflexivity.
      + unfold treeseq_one_upd. rewrite H0. destruct t; eauto.
      + unfold treeseq_one_upd. rewrite H0. destruct t; eauto.
      + simpl. rewrite length_updN. omega.
      + unfold treeseq_one_upd. rewrite H0. simpl.
        eapply tree_names_distinct_update_subtree.
        eauto. constructor.
      + subst; simpl.
        unfold treeseq_one_upd. rewrite H0; simpl.
        erewrite selN_map.
        erewrite find_update_subtree; eauto.
        unfold BFILE.datatype in *; omega.
      + subst; simpl.
        rewrite map_updN; simpl.
        erewrite selN_eq_updN_eq; eauto.
        erewrite selN_map; eauto.
  Grab Existential Variables.
    exact $0.
  Qed.

  Lemma treeseq_one_file_sync_alt_equiv_d_map : forall pathname ts,
    NEforall (fun t => tree_names_distinct (TStree t)) ts ->
    d_map (fun t => treeseq_one_file_sync t pathname) ts =
    d_map (fun t => treeseq_one_file_sync_alt t pathname) ts.
  Proof.
    unfold d_map; destruct ts; intros.
    f_equal; simpl.
    - eapply treeseq_one_file_sync_alt_equiv.
      eapply H.
    - eapply map_ext_in; intros.
      eapply treeseq_one_file_sync_alt_equiv.
      destruct H; simpl in *.
      eapply Forall_forall in H1; eauto.
  Qed.

  Lemma tree_safe_file_sync_1 : forall Fm Ftop fsxp mscs ds ts mscs' pathname,
    (exists inum f, find_subtree pathname (TStree ts !!) = Some (TreeFile inum f)) ->
    treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs -> 
    treeseq_one_safe (ts !!) (treeseq_one_file_sync (ts !!) pathname) mscs'.
  Proof.
    intros.
    rewrite treeseq_one_file_sync_alt_equiv.
    unfold treeseq_one_file_sync_alt.
    inversion H.
    destruct H2.
    rewrite H2.
    remember (Datatypes.length (BFILE.BFData x0)) as len; clear Heqlen.
    remember (ts !!) as y. rewrite Heqy at 1.
    assert (treeseq_one_safe ts !! y mscs').
    subst; eapply treeseq_one_safe_refl.
    clear Heqy. clear H2.
    generalize dependent y.
    induction len; simpl; intros; eauto.
    eapply IHlen.
    admit.
    repeat deex.
    eapply treeseq_one_safe_dsupd_2; eauto.
    admit.
  Admitted.

  Lemma tree_safe_file_sync_2 : forall Fm Ftop fsxp mscs ds ts mscs' n pathname,
    treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs -> 
    treeseq_one_safe (treeseq_one_file_sync (nthd n ts) pathname) (ts !!) mscs'.
  Proof.
    intros.
    rewrite treeseq_one_file_sync_alt_equiv.
    unfold treeseq_one_file_sync_alt.
    case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
    destruct d.

    remember (Datatypes.length (BFILE.BFData b)) as len; clear Heqlen.
    remember (nthd n ts) as y.
    assert (treeseq_one_safe (nthd n ts) y mscs').
    subst; eapply treeseq_one_safe_refl.
    clear Heqy.
    assert (exists b0, find_subtree pathname (TStree y) = Some (TreeFile n0 b0) /\ map fst (BFILE.BFData b) = map fst (BFILE.BFData b0)).
    eexists; intuition eauto.
    clear H1.
    generalize dependent y.
    induction len; simpl; intros; eauto.
    admit.
    eapply IHlen.
    destruct H3; intuition.
    eapply treeseq_one_safe_dsupd_2; eauto.
    destruct H3; intuition.
    eexists; split.
    unfold treeseq_one_upd.
    rewrite H3; simpl.
    erewrite find_update_subtree by eauto. reflexivity.
    simpl.
    admit.
    admit.
    admit.
    admit.
  Admitted.

  Lemma tree_safe_file_sync: forall Fm Ftop fsxp mscs ds ts mscs' n al pathname inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (BFILE.BFData f) ->
    (length al = length (BFILE.BFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs -> 
    treeseq_one_safe (treeseq_one_file_sync (nthd n ts) pathname) 
     (d_map (fun t : treeseq_one => treeseq_one_file_sync t pathname) ts) !! mscs'.
  Proof.
    intros.
    rewrite d_map_latest.
    eapply treeseq_one_safe_trans.
    eapply tree_safe_file_sync_2; eauto.
    eapply tree_safe_file_sync_1; eauto.
  Qed.

  Lemma treeseq_in_ds_file_sync: forall  Fm Ftop fsxp mscs mscs' ds ts al pathname inum  f,
    treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (BFILE.BFData f) ->
    (length al = length (BFILE.BFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs ->
    treeseq_in_ds Fm Ftop fsxp mscs' (ts_file_sync pathname ts) (dssync_vecs ds al).
  Proof.
    unfold treeseq_in_ds.
    intros.
    simpl; intuition.
    unfold ts_file_sync, dssync_vecs.
    eapply NEforall2_d_map; eauto.
    simpl; intros.
    intuition; subst.
    eapply tree_rep_nth_file_sync; eauto.
    eapply tree_safe_file_sync; eauto.
  Qed.

  Lemma treeseq_sync_safe_sync: forall Fm fsxp Ftop mscs Ftree ts ds pathname pathname' f inum al,
    (Fm ✶ rep fsxp Ftop (update_subtree pathname (TreeFile inum (BFILE.synced_file f)) (TStree ts !!))
           (TSilist ts !!) (fst (TSfree ts !!), snd (TSfree ts !!)))%pred
        (list2nmem (dssync_vecs ds al) !!) ->
    (Ftree ✶ pathname |-> Some (inum, f))%pred (dir2flatmem2 (TStree ts !!)) -> 
    Datatypes.length al = Datatypes.length (BFILE.BFData f) ->
    (length al = length (BFILE.BFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) ts !!) ts ->
    tree_names_distinct (TStree ts !!) ->
    tree_inodes_distinct (TStree ts !!) ->
    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) 
      (treeseq_one_file_sync ts !! pathname))
      (d_map (fun t : treeseq_one => treeseq_one_file_sync t pathname) ts).
  Proof.
    
  Admitted.

  Ltac distinct_inodes' :=
    repeat match goal with
      | [ H: treeseq_in_ds _ _ _ _ ?ts _ |- DIRTREE.tree_inodes_distinct (TStree ?ts !!) ] => 
        idtac "inodes"; eapply treeseq_in_ds_tree_pred_latest in H as Hpred;
        eapply DIRTREE.rep_tree_inodes_distinct; eapply Hpred
    end.

  Theorem treeseq_file_sync_ok : forall fsxp inum mscs,
    {< ds ts Fm Ftop Ftree pathname f,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
      [[ (Ftree * pathname |-> Some (inum, f))%pred (dir2flatmem2 (TStree ts!!)) ]]
    POST:hm' RET:^(mscs')
      exists ds' al,
       let ts' := ts_file_sync pathname ts in
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
         [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
          [[ forall pathname',
             treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
             treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
         [[ ds' = dssync_vecs ds al]] *
         [[ length al = length (BFILE.BFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i ]] *
         [[ MSAlloc mscs' = MSAlloc mscs ]] *
         [[ (Ftree * pathname |-> Some (inum, (BFILE.synced_file f)))%pred (dir2flatmem2 (TStree ts' !!)) ]]
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
   >} AFS.file_sync fsxp inum mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.file_sync_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
    step.
    eapply treeseq_in_ds_file_sync; eauto.
    eapply dir2flatmem2_find_subtree_ptsto in H4 as H4'.
    eassumption.
    distinct_names'.

    unfold ts_file_sync.
    rewrite d_map_latest.
    eapply treeseq_sync_safe_sync; eauto.
    distinct_names'.
    distinct_inodes'.
    unfold ts_file_sync.
    rewrite d_map_latest.
    unfold treeseq_one_file_sync.
    eapply dir2flatmem2_find_subtree_ptsto in H4 as H4'; eauto.
    rewrite H4'; simpl.
    eapply dir2flatmem2_update_subtree; eauto.
    distinct_names'.
    distinct_names'.
  Qed.

  Lemma treeseq_latest: forall (ts : treeseq),
    (ts !!, []) !! = ts !!.
  Proof.
    intros.
    unfold latest.
    simpl; reflexivity.
  Qed.

  Theorem treeseq_tree_sync_ok : forall fsxp mscs,
    {< ds ts Fm Ftop,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]]
    POST:hm' RET:^(mscs')
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (ds!!, nil)) (MSLL mscs') hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ((ts !!), nil) (ds!!, nil)]]
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
   >} AFS.tree_sync fsxp mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.tree_sync_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H5 as Hpred; eauto.
    step.
    unfold treeseq_in_ds.
    unfold NEforall2.
    simpl in *.
    split.
    split.
    unfold treeseq_in_ds in H5.
    eapply NEforall2_latest in H5.
    intuition.
    simpl.
    unfold treeseq_in_ds in H5.
    eapply NEforall2_latest in H5.
    intuition.
    unfold treeseq_one_safe in *.
    simpl in *.
    rewrite H9; simpl.
    erewrite treeseq_latest.
    eapply dirtree_safe_refl.
    constructor.
  Qed.


Lemma find_subtree_find_dirlist_eq: forall name inum dents ,
  find_subtree [name] (TreeDir inum dents) = find_dirlist name dents.
Proof.
  intros.
Admitted.

  Theorem treeseq_rename_ok : forall fsxp dnum srcbase (srcname:string) dstbase dstname mscs,
    {< ds ts Fm Ftop Ftree cwd tree_elem srcnum dstnum srcfile dstfile,
    PRE:hm
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ DIRTREE.find_subtree cwd (TStree ts !!) = Some (DIRTREE.TreeDir dnum tree_elem) ]] *
      [[ (Ftree * (cwd ++ srcbase ++ [srcname]) |-> Some (srcnum, srcfile)
                * (cwd ++ dstbase ++ [dstname]) |-> Some (dstnum, dstfile))%pred (dir2flatmem2 (TStree ts !!)) ]]
    POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      ([[ isError ok ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' \/
       [[ ok = OK tt ]] * exists d ds' ts' ilist' frees' tree',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
        [[ forall pathname',
           pathname' <> cwd ++ srcbase ++ [srcname] ->
           pathname' <> cwd ++ dstbase ++ [dstname] ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
       [[ ds' = (pushd d ds) ]] *
       [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees') ]]] *
       [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
       [[ (Ftree * (cwd ++ srcbase ++ [srcname]) |-> None
                 * (cwd ++ dstbase ++ [dstname]) |-> Some (srcnum, srcfile))%pred (dir2flatmem2 (TStree ts' !!)) ]])
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
   >} AFS.rename fsxp dnum srcbase srcname dstbase dstname mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.rename_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred; eauto.
    eassumption.
    step.
    unfold AFS.rename_rep.
    cancel.
    or_r.

    (* a few obligations need: subtree = (TreeFile srcnum srcfile) using H0 *)
    eapply sep_star_split_l in H0 as H0'.
    destruct H0'.
    eapply dir2flatmem2_find_subtree_ptsto in H5.
    erewrite find_subtree_app in H5.
    2: eassumption.
    erewrite find_subtree_find_dirlist_eq in H5.
    rewrite H14 in H5.
    inversion H5.
    rewrite H11 in *.

    cancel.
    eapply treeseq_in_ds_pushd; eauto.
    unfold treeseq_one_safe; simpl.
    rewrite H4 in H9.
    eassumption.
    eapply dirents2mem2_graft_file'.
    admit.  (* XXX distinct names *)
    eapply dirents2mem2_prune_file.
    admit. (* XXX distinct names *)
    pred_apply.
    cancel.
    cancel.
    admit. (* XXX distinct names *)
  Admitted.

  (* restricted to deleting files *)
  Theorem treeseq_delete_ok : forall fsxp dnum name mscs,
    {< ds ts pathname Fm Ftop Ftree tree_elem finum file,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ DIRTREE.find_subtree pathname (TStree ts !!) = Some (DIRTREE.TreeDir dnum tree_elem) ]] *
      [[ (Ftree * ((pathname++[name])%list) |-> Some (finum, file))%pred (dir2flatmem2 (TStree ts !!)) ]]
    POST:hm RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      [[ isError ok ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm \/
      [[ ok = OK tt ]] * exists d ds' ts' tree' ilist' frees',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm *
        [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
        [[ forall pathname',
           pathname' <> pathname ++ [name] ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees') ]]] *
        [[ tree' = DIRTREE.update_subtree pathname
                      (DIRTREE.delete_from_dir name (DIRTREE.TreeDir dnum tree_elem)) (TStree ts !!) ]] *
        [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
        [[ (Ftree * (pathname ++ [name]) |-> None)%pred (dir2flatmem2 (TStree ts' !!)) ]]
    CRASH:hm
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm
    >} AFS.delete fsxp dnum name mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.delete_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    eassumption.
    step.
    or_r.
    cancel.
    eapply treeseq_in_ds_pushd; eauto.
    unfold treeseq_one_safe; simpl.
    rewrite H0 in H12.
    eassumption.
    eapply dir2flatmem2_delete_file; eauto.
    distinct_names'.
  Qed.


  Hint Extern 1 ({{_}} Bind (AFS.file_get_attr _ _ _) _) => apply treeseq_file_getattr_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.lookup _ _ _ _) _) => apply treeseq_lookup_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.read_fblock _ _ _ _) _) => apply treeseq_read_fblock_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.file_set_attr _ _ _ _) _) => apply treeseq_file_set_attr_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.update_fblock_d _ _ _ _ _) _) => apply treeseq_update_fblock_d_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.file_sync _ _ _ ) _) => apply treeseq_file_sync_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.file_truncate _ _ _ _) _) => apply treeseq_file_grow_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.tree_sync _ _ ) _) => apply treeseq_tree_sync_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.rename _ _ _ _ _ _ _) _) => apply treeseq_rename_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.delete _ _ _ _) _) => apply treeseq_delete_ok : prog.

End TREESEQ.

