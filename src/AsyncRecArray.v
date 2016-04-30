Require Import Arith.
Require Import Bool.
Require Import Pred PredCrash.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import Array.
Require Import WordAuto.
Require Import Cache.
Require Import Rounding.
Require Import List ListUtils.
Require Import Psatz.
Require Import AsyncDisk.
Require Import Classes.SetoidTactics.
Require Import RecArrayUtils.

Import ListNotations.

Set Implicit Arguments.


(* RecArray on raw, async disk *)

Module AsyncRecArray (RA : RASig).

  Module Defs := RADefs RA.
  Import RA Defs.

  Definition items_valid xp start (items : itemlist) :=
    xparams_ok xp /\  start <= (RALen xp) /\
    Forall Rec.well_formed items /\
    length items <= (RALen xp - start) * items_per_val.

  (** rep invariant *)
  Inductive state : Type :=
  | Synced : itemlist -> state
  | Unsync : itemlist -> state
  .

  Definition rep_common xp start items vl (vsl : list (list valu)) :=
    items_valid xp start items /\
    vl = ipack items /\ eqlen vl vsl.

  Definition synced_array xp start items :=
    (exists vl vsl, [[ rep_common xp start items vl vsl /\
        vsl = nils (length vl) ]] *
    arrayN ((RAStart xp ) + start) (combine vl vsl))%pred.

  Definition unsync_array xp start items :=
    (exists vl vsl, [[ rep_common xp start items vl vsl ]] *
    arrayN ((RAStart xp ) + start) (combine vl vsl))%pred.

  Definition array_rep xp start (st : state) :=
   (match st with
    | Synced items => synced_array xp start items
    | Unsync items => unsync_array xp start items
    end)%pred.

  Definition avail_rep xp start nr : rawpred :=
    (exists vsl, [[ length vsl = nr ]] *
     arrayN ((RAStart xp) + start) vsl)%pred.

  Local Hint Extern 0 (okToUnify (arrayN (RAStart ?a) _ _) (arrayN (RAStart ?a) _ _)) => constructor : okToUnify.
  Local Hint Extern 0 (okToUnify (arrayN (RAStart ?b + ?a) _ _) (arrayN (RAStart ?b + ?a) _ _)) 
    => constructor : okToUnify.

  Definition nr_blocks st :=
    match st with
    | Synced l => (divup (length l) items_per_val)
    | Unsync l => (divup (length l) items_per_val)
    end.

  Lemma items_valid_app : forall xp st a b,
    items_valid xp st (a ++ b) ->
    items_valid xp st a /\ items_valid xp st b.
  Proof.
    unfold items_valid; intros; split; intros;
    pose proof (well_formed_app_iff itemtype a b);
    rewrite app_length in *; intuition.
  Qed.

  Lemma le_add_helper: forall a b c d,
    b <= d -> a + d <= c -> a + b <= c.
  Proof.
    intros; omega.
  Qed.

  Lemma le_add_le_sub : forall a b c,
    a <= c -> b <= c - a -> a + b <= c.
  Proof.
    intros. omega.
  Qed.

  Lemma items_valid_app2 : forall xp st a b,
    length b <= (roundup (length a) items_per_val - length a)
    -> items_valid xp st a
    -> Forall Rec.well_formed b
    -> items_valid xp st (a ++ b).
  Proof.
    unfold items_valid, roundup; intuition.
    pose proof (well_formed_app_iff itemtype a b); intuition.
    rewrite app_length.
    eapply le_add_helper. apply H.
    rewrite le_plus_minus_r.
    apply mult_le_compat_r.
    apply divup_le; lia.
    apply roundup_ge.
    apply items_per_val_gt_0.
  Qed.

  Lemma items_valid_app3 : forall xp st a b na,
    length a = na * items_per_val ->
    items_valid xp st (a ++ b) -> items_valid xp (st + na) b.
  Proof.
    unfold items_valid; intros; split; intros;
    pose proof (well_formed_app_iff itemtype a b);
    rewrite app_length in *; intuition.

    apply le_add_le_sub; auto.
    eapply Nat.mul_le_mono_pos_r.
    apply items_per_val_gt_0.
    rewrite <- H; omega.

    rewrite Nat.sub_add_distr.
    rewrite Nat.mul_sub_distr_r.
    apply Nat.le_add_le_sub_l.
    setoid_rewrite <- H; auto.
  Qed.

  Lemma items_valid_app4 : forall xp st a b na,
    length a = na * items_per_val ->
    items_valid xp st a ->
    items_valid xp (st + na) b ->
    items_valid xp st (a ++ b).
  Proof.
    unfold items_valid, roundup; intuition.
    apply well_formed_app_iff; intuition.
    rewrite app_length.
    rewrite Nat.sub_add_distr in H8.
    rewrite Nat.mul_sub_distr_r in H8.
    rewrite <- H in H8.
    omega.
  Qed.

  Lemma synced_array_is : forall xp start items,
    synced_array xp start items =p=>
    arrayN ((RAStart xp) + start) (combine (ipack items) (nils (length (ipack items)))).
  Proof.
    unfold synced_array, rep_common; cancel; subst; auto.
  Qed.

  Lemma array_rep_sync_nil : forall xp a,
    xparams_ok xp -> a <= (RALen xp) ->
    array_rep xp a (Synced nil) <=p=> emp.
  Proof.
    unfold array_rep, synced_array, rep_common; intros.
    split; cancel; subst; simpl; unfold items_valid, eqlen;
      try setoid_rewrite ipack_nil; simpl; intuition; auto.
  Qed.

  Lemma array_rep_sync_nil_emp : forall xp a,
    array_rep xp a (Synced nil) =p=> emp.
  Proof.
    unfold array_rep, synced_array, rep_common; intros.
    cancel; subst; simpl; unfold items_valid, eqlen;
      try setoid_rewrite ipack_nil; simpl; intuition; auto.
  Qed.

  Lemma array_rep_sync_nil_sep_star : forall xp a l,
    array_rep xp a (Synced l) =p=> array_rep xp a (Synced nil) * array_rep xp a (Synced l).
  Proof.
    intros.
    unfold array_rep, synced_array, rep_common, eqlen; intros.
    norm.
    eassign (@nil valu).
    cancel.
    subst; repeat setoid_rewrite ipack_nil; simpl; auto;
    unfold items_valid in *; intuition.
    rewrite nils_length; auto.
  Qed.

  Hint Rewrite list_chunk_nil ipack_nil.
  Hint Rewrite Nat.add_0_r Nat.add_0_l.
  Hint Rewrite synced_array_is.
  Hint Rewrite combine_length nils_length : lists.
  Hint Rewrite ipack_length divup_mul.

  Ltac rewrite_ignore H :=
    match type of H with
    | forall _, corr2 _ _ => idtac
    | sep_star _ _ _ => idtac
    end.

  Ltac simplen_rewrite H := try progress (
    set_evars_in H; (rewrite_strat (topdown (hints core)) in H); subst_evars;
      [ try simplen_rewrite H | try autorewrite with core .. ];
    match type of H with
    | context [ length (list_chunk _ _ _) ] => rewrite block_chunk_length in H
    end).

  Ltac simplen' := repeat match goal with
    | [H : @eqlen _ ?T ?a ?b |- context [length ?a] ] => setoid_replace (length a) with (length b) by auto
    | [H : context[length ?x] |- _] => progress ( first [ is_var x | rewrite_ignore H | simplen_rewrite H ] )
    | [H : length ?l = _  |- context [ length ?l ] ] => setoid_rewrite H
    | [H : ?l = _  |- context [ ?l ] ] => setoid_rewrite H
    | [H : ?l = _ , H2 : context [ ?l ] |- _ ] => rewrite H in H2
    | [H : @length ?T ?l = 0 |- context [?l] ] => replace l with (@nil T) by eauto
    | [H : @eqlen _ ?T ?l nil |- context [?l] ] => replace l with (@nil T) by eauto
    | [ |- _ < _ ] => try solve [eapply lt_le_trans; eauto; try omega ]
    end.

  Ltac simplen := unfold eqlen; eauto; repeat (try subst; simpl;
    auto; simplen'; autorewrite with core lists); simpl; eauto; try omega.

  Lemma xform_synced_array : forall xp st l,
    crash_xform (synced_array xp st l) =p=> synced_array xp st l.
  Proof.
    unfold synced_array; intros.
    xform; cancel; subst.
    rewrite crash_xform_arrayN_combine_nils.
    cancel.
    auto.
  Qed.

  Lemma xform_synced_rep : forall xp st l,
    crash_xform (array_rep xp st (Synced l)) =p=> array_rep xp st (Synced l).
  Proof.
    intros; simpl.
    apply xform_synced_array.
  Qed.

  Lemma xform_avail_rep : forall xp st nr,
    crash_xform (avail_rep xp st nr) =p=> avail_rep xp st nr.
  Proof.
    unfold avail_rep; intros; intros.
    xform.
    rewrite crash_xform_arrayN; cancel.
    unfold possible_crash_list in *; subst; intuition.
    rewrite H0.
    replace (combine l' (repeat [] (length l'))) with (synced_list l') by auto.
    rewrite synced_list_length; auto.
  Qed.


  Lemma xform_avail_rep_array_rep : forall xp st nr,
    (forall l', Forall (@Rec.well_formed itemtype) l') ->
    nr * items_per_val <= (RALen xp - st) * items_per_val ->
    xparams_ok xp ->
    st <= RALen xp ->
    crash_xform (avail_rep xp st nr) =p=>
      exists l, array_rep xp st (Synced l) *
      [[ length l = (nr * items_per_val)%nat ]].
  Proof.
    unfold avail_rep; intros.
    xform.
    rewrite crash_xform_arrayN; cancel;
    apply possible_crash_list_length in H3 as Hlength; subst.
    unfold possible_crash_list in *; subst; intuition.
    instantiate (l := fold_left iunpack l' []).
    unfold synced_array.
    cancel.
    unfold rep_common; intuition.
    unfold items_valid; intuition.
    rewrite fold_left_iunpack_length.
    congruence.

    apply ipack_iunpack; auto.

    unfold eqlen.
    rewrite repeat_length; auto.

    rewrite fold_left_iunpack_length.
    congruence.
  Qed.

  Lemma xform_unsync_array_avail : forall xp st l,
    crash_xform (unsync_array xp st l) =p=>
      avail_rep xp st (divup (length l) items_per_val).
  Proof.
    unfold unsync_array, avail_rep, rep_common; intros.
    xform.
    rewrite crash_xform_arrayN.
    unfold possible_crash_list.
    cancel.
    rewrite combine_length_eq in *; simplen.
    rewrite <- ipack_length; auto.
    rewrite synced_list_length; auto.
  Qed.

  Lemma array_rep_size_ok : forall m xp start st,
    array_rep xp start st m ->
    nr_blocks st <= RALen xp - start.
  Proof.
    unfold array_rep, synced_array, unsync_array, rep_common, items_valid.
    destruct st; intros; destruct_lift H; subst;
    apply divup_le; rewrite Nat.mul_comm; eauto.
  Qed.

  Lemma array_rep_size_ok_pimpl : forall xp st,
    array_rep xp 0 st =p=>
    array_rep xp 0 st * [[ nr_blocks st <= RALen xp ]].
  Proof.
    intros; unfold pimpl; intros.
    apply array_rep_size_ok in H as H1.
    pred_apply; cancel.
  Qed.

  Lemma array_rep_avail : forall xp start st,
    array_rep xp start st =p=>
    avail_rep xp start (nr_blocks st).
  Proof.
    unfold array_rep, avail_rep, synced_array, unsync_array, rep_common, eqlen, nr_blocks.
    intros; destruct st; cancel; subst; autorewrite with lists.
    rewrite ipack_length; auto.
    rewrite <- ipack_length.
    rewrite Nat.min_l; simplen.
  Qed.

  Lemma array_rep_avail_synced : forall xp start items,
    array_rep xp start (Synced items) =p=>
    avail_rep xp start (divup (length items) items_per_val).
  Proof.
    intros; apply array_rep_avail.
  Qed.

  Lemma avail_rep_split : forall xp start nr n1 n2,
    n1 + n2 = nr ->
    avail_rep xp start nr =p=> avail_rep xp start n1 * avail_rep xp (start + n1) n2.
  Proof.
    unfold avail_rep; intros; norm.
    instantiate (2 := (firstn n1 vsl)).
    instantiate (1 := (skipn n1 vsl)).
    cancel.
    rewrite Nat.add_assoc.
    rewrite arrayN_split by auto.
    cancel.
    intuition.
    rewrite firstn_length.
    rewrite Nat.min_l; omega.
    rewrite skipn_length.
    omega.
  Qed.

  Lemma avail_rep_merge : forall xp start nr n1 n2,
    n1 + n2 = nr ->
    avail_rep xp start n1 * avail_rep xp (start + n1) n2 =p=> avail_rep xp start nr.
  Proof.
    unfold avail_rep; intros; norm.
    instantiate (1 := vsl ++ vsl0).
    setoid_rewrite arrayN_app.
    rewrite Nat.add_assoc.
    cancel.
    intuition.
    rewrite app_length; omega.
  Qed.

  Lemma helper_add_sub : forall a b c,
    b <= c -> c <= a -> a >= b + (a - c).
  Proof.
    intros; omega.
  Qed.

  Lemma helper_add_le : forall a b nb n,
    b <= nb -> n >= a + nb -> a + b <= n.
  Proof.
    intros; omega.
  Qed.

  Local Hint Resolve items_per_val_not_0 items_per_val_gt_0 items_per_val_gt_0'.

  Lemma array_rep_synced_app : forall xp start na a b,
    length a = na * items_per_val ->
    array_rep xp start (Synced a) *
    array_rep xp (start + (divup (length a) items_per_val)) (Synced b) =p=>
    array_rep xp start (Synced (a ++ b)).
  Proof.
    simpl; intros;
    unfold synced_array, rep_common, nils; norm; subst; intuition.
    cancel.
    erewrite ipack_app by eauto.
    rewrite app_length, Nat.add_assoc.
    rewrite <- repeat_app.
    rewrite combine_app, arrayN_app, combine_length_eq by auto.
    repeat rewrite ipack_length.
    cancel.

    unfold items_valid, roundup in *; intuition.
    apply well_formed_app_iff; auto.
    rewrite app_length.
    eapply helper_add_le; eauto.
    rewrite Nat.sub_add_distr.
    setoid_rewrite Nat.mul_sub_distr_r at 2.
    apply helper_add_sub.
    apply roundup_ge; auto.
    apply Nat.mul_le_mono_r; omega.

    erewrite ipack_app; eauto.
    simplen.
  Qed.

  Lemma array_rep_synced_app_rev : forall xp start na a b,
    length a = na * items_per_val ->
    array_rep xp start (Synced (a ++ b)) =p=>
    array_rep xp start (Synced a) *
    array_rep xp (start + (divup (length a) items_per_val)) (Synced b).
  Proof.
    simpl; intros;
    unfold synced_array, rep_common, nils, eqlen; norm; subst; intuition;
    try rewrite repeat_length; auto.
    cancel.
    erewrite ipack_app by eauto.
    rewrite app_length, Nat.add_assoc.
    rewrite <- repeat_app.
    rewrite combine_app, arrayN_app, combine_length_eq by (rewrite repeat_length; auto).
    repeat rewrite ipack_length.
    cancel.
    apply (@items_valid_app xp start a b H1).
    rewrite H, divup_mul by auto.
    eapply items_valid_app3; eauto.
  Qed.

  (** read count blocks starting from the beginning *)
  Definition read_all T xp count cs rx : prog T :=
    let^ (cs, r) <- BUFCACHE.read_range (RAStart xp) count iunpack nil cs;
    rx ^(cs, r).

  Theorem read_all_ok : forall xp count cs,
    {< F d items,
    PRE            BUFCACHE.rep cs d *
                   [[ length items = (count * items_per_val)%nat /\
                      Forall Rec.well_formed items /\ xparams_ok xp ]] *
                   [[ (F * array_rep xp 0 (Synced items))%pred d ]]
    POST RET:^(cs, r)
                   BUFCACHE.rep cs d *
                   [[ (F * array_rep xp 0 (Synced items))%pred d ]] *
                   [[ r = items ]]
    CRASH  exists cs', BUFCACHE.rep cs' d
    >} read_all xp count cs.
  Proof.
    unfold read_all.
    step.

    pred_apply.
    simplen.
    simplen.

    step; subst.
    rewrite map_fst_combine by simplen.
    rewrite firstn_oob by simplen.
    eapply iunpack_ipack; eauto.
  Qed.

  Lemma vsupd_range_unsync_array : forall xp start items old_vs,
    items_valid xp start items ->
    eqlen old_vs (ipack items) ->
    arrayN (RAStart xp + start) (vsupd_range old_vs (ipack items))
      =p=> unsync_array xp start items.
  Proof.
    intros.
    unfold vsupd_range, unsync_array, rep_common, ipack.
    cancel.
    apply arrayN_unify.
    rewrite skipn_oob.
    rewrite app_nil_r.
    f_equal.
    simplen.
    simplen.
  Qed.

  Lemma write_aligned_length_helper : forall n l,
    n <= length (map block2val (list_chunk l items_per_val item0)) ->
    n <= divup (length l) items_per_val.
  Proof.
    intros; autorewrite with lists in *.
    erewrite <- list_chunk_length; eauto.
  Qed.
  Local Hint Resolve write_aligned_length_helper.

  (** write items from a given block index, 
      slots following the items will be cleared *)
  Definition write_aligned T xp start (items: itemlist) cs rx : prog T :=
    let chunks := list_chunk items items_per_val item0 in
    cs <- BUFCACHE.write_range ((RAStart xp) + start) (map block2val chunks) cs;
    rx cs.

  Theorem write_aligned_ok : forall xp start new cs,
    {< F d,
    PRE            BUFCACHE.rep cs d *
                   [[ items_valid xp start new ]] *
                   [[ (F * avail_rep xp start (divup (length new) items_per_val))%pred d ]]
    POST RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * array_rep xp start (Unsync new))%pred d' ]]
    XCRASH  exists cs' d',
                   BUFCACHE.rep cs' d' *
                   [[ (F * avail_rep xp start (divup (length new) items_per_val)) % pred d' ]]
    >} write_aligned xp start new cs.
  Proof.
    unfold write_aligned, avail_rep.
    step.
    simplen.
    step.
    setoid_rewrite vsupd_range_unsync_array; auto.
    simplen.

    eapply pimpl_trans; [ | eapply H1 ]; cancel.
    rewrite H0.
    do 3 (xform_norm; cancel).
    rewrite vsupd_range_length; auto.
    simplen; rewrite Nat.min_l; eauto.
  Qed.


  Lemma vssync_range_sync_array : forall xp start items count vsl,
    items_valid xp start items ->
    length items = (count * items_per_val)%nat ->
    length vsl = count ->
    arrayN (RAStart xp + start) (vssync_range (combine (ipack items) vsl) count)
      =p=> synced_array xp start items.
  Proof.
    unfold synced_array, rep_common; cancel; simplen.
    unfold vssync_range.
    rewrite skipn_oob by simplen.
    rewrite app_nil_r.
    apply arrayN_unify.
    rewrite firstn_oob by simplen.
    rewrite map_fst_combine by simplen.
    auto.
  Qed.

  Lemma helper_ipack_length_eq: forall (vsl : list (list valu)) count items,
    eqlen (ipack items) vsl ->
    length items = count * items_per_val ->
    count = length vsl.
  Proof.
    intros.
    replace (length vsl) with (length (ipack items)) by simplen.
    rewrite ipack_length; simplen.
  Qed.

  Lemma helper_ipack_length_eq': forall (vsl : list (list valu)) count items,
    eqlen (ipack items) vsl ->
    length items = count * items_per_val ->
    length vsl = count.
  Proof.
    intros; apply eq_sym; eapply helper_ipack_length_eq; eauto.
  Qed.

  Local Hint Resolve helper_ipack_length_eq helper_ipack_length_eq'.
  Hint Rewrite ipack_length.

  Lemma vssync_range_pimpl : forall xp start items vsl m,
    length items = (length vsl) * items_per_val ->
    m <= (length vsl) ->
    arrayN (RAStart xp + start) (vssync_range (combine (ipack items) vsl) m) =p=>
    arrayN (RAStart xp + start) (combine (ipack items) (repeat nil m ++ skipn m vsl)).
  Proof.
      intros.
      unfold vssync_range, ipack.
      apply arrayN_unify.
      rewrite skipn_combine by simplen.
      rewrite <- combine_app.
      f_equal.
      rewrite <- firstn_map_comm.
      rewrite map_fst_combine by simplen.
      rewrite firstn_skipn; auto.
      simplen.
      lia.
  Qed.


  (** sync count blocks starting from start *)
  Definition sync_aligned T xp start count cs rx : prog T :=
    cs <- BUFCACHE.sync_range ((RAStart xp) + start) count cs;
    rx cs.

  Theorem sync_aligned_ok : forall xp start count cs,
    {< F d items,
    PRE            BUFCACHE.rep cs d * 
                   [[ length items = (count * items_per_val)%nat ]] *
                   [[ items_valid xp start items ]] *
                   [[ (F * array_rep xp start (Unsync items))%pred d ]]
    POST RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * array_rep xp start (Synced items))%pred d' ]]
    XCRASH  exists cs' d', BUFCACHE.rep cs' d' *
                   [[ (F * array_rep xp start (Unsync items))%pred d' ]]
    >} sync_aligned xp start count cs.
  Proof.
    unfold sync_aligned.
    prestep. norml.
    unfold unsync_array, rep_common in *; destruct_lifts.
    cancel.
    rewrite combine_length_eq by simplen.
    rewrite ipack_length; simplen.

    step.
    apply vssync_range_sync_array; eauto.

    eapply pimpl_trans; [ | eapply H1 ]; cancel.
    rewrite H.
    do 3 (xform_norm; cancel).
  Qed.

  Hint Extern 1 ({{_}} progseq (read_all _ _ _) _) => apply read_all_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_aligned _ _ _ _) _) => apply write_aligned_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync_aligned _ _ _ _) _) => apply sync_aligned_ok : prog.



End AsyncRecArray.

