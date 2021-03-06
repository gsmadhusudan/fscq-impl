Require Import Prog ProgMonad.
Require Import Pred.
Require Import PredCrash.
Require Import Hoare.
Require Import Omega.
Require Import SepAuto.
Require Import Word.
Require Import Nomega.
Require Import NArith.
Require Import FunctionalExtensionality.
Require Import List.
Require Import AsyncDisk.
Require Import Hashmap.
Require Import ListUtils.

Set Implicit Arguments.

(** * Some helpful [prog] combinators and proofs *)

Lemma sync_invariant_possible_sync : forall (F: rawpred) (m: rawdisk),
    F m ->
    sync_invariant F ->
    possible_sync m =p=> F.
Proof.
  unfold sync_invariant; eauto.
Qed.

Hint Resolve sync_invariant_possible_sync.

Theorem read_ok:
  forall (a:addr),
  {< v,
  PRE        a |+> v
  POST RET:r a |+> v * [[ r = (fst v) ]]
  CRASH      a |+> v
  >} Read a.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec.
    eapply H4; eauto.
    pred_apply; cancel.
    eauto.
    eapply ptsto_subset_valid' in H; deex.
    unfold possible_sync in *.
    destruct (H10 a).
    intuition congruence.
    repeat deex; simpl in *.
    congruence.
  - exfalso.
    apply sep_star_comm in H. eapply ptsto_subset_valid in H. repeat deex.
    congruence.
  - right. repeat eexists; intuition eauto.
    eapply H3.
    pred_apply; cancel.
Qed.

Hint Extern 1 ({{_}} Bind (Read _) _) => apply read_ok : prog.

Theorem write_ok:
  forall (a:addr) (v:valu),
  {< v0,
  PRE        a |+> v0
  POST RET:r a |+> (v, vsmerge v0)
  CRASH      a |+> v0
  >} Write a v.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec.
    eapply H4; eauto.
    eapply pimpl_trans.
    reflexivity.
    2: eapply ptsto_subset_upd.
    cancel.
    eapply sync_invariant_possible_sync; eauto.
    specialize (H10 a).
    apply ptsto_subset_valid' in H; repeat deex.
    congruence.
    simpl in *.
    rewrite H0 in H2; inversion H2; subst.
    rewrite H14 in H; inversion H; subst.
    unfold vsmerge; simpl.
    eapply incl_cons. eapply in_eq.
    eapply incl_tl. eapply incl_tran. eauto. eauto.
  - exfalso.
    apply sep_star_comm in H. eapply ptsto_subset_valid in H. repeat deex.
    congruence.
  - right. repeat eexists; intuition eauto.
    eapply H3.
    pred_apply; cancel.
Qed.

Hint Extern 1 ({{_}} Bind (Write _ _) _) => apply write_ok : prog.

Theorem sync_ok:
  {!< F,
  PRE        F * [[ sync_invariant F ]]
  POST RET:r sync_xform F
  CRASH      F
  >!} Sync.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec.
    eapply H4; eauto.

    eapply pimpl_apply; [ | eapply sync_xform_pred_apply; pred_apply; reflexivity ].
    cancel.
    apply sync_xform_pimpl; eauto.
Qed.

Hint Extern 1 ({{_}} Bind Sync _) => apply sync_ok : prog.
Hint Extern 1 ({{_}} Bind (@Sync _) _) => apply sync_ok : prog.

Theorem trim_ok:
  forall (a:addr),
  {< v0,
  PRE        a |+> v0
  POST RET:r a |+>?
  CRASH      a |+>?
  >} Trim a.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - eapply H4; eauto.
    apply sep_star_comm in H as H'. apply ptsto_subset_valid in H'; repeat deex.
    apply sep_star_comm in H as H'. rewrite ptsto_subset_pimpl_ptsto_ex in H'. destruct_lift H'.
    apply ptsto_valid in H0.
    rewrite H0 in H1; inversion H1; subst.
    inv_exec.
    destruct vs'.
    eapply pimpl_trans.
    reflexivity.
    2: eapply ptsto_subset_upd.
    cancel.
    eapply sync_invariant_possible_sync; eauto.
    eapply incl_refl.
Qed.

Hint Extern 1 ({{_}} Bind (Trim _) _) => apply trim_ok : prog.

Theorem hash_ok:
  forall sz (buf : word sz),
  {< (_: unit),
  PRE:hm    emp
  POST:hm'
    RET:h   emp *
              [[ hash_safe hm h buf ]] *
              [[ h = hash_fwd buf ]] *
              [[ hm' = upd_hashmap' hm h buf ]]
  CRASH:hm' emp * [[ hm' = hm ]]
  >} Hash buf.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec.
    eapply H4; eauto.
    pred_apply; cancel.
    eauto.
Qed.

Hint Extern 1 ({{_}} Bind (Hash _) _) => apply hash_ok : prog.

(** program equivalence and monad laws *)

Definition If_ T P Q (b : {P} + {Q}) (p1 p2 : prog T) :=
  if b then p1 else p2.

Theorem if_ok:
  forall T T' P Q (b : {P}+{Q}) (p1 p2 : prog T) (p': T -> prog T'),
  {{ fun hm done crash => exists pre, pre
   * [[ {{ fun hm' done' crash' => pre * [[P]] * [[ hm = hm' ]] * [[ done' = done ]] * [[ crash' = crash ]] }} Bind p1 p' ]]
   * [[ {{ fun hm' done' crash' => pre * [[Q]] * [[ hm = hm' ]] * [[ done' = done ]] * [[ crash' = crash ]] }} Bind p2 p' ]]
  }} Bind (If_ b p1 p2) p'.
Proof.
  unfold corr2, corr2, exis; intros; repeat deex.
  repeat ( apply sep_star_lift2and in H; destruct H ).
  destruct b.
  - eapply H2; eauto.
    eapply pimpl_apply; [|apply H].
    cancel.
  - eapply H1; eauto.
    eapply pimpl_apply; [|apply H].
    cancel.
Qed.

(* helper to use If with an option *)
Definition is_some A (a: option A) : {a <> None} + {a = None}.
Proof.
  destruct a; left + right; congruence.
Defined.

Hint Extern 1 ({{_}} Bind (If_ _ _ _) _) => apply if_ok : prog.
Notation "'If' b { p1 } 'else' { p2 }" := (If_ b p1 p2) (at level 9, b at level 0).

Record For_args (L : Type) := {
  For_args_i : waddr;
  For_args_n : waddr;
  For_args_l : L
}.

Theorem for_args_wf: forall L,
  well_founded (fun a b => wlt a.(@For_args_n L) b.(@For_args_n L)).
Proof.
  intros.
  apply well_founded_lt_compat with (f:=fun a => wordToNat (a.(For_args_n))).
  intros.
  apply wlt_lt; auto.
Qed.

Lemma word_minus_1 : forall sz (w: word sz),
    w <> $ 0 ->
    (w ^- $1 < w)%word.
Proof.
  intros.
  apply weq_minus1_wlt; auto.
Qed.

Definition For_ (L : Type) (G : Type) (f : waddr -> L -> prog L)
                (i n : waddr)
                (nocrash : G -> waddr -> L -> hashmap -> rawpred)
                (crashed : G -> hashmap -> rawpred)
                (l : L) : prog L.
Proof.
  refine (Fix (@for_args_wf L) (fun _ => prog L)
          (fun args For_ => _)
          {| For_args_i := i; For_args_n := n; For_args_l := l |}).
  clear i n l.
  destruct args.
  refine (if weq For_args_n0 $0 then Ret For_args_l0 else _).
  refine (l' <- (f For_args_i0 For_args_l0); _).
  refine (For_ {| For_args_i := For_args_i0 ^+ $1;
                  For_args_n := For_args_n0 ^- $1;
                  For_args_l := l' |} _).

  simpl.
  apply word_minus_1; auto.
Defined.

Lemma For_step: forall L G (f: waddr -> L -> prog L) i n l nocrash crashed,
  @For_ L G f i n nocrash crashed l =
    if weq n $0
    then Ret l
    else l' <- (f i l);
         @For_ L G f
             (i ^+ $1)
             (n ^- $1)
             nocrash crashed l'.
Proof.
  intros.
  unfold For_.
  rewrite Fix_eq.
  simpl.

  destruct (weq n $0); f_equal.

  intros.

  match goal with
  | [ |- context[match ?x with _ => _ end] ] =>
     destruct x; f_equal
  end.

  match goal with
  | [ |- context[match ?x with _ => _ end] ] =>
     destruct x; try reflexivity
  end.

  apply f_equal.
  apply functional_extensionality; auto.
Qed.

Theorem for_ok':
  forall T (n i : waddr)
         (L : Type) (G : Type)
         (f: waddr -> L -> prog L) (rx: L -> prog T)
         (nocrash : G -> waddr -> L -> hashmap -> rawpred)
         (crashed : G -> hashmap -> rawpred)
         (li : L),
  {{ fun hm done crash => exists F (g:G) hm', F * nocrash g i li hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      (i <= m)%word ->
      (m < n ^+ i)%word ->
      (forall lSm,
       {{ fun hm'' done' crash' => F * nocrash g (m ^+ $1) lSm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun hm'' done' crash' => F * nocrash g m lm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]]
   * [[forall lfinal,
       {{ fun hm'' done' crash' => F * nocrash g (n ^+ i) lfinal hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[wordToNat i + wordToNat n = wordToNat (i ^+ n)]]
   * [[forall hm'',
        F * crashed g hm'' * [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} Bind (For_ f i n nocrash crashed li) rx.
Proof.
  intro T.
  wlt_ind.

  intros.
  apply corr2_exists; intros.
  apply corr2_exists; intros.
  apply corr2_exists; intros.
  case_eq (weq x $0); intros; subst.

  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + unfold pimpl, lift; intros.
      rewrite For_step.
      eapply pimpl_ok2.
      simpl; monad_simpl; eauto.
      intros.
      apply pimpl_refl.
    + fold (wzero addrlen). ring_simplify (wzero addrlen ^+ i). cancel.

  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + assert (wordToNat x <> 0).
      unfold not in *; intros; apply n.
      rewrite <- H6; rewrite natToWord_wordToNat; auto.

      unfold pimpl, lift; intros.
      rewrite For_step.
      rewrite H0.
      monad_simpl.
      apply H4.

      apply eq_le; auto.
      rewrite wplus_comm.
      apply lt_wlt.
      omega.

      intros.
      eapply pimpl_ok2.
      apply H.

      apply word_minus_1; auto.

      intros.
      apply pimpl_exists_r; exists a.
      apply pimpl_exists_r; exists a0.
      apply pimpl_exists_r; exists a1.
      ring_simplify (i ^+ $1 ^+ (x ^- $1)).
      ring_simplify (x ^- $1 ^+ (i ^+ $1)).
      cancel.

      subst; apply H4; eauto.
      intros; apply H9; clear H9.
      apply wlt_lt in H12.
      unfold wlt.
      repeat rewrite wordToN_nat.
      apply Nlt_in.
      repeat rewrite Nat2N.id.
      rewrite wplus_alt.
      unfold wplusN, wordBinN.
      simpl (wordToNat $1).
      rewrite wordToNat_natToWord_idempotent'.
      omega.
      eapply Nat.le_lt_trans; [| apply (wordToNat_bound (i ^+ x)) ]; omega.

      rewrite wminus_Alt.
      rewrite wminus_Alt2.
      repeat rewrite wplus_alt.
      repeat unfold wplusN, wordBinN.

      simpl (wordToNat $1).
      repeat rewrite wordToNat_natToWord_idempotent'.
      omega.
      rewrite H2; apply wordToNat_bound.

      eapply Nat.le_lt_trans; [| apply (wordToNat_bound x) ]; omega.
      eapply Nat.le_lt_trans; [| apply (wordToNat_bound (i ^+ x)) ]; omega.

      unfold not; intros; apply H6.
      assert (wordToNat x < 1); [| omega ].
      apply wlt_lt in H9; simpl in H9; auto.
    + cancel.
Qed.

Theorem for_ok:
  forall T (n : waddr)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> waddr -> L -> hashmap -> rawpred)
         (crashed : G -> hashmap -> rawpred)
         (li : L),
  {{ fun hm done crash => exists F (g:G) hm', F * nocrash g $0 li hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      (m < n)%word ->
      (forall lSm,
       {{ fun hm'' done' crash' => F * nocrash g (m ^+ $1) lSm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun hm'' done' crash' => F * nocrash g m lm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]]
   * [[forall lfinal,
       {{ fun hm'' done' crash' => F * nocrash g n lfinal hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' * [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} Bind (For_ f $0 n nocrash crashed li) rx.
Proof.
  intros.
  eapply pimpl_ok2.
  apply for_ok'.
  fold (wzero addrlen); ring_simplify (wzero addrlen ^+ n).
  simpl (wordToNat (wzero addrlen)); replace (0 + wordToNat n) with (wordToNat n) by omega.
  ring_simplify (n ^+ wzero addrlen).
  cancel.
  cancel.
Qed.

Hint Extern 1 ({{_}} Bind (For_ _ _ _ _ _ _) _) => apply for_ok : prog.

Notation "'For' i < n 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        $0 n
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun hm => nocrash%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'For' i < n 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        $0 n
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun hm => nocrash%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Fixpoint ForN_  (L : Type) (G : Type) (f : nat -> L -> prog L)
                (i n : nat)
                (nocrash : G -> nat -> L -> hashmap -> rawpred)
                (crashed : G -> hashmap -> rawpred)
                (l : L) : prog L :=
  match n with
  | 0 =>   Ret l
  | S m => l' <- f i l;  ForN_ f (S i) m nocrash crashed l'
  end.


Theorem forN_ok':
  forall T (n i : nat)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> nat -> L -> hashmap -> pred)
         (crashed : G -> hashmap -> pred)
         (li : L),
  {{ fun hm done crash => exists F (g:G) hm', F * nocrash g i li hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      i <= m ->
      m < n + i ->
      (forall lSm,
       {{ fun hm'' done' crash' => F * nocrash g (S m) lSm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun hm'' done' crash' => F * nocrash g m lm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]]
   * [[forall lfinal,
       {{ fun hm'' done' crash' => F * nocrash g (n + i) lfinal hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' *
        [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} Bind (ForN_ f i n nocrash crashed li) rx.
Proof.
  induction n; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros.
  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2; monad_simpl; eauto.
      intros.
      apply pimpl_refl.
    + cancel.
  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2; monad_simpl.
      apply H1. omega. omega.
      intros.
      eapply pimpl_ok2.
      eapply IHn.
      cancel.
      cancel.
      eapply pimpl_ok2.
      apply H0.
      intros.
      cancel.
      replace (n + S i) with (S (n + i)) by omega.
      cancel.
      intros.
      apply pimpl_refl.
    + cancel.
Qed.

Theorem forN_ok:
  forall (n : nat)
         T (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> nat -> L -> hashmap -> pred)
         (crashed : G -> hashmap -> pred)
         (li : L),
  {{ fun hm done crash => exists F (g:G) hm', F * nocrash g 0 li hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      m < n ->
      (forall lSm,
       {{ fun hm'' done' crash' => F * nocrash g (S m) lSm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun hm'' done' crash' => F * nocrash g m lm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]]
   * [[forall lfinal,
       {{ fun hm'' done' crash' => F * nocrash g n lfinal hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' *
        [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} Bind (ForN_ f 0 n nocrash crashed li) rx.
Proof.
  intros.
  eapply pimpl_ok2.
  apply forN_ok'.
  cancel.
  cancel.
  eapply pimpl_ok2.
  eauto.
  cancel.
  replace (n + 0) with n by omega; auto.
Qed.

Hint Extern 1 ({{_}} Bind (ForN_ _ _ _ _ _ _) _) => apply forN_ok : prog.

Notation "'ForN' i < n 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForN_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        0 n
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun hm => nocrash%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForN' i < n 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForN_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        0 n
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun hm => nocrash%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).


Fixpoint ForEach_ (ITEM : Type)
                (L : Type) (G : Type) (f : ITEM -> L -> prog L)
                (lst : list ITEM)
                (nocrash : G -> list ITEM -> L -> hashmap -> rawpred)
                (crashed : G -> hashmap -> rawpred)
                (l : L) : prog L :=
  match lst with
  | nil => Ret l
  | elem :: lst' =>
    l' <- f elem l;
    ForEach_ f lst' nocrash crashed l'
  end.

Theorem foreach_ok:
  forall T ITEM (lst : list ITEM)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> list ITEM -> L -> hashmap -> pred)
         (crashed : G -> hashmap -> pred)
         (li : L),
  {{ fun hm done crash => exists F (g:G) hm', F * nocrash g lst li hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall elem lst' lm rxm,
      (forall lSm,
       {{ fun hm'' done' crash' => F * nocrash g lst' lSm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]]  * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun hm'' done' crash' => F * nocrash g (elem :: lst') lm hm'' *
         [[ exists l, hashmap_subset l hm' hm'' ]] *
         [[ exists prefix, prefix ++ elem :: lst' = lst ]] *
         [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f elem lm) rxm]]
   * [[forall lfinal,
       {{ fun hm'' done' crash' => F * nocrash g nil lfinal hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' * [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} Bind (ForEach_ f lst nocrash crashed li) rx.
Proof.
  intros ITEM.
  induction lst; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros.

  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2; monad_simpl; eauto.
      intros.
      apply pimpl_refl.
    + cancel.
  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2; monad_simpl.
      apply H1.
      intros.
      eapply pimpl_ok2.
      apply IHlst.
      cancel.
      eassign lst.
      cancel.
      eapply pimpl_ok2.
      apply H1.
      intros.
      eapply pimpl_ok2.
      apply H2.
      cancel.
      cancel.
      exists (a :: prefix); auto.

      intros.
      apply pimpl_refl.
    + cancel.
      exists nil; auto.
Qed.

Hint Extern 1 ({{_}} Bind (ForEach_ _ _ _ _ _) _) => apply foreach_ok : prog.

Notation "'ForEach' elem rest lst 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForEach_ (fun elem => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) => body)) ..)))
        lst
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun rest => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
         fun hm => nocrash%pred)) ..))  )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, elem at level 0, rest at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForEach' elem rest lst 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForEach_ (fun elem => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) => body)) ..)))
        lst
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun rest => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
         fun hm => nocrash%pred)) ..))  )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, elem at level 0, rest at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

(* TODO: need a good spec for this. Probably want a predicate
describing early breaks, so that we can guarantee something if the
function terminates without breaking (otherwise the spec would equally
apply to a loop that didn't do anything) *)
Fixpoint ForNBreak_  (L : Type) (G : Type) (f : nat -> L -> prog (L+L))
                (i n : nat)
                (nocrash : G -> nat -> L -> hashmap -> rawpred)
                (crashed : G -> hashmap -> rawpred)
                (l : L) : prog L :=
  match n with
  | 0 =>   Ret l
  | S m => l' <- f i l;
            match l' with
            | inl l' => ForNBreak_ f (S i) m nocrash crashed l'
            | inr l' => Ret l'
            end
  end.

Definition Continue L (l:L) : L + L := inl l.
Definition Break L (l:L) : L + L := inr l.