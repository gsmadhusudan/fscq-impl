Require Import CpdtTactics.
Require Import FsTactics.
Require Import Util.
Require Import Smallstep.
Require Import Closures.
Require Import Tactics.
Require Import FsLayout.
Require Import Arith.
Require Import FunctionalExtensionality.
Require Import BmapLayout.
Require Import BmapAllocOneMod.
Require Import BmapAllocPairMod.
Require Import NPeano.
Open Scope fscq.


Module BmapAlloc <: SmallStepLang.

Inductive prog {R:Type} : Type :=
  | Alloc (rx:option BlocksPartDisk.addr->prog)
  | Free (a:BlocksPartDisk.addr) (rx:unit->prog)
  | Return (v:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.
Definition State := BlocksPartDisk.addr -> AllocState.

Definition freebit (bm:State) (off:BlocksPartDisk.addr) :=
  bm off = Avail.

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepAllocOK: forall d n rx,
    highest (freebit d) n ->
    step (PS (Alloc rx) d)
         (PS (rx (Some n)) (setidx BlocksPartDisk.eq_addr_dec d n InUse))
  | StepAllocOut: forall d rx,
    (~exists n, freebit d n) ->
    step (PS (Alloc rx) d)
         (PS (rx None) d)
  | StepFree: forall d n rx,
    step (PS (Free n rx) d)
         (PS (rx tt) (setidx BlocksPartDisk.eq_addr_dec d n Avail)).
Definition Step := @step.

End BmapAlloc.


Module BmapAllocToAllocPair <: Refines BmapAlloc BmapAllocPair.

Obligation Tactic := idtac.

Program Definition pair2addr (bn:blockmapnum) (off:blockmapoff) : BlocksPartDisk.addr :=
  bn * SizeBlock + off.
Solve Obligations using Tactics.program_simpl; omega'.

Program Definition addr2bn (n:BlocksPartDisk.addr) : blockmapnum :=
  n / SizeBlock.
Solve Obligations using intros; apply Nat.div_lt_upper_bound; omega'.

Program Definition addr2off (n:BlocksPartDisk.addr) : blockmapoff :=
  n mod SizeBlock.
Solve Obligations using intros; apply Nat.mod_upper_bound; omega'.

Opaque modulo div.
Lemma eq_bnoff_dec:
  forall a b,
  {a=b} +
  {a<>b /\ addr2bn a<>addr2bn b} +
  {a<>b /\ addr2bn a=addr2bn b /\ addr2off a <> addr2off b}.
Proof.
  intros.
  destruct (eq_nat_dec (proj1_sig a) (proj1_sig b)) as [|Hab];
    [ left; left; apply sig_pi; crush | ].
  destruct (eq_nat_dec (proj1_sig (addr2bn a)) (proj1_sig (addr2bn b))) as [HBab|];
    [ | left; right; split; apply sig_pi_ne; auto ].
  right; split; [ apply sig_pi_ne; crush | ].
  split; [ apply sig_pi; crush | ].
  unfold not in *; intro HOab; apply Hab; clear Hab.
  destruct a as [a]; destruct b as [b].
  unfold addr2off in *; unfold addr2bn in *; unfold proj1_sig in *.
  inversion HOab as [HOab']; clear HOab.
  rewrite (Nat.div_mod a SizeBlock); [|omega'].
  rewrite HBab. rewrite HOab'.
  rewrite <- (Nat.div_mod b SizeBlock); [|omega'].
  reflexivity.
Qed.

Lemma addr2pair2addr:
  forall n,
  pair2addr (addr2bn n) (addr2off n) = n.
Proof.
  intros; unfold addr2bn; unfold addr2off; unfold pair2addr; apply sig_pi; simpl.
  rewrite Mult.mult_comm.
  rewrite <- Nat.div_mod; omega'.
Qed.
Hint Rewrite addr2pair2addr.

Lemma pair2addr2bn:
  forall bn off,
  addr2bn (pair2addr bn off) = bn.
Proof.
  intros; unfold addr2bn; unfold pair2addr; apply sig_pi; simpl.
  rewrite Nat.div_add_l; [|omega'].
  rewrite Nat.div_small; omega'.
Qed.
Hint Rewrite pair2addr2bn.

Lemma pair2addr2off:
  forall bn off,
  addr2off (pair2addr bn off) = off.
Proof.
  intros; unfold addr2bn; unfold pair2addr; apply sig_pi; simpl.
  rewrite Plus.plus_comm.
  rewrite Nat.mod_add; [|omega'].
  rewrite Nat.mod_small; omega'.
Qed.
Hint Rewrite pair2addr2off.
Ltac rewrite_bn_off := repeat rewrite addr2pair2addr in *;
                       repeat rewrite pair2addr2bn in *;
                       repeat rewrite pair2addr2off in *.

Fixpoint Compile {R:Type} (p:BmapAlloc.Prog R) : BmapAllocPair.Prog R :=
  match p with
  | BmapAlloc.Alloc rx =>
    x <- BmapAllocPair.Alloc;
    match x with
    | None => Compile (rx None)
    | Some (bn,off) => Compile (rx (Some (pair2addr bn off)))
    end
  | BmapAlloc.Free n rx =>
    BmapAllocPair.Free (addr2bn n) (addr2off n) ;; Compile (rx tt)
  | BmapAlloc.Return r =>
    BmapAllocPair.Return r
  end.

Inductive statematch : BmapAlloc.State -> BmapAllocPair.State -> Prop :=
  | Match: forall fs s
    (M: forall bn off, fs (pair2addr bn off) = s bn off),
    statematch fs s.
Definition StateMatch := statematch.
Hint Constructors statematch.

Ltac auto_omega' := auto; omega'.

Lemma highest_bn:
  forall fs s n,
  statematch fs s ->
  highest (BmapAlloc.freebit fs) n ->
  highest (fun bn => exists off, BmapAllocOne.freebit (s bn) off) (addr2bn n).
Proof.
  unfold BmapAllocOne.freebit; unfold BmapAlloc.freebit; intros.
  invert_rel (@highest (fun x => x < BlocksPartSize.Size)).
  invert_rel statematch; subst.
  split; [ exists (addr2off n); rewrite <- M; rewrite_bn_off; auto | ].
  unfold not; intros; apply H2; clear H2.
  destruct H as [bn H]. destruct H as [Hbn H]. destruct H as [off Havail].
  exists (pair2addr bn off); split.
  - rewrite <- (addr2pair2addr n). unfold pair2addr. omega'.
  - crush.
Qed.

Lemma highest_off:
  forall fs s n,
  statematch fs s ->
  highest (BmapAlloc.freebit fs) n ->
  highest (BmapAllocOne.freebit (s (addr2bn n))) (addr2off n).
Proof.
  unfold BmapAllocOne.freebit; unfold BmapAlloc.freebit; intros.
  invert_rel (@highest (fun x => x < BlocksPartSize.Size)).
  invert_rel statematch; subst.
  split; [ rewrite <- M; rewrite_bn_off; auto | ].
  unfold not; intros; apply H2; clear H2.
  destruct H as [off H]. destruct H as [Hoff Havail].
  exists (pair2addr (addr2bn n) off); split.
  - rewrite <- (addr2pair2addr n). rewrite pair2addr2bn. unfold pair2addr. omega'.
  - crush.
Qed.

Theorem FSim:
  forall R,
  forward_simulation (BmapAlloc.Step R) (BmapAllocPair.Step R).
Proof.
  intros; fsim_begin (@Compile R) statematch.

  - (* Alloc Some *)
    eexists; split.
    + eapply star_step; [apply BmapAllocPair.StepAllocOK|].
      * eapply highest_bn; eauto.
      * eapply highest_off; eauto.
      * fold (@Compile R).
        apply star_refl.
    + constructor; rewrite_bn_off; [auto|constructor]; intros.
      destruct (eq_bnoff_dec n (pair2addr bn off)) as [H'|]; [destruct H'|];
      Tactics.destruct_pairs;
      subst; rewrite_bn_off; repeat resolve_setidx auto_omega'; auto.

  - (* Alloc None *)
    eexists; split.
    + eapply star_step; [apply BmapAllocPair.StepAllocOut|apply star_refl].
      unfold not; intros. apply H3; clear H3.
      unfold BmapAllocOne.freebit in *.
      unfold BmapAlloc.freebit in *.
      destruct H. destruct H.
      eexists. rewrite M0. eauto.
    + crush.

  - (* Free *)
    eexists; split.
    + eapply star_step; [constructor|apply star_refl].
    + constructor; [auto|constructor]; intros.
      destruct (eq_bnoff_dec n (pair2addr bn off)) as [H'|]; [destruct H'|];
      Tactics.destruct_pairs;
      subst; rewrite_bn_off; repeat resolve_setidx auto_omega'; auto.
Qed.

End BmapAllocToAllocPair.
