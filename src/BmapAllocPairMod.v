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
Open Scope fscq.


Module BmapAllocPair <: SmallStepLang.

Inductive prog {R:Type} : Type :=
  | Alloc (rx:option (blockmapnum*blockmapoff)->prog)
  | Free (a:blockmapnum) (off:blockmapoff) (rx:unit->prog)
  | Return (v:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.
Definition State := blockmapnum -> blockmap.

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepAllocOK: forall d bn off rx,
    highest (fun bn' => exists off', BmapAllocOne.freebit (d bn') off') bn ->
    highest (BmapAllocOne.freebit (d bn)) off ->
    step (PS (Alloc rx) d)
         (PS (rx (Some (bn, off)))
             (setidx eq_blockmapnum_dec d bn
              (setidx eq_blockmapoff_dec (d bn) off InUse)))
  | StepAllocOut: forall d rx,
    (~exists bn off, BmapAllocOne.freebit (d bn) off) ->
    step (PS (Alloc rx) d)
         (PS (rx None) d)
  | StepFree: forall d bn off rx,
    step (PS (Free bn off rx) d)
         (PS (rx tt)
             (setidx eq_blockmapnum_dec d bn
              (setidx eq_blockmapoff_dec (d bn) off Avail))).
Definition Step := @step.

End BmapAllocPair.


Module BmapAllocPairToAllocOne <: Refines BmapAllocPair BmapAllocOne.

Obligation Tactic := Tactics.program_simpl; omega'.

Definition bmalloc_helper (R:Type) (bn:blockmapnum) (oa:option blockmapoff)
                          (rxok:(blockmapnum*blockmapoff)->BmapAllocOne.Prog R)
                          (rxfail:BmapAllocOne.Prog R) : BmapAllocOne.Prog R :=
  match oa with
  | None => rxfail
  | Some off => rxok (bn, off)
  end.

Program Fixpoint bmalloc (R:Type) (n:nat) (NOK:n<=NBlockMap)
                         (rx:option (blockmapnum*blockmapoff)->BmapAllocOne.Prog R) :=
  match n with
  | O => rx None
  | S x =>
    oa <- BmapAllocOne.Alloc x;
    bmalloc_helper R x oa
                   (fun x => rx (Some x))
                   (bmalloc R x _ rx)
  end.

Program Fixpoint Compile {R:Type} (p:BmapAllocPair.Prog R) : BmapAllocOne.Prog R :=
  match p with
  | BmapAllocPair.Alloc rx =>
    bmalloc R NBlockMap _ (fun x => Compile (rx x))
  | BmapAllocPair.Free bn off rx =>
    BmapAllocOne.Free bn off ;; (Compile (rx tt))
  | BmapAllocPair.Return r =>
    BmapAllocOne.Return r
  end.

Inductive statematch : BmapAllocPair.State -> BmapAllocOne.State -> Prop :=
  | Match: forall s,
    statematch s s.
Definition StateMatch := statematch.
Hint Constructors statematch.

Lemma bmalloc_fail:
  forall R n Hn rx d,
  (~exists bn off, BmapAllocOne.freebit (d bn) off) ->
  star (BmapAllocOne.Step R)
    (PS (bmalloc R n Hn rx) d)
    (PS (rx None) d).
Proof.
  induction n; intros.
  - apply star_refl.
  - eapply star_step; [apply BmapAllocOne.StepAllocOut|].
    + unfold not; intros. apply H; clear H. eexists (exist _ n _). apply H0.
    + cbv beta.
      fold bmalloc. unfold bmalloc_helper. apply IHn. auto.
Qed.

Lemma bmalloc_ok:
  forall R n Hn rx d bn off,
  highest_below (fun bn' => exists off', BmapAllocOne.freebit (d bn') off') n bn ->
  highest (BmapAllocOne.freebit (d bn)) off ->
  star (BmapAllocOne.Step R)
    (PS (bmalloc R n Hn rx) d)
    (PS (rx (Some (bn, off)))
        (setidx eq_blockmapnum_dec d bn
         (setidx eq_blockmapoff_dec (d bn) off InUse))).
Proof.
  induction n; intros.
  - destruct H. crush.
  - case_eq (eq_nat_dec (proj1_sig bn) n); intros.
    + eapply star_step; [apply BmapAllocOne.StepAllocOK|];
      subst; repeat rewrite exist_proj_sig.
      * eauto.
      * apply star_refl.
    + eapply star_step; [apply BmapAllocOne.StepAllocOut|];
      [ | apply IHn; auto; apply highest_below_next with (Hbound:=Hn); auto ];
      ( unfold not; intros;
        destruct H; Tactics.destruct_pairs; apply H3;
        eexists (exist _ n _);
        split; [omega'|eauto] ).
Qed.

Theorem FSim:
  forall R,
  forward_simulation (BmapAllocPair.Step R) (BmapAllocOne.Step R).
Proof.
  intros; exists (progmatch Compile statematch); intros.

  repeat match goal with
  | [ x: progmatch _ _ _ _ |- _ ] => inversion x; clear x; subst
  | [ x: statematch _ _ |- _ ] => inversion x; clear x; subst
  end.

  match goal with
  | [ x: BmapAllocPair.Step _ _ _ |- _ ] => inversion x; clear x; subst
  end.

  - (* Alloc Some *)
    econstructor; split.
    + apply bmalloc_ok; [ apply highest_below_bound | ]; eauto.
    + crush.

  - (* Alloc None *)
    econstructor; split.
    + apply bmalloc_fail; auto.
    + crush.

  - (* Free *)
    econstructor; split.
    + eapply star_step; [constructor|].
      apply star_refl.
    + crush.
Qed.

End BmapAllocPairToAllocOne.
