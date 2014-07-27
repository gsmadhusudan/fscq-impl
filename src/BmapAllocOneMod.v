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
Open Scope fscq.


Definition highest {SigP:nat->Prop} (P:sig SigP->Prop) (a:sig SigP) :=
  P a /\ ~exists a', proj1_sig a < proj1_sig a' /\ P a'.
Definition highest_below {SigP:nat->Prop} (P:sig SigP->Prop) (bound:nat) (a:sig SigP) :=
  @highest SigP (fun x => P x /\ proj1_sig x < bound) a.

Lemma highest_below_next:
  forall SigBound P bound a (Hbound: bound<SigBound),
  @highest_below (fun x => x < SigBound) P (S bound) a ->
  ~P (exist _ bound Hbound) ->
  @highest_below (fun x => x < SigBound) P bound a.
Proof.
  intros. destruct H. Tactics.destruct_pairs.
  destruct (eq_nat_dec bound (proj1_sig a)); subst.
  - destruct H0. rewrite exist_proj_sig. auto.
  - split; [split|]; [ auto | omega' | ].
    unfold not; intros. apply H1.
    destruct H3. exists x. crush.
Qed.

Lemma highest_below_bound:
  forall bound P a,
  @highest (fun x => x < bound) P a ->
  @highest_below (fun x => x < bound) P bound a.
Proof.
  intros. destruct H.
  split; [split|]. auto. omega'.
  unfold not; intros. destruct H0. destruct H1. exists x. crush.
Qed.

Definition eq_blockmapoff_dec (a b:blockmapoff) : {a=b}+{a<>b}.
  refine (if eq_nat_dec (proj1_sig a) (proj1_sig b) then _ else _).
  - left. apply sig_pi. auto.
  - right. apply sig_pi_ne. auto.
Defined.


Module BmapAllocOne <: SmallStepLang.

Inductive prog {R:Type} : Type :=
  | Alloc (a:blockmapnum) (rx:option blockmapoff->prog)
  | Free (a:blockmapnum) (off:blockmapoff) (rx:unit->prog)
  | Return (v:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.
Definition State := blockmapnum -> blockmap.

Definition freebit (bm:blockmap) (off:blockmapoff) :=
  bm off = Avail.

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepAllocOK: forall d a off rx,
    highest (freebit (d a)) off ->
    step (PS (Alloc a rx) d)
         (PS (rx (Some off)) (setidx eq_blockmapnum_dec d a
                              (setidx eq_blockmapoff_dec (d a) off InUse)))
  | StepAllocOut: forall d a rx,
    (~exists off, freebit (d a) off) ->
    step (PS (Alloc a rx) d)
         (PS (rx None) d)
  | StepFree: forall d a off rx,
    step (PS (Free a off rx) d)
         (PS (rx tt) (setidx eq_blockmapnum_dec d a
                      (setidx eq_blockmapoff_dec (d a) off Avail))).
Definition Step := @step.

End BmapAllocOne.


Module BmapAllocOneToStore <: Refines BmapAllocOne BmapStore.

Obligation Tactic := Tactics.program_simpl; omega'.

Definition bmfree (R:Type) (a:blockmapnum) (off:blockmapoff) rx :
                  BmapStore.Prog R :=
  bm <- BmapStore.Read a;
  BmapStore.Write a (setidx eq_blockmapoff_dec bm off Avail);;
  rx.

Definition bmalloc_helper (R:Type) (bm:blockmap) (off:blockmapoff)
                          (rxok:blockmapoff->BmapStore.Prog R)
                          (rxfail:BmapStore.Prog R) :
                          BmapStore.Prog R :=
  match bm off with
  | InUse => rxfail
  | Avail => rxok off
  end.

Program Fixpoint bmalloc (R:Type) (a:blockmapnum)
                         (n:nat) (NOK:n<=SizeBlock)
                         (rx:option blockmapoff->BmapStore.Prog R) :
                         BmapStore.Prog R :=
  match n with
  | O => rx None
  | S x =>
    bm <- BmapStore.Read a;
    bmalloc_helper R bm x
                   (fun off =>
                    BmapStore.Write a (setidx eq_blockmapoff_dec bm off InUse);;
                    rx (Some off))
                   (bmalloc R a x _ rx)
  end.

Program Fixpoint Compile {R:Type} (p:BmapAllocOne.Prog R) : (BmapStore.Prog R) :=
  match p with
  | BmapAllocOne.Alloc a rx =>
    bmalloc R a SizeBlock _ (fun ob => Compile (rx ob))
  | BmapAllocOne.Free a off rx =>
    bmfree R a off (Compile (rx tt))
  | BmapAllocOne.Return r =>
    BmapStore.Return r
  end.

Inductive statematch : BmapAllocOne.State -> BmapStore.State -> Prop :=
  | Match: forall s,
    statematch s s.
Definition StateMatch := statematch.
Hint Constructors statematch.

Lemma bmalloc_fail:
  forall R n Hn a rx d,
  (~exists off, BmapAllocOne.freebit (d a) off) ->
  star (BmapStore.Step R)
    (PS (bmalloc R a n Hn rx) d)
    (PS (rx None) d).
Proof.
  induction n; intros.
  - apply star_refl.
  - eapply star_step; [constructor|].
    fold bmalloc. unfold bmalloc_helper.
    match goal with
    | [ |- context[d a ?n] ] =>
      case_eq (d a n); intros; subst;
      [ apply IHn; auto
      | destruct H; exists n; crush ]
    end.
Qed.

Lemma bmalloc_ok:
  forall R n Hn a rx d off,
  highest_below (BmapAllocOne.freebit (d a)) n off ->
  star (BmapStore.Step R)
    (PS (bmalloc R a n Hn rx) d)
    (PS (rx (Some off))
        (setidx eq_blockmapnum_dec d a
         (setidx eq_blockmapoff_dec (d a) off InUse))).
Proof.
  induction n; intros.
  - destruct H. crush.
  - eapply star_step; [constructor|].
    fold bmalloc. unfold bmalloc_helper.
    match goal with
    | [ H: highest_below _ _ _ |- _ ] => inversion H
    end; Tactics.destruct_pairs.
    destruct (eq_nat_dec n (proj1_sig off)).
    + generalize H0; subst; intros. repeat rewrite exist_proj_sig; crush.
      eapply star_step; [constructor|]. apply star_refl.
    + match goal with
      | [ |- context[d a ?n] ] =>
        case_eq (d a n); intros;
        [ apply IHn; apply highest_below_next with (Hbound:=Hn); crush
        | destruct H1; exists n; crush ]
      end.
Qed.

Theorem FSim:
  forall R,
  forward_simulation (BmapAllocOne.Step R) (BmapStore.Step R).
Proof.
  intros; fsim_begin (@Compile R) statematch.

  - (* Alloc Some *)
    econstructor; split.
    + apply bmalloc_ok.
      apply highest_below_bound. eauto.
    + crush.

  - (* Alloc None *)
    econstructor; split.
    + apply bmalloc_fail; auto.
    + crush.

  - (* Free *)
    econstructor; split.
    + simpl. unfold bmfree.
      eapply star_step; [constructor|].
      eapply star_step; [constructor|].
      cbv beta.
      apply star_refl.
    + constructor; auto.
Qed.

End BmapAllocOneToStore.
