Require Import CpdtTactics.
Require Import FsTactics.
Require Import Util.
Require Import Smallstep.
Require Import Closures.
Require Import Tactics.
Require Import FsLayout.
Require Import Arith.
Require Import FunctionalExtensionality.
Require Import InodeLayout.
Open Scope fscq.


Module InodeAlloc <: SmallStepLang.

Inductive prog {R:Type} : Type :=
  | Read (a:inodenum) (rx:inode->prog)
  | Write (a:inodenum) (i:inode) (rx:unit->prog)
  | Alloc (rx:option inodenum->prog)
  | Free (a:inodenum) (rx:unit->prog)
  | Return (v:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.
Definition State := InodeStore.State.

Definition freeinode (s:State) (inum:inodenum) :=
  IFree (s inum) = Avail.

Program Definition initial_inode := Inode InUse 0 (fun _ => 0).
Program Definition free_inode := Inode Avail 0 (fun _ => 0).

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepRead: forall d a rx,
    step (PS (Read a rx) d)
         (PS (rx (d a)) d)
  | StepWrite: forall d a i rx,
    step (PS (Write a i rx) d)
         (PS (rx tt) (setidx eq_inodenum_dec d a i))
  | StepAllocOK: forall d inum rx,
    highest (freeinode d) inum ->
    step (PS (Alloc rx) d)
         (PS (rx (Some inum)) (setidx eq_inodenum_dec d inum initial_inode))
  | StepAllocOut: forall d rx,
    (~exists inum, freeinode d inum) ->
    step (PS (Alloc rx) d)
         (PS (rx None) d)
  | StepFree: forall d inum rx,
    step (PS (Free inum rx) d)
         (PS (rx tt) (setidx eq_inodenum_dec d inum free_inode)).
Definition Step := @step.

End InodeAlloc.


Module InodeAllocToStore <: Refines InodeAlloc InodeStore.

Obligation Tactic := Tactics.program_simpl; omega'.

Definition ifree (R:Type) (inum:inodenum) rx : InodeStore.Prog R :=
  InodeStore.Write inum InodeAlloc.free_inode;;
  rx.

Definition ialloc_helper (R:Type) (i:inode) (inum:inodenum)
                         (rxok:inodenum->InodeStore.Prog R)
                         (rxfail:InodeStore.Prog R) :
                         InodeStore.Prog R :=
  match IFree i with
  | InUse => rxfail
  | Avail => rxok inum
  end.

Program Fixpoint ialloc (R:Type) (n:nat) (NOK:n<=NInode)
                        (rx:option inodenum->InodeStore.Prog R) :
                        InodeStore.Prog R :=
  match n with
  | O => rx None
  | S x =>
    i <- InodeStore.Read x;
    ialloc_helper R i x
                  (fun inum =>
                   InodeStore.Write inum InodeAlloc.initial_inode;;
                   rx (Some inum))
                  (ialloc R x _ rx)
  end.

Program Fixpoint Compile {R:Type} (p:InodeAlloc.Prog R) : (InodeStore.Prog R) :=
  match p with
  | InodeAlloc.Read inum rx =>
    i <- InodeStore.Read inum ; Compile (rx i)
  | InodeAlloc.Write inum i rx =>
    InodeStore.Write inum i ;; Compile (rx tt)
  | InodeAlloc.Alloc rx =>
    ialloc R NInode _ (fun o => Compile (rx o))
  | InodeAlloc.Free inum rx =>
    ifree R inum (Compile (rx tt))
  | InodeAlloc.Return r =>
    InodeStore.Return r
  end.

Inductive statematch : InodeAlloc.State -> InodeStore.State -> Prop :=
  | Match: forall s,
    statematch s s.
Definition StateMatch := statematch.
Hint Constructors statematch.

Lemma ialloc_fail:
  forall R n Hn rx d,
  (~exists off, InodeAlloc.freeinode d off) ->
  star (InodeStore.Step R)
    (PS (ialloc R n Hn rx) d)
    (PS (rx None) d).
Proof.
  induction n; intros.
  - apply star_refl.
  - eapply star_step; [constructor|].
    fold ialloc. unfold ialloc_helper.
    match goal with
    | [ |- context[IFree (d ?n)] ] => 
      case_eq (IFree (d n)); intros; subst;
      [ apply IHn; auto
      | destruct H; exists n; crush ]
    end.
Qed.

Lemma ialloc_ok:
  forall R n Hn rx d inum,
  highest_below (InodeAlloc.freeinode d) n inum ->
  star (InodeStore.Step R)
    (PS (ialloc R n Hn rx) d)
    (PS (rx (Some inum))
        (setidx eq_inodenum_dec d inum InodeAlloc.initial_inode)).
Proof.
  induction n; intros.
  - destruct H. crush.
  - eapply star_step; [constructor|].
    fold ialloc. unfold ialloc_helper.
    match goal with
    | [ H: highest_below _ _ _ |- _ ] => inversion H
    end; Tactics.destruct_pairs.
    destruct (eq_nat_dec n (proj1_sig inum)).
    + generalize H0; subst; intros. repeat rewrite exist_proj_sig; crush.
      eapply star_step; [constructor|]. apply star_refl.
    + match goal with
      | [ |- context[IFree (d ?n)] ] =>
        case_eq (IFree (d n)); intros;
        [ apply IHn; apply highest_below_next with (Hbound:=Hn); crush
        | destruct H1; exists n; crush ]
      end.
Qed.

Theorem FSim:
  forall R,
  forward_simulation (InodeAlloc.Step R) (InodeStore.Step R).
Proof.
  intros; fsim_begin (@Compile R) statematch.

  - (* Read *)
    econstructor; split.
    + eapply star_step; [constructor|apply star_refl].
    + crush.

  - (* Write *)
    econstructor; split.
    + eapply star_step; [constructor|apply star_refl].
    + crush.

  - (* Alloc Some *)
    econstructor; split.
    + apply ialloc_ok.
      apply highest_below_bound. eauto.
    + crush.

  - (* Alloc None *)
    econstructor; split.
    + apply ialloc_fail; auto.
    + crush.

  - (* Free *)
    econstructor; split.
    + simpl. unfold ifree.
      eapply star_step; [constructor|].
      cbv beta.
      apply star_refl.
    + constructor; auto.
Qed.

End InodeAllocToStore.
