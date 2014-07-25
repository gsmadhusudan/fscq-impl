Require Import CpdtTactics.
Require Import FsTactics.
Require Import Closures.
Require Import Util.
Require Import Arith.
Require Import Smallstep.
Require Import DiskMod.
Open Scope fscq.


Module Pair <: SmallStepLang.

Inductive prog {R:Type} : Type :=
  | Read (n:nat) (rx:(nat*nat)->prog)
  | Write (n:nat) (p:nat*nat) (rx:unit->prog)
  | Return (v:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.
Definition State := nat -> (nat*nat).

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepRead: forall d b rx,
    step (PS (Read b rx) d)
         (PS (rx (d b)) d)
  | StepWrite: forall d b v rx,
    step (PS (Write b v rx) d)
         (PS (rx tt) (setidx eq_nat_dec d b v)).
Definition Step := @step.

End Pair.


Module PairToDisk <: Refines Pair Disk.

Fixpoint Compile {R:Type} (p:@Pair.Prog R) : (Disk.Prog R) :=
  match p with
  | Pair.Read n rx =>
    a <- Disk.Read (2*n) ; b <- Disk.Read (2*n+1) ; Compile (rx (a, b))
  | Pair.Write n v rx =>
    let (a,b) := v in Disk.Write (2*n) a ;; Disk.Write (2*n+1) b ;; Compile (rx tt)
  | Pair.Return r =>
    Disk.Return r
  end.

Inductive statematch : Pair.State -> Disk.State -> Prop :=
  | Match: forall p d
    (M: forall n, p n = (d (2*n), d (2*n+1))),
    statematch p d.
Definition StateMatch := statematch.
Hint Constructors statematch.

Theorem FSim:
  forall R,
  forward_simulation (Pair.Step R) (Disk.Step R).
Proof.
  intros; exists (progmatch Compile statematch); intros.

  repeat match goal with
  | [ x: progmatch _ _ _ _ |- _ ] => inversion x; clear x; subst
  | [ x: statematch _ _ |- _ ] => inversion x; clear x; subst
  end.

  match goal with
  | [ x: Pair.Step _ _ _ |- _ ] => inversion x; clear x; subst
  end.

  - (* PRead *)
    eexists; split.
    + eapply star_step; [constructor|].
      eapply star_step; [constructor|].
      apply star_refl.
    + crush.
  - (* PWrite *)
    destruct v; eexists; split.
    + eapply star_step; [constructor|].
      eapply star_step; [constructor|].
      apply star_refl.
    + constructor; [crush|constructor; intros].
      destruct (eq_nat_dec b n1); repeat resolve_setidx omega; crush.
Qed.

End PairToDisk.








(* An example of how to write a program in a dual language *)
Module DDisk := DualProg Disk Disk.
Definition example_dd_prog : DDisk.Prog nat :=
  DDisk.DoLeft (Disk.Write 0 5 ;; Disk.Write 1 6 ;; Disk.Return tt) ;;
  a <- DDisk.DoLeft (x <- Disk.Read 0 ; Disk.Return x) ;
  b <- DDisk.DoRight (Disk.Write 2 a ;; x <- Disk.Read 2 ; Disk.Return x) ;
  DDisk.Return b.

Module PairDisk := DualProg Pair Disk.
Definition example_pd_prog : PairDisk.Prog nat :=
  PairDisk.DoLeft (Pair.Write 0 (1,2) ;; Pair.Return tt) ;;
  a <- PairDisk.DoLeft (x <- Pair.Read 0 ; Pair.Return x) ;
  b <- PairDisk.DoRight (Disk.Write 7 (fst a) ;; x <- Disk.Read 7 ; Disk.Return x) ;
  PairDisk.Return b.

Module DiskToDisk := RefineSelf Disk.
Module PairDiskToDDisk :=
  RefineDual Pair Disk Disk Disk
             PairDisk DDisk PairToDisk DiskToDisk.

Eval compute in PairDiskToDDisk.Compile example_pd_prog.
(*
 * Cool: even though I never wrote how to compile (Pair+Disk) -> (Disk+Disk),
 * and never proved that it correctly refines, this module figures out how to
 * compile these programs, and constructs a proof of correct refinement (as
 * long as each component refines).
 *)
