Require Import CpdtTactics.
Require Import FsTactics.
Require Import Closures.
Require Import Util.
Require Import Smallstep.
Require Import Arith.


Module Type DiskSize.

Parameter Size: nat.

End DiskSize.


Module Disk (Size: DiskSize) <: SmallStepLang.

Definition addr := {x:nat | x < Size.Size}.
Definition block := nat.

Definition eq_addr_dec (a b:addr) : {a=b}+{a<>b}.
  refine (if eq_nat_dec (proj1_sig a) (proj1_sig b) then _ else _).
  - left. apply sig_pi. auto.
  - right. apply sig_pi_ne. auto.
Defined.

Inductive prog {R:Type} : Type :=
  | Read (a:addr) (rx:block->prog)
  | Write (a:addr) (v:block) (rx:unit->prog)
  | Return (v:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.
Definition State := addr -> block.

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepRead: forall d a rx,
    step (PS (Read a rx) d)
         (PS (rx (d a)) d)
  | StepWrite: forall d a v rx,
    step (PS (Write a v rx) d)
         (PS (rx tt) (setidx eq_addr_dec d a v)).
Definition Step := @step.

Theorem opp_step_wf:
  forall R,
  well_founded (opposite_rel (@step R)).
Proof.
  intro R. unfold well_founded. destruct a. generalize dependent s.
  induction p; constructor; intros; invert_rel (opposite_rel (@step R));
  destruct_type State; crush.
Qed.

End Disk.
