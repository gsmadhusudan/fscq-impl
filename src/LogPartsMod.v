Require Import CpdtTactics.
Require Import FsTactics.
Require Import DiskMod.
Require Import Util.
Require Import Smallstep.
Require Import Closures.
Require Import Tactics.


Module Type LogPartsType
       (Log: SmallStepLang)
       (Data: SmallStepLang) <: SmallStepLang.

(*
 * XXX Module system warts: see comment in FsPartsMod.v
 *)

Inductive prog {R:Type} : Type :=
  | L {T:Type} (p:Log.Prog T) (rx:T->prog)
  | D {T:Type} (p:Data.Prog T) (rx:T->prog)
  | Return (r:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.

Inductive state :=
  | PartState (l:Log.State) (d:Data.State).
Definition State := state.

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepL: forall p rx s s' d r
    (S: progreturns (Log.Step R) (Log.ReturnOp R) p s s' r),
    step (PS (L p rx) (PartState s d))
         (PS (rx r) (PartState s' d))
  | StepD: forall p rx s s' l r
    (S: progreturns (Data.Step R) (Data.ReturnOp R) p s s' r),
    step (PS (D p rx) (PartState l s))
         (PS (rx r) (PartState l s')).
Definition Step := @step.

End LogPartsType.


Module LogParts
       (Log: SmallStepLang)
       (Data: SmallStepLang) <: LogPartsType Log Data.

Inductive prog {R:Type} : Type :=
  | L {T:Type} (p:Log.Prog T) (rx:T->prog)
  | D {T:Type} (p:Data.Prog T) (rx:T->prog)
  | Return (r:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.

Inductive state :=
  | PartState (l:Log.State) (d:Data.State).
Definition State := state.

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepL: forall p rx s s' d r
    (S: progreturns (Log.Step R) (Log.ReturnOp R) p s s' r),
    step (PS (L p rx) (PartState s d))
         (PS (rx r) (PartState s' d))
  | StepD: forall p rx s s' l r
    (S: progreturns (Data.Step R) (Data.ReturnOp R) p s s' r),
    step (PS (D p rx) (PartState l s))
         (PS (rx r) (PartState l s')).
Definition Step := @step.

End LogParts.


Module RefineLogParts (L1 D1: SmallStepLang)
                      (L2 D2: SmallStepLang)
                      (P1: LogPartsType L1 D1)
                      (P2: LogPartsType L2 D2)
                      (L12: Refines L1 L2)
                      (D12: Refines D1 D2) <: Refines P1 P2.

Module FSR_L := FSimReturn L1 L2 L12.
Module FSR_D := FSimReturn D1 D2 D12.

Fixpoint Compile {R:Type} (p:@P1.Prog R) : @P2.Prog R :=
  match p with
  | P1.L T p rx => P2.L (L12.Compile T p) (fun x => Compile (rx x))
  | P1.D T p rx => P2.D (D12.Compile T p) (fun x => Compile (rx x))
  | P1.Return v => P2.Return v
  end.

Inductive statematch : P1.State -> P2.State -> Prop :=
  | Match: forall l1 l2 d1 d2
    (ML: L12.StateMatch l1 l2)
    (MD: D12.StateMatch d1 d2),
    statematch (P1.PartState l1 d1) (P2.PartState l2 d2).
Definition StateMatch := statematch.
Hint Constructors statematch.

Theorem FSim:
  forall R,
  forward_simulation (P1.Step R) (P2.Step R).
Proof.
  intros; fsim_begin (@Compile R) statematch;
  [ edestruct FSR_L.fsim_implies_returns
  | edestruct FSR_D.fsim_implies_returns ];
  eauto; Tactics.destruct_pairs; eexists;
  ( split;
    [ eapply star_step; [constructor; eauto|apply star_refl]
    | constructor; [|constructor]; auto ] ).
Qed.

End RefineLogParts.
