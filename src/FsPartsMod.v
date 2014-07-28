Require Import CpdtTactics.
Require Import FsTactics.
Require Import DiskMod.
Require Import Util.
Require Import Smallstep.
Require Import Closures.
Require Import Tactics.


Module Type FsPartsType
       (Inode: SmallStepLang)
       (Bmap: SmallStepLang)
       (Blocks: SmallStepLang) <: SmallStepLang.

(*
 * XXX Module system warts: this weird type seems needed for the RefineParts
 * module below, for two reasons.
 *
 * First, RefineParts needs to refer to (FsParts I1 M1 B1) and (FsParts I2 M2 B2).
 * If RefineParts instantiates these internally, then they appear as different
 * types from instantiations of the same FsParts elsewhere; as a result,
 * programs that are the same appear to have different types.  This seems to be
 * the bigger problem.
 *
 * Second, RefineParts satisfies Refine (FsParts I1 M1 B1) (FsParts I2 M2 B2), but
 * specifying that syntax causes Coq to complain that "Application of modules
 * is restricted to paths".  This seems less critical; if the first problem above
 * were solved, we could solve this one by just stating later that it satisfies
 * the type; modules in Coq do not need to state every type they satisfy upfront.
 *
 * This type allows passing in "existing" copies of the two FsParts modules,
 * avoiding both problems.
 *
 * Unfortunately, it's a verbatim copy of FsParts..
 *)

Inductive prog {R:Type} : Type :=
  | I {T:Type} (p:Inode.Prog T) (rx:T->prog)
  | M {T:Type} (p:Bmap.Prog T) (rx:T->prog)
  | B {T:Type} (p:Blocks.Prog T) (rx:T->prog)
  | Return (r:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.

Inductive state :=
  | PartState (i:Inode.State) (m:Bmap.State) (b:Blocks.State).
Definition State := state.

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepI: forall (T:Type) p (rx:T->Prog R) s s' m b r
    (S: progreturns (Inode.Step T) (Inode.ReturnOp T) p s s' r),
    step (PS (I p rx) (PartState s m b))
         (PS (rx r) (PartState s' m b))
  | StepM: forall (T:Type) p (rx:T->Prog R) s s' i b r
    (S: progreturns (Bmap.Step T) (Bmap.ReturnOp T) p s s' r),
    step (PS (M p rx) (PartState i s b))
         (PS (rx r) (PartState i s' b))
  | StepB: forall (T:Type) p (rx:T->Prog R) s s' i m r
    (S: progreturns (Blocks.Step T) (Blocks.ReturnOp T) p s s' r),
    step (PS (B p rx) (PartState i m s))
         (PS (rx r) (PartState i m s')).
Definition Step := @step.

End FsPartsType.


Module FsParts
       (Inode: SmallStepLang)
       (Bmap: SmallStepLang)
       (Blocks: SmallStepLang) <: FsPartsType Inode Bmap Blocks.

Inductive prog {R:Type} : Type :=
  | I {T:Type} (p:Inode.Prog T) (rx:T->prog)
  | M {T:Type} (p:Bmap.Prog T) (rx:T->prog)
  | B {T:Type} (p:Blocks.Prog T) (rx:T->prog)
  | Return (r:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.

Inductive state :=
  | PartState (i:Inode.State) (m:Bmap.State) (b:Blocks.State).
Definition State := state.

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepI: forall (T:Type) p (rx:T->Prog R) s s' m b r
    (S: progreturns (Inode.Step T) (Inode.ReturnOp T) p s s' r),
    step (PS (I p rx) (PartState s m b))
         (PS (rx r) (PartState s' m b))
  | StepM: forall (T:Type) p (rx:T->Prog R) s s' i b r
    (S: progreturns (Bmap.Step T) (Bmap.ReturnOp T) p s s' r),
    step (PS (M p rx) (PartState i s b))
         (PS (rx r) (PartState i s' b))
  | StepB: forall (T:Type) p (rx:T->Prog R) s s' i m r
    (S: progreturns (Blocks.Step T) (Blocks.ReturnOp T) p s s' r),
    step (PS (B p rx) (PartState i m s))
         (PS (rx r) (PartState i m s')).
Definition Step := @step.

End FsParts.


Module RefineFsParts (I1 M1 B1: SmallStepLang)
                     (I2 M2 B2: SmallStepLang)
                     (P1: FsPartsType I1 M1 B1)
                     (P2: FsPartsType I2 M2 B2)
                     (I12: Refines I1 I2)
                     (M12: Refines M1 M2)
                     (B12: Refines B1 B2) <: Refines P1 P2.

Module FSR_I := FSimReturn I1 I2 I12.
Module FSR_M := FSimReturn M1 M2 M12.
Module FSR_B := FSimReturn B1 B2 B12.

Fixpoint Compile {R:Type} (p:@P1.Prog R) : @P2.Prog R :=
  match p with
  | P1.I T p rx => P2.I (I12.Compile T p) (fun x => Compile (rx x))
  | P1.M T p rx => P2.M (M12.Compile T p) (fun x => Compile (rx x))
  | P1.B T p rx => P2.B (B12.Compile T p) (fun x => Compile (rx x))
  | P1.Return v => P2.Return v
  end.

Inductive statematch : P1.State -> P2.State -> Prop :=
  | Match: forall i1 i2 m1 m2 b1 b2
    (MI: I12.StateMatch i1 i2)
    (MM: M12.StateMatch m1 m2)
    (MB: B12.StateMatch b1 b2),
    statematch (P1.PartState i1 m1 b1) (P2.PartState i2 m2 b2).
Definition StateMatch := statematch.
Hint Constructors statematch.

Theorem FSim:
  forall R,
  forward_simulation (P1.Step R) (P2.Step R).
Proof.
  intros; fsim_begin (@Compile R) statematch;
  [ edestruct FSR_I.fsim_implies_returns
  | edestruct FSR_M.fsim_implies_returns
  | edestruct FSR_B.fsim_implies_returns ];
  eauto; Tactics.destruct_pairs; eexists;
  ( split;
    [ eapply star_step; [constructor; eauto|apply star_refl]
    | constructor; [|constructor]; auto ] ).
Qed.

End RefineFsParts.
