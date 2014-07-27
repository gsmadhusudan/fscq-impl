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


Module BmapAllocAll <: SmallStepLang.

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
  | StepAllocOK: forall d off rx,
    highest (freebit d) off ->
    step (PS (Alloc rx) d)
         (PS (rx (Some off)) (setidx BlocksPartDisk.eq_addr_dec d off InUse))
  | StepAllocOut: forall d rx,
    (~exists off, freebit d off) ->
    step (PS (Alloc rx) d)
         (PS (rx None) d)
  | StepFree: forall d off rx,
    step (PS (Free off rx) d)
         (PS (rx tt) (setidx BlocksPartDisk.eq_addr_dec d off Avail)).
Definition Step := @step.

End BmapAllocAll.


Module BmapAllocAllToAllocOne <: Refines BmapAllocAll BmapAllocOne.

Obligation Tactic := Tactics.program_simpl; omega'.

(* XXX *)


End BmapAllocAllToAllocOne.
