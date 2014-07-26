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
  P a /\ ~exists a', proj1_sig a' > proj1_sig a /\ P a'.

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
  bm off = true.

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepAllocOK: forall d a off rx,
    highest (freebit (d a)) off ->
    step (PS (Alloc a rx) d)
         (PS (rx (Some off)) (setidx eq_blockmapnum_dec d a
                              (setidx eq_blockmapoff_dec (d a) off false)))
  | StepAllocOut: forall d a rx,
    (~exists off, freebit (d a) off) ->
    step (PS (Alloc a rx) d)
         (PS (rx None) d)
  | StepFree: forall d a off rx,
    step (PS (Free a off rx) d)
         (PS (rx tt) (setidx eq_blockmapnum_dec d a
                      (setidx eq_blockmapoff_dec (d a) off true))).
Definition Step := @step.

End BmapAllocOne.


Module BmapAllocOneToStore <: Refines BmapAllocOne BmapStore.

Obligation Tactic := Tactics.program_simpl; omega'.

(* XXX *)


End BmapAllocOneToStore.
