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

Fixpoint bmfree (R:Type) (a:blockmapnum) (off:blockmapoff) rx :
                BmapStore.Prog R :=
  bm <- BmapStore.Read a;
  BmapStore.Write a (setidx eq_blockmapoff_dec bm off Avail);;
  rx.

Program Fixpoint bmalloc (R:Type) (a:blockmapnum)
                         (n:nat) (NOK:n<=SizeBlock)
                         (rx:option blockmapoff->BmapStore.Prog R) :
                         BmapStore.Prog R :=
  match n with
  | O => rx None
  | S x =>
    bm <- BmapStore.Read a;
    match bm x with
    | InUse => bmalloc R a x _ rx
    | Avail =>
      BmapStore.Write a (setidx eq_blockmapoff_dec bm x InUse);;
      rx (Some x)
    end
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

Theorem FSim:
  forall R,
  forward_simulation (BmapAllocOne.Step R) (BmapStore.Step R).
Proof.
  intros; exists (progmatch Compile statematch); intros.

  repeat match goal with
  | [ x: progmatch _ _ _ _ |- _ ] => inversion x; clear x; subst
  | [ x: statematch _ _ |- _ ] => inversion x; clear x; subst
  end.

  match goal with
  | [ x: BmapAllocOne.Step _ _ _ |- _ ] => inversion x; clear x; subst
  end.

  - (* Alloc Some *)
    admit.

  - (* Alloc None *)
    admit.

  - (* Free *)
    admit.
Qed.

End BmapAllocOneToStore.
