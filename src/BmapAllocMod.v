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
Require Import BmapAllocAllMod.
Require Import NPeano.
Open Scope fscq.


Module BmapAlloc <: SmallStepLang.

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

End BmapAlloc.


Module BmapAllocToAllocAll <: Refines BmapAlloc BmapAllocAll.

Obligation Tactic := idtac.

Program Definition pair2addr (bn:blockmapnum) (off:blockmapoff) : BlocksPartDisk.addr :=
  bn * SizeBlock + off.
Solve Obligations using Tactics.program_simpl; omega'.

Program Definition addr2pair (n:BlocksPartDisk.addr) : blockmapnum * blockmapoff :=
  (n / SizeBlock, n mod SizeBlock).
Solve Obligations using intros; apply Nat.div_lt_upper_bound || apply Nat.mod_upper_bound; omega'.

Program Fixpoint Compile {R:Type} (p:BmapAlloc.Prog R) : BmapAllocAll.Prog R :=
  match p with
  | BmapAlloc.Alloc rx =>
    x <- BmapAllocAll.Alloc;
    match x with
    | None => Compile (rx None)
    | Some (bn,off) => Compile (rx (Some (pair2addr bn off)))
    end
  | BmapAlloc.Free n rx =>
    let (bn, off) := addr2pair n in
    BmapAllocAll.Free bn off ;; Compile (rx tt)
  | BmapAlloc.Return r =>
    BmapAllocAll.Return r
  end.

Inductive statematch : BmapAlloc.State -> BmapAllocAll.State -> Prop :=
  | Match: forall fs s
    (M: forall bn off, fs (pair2addr bn off) = s bn off),
    statematch fs s.
Definition StateMatch := statematch.
Hint Constructors statematch.

Theorem FSim:
  forall R,
  forward_simulation (BmapAlloc.Step R) (BmapAllocAll.Step R).
Proof.
  intros; exists (progmatch Compile statematch); intros.

  repeat match goal with
  | [ x: progmatch _ _ _ _ |- _ ] => inversion x; clear x; subst
  | [ x: statematch _ _ |- _ ] => inversion x; clear x; subst
  end.

  match goal with
  | [ x: BmapAlloc.Step _ _ _ |- _ ] => inversion x; clear x; subst
  end.

  - (* Alloc Some *)
    admit.

  - (* Alloc None *)
    admit.

  - (* Free *)
    admit.
Qed.

End BmapAllocToAllocAll.
