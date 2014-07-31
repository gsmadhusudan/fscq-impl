Require Import CpdtTactics.
Require Import FsTactics.
Require Import Closures.
Require Import Util.
Require Import Smallstep.
Require Import Arith.


Definition TheDiskSize := 20.

Module Type SmallStepLang'.
Parameter Prog: Type->Type.
End SmallStepLang'.

Module Disk <: SmallStepLang'.

Definition addr := {x:nat | x < TheDiskSize}.
Definition block := nat.

Definition eq_addr_dec (a b:addr) : {a=b}+{a<>b}.
  refine (if eq_nat_dec (proj1_sig a) (proj1_sig b) then _ else _).
  - left. apply sig_pi. auto.
  - right. apply sig_pi_ne. auto.
Defined.

Inductive prog : Type -> Type :=
  | Read (a:addr): prog block
  | Write (a:addr) (v:block): prog unit.
Definition Prog := @prog.
Definition State := addr -> block.

(*
Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepRead: forall d a rx,
    step (PS (Read a rx) d)
         (PS (rx (d a)) d)
  | StepWrite: forall d a v rx,
    step (PS (Write a v rx) d)
         (PS (rx tt) (setidx eq_addr_dec d a v)).
Definition Step := @step.
*)

End Disk.


Module Type Executable (L:SmallStepLang').
Parameter MemState : Type.
Parameter MemInit : MemState.
Parameter Execute : forall {R:Type}, MemState -> L.Prog R -> MemState * R.
End Executable.


Module MyDisk := Disk.
Module MyDiskCache := Disk.

Module ExecDisk <: Executable Disk.
(* This is just a Coq sketch; actual implementation of (Executable Disk)
 * would likely come from native code like Ocaml.
 *)
Definition MemState := MyDisk.addr->MyDisk.block.
Definition MemInit := fun (x: MyDisk.addr) => 0.
Fixpoint Execute {R:Type} (s:MemState) (p:MyDisk.Prog R) : MemState * R :=
  match p with
  | MyDisk.Read addr =>
    (s, s addr)
  | MyDisk.Write addr val =>
    (setidx MyDisk.eq_addr_dec s addr val, tt)
  end.
End ExecDisk.

Module DiskCacheOnDisk (DE:Executable MyDisk).
(* Cache the last block accessed on disk *)
Inductive state :=
  | CacheState: forall (a:option MyDisk.addr) (b:MyDisk.block) (ds:DE.MemState), state.
Definition MemState := state.
Definition MemInit := CacheState None 0 DE.MemInit.
Fixpoint Execute {R:Type} (s:MemState) (p:MyDiskCache.Prog R) : MemState * R :=
  let (a, b, ds) := s in
  match p with
  | MyDiskCache.Read addr =>
    match a with
    | Some addr => (s, b)
    | _ =>
      let (ds', b') := DE.Execute ds (MyDisk.Read addr) in
      (CacheState (Some addr) b' ds', b')
    end
  | MyDiskCache.Write addr val =>
    let (ds', r) := DE.Execute ds (MyDisk.Write addr val) in
    (CacheState (Some addr) val ds', r)
  end.
End DiskCacheOnDisk.
