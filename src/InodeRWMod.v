Require Import CpdtTactics.
Require Import FsTactics.
Require Import Util.
Require Import Smallstep.
Require Import Closures.
Require Import Tactics.
Require Import Arith.
Require Import InodeAllocMod.
Require Import BmapAllocMod.
Require Import DiskMod.
Require Import FsPartsMod.
Require Import FsLayout.
Require Import InodeLayout.
Open Scope fscq.


Record file := File {
  FFree: AllocState;
  FLen: ilength;
  FData: iblocknum -> BlocksPartDisk.block
}.

Definition eq_iblocknum_dec (a b:iblocknum) : {a=b}+{a<>b}.
  refine (if eq_nat_dec (proj1_sig a) (proj1_sig b) then _ else _).
  - left. apply sig_pi. auto.
  - right. apply sig_pi_ne. auto.
Defined.


Module InodeRW <: SmallStepLang.

(* Note: Shrink and Grow work only for one block at a time;
 * you must pass increasingly smaller or larger len values
 * to resize by multiple blocks.
 *
 * Note: Free works only for empty files; Shrink it first.
 *)

Inductive prog {R:Type} : Type :=
  | Read (inum:inodenum) (off:iblocknum) (rx:BlocksPartDisk.block->prog)
  | Write (inum:inodenum) (off:iblocknum) (b:BlocksPartDisk.block) (rx:unit->prog)
  | Alloc (rx:option inodenum->prog)
  | Free (inum:inodenum) (rx:unit->prog)
  | Shrink (inum:inodenum) (len:ilength) (rx:unit->prog)
  | Grow (inum:inodenum) (len:ilength) (rx:bool->prog)
  | Return (v:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.
Definition State := inodenum -> file.

Definition freeinode (s:State) (inum:inodenum) :=
  FFree (s inum) = Avail.
Program Definition initial_file := File InUse 0 (fun _ => 0).
Program Definition free_file := File Avail 0 (fun _ => 0).
Definition empty_block : BlocksPartDisk.block := 0.

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepRead: forall inum off rx d,
    step (PS (Read inum off rx) d)
         (PS (rx (FData (d inum) off)) d)
  | StepWrite: forall inum off b rx d ,
    step (PS (Write inum off b rx) d)
         (PS (rx tt) (setidx eq_inodenum_dec d inum
                      (File (FFree (d inum))
                            (FLen (d inum))
                            (setidx eq_iblocknum_dec (FData (d inum)) off b))))
  | StepAllocOK: forall inum rx d,
    highest (freeinode d) inum ->
    step (PS (Alloc rx) d)
         (PS (rx (Some inum)) (setidx eq_inodenum_dec d inum initial_file))
  | StepAllocOut: forall rx d,
    (~exists inum, freeinode d inum) ->
    step (PS (Alloc rx) d)
         (PS (rx None) d)
  | StepFree: forall d inum rx,
    proj1_sig (FLen (d inum)) = 0 ->
    step (PS (Free inum rx) d)
         (PS (rx tt) (setidx eq_inodenum_dec d inum free_file))
  | StepShrink: forall inum len rx d,
    proj1_sig len + 1 = proj1_sig (FLen (d inum)) ->
    step (PS (Shrink inum len rx) d)
         (PS (rx tt) (setidx eq_inodenum_dec d inum
                      (File (FFree (d inum))
                            len
                            (FData (d inum)))))
  | StepGrowOK: forall inum len rx d,
    proj1_sig len = proj1_sig (FLen (d inum)) + 1 ->
    step (PS (Grow inum len rx) d)
         (PS (rx true) (setidx eq_inodenum_dec d inum
                        (File (FFree (d inum))
                              len
                              (setidxsig eq_nat_dec (FData (d inum))
                                         (proj1_sig (FLen (d inum))) empty_block)))).

(* XXX When does Grow fail?  Need to model freelist as part of the state...
 *)

Definition Step := @step.

End InodeRW.


Module FsPartsTop := FsParts InodeAlloc BmapAlloc BlocksPartDisk.
Module InodeRWToFsPartsTop <: Refines InodeRW FsPartsTop.

Program Fixpoint Compile {R:Type} (p:InodeRW.Prog R) : (FsPartsTop.Prog R) :=
  match p with
  | InodeRW.Read inum off rx =>
    n <- FsPartsTop.I (i <- InodeAlloc.Read inum; InodeAlloc.Return (IBlocks i off));
    b <- FsPartsTop.B (v <- BlocksPartDisk.Read n; BlocksPartDisk.Return v);
    Compile (rx b)
  | InodeRW.Write inum off b rx =>
    n <- FsPartsTop.I (i <- InodeAlloc.Read inum; InodeAlloc.Return (IBlocks i off));
    FsPartsTop.B (BlocksPartDisk.Write n b;; BlocksPartDisk.Return tt);;
    Compile (rx tt)
  | InodeRW.Alloc rx =>
    oi <- FsPartsTop.I (v <- InodeAlloc.Alloc;
                        match v with
                        | None   => InodeAlloc.Return v
                        | Some n => InodeAlloc.Write n (Inode InUse 0 (fun _ => 0));;
                                    InodeAlloc.Return v
                        end);
    Compile (rx oi)
  | InodeRW.Free inum rx =>
    FsPartsTop.I (InodeAlloc.Free inum;;
                  InodeAlloc.Write inum (Inode Avail 0 (fun _ => 0));;
                  InodeAlloc.Return tt);;
    Compile (rx tt)
  | InodeRW.Shrink inum len rx =>
    b <- FsPartsTop.I (v <- InodeAlloc.Read inum;
                       InodeAlloc.Write inum (Inode InUse len (IBlocks v));;
                       InodeAlloc.Return (IBlocks v ((ILen v) - 1)));
    FsPartsTop.M (BmapAlloc.Free b;; BmapAlloc.Return tt);;
    Compile (rx tt)
  | InodeRW.Grow inum len rx =>
    ob <- FsPartsTop.M (v <- BmapAlloc.Alloc; BmapAlloc.Return v);
    match ob with
    | None   => Compile (rx false)
    | Some b =>
      FsPartsTop.I (v <- InodeAlloc.Read inum;
                    InodeAlloc.Write inum (Inode InUse len
                                           (setidx eq_iblocknum_dec (IBlocks v) (len-1) b));;
                    InodeAlloc.Return tt);;
      FsPartsTop.B (BlocksPartDisk.Write b InodeRW.empty_block;;
                    BlocksPartDisk.Return tt);;
      Compile (rx true)
    end
  | InodeRW.Return v => FsPartsTop.Return v
  end.

Inductive statematch : InodeRW.State -> FsPartsTop.State -> Prop :=
  | Match: forall f i m b
    (MFree: forall inum, FFree (f inum) = IFree (i inum))
    (MLen: forall inum, FLen (f inum) = ILen (i inum))
    (MData: forall inum off, FData (f inum) off = b (IBlocks (i inum) off)),
    statematch f (FsPartsTop.PartState i m b).
Definition StateMatch := statematch.
Hint Constructors statematch.

Theorem FSim:
  forall R,
  forward_simulation (InodeRW.Step R) (FsPartsTop.Step R).
Proof.
  intros; fsim_begin (@Compile R) statematch.

  - (* Read *)
    econstructor; split.
    + unfold Compile; fold (@Compile R).
      eapply star_step;
      [ constructor;
        constructor; (* invert progreturns *)
        eapply star_step; [constructor|]; (* inode program *)
        apply star_refl |].
      eapply star_step;
      [ constructor;
        constructor; (* invert progreturns *)
        eapply star_step; [constructor|]; (* blocks program *)
        apply star_refl |].
      apply star_refl.
    + crush.

  - (* Write *)
    admit.

  - (* Alloc OK *)
    admit.

  - (* Alloc fail *)
    admit.

  - (* Free *)
    admit.

  - (* Shrink *)
    admit.

  - (* Grow OK *)
    admit.
Qed.

End InodeRWToFsPartsTop.
