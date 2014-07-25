Require Import CpdtTactics.
Require Import FsTactics.
Require Import DiskMod.
Require Import Util.
Require Import Smallstep.
Require Import Closures.
Require Import Tactics.
Require Import FsPartsMod.
Open Scope fscq.


Definition SizeBlock := 4.
Definition NBlockPerInode := 2.
Definition NInode := 2.
Definition NBlockMap := 3.


Module InodePartSize <: DiskSize.
Definition Size := NInode * SizeBlock.
End InodePartSize.

Module BmapPartSize <: DiskSize.
Definition Size := NBlockMap * SizeBlock.
End BmapPartSize.

Module BlocksPartSize <: DiskSize.
Definition Size := NBlockMap * SizeBlock.
End BlocksPartSize.

Module WholeDiskSize <: DiskSize.
Definition Size := InodePartSize.Size + BmapPartSize.Size + BlocksPartSize.Size.
End WholeDiskSize.


Module InodePartDisk := Disk InodePartSize.
Module BmapPartDisk := Disk BmapPartSize.
Module BlocksPartDisk := Disk BlocksPartSize.
Module FsPartsDisk := FsParts InodePartDisk BmapPartDisk BlocksPartDisk.
Module WholeDisk := Disk WholeDiskSize.


Ltac omega' := repeat elim_sigs; intros; subst; simpl in *;
               unfold WholeDiskSize.Size in *;
               unfold InodePartSize.Size in *;
               unfold BmapPartSize.Size in *;
               unfold BlocksPartSize.Size in *;
               unfold SizeBlock in *; unfold NInode in *;
               unfold NBlockPerInode in *; unfold NBlockMap in *;
               omega.


Module FsPartsOnDisk <: Refines FsPartsDisk WholeDisk.

Program Definition i2w (n:InodePartDisk.addr) : WholeDisk.addr :=
  n.
Solve Obligations using intros; omega'.

Program Definition m2w (n:BmapPartDisk.addr) : WholeDisk.addr :=
  n + InodePartSize.Size.
Solve Obligations using intros; omega'.

Program Definition b2w (n:BlocksPartDisk.addr) : WholeDisk.addr :=
  n + InodePartSize.Size + BmapPartSize.Size.
Solve Obligations using intros; omega'.

Fixpoint CompileI (R T:Type) (p:InodePartDisk.Prog T)
                             (rx:T->WholeDisk.Prog R) : WholeDisk.Prog R :=
  match p with
  | InodePartDisk.Read n rx' =>
    a <- WholeDisk.Read (i2w n) ;
    CompileI R T (rx' a) rx
  | InodePartDisk.Write n b rx' =>
    WholeDisk.Write (i2w n) b ;;
    CompileI R T (rx' tt) rx
  | InodePartDisk.Return r =>
    rx r
  end.

Fixpoint CompileM (R T:Type) (p:BmapPartDisk.Prog T)
                             (rx:T->WholeDisk.Prog R) : WholeDisk.Prog R :=
  match p with
  | BmapPartDisk.Read n rx' =>
    a <- WholeDisk.Read (m2w n) ;
    CompileM R T (rx' a) rx
  | BmapPartDisk.Write n b rx' =>
    WholeDisk.Write (m2w n) b ;;
    CompileM R T (rx' tt) rx
  | BmapPartDisk.Return r =>
    rx r
  end.

Fixpoint CompileB (R T:Type) (p:BlocksPartDisk.Prog T)
                             (rx:T->WholeDisk.Prog R) : WholeDisk.Prog R :=
  match p with
  | BlocksPartDisk.Read n rx' =>
    a <- WholeDisk.Read (b2w n) ;
    CompileB R T (rx' a) rx
  | BlocksPartDisk.Write n b rx' =>
    WholeDisk.Write (b2w n) b ;;
    CompileB R T (rx' tt) rx
  | BlocksPartDisk.Return r =>
    rx r
  end.

Fixpoint Compile {R:Type} (p:FsPartsDisk.Prog R) : (WholeDisk.Prog R) :=
  match p with
  | FsPartsDisk.I T p rx => CompileI R T p (fun x => Compile (rx x))
  | FsPartsDisk.M T p rx => CompileM R T p (fun x => Compile (rx x))
  | FsPartsDisk.B T p rx => CompileB R T p (fun x => Compile (rx x))
  | FsPartsDisk.Return r => WholeDisk.Return r
  end.

Inductive statematch : FsPartsDisk.State -> WholeDisk.State -> Prop :=
  | Match: forall i m b d
    (I: forall (a:InodePartDisk.addr), i a = d (i2w a))
    (M: forall (a:BmapPartDisk.addr), m a = d (m2w a))
    (B: forall (a:BlocksPartDisk.addr), b a = d (b2w a)),
    statematch (FsPartsDisk.PartState i m b) d.
Definition StateMatch := statematch.
Hint Constructors statematch.

Theorem FSim:
  forall R,
  forward_simulation (FsPartsDisk.Step R) (WholeDisk.Step R).
Proof.
  intros; exists (progmatch Compile statematch); intros.

  repeat match goal with
  | [ x: progmatch _ _ _ _ |- _ ] => inversion x; clear x; subst
  | [ x: statematch _ _ |- _ ] => inversion x; clear x; subst
  end.

  match goal with
  | [ x: FsPartsDisk.Step _ _ _ |- _ ] => inversion x; clear x; subst
  end.

  - (* I *)
    eexists; split.
    + inversion S; subst.
      unfold Compile; fold (@Compile R).
      induction p.
      * eapply star_step; [constructor|].
        match goal with
        | [ H: forall _ _, _ -> star (WholeDisk.Step R) _ _ |- _ ] => apply H; [constructor|]
        end;
        match goal with
        | [ H: star (?STEP R) _ _ |- _ ] =>
          inversion H; match goal with
          | [ Hstep: STEP _ _ _ |- _ ] => inversion Hstep; subst; crush
          end
        end.
      * eapply star_step; [constructor|].
fold CompileI. cbv beta.

        match goal with
        | [ H: forall _ _, _ -> star (WholeDisk.Step R) _ _ |- _ ] => apply H; [constructor|]
        | [ H: forall _, _ -> star (WholeDisk.Step R) _ _ |- _ ] => apply H; [constructor|]
        end.
        match goal with
        | [ H: star (?STEP R) _ _ |- _ ] =>
          inversion H; match goal with
          | [ Hstep: STEP _ _ _ |- _ ] => inversion Hstep; subst; crush
          end
        end.


        


apply STAR.
