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

Module FsDiskSize <: DiskSize.
Definition Size := InodePartSize.Size + BmapPartSize.Size + BlocksPartSize.Size.
End FsDiskSize.


Module InodePartDisk := Disk InodePartSize.
Module BmapPartDisk := Disk BmapPartSize.
Module BlocksPartDisk := Disk BlocksPartSize.
Module FsPartsDisk := FsParts InodePartDisk BmapPartDisk BlocksPartDisk.
Module FsDisk := Disk FsDiskSize.


Ltac unfold_fslayout :=
  unfold FsDiskSize.Size in *;
  unfold InodePartSize.Size in *;
  unfold BmapPartSize.Size in *;
  unfold BlocksPartSize.Size in *;
  unfold SizeBlock in *; unfold NInode in *;
  unfold NBlockMap in *.

Ltac omega' :=
  omega'unfold unfold_fslayout.

Module FsPartsOnDisk <: Refines FsPartsDisk FsDisk.

Obligation Tactic := Tactics.program_simpl; omega'.

Program Definition i2w (n:InodePartDisk.addr) : FsDisk.addr :=
  n.

Program Definition m2w (n:BmapPartDisk.addr) : FsDisk.addr :=
  n + InodePartSize.Size.

Program Definition b2w (n:BlocksPartDisk.addr) : FsDisk.addr :=
  n + InodePartSize.Size + BmapPartSize.Size.

Ltac omega'' := unfold i2w in *; unfold m2w in *; unfold b2w in *; auto; omega'.

Fixpoint CompileI (R T:Type) (p:InodePartDisk.Prog T)
                             (rx:T->FsDisk.Prog R) : FsDisk.Prog R :=
  match p with
  | InodePartDisk.Read n rx' =>
    a <- FsDisk.Read (i2w n) ;
    CompileI R T (rx' a) rx
  | InodePartDisk.Write n b rx' =>
    FsDisk.Write (i2w n) b ;;
    CompileI R T (rx' tt) rx
  | InodePartDisk.Return r =>
    rx r
  end.

Fixpoint CompileM (R T:Type) (p:BmapPartDisk.Prog T)
                             (rx:T->FsDisk.Prog R) : FsDisk.Prog R :=
  match p with
  | BmapPartDisk.Read n rx' =>
    a <- FsDisk.Read (m2w n) ;
    CompileM R T (rx' a) rx
  | BmapPartDisk.Write n b rx' =>
    FsDisk.Write (m2w n) b ;;
    CompileM R T (rx' tt) rx
  | BmapPartDisk.Return r =>
    rx r
  end.

Fixpoint CompileB (R T:Type) (p:BlocksPartDisk.Prog T)
                             (rx:T->FsDisk.Prog R) : FsDisk.Prog R :=
  match p with
  | BlocksPartDisk.Read n rx' =>
    a <- FsDisk.Read (b2w n) ;
    CompileB R T (rx' a) rx
  | BlocksPartDisk.Write n b rx' =>
    FsDisk.Write (b2w n) b ;;
    CompileB R T (rx' tt) rx
  | BlocksPartDisk.Return r =>
    rx r
  end.

Fixpoint Compile {R:Type} (p:FsPartsDisk.Prog R) : (FsDisk.Prog R) :=
  match p with
  | FsPartsDisk.I T p rx => CompileI R T p (fun x => Compile (rx x))
  | FsPartsDisk.M T p rx => CompileM R T p (fun x => Compile (rx x))
  | FsPartsDisk.B T p rx => CompileB R T p (fun x => Compile (rx x))
  | FsPartsDisk.Return r => FsDisk.Return r
  end.

Inductive statematch : FsPartsDisk.State -> FsDisk.State -> Prop :=
  | Match: forall i m b d
    (I: forall (a:InodePartDisk.addr), i a = d (i2w a))
    (M: forall (a:BmapPartDisk.addr), m a = d (m2w a))
    (B: forall (a:BlocksPartDisk.addr), b a = d (b2w a)),
    statematch (FsPartsDisk.PartState i m b) d.
Definition StateMatch := statematch.
Hint Constructors statematch.

Ltac resolve_disks :=
  intros;
  match goal with
  | [ |- setidx ?eq _ ?a _ ?b = _ ] => destruct (eq a b)
  | [ |- _ = setidx ?eq _ ?a _ ?b ] => idtac
  end;
  repeat resolve_setidx omega''; auto.

Theorem FSim:
  forall R,
  forward_simulation (FsPartsDisk.Step R) (FsDisk.Step R).
Proof.
  intros; fsim_begin (@Compile R) statematch.

  - (* I *)
    generalize dependent s2. generalize dependent S.
    generalize dependent i. generalize dependent m.
    generalize dependent b.
    unfold Compile; fold (@Compile R).
    induction p.

    + intros; simpl;
      edestruct H; inversion S; clear S;
      match goal with
      | [ H: star (?STEP T) _ _ |- _ ] =>
        inversion H; match goal with
        | [ Hstep: STEP _ _ _ |- _ ] => inversion Hstep
        end
      end; subst;
      [ constructor; eauto
      | instantiate (1:=s2); eauto
      | instantiate (2:=m); eauto
      | instantiate (2:=b); eauto
      | exists x; split;
        [ eapply star_step; [constructor|crush] | crush ] ].
    + intros; simpl;
      edestruct H; inversion S; clear S;
      match goal with
      | [ H: star (?STEP T) _ _ |- _ ] =>
        inversion H; match goal with
        | [ Hstep: STEP _ _ _ |- _ ] => inversion Hstep
        end
      end; subst;
      [ constructor; eauto
      | instantiate (1:=(setidx FsDisk.eq_addr_dec s2 (i2w a) v)); resolve_disks
      | instantiate (2:=m); resolve_disks
      | instantiate (2:=b); resolve_disks
      | exists x; split;
        [ eapply star_step; [constructor|crush] | crush ] ].
    + intros; simpl;
      inversion S; clear S; subst.
      inversion STAR; [| match goal with
                         | [ H: _ T (PS (_ v) _) _ |- _ ] => inversion H
                         end ].
      eexists; split; [ apply star_refl | constructor; crush ].

  - (* M *)
    generalize dependent s2. generalize dependent S.
    generalize dependent i. generalize dependent m.
    generalize dependent b.
    unfold Compile; fold (@Compile R).
    induction p.

    + intros; simpl;
      edestruct H; inversion S; clear S;
      match goal with
      | [ H: star (?STEP T) _ _ |- _ ] =>
        inversion H; match goal with
        | [ Hstep: STEP _ _ _ |- _ ] => inversion Hstep
        end
      end; subst;
      [ constructor; eauto
      | instantiate (2:=i);
        instantiate (1:=s2); eauto
      | eauto
      | instantiate (2:=b); eauto
      | exists x; split;
        [ eapply star_step; [constructor|crush] | crush ] ].
    + intros; simpl;
      edestruct H; inversion S; clear S;
      match goal with
      | [ H: star (?STEP T) _ _ |- _ ] =>
        inversion H; match goal with
        | [ Hstep: STEP _ _ _ |- _ ] => inversion Hstep
        end
      end; subst;
      [ constructor; eauto
      | instantiate (2:=i);
        instantiate (1:=(setidx FsDisk.eq_addr_dec s2 (m2w a) v)); resolve_disks
      | resolve_disks
      | instantiate (2:=b); resolve_disks
      | exists x; split;
        [ eapply star_step; [constructor|crush] | crush ] ].
    + intros; simpl;
      inversion S; clear S; subst.
      inversion STAR; [| match goal with
                         | [ H: _ T (PS (_ v) _) _ |- _ ] => inversion H
                         end ].
      eexists; split; [ apply star_refl | constructor; crush ].

  - (* B *)
    generalize dependent s2. generalize dependent S.
    generalize dependent i. generalize dependent m.
    generalize dependent b.
    unfold Compile; fold (@Compile R).
    induction p.

    + intros; simpl;
      edestruct H; inversion S; clear S;
      match goal with
      | [ H: star (?STEP T) _ _ |- _ ] =>
        inversion H; match goal with
        | [ Hstep: STEP _ _ _ |- _ ] => inversion Hstep
        end
      end; subst;
      [ constructor; eauto
      | instantiate (2:=i);
        instantiate (1:=s2); eauto
      | instantiate (2:=m); eauto
      | eauto
      | exists x; split;
        [ eapply star_step; [constructor|crush] | crush ] ].
    + intros; simpl;
      edestruct H; inversion S; clear S;
      match goal with
      | [ H: star (?STEP T) _ _ |- _ ] =>
        inversion H; match goal with
        | [ Hstep: STEP _ _ _ |- _ ] => inversion Hstep
        end
      end; subst;
      [ constructor; eauto
      | instantiate (2:=i);
        instantiate (1:=(setidx FsDisk.eq_addr_dec s2 (b2w a) v)); resolve_disks
      | instantiate (2:=m); resolve_disks
      | resolve_disks
      | exists x; split;
        [ eapply star_step; [constructor|crush] | crush ] ].
    + intros; simpl;
      inversion S; clear S; subst.
      inversion STAR; [| match goal with
                         | [ H: _ T (PS (_ v) _) _ |- _ ] => inversion H
                         end ].
      eexists; split; [ apply star_refl | constructor; crush ].
Qed.

End FsPartsOnDisk.
