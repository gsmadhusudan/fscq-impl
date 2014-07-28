Require Import CpdtTactics.
Require Import FsTactics.
Require Import DiskMod.
Require Import Util.
Require Import Smallstep.
Require Import Closures.
Require Import Tactics.
Require Import LogPartsMod.
Require Import FsLayout.
Open Scope fscq.


Definition LogHeader := 2.
Definition LogEntries := 20.
Definition SizeLogEntry := 2.


Module LogPartSize <: DiskSize.
Definition Size := LogHeader + LogEntries * SizeLogEntry.
End LogPartSize.

Module WholeDiskSize <: DiskSize.
Definition Size := LogPartSize.Size + FsDiskSize.Size.
End WholeDiskSize.


Module LogPartDisk := Disk LogPartSize.
Module LogPartsDisk := LogParts LogPartDisk FsDisk.
Module WholeDisk := Disk WholeDiskSize.


Ltac unfold_loglayout :=
  unfold WholeDiskSize.Size in *;
  unfold LogPartSize.Size in *;
  unfold LogHeader in *;
  unfold LogEntries in *;
  unfold SizeLogEntry in *;
  unfold_fslayout.

Ltac omega'log :=
  omega'unfold unfold_loglayout.

Module LogPartsOnDisk <: Refines LogPartsDisk WholeDisk.

Obligation Tactic := Tactics.program_simpl; omega'log.

Program Definition l2w (n:LogPartDisk.addr) : WholeDisk.addr :=
  n.

Program Definition d2w (n:FsDisk.addr) : WholeDisk.addr :=
  n + LogPartSize.Size.

Ltac omega''log := unfold l2w in *; unfold d2w in *; auto; omega'log.

Fixpoint CompileL (R T:Type) (p:LogPartDisk.Prog T)
                             (rx:T->WholeDisk.Prog R) : WholeDisk.Prog R :=
  match p with
  | LogPartDisk.Read n rx' =>
    a <- WholeDisk.Read (l2w n) ;
    CompileL R T (rx' a) rx
  | LogPartDisk.Write n b rx' =>
    WholeDisk.Write (l2w n) b ;;
    CompileL R T (rx' tt) rx
  | LogPartDisk.Return r =>
    rx r
  end.

Fixpoint CompileD (R T:Type) (p:FsDisk.Prog T)
                             (rx:T->WholeDisk.Prog R) : WholeDisk.Prog R :=
  match p with
  | FsDisk.Read n rx' =>
    a <- WholeDisk.Read (d2w n) ;
    CompileD R T (rx' a) rx
  | FsDisk.Write n b rx' =>
    WholeDisk.Write (d2w n) b ;;
    CompileD R T (rx' tt) rx
  | FsDisk.Return r =>
    rx r
  end.

Fixpoint Compile {R:Type} (p:LogPartsDisk.Prog R) : (WholeDisk.Prog R) :=
  match p with
  | LogPartsDisk.L T p rx => CompileL R T p (fun x => Compile (rx x))
  | LogPartsDisk.D T p rx => CompileD R T p (fun x => Compile (rx x))
  | LogPartsDisk.Return r => WholeDisk.Return r
  end.

Inductive statematch : LogPartsDisk.State -> WholeDisk.State -> Prop :=
  | Match: forall ls ds d
    (L: forall (a:LogPartDisk.addr), ls a = d (l2w a))
    (D: forall (a:FsDisk.addr), ds a = d (d2w a)),
    statematch (LogPartsDisk.PartState ls ds) d.
Definition StateMatch := statematch.
Hint Constructors statematch.

Ltac resolve_disks :=
  intros;
  match goal with
  | [ |- setidx ?eq _ ?a _ ?b = _ ] => destruct (eq a b)
  | [ |- _ = setidx ?eq _ ?a _ ?b ] => idtac
  end;
  repeat resolve_setidx omega''log; auto.

Theorem FSim:
  forall R,
  forward_simulation (LogPartsDisk.Step R) (WholeDisk.Step R).
Proof.
  intros; fsim_begin (@Compile R) statematch.

  - (* L *)
    generalize dependent s2. generalize dependent S.
    generalize dependent ls. generalize dependent ds.
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
      | instantiate (2:=ds); eauto
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
      | instantiate (1:=(setidx WholeDisk.eq_addr_dec s2 (l2w a) v)); resolve_disks
      | instantiate (2:=ds); resolve_disks
      | exists x; split;
        [ eapply star_step; [constructor|crush] | crush ] ].
    + intros; simpl;
      inversion S; clear S; subst.
      inversion STAR; [| match goal with
                         | [ H: _ T (PS (_ v) _) _ |- _ ] => inversion H
                         end ].
      eexists; split; [ apply star_refl | constructor; crush ].

  - (* D *)
    generalize dependent s2. generalize dependent S.
    generalize dependent ls. generalize dependent ds.
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
      | instantiate (2:=ls);
        instantiate (1:=s2); eauto
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
      | instantiate (2:=ls);
        instantiate (1:=(setidx WholeDisk.eq_addr_dec s2 (d2w a) v)); resolve_disks
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

End LogPartsOnDisk.
