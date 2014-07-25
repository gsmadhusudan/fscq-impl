Require Import CpdtTactics.
Require Import FsTactics.
Require Import DiskMod.
Require Import Util.
Require Import Smallstep.
Require Import Closures.
Require Import Tactics.
Require Import FsLayout.
Require Import Arith.
Open Scope fscq.


Definition inodenum := {n: nat | n < NInode}.
Definition NBlockPerInode := SizeBlock - 2.
Definition iblocknum := {n: nat | n < NBlockPerInode}.

Ltac unfold_inode := unfold_fslayout; unfold NBlockPerInode in *.
Ltac omega'inode := omega'unfold unfold_inode.

Definition eq_inodenum_dec (a b:inodenum) : {a=b}+{a<>b}.
  refine (if eq_nat_dec (proj1_sig a) (proj1_sig b) then _ else _).
  - left. apply sig_pi. auto.
  - right. apply sig_pi_ne. auto.
Defined.

Record inode := Inode {
  IFree: bool;
  ILen: { l: nat | l <= NBlockPerInode };  (* in blocks *)
  IBlocks: iblocknum -> BlocksPartDisk.addr
}.


Module InodeStore <: SmallStepLang.

Inductive prog {R:Type} : Type :=
  | Read (a:inodenum) (rx:inode->prog)
  | Write (a:inodenum) (i:inode) (rx:unit->prog)
  | Return (v:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.
Definition State := inodenum -> inode.

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepRead: forall d a rx,
    step (PS (Read a rx) d)
         (PS (rx (d a)) d)
  | StepWrite: forall d a i rx,
    step (PS (Write a i rx) d)
         (PS (rx tt) (setidx eq_inodenum_dec d a i)).
Definition Step := @step.

End InodeStore.


Module InodeToDisk <: Refines InodeStore InodePartDisk.

Obligation Tactic := Tactics.program_simpl; omega'inode.

Program Definition faddr (a:inodenum) : InodePartDisk.addr := a * SizeBlock.
Program Definition laddr (a:inodenum) : InodePartDisk.addr := a * SizeBlock + 1.
Program Definition baddr (a:inodenum) (off:iblocknum) : InodePartDisk.addr :=
  a * SizeBlock + 2 + off.

Program Fixpoint iread_blocklist (R:Type) (a:inodenum)
                                 (n:nat) (NOK:n<=NBlockPerInode)
                                 (bl:iblocknum->BlocksPartDisk.addr) rx :
                                 InodePartDisk.Prog R :=
  match n with
  | 0 => rx bl
  | S x =>
    bx <- InodePartDisk.Read (baddr a x);
    if lt_dec bx BlocksPartSize.Size then
      @iread_blocklist R a x _ (setidxsig eq_nat_dec bl x bx) rx
    else
      @iread_blocklist R a x _ (setidxsig eq_nat_dec bl x 0) rx
  end.

Program Definition iread {R:Type} (a:inodenum) rx : InodePartDisk.Prog R :=
  free <- InodePartDisk.Read (faddr a);
  len <- InodePartDisk.Read (laddr a);
  bl <- @iread_blocklist R a NBlockPerInode _ (fun _ => 0);
  if le_dec len NBlockPerInode then
    rx (Inode (nat2bool free) len bl)
  else
    rx (Inode (nat2bool free) 0 bl).

Program Fixpoint iwrite_blocklist (R:Type) (a:inodenum) (i:inode)
                                  (n:nat) (NOK:n<=NBlockPerInode) rx :
                                  InodePartDisk.Prog R :=
  match n with
  | 0 => rx
  | S x =>
    InodePartDisk.Write (baddr a x) (IBlocks i x);;
    @iwrite_blocklist R a i x _ rx
  end.

Program Definition iwrite {R:Type} (a:inodenum) (i:inode) rx : InodePartDisk.Prog R :=
  InodePartDisk.Write (faddr a) (bool2nat (IFree i));;
  InodePartDisk.Write (laddr a) (ILen i);;
  @iwrite_blocklist R a i NBlockPerInode _ rx.

Fixpoint Compile {R:Type} (p:InodeStore.Prog R) : (InodePartDisk.Prog R) :=
  match p with
  | InodeStore.Read a rx =>
    iread a (fun i => Compile (rx i))
  | InodeStore.Write a i rx =>
    iwrite a i (Compile (rx tt))
  | InodeStore.Return r =>
    InodePartDisk.Return r
  end.

Inductive statematch : InodeStore.State -> InodePartDisk.State -> Prop :=
  | Match: forall (i:InodeStore.State) (d:InodePartDisk.State)
    (MF: forall a, IFree (i a) = nat2bool (d (faddr a)))
    (ML: forall a, proj1_sig (ILen (i a)) = d (laddr a))
    (MF: forall a off, proj1_sig (IBlocks (i a) off) = d (baddr a off)),
    statematch i d.
Definition StateMatch := statematch.
Hint Constructors statematch.



Theorem FSim:
  forall R,
  forward_simulation (InodeStore.Step R) (InodePartDisk.Step R).
Proof.
  intros; exists (progmatch Compile statematch); intros.

  repeat match goal with
  | [ x: progmatch _ _ _ _ |- _ ] => inversion x; clear x; subst
  | [ x: statematch _ _ |- _ ] => inversion x; clear x; subst
  end.

  match goal with
  | [ x: InodeStore.Step _ _ _ |- _ ] => inversion x; clear x; subst
  end.

Abort.

End InodeToDisk.
