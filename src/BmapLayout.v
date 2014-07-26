Require Import CpdtTactics.
Require Import FsTactics.
Require Import DiskMod.
Require Import Util.
Require Import Smallstep.
Require Import Closures.
Require Import Tactics.
Require Import FsLayout.
Require Import Arith.
Require Import FunctionalExtensionality.
Open Scope fscq.


Definition blockmapnum := {n: nat | n < NBlockMap}.
Definition blockmapoff := {n: nat | n < SizeBlock}.
Definition blockmap := blockmapoff -> bool.

Definition eq_blockmapnum_dec (a b:blockmapnum) : {a=b}+{a<>b}.
  refine (if eq_nat_dec (proj1_sig a) (proj1_sig b) then _ else _).
  - left. apply sig_pi. auto.
  - right. apply sig_pi_ne. auto.
Defined.

Module BmapStore <: SmallStepLang.

Inductive prog {R:Type} : Type :=
  | Read (a:blockmapnum) (rx:blockmap->prog)
  | Write (a:blockmapnum) (bm:blockmap) (rx:unit->prog)
  | Return (v:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.
Definition State := blockmapnum -> blockmap.

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepRead: forall d a rx,
    step (PS (Read a rx) d)
         (PS (rx (d a)) d)
  | StepWrite: forall d a bm rx,
    step (PS (Write a bm rx) d)
         (PS (rx tt) (setidx eq_blockmapnum_dec d a bm)).
Definition Step := @step.

End BmapStore.


Module BmapToDisk <: Refines BmapStore BmapPartDisk.

Obligation Tactic := Tactics.program_simpl; omega'.

Program Definition baddr (a:blockmapnum) (off:blockmapoff) : BmapPartDisk.addr :=
  a * SizeBlock + off.

Ltac unfold_bmap := unfold baddr in *; unfold_fslayout.
Ltac omega'bmap := auto; omega'unfold unfold_bmap.

Program Fixpoint bmread (R:Type) (a:blockmapnum)
                        (n:nat) (NOK:n<=SizeBlock)
                        (bm:blockmap) rx :
                        BmapPartDisk.Prog R :=
  match n with
  | 0 => rx bm
  | S x =>
    f <- BmapPartDisk.Read (baddr a x);
    bmread R a x _ (setidxsig eq_nat_dec bm x (nat2bool f)) rx
  end.

Program Fixpoint bmwrite (R:Type) (a:blockmapnum)
                         (n:nat) (NOK:n<=SizeBlock)
                         (bm:blockmap) rx :
                         BmapPartDisk.Prog R :=
  match n with
  | 0 => rx
  | S x =>
    BmapPartDisk.Write (baddr a x) (bool2nat (bm x));;
    bmwrite R a x _ bm rx
  end.

Program Fixpoint Compile {R:Type} (p:BmapStore.Prog R) : (BmapPartDisk.Prog R) :=
  match p with
  | BmapStore.Read a rx =>
    bmread R a SizeBlock _ (fun _ => true) (fun bm => Compile (rx bm))
  | BmapStore.Write a bm rx =>
    bmwrite R a SizeBlock _ bm (Compile (rx tt))
  | BmapStore.Return r =>
    BmapPartDisk.Return r
  end.

Definition bmap_match (bl:blockmap) (d:BmapPartDisk.State) (a:blockmapnum) :=
  forall off, bool2nat (bl off) = d (baddr a off).

Inductive statematch : BmapStore.State -> BmapPartDisk.State -> Prop :=
  | Match: forall (bms:BmapStore.State) (d:BmapPartDisk.State)
    (M: forall a, bmap_match (bms a) d a),
    statematch bms d.
Definition StateMatch := statematch.
Hint Constructors statematch.

Lemma star_bmwrite:
  forall R n Hn a bm rx disk (Hz: 0<=SizeBlock),
  exists disk',
  star (BmapPartDisk.Step R)
    (PS (progseq2 (bmwrite R a n Hn bm) rx) disk)
    (PS (progseq2 (bmwrite R a 0 Hz bm) rx) disk') /\
  (forall off, proj1_sig off < n ->
   disk' (baddr a off) = bool2nat (bm off)) /\
  (forall b, (proj1_sig b < (proj1_sig a) * SizeBlock \/
              proj1_sig b >= (proj1_sig a) * SizeBlock + n) ->
   disk' b = disk b).
Proof.
  induction n; intros.
  - eexists; split; [ apply star_refl | crush ].
  - edestruct IHn; clear IHn; Tactics.destruct_pairs; exists x.
    split; [|split]; intros.
    + eapply star_step; [constructor|]. apply H.
    + destruct (eq_nat_dec (proj1_sig off) n).
      * subst. rewrite H1; auto.
        repeat resolve_setidx omega'. auto.
      * apply H0. omega'.
    + rewrite H1; [ | crush ].
      repeat resolve_setidx omega'bmap. auto.
Qed.

Theorem FSim:
  forall R,
  forward_simulation (BmapStore.Step R) (BmapPartDisk.Step R).
Proof.
  intros; exists (progmatch Compile statematch); intros.

  repeat match goal with
  | [ x: progmatch _ _ _ _ |- _ ] => inversion x; clear x; subst
  | [ x: statematch _ _ |- _ ] => inversion x; clear x; subst
  end.

  match goal with
  | [ x: BmapStore.Step _ _ _ |- _ ] => inversion x; clear x; subst
  end.

  - (* Read *)
    admit.
(*
    econstructor; split.
    + apply star_iread. instantiate (1:=(s1 a)). auto.
    + constructor; cc.
*)

  - (* Write *)
    edestruct star_bmwrite. Tactics.destruct_pairs.
    econstructor; split; subst.
    + apply H.
    + clear H. unfold bmap_match in M0.
      constructor; cc.
      unfold bmap_match; intros.
      destruct (eq_blockmapnum_dec a a0); subst.
      * rewrite H0; [|omega'bmap].
        repeat resolve_setidx omega'bmap; auto.
      * rewrite H1; [|omega'bmap].
        repeat resolve_setidx omega'bmap; apply M0.
Qed.

End BmapToDisk.
