Require Import Arith.
Require Import Word.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

(** * The programming language *)

Module Type VALULEN.
  Parameter valulen : nat.
  Axiom valulen_is: valulen = 4096. (* 512 bytes *)
End VALULEN.

Module Valulen : VALULEN.
  Definition valulen := 4096.
  Theorem valulen_is: valulen = 4096.
  Proof.
    auto.
  Qed.
End Valulen.

Definition addrlen := 64.
Notation "'valulen'" := (Valulen.valulen).
Notation "'valulen_is'" := (Valulen.valulen_is).

Notation "'addr'" := (word addrlen).
Notation "'valu'" := (word valulen).
Definition addr_eq_dec := @weq addrlen.

Definition wringaddr := wring addrlen.
Add Ring wringaddr : wringaddr (decidable (weqb_sound addrlen), constants [wcst]).

Inductive prog : Set -> Type :=
| Done (t: donetoken)
| Read (a: addr) (rx: valu -> prog)
| Write (a: addr) (v: valu) (rx: unit -> prog).

Definition progseq (A B:Type) (a:B->A) (b:B) := a b.

Notation "p1 ;; p2" := (progseq p1 (fun _: unit => p2)) (at level 60, right associativity).
Notation "x <- p1 ; p2" := (progseq p1 (fun x => p2)) (at level 60, right associativity).


Definition mem := addr -> option valu.
Definition upd (m : mem) (a : addr) (v : valu) : mem :=
  fun a' => if addr_eq_dec a' a then Some v else m a'.

Inductive outcome :=
| Failed
| Finished
| Crashed.

Inductive exec : mem -> prog -> mem -> outcome -> Prop :=
| XDone : forall m t, exec m (Done t) m Finished
| XReadFail : forall m a rx,
  m a = None ->
  exec m (Read a rx) m Failed
| XWriteFail : forall m a v rx,
  m a = None ->
  exec m (Write a v rx) m Failed
| XReadOK : forall m a v rx m' out,
  m a = Some v ->
  exec m (rx v) m' out ->
  exec m (Read a rx) m' out
| XWriteOK : forall m a v v0 rx m' out,
  m a = Some v0 ->
  exec (upd m a v) (rx tt) m' out ->
  exec m (Write a v rx) m' out
| XCrash : forall m p, exec m p m Crashed.

Inductive exec_recover : mem -> prog -> prog -> mem -> outcome -> Prop :=
| XRFail : forall m p1 p2 m',
  exec m p1 m' Failed -> exec_recover m p1 p2 m' Failed
| XRFinished : forall m p1 p2 m',
  exec m p1 m' Finished -> exec_recover m p1 p2 m' Finished
| XRCrashed : forall m p1 p2 m' m'' out,
  exec m p1 m' Crashed ->
  exec_recover m' p2 p2 m'' out -> exec_recover m p1 p2 m'' out.

Hint Constructors exec.
Hint Constructors exec_recover.


Theorem exec_need_not_crash : forall p m,
  exists m' out, exec m p m' out /\ out <> Crashed.
Proof.
  induction p.
  - do 2 eexists; split.
    constructor.
    discriminate.
  - intros.
    case_eq (m a); intros.
    + edestruct H. destruct H1. destruct H1.
      do 2 eexists; split.
      * eapply XReadOK; eauto.
      * auto.
    + do 2 eexists; split.
      * eapply XReadFail; eauto.
      * discriminate.
  - intros.
    case_eq (m a); intros.
    + edestruct H. destruct H1. destruct H1.
      do 2 eexists; split.
      * eapply XWriteOK; eauto.
      * auto.
    + do 2 eexists; split.
      * eapply XWriteFail; eauto.
      * discriminate.
Qed.

Theorem exec_recover_can_terminate : forall p1 p2 m,
  exists m' out, exec_recover m p1 p2 m' out.
Proof.
  intros.
  destruct (exec_need_not_crash p1 m).
  destruct H. destruct H.
  do 2 eexists.
  destruct x0; try congruence.
  - apply XRFail; eauto.
  - apply XRFinished; eauto.
Qed.

Theorem prog_can_crash : forall p m m' out,
  exec m p m' out ->
  exec m p m' Crashed.
Proof.
  induction p; intros.
  - inversion H; eauto.
  - inversion H0; eauto.
  - inversion H0; eauto.
Qed.


Theorem upd_eq : forall m a v a',
  a' = a
  -> upd m a v a' = Some v.
Proof.
  intros; subst; unfold upd.
  destruct (addr_eq_dec a a); tauto.
Qed.

Theorem upd_ne : forall m a v a',
  a' <> a
  -> upd m a v a' = m a'.
Proof.
  intros; subst; unfold upd.
  destruct (addr_eq_dec a' a); tauto.
Qed.

Theorem upd_repeat: forall m a v v',
  upd (upd m a v') a v = upd m a v.
Proof.
  intros; apply functional_extensionality; intros.
  case_eq (addr_eq_dec a x); intros; subst.
  repeat rewrite upd_eq; auto.
  repeat rewrite upd_ne; auto.
Qed.

Theorem upd_comm: forall m a0 v0 a1 v1, a0 <> a1
  -> upd (upd m a0 v0) a1 v1 = upd (upd m a1 v1) a0 v0.
Proof.
  intros; apply functional_extensionality; intros.
  case_eq (addr_eq_dec a1 x); case_eq (addr_eq_dec a0 x); intros; subst.
  rewrite upd_eq; auto. rewrite upd_ne; auto. rewrite upd_eq; auto.
  rewrite upd_eq; auto. rewrite upd_ne; auto. rewrite upd_eq; auto.
  rewrite upd_ne; auto. rewrite upd_eq; auto. rewrite upd_eq; auto.
  rewrite upd_ne; auto. rewrite upd_ne; auto. rewrite upd_ne; auto. rewrite upd_ne; auto.
Qed.
