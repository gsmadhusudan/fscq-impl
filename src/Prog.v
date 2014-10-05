Require Import Arith.
Require Import Word.
Require Import FunctionalExtensionality.
Require Import Classical_Prop.

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

Parameter donetoken : Set.
Definition mem := addr -> option valu.

Inductive prog :=
| Check (p: mem -> Prop) (rx: unit -> prog)
| Done (t: donetoken)
| Read (a: addr) (rx: valu -> prog)
| Write (a: addr) (v: valu) (rx: unit -> prog).

Definition progseq (A B:Type) (a:B->A) (b:B) := a b.

Notation "p1 ;; p2" := (progseq p1 (fun _: unit => p2)) (at level 60, right associativity).
Notation "x <- p1 ; p2" := (progseq p1 (fun x => p2)) (at level 60, right associativity).


Definition upd (m : mem) (a : addr) (v : valu) : mem :=
  fun a' => if addr_eq_dec a' a then Some v else m a'.

Inductive crash_status :=
| Crashed
| Finished.

Inductive exec_outcome :=
| Failed : exec_outcome
| Stopped : mem -> crash_status -> exec_outcome.

Inductive xr_outcome :=
| RFailed : xr_outcome
| RFinished : mem -> xr_outcome.

Inductive exec : mem -> prog -> exec_outcome -> Prop :=
| XDone : forall m t, exec m (Done t) (Stopped m Finished)
| XCheckFail : forall m (p : mem -> Prop) rx,
  ~ p m ->
  exec m (Check p rx) Failed
| XCheckOK : forall m (p : mem -> Prop) rx out,
  p m ->
  exec m (rx tt) out ->
  exec m (Check p rx) out
| XReadFail : forall m a rx,
  m a = None ->
  exec m (Read a rx) Failed
| XWriteFail : forall m a v rx,
  m a = None ->
  exec m (Write a v rx) Failed
| XReadOK : forall m a v rx out,
  m a = Some v ->
  exec m (rx v) out ->
  exec m (Read a rx) out
| XWriteOK : forall m a v v0 rx out,
  m a = Some v0 ->
  exec (upd m a v) (rx tt) out ->
  exec m (Write a v rx) out
| XCrashDone : forall m t, exec m (Done t) (Stopped m Crashed)
| XCrashRead : forall m a rx, exec m (Read a rx) (Stopped m Crashed)
| XCrashWrite : forall m a v rx, exec m (Write a v rx) (Stopped m Crashed).

Inductive exec_recover : mem -> prog -> prog -> xr_outcome -> Prop :=
| XRFail : forall m p1 p2,
  exec m p1 Failed -> exec_recover m p1 p2 RFailed
| XRFinished : forall m p1 p2 m',
  exec m p1 (Stopped m' Finished) -> exec_recover m p1 p2 (RFinished m')
| XRCrashed : forall m p1 p2 m' out,
  exec m p1 (Stopped m' Crashed) ->
  exec_recover m' p2 p2 out -> exec_recover m p1 p2 out.

Hint Constructors exec.
Hint Constructors exec_recover.


Theorem exec_need_not_crash : forall p m,
  exists out, exec m p out /\ forall m', out <> (Stopped m' Crashed).
Proof.
  induction p.
  - intros.
    destruct (H tt m); destruct H0.
    destruct (classic (p m)); eexists.
    + split.
      apply XCheckOK; try eassumption.
      auto.
    + split.
      apply XCheckFail; try eassumption.
      discriminate.
  - eexists; split.
    constructor.
    discriminate.
  - intros.
    case_eq (m a); intros.
    + edestruct H. destruct H1.
      eexists; split.
      * eapply XReadOK; eauto.
      * auto.
    + eexists; split.
      * eapply XReadFail; eauto.
      * discriminate.
  - intros.
    case_eq (m a); intros.
    + edestruct H. destruct H1.
      eexists; split.
      * eapply XWriteOK; eauto.
      * auto.
    + eexists; split.
      * eapply XWriteFail; eauto.
      * discriminate.
Qed.

Theorem exec_recover_can_terminate : forall p1 p2 m,
  exists out, exec_recover m p1 p2 out.
Proof.
  intros.
  destruct (exec_need_not_crash p1 m).
  destruct H.
  destruct x; try congruence; eexists.
  - apply XRFail; eauto.
  - destruct c.
    exfalso; apply (H0 m0); auto.
    apply XRFinished; eauto.
Qed.

Theorem prog_can_crash : forall p m m' c,
  exec m p (Stopped m' c) ->
  exec m p (Stopped m' Crashed).
Proof.
  induction p; intros.
  - inversion H0; eauto.
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
