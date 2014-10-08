Require Import Arith.
Require Import Word.
Require Import FunctionalExtensionality.
Require Import Eqdep.

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
| Return {R: Set} (v: R) : prog R
| Read (a: addr) : prog valu
| Write (a: addr) (v: valu) : prog unit
| Seq {T R: Set} (p1: prog T) (p2: T -> prog R) : prog R.

Notation "p1 ;; p2" := (Seq p1 (fun _: unit => p2)) (at level 60, right associativity).
Notation "x <- p1 ; p2" := (Seq p1 (fun x => p2)) (at level 60, right associativity).


Definition mem := addr -> option valu.
Definition upd (m : mem) (a : addr) (v : valu) : mem :=
  fun a' => if addr_eq_dec a' a then Some v else m a'.

Inductive outcome {R: Set} :=
| Failed
| Crashed (m: mem)
| Finished (v: R) (m: mem).

Inductive exec : forall (R: Set), mem -> prog R -> @outcome R -> Prop :=
| XReturn : forall m R v, exec m (@Return R v) (Finished v m)
| XReadFail : forall m a, m a = None
  -> exec m (Read a) Failed
| XWriteFail : forall m a v, m a = None
  -> exec m (Write a v) Failed
| XReadOK : forall m a v, m a = Some v
  -> exec m (Read a) (Finished v m)
| XWriteOK : forall m a v v0, m a = Some v0
  -> exec m (Write a v) (Finished tt (upd m a v))
| XSeqFail : forall R T m p1 p2, exec m p1 (@Failed R)
  -> exec m (Seq p1 p2) (@Failed T)
| XSeqCrash : forall R T m p1 p2 m', exec m p1 (@Crashed R m')
  -> exec m (Seq p1 p2) (@Crashed T m')
| XSeqOK : forall R T m p1 p2 v m' (out: @outcome T), exec m p1 (@Finished R v m')
  -> exec m' (p2 v) out
  -> exec m (Seq p1 p2) out
| XCrashBefore : forall R m p, exec m p (@Crashed R m)
| XCrashAfter : forall R m p v m', exec m p (@Finished R v m')
  -> exec m p (@Crashed R m').

Inductive exec_recover : forall (R: Set), mem -> prog R -> prog unit -> @outcome R -> Prop :=
| XRFail : forall R m p1 p2, exec m p1 (@Failed R)
  -> exec_recover m p1 p2 Failed
| XRFinished : forall R m p1 p2 v m', exec m p1 (@Finished R v m')
  -> exec_recover m p1 p2 (Finished v m')
| XRCrashFail : forall R m p1 p2 m', exec m p1 (@Crashed R m')
  -> exec_recover m' p2 p2 Failed
  -> exec_recover m p1 p2 Failed
| XRCrashFinished : forall R m p1 p2 m' v m'', exec m p1 (@Crashed R m')
  -> exec_recover m' p2 p2 (Finished v m'')
  -> exec_recover m p1 p2 (Crashed m'')
| XRCrashCrash : forall R m p1 p2 m' m'', exec m p1 (@Crashed R m')
  -> exec_recover m' p2 p2 (Crashed m'')
  -> exec_recover m p1 p2 (Crashed m'').

Hint Constructors exec.
Hint Constructors exec_recover.


Theorem exec_need_not_crash : forall R (p : prog R) m, exists out,
  exec m p out /\ forall m', out <> Crashed m'.
Proof.
  induction p; intros.
  - eexists; split.
    constructor.
    discriminate.
  - case_eq (m a); intros.
    + eexists; split; [ eapply XReadOK; eauto | discriminate ].
    + eexists; split; [ eapply XReadFail; eauto | discriminate ].
  - case_eq (m a); intros.
    + eexists; split; [ eapply XWriteOK; eauto | discriminate ].
    + eexists; split; [ eapply XWriteFail; eauto | discriminate ].
  - edestruct IHp; destruct x.
    + eexists; split; [ eapply XSeqFail; intuition eauto | discriminate ].
    + intuition congruence.
    + edestruct H.
      eexists; split; [ eapply XSeqOK; intuition eauto | intuition eauto ].
Qed.

Theorem exec_recover_can_terminate : forall R (p1: prog R) p2 m,
  exists out, exec_recover m p1 p2 out.
Proof.
  intros.
  destruct (exec_need_not_crash p1 m).
  destruct x; ( try intuition congruence ) ; eexists.
  - apply XRFail; intuition eauto.
  - apply XRFinished; intuition eauto.
Qed.

Theorem prog_can_crash : forall R (p: prog R) m r m', exec m p (Finished r m') ->
  exec m p (Crashed m').
Proof.
  induction p; intros; try ( inversion H; eauto ).
  inversion H0; eauto.
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
