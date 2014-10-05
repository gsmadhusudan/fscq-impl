Require Import Hoare.
Require Import Prog.
Require Import Pred.

Definition preserves_precondition (pre : pred) p :=
  forall m out, pre m -> exec m p out -> exists m' s, out = (Stopped m' s) /\ pre m'.

Theorem pp_lift : forall pre P p,
  preserves_precondition pre p ->
  preserves_precondition (pre * [[ P ]]) p.
Proof.
  unfold preserves_precondition; intros.
  apply sep_star_lift2and in H0; destruct H0.
  edestruct H; clear H; eauto.
  destruct H3.
  do 2 eexists; intuition eauto.
  apply sep_star_and2lift.
  split; eauto.
Qed.

Theorem idempotent_ok' : forall p p1 p2 pre,
  preserves_precondition pre p ->
  p1 = p ->
  p2 = p ->
  {{ pre }} p1 >> p2.
Proof.
  unfold corr at 1.
  intros.

  match goal with
  | [ H: exec_recover _ _ _ _ |- _ ] => induction H; subst; eauto
  end.

  - edestruct H; eauto. destruct H0. destruct H0. congruence.
  - discriminate.
  - apply IHexec_recover; eauto.
    edestruct H; eauto.
    destruct H0; destruct H0.
    inversion H0.
    eauto.
Qed.

Theorem idempotent_ok : forall p pre,
  preserves_precondition pre p ->
  {{ pre }} p >> p.
Proof.
  intros.
  eapply idempotent_ok'; eauto.
Qed.

Theorem corr_to_pp : forall p1 p2 pre1 pre2,
  {{ pre1 }} p1 >> Check pre2 ;; p2 ->
  (pre1 ==> [ pre2 ==> pre1 ]) ->
  preserves_precondition pre1 p1.
Proof.
  unfold preserves_precondition.
  intros.
  unfold corr in H.
  destruct out.
  - exfalso.
    destruct (H m RFailed); eauto.
  - do 2 eexists; split; eauto.

    assert (exec m p1 (Stopped m0 Crashed)) by ( eapply prog_can_crash; eauto ).
    clear H2.

    assert (forall out, exec m0 (Check pre2 ;; p2) out -> out <> Failed).
    + unfold not in *; intros; subst; eauto.
    + destruct (exec_need_not_crash (Check pre2 ;; p2) m0).
      destruct H4.
      inversion H4; subst.
      * exfalso. edestruct H2; eauto.
      * eapply H0; eauto.
      * exfalso. edestruct H5; eauto.
Qed.


(* Sketch of how we might prove recover's idempotence *)

Parameter xrecover : prog -> prog.
Parameter log_intact : pred.
Parameter recovered : pred.


Section DONETOKEN_EXISTS.

Variable p: prog.
Variable rec: prog.
Variable pre: pred.
Variable pok: {{ pre }} p >> rec.
Variable m: mem.
Variable mok: pre m.

Definition exec_t_ex: forall m p out m',
  exec m p out ->
  out = (Stopped m' Finished) ->
  exists t: donetoken, True.
Proof.
  intros.
  induction H; try discriminate; eauto.
Qed.

Definition execr_t_ex: forall m p1 p2 out,
  exec_recover m p1 p2 out ->
  out <> RFailed ->
  exists t: donetoken, True.
Proof.
  intros.
  induction H.
  - exfalso. auto.
  - eapply exec_t_ex; eauto.
  - eauto.
Qed.

Definition t_ex: exists t: donetoken, True.
  destruct (exec_recover_can_terminate p rec m).
  apply execr_t_ex with (m:=m) (p1:=p) (p2:=rec) (out:=x); auto.
  eapply pok; eauto.
Qed.

End DONETOKEN_EXISTS.


Theorem recover_base_ok : forall rx rec,
  {{ log_intact
   * [[ exists p, {{ recovered }} rx >> Check log_intact ;; p ]]
   * [[ exists p, {{ log_intact }} rec >> Check log_intact ;; p ]]
  }} xrecover rx >> Check log_intact ;; rec.
Admitted.

Theorem recover_preserves : forall rx rec,
  preserves_precondition
    (log_intact
   * [[ exists p, {{ recovered }} rx >> Check log_intact ;; p ]]
   * [[ exists p, {{ log_intact }} rec >> Check log_intact ;; p ]])
    (xrecover rx).
Proof.
  intros.
  eapply corr_to_pp.
  eapply pimpl_ok. apply recover_base_ok. apply pimpl_refl.
  repeat ( apply sep_star_lift_l; intros ).
  unfold lift, pimpl; intros.
  repeat ( apply sep_star_and2lift; unfold lift; split; eauto ).
Qed.

Theorem recover_idempotent_ok : forall rec,
  {{ log_intact
   * [[ {{ recovered }} rec >> Check log_intact ;; rec ]]
  }} xrecover rec >> xrecover rec.
Proof.
  intros.
  apply idempotent_ok.
  apply recover_preserves.
Qed.
