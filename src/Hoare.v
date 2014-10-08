Require Import Prog.
Require Import Pred.

Set Implicit Arguments.


(** ** Hoare triples *)

Definition postok (R: Set) (out: @outcome R) (post: R -> pred) (crash: pred) :=
  match out with
  | Failed => False
  | Crashed m => crash m
  | Finished v m => post v m
  end.

Definition corr (R: Set) (p1: prog R) (p2: prog unit)
                (pre: pred) (post: R -> pred) (crash: pred) :=
  forall m out,
  pre m ->
  exec_recover m p1 p2 out ->
  postok out post crash.

Notation "{{ pre }} p1 >> p2 {{ post >> crash }}" := (corr p1 p2 pre%pred post%pred crash%pred)
  (at level 70, p1 at level 60, p2 at level 60).

Theorem pimpl_ok:
  forall R pre pre' (pr: prog R) rec (post post': R -> pred) crash crash',
  ({{pre'}} pr >> rec {{post' >> crash'}}) ->
  (pre ==> pre') ->
  (forall r, post' r ==> post r) ->
  (crash' ==> crash) ->
  {{pre}} pr >> rec {{post >> crash}}.
Proof.
  unfold corr; intros.
  destruct out; unfold postok.
  - eapply (H _ Failed); eauto.
  - apply H2. eapply (H _ (Crashed _)); eauto.
  - apply H1. eapply (H _ (Finished _ _)); eauto.
Qed.

Theorem pimpl_ok_cont :
  forall pre pre' A R (k : A -> prog R) rec x y post post' crash crash',
  {{pre'}} k y >> rec {{post' >> crash'}} ->
  (pre ==> pre') ->
  (pre ==> exists F, F * [[x = y]]) ->
  (forall rr, post' rr ==> post rr) ->
  (crash' ==> crash) ->
  {{pre}} k x >> rec {{post >> crash}}.
Proof.
  unfold corr, pimpl; intros.
  remember (H1 m H4) as Hpre; clear HeqHpre.
  destruct Hpre.
  eapply sep_star_lift_l in H6; [| instantiate (1:=([x=y])%pred); firstorder ].
  unfold lift in *; subst.
  destruct out; unfold postok.
  - eapply (H _ Failed); eauto.
  - apply H3. eapply (H _ (Crashed _)); eauto.
  - apply H2. eapply (H _ (Finished _ _)); eauto.
Qed.
