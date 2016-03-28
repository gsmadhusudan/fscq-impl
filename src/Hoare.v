Require Import Mem.
Require Import Prog.
Require Import Pred PredCrash.
Require Import List.
Require Import Morphisms.
Require Import Word.
Require Import Hashmap.

Set Implicit Arguments.


(** ** Hoare logic *)

Definition donecond (T: Type) := T -> @mem addr (@weq addrlen) valuset -> Prop.

Definition corr2 (T: Type) (pre: hashmap -> donecond T -> pred -> pred) (p: prog T) :=
  forall done crash m hm out, pre hm done crash m
  -> exec m hm p out
  -> (exists m' hm' v, out = Finished m' hm' v /\ done v m') \/
     (exists m' hm', out = Crashed T m' hm' /\ crash m').

Notation "{{ pre }} p" := (corr2 pre%pred p)
  (at level 0, p at level 60).


Definition corr3 (TF TR: Type) (pre: hashmap -> donecond TF -> donecond TR -> pred)
                 (p1: prog TF) (p2: prog TR) :=
  forall done crashdone m hm out, pre hm done crashdone m
  -> exec_recover m hm p1 p2 out
  -> (exists m' hm' v, out = RFinished TR m' hm' v /\ done v m') \/
     (exists m' hm' v, out = RRecovered TF m' hm' v /\ crashdone v m').

Notation "{{ pre }} p1 >> p2" := (corr3 pre%pred p1 p2)
  (at level 0, p1 at level 60, p2 at level 60).

Notation "'RET' : r post" :=
  (fun F =>
    (fun r => (F * post)%pred)
  )%pred
  (at level 0, post at level 90, r at level 0, only parsing).

Notation "'RET' : ^( ra , .. , rb ) post" :=
  (fun F =>
    (pair_args_helper (fun ra => ..
      (pair_args_helper (fun rb (_:unit) => (F * post)%pred))
    ..))
  )%pred
  (at level 0, post at level 90, ra closed binder, rb closed binder, only parsing).

(**
  * Underlying CHL that allows pre, post, and crash conditions to state
  * propositions about the hashmap machine state.
  * The pre-hashmap must be a subset of both the post- and crash-hashmaps.
  *)
Notation "{< e1 .. e2 , 'PRE' : hm pre 'POST' : hm' post 'CRASH' : hm_crash crash >} p1" :=
  (forall T (rx: _ -> prog T), corr2
   (fun hm done_ crash_ =>
    (exis (fun e1 => .. (exis (fun e2 =>
     exists F_,
     F_ * pre *
     [[ forall r_ ,
        {{ fun hm' done'_ crash'_ =>
           post F_ r_ * [[ exists l, hashmap_subset l hm hm' ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]]
        }} rx r_ ]] *
     [[ forall (hm_crash : hashmap),
        (F_ * crash * [[ exists l, hashmap_subset l hm hm_crash ]])%pred =p=> crash_ ]]
     )) .. ))
   )%pred
   (p1 rx)%pred)
  (at level 0, p1 at level 60,
    hm at level 0, hm' at level 0, hm_crash at level 0,
    e1 closed binder, e2 closed binder).

(**
  * Same as {{< ... >}}, except that the specified pre, post, and
  * crash conditions cannot state additional propositions about the
  * hashmap machine state. This can be used for any programs that
  * don't need to reason about the contents of the hashmap, including
  * programs that don't contain a Hash step
  * reason about the contents of the hashmap.
  *)
Notation "{< e1 .. e2 , 'PRE' pre 'POST' post 'CRASH' crash >} p1" :=
  (forall T (rx: _ -> prog T), corr2
   (fun hm done_ crash_ =>
    (exis (fun e1 => .. (exis (fun e2 =>
     exists F_,
     F_ * pre *
     [[ forall r_ ,
        {{ fun hm' done'_ crash'_ =>
           post F_ r_ * [[ exists l, hashmap_subset l hm hm' ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]]
        }} rx r_ ]] *
     [[ forall (hm_crash : hashmap),
        (F_ * crash * [[ exists l, hashmap_subset l hm hm_crash ]]) =p=> crash_ ]]
     )) .. ))
   )%pred
   (p1 rx)%pred)
  (at level 0, p1 at level 60,
    e1 closed binder, e2 closed binder).

(**
 * The {!< .. >!} notation is the same as above, except it lacks a frame
 * predicate.  This is useful for bootstrapping-style programs.
 *)
Notation "{!< e1 .. e2 , 'PRE' pre 'POST' post 'CRASH' crash >!} p1" :=
  (forall T (rx: _ -> prog T), corr2
   (fun hm done_ crash_ =>
    (exis (fun e1 => .. (exis (fun e2 =>
     pre *
     [[ forall r_,
        {{ fun hm' done'_ crash'_ =>
           post emp r_ * [[ exists l, hashmap_subset l hm hm' ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]]
        }} rx r_ ]] *
     [[ forall (hm_crash : hashmap),
        crash * [[ exists l, hashmap_subset l hm hm_crash ]] =p=> crash_ ]]
     )) .. ))
   )%pred
   (p1 rx)%pred)
  (at level 0, p1 at level 60, e1 binder, e2 binder).

Definition forall_helper T (p : T -> Prop) :=
  forall v, p v.

Notation "{<< e1 .. e2 , 'PRE' : hm pre 'POST' : hm' post 'REC' : hm_crash crash >>} p1 >> p2" :=
  (forall_helper (fun e1 => .. (forall_helper (fun e2 =>
   exists idemcrash,
   forall TF TR (rxOK: _ -> prog TF) (rxREC: _ -> prog TR),
   corr3
   (fun hm done_ crashdone_ =>
     exists F_,
     F_ * pre *
     [[ crash_xform F_ =p=> F_ ]] *
     [[ forall r_,
        {{ fun hm' done'_ crash'_ => post F_ r_ *
                                 [[ exists l, hashmap_subset l hm hm' ]] *
                                 [[ done'_ = done_ ]] * [[ crash'_ =p=> F_ * idemcrash ]]
        }} rxOK r_ ]] *
     [[ forall r_,
        {{ fun hm_crash done'_ crash'_ => crash F_ r_ *
                                 [[ exists l, hashmap_subset l hm hm_crash ]] *
                                 [[ done'_ = crashdone_ ]] *
                                 [[ crash'_ =p=> F_ * idemcrash ]]
        }} rxREC r_ ]]
   )%pred
   (p1 rxOK)%pred
   (p2 rxREC)%pred)) .. ))
  (at level 0, p1 at level 60, p2 at level 60, e1 binder, e2 binder,
   hm at level 0, hm' at level 0, hm_crash at level 0,
   post at level 1, crash at level 1).


Notation "{<< e1 .. e2 , 'PRE' pre 'POST' post 'REC' crash >>} p1 >> p2" :=
  (forall_helper (fun e1 => .. (forall_helper (fun e2 =>
   exists idemcrash,
   forall TF TR (rxOK: _ -> prog TF) (rxREC: _ -> prog TR),
   corr3
   (fun hm done_ crashdone_ =>
     exists F_,
     F_ * pre *
     [[ crash_xform F_ =p=> F_ ]] *
     [[ forall r_,
        {{ fun hm' done'_ crash'_ => post F_ r_ *
                                 [[ exists l, hashmap_subset l hm hm' ]] *
                                 [[ done'_ = done_ ]] * [[ crash'_ =p=> F_ * idemcrash ]]
        }} rxOK r_ ]] *
     [[ forall r_,
        {{ fun hm_crash done'_ crash'_ => crash F_ r_ *
                                 [[ exists l, hashmap_subset l hm hm_crash ]] *
                                 [[ done'_ = crashdone_ ]] *
                                 [[ crash'_ * [[ exists l, hashmap_subset l hm hm_crash ]] =p=> F_ * idemcrash ]]
        }} rxREC r_ ]]
   )%pred
   (p1 rxOK)%pred
   (p2 rxREC)%pred)) .. ))
  (at level 0, p1 at level 60, p2 at level 60, e1 binder, e2 binder,
   post at level 1, crash at level 1).

Inductive corr3_result {A B : Type} :=
  | Complete : A -> corr3_result
  | Recover : B -> corr3_result.

(* TODO: Like above notations, allow propositions about hashmap. *)
Notation "{<<< e1 .. e2 , 'PRE' pre 'POST' post >>>} p1 >> p2" :=
  (forall_helper (fun e1 => .. (forall_helper (fun e2 =>
   exists idemcrash,
   forall TF TR (rxOK: _ -> prog TF) (rxREC: _ -> prog TR),
   corr3
   (fun done_ crashdone_ =>
     exists F_,
     F_ * pre *
     [[ crash_xform F_ =p=> F_ ]] *
     [[ forall r_,
        {{ fun done'_ crash'_ => post F_ (Complete r_) *
                                 [[ done'_ = done_ ]] * [[ crash'_ =p=> F_ * idemcrash ]]
        }} rxOK r_ ]] *
     [[ forall r_,
        {{ fun done'_ crash'_ => post F_ (Recover r_) *
                                 [[ done'_ = crashdone_ ]] * [[ crash'_ =p=> F_ * idemcrash ]]
        }} rxREC r_ ]]
   )%pred
   (p1 rxOK)%pred
   (p2 rxREC)%pred)) .. ))
  (at level 0, p1 at level 60, p2 at level 60, e1 binder, e2 binder,
   post at level 1).


Theorem pimpl_ok2:
  forall T pre pre' (pr: prog T),
  {{pre'}} pr ->
  (forall hm done crash, pre hm done crash =p=> pre' hm done crash) ->
  {{pre}} pr.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.

Theorem pimpl_ok3:
  forall TF TR pre pre' (p: prog TF) (r: prog TR),
  {{pre'}} p >> r ->
  (forall hm done crashdone, pre hm done crashdone =p=> pre' hm done crashdone) ->
  {{pre}} p >> r.
Proof.
  unfold corr3; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.

Theorem pimpl_ok2_cont :
  forall T pre pre' A (k : A -> prog T) x y,
  {{pre'}} k y ->
  (forall hm done crash, pre hm done crash =p=> pre' hm done crash) ->
  (forall hm done crash, pre hm done crash =p=> exists F, F * [[x = y]]) ->
  {{pre}} k x.
Proof.
  unfold corr2, pimpl; intros.
  edestruct H1; eauto.
  eapply sep_star_lift_l in H4; [|instantiate (1:=([x=y])%pred)].
  unfold lift in *; subst; eauto.
  firstorder.
Qed.

Theorem pimpl_ok3_cont :
  forall TF TR pre pre' A (k : A -> prog TF) x y (r: prog TR),
  {{pre'}} k y >> r ->
  (forall hm done crashdone, pre hm done crashdone =p=> pre' hm done crashdone) ->
  (forall hm done crashdone, pre hm done crashdone =p=> exists F, F * [[x = y]]) ->
  {{pre}} k x >> r.
Proof.
  unfold corr3, pimpl; intros.
  edestruct H1; eauto.
  eapply sep_star_lift_l in H4; [|instantiate (1:=([x=y])%pred)].
  unfold lift in *; subst; eauto.
  firstorder.
Qed.

Theorem pimpl_pre2:
  forall T pre pre' (pr: prog T),
  (forall hm done crash, pre hm done crash =p=> [{{pre' hm done crash}} pr])
  -> (forall hm done crash, pre hm done crash =p=> pre' hm done crash hm done crash)
  -> {{pre}} pr.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.

Theorem pimpl_pre3:
  forall TF TR pre pre' (p: prog TF) (r: prog TR),
  (forall hm done crashdone, pre hm done crashdone =p=> [{{pre' hm done crashdone}} p >> r])
  -> (forall hm done crashdone, pre hm done crashdone =p=> pre' hm done crashdone hm done crashdone)
  -> {{pre}} p >> r.
Proof.
  unfold corr3; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.

Theorem pre_false2:
  forall T pre (p: prog T),
  (forall hm done crash, pre hm done crash =p=> [False])
  -> {{ pre }} p.
Proof.
  unfold corr2; intros; exfalso.
  eapply H; eauto.
Qed.

Theorem pre_false3:
  forall TF TR pre (p: prog TF) (r: prog TR),
  (forall hm done crashdone, pre hm done crashdone =p=> [False])
  -> {{ pre }} p >> r.
Proof.
  unfold corr3; intros; exfalso.
  eapply H; eauto.
Qed.


Theorem corr2_exists:
  forall T R pre (p: prog R),
  (forall (a:T), {{ fun hm done crash => pre hm done crash a }} p)
  -> {{ fun hm done crash => exists a:T, pre hm done crash a }} p.
Proof.
  unfold corr2; intros.
  destruct H0.
  eapply H; eauto.
Qed.

Theorem corr3_exists:
  forall T RF RR pre (p: prog RF) (r: prog RR),
  (forall (a:T), {{ fun hm done crashdone => pre hm done crashdone a }} p >> r)
  -> {{ fun hm done crashdone => exists a:T, pre hm done crashdone a }} p >> r.
Proof.
  unfold corr3; intros.
  destruct H0.
  eapply H; eauto.
Qed.

Theorem corr2_forall: forall T R pre (p: prog R),
  {{ fun hm done crash => exists a:T, pre hm done crash a }} p
  -> forall (a:T), {{ fun hm done crash => pre hm done crash a }} p.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  exists a; eauto.
Qed.

Theorem corr3_forall: forall T RF RR pre (p: prog RF) (r: prog RR),
  {{ fun hm done crashdone => exists a:T, pre hm done crashdone a }} p >> r
  -> forall (a:T), {{ fun hm done crashdone => pre hm done crashdone a }} p >> r.
Proof.
  unfold corr3; intros.
  eapply H; eauto.
  exists a; eauto.
Qed.

Instance corr2_proper {T : Type} :
  Proper (pointwise_relation hashmap
            (pointwise_relation (donecond T) (pointwise_relation pred piff))
          ==> eq ==> iff) (@corr2 T).
Proof.
  intros a b Hab x y Hxy; subst.
  split; intros; eapply pimpl_ok2; try eassumption; apply Hab.
Qed.

Instance corr3_proper {T R : Type} :
  Proper (pointwise_relation hashmap
            (pointwise_relation (donecond T) (pointwise_relation (donecond R) piff))
          ==> eq ==> eq ==> iff) (@corr3 T R).
Proof.
  intros a b Hab x y Hxy p q Hpq; subst.
  split; intros; eapply pimpl_ok3; try eassumption; apply Hab.
Qed.
