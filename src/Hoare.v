Require Import Mem.
Require Import Prog.
Require Import Pred PredCrash.
Require Import List.
Require Import Morphisms.
Require Import Word.
Require Import Arith.

Set Implicit Arguments.


(** ** Hoare logic *)

Definition donecond (T: Type) := T -> @mem addr (@weq addrlen) valuset -> @mem nat eq_nat_dec mobj -> Prop.

Definition corr2 (T: Type) (pre: donecond T -> pred -> @mem _ (@weq addrlen) valuset -> @mem _ eq_nat_dec mobj -> Prop) (p: prog T) :=
  forall done crash d m out, pre done crash d m
  -> exec d m p out
  -> (exists d' m' v, out = Finished d' m' v /\ done v d' m') \/
     (exists d', out = Crashed T d' /\ crash d').

Notation "{{ pre }} p" := (corr2 pre p)
  (at level 0, p at level 60).


Definition corr3 (TF TR: Type) (pre: donecond TF -> donecond TR -> @mem _ (@weq addrlen) valuset -> @mem _ eq_nat_dec mobj -> Prop)
                 (p1: prog TF) (p2: prog TR) :=
  forall done crashdone d m out, pre done crashdone d m
  -> exec_recover d m p1 p2 out
  -> (exists d' m' v, out = RFinished TR d' m' v /\ done v d' m') \/
     (exists d' m' v, out = RRecovered TF d' m' v /\ crashdone v d' m').

Notation "{{ pre }} p1 >> p2" := (corr3 pre p1 p2)
  (at level 0, p1 at level 60, p2 at level 60).

Notation "'RET' : r post" :=
  (fun r => post)
  (at level 0, post at level 90, r at level 0, only parsing).

Notation "'RET' : ^( ra , .. , rb ) post" :=
  (pair_args_helper (fun ra => ..
    (pair_args_helper (fun rb (_:unit) => post))
  ..))
  (at level 0, post at level 90, ra closed binder, rb closed binder, only parsing).

Notation "{< D M || e1 .. e2 , 'PRE' pre 'POST' post 'CRASH' crash >} p1" :=
  (forall T (rx: _ -> prog T), corr2
   (fun done_ crash_ disk_ mem_ =>
    (exis (fun e1 => .. (exis (fun e2 =>
     (fun D M => pre) disk_ mem_ /\
     ( forall r_,
       {{ fun done'_ crash'_ disk'_ mem'_ =>
          (fun D M => post) disk'_ mem'_ r_ /\
          done'_ = done_ /\
          crash'_ = crash_
       }} rx r_ ) /\
     (fun D => crash) =p=> (fun D => crash_)
     )) .. ))
   )%pred
   (p1 rx)%pred)
  (at level 0, p1 at level 60, e1 binder, e2 binder).


Definition forall_helper T (p : T -> Prop) :=
  forall v, p v.

Notation "{<< D M || e1 .. e2 , 'PRE' pre 'POST' post 'REC' crash >>} p1 >> p2" :=
  (forall_helper (fun e1 => .. (forall_helper (fun e2 =>
   exists idemcrash,
   forall TF TR (rxOK: _ -> prog TF) (rxREC: _ -> prog TR),
   corr3
   (fun done_ crashdone_ disk_ mem_ =>
     (fun D M => pre) disk_ mem_ /\
     ( forall r_,
       {{ fun done'_ crash'_ disk'_ mem'_ =>
          (fun D M => post) disk'_ mem'_ r_ /\
          done'_ = done_ /\
          crash'_ =p=> idemcrash
       }} rxOK r_ ) /\
     ( forall r_,
       {{ fun done'_ crash'_ disk'_ mem'_ =>
          (fun D => crash) disk'_ r_ /\
          done'_ = crashdone_ /\
          crash'_ =p=> idemcrash
       }} rxREC r_ )
   )%pred
   (p1 rxOK)%pred
   (p2 rxREC)%pred)) .. ))
  (at level 0, p1 at level 60, p2 at level 60, e1 binder, e2 binder,
   post at level 1, crash at level 1).

Inductive corr3_result {A B : Type} :=
  | Complete : A -> corr3_result
  | Recover : B -> corr3_result.

Notation "{<<< D M || e1 .. e2 , 'PRE' pre 'POST' post >>>} p1 >> p2" :=
  (forall_helper (fun e1 => .. (forall_helper (fun e2 =>
   exists idemcrash,
   forall TF TR (rxOK: _ -> prog TF) (rxREC: _ -> prog TR),
   corr3
   (fun done_ crashdone_ disk_ mem_ =>
     (fun D M => pre) disk_ mem_ /\
     ( forall r_,
       {{ fun done'_ crash'_ disk'_ mem'_ =>
          (fun D M => post) disk'_ mem'_ (Complete r_) /\
          done'_ = done_ /\
          crash'_ =p=> idemcrash
       }} rxOK r_ ) /\
     ( forall r_,
       {{ fun done'_ crash'_ disk'_ mem'_ =>
          (fun D M => post) disk'_ mem'_ (Recover r_) /\
          done'_ = crashdone_ /\
          crash'_ =p=> idemcrash
       }} rxREC r_ )
   )%pred
   (p1 rxOK)%pred
   (p2 rxREC)%pred)) .. ))
  (at level 0, p1 at level 60, p2 at level 60, e1 binder, e2 binder,
   post at level 1).


Theorem pimpl_ok2:
  forall T (pre pre' : _ -> _ -> _ -> _ -> Prop) (pr: prog T),
  {{pre'}} pr ->
  (forall done crash d m, pre done crash d m -> pre' done crash d m) ->
  {{pre}} pr.
Proof.
  unfold corr2; eauto.
Qed.

Theorem pimpl_ok3:
  forall TF TR (pre pre' : _ -> _ -> _ -> _ -> Prop) (p: prog TF) (r: prog TR),
  {{pre'}} p >> r ->
  (forall done crashdone d m, pre done crashdone d m -> pre' done crashdone d m) ->
  {{pre}} p >> r.
Proof.
  unfold corr3; eauto.
Qed.

Theorem pimpl_ok2_cont :
  forall T (pre pre' : _ -> _ -> _ -> _ -> Prop) A (k : A -> prog T) x y,
  {{pre'}} k y ->
  (forall done crash d m, pre done crash d m -> pre' done crash d m) ->
  (forall done crash d m, pre done crash d m -> x = y) ->
  {{pre}} k x.
Proof.
  unfold corr2; intros.
  edestruct H1; eauto.
Qed.

Theorem pimpl_ok3_cont :
  forall TF TR (pre pre' : _ -> _ -> _ -> _ -> Prop) A (k : A -> prog TF) x y (r: prog TR),
  {{pre'}} k y >> r ->
  (forall done crashdone d m, pre done crashdone d m -> pre' done crashdone d m) ->
  (forall done crashdone d m, pre done crashdone d m -> x = y) ->
  {{pre}} k x >> r.
Proof.
  unfold corr3; intros.
  edestruct H1; eauto.
Qed.

Theorem pimpl_pre2:
  forall T (pre : _ -> _ -> _ -> _ -> Prop) pre' (pr: prog T),
  (forall done crash d m, pre done crash d m -> {{pre' done crash}} pr)
  -> (forall done crash d m, pre done crash d m -> pre' done crash done crash d m)
  -> {{pre}} pr.
Proof.
  unfold corr2; eauto.
Qed.

Theorem pimpl_pre3:
  forall TF TR (pre : _ -> _ -> _ -> _ -> Prop) pre' (p: prog TF) (r: prog TR),
  (forall done crashdone d m, pre done crashdone d m -> {{pre' done crashdone}} p >> r)
  -> (forall done crashdone d m, pre done crashdone d m -> pre' done crashdone done crashdone d m)
  -> {{pre}} p >> r.
Proof.
  unfold corr3; eauto.
Qed.

Theorem pre_false2:
  forall T (pre : _ -> _ -> _ -> _ -> Prop) (p: prog T),
  (forall done crash d m, pre done crash d m -> False)
  -> {{ pre }} p.
Proof.
  unfold corr2; intros; exfalso; eauto.
Qed.

Theorem pre_false3:
  forall TF TR (pre : _ -> _ -> _ -> _ -> Prop) (p: prog TF) (r: prog TR),
  (forall done crashdone d m, pre done crashdone d m -> False)
  -> {{ pre }} p >> r.
Proof.
  unfold corr3; intros; exfalso; eauto.
Qed.


Theorem corr2_exists:
  forall T R pre (p: prog R),
  (forall (a:T), {{ fun done crash d m => pre done crash d m a }} p)
  -> {{ fun done crash d m => exists a:T, pre done crash d m a }} p.
Proof.
  unfold corr2; intros.
  destruct H0.
  eauto.
Qed.

Theorem corr3_exists:
  forall T RF RR pre (p: prog RF) (r: prog RR),
  (forall (a:T), {{ fun done crashdone d m => pre done crashdone d m a }} p >> r)
  -> {{ fun done crashdone d m => exists a:T, pre done crashdone d m a }} p >> r.
Proof.
  unfold corr3; intros.
  destruct H0.
  eauto.
Qed.

Theorem corr2_forall: forall T R pre (p: prog R),
  {{ fun done crash d m => exists a:T, pre done crash d m a }} p
  -> forall (a:T), {{ fun done crash d m => pre done crash d m a }} p.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
Qed.

Theorem corr3_forall: forall T RF RR pre (p: prog RF) (r: prog RR),
  {{ fun done crashdone d m => exists a:T, pre done crashdone d m a }} p >> r
  -> forall (a:T), {{ fun done crashdone d m => pre done crashdone d m a }} p >> r.
Proof.
  unfold corr3; intros.
  eapply H; eauto.
Qed.


(*
Instance corr2_proper {T : Type} :
  Proper (pointwise_relation (donecond T) (pointwise_relation pred piff)
          ==> eq ==> iff) (@corr2 T).
Proof.
  intros a b Hab x y Hxy; subst.
  split; intros; eapply pimpl_ok2; try eassumption; apply Hab.
Qed.

Instance corr3_proper {T R : Type} :
  Proper (pointwise_relation (donecond T) (pointwise_relation (donecond R) piff)
          ==> eq ==> eq ==> iff) (@corr3 T R).
Proof.
  intros a b Hab x y Hxy p q Hpq; subst.
  split; intros; eapply pimpl_ok3; try eassumption; apply Hab.
Qed.
*)
