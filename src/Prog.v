Require Import Arith.
Require Import Word.
Require Import Bytes.
Require Import FunctionalExtensionality.
Require Import Eqdep_dec.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Omega.
Require Import List.
Require Import Mem.
Import ListNotations.

Set Implicit Arguments.

(** * The programming language *)

Notation "'valubytes_real'" := 4096. (* 4KB *)
Notation "'valulen_real'" := (valubytes_real * 8)%nat.

Module Type VALULEN.
  Parameter valulen : nat.
  Parameter valubytes : nat.
  Axiom valulen_is : valulen = valulen_real.
  Axiom valubytes_is : valubytes = valubytes_real.
End VALULEN.

Module Valulen : VALULEN.
  Definition valulen := valulen_real.
  Definition valubytes := valubytes_real.
  Theorem valulen_is: valulen = valulen_real.
  Proof.
    auto.
  Qed.
  Theorem valubytes_is: valubytes = valubytes_real.
  Proof.
    auto.
  Qed.
End Valulen.

Definition addrlen := 64.
Notation "'valulen'" := (Valulen.valulen).
Notation "'valubytes'" := (Valulen.valubytes).
Notation "'valulen_is'" := (Valulen.valulen_is).
Notation "'valubytes_is'" := (Valulen.valubytes_is).

Notation "'addr'" := (word addrlen).
Notation "'valu'" := (word valulen).
Definition addr_eq_dec := @weq addrlen.

Definition valu2bytes (v : valu) : bytes valubytes.
  refine (@word2bytes valulen valubytes _ v).
  rewrite valulen_is. rewrite valubytes_is. reflexivity.
Defined.

Definition bytes2valu (v : bytes valubytes) : valu.
  rewrite valulen_is.
  unfold bytes in *.
  rewrite valubytes_is in *.
  exact v.
Defined.

Theorem valu2bytes2valu : forall v, valu2bytes (bytes2valu v) = v.
Proof.
  unfold valu2bytes, bytes2valu, eq_rec_r, eq_rec.
  intros.
  rewrite eq_rect_word_mult.
  rewrite eq_rect_nat_double.
  generalize dependent v.
  rewrite valubytes_is.
  rewrite valulen_is.
  intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Theorem bytes2valu2bytes : forall v, bytes2valu (valu2bytes v) = v.
Proof.
  unfold valu2bytes, bytes2valu, eq_rec_r, eq_rec.
  intros.
  rewrite eq_rect_word_mult.
  rewrite eq_rect_nat_double.
  generalize dependent v.
  rewrite valubytes_is.
  rewrite valulen_is.
  intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Theorem valulen_wordToNat_natToWord : # (natToWord addrlen valulen) = valulen.
Proof.
  rewrite valulen_is.
  compute.
  reflexivity.
Qed.

(* tight bound for valulen *)
Theorem valulen_bound : valulen < pow2 16.
Proof.
  eapply Nat.lt_le_trans with (m := pow2 15 + 1).
  rewrite valulen_is.
  compute; auto.
  apply pow2_le_S.
Qed.


Definition wringaddr := wring addrlen.
Add Ring wringaddr : wringaddr (decidable (weqb_sound addrlen), constants [wcst]).

Inductive mobj :=
| MObj (T : Type) (v : T).

Inductive prog (T: Type) :=
| Done (v: T)
| Read (a: addr) (rx: valu -> prog T)
| Write (a: addr) (v: valu) (rx: unit -> prog T)
| Sync (a: addr) (rx: unit -> prog T)
| Trim (a: addr) (rx: unit -> prog T)
| MGet (i: nat) (rx: mobj -> prog T)
| MPut (i: nat) (o: mobj) (rx: unit -> prog T).

Definition progseq (A B:Type) (a:B->A) (b:B) := a b.
Definition pair_args_helper (A B C:Type) (f: A->B->C) (x: A*B) := f (fst x) (snd x).
Notation "^( a )" := (pair a tt).
Notation "^( a , .. , b )" := (pair a .. (pair b tt) .. ).

Notation "p1 ;; p2" := (progseq p1 (fun _: unit => p2)) (at level 60, right associativity).
Notation "x <- p1 ; p2" := (progseq p1 (fun x => p2)) (at level 60, right associativity).
Notation "'let^' ( a ) <- p1 ; p2" :=
  (progseq p1
    (pair_args_helper (fun a (_:unit) => p2))
  )
  (at level 60, right associativity, a ident).
Notation "'let^' ( a , .. , b ) <- p1 ; p2" :=
  (progseq p1
    (pair_args_helper (fun a => ..
      (pair_args_helper (fun b (_:unit) => p2))
    ..))
  )
  (at level 60, right associativity, a closed binder, b closed binder).


Notation "'valuset'" := (valu * list valu)%type.

Definition valuset_list (vs : valuset) := fst vs :: snd vs.


Inductive outcome (T: Type) :=
| Failed
| Finished (d: @mem addr (@weq addrlen) valuset) (m: @mem _ eq_nat_dec mobj) (v: T)
| Crashed (d: @mem addr (@weq addrlen) valuset).

Inductive step (T: Type) : @mem _ (@weq addrlen) _ -> @mem _ eq_nat_dec mobj -> prog T ->
                           @mem _ (@weq addrlen) _ -> @mem _ eq_nat_dec mobj -> prog T -> Prop :=
| StepRead : forall d m a rx v x, d a = Some (v, x) ->
  step d m (Read a rx) d m (rx v)
| StepWrite : forall d m a rx v v0 x, d a = Some (v0, x) ->
  step d m (Write a v rx) (upd d a (v, v0 :: x)) m (rx tt)
| StepSync : forall d m a rx v l, d a = Some (v, l) ->
  step d m (Sync a rx) (upd d a (v, nil)) m (rx tt)
| StepTrim : forall d m a rx vs vs', d a = Some vs ->
  step d m (Trim a rx) (upd d a vs') m (rx tt)
| StepMGet : forall d m i rx v, m i = Some v ->
  step d m (MGet i rx) d m (rx v)
| StepMPut : forall d m i rx v,
  step d m (MPut i v rx) d (upd m i v) (rx tt).

Inductive exec (T: Type) : mem -> mem -> prog T -> outcome T -> Prop :=
| XStep : forall d d' m m' p p' out, step d m p d' m' p' ->
  exec d' m' p' out ->
  exec d m p out
| XFail : forall d m p, (~exists d' m' p', step d m p d' m' p') -> (~exists r, p = Done r) ->
  exec d m p (Failed T)
| XCrash : forall d m p, exec d m p (Crashed T d)
| XDone : forall d m v, exec d m (Done v) (Finished d m v).

Hint Constructors exec.
Hint Constructors step.


Inductive recover_outcome (TF TR: Type) :=
| RFailed
| RFinished (d: @mem addr (@weq addrlen) valuset) (m: @mem _ eq_nat_dec mobj) (v: TF)
| RRecovered (d: @mem addr (@weq addrlen) valuset) (m: @mem _ eq_nat_dec mobj) (v: TR).

Definition possible_crash {A : Type} {eq : DecEq A} (d d' : @mem A eq valuset) : Prop :=
  forall a,
  (d a = None /\ d' a = None) \/
  (exists vs v', d a = Some vs /\ d' a = Some (v', nil) /\ In v' (valuset_list vs)).

Inductive exec_recover (TF TR: Type)
  : mem -> mem -> prog TF -> prog TR -> recover_outcome TF TR -> Prop :=
| XRFail : forall d m p1 p2, exec d m p1 (Failed TF)
  -> exec_recover d m p1 p2 (RFailed TF TR)
| XRFinished : forall d m p1 p2 d' m' (v: TF), exec d m p1 (Finished d' m' v)
  -> exec_recover d m p1 p2 (RFinished TR d' m' v)
| XRCrashedFailed : forall d m p1 p2 d' d'r, exec d m p1 (Crashed TF d')
  -> possible_crash d' d'r
  -> @exec_recover TR TR d'r empty_mem p2 p2 (RFailed TR TR)
  -> exec_recover d m p1 p2 (RFailed TF TR)
| XRCrashedFinished : forall d m p1 p2 d' d'r d'' m'' (v: TR), exec d m p1 (Crashed TF d')
  -> possible_crash d' d'r
  -> @exec_recover TR TR d'r empty_mem p2 p2 (RFinished TR d'' m'' v)
  -> exec_recover d m p1 p2 (RRecovered TF d'' m'' v)
| XRCrashedRecovered : forall d m p1 p2 d' d'r d'' m'' (v: TR), exec d m p1 (Crashed TF d')
  -> possible_crash d' d'r
  -> @exec_recover TR TR d'r empty_mem p2 p2 (RRecovered TR d'' m'' v)
  -> exec_recover d m p1 p2 (RRecovered TF d'' m'' v).

Hint Constructors exec_recover.


Module Addr_as_OT <: UsualOrderedType.
  Definition t := addr.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition lt := @wlt addrlen.

  Lemma lt_trans: forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros.
    apply wlt_lt in H; apply wlt_lt in H0.
    apply lt_wlt.
    omega.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq; intros.
    apply wlt_lt in H.
    intro He; subst; omega.
  Qed.

  Definition compare x y : Compare lt eq x y.
    unfold lt, eq.
    destruct (wlt_dec x y); [ apply LT; auto | ].
    destruct (weq x y); [ apply EQ; auto | ].
    apply GT. apply le_neq_lt; auto.
  Defined.

  Definition eq_dec := @weq addrlen.
End Addr_as_OT.


Lemma addrlen_valulen: addrlen + (valulen - addrlen) = valulen.
Proof.
  rewrite valulen_is; auto.
Qed.

Definition addr2valu (a: addr) : valu.
  set (zext a (valulen-addrlen)) as r.
  rewrite addrlen_valulen in r.
  apply r.
Defined.

Definition valu2addr (v: valu) : addr.
  rewrite <- addrlen_valulen in v.
  apply (split1 addrlen (valulen-addrlen) v).
Defined.

Lemma addr2valu2addr: forall a,
  valu2addr (addr2valu a) = a.
Proof.
  unfold valu2addr, addr2valu.
  unfold eq_rec_r, eq_rec.
  intros.
  rewrite <- addrlen_valulen.
  rewrite <- eq_rect_eq_dec; try apply eq_nat_dec.
  rewrite <- eq_rect_eq_dec; try apply eq_nat_dec.
  apply split1_combine.
Qed.

Lemma addr2valu_inj : forall a b,
  addr2valu a = addr2valu b ->
  a = b.
Proof.
  unfold valu2addr, addr2valu.
  unfold eq_rec_r, eq_rec.
  rewrite <- addrlen_valulen.
  intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec) in H.
  rewrite <- (eq_rect_eq_dec eq_nat_dec) in H.
  unfold zext in *.
  apply combine_inj in H.
  intuition.
Qed.


Global Opaque addr2valu.
Global Opaque valu2addr.
(* Once this bug is fixed:
     https://coq.inria.fr/bugs/show_bug.cgi?id=3731
   we should enable this rewrite hint:
Hint Rewrite addr2valu2addr.
*)
