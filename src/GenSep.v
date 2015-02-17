Require Import Prog.
Require Import List.
Require Import Array.
Require Import Pred.
Require Import FunctionalExtensionality.
Require Import Word.
Require Import WordAuto.
Require Import Omega.
Require Import Ring.
Require Import SepAuto.
Require Import ListPred.

Set Implicit Arguments.

(**
 * This module is meant to generalize separation logic to arbitrary functions
 * from some address-like thing to some value-like thing.  The motivating use
 * case is in files: we want to think of the disk as a mapping from inode numbers
 * to file objects, where each file object includes metadata and the entire file
 * contents.  Current separation logic is not quite good enough, because we want
 * to have values that are bigger than a 512-byte block.
 *)

(**
 * list2mem is meant to convert a list representation of files into a memory-like
 * object that maps inode numbers (list positions) into files (or None, if the
 * inode number is too big).  For now, this always uses [addr] as the index.
 *)
Definition list2mem (A: Type) (l: list A) : @mem addr (@weq addrlen) A :=
  fun a => if (lt_dec #a (length l)) then sel (map (@Some A) l) a else None.

Theorem list2mem_ptsto_bounds: forall A F (l: list A) i x,
  (F * i |-> x)%pred (list2mem l) -> wordToNat i < length l.
Proof.
  intros.
  unfold list2mem in H.
  apply ptsto_valid' in H.
  destruct (lt_dec (wordToNat i) (length l)); auto.
  congruence.
Qed.


Theorem list2mem_oob : forall A (l : list A) i,
  wordToNat i >= length l
  -> (list2mem l) i = None.
Proof.
  unfold list2mem; intros.
  destruct (lt_dec (wordToNat i) (length l)); auto.
  omega.
Qed.


Theorem list2mem_inbound: forall A F (l : list A) i x,
  (F * i |-> x)%pred (list2mem l)
  -> wordToNat i < length l.
Proof.
  intros.
  destruct (lt_dec (wordToNat i) (length l)); auto; exfalso.
  apply not_lt in n.
  apply list2mem_oob in n.
  apply ptsto_valid' in H.
  rewrite H in n.
  inversion n.
Qed.


Theorem list2mem_sel: forall A {defA : Defaultable A} F (l: list A) i x,
  (F * i |-> x)%pred (list2mem l)
  -> x = sel l i.
Proof.
  intros.
  assert (wordToNat i < length l).
  eapply list2mem_inbound; eauto.
  unfold list2mem in H.
  apply ptsto_valid' in H.
  erewrite sel_map in H by auto.
  destruct (lt_dec (wordToNat i) (length l)); try omega.
  inversion H; eauto.
Qed.


Lemma listupd_progupd: forall A l i (v : A),
  wordToNat i < length l
  -> list2mem (upd l i v) = Prog.upd (list2mem l) i v.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2mem, sel, upd, Prog.upd.
  autorewrite with core.

  destruct (weq x i).
  subst; destruct (lt_dec #i (length l)); try omega.
  rewrite selN_updN_eq; auto.
  rewrite map_length; auto.
  erewrite selN_updN_ne; auto.
  word2nat_simpl; omega.
Qed.

Theorem list2mem_upd: forall A F (l: list A) i x y,
  (F * i |-> x)%pred (list2mem l)
  -> (F * i |-> y)%pred (list2mem (upd l i y)).
Proof.
  intros.
  rewrite listupd_progupd by (eapply list2mem_inbound; eauto).
  apply sep_star_comm.
  apply sep_star_comm in H.
  eapply ptsto_upd; eauto.
Qed.

Theorem list2mem_cur_upd : forall F (l : list valuset) i x y old,
  (F * i |-> x)%pred (list2mem l)
  -> (F * (exists old, i |-> (y, old)))%pred (list2mem (upd l i (y, old))).
Proof.
  intros.
  rewrite listupd_progupd by (eapply list2mem_inbound; eauto).
  apply sep_star_comm in H.
  eapply ptsto_upd in H.
  eapply pimpl_apply; [|eauto].
  cancel.
Qed.


Theorem listapp_progupd: forall A {defA : Defaultable A} l (a : A) (b : addr),
  length l <= wordToNat b
  -> list2mem (l ++ a :: nil) = Prog.upd (list2mem l) $ (length l) a.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2mem, sel, upd, Prog.upd.

  destruct (wlt_dec x $ (length l)).
  - apply wlt_lt in w.
    erewrite wordToNat_natToWord_bound in w; eauto.
    subst; rewrite selN_map with (defT' := defA).
    destruct (weq x $ (length l)); subst.
    + erewrite wordToNat_natToWord_bound in *; eauto. omega.
    + rewrite selN_map with (defT' := defA); auto.
      rewrite selN_app; auto.
      destruct (lt_dec #x (length l)); try omega.
      destruct (lt_dec #x (length (l ++ a::nil))); auto.
      rewrite app_length in *; omega.
    + rewrite app_length; simpl; omega.
  - destruct (weq x $ (length l)).
    + subst; erewrite selN_map with (defT' := defA).
      rewrite selN_last; auto.
      destruct (lt_dec # ($ (length l)) (length (l ++ a :: nil))); auto.
      rewrite app_length in *; simpl in *.
      erewrite wordToNat_natToWord_bound in n0 by eauto. omega.
      eapply wordToNat_natToWord_bound; eauto.
      erewrite wordToNat_natToWord_bound; eauto.
      rewrite app_length; simpl; omega.
    + apply wle_le in n.
      erewrite wordToNat_natToWord_bound in n; eauto.
      rewrite app_length; simpl.
      repeat erewrite selN_oob; try rewrite map_length; auto.
      destruct (lt_dec #x (length l)); try omega.
      destruct (lt_dec #x (length l + 1)); auto.
      rewrite app_length; simpl; intuition.
      rewrite Nat.add_1_r. apply lt_le_S.
      apply le_lt_or_eq in n; intuition.
      contradict n0; rewrite H0.
      apply wordToNat_inj.
      erewrite wordToNat_natToWord_bound; eauto.
Qed.


Theorem list2mem_app: forall A {defA : Defaultable A}
  (F : @pred addr (@weq addrlen) A) l a (b : addr),
  length l <= wordToNat b
  -> F (list2mem l)
  -> (F * $ (length l) |-> a)%pred (list2mem (l ++ a :: nil)).
Proof.
  intros.
  erewrite listapp_progupd; eauto.
  apply ptsto_upd_disjoint; auto.
  unfold list2mem, sel.
  erewrite wordToNat_natToWord_bound; eauto.
  destruct (lt_dec (length l) (length l)); try omega; auto.
Qed.


Theorem list2mem_removelast_is : forall A {defA : Defaultable A} (l : list A) (b : addr),
  l <> nil -> length l <= wordToNat b
  -> list2mem (removelast l) =
     fun i => if (wlt_dec i $ (length l - 1)) then Some (sel l i) else None.
Proof.
  intros; apply functional_extensionality; intros.
  destruct (wlt_dec x $ (length l - 1)); unfold list2mem, sel.
  - assert (wordToNat x < length l - 1); apply wlt_lt in w.
    erewrite wordToNat_natToWord_bound with (bound:=b) in w by omega; auto.
    rewrite length_removelast by auto.
    rewrite selN_map with (defT' := defA).
    rewrite selN_removelast by omega; auto.
    destruct (lt_dec #x (length l - 1)); try omega; auto.
    rewrite length_removelast by auto; omega.
  - rewrite length_removelast by auto.
    rewrite selN_oob; auto.
    destruct (lt_dec #x (length l - 1)); auto.
    rewrite map_length.
    rewrite length_removelast by auto.
    apply wle_le in n.
    rewrite wordToNat_natToWord_bound with (bound:=b) in n by omega; auto.
Qed.


Theorem list2mem_removelast_list2mem : forall A {defA : Defaultable A} (l : list A) (b : addr),
  l <> nil -> length l <= wordToNat b
  -> list2mem (removelast l) =
     fun i => if (weq i $ (length l - 1)) then None else (list2mem l) i.
Proof.
  intros; apply functional_extensionality; intros.

  erewrite list2mem_removelast_is by eauto.
  unfold list2mem, sel.
  destruct (wlt_dec x $ (length l - 1));
  destruct (weq x $ (length l - 1)); subst; intuition.
  apply wlt_lt in w; omega.
  erewrite selN_map; auto.
  destruct (lt_dec #x (length l)); auto.
  contradict n0. apply wlt_lt in w.
  erewrite wordToNat_natToWord_bound with (bound:=b) in w by omega. omega.
  apply wlt_lt in w; rewrite wordToNat_natToWord_bound with (bound:=b) in w by omega; omega.
  erewrite selN_oob; auto.
  destruct (lt_dec #x (length l)); auto.
  rewrite map_length.
  assert ($ (length l - 1) < x)%word.
  destruct (weq $ (length l - 1) x); intuition.
  apply wlt_lt in H1; rewrite wordToNat_natToWord_bound with (bound:=b) in H1 by omega; omega.
Qed.


Theorem list2mem_removelast: forall A {defA : Defaultable A} F (l : list A) v (b : addr),
  l <> nil -> length l <= wordToNat b
  -> (F * $ (length l - 1) |-> v)%pred (list2mem l)
  -> F (list2mem (removelast l)).
Proof.
  unfold_sep_star; unfold ptsto; intuition; repeat deex.
  assert (x = list2mem (removelast l)); subst; auto.
  apply functional_extensionality; intros.
  rewrite list2mem_removelast_list2mem with (b:=b); auto.

  destruct (weq x1 $ (length l - 1)); subst.
  apply mem_disjoint_comm in H1. 
  eapply mem_disjoint_either; eauto.

  rewrite H2; unfold mem_union.
  destruct (x x1); subst; simpl; auto.
  apply eq_sym; apply H6; auto.
Qed.


Theorem list2mem_array: forall A {defA : Defaultable A} (l : list A) (b : addr),
  length l <= wordToNat b
  -> array $0 l $1 (list2mem l).
Proof.
  induction l using rev_ind; simpl; intros.
  firstorder.
  rewrite app_length in H; simpl in H.
  rewrite listapp_progupd with (b := b); try omega; eauto.
  apply array_app_progupd with (b := b); try omega; eauto.
  apply IHl with (b:=b); omega.
Qed.


(* Alternative variants of [list2mem] that are more induction-friendly *)
Definition list2mem_off (A: Type) (start : nat) (l: list A) : (addr -> option A) :=
  fun a => if lt_dec (wordToNat a) start then None else
           if lt_dec (wordToNat a - start) (length l)
           then selN (map (@Some A) l) (wordToNat a - start) else None.

Theorem list2mem_off_eq : forall A (l : list A), list2mem l = list2mem_off 0 l.
Proof.
  unfold list2mem, list2mem_off, sel; intros.
  apply functional_extensionality; intros.
  rewrite <- minus_n_O.
  destruct (lt_dec #x 0); try omega.
  reflexivity.
Qed.

Fixpoint list2mem_fix (A : Type) (start : nat) (l : list A) : (addr -> option A) :=
  match l with
  | nil => fun a => None
  | h :: l' => fun a => if eq_nat_dec (wordToNat a) start then Some h else list2mem_fix (S start) l' a
  end.

Lemma list2mem_fix_below : forall (A : Type) (l : list A) start a,
  wordToNat a < start -> list2mem_fix start l a = None.
Proof.
  induction l; auto; simpl; intros.
  destruct (eq_nat_dec (wordToNat a0) start); [omega |].
  apply IHl; omega.
Qed.

Theorem list2mem_fix_off_eq : forall A (l : list A) n (b : addr),
  length l + n <= wordToNat b -> list2mem_off n l = list2mem_fix n l.
Proof.
  induction l; intros; apply functional_extensionality; intros.
  unfold list2mem_off; destruct (lt_dec (wordToNat x) n); auto.

  unfold list2mem_off; simpl in *.

  destruct (lt_dec (wordToNat x) n).
  destruct (eq_nat_dec (wordToNat x) n); [omega |].
  rewrite list2mem_fix_below by omega.
  auto.

  destruct (eq_nat_dec (wordToNat x) n).
  rewrite e; replace (n-n) with (0) by omega; auto.

  assert (wordToNat x - n <> 0) by omega.
  destruct (wordToNat x - n) eqn:Hxn; try congruence.

  rewrite <- IHl with (b:=b) by omega.
  unfold list2mem_off.

  destruct (lt_dec (wordToNat x) (S n)); [omega |].
  replace (#x - S n) with (n2) by omega.
  destruct (lt_dec n2 (length l));
  destruct (lt_dec (S n2) (S (length l))); try omega; reflexivity.
Qed.

Theorem list2mem_fix_eq : forall A (l : list A) (b : addr),
  length l <= wordToNat b -> list2mem l = list2mem_fix 0 l.
Proof.
  intros.
  rewrite list2mem_off_eq.
  eapply list2mem_fix_off_eq.
  rewrite <- plus_n_O.
  eassumption.
Qed.


Lemma list2mem_nil_array : forall A (l : list A) start,
  array $ start l $1 (list2mem nil) -> l = nil.
Proof.
  destruct l; simpl; auto.
  unfold_sep_star; unfold ptsto, list2mem, sel; simpl; intros.
  repeat deex.
  unfold mem_union in H0.
  apply equal_f with ($ start) in H0.
  rewrite H2 in H0.
  congruence.
Qed.

Lemma list2mem_array_nil : forall A (l : list A) start (b : addr),
  start <= wordToNat b -> array $ start nil $1 (list2mem_fix start l) -> l = nil.
Proof.
  destruct l; simpl; auto.
  unfold list2mem, sel, emp; intros.
  pose proof (H0 $ start).
  erewrite wordToNat_natToWord_bound in H1 by eauto.
  destruct (eq_nat_dec start start); simpl in *; congruence.
Qed.

Theorem list2mem_array_eq': forall A (l' l : list A) (b : addr) start,
  array $ start l $1 (list2mem_fix start l')
  -> length l + start <= wordToNat b
  -> length l' + start <= wordToNat b
  -> l' = l.
Proof.
  induction l'; simpl; intros.
  - erewrite list2mem_nil_array; eauto.
  - destruct l.
    + eapply list2mem_array_nil with (start:=start) (b:=b).
      omega.
      auto.
    + simpl in *.
      unfold sep_star in H; rewrite sep_star_is in H; unfold sep_star_impl in H.
      repeat deex.
      unfold ptsto in H3; destruct H3.
      f_equal.
      * eapply equal_f with ($ start) in H2 as H2'.
        erewrite wordToNat_natToWord_bound with (bound:=b) in H2' by omega.

        unfold mem_union in H2'.
        rewrite H3 in H2'.
        destruct (eq_nat_dec start start); congruence.
      * apply IHl' with (b:=b) (start:=S start); eauto; try omega.
        replace ($ start ^+ $1) with (natToWord addrlen (S start)) in H5 by words.
        assert (x0 = list2mem_fix (S start) l'); subst; auto.

        apply functional_extensionality; intros.
        unfold mem_union in H2.
        apply equal_f with x1 in H2.
        destruct (eq_nat_dec (wordToNat x1) start).

        rewrite list2mem_fix_below by omega.
        eapply mem_disjoint_either.
        eauto.
        rewrite <- e in H3.
        rewrite natToWord_wordToNat in *.
        eauto.

        rewrite H2.
        rewrite H4; auto.
        intro; apply n.
        rewrite <- H6.
        rewrite wordToNat_natToWord_bound with (bound:=b); auto.
        omega.
Qed.

Theorem list2mem_array_eq: forall A (l' l : list A) (b : addr),
  array $0 l $1 (list2mem l')
  -> length l <= wordToNat b
  -> length l' <= wordToNat b
  -> l' = l.
Proof.
  intros; eapply list2mem_array_eq' with (start:=0); try rewrite <- plus_n_O; eauto.
  erewrite <- list2mem_fix_eq; eauto.
Qed.


Theorem list2mem_array_app_eq: forall A V {defA : Defaultable A} (F : @pred addr (@weq addrlen) V) (l l' : list A) a (b : addr),
  length l < wordToNat b
  -> length l' <= wordToNat b
  -> (array $0 l $1 * $ (length l) |-> a)%pred (list2mem l')
  -> l' = (l ++ a :: nil).
Proof.
  intros.
  rewrite list2mem_array_eq with (l':=l') (l:=l++a::nil) (b:=b); eauto;
    [ | rewrite app_length; simpl; omega ].
  pred_apply.
  rewrite <- isolate_bwd with (vs:=l++a::nil) (i:=$ (length l)) by
    ( rewrite wordToNat_natToWord_bound with (bound:=b) by omega;
      rewrite app_length; simpl; omega ).
  unfold sel.
  erewrite wordToNat_natToWord_bound with (bound:=b) by omega.
  rewrite firstn_app by auto.
  replace (S (length l)) with (length (l ++ a :: nil)) by (rewrite app_length; simpl; omega).
  rewrite skipn_oob by omega; simpl.
  rewrite selN_last by auto.
  cancel.
  Grab Existential Variables.
  eauto.
Qed.


Definition array_ex A (vs : list A) i :=
  ( array $0 (firstn (wordToNat i) vs) $1 *
    array (i ^+ $1) (skipn (S (wordToNat i)) vs) $1)%pred.


Theorem array_except : forall V {defV : Defaultable V} vs (i : addr),
  wordToNat i < length vs
  -> array $0 vs $1 <=p=> (array_ex vs i) * (i |-> sel vs i).
Proof.
  intros; unfold array_ex.
  erewrite array_isolate; eauto.
  ring_simplify ($ (0) ^+ i ^* $ (1)).
  ring_simplify ($ (0) ^+ (i ^+ $ (1)) ^* $ (1)).
  unfold piff; split; cancel.
Qed.


Theorem array_except_upd : forall V {defV : Defaultable V} vs (v : V) (i : addr),
  wordToNat i < length vs
  -> array $0 (upd vs i v) $1 <=p=> (array_ex vs i) * (i |-> v).
Proof.
  intros; unfold array_ex.
  erewrite array_isolate_upd; eauto.
  ring_simplify ($ (0) ^+ i ^* $ (1)).
  ring_simplify ($ (0) ^+ (i ^+ $ (1)) ^* $ (1)).
  unfold piff; split; cancel.
Qed.


Theorem list2mem_array_pick : forall V {defV : Defaultable V} l (i b : addr),
  length l <= wordToNat b
  -> wordToNat i < length l
  -> (array_ex l i * i |-> sel l i)%pred (list2mem l).
Proof.
  intros.
  eapply array_except; eauto.
  eapply list2mem_array; eauto.
Qed.

Theorem list2mem_array_upd : forall V {defV : Defaultable V} ol nl (v : V) (i b : addr),
  (array_ex ol i * i |-> v)%pred (list2mem nl)
  -> length ol <= wordToNat b
  -> length nl <= wordToNat b
  -> wordToNat i < length ol
  -> nl = upd ol i v.
Proof.
  intros.
  eapply list2mem_array_eq with (b := b); autorewrite with core; auto.
  pred_apply.
  rewrite array_except_upd; auto.
Qed.

Theorem list2mem_array_updN : forall V {defV : Defaultable V} ol nl (v : V) (i b : addr),
  (array_ex ol i * i |-> v)%pred (list2mem nl)
  -> length ol <= wordToNat b
  -> length nl <= wordToNat b
  -> wordToNat i < length ol
  -> updN ol (wordToNat i) v = nl.
Proof.
  intros; apply eq_sym.
  replace (updN ol (wordToNat i) v) with (upd ol i v) by auto.
  eapply list2mem_array_upd; eauto.
Qed.

Theorem list2mem_array_removelast_eq : forall V (nl ol : list V) (b : addr),
  (array_ex ol $ (length ol - 1))%pred (list2mem nl)
  -> length ol <= wordToNat b
  -> length nl <= wordToNat b
  -> length ol > 0
  -> nl = removelast ol.
Proof.
  unfold array_ex; intros.
  destruct ol.
  inversion H2.

  eapply list2mem_array_eq with (l' := nl); eauto.
  pred_apply.
  erewrite wordToNat_natToWord_bound with (bound:=b) by omega.
  rewrite firstn_removelast_eq; auto.
  rewrite skipn_oob by omega.
  unfold array at 2.
  clear H; cancel.
  rewrite length_removelast.
  omega.
  contradict H2; rewrite H2.
  unfold length; omega.
Qed.


Theorem list2mem_array_exis : forall V {defV : Defaultable V} (l : list V) i,
  (array_ex l i * i |-> sel l i)%pred (list2mem l)
  -> (array_ex l i * i |->?)%pred (list2mem l).
Proof.
  intros; pred_apply; cancel.
Qed.


(* Ltacs *)

Ltac rewrite_list2mem_pred_bound H :=
  let Hi := fresh in
  eapply list2mem_inbound in H as Hi.

Ltac rewrite_list2mem_pred_sel H :=
  let Hx := fresh in
  eapply list2mem_sel in H as Hx;
  unfold sel in Hx.

Ltac rewrite_list2mem_pred_upd H:=
  let Hx := fresh in
  eapply list2mem_array_upd in H as Hx;
  [ unfold upd in Hx | .. ].

Ltac rewrite_list2mem_pred :=
  match goal with
  | [ H : (?prd * ?ix |-> ?v)%pred (list2mem ?l) |- _ ] =>
    rewrite_list2mem_pred_bound H;
    first [
      is_var v; rewrite_list2mem_pred_sel H; subst v |
      match prd with
      | array_ex ?ol ix =>
        is_var l; rewrite_list2mem_pred_upd H;
        [ subst l | clear H .. ]
      end ]
  end.

Ltac list2mem_ptsto_cancel :=
  match goal with
  | [ |- (_ * ?p |-> ?a)%pred (list2mem ?l) ] =>
    let Hx := fresh in
    assert (array $0 l $1 (list2mem l)) as Hx;
      [ eapply list2mem_array; eauto; try omega |
        pred_apply; erewrite array_except; unfold sel; clear Hx; eauto ]
  end.

Ltac destruct_listmatch :=
  match goal with
    | [  H : context [ listmatch ?prd ?a _ ],
        H2 : ?p%pred (list2mem ?a) |- _ ] =>
      match p with
        | context [ (?ix |-> _)%pred ] =>
            let Hb := fresh in
            apply list2mem_inbound in H2 as Hb;
            extract_listmatch_at ix;
            clear Hb
      end
  end.

Ltac list2mem_cancel :=
    repeat rewrite_list2mem_pred;
    repeat destruct_listmatch;
    subst; eauto;
    try list2mem_ptsto_cancel; eauto.


Ltac list2mem_bound :=
   match goal with
    | [ H : ( _ * ?p |-> ?i)%pred (list2mem ?l) |- wordToNat ?p < length ?l' ] =>
          let Ha := fresh in assert (length l = length l') by solve_length_eq;
          let Hb := fresh in apply list2mem_inbound in H as Hb;
          eauto; (omega || setoid_rewrite <- Ha; omega); clear Hb Ha
  end.
