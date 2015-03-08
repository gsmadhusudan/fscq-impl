Require Import List Omega Ring Word Pred Prog Hoare SepAuto BasicProg Array.
Require Import FunctionalExtensionality.
Require Import ListPred.

Set Implicit Arguments.

(* bijection on restricted domain *)

Section BIJECTION.

  Variables A B : Type.
  Variable f : A -> B.
  Variable PA : A -> Prop.
  Variable PB : B -> Prop.

  Definition cond_injective :=
    forall x y : A, PA x -> PA y -> f x = f y -> x = y.

  Definition cond_surjective :=
    forall y : B, PB y -> {x : A | PA x /\ f x = y}.

  Inductive cond_bijective :=
    CondBijective : cond_injective -> cond_surjective -> cond_bijective.

  Section BIJECTION_INVERSION.

    Variable f' : B -> A.

    Definition cond_left_inverse := 
      forall x : A, PA x -> PB (f x) /\ f' (f x) = x.

    Definition cond_right_inverse := 
      forall y : B, PB y -> PA (f' y) /\ f (f' y) = y.

    Definition cond_inverse := 
      cond_left_inverse /\ cond_right_inverse.

    Lemma cond_left_inv_inj : cond_left_inverse -> cond_injective.
    Proof.
      intros H x y P1 P2 H0.
      pose proof (H x P1) as [P3 P4].
      rewrite <- P4.
      rewrite H0.
      apply H.
      auto.
    Qed.

    Lemma cond_right_inv_surj : cond_right_inverse -> cond_surjective.
    Proof.
      intros H y P1.
      pose proof (H y P1) as [P2 P3].
      rewrite <- P3.
      exists (f' y); intuition.
    Qed.

    Lemma cond_inv2bij : cond_inverse -> cond_bijective.
    Proof.
      intros [H1 H2].
      constructor.
      eapply cond_left_inv_inj; eauto.
      eapply cond_right_inv_surj; eauto.
    Qed.

    Lemma cond_inv_rewrite_right : forall y,
      cond_inverse -> PB y -> f (f' y) = y.
    Proof.
      intros; apply H; auto.
    Qed.

    Lemma cond_inv_rewrite_left : forall x,
      cond_inverse -> PA x -> f' (f x) = x.
    Proof.
      intros; apply H; auto.
    Qed.

  End BIJECTION_INVERSION.

End BIJECTION.


Section MEMMATCH.

  Variable AT1 : Type.
  Variable AT2 : Type.
  Variable atrans : AT1 -> AT2.

  Variable AEQ1 : DecEq AT1.
  Variable AEQ2 : DecEq AT2.
  Variable V : Type.
  Variable m1 : @mem AT1 AEQ1 V.
  Variable m2 : @mem AT2 AEQ2 V.

  (* restrictions on atrans' domain and codomain *)
  Variable AP1 : AT1 -> Prop.
  Variable AP2 : AT2 -> Prop.

  (* decidablity of subdomain *)
  Variable AP1_dec : forall a1, {AP1 a1} + {~ AP1 a1}.
  Variable AP2_dec : forall a2, {AP2 a2} + {~ AP2 a2}.

  (* well-formedness of memory addresses *)
  Variable AP1_ok : forall a1, indomain a1 m1 -> AP1 a1.
  Variable AP2_ok : forall a2, indomain a2 m2 -> AP2 a2.

  Definition mem_atrans f (m : @mem AT1 AEQ1 V) (m' : @mem AT2 AEQ2 V) (_ : unit) :=
    forall a, m a = m' (f a).

  Variable MTrans : mem_atrans atrans m1 m2 tt.

  Lemma mem_atrans_any : forall a1 x, 
    m1 a1 = x -> m2 (atrans a1) = x.
  Proof.
    intros.
    rewrite <- (MTrans a1); auto.
  Qed.

  Lemma mem_atrans_indomain : forall a1,
    indomain a1 m1 -> indomain (atrans a1) m2.
  Proof.
    unfold indomain; intros.
    rewrite <- (MTrans a1); auto.
  Qed.

  Lemma mem_atrans_notindomain : forall a1,
    notindomain a1 m1 -> notindomain (atrans a1) m2.
  Proof.
    unfold notindomain; intros.
    apply mem_atrans_any; auto.
  Qed.

  Lemma mem_atrans_mem_except : forall a (ap : AP1 a),
    cond_bijective atrans AP1 AP2 ->
    mem_atrans atrans (mem_except m1 a) (mem_except m2 (atrans a)) tt.
  Proof.
    intros; unfold mem_atrans, mem_except; intro x.
    destruct (AEQ1 x a); destruct (AEQ2 (atrans x) (atrans a));
      subst; auto; try tauto.
    destruct (indomain_dec x m1); auto.
    contradict n.
    apply X; auto.
  Qed.

  Section MEMMATCH_INVERSION.

    Variable ainv : AT2 -> AT1.
    Variable HInv : cond_inverse atrans AP1 AP2 ainv.

    Lemma mem_ainv_any : forall a (ap : AP2 a) x,
      m1 (ainv a) = x -> m2 a = x.
    Proof.
      intros.
      replace a with (atrans (ainv a)).
      rewrite <- (MTrans (ainv a)); auto.
      apply HInv; auto.
    Qed.

    Lemma mem_atrans_inv_ptsto : forall a (ap : AP2 a) F v,
      (F * (ainv a) |-> v)%pred m1
      -> (any * a |-> v)%pred m2.
    Proof.
      intros.
      apply any_sep_star_ptsto.
      eapply mem_ainv_any; eauto.
      eapply ptsto_valid'; eauto.
    Qed.

    Lemma mem_atrans_inv_notindomain : forall a (ap : AP2 a),
      notindomain (ainv a) m1 -> notindomain a m2.
    Proof.
      unfold notindomain; intros.
      eapply mem_ainv_any; eauto.
    Qed.

    Lemma mem_atrans_emp :
      emp m1 -> emp m2.
    Proof.
      unfold emp; intros.
      destruct (AP2_dec a).

      replace a with (atrans (ainv a)).
      apply mem_ainv_any; auto.
      replace (atrans (ainv a)) with a; auto.
      apply eq_sym; apply HInv; auto.
      apply HInv; auto.

      destruct (indomain_dec a m2); auto.
      contradict n.
      apply AP2_ok; auto.
    Qed.

  End MEMMATCH_INVERSION.

End MEMMATCH.

