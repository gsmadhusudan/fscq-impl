Require Import Prog.
Require Import Pred.
Require Import Hoare.
Require Import Omega.
Require Import SepAuto.
Require Import Word.
Require Import Nomega.
Require Import NArith.
Require Import FunctionalExtensionality.
Require Import Eqdep.

Set Implicit Arguments.


(** * Some helpful [prog] combinators and proofs *)

Ltac inv_option :=
  match goal with
  | [ H: Some _ = Some _ |- _ ] => inversion H; clear H; subst
  | [ H: ?a = Some ?b |- _ ] =>
    match goal with
    | [ H': a = Some ?c |- _ ] =>
      match b with
      | c => fail 1
      | _ => rewrite H in H'
      end
    end
  end.

Ltac do_inj_pair2 :=
  repeat match goal with
  | [ H: existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H; subst
  end.

Ltac inv_exec_recover :=
  match goal with
  | [ H: exec_recover _ _ _ _ |- _ ] => inversion H; clear H; subst; do_inj_pair2
  end.

Ltac inv_exec :=
  match goal with
  | [ H: exec _ _ _ |- _ ] => inversion H; clear H; subst; do_inj_pair2
  end.

Lemma postok_null_recover: forall m R (p: prog R) rec out post crash,
  exec_recover m p rec out
  -> rec = Return tt
  -> (forall out', exec m p out' -> postok out' post crash)
  -> postok out post crash.
Proof.
  intros.
  induction H; do_inj_pair2; subst; simpl.
  - eapply (H1 Failed); eauto.
  - eapply (H1 (Finished _ _)); eauto.
  - eapply IHexec_recover with (post:=fun _ => crash); eauto; intros.
    inv_exec; simpl; eapply (H1 (Crashed _)); eauto.
    inv_exec; eauto.
  - eapply IHexec_recover with (post:=fun _ => crash); eauto; intros.
    inv_exec; simpl; eapply (H1 (Crashed _)); eauto.
    inv_exec; eauto.
  - eapply IHexec_recover with (post:=fun _ => crash); eauto; intros.
    inv_exec; simpl; eapply (H1 (Crashed _)); eauto.
    inv_exec; eauto.
Qed.

Theorem read_ok:
  forall (a:addr),
  forall v F,
  {{ a |-> v * F }}
  Read a >> Return tt
  {{ fun r => a |-> v * F * [[r=v]]
  >> a |-> v * F }}.
Proof.
  unfold corr; intros.
  apply ptsto_valid in H as H'.
  eapply postok_null_recover; eauto; intros.
  inv_exec; simpl; repeat inv_option; try congruence.
  apply sep_star_and2lift; split; firstorder.
  inv_exec; eauto.
Qed.

Hint Extern 1 ({{_}} Read _ >> Return tt {{_>>_}}) => apply read_ok : prog.

Theorem write_ok:
  forall (a:addr) (v:valu),
  forall v0 F,
  {{ a |-> v0 * F }}
  Write a v >> Return tt
  {{ fun _ => a |-> v * F
  >> a |-> v0 * F \/ a |-> v * F }}.
Proof.
  unfold corr; intros.
  apply ptsto_valid in H as H'.
  eapply postok_null_recover; eauto; intros.
  inv_exec; simpl; repeat inv_option; try congruence.
  - eapply ptsto_upd; eauto.
  - eapply pimpl_apply. eapply pimpl_or_r; left; eauto. eauto.
  - eapply pimpl_apply. eapply pimpl_or_r; right; eauto.
    inv_exec. eapply ptsto_upd; eauto.
Qed.

Hint Extern 1 ({{_}} Write _ _ >> Return tt {{_>>_}}) => apply write_ok : prog.

Theorem seq_ok:
  forall R S (p1: prog R) (p2: R -> prog S) rec,
  forall pre1 post1 crash1 pre2 post2 crash2,
  {{ pre1
   * [[ {{ pre1 }} p1 >> rec {{ post1 >> crash1 }} ]]
   * [[ forall r m, post1 r m -> {{ pre2 }} p2 r >> rec {{ post2 >> crash2 }} ]]
   * [[ forall r, post1 r ==> pre2 ]]
  }}
  Seq p1 p2 >> rec
  {{ post2
  >> crash1 \/ crash2 }}.
Proof.
  unfold corr; intros.
  repeat ( apply sep_star_lift2and in H; destruct H; unfold lift in * ).
  inv_exec_recover; simpl.
  - inv_exec.
    eapply (H3 _ Failed); eauto.
    eapply (H2 _ _ _ _ Failed).
    eapply H1; eapply (H3 _ (Finished _ _)); eauto.
    eauto.
  - inv_exec.
    eapply H2 with (out:=(Finished _ _)); eauto.
    eapply (H3 _ (Finished _ _)); eauto.
    eapply H1. eapply (H3 _ (Finished _ _)); eauto.
  - admit.
  - admit.
  - admit.
Admitted.

Hint Extern 1 ({{_}} Seq _ _ >> _ {{_>>_}}) => eapply seq_ok : prog.

Definition two_writes a1 v1 a2 v2 :=
  Write a1 v1 ;; Write a2 v2.

Theorem two_writes_ok : forall a1 v1 a2 v2,
  forall v1' v2' F,
  {{ a1 |-> v1' * a2 |-> v2' * F }}
  two_writes a1 v1 a2 v2 >> Return tt
  {{ fun _ => a1 |-> v1 * a2 |-> v2 * F
  >> (a1 |-> v1' * a2 |-> v2' * F) \/
     (a1 |-> v1  * a2 |-> v2' * F) \/
     (a1 |-> v1  * a2 |-> v2  * F) }}.
Proof.
  unfold two_writes; intros.
  eapply pimpl_ok; intros.
  eauto with prog.
  cancel.

  eapply pimpl_ok; intros.
  eauto with prog.
  cancel.

  unfold stars; simpl.
  cancel.

  apply pimpl_refl.

  unfold stars; simpl.
  cancel.

  unfold stars; simpl.
  cancel.

  unfold stars; simpl.
  cancel.
Qed.

Definition If_ P Q (b : {P} + {Q}) (p1 p2 : prog) :=
  if b then p1 else p2.

(*
Theorem if_ok:
  forall P Q (b : {P}+{Q}) p1 p2 post1 post2,
  {{ exists pre, pre
   * [[{{ pre * [[P]] }} p1 {{ post1 }}]]
   * [[{{ pre * [[Q]] }} p2 {{ post2 }}]]
  }} If_ b p1 p2 {{ post1 \/ post2 }}.
Proof.
  unfold corr, exis; intros; repeat deex.
  repeat ( apply sep_star_lift2and in H; destruct H ).
  unfold lift in *. destruct b.
  - edestruct H2; eauto.
    apply sep_star_and2lift; split; eauto.
    split; eauto.
    left; eauto.
  - edestruct H1; eauto.
    apply sep_star_and2lift; split; eauto.
    split; eauto.
    right; eauto.
Qed.

Hint Extern 1 ({{_}} If_ _ _ _ {{_}}) => apply if_ok : prog.
Notation "'If' b { p1 } 'else' { p2 }" := (If_ b p1 p2) (at level 9, b at level 0).

Record For_args (L : Set) := {
  For_args_i : addr;
  For_args_n : addr;
  For_args_l : L
}.

Theorem for_args_wf: forall L,
  well_founded (fun a b => wlt a.(@For_args_n L) b.(@For_args_n L)).
Proof.
  intros.
  apply well_founded_lt_compat with (f:=fun a => wordToNat (a.(For_args_n))).
  intros.
  apply wlt_lt; auto.
Qed.
*)

(*
Definition For_ (L : Set) (G : Type) (f : addr -> L -> (L -> prog) -> prog)
                (i n : addr) (l : L)
                (nocrash : G -> addr -> L -> pred)
                (crashed : G -> pred)
                (rx: L -> prog) : prog.
  refine (Fix (@for_args_wf L) (fun _ => prog)
          (fun args For_ => _)
          {| For_args_i := i; For_args_n := n; For_args_l := l |}).
  clear i n l.
  destruct args.
  refine (if weq For_args_n0 $0 then rx For_args_l0 else _).
  refine (l' <- (f For_args_i0 For_args_l0); _).
  refine (For_ {| For_args_i := For_args_i0 ^+ $1;
                  For_args_n := For_args_n0 ^- $1;
                  For_args_l := l' |} _).

  assert (wordToNat For_args_n0 <> 0).
  unfold not in *; intros; apply n.
  rewrite <- H.
  rewrite natToWord_wordToNat; auto.

  simpl.
  rewrite wminus_Alt.
  rewrite wminus_Alt2.
  unfold wordBinN.
  rewrite (@wordToNat_natToWord_idempotent' addrlen 1);
    [| replace (1) with (wordToNat (natToWord addrlen 1)) by auto; apply wordToNat_bound ].
  apply lt_wlt.

  rewrite wordToNat_natToWord_idempotent';
    [| assert (wordToNat For_args_n0 < pow2 addrlen) by apply wordToNat_bound; omega ].
  apply PeanoNat.Nat.sub_lt; omega.

  unfold wlt, not in *; intro Hn.
  apply H.
  apply Nlt_out in Hn.
  repeat rewrite wordToN_nat in Hn.
  repeat rewrite Nat2N.id in Hn.
  simpl in Hn.
  omega.
Defined.

Lemma For_step: forall L G f i n l nocrash crashed rx,
  @For_ L G f i n l nocrash crashed rx =
    if weq n $0
    then rx l
    else l' <- (f i l);
         @For_ L G f
               (i ^+ $1)
               (n ^- $1)
               l' nocrash crashed rx.
Proof.
  intros.
  unfold For_.
  rewrite Fix_eq.

  destruct (weq n $0); f_equal.

  intros.
  repeat match goal with
  | [ |- context[match ?x with _ => _ end] ] =>
     destruct x; f_equal
  end.
  apply functional_extensionality; auto.
Qed.

Theorem for_ok':
  forall (n i : addr)
         (L : Set) (G : Type)
         f rx rec (nocrash : G -> addr -> L -> pred) (crashed : G -> pred)
         (li : L),
  {{ exists F (g:G), F * nocrash g i li
   * [[forall m l, F * nocrash g m l ==> F * crashed g]]
   * [[forall m lm rxm,
      (i <= m)%word ->
      (m < n ^+ i)%word ->
      (forall lSm, {{ F * nocrash g (m ^+ $1) lSm }} (rxm lSm) >> rec) ->
      {{ F * nocrash g m lm }} f m lm rxm >> rec]]
   * [[forall lfinal, {{ F * nocrash g (n ^+ i) lfinal }} (rx lfinal) >> rec]]
   * [[wordToNat i + wordToNat n = wordToNat (i ^+ n)]]
  }} (For_ f i n li nocrash crashed rx) >> rec.
Proof.
  match goal with
  | [ |- forall (n: addr), ?P ] =>
    refine (well_founded_ind (@wlt_wf addrlen) (fun n => P) _)
  end.

  intros.
  apply corr_exists; intros.
  apply corr_exists; intros.
  case_eq (weq x $0); intros; subst.

  - eapply pimpl_pre; repeat ( apply sep_star_lift_l; intros ).
    + unfold pimpl, lift; intros.
      rewrite For_step.
      apply H2.
    + fold (wzero addrlen). ring_simplify (wzero addrlen ^+ i). auto.

  - eapply pimpl_pre; repeat ( apply sep_star_lift_l; intros ).
    + assert (wordToNat x <> 0).
      unfold not in *; intros; apply n.
      rewrite <- H5; rewrite natToWord_wordToNat; auto.

      unfold pimpl, lift; intros.
      rewrite For_step.
      rewrite H0.
      apply H3.

      apply eq_le; auto.
      rewrite wplus_comm.
      apply lt_wlt.
      omega.

      intros.
      eapply pimpl_ok.
      apply H.

      apply lt_wlt.
      rewrite wminus_Alt.
      rewrite wminus_Alt2.
      unfold wordBinN.
      rewrite wordToNat_natToWord_idempotent'.
      simpl; omega.
      simpl (wordToNat $1).
      eapply Nat.lt_le_trans; [| apply (wordToNat_bound x) ].
      omega.
      unfold not in *; intros; apply n.
      apply wlt_lt in H7; simpl in H7.
      rewrite <- natToWord_wordToNat with (w:=x).
      f_equal.
      omega.

      apply pimpl_exists_r; exists a.
      apply pimpl_exists_r; exists a0.
      ring_simplify (i ^+ $1 ^+ (x ^- $1)).
      ring_simplify (x ^- $1 ^+ (i ^+ $1)).
      repeat ( apply sep_star_lift_r; apply pimpl_and_split );
        unfold pimpl, lift; intuition eauto.

      apply H3; eauto.
      intros; apply H8; clear H8.
      apply wlt_lt in H11.
      unfold wlt.
      repeat rewrite wordToN_nat.
      apply Nlt_in.
      repeat rewrite Nat2N.id.
      rewrite wplus_alt.
      unfold wplusN, wordBinN.
      simpl (wordToNat $1).
      rewrite wordToNat_natToWord_idempotent'.
      omega.
      eapply Nat.le_lt_trans; [| apply (wordToNat_bound (i ^+ x)) ]; omega.

      rewrite wminus_Alt.
      rewrite wminus_Alt2.
      repeat rewrite wplus_alt.
      repeat unfold wplusN, wordBinN.

      simpl (wordToNat $1).
      repeat rewrite wordToNat_natToWord_idempotent'.
      omega.
      rewrite H1; apply wordToNat_bound.

      eapply Nat.le_lt_trans; [| apply (wordToNat_bound x) ]; omega.
      eapply Nat.le_lt_trans; [| apply (wordToNat_bound (i ^+ x)) ]; omega.

      unfold not; intros; apply H5.
      assert (wordToNat x < 1); [| omega ].
      apply wlt_lt in H8; simpl in H8; auto.
    + auto.
Qed.

Theorem for_ok:
  forall (n : addr)
         (L : Set) (G : Type)
         f rx rec (nocrash : G -> addr -> L -> pred) (crashed : G -> pred)
         (li : L),
  {{ exists F (g:G), F * nocrash g $0 li
   * [[forall m l, F * nocrash g m l ==> F * crashed g]]
   * [[forall m lm rxm,
      (m < n)%word ->
      (forall lSm, {{ F * nocrash g (m ^+ $1) lSm }} (rxm lSm) >> rec) ->
      {{ F * nocrash g m lm }} f m lm rxm >> rec]]
   * [[forall lfinal, {{ F * nocrash g n lfinal }} (rx lfinal) >> rec]]
  }} (For_ f $0 n li nocrash crashed rx) >> rec.
Proof.
  intros.
  eapply pimpl_ok.
  apply for_ok'.
  fold (wzero addrlen); ring_simplify (wzero addrlen ^+ n).
  simpl (wordToNat (wzero addrlen)); replace (0 + wordToNat n) with (wordToNat n) by omega.
  ring_simplify (n ^+ wzero addrlen).
  cancel.
  cancel.
Qed.

Hint Extern 1 ({{_}} progseq (For_ _ _ _ _ _ _) _ >> _) => apply for_ok : prog.
Notation "'For' i < n 'Loopvar' l <- l0 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i l lrx => body)
        $0 n l0
        (fun (_:unit) i l => nocrash%pred)
        (fun (_:unit) => crashed%pred))
  (at level 9, i at level 0, n at level 0, lrx at level 0, l at level 0, l0 at level 0,
   body at level 9).

Notation "'For' i < n 'Ghost' g1 .. g2 'Loopvar' l <- l0 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i l lrx => body)
        $0 n l0
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i l => nocrash%pred)) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 binder, g2 binder,
   lrx at level 0, l at level 0, l0 at level 0,
   body at level 9).
*)

(*
Definition read_array a rx :=
  v <- Read a;
  rx v.

Local Hint Extern 1 (diskIs ?m =!=> _) =>
  match goal with
  | [ H: norm_goal (?L ==> ?R) |- _ ] =>
    match R with
    | context[(?a |-> ?v)%pred] =>
      apply diskIs_split; eauto
    end
  end : norm_hint_left.

Local Hint Extern 1 (_ =!=> diskIs ?m) =>
  match goal with
  | [ H: norm_goal (?L ==> ?R) |- _ ] =>
    match L with
    | context[(?a |-> ?v)%pred] =>
      match L with
      | context[diskIs (mem_except m a)] =>
        apply diskIs_merge_except; eauto
      end
    end
  end : norm_hint_right.

Theorem read_array_ok : forall a rx rec,
  {{ exists m v F, diskIs m * F * [[ m @ a |-> v ]]
   * [[ {{ diskIs m * F }} rx v >> rec ]]
   * [[ {{ diskIs m * F }} rec >> rec ]]
  }} read_array a rx >> rec.
Proof.
  unfold read_array.
  hoare.
Qed.

Definition write_array a v rx :=
  Write a v ;;
  rx tt.

Local Hint Extern 1 (_ =!=> diskIs (upd ?m ?a ?v)) =>
  match goal with
  | [ H: norm_goal (?L ==> ?R) |- _ ] =>
    match L with
    | context[(?a |-> ?v')%pred] =>
      match L with
      | context[diskIs (mem_except m a)] =>
        apply diskIs_merge_upd; eauto
      end
    end
  end : norm_hint_right.

Theorem write_array_ok : forall a v rx rec,
  {{ exists m F, diskIs m * F * [[ indomain a m ]]
   * [[ {{ diskIs (upd m a v) * F }} rx tt >> rec ]]
   * [[ {{ diskIs m * F
        \/ diskIs (upd m a v) * F }} rec >> rec ]]
  }} write_array a v rx >> rec.
Proof.
  unfold write_array, indomain.
  hoare.
Qed.

Hint Extern 1 ({{_}} progseq (read_array _) _ >> _) => apply read_array_ok : prog.
Hint Extern 1 ({{_}} progseq (write_array _ _) _ >> _) => apply write_array_ok : prog.
*)
