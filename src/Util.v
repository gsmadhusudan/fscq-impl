Require Import ProofIrrelevance.

Definition bool2nat (v : bool) : nat :=
   match v with
   | false => 0
   | true => 1
   end.

Definition nat2bool (v : nat) : bool :=
   match v with
   | 0 => false
   | _ => true
   end.

Lemma nat2bool2nat:
  forall b,
  nat2bool (bool2nat b) = b.
Proof.
  destruct b; auto.
Qed.
Hint Rewrite nat2bool2nat.

Definition progseq1 {A B:Type} (a:B->A) (b:B) := a b.
Definition progseq2 {A B:Type} (a:B->A) (b:B) := a b.

Notation "a ;; b" := (progseq1 a (fun _: unit => b))
  (right associativity, at level 60) : fscq_scope.

Notation "ra <- a ; b" := (progseq2 a (fun ra => b))
  (right associativity, at level 60) : fscq_scope.

Delimit Scope fscq_scope with fscq.

Lemma sig_pi:
  forall {T:Type} {P:T->Prop} (a b:sig P),
  proj1_sig a = proj1_sig b ->
  a = b.
Proof.
  intros; destruct a; destruct b.
  simpl in *; subst.
  replace p with p0; [ auto | apply proof_irrelevance ].
Qed.

Lemma sig_pi_ne:
  forall {T:Type} {P:T->Prop} (a b:sig P),
  proj1_sig a <> proj1_sig b ->
  a <> b.
Proof.
  unfold not; intros. apply H. rewrite H0. auto.
Qed.

Lemma arg_sig_pi:
  forall {T R:Type} {P:T->Prop} (a b:sig P) (M:sig P->R),
  proj1_sig a = proj1_sig b ->
  M a = M b.
Proof.
  intros.
  rewrite (sig_pi a b); auto.
Qed.

Lemma sig_ne:
  forall {T:Type} {P:T->Prop} (a b:sig P),
  a <> b ->
  proj1_sig a <> proj1_sig b.
Proof.
  unfold not; intros. apply H. apply sig_pi. auto.
Qed.

Lemma sig_exists:
  forall {T:Type} (P:T->Prop) (a:T),
  P a ->
  exists H,
  a = proj1_sig (exist P a H).
Proof.
  intros. exists H. auto.
Qed.

Definition setidx {K: Type} {V: Type}
                  (eq: forall (a b:K), {a=b}+{a<>b})
                  (db: K->V) (k: K) (v: V) :=
  fun x: K => if eq x k then v else db x.

Definition setidxsig {K: Type} {V: Type} {KP: K->Prop}
                     (eq: forall (a b:K), {a=b}+{a<>b})
                     (db: (sig KP) -> V) (k: K) (v: V) :=
  fun x: (sig KP) => if eq (proj1_sig x) k then v else db x.

Lemma setidx_same:
  forall K V eq db (k:K) (v:V),
  setidx eq db k v k = v.
Proof.
  intros. unfold setidx. destruct (eq k k). auto. destruct n. auto.
Qed.

Lemma setidx_other:
  forall K V eq db (k k':K) (v:V),
  k <> k' ->
  setidx eq db k v k' = db k'.
Proof.
  intros. unfold setidx. destruct (eq k' k). destruct H. auto. auto.
Qed.

Lemma setidxsig_same:
  forall K V {KP:K->Prop} eq (db:sig KP->V) (k:K) (v:V) (k':sig KP),
  (proj1_sig k' = k) ->
  setidxsig eq db k v k' = v.
Proof.
  intros. unfold setidxsig. destruct (eq (proj1_sig k') k). auto. destruct n. auto.
Qed.

Lemma setidxsig_other:
  forall K V {KP:K->Prop} eq (db:sig KP->V) (k:K) (v:V) (k':sig KP),
  (proj1_sig k' <> k) ->
  setidxsig eq db k v k' = db k'.
Proof.
  intros. unfold setidxsig. destruct (eq (proj1_sig k') k). destruct H. auto. auto.
Qed.

Ltac resolve_setidx t :=
  (subst; rewrite setidx_same) || (rewrite setidx_other; [|t]).

Ltac elim_intact_sig e :=
  match e with
  | exist _ _ _ => (* idtac "elim_intact_sig: unfolded version" e; *) fail 1
  | _ =>
    match goal with
    | [ _: e = exist _ _ _ |- _ ] => (* idtac "elim_intact_sig: already got" e; *) fail 2
    | _ => (* idtac "elim_intact_sig:" e; *) destruct e || case_eq e; intros
    end
  end.

Ltac elim_sigs :=
  match goal with
  | [ _: context[proj1_sig ?x] |- _ ] => elim_intact_sig x
  | [ |- context[proj1_sig ?x] ] => elim_intact_sig x
  end.

Ltac propagate_sigs :=
  match goal with
  | [ H1: ?a = exist _ _ _ |- _ ] =>
    match goal with
    | [ H2: context[proj1_sig a] |- _ ] => rewrite H1 in H2; simpl in H2
    | [ |- context[proj1_sig a] ] => rewrite H1; simpl
    end
  end.
