Require Import List Omega Ring Word Pred Prog Hoare SepAuto BasicProg.
Require Import FunctionalExtensionality.

Set Implicit Arguments.


(** * A generic array predicate: a sequence of consecutive points-to facts *)

Fixpoint array {V : Type} (a : addr) (vs : list V) (stride : addr) : @pred _ (@weq addrlen) _ :=
  match vs with
    | nil => emp
    | v :: vs' => a |-> v * array (a ^+ stride) vs' stride
  end%pred.

Fixpoint arrayN {V : Type} (a : nat) (vs : list V) : @pred _ eq_nat_dec _ :=
  match vs with
    | nil => emp
    | v :: vs' => a |-> v * arrayN (S a) vs'
  end%pred.

(** * Reading and writing from arrays *)

Class Defaultable (T : Type) := {
  the_default : T
}.

Instance valu_def : Defaultable valu := {
  the_default := $0
}.

Instance word_def {len} : Defaultable (word len) := {
  the_default := $0
}.

Instance nat_def : Defaultable nat := {
  the_default := 0
}.

Instance list_def {T} : Defaultable (list T) := {
  the_default := nil
}.

Instance pair_def {A B} {defA : Defaultable A} {defB : Defaultable B} : Defaultable (A * B) := {
  the_default := (the_default, the_default)
}.

Instance valuset_def : Defaultable valuset := {
  the_default := ($0, nil)
}.

Fixpoint selN (V : Type) {defV : Defaultable V} (vs : list V) (n : nat) : V :=
  match vs with
    | nil => the_default
    | v :: vs' =>
      match n with
        | O => v
        | S n' => selN vs' n'
      end
  end.

Definition sel (V : Type) {defV : Defaultable V} (vs : list V) (i : addr) : V :=
  selN vs (wordToNat i).

Fixpoint updN T (vs : list T) (n : nat) (v : T) : list T :=
  match vs with
    | nil => nil
    | v' :: vs' =>
      match n with
        | O => v :: vs'
        | S n' => v' :: updN vs' n' v
      end
  end.

Definition upd T (vs : list T) (i : addr) (v : T) : list T :=
  updN vs (wordToNat i) v.

Definition upd_prepend (vs : list valuset) (i : addr) (v : valu) : list valuset :=
  upd vs i (v, valuset_list (sel vs i)).

Definition upd_sync (vs : list valuset) (i : addr) : list valuset :=
  upd vs i (fst (sel vs i), nil).

Notation "l [ i ]" := (selN l i _) (at level 56, left associativity).
Notation "l [ i := v ]" := (updN l i v) (at level 76, left associativity).
Notation "l $[ i ]" := (sel l i _) (at level 56, left associativity).
Notation "l $[ i := v ]" := (upd l i v) (at level 76, left associativity).


Lemma length_updN : forall T vs n (v : T), length (updN vs n v) = length vs.
Proof.
  induction vs; destruct n; simpl; intuition.
Qed.

Theorem length_upd : forall T vs i (v : T), length (upd vs i v) = length vs.
Proof.
  intros; apply length_updN.
Qed.

Hint Rewrite length_updN length_upd.

Lemma selN_updN_eq : forall V {defV : Defaultable V} vs n (v : V),
  n < length vs
  -> selN (updN vs n v) n = v.
Proof.
  induction vs; destruct n; simpl; intuition; omega.
Qed.

Lemma selN_updN_ne : forall V {defV : Defaultable V} vs n n' (v : V),
  n <> n'
  -> selN (updN vs n v) n' = selN vs n'.
Proof.
  induction vs; destruct n; destruct n'; simpl; intuition.
Qed.

Lemma sel_upd_eq : forall V {defV : Defaultable V} vs i (v : V),
  wordToNat i < length vs
  -> sel (upd vs i v) i = v.
Proof.
  intros; apply selN_updN_eq; auto.
Qed.

Lemma sel_upd_ne : forall V {defV : Defaultable V} vs i i' (v : V),
  i <> i'
  -> sel (upd vs i v) i' = sel vs i'.
Proof.
  intros; apply selN_updN_ne.
  intro Heq. apply H; clear H.
  apply wordToNat_inj; auto.
Qed.

Hint Rewrite selN_updN_eq sel_upd_eq using (simpl; omega).

Lemma firstn_updN : forall T (v : T) vs i j,
  i <= j
  -> firstn i (updN vs j v) = firstn i vs.
Proof.
  induction vs; destruct i, j; simpl; intuition.
  omega.
  rewrite IHvs; auto; omega.
Qed.

Lemma firstn_upd : forall T (v : T) vs i j,
  i <= wordToNat j
  -> firstn i (upd vs j v) = firstn i vs.
Proof.
  intros; apply firstn_updN; auto.
Qed.

Theorem updN_firstn_comm : forall T (v : T) vs i j,
  j < i
  -> firstn i (updN vs j v) = updN (firstn i vs) j v.
Proof.
  induction vs; destruct i, j; simpl; intuition.
  rewrite IHvs by omega.
  reflexivity.
Qed.

Hint Rewrite firstn_updN firstn_upd using omega.

Lemma skipn_selN : forall T {defT : Defaultable T} i j (vs : list T),
  selN (skipn i vs) j = selN vs (i + j).
Proof.
  induction i; intros; auto.
  destruct vs; simpl; auto.
Qed.

Hint Rewrite skipn_selN using omega.

Lemma skipN_updN' : forall T (v : T) vs i j,
  i > j
  -> skipn i (updN vs j v) = skipn i vs.
Proof.
  induction vs; destruct i, j; simpl; intuition; omega.
Qed.

Lemma skipn_updN : forall T (v : T) vs i j,
  i >= j
  -> match updN vs j v with
       | nil => nil
       | _ :: vs' => skipn i vs'
     end
     = match vs with
         | nil => nil
         | _ :: vs' => skipn i vs'
       end.
Proof.
  destruct vs, j; simpl; eauto using skipN_updN'.
Qed.

Lemma skipn_upd : forall T (v : T) vs i j,
  i >= wordToNat j
  -> match upd vs j v with
       | nil => nil
       | _ :: vs' => skipn i vs'
     end
     = match vs with
         | nil => nil
         | _ :: vs' => skipn i vs'
       end.
Proof.
  intros; apply skipn_updN; auto.
Qed.

Hint Rewrite skipn_updN skipn_upd using omega.

Theorem list_selN_ext' : forall len T {defT : Defaultable T} (a b : list T),
  length a = len
  -> length b = len
  -> (forall pos, pos < len -> selN a pos = selN b pos)
  -> a = b.
Proof.
  induction len; intros; destruct a; destruct b; simpl in *; try congruence.
  f_equal.
  apply (H1 0).
  omega.
  eapply IHlen; [ omega | omega | ].
  intros.
  apply (H1 (S pos)).
  omega.
Qed.

Theorem list_selN_ext : forall T {defT : Defaultable T} (a b : list T),
  length a = length b
  -> (forall pos, pos < length a -> selN a pos = selN b pos)
  -> a = b.
Proof.
  intros. eapply list_selN_ext' with (len:=length a); auto.
Qed.


Lemma nth_selN_eq : forall t n l (z:t) {deft : Defaultable t},
  n < length l -> selN l n = nth n l z.
Proof.
  induction n; intros; destruct l; simpl in *; try omega; auto.
  apply IHn; omega.
Qed.

Lemma in_selN : forall t n l (z:t) {deft : Defaultable t},
  n < length l -> In (selN l n) l.
Proof.
  intros; repeat rewrite nth_selN_eq with (z:=z) by auto.
  apply nth_In; assumption.
Qed.

Lemma in_sel : forall t n l (z:t) {deft : Defaultable t},
  wordToNat n < length l -> In (sel l n) l.
Proof.
  intros. apply in_selN; assumption.
Qed.

Lemma in_updN : forall t n l x (xn:t), In x (updN l n xn) ->
  In x l \/ x = xn.
Proof.
  induction n; intros; destruct l; intuition; simpl in *; destruct H; auto.
  destruct (IHn l x xn H); auto.
Qed.

Lemma in_upd : forall t n l x (xn:t), In x (upd l n xn) ->
  In x l \/ x = xn.
Proof.
  intros. apply in_updN with (n:=wordToNat n); auto.
Qed.

Lemma Forall_upd : forall t P l n (v:t), Forall P l -> P v -> Forall P (upd l n v).
Proof.
  intros. apply Forall_forall. intros v0 Hi. apply in_upd in Hi. destruct Hi.
  rewrite Forall_forall in H. apply H; assumption.
  subst. assumption.
Qed.

Lemma updN_selN_eq : forall T {defT : Defaultable T} (l : list T) ix,
  updN l ix (selN l ix) = l.
Proof.
  induction l; auto.
  intros. destruct ix. auto. simpl. rewrite IHl. trivial.
Qed.

Lemma upd_sel_eq : forall T {defT : Defaultable T} (l : list T) ix,
  upd l ix (sel l ix) = l.
Proof.
  unfold upd, sel. intros. apply updN_selN_eq.
Qed.

Lemma updN_app1 : forall t l l' (v:t) n,
  n < length l -> updN (l ++ l') n v = updN l n v ++ l'.
Proof.
  (* copied from proof of app_nth1 *)
  induction l.
  intros.
  inversion H.
  intros l' d n.
  case n; simpl; auto.
  intros; rewrite IHl; auto with arith.
Qed.

Lemma updN_app2 : forall t l l' (v:t) n,
  n >= length l -> updN (l ++ l') n v = l ++ updN l' (n - length l) v.
Proof.
  (* copied from proof of app_nth2 *)
  induction l.
  intros.
  simpl.
  rewrite <- minus_n_O; auto.
  intros l' d n.
  case n; simpl; auto.
  intros.
  inversion H.
  intros.
  rewrite IHl; auto with arith.
Qed.

Lemma updN_concat : forall t a b m l (v:t), b < m ->
  Forall (fun sl => length sl = m) l ->
  updN (fold_right (@app _) nil l) (b + a * m) v =
    fold_right (@app _) nil (updN l a (updN (selN l a) b v)).
Proof.
  (* XXX this is almost exactly the same as selN_concat *)
  induction a; intros; destruct l; simpl; inversion H0.
  trivial.
  replace (b + 0) with b by omega. subst.
  rewrite updN_app1; auto.
  trivial.
  subst. remember (a * length l) as al. rewrite updN_app2 by omega.
  replace (b + (length l + al) - length l) with (b + al) by omega. subst.
  rewrite IHa; auto.
Qed.

Lemma selN_app1 : forall t {deft : Defaultable t} l l' n,
  n < length l -> selN (l ++ l') n = selN l n.
Proof.
  intros.
  rewrite nth_selN_eq with (z:=the_default).
  rewrite nth_selN_eq with (z:=the_default) by auto.
  apply app_nth1; auto.
  rewrite app_length; omega.
Qed.

Lemma selN_app2 : forall t {deft : Defaultable t} l l' n,
  n >= length l -> selN (l ++ l') n = selN l' (n - length l).
Proof.
  induction l; simpl; intros.
  - f_equal; omega.
  - destruct n; try omega.
    replace (S n - S (length l)) with (n - length l) by omega.
    apply IHl; omega.
Qed.

Lemma map_ext_in : forall A B (f g : A -> B) l, (forall a, In a l -> f a = g a)
  -> map f l = map g l.
Proof.
  induction l; auto; simpl; intros; f_equal; auto.
Qed.

Theorem seq_right : forall b a, seq a (S b) = seq a b ++ (a + b :: nil).
Proof.
  induction b; simpl; intros.
  replace (a + 0) with (a) by omega; reflexivity.
  f_equal.
  replace (a + S b) with (S a + b) by omega.
  rewrite <- IHb.
  auto.
Qed.

Theorem seq_right_0 : forall b, seq 0 (S b) = seq 0 b ++ (b :: nil).
Proof.
  intros; rewrite seq_right; f_equal.
Qed.

Lemma map_updN : forall T U (v : T) (f : T -> U) vs i,
  map f (updN vs i v) = updN (map f vs) i (f v).
Proof.
  induction vs; auto; destruct i; simpl; f_equal; auto.
Qed.

Lemma map_upd : forall T U (v : T) (f : T -> U) vs i,
  map f (upd vs i v) = upd (map f vs) i (f v).
Proof.
  unfold upd; intros.
  apply map_updN.
Qed.

Hint Rewrite map_updN map_upd.

Theorem selN_map_seq' : forall T {defT : Defaultable T} i n f base, i < n
  -> selN (map f (seq base n)) i = f (i + base).
Proof.
  induction i; destruct n; simpl; intros; try omega; auto.
  replace (S (i + base)) with (i + (S base)) by omega.
  apply IHi; omega.
Qed.

Theorem selN_map_seq : forall T {defT : Defaultable T} i n f, i < n
  -> selN (map f (seq 0 n)) i = f i.
Proof.
  intros.
  replace i with (i + 0) at 2 by omega.
  apply selN_map_seq'; auto.
Qed.

Theorem sel_map_seq : forall T {defT : Defaultable T} i n f, (i < n)%word
  -> sel (map f (seq 0 (wordToNat n))) i = f (wordToNat i).
Proof.
  intros.
  unfold sel.
  apply selN_map_seq.
  apply wlt_lt; auto.
Qed.

Hint Rewrite selN_map_seq sel_map_seq using ( solve [ auto ] ).

Theorem selN_map : forall T T' {defT : Defaultable T} {defT' : Defaultable T'} l i
  (f : T' -> T),
  i < length l
  -> selN (map f l) i = f (selN l i).
Proof.
  induction l; simpl; intros; try omega.
  destruct i; auto.
  apply IHl; omega.
Qed.

Theorem sel_map : forall T T' {defT : Defaultable T} {defT' : Defaultable T'} l i
  (f : T' -> T),
  wordToNat i < length l
  -> sel (map f l) i = f (sel l i).
Proof.
  intros.
  unfold sel.
  apply selN_map; auto.
Qed.

Theorem updN_map_seq_app_eq : forall T (f : nat -> T) len start (v : T) x,
  updN (map f (seq start len) ++ (x :: nil)) len v =
  map f (seq start len) ++ (v :: nil).
Proof.
  induction len; auto; simpl; intros.
  f_equal; auto.
Qed.

Theorem updN_map_seq_app_ne : forall T (f : nat -> T) len start (v : T) x pos, pos < len
  -> updN (map f (seq start len) ++ (x :: nil)) pos v =
     updN (map f (seq start len)) pos v ++ (x :: nil).
Proof.
  induction len; intros; try omega.
  simpl; destruct pos; auto.
  rewrite IHlen by omega.
  auto.
Qed.

Theorem updN_map_seq : forall T f len start pos (v : T), pos < len
  -> updN (map f (seq start len)) pos v =
     map (fun i => if eq_nat_dec i (start + pos) then v else f i) (seq start len).
Proof.
  induction len; intros; try omega.
  simpl seq; simpl map.
  destruct pos.
  - replace (start + 0) with (start) by omega; simpl.
    f_equal.
    + destruct (eq_nat_dec start start); congruence.
    + apply map_ext_in; intros.
      destruct (eq_nat_dec a start); auto.
      apply in_seq in H0; omega.
  - simpl; f_equal.
    destruct (eq_nat_dec start (start + S pos)); auto; omega.
    rewrite IHlen by omega.
    replace (S start + pos) with (start + S pos) by omega.
    auto.
Qed.

Lemma combine_l_nil : forall T R (a : list T), List.combine a (@nil R) = nil.
Proof.
  induction a; auto.
Qed.

Hint Rewrite combine_l_nil.

Theorem firstn_combine_comm : forall n T R (a : list T) (b : list R),
  firstn n (List.combine a b) = List.combine (firstn n a) (firstn n b).
Proof.
  induction n; simpl; intros; auto.
  destruct a; simpl; auto.
  destruct b; simpl; auto.
  f_equal.
  auto.
Qed.

Theorem skipn_combine_comm : forall n T R (a : list T) (b : list R),
  match (List.combine a b) with
  | nil => nil
  | _ :: c => skipn n c
  end = List.combine (skipn (S n) a) (skipn (S n) b).
Proof.
  induction n.
  - simpl; intros.
    destruct a; simpl; auto.
    destruct b; simpl; auto.
    autorewrite with core; auto.
  - intros.
    destruct a; [simpl; auto|].
    destruct b; [simpl; auto|].
    autorewrite with core; auto.
    replace (skipn (S (S n)) (t :: a)) with (skipn (S n) a) by auto.
    replace (skipn (S (S n)) (r :: b)) with (skipn (S n) b) by auto.
    rewrite <- IHn.
    simpl; auto.
Qed.


(** * Isolating an array cell *)

Lemma isolate_fwd' : forall V {defV : Defaultable V} vs i a stride,
  i < length vs
  -> array a vs stride =p=> array a (firstn i vs) stride
     * (a ^+ $ i ^* stride) |-> selN vs i
     * array (a ^+ ($ i ^+ $1) ^* stride) (skipn (S i) vs) stride.
Proof.
  induction vs; simpl; intuition.

  inversion H.

  destruct i; simpl.

  replace (a0 ^+ $0 ^* stride) with (a0) by words.
  replace (($0 ^+ $1) ^* stride) with (stride) by words.
  cancel.

  eapply pimpl_trans; [ apply pimpl_sep_star; [ apply pimpl_refl | apply IHvs ] | ]; clear IHvs.
  instantiate (1 := i); omega.
  simpl.
  replace (a0 ^+ stride ^+ ($ i ^+ $1) ^* stride)
    with (a0 ^+ ($ (S i) ^+ $1) ^* stride) by words.
  replace (a0 ^+ stride ^+ $ i ^* stride)
    with (a0 ^+ $ (S i) ^* stride) by words.
  cancel.
Qed.

Theorem isolate_fwd : forall V {defV : Defaultable V} (a i : addr) vs stride,
  wordToNat i < length vs
  -> array a vs stride =p=> array a (firstn (wordToNat i) vs) stride
     * (a ^+ i ^* stride) |-> sel vs i
     * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride.
Proof.
  intros.
  eapply pimpl_trans; [ apply isolate_fwd' | ].
  eassumption.
  rewrite natToWord_wordToNat.
  apply pimpl_refl.
Qed.

Lemma isolateN_fwd' : forall V {defV : Defaultable V} vs i a,
  i < length vs
  -> arrayN a vs =p=> arrayN a (firstn i vs)
     * (a + i) |-> selN vs i
     * arrayN (a + i + 1) (skipn (S i) vs).
Proof.
  induction vs; simpl; intuition.

  inversion H.

  destruct i; simpl.

  replace (a0 + 0) with (a0) by omega.
  replace (a0 + 1) with (S a0) by omega.
  cancel.

  eapply pimpl_trans; [ apply pimpl_sep_star; [ apply pimpl_refl | apply IHvs ] | ]; clear IHvs.
  instantiate (1 := i); omega.
  simpl.
  replace (S (a0 + i)) with (a0 + S i) by omega.
  replace (S (a0 + i + 1)) with (a0 + S i + 1) by omega.
  cancel.
Qed.

Theorem isolateN_fwd : forall V {defV : Defaultable V} a i vs,
  i < length vs
  -> arrayN a vs =p=> arrayN a (firstn i vs)
     * (a + i) |-> selN vs i
     * arrayN (a + i + 1) (skipn (S i) vs).
Proof.
  intros.
  eapply pimpl_trans; [ apply isolateN_fwd' | ].
  eassumption.
  apply pimpl_refl.
Qed.


Lemma isolate_bwd' : forall V {defV : Defaultable V} vs i a stride,
  i < length vs
  -> array a (firstn i vs) stride
     * (a ^+ $ i ^* stride) |-> selN vs i
     * array (a ^+ ($ i ^+ $1) ^* stride) (skipn (S i) vs) stride
  =p=> array a vs stride.
Proof.
  induction vs; simpl; intuition.

  inversion H.

  destruct i; simpl.

  replace (a0 ^+ $0 ^* stride) with (a0) by words.
  replace (($0 ^+ $1) ^* stride) with (stride) by words.
  cancel.

  eapply pimpl_trans; [ | apply pimpl_sep_star; [ apply pimpl_refl | apply IHvs ] ]; clear IHvs.
  2: instantiate (1 := i); omega.
  simpl.
  replace (a0 ^+ stride ^+ ($ i ^+ $1) ^* stride)
    with (a0 ^+ ($ (S i) ^+ $1) ^* stride) by words.
  replace (a0 ^+ stride ^+ $ i ^* stride)
    with (a0 ^+ $ (S i) ^* stride) by words.
  cancel.
Qed.

Theorem isolate_bwd : forall V {defV : Defaultable V} (a i : addr) vs stride,
  wordToNat i < length vs
  -> array a (firstn (wordToNat i) vs) stride
     * (a ^+ i ^* stride) |-> sel vs i
     * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride
  =p=> array a vs stride.
Proof.
  intros.
  eapply pimpl_trans; [ | apply isolate_bwd' ].
  2: eassumption.
  rewrite natToWord_wordToNat.
  apply pimpl_refl.
Qed.

Lemma isolateN_bwd' : forall V {defV : Defaultable V} vs i a,
  i < length vs
  -> arrayN a (firstn i vs)
     * (a + i) |-> selN vs i
     * arrayN (a + i + 1) (skipn (S i) vs)
  =p=> arrayN a vs.
Proof.
  induction vs; simpl; intuition.

  inversion H.

  destruct i; simpl.

  replace (a0 + 0) with (a0) by omega.
  replace (a0 + 1) with (S a0) by omega.
  cancel.

  eapply pimpl_trans; [ | apply pimpl_sep_star; [ apply pimpl_refl | apply IHvs ] ]; clear IHvs.
  2: instantiate (1 := i); omega.
  simpl.
  replace (a0 + S i) with (S (a0 + i)) by omega.
  cancel.
Qed.

Theorem isolateN_bwd : forall V {defV : Defaultable V} a i vs,
  i < length vs
  -> arrayN a (firstn i vs)
     * (a + i) |-> selN vs i
     * arrayN (a + i + 1) (skipn (S i) vs)
  =p=> arrayN a vs.
Proof.
  intros.
  eapply pimpl_trans; [ | apply isolateN_bwd' ].
  2: eassumption.
  apply pimpl_refl.
Qed.


Theorem array_isolate : forall V {defV : Defaultable V} (a i : addr) (vs : list V) stride,
  wordToNat i < length vs
  -> array a vs stride <=p=>
     array a (firstn (wordToNat i) vs) stride
     * (a ^+ i ^* stride) |-> sel vs i
     * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride.
Proof.
  unfold piff; split.
  apply isolate_fwd; auto.
  apply isolate_bwd; auto.
Qed.

Theorem arrayN_isolate : forall V {defV : Defaultable V} a i (vs : list V),
  i < length vs
  -> arrayN a vs <=p=>
     arrayN a (firstn i vs)
     * (a + i) |-> selN vs i
     * arrayN (a + i + 1) (skipn (S i) vs).
Proof.
  unfold piff; split.
  apply isolateN_fwd; auto.
  apply isolateN_bwd; auto.
Qed.

Theorem array_isolate_upd : forall V {defV : Defaultable V} (v : V) (a i : addr) vs stride,
  wordToNat i < length vs
  -> array a (upd vs i v) stride <=p=>
     array a (firstn (wordToNat i) vs) stride
     * (a ^+ i ^* stride) |-> v
     * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride.
Proof.
  intros.
  rewrite array_isolate with (vs:=upd vs i v) (i:=i) (defV:=defV);
    autorewrite with core; auto.
  unfold piff; split.
  cancel; autorewrite with core; cancel.
  cancel; autorewrite with core; cancel.
Qed.

Theorem arrayN_isolate_upd : forall V {defV : Defaultable V} (v : V) a i vs,
  i < length vs
  -> arrayN a (updN vs i v) <=p=>
     arrayN a (firstn i vs)
     * (a + i) |-> v
     * arrayN (a + i + 1) (skipn (S i) vs).
Proof.
  intros.
  erewrite arrayN_isolate with (vs:=updN vs i v) (i:=i) (defV:=defV);
    autorewrite with core; auto.
  unfold piff; split.
  cancel; autorewrite with core; cancel.
  cancel; autorewrite with core; cancel.
Qed.


Theorem isolate_bwd_upd : forall V {defV : Defaultable V} (v : V) (a i : addr) vs stride,
  wordToNat i < length vs
  -> array a (firstn (wordToNat i) vs) stride
     * (a ^+ i ^* stride) |-> v
     * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride
     =p=> array a (upd vs i v) stride.
Proof.
  intros.
  erewrite <- isolate_bwd with (vs:=upd vs i v) (i:=i) (defV:=defV).
  cancel.
  autorewrite with core.
  cancel.
  autorewrite with core.
  auto.
Qed.

Theorem isolateN_bwd_upd : forall V {defV : Defaultable V} (v : V) a i vs,
  i < length vs
  -> arrayN a (firstn i vs)
     * (a + i) |-> v
     * arrayN (a + i + 1) (skipn (S i) vs)
     =p=> arrayN a (updN vs i v).
Proof.
  intros.
  erewrite <- isolateN_bwd with (vs:=updN vs i v) (i:=i) (defV:=defV).
  cancel.
  autorewrite with core.
  cancel.
  autorewrite with core.
  auto.
Qed.


Theorem array_progupd : forall V {defV : Defaultable V} l off (v : V) m,
  array $0 l $1 m
  -> wordToNat off < length l
  -> array $0 (updN l (wordToNat off) v) $1 (Prog.upd m off v).
Proof.
  intros.
  eapply isolate_bwd with (defV:=defV).
  autorewrite with core.
  eassumption.
  eapply pimpl_trans; [| apply pimpl_refl | eapply ptsto_upd ].
  unfold sel; rewrite selN_updN_eq by auto.
  cancel.
  pred_apply.
  rewrite isolate_fwd with (defV:=defV) by eassumption.
  simpl.
  rewrite firstn_updN by auto.
  rewrite skipn_updN by auto.
  cancel.
Qed.

Lemma array_oob': forall A (l : list A) a i m,
  wordToNat i >= length l
  -> array a l $1 m
  -> m (a ^+ i)%word = None.
Proof.
  induction l; intros; auto; simpl in *.
  destruct (weq i $0); auto.
  subst; simpl in *; omega.

  unfold sep_star in H0; rewrite sep_star_is in H0; unfold sep_star_impl in H0.
  repeat deex.
  unfold mem_union.
  unfold ptsto in H2; destruct H2; rewrite H2.
  pose proof (IHl (a0 ^+ $1) (i ^- $1)).
  ring_simplify (a0 ^+ $1 ^+ (i ^- $1)) in H3.
  apply H3.
  rewrite wordToNat_minus_one; try omega; auto.

  auto.
  apply not_eq_sym.
  apply word_neq.
  replace (a0 ^+ i ^- a0) with i by ring; auto.
Qed.

Lemma array_oob: forall A (l : list A) i m,
  wordToNat i >= length l
  -> array $0 l $1 m
  -> m i = None.
Proof.
  intros.
  replace i with ($0 ^+ i).
  eapply array_oob'; eauto.
  ring_simplify ($0 ^+ i); auto.
Qed.

Lemma arrayN_oob': forall A (l : list A) a i m,
  i >= length l
  -> arrayN a l m
  -> m (a + i) = None.
Proof.
  induction l; intros; auto; simpl in *.
  destruct (eq_nat_dec i 0); auto.
  subst; simpl in *; omega.

  unfold sep_star in H0; rewrite sep_star_is in H0; unfold sep_star_impl in H0.
  repeat deex.
  unfold mem_union.
  unfold ptsto in H2; destruct H2; rewrite H2.
  pose proof (IHl (S a0) (i - 1)).
  replace (S a0 + (i - 1)) with (a0 + i) in H3 by omega.
  apply H3; try omega.

  auto.
  omega.
Qed.

Lemma arrayN_oob: forall A (l : list A) i m,
  i >= length l
  -> arrayN 0 l m
  -> m i = None.
Proof.
  intros.
  replace i with (0 + i) by omega.
  eapply arrayN_oob'; eauto.
Qed.


Lemma emp_star_r: forall AT AEQ V (F:@pred AT AEQ V),
  F =p=> (F * emp)%pred.
Proof.
  intros.
  rewrite sep_star_comm.
  apply emp_star.
Qed.


Lemma selN_last: forall A {defA : Defaultable A} l n (a : A),
  n = length l -> selN (l ++ a :: nil) n = a.
Proof.
  unfold selN; induction l; destruct n; intros;
  firstorder; inversion H.
Qed.


Lemma selN_firstn: forall {A} {defA : Defaultable A} (l:list A) i n,
  i < n -> selN (firstn n l) i = selN l i.
Proof.
  induction l; destruct i, n; intros; try omega; auto.
  apply IHl; omega.
Qed.


Lemma selN_oob: forall A {defA : Defaultable A} n l,
  length l <= n
  -> selN l n = the_default.
Proof.
  induction n; destruct l; simpl; firstorder.
  inversion H.
Qed.


Lemma selN_app: forall A {defA : Defaultable A} n l l',
  n < length l
  -> selN (l ++ l') n = selN l n.
Proof.
  induction n; destruct l; simpl; firstorder; inversion H.
Qed.


Lemma firstn_app: forall A n (l1 l2 : list A),
  n = length l1 -> firstn n (l1 ++ l2) = l1.
Proof.
  induction n; destruct l1; intros; inversion H; auto; subst.
  unfold firstn; simpl.
  rewrite IHn; auto.
Qed.


Lemma skipn_oob: forall T n (l : list T),
  n >= length l -> skipn n l = nil.
Proof.
  unfold skipn; induction n; destruct l; intros; auto.
  inversion H.
  apply IHn; firstorder.
Qed.

Lemma updN_oob: forall T l i (v : T),
  i >= length l -> updN l i v = l.
Proof.
  unfold updN; induction l; destruct i; intros; auto.
  inversion H.
  rewrite IHl; firstorder.
Qed.


Lemma firstn_oob: forall A (l : list A) n,
  n >= length l -> firstn n l = l.
Proof.
  unfold firstn; induction l; destruct n; intros; firstorder.
  rewrite IHl; firstorder.
Qed.


Lemma firstn_firstn : forall A (l : list A) n1 n2 ,
  firstn n1 (firstn n2 l) = firstn (Init.Nat.min n1 n2) l.
Proof.
  induction l; destruct n1, n2; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma firstn_plusone_selN : forall A {defA : Defaultable A} n (l : list A),
  n < length l
  -> firstn (n + 1) l = firstn n l ++ (selN l n :: nil).
Proof.
  induction n; destruct l; intros; simpl in *; firstorder.
  inversion H.
  rewrite IHn by omega; auto.
Qed.

Lemma firstn_updN_oob: forall A (l : list A) n i x,
  n <= i -> firstn n (updN l i x) = firstn n l.
Proof.
  induction l; destruct n; destruct i; intros; simpl; auto.
  inversion H.
  rewrite IHl by omega; auto.
Qed.

Lemma firstn_app_updN_eq : forall A {defA : Defaultable A} l n (x : A),
  n < length l
  -> (firstn n l) ++ x :: nil = firstn (n + 1) (updN l n x).
Proof.
  intros.
  rewrite firstn_plusone_selN with (defA := defA).
  rewrite selN_updN_eq by auto.
  rewrite firstn_updN_oob; auto.
  rewrite length_updN; auto.
Qed.

Lemma array_app_progupd : forall V {defV : Defaultable V} l (v : V) m (b : addr),
  length l <= wordToNat b
  -> array $0 l $1 m
  -> array $0 (l ++ v :: nil) $1 (Prog.upd m $ (length l) v)%word.
Proof.
  intros.

  assert (wordToNat (natToWord addrlen (length l)) = length l).
  erewrite wordToNat_natToWord_bound; eauto.
  eapply isolate_bwd with (i := $ (length l)) (defV := defV).
  rewrite H1; rewrite app_length; simpl; omega.

  unfold sel; rewrite H1; rewrite firstn_app; auto.
  rewrite selN_last; auto.
  rewrite skipn_oob; [ | rewrite app_length; simpl; omega ].
  unfold array at 2; auto; apply emp_star_r.
  ring_simplify ($ (0) ^+ $ (length l) ^* natToWord addrlen (1)).
  replace (0 + length l * 1) with (length l) by omega; auto.

  apply ptsto_upd_disjoint; auto.
  eapply array_oob; eauto.
  erewrite wordToNat_natToWord_bound; eauto.
Qed.

Lemma arrayN_app_progupd : forall V {defV : Defaultable V} l (v : V) m,
  arrayN 0 l m
  -> arrayN 0 (l ++ v :: nil) (Prog.upd m (length l) v).
Proof.
  intros.

  eapply isolateN_bwd with (i := (length l)) (defV := defV).
  rewrite app_length; simpl; omega.

  rewrite firstn_app; auto.
  rewrite selN_last; auto.
  rewrite skipn_oob; [ | rewrite app_length; simpl; omega ].
  unfold arrayN at 2; auto; apply emp_star_r.
  simpl.

  apply ptsto_upd_disjoint; auto.
  eapply arrayN_oob; eauto.
Qed.


Lemma length_not_nil : forall A (l : list A),
  l <> nil <-> length l > 0.
Proof.
  split; induction l; simpl; firstorder.
Qed.

Lemma length_not_nil' : forall A (l : list A),
  l <> nil <-> length l <> 0.
Proof.
  split; intros.
  apply length_not_nil in H; omega.
  apply length_not_nil; omega.
Qed.

Lemma firstn_is_nil : forall A n (l : list A),
  n > 0 -> firstn n l = nil -> l = nil.
Proof.
  induction n; destruct l; firstorder.
  inversion H.
  simpl in H0; inversion H0.
Qed.

Lemma removelast_firstn_sub : forall A n (l : list A),
  n > 0 -> n <= length l
  -> removelast (firstn n l) = firstn (n - 1) l.
Proof.
  intros.
  replace n with (S (n - 1)) by omega.
  replace (S (n - 1) - 1) with (n - 1) by omega.
  apply removelast_firstn; omega.
Qed.


(** * Operations for array accesses, to guide automation *)

Definition ArrayRead T a i stride rx : prog T :=
  Xform (isolate_fwd (V:=valuset)) isolate_bwd
    (v <- Read (a ^+ i ^* stride);
     Xform isolate_bwd pimpl_refl (rx v)).

Definition ArrayWrite T a i stride v rx : prog T :=
  Xform (isolate_fwd (V:=valuset)) isolate_bwd
    (v <- Write (a ^+ i ^* stride) v;
     Xform isolate_bwd_upd pimpl_refl (rx v)).


Definition ArraySync T a i stride rx : prog T :=
  Xform (isolate_fwd (V:=valuset)) isolate_bwd
    (v <- Sync (a ^+ i ^* stride);
     Xform isolate_bwd_upd pimpl_refl (rx v)).

(** * Hoare rules *)

Hint Extern 0 (okToUnify (array _ _ _) (array _ _ _)) => constructor : okToUnify.

Theorem read_ok:
  forall T (a i stride:addr) (rx:valu->prog T),
  {{ fun done crash => exists vs F, array a vs stride * F
   * [[wordToNat i < length vs]]
   * [[{{ fun done' crash' => array a vs stride * F * [[ done' = done ]] * [[ crash' = crash ]]
       }} rx (fst (sel vs i))]]
   * [[array a vs stride * F =p=> crash]]
  }} ArrayRead a i stride rx.
Proof.
  unfold ArrayRead.
  hoare.

  rewrite <- surjective_pairing; cancel.
  rewrite <- surjective_pairing; cancel.
  rewrite <- surjective_pairing; cancel.
Qed.

Theorem write_ok:
  forall T (a i stride:addr) (v:valu) (rx:unit->prog T),
  {{ fun done crash => exists vs F, array a vs stride * F
   * [[wordToNat i < length vs]]
   * [[{{ fun done' crash' => array a (upd_prepend vs i v) stride * F
        * [[ done' = done ]] * [[ crash' = crash ]]
       }} rx tt]]
   * [[ array a vs stride * F =p=> crash ]]
  }} ArrayWrite a i stride v rx.
Proof.
  unfold ArrayWrite.
  hoare.
  apply valuset_def.
Qed.

Theorem sync_ok:
  forall T (a i stride:addr) (rx:unit->prog T),
  {{ fun done crash => exists vs F, array a vs stride * F
   * [[wordToNat i < length vs]]
   * [[{{ fun done' crash' => array a (upd_sync vs i) stride * F
        * [[ done' = done ]] * [[ crash' = crash ]]
       }} rx tt]]
   * [[ array a vs stride * F =p=> crash ]]
  }} ArraySync a i stride rx.
Proof.
  unfold ArraySync.
  hoare.

  rewrite <- surjective_pairing; cancel.
  apply valuset_def.
  rewrite <- surjective_pairing; cancel.
Qed.

Hint Extern 1 ({{_}} progseq (ArrayRead _ _ _) _) => apply read_ok : prog.
Hint Extern 1 ({{_}} progseq (ArrayWrite _ _ _ _) _) => apply write_ok : prog.
Hint Extern 1 ({{_}} progseq (ArraySync _ _ _) _) => apply sync_ok : prog.

Hint Extern 0 (okToUnify (array ?base ?l ?stride) (array ?base ?r ?stride)) =>
  unfold okToUnify; constructor : okToUnify.


(** * Some test cases *)

Definition read_back T a rx : prog T :=
  ArrayWrite a $0 $1 $42;;
  v <- ArrayRead a $0 $1;
  rx v.

Ltac unfold_prepend := unfold upd_prepend.

Theorem read_back_ok : forall T a (rx : _ -> prog T),
  {{ fun done crash => exists vs F, array a vs $1 * F
     * [[length vs > 0]]
     * [[{{fun done' crash' => array a (upd_prepend vs $0 $42) $1 * F
          * [[ done' = done ]] * [[ crash' = crash ]]
         }} rx $42 ]]
     * [[ array a vs $1 * F \/
          array a (upd_prepend vs $0 $42) $1 * F =p=> crash ]]
  }} read_back a rx.
Proof.
  unfold read_back; hoare_unfold unfold_prepend.
  autorewrite with core; omega.
  autorewrite with core; auto.
Qed.

Definition swap T a i j rx : prog T :=
  vi <- ArrayRead a i $1;
  vj <- ArrayRead a j $1;
  ArrayWrite a i $1 vj;;
  ArrayWrite a j $1 vi;;
  rx.

Theorem swap_ok : forall T a i j (rx : prog T),
  {{ fun done crash => exists vs F, array a vs $1 * F
     * [[wordToNat i < length vs]]
     * [[wordToNat j < length vs]]
     * [[{{fun done' crash' => array a (upd_prepend (upd_prepend vs i (fst (sel vs j))) j (fst (sel vs i))) $1 * F
           * [[ done' = done ]] * [[ crash' = crash ]]
         }} rx ]]
     * [[ array a vs $1 * F \/
          array a (upd_prepend vs i (fst (sel vs j))) $1 * F \/
          array a (upd_prepend (upd_prepend vs i (fst (sel vs j))) j (fst (sel vs i))) $1 * F =p=> crash ]]
  }} swap a i j rx.
Proof.
  unfold swap; hoare_unfold unfold_prepend.
Qed.


Definition combine_updN : forall A B i a b (va:A) (vb:B),
  List.combine (updN a i va) (updN b i vb) = updN (List.combine a b) i (va, vb).
Proof.
  induction i; intros; destruct a, b; simpl; auto.
  rewrite IHi; auto.
Qed.

Lemma selN_combine : forall Ta Tb {defTa : Defaultable Ta} {defTb : Defaultable Tb}
  i (a : list Ta) (b : list Tb),
  length a = length b
  -> selN (List.combine a b) i = pair (selN a i) (selN b i).
Proof.
  induction i; destruct a, b; intros; inversion H; auto.
  simpl; apply IHi; assumption.
Qed.

Lemma combine_length_eq: forall A B (a : list A) (b : list B),
  length a = length b
  -> length (List.combine a b) = length a.
Proof.
  intros.
  rewrite combine_length.
  rewrite H; intuition.
Qed.

Theorem combine_app: forall A B (al ar : list A) (bl br: list B),
  length al = length bl
  -> List.combine (al ++ ar) (bl ++ br) 
     = (List.combine al bl) ++ (List.combine ar br).
Proof.
  induction al; destruct bl; simpl; intros; try omega; auto.
  f_equal.
  apply IHal; omega.
Qed.


Definition removeN {V} (l : list V) i :=
   (firstn i l) ++ (skipn (S i) l).

Theorem removeN_updN : forall V l i (v : V),
   removeN (updN l i v) i = removeN l i.
Proof.
   unfold removeN; intros.
   rewrite firstn_updN; auto.
   simpl; rewrite skipn_updN; auto.
Qed.

Theorem removeN_oob: forall A (l : list A) i,
  i >= length l -> removeN l i = l.
Proof.
  intros; unfold removeN.
  rewrite firstn_oob by auto.
  rewrite skipn_oob by auto.
  firstorder.
Qed.

Lemma removeN_head: forall A l i (a : A),
  removeN (a :: l) (S i) = a :: (removeN l i).
Proof.
  unfold removeN; firstorder.
Qed.

Theorem removeN_combine: forall A B i (a : list A) (b : list B),
  removeN (List.combine a b) i = List.combine (removeN a i) (removeN b i).
Proof.
  induction i; destruct a, b; intros; simpl; auto.
  - unfold removeN at 2; simpl.
    repeat rewrite removeN_oob by auto.
    induction a0; firstorder.
  - rewrite removeN_head.
    rewrite IHi.
    unfold removeN; firstorder.
Qed.


Lemma skipn_length: forall A n (l : list A),
  n <= length l
  -> length (skipn n l) = length l - n.
Proof.
  induction n; destruct l; intros; firstorder.
Qed.

Lemma removeN_length: forall A (l : list A) i,
  i < length l -> length (removeN l i) = length l - 1.
Proof.
  unfold removeN; induction l; intros; simpl.
  unfold length in H; omega.
  rewrite app_length.
  rewrite firstn_length; rewrite Nat.min_l; simpl in *; try omega.
  rewrite skipn_length; omega.
Qed.


Lemma removeN_length_eq: forall A B (a : list A) (b : list B) i,
  i < length a -> i < length b
  -> length (removeN a i) = length (removeN b i)
  -> length a = length b.
Proof.
  intros; destruct (Nat.eq_dec (length a) 0); try omega.
  rewrite removeN_length in H1; auto.
  rewrite removeN_length in H1; auto.
  omega.
Qed.


Lemma removeN_tail: forall A (l : list A) a,
  removeN (l ++ a :: nil) (length l) = l.
Proof.
  intros; unfold removeN.
  rewrite skipn_oob.
  rewrite firstn_app; firstorder.
  rewrite app_length; simpl; omega.
Qed.


Lemma selN_removelast : forall A {defA : Defaultable A} n l,
  n < length l - 1
  -> selN (removelast l) n = selN l n.
Proof.
  induction l using rev_ind; destruct n;
  intros; simpl; intuition;
  rewrite removelast_app; pred;
  simpl; rewrite app_nil_r;
  rewrite app_length in H; simpl in H;
  rewrite selN_app; firstorder.
Qed.


Lemma length_removelast : forall A (l : list A),
  l <> nil -> length (removelast l) = length l - 1.
Proof.
  induction l using rev_ind; intros; simpl; auto.
  rewrite app_length; simpl.
  rewrite removelast_app; firstorder.
  unfold removelast; rewrite app_length; simpl.
  omega.
Qed.

Lemma removeN_removelast : forall A (l : list A),
  length l > 0
  -> removeN l (length l - 1) = removelast l.
Proof.
  induction l using rev_ind; intros; simpl; firstorder.
  rewrite removelast_app; simpl.
  rewrite app_nil_r.
  rewrite app_length; simpl.
  replace (length l + 1 - 1) with (length l) by omega.
  rewrite removeN_tail; auto.
  congruence.
Qed.


Theorem firstn_removelast_eq : forall V (l : list V),
  length l > 0
  -> firstn (length l - 1) l = removelast l.
Proof.
  destruct l using rev_ind; firstorder.
  rewrite app_length; simpl.
  rewrite removelast_app; simpl; try congruence.
  replace (length l + 1 - 1) with (length l) by omega.
  rewrite firstn_app; auto.
  rewrite app_nil_r; auto.
Qed.


Lemma isolate_last: forall A {defA : Defaultable A} l (a : A) (b:addr),
  length l <= wordToNat b ->
  (array $0 (l ++ a :: nil) $1 <=p=>
   array $0 l $1 * $ (length l) |-> a)%pred.
Proof.
  intros.
  assert (wordToNat (natToWord addrlen (length l)) = length l) as Heq by
    (eapply wordToNat_natToWord_bound; eauto).

  rewrite array_isolate with (i := $ (length l)) (defV := defA) by
    (rewrite app_length; unfold length at 3; omega ).
  unfold sel; rewrite selN_last by omega.
  ring_simplify ((natToWord addrlen 0) ^+ $ (length l) ^* $ (1)).
  replace (wordToNat $ (length l)) with (length l) by auto.
  rewrite firstn_app by auto.
  rewrite skipn_oob by (rewrite app_length; simpl; omega).
  unfold array at 2.

  clear Heq.
  unfold piff; split; cancel.
Qed.
