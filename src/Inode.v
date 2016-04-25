Require Import Arith.
Require Import Pred.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Log.
Require Import Array.
Require Import List.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import RecArray.
Require Import GenSep.
Require Import GenSepN.
Require Import Balloc.
Require Import ListPred.
Require Import FSLayout.

Import ListNotations.

Set Implicit Arguments.


(* Inode layout *)

Module INODE.

  (* on-disk representation of inode *)

  Definition iattrtype : Rec.type := Rec.RecF ([
    ("size",   Rec.WordF addrlen) ;   (* file size in bytes *)
    ("mtime",  Rec.WordF 32) ;        (* last modify time *)
    ("itype",  Rec.WordF 32) ;        (* type, used to represent sockets, devices, etc *)
    ("dev",    Rec.WordF 64) ;        (* device ID, for character/block devices *)
    ("pad",    Rec.WordF 64)
  ]).

  Definition iarec  := Rec.data iattrtype.
  Definition iarec0 := @Rec.of_word iattrtype $0.

  Record iattr := {
    ISize : addr;
    IMTime : word 32;
    IType : word 32;
    IDev : word 64;
    IPad : word 64;
  }.

  Definition iattr0 := Build_iattr $0 $0 $0 $0 $0.

  Definition pack_attr (ia : iattr) := Eval compute_rec in
    iarec0 :=> "size" := (ISize ia)
           :=> "mtime" := (IMTime ia)
           :=> "itype" := (IType ia)
           :=> "dev" := (IDev ia)
           :=> "pad" := (IPad ia).

  Definition unpack_attr (iar : iarec) := Eval compute_rec in
    Build_iattr (iar :-> "size") (iar :-> "mtime") (iar :-> "itype") (iar :-> "dev") (iar :-> "pad").

  Theorem unpack_pack_attr : forall a, unpack_attr (pack_attr a) = a.
  Proof.
    destruct a.
    reflexivity.
  Qed.

  Theorem pack_unpack_attr : forall a, pack_attr (unpack_attr a) = a.
  Proof.
    unfold pack_attr, unpack_attr.
    repeat ( destruct a as [? a]; simpl; try reflexivity ).
  Qed.

  Definition iattr_match ia (rec : iarec) : Prop :=
    ISize ia = rec :-> "size" /\
    IMTime ia = rec :-> "mtime" /\
    IType ia = rec :-> "itype" /\
    IDev ia = rec :-> "dev" /\
    IPad ia = rec :-> "pad".


  Definition nr_direct := 9.
  Definition wnr_direct := natToWord addrlen nr_direct.

  Definition inodetype : Rec.type := Rec.RecF ([
    ("len", Rec.WordF addrlen);     (* number of blocks *)
    ("attr", iattrtype);            (* file attributes *)
    ("dindptr", Rec.WordF addrlen); (* doubly-indirect block pointer *)
    ("indptr", Rec.WordF addrlen);  (* indirect block pointer *)
    ("blocks", Rec.ArrayF (Rec.WordF addrlen) nr_direct)]).

  Definition irec := Rec.data inodetype.
  Definition irec0 := @Rec.of_word inodetype $0.

  Definition itemsz := Rec.len inodetype.
  Definition items_per_valu : addr := $ (valulen / itemsz).
  Theorem itemsz_ok : valulen = wordToNat items_per_valu * itemsz.
  Proof.
    unfold items_per_valu; simpl.
    rewrite valulen_is; auto.
  Qed.

  Definition xp_to_raxp xp :=
    RecArray.Build_xparams (IXStart xp) (IXLen xp).


  (** `ilist` is a list of inodes *)
  Definition irrep xp (ilist : list irec) :=
    ([[ length ilist = wordToNat (IXLen xp ^* items_per_valu) ]] *
     RecArray.array_item inodetype items_per_valu itemsz_ok (xp_to_raxp xp) ilist
    )%pred.

  Definition irget T lxp xp inum mscs rx : prog T :=
    v <- RecArray.get inodetype items_per_valu itemsz_ok
      lxp (xp_to_raxp xp) inum mscs;
    rx v.

  Definition irput T lxp xp inum i mscs rx : prog T :=
    v <- RecArray.put inodetype items_per_valu itemsz_ok
      lxp (xp_to_raxp xp) inum i mscs;
    rx v.

  Lemma lt_wordToNat_len : forall T (l : list T) x len (w : word len),
    length l = # w
    -> x < length l
    -> x < # w.
  Proof.
    intros; omega.
  Qed.

  Lemma list2nmem_sel_for_eauto : forall V A i (v v' : V) l def,
    (A * #i |-> v)%pred (list2nmem l)
    -> v' = sel l i def
    -> v' = v.
  Proof.
    unfold sel; intros.
    apply list2nmem_sel with (def:=def) in H.
    congruence.
  Qed.

  Hint Resolve list2nmem_inbound.
  Hint Resolve lt_wlt.
  Hint Resolve lt_wordToNat_len.
  Hint Resolve list2nmem_sel_for_eauto.
  Hint Resolve list2nmem_upd.
  Hint Resolve list2nmem_updN.

  Theorem irget_ok : forall lxp xp inum mscs,
    {< F Fm A mbase m ilist ino,
    PRE            LOG.rep lxp F (ActiveTxn mbase m) mscs *
                   [[ (Fm * irrep xp ilist)%pred (list2mem m) ]] *
                   [[ (A * #inum |-> ino)%pred (list2nmem ilist) ]]
    POST RET:^(mscs,r)
                   LOG.rep lxp F (ActiveTxn mbase m) mscs *
                   [[ r = ino ]]
    CRASH          LOG.would_recover_old lxp F mbase
    >} irget lxp xp inum mscs.
  Proof.
    unfold irget, irrep.
    hoare.
  Qed.

  Theorem irput_ok : forall lxp xp inum i mscs,
    {< F Fm A mbase m ilist ino,
    PRE        LOG.rep lxp F (ActiveTxn mbase m) mscs *
               [[ (Fm * irrep xp ilist)%pred (list2mem m) ]] *
               [[ (A * #inum |-> ino)%pred (list2nmem ilist) ]] *
               [[ Rec.well_formed i ]]
    POST RET:mscs
               exists m' ilist', LOG.rep lxp F (ActiveTxn mbase m') mscs *
               [[ (Fm * irrep xp ilist')%pred (list2mem m') ]] *
               [[ (A * #inum |-> i)%pred (list2nmem ilist')]]
    CRASH      LOG.would_recover_old lxp F mbase
    >} irput lxp xp inum i mscs.
  Proof.
    unfold irput, irrep.
    hoare.
    autorewrite with core; auto.  (* Coq bug 4197 *)
  Qed.

  Hint Extern 1 ({{_}} progseq (irget _ _ _ _) _) => apply irget_ok : prog.
  Hint Extern 1 ({{_}} progseq (irput _ _ _ _ _) _) => apply irput_ok : prog.


  (* on-disk representation of indirect blocks *)

  Definition indtype := Rec.WordF addrlen.
  Definition indblk := Rec.data indtype.
  Definition ind0 := @Rec.of_word indtype $0.

  Definition nr_indirect := Eval compute in valulen_real / addrlen.
  Definition wnr_indirect : addr := natToWord addrlen nr_indirect.
  Definition inditemsz := Rec.len indtype.

  Theorem indsz_ok : valulen = wordToNat wnr_indirect * inditemsz.
  Proof.
    unfold wnr_indirect, nr_indirect, inditemsz, indtype.
    rewrite valulen_is.
    rewrite wordToNat_natToWord_idempotent; compute; auto.
  Qed.

  Definition indxp bn := RecArray.Build_xparams bn $1.

  (** The block at `bn` is an indirect block that contains the list `blist` of addresses (each of a data block) *)
  Definition indrep bxp bn (blist : list addr) :=
    ([[ length blist = nr_indirect ]] * [[ BALLOC.valid_block bxp bn ]] *
     RecArray.array_item indtype wnr_indirect indsz_ok (indxp bn) blist)%pred.

  Definition indget T lxp a off mscs rx : prog T :=
    let^ (mscs, v) <- RecArray.get indtype wnr_indirect indsz_ok
         lxp (indxp a) off mscs;
    rx ^(mscs, v).

  Definition indput T lxp a off v mscs rx : prog T :=
    mscs <- RecArray.put indtype wnr_indirect indsz_ok
           lxp (indxp a) off v mscs;
    rx mscs.

  Theorem indirect_length : forall Fm bxp bn l m,
    (Fm * indrep bxp bn l)%pred m -> length l = nr_indirect.
  Proof.
    unfold indrep; intros.
    destruct_lift H; auto.
  Qed.

  Theorem wordToNat_wnr_indirect : # wnr_indirect = nr_indirect.
  Proof.
    unfold wnr_indirect.
    erewrite wordToNat_natToWord_bound with (bound:=$ valulen).
    reflexivity.
    unfold nr_indirect.
    apply Nat.sub_0_le.
    rewrite valulen_is.
    compute.
    reflexivity.
  Qed.

  Theorem indirect_bound : forall Fm bxp bn l m,
    (Fm * indrep bxp bn l)%pred m -> length l <= wordToNat wnr_indirect.
  Proof.
    rewrite wordToNat_wnr_indirect.
    intros.
    erewrite indirect_length; eauto.
  Qed.

  Theorem indget_ok : forall lxp bxp a off mscs,
    {< F Fm A mbase m blist bn,
    PRE            LOG.rep lxp F (ActiveTxn mbase m) mscs *
                   [[ (Fm * indrep bxp a blist)%pred (list2mem m) ]] *
                   [[ (A * #off |-> bn)%pred (list2nmem blist) ]]
    POST RET:^(mscs,r)
                   LOG.rep lxp F (ActiveTxn mbase m) mscs *
                   [[ r = bn ]]
    CRASH          LOG.would_recover_old lxp F mbase
    >} indget lxp a off mscs.
  Proof.
    unfold indget, indrep, indxp.
    hoare.
  Qed.


  Theorem indput_ok : forall lxp bxp a off bn mscs,
    {< F Fm A mbase m blist v0,
    PRE        LOG.rep lxp F (ActiveTxn mbase m) mscs *
               [[ (Fm * indrep bxp a blist)%pred (list2mem m) ]] *
               [[ (A * #off |-> v0)%pred (list2nmem blist) ]]
    POST RET:mscs
               exists m' blist', LOG.rep lxp F (ActiveTxn mbase m') mscs *
               [[ (Fm * indrep bxp a blist')%pred (list2mem m') ]] *
               [[ (A * #off |-> bn)%pred (list2nmem blist')]]
    CRASH      LOG.would_recover_old lxp F mbase
    >} indput lxp a off bn mscs.
  Proof.
    unfold indput, indrep, indxp.
    hoare.
  Qed.


  Hint Extern 1 ({{_}} progseq (indget _ _ _ _) _) => apply indget_ok : prog.
  Hint Extern 1 ({{_}} progseq (indput _ _ _ _ _) _) => apply indput_ok : prog.

  (* on-disk representation of doubly-indirect blocks *)

  Definition dindtype := Rec.WordF addrlen.
  Definition dindblk := Rec.data dindtype.
  Definition dind0 := @Rec.of_word dindtype $0.

  Definition nr_ind_in_dindirect := Eval compute in (valulen_real / addrlen).
  Definition wnr_ind_in_dindirect : addr := natToWord addrlen nr_ind_in_dindirect.
  Definition dinditemsz := Rec.len dindtype.

  Definition nr_dindirect := nr_indirect * nr_ind_in_dindirect.
  Definition wnr_dindirect : addr := natToWord addrlen nr_dindirect.


  Theorem wordToNat_wnr_dindirect : # wnr_dindirect = nr_dindirect.
  Proof.
    unfold wnr_dindirect.
    rewrite wordToNat_natToWord_idempotent. reflexivity.
    unfold nr_dindirect, nr_indirect, nr_ind_in_dindirect.
    rewrite Nat2N.inj_mul. compute. reflexivity.
  Qed.

  Theorem nr_in_dindirect_eq_nr_indirect: nr_ind_in_dindirect = nr_indirect.
  Proof. reflexivity. Qed.

  Theorem wnr_in_dindirect_eq_wnr_indirect : wnr_ind_in_dindirect = wnr_indirect.
  Proof. reflexivity. Qed.

  Theorem wnr_indirect_sqr_eq_wnr_dindirect : wnr_indirect ^* wnr_indirect = wnr_dindirect.
  Proof.
    unfold wnr_dindirect, nr_dindirect, wnr_indirect.
    rewrite nr_in_dindirect_eq_nr_indirect.
    rewrite natToWord_mult.
    reflexivity.
  Qed.

  Theorem dindsz_ok : valulen= wordToNat wnr_ind_in_dindirect * dinditemsz.
  Proof.
    unfold nr_ind_in_dindirect, dinditemsz, nr_ind_in_dindirect.
    rewrite valulen_is; compute; auto.
  Qed.

  Definition dindxp bn := RecArray.Build_xparams bn $1.

  (** The block at `bn` is a doubly indirect block that contains a list of addresses of indirect blocks *)
  Definition dindrep bxp bn (indlist : list addr) :=
    ([[ length indlist = nr_ind_in_dindirect ]] * [[ BALLOC.valid_block bxp bn ]] *
     RecArray.array_item dindtype wnr_ind_in_dindirect dindsz_ok (dindxp bn) indlist)%pred.

(*
  Definition dindrep2 bxp bn off indlist  :=
    (exists indlist indaddr ind_ v,
    [[ length  = nr_dindirect ]] * 
    [[ (off |-> v) (list2mem ) ]] *
    dindrep bxp bn indlist *
    [[ ((off ^/ wnr_ind_in_dindirect) |-> indaddr) (list2mem indlist) ]] *
    indrep bxp indaddr ind_ *
    [[ ((off ^% wnr_ind_in_dindirect) |-> v) (list2mem ind_) ]])%pred.
*)
Print Forall.
Print In.

Print seq.
  Definition dindrep_big bxp bn indlist indblocks (blist : list addr) :=
    (dindrep bxp bn indlist
      * listmatch (indrep bxp) indlist indblocks
      * [[ length blist = nr_dindirect ]]
      * [[ blist = concat indblocks ]]
      )%pred.


  Definition sublist (A:Type) (n m:nat) (l:list A) :=
    skipn n (firstn m l).

  Opaque nr_ind_in_dindirect.

  Theorem dindrep_big_seq : forall A B bxp bn indlist indblocks blist off v v2 m,
    (dindrep_big bxp bn indlist indblocks blist * [[ off < nr_dindirect ]]
      * [[(A * (off / nr_ind_in_dindirect) |-> v2)%pred (list2nmem indblocks) ]]
      * [[ (B * (off mod nr_ind_in_dindirect) |-> v)%pred (list2nmem v2) ]])%pred m ->
    selN blist off $0 = v.
  Proof.
    unfold dindrep_big, dindrep, indrep; intros.
    destruct_lift H.
    subst.
    eapply list2nmem_sel in H2.
    eapply list2nmem_sel in H0.
    rewrite H2.
    rewrite H0.
    admit.
  Admitted.

  Definition blist_ind (blist : list addr) off :=
    let start := ((off ^/ wnr_ind_in_dindirect) ^* wnr_ind_in_dindirect) in
    sublist (# start) ((# start) + nr_ind_in_dindirect) blist.

  Theorem map_skip_comm : forall T V (l : list T) (f : T -> V) n, skipn n (map f l) = map f (skipn n l).
  Proof.
    intros. generalize dependent l.
    induction n; auto.
    induction l; auto.
    simpl. rewrite IHn. reflexivity.
  Qed.
  Theorem map_sublist_comm : forall T V (l : list T) (f : T -> V) m n, map f (sublist m n l) = sublist m n (map f l).
  Proof.
    unfold sublist.
    intros. erewrite LOG.firstn_map.
    rewrite map_skip_comm. auto.
  Qed.

  Theorem selN_skipn : forall T (l : list T) n i, selN (skipn n l) i = selN l (n + i).
  Proof.
    intros. generalize dependent l. induction n; auto.
    intros. simpl. induction l; auto; simpl in *. rewrite IHn; try omega. unfold selN. reflexivity.
  Qed.
  Fact off_div_wnr_indirect_lt_addrlen_N : forall (off : addr), #(off) < nr_dindirect ->
    (N.of_nat # (off) / N.of_nat # (wnr_indirect) < Npow2 addrlen)%N.
  Proof. intros.
    apply N.div_lt_upper_bound.
    compute. intuition. inversion H0.
    rewrite wordToNat_wnr_indirect.

    apply Nomega.Nlt_in.
    rewrite N2Nat.inj_mul.
    repeat rewrite N2Nat.id;
    repeat rewrite Nat2N.id.
    eapply Nat.lt_trans.
    apply H.
    unfold nr_dindirect.
    Search (_ * _ < _).
    apply mult_lt_compat_l.
    rewrite <- Nat2N.id with (n := nr_ind_in_dindirect).
    apply Nomega.Nlt_out. compute. auto. compute. omega.
  Qed.


  Theorem sublist_blist : forall off blist a v, length blist = nr_dindirect ->
    v = selN blist #off a ->  #off < length blist ->
    (selN (blist_ind blist off) (#(off ^% wnr_ind_in_dindirect)) a) = v.
  Proof. intros.

    unfold blist_ind, sublist.
    rewrite selN_skipn. rewrite wnr_in_dindirect_eq_wnr_indirect.
    rewrite selN_firstn.
    Search wordToNat.
    unfold wdiv, wmult, wmod.
    unfold wordBin.
    repeat rewrite wordToN_nat.
    rewrite N.mul_comm.
    Search NToWord.
    repeat rewrite N2Nat_word.
    Search N.div.
    Search N.of_nat.
    rewrite Ninj_mod.
    rewrite Ninj_div.
    rewrite N2Nat.inj_mul.
    Search N.to_nat.
    repeat rewrite N2Nat.id.
    repeat rewrite Nat2N.id.
    Search (_ * (_ / _ ) ).
    rewrite <- Nat.div_mod.
    symmetry. assumption.

    compute; intuition.
    compute; intuition.
    eapply N.lt_trans.
    Search N.modulo.
    apply N.mod_lt.
    compute; intuition; inversion H2.
    compute; auto.
    Search N.div.
    apply off_div_wnr_indirect_lt_addrlen_N; omega.
    rewrite <- Nat2N.inj_mul.
    rewrite Ninj_div.
    apply Nomega.Nlt_in.
    repeat rewrite Nat2N.id; repeat rewrite N2Nat.id. rewrite wordToNat_wnr_indirect.
    Search ( _ * (_ / _ )).
    assert (nr_indirect * (# (off) / nr_indirect) <= # off).
    Search (_ <= _).
    apply Nat.mul_div_le; compute; intuition.
    Search (_ <= _ -> _ < _).
    eapply Nat.le_lt_trans. apply H2.
    rewrite H in H1. eapply lt_trans. apply H1.
    Search (_ < _ -> (_ < _)).
    Search nr_dindirect.
    SearchAbout nr_dindirect.
    admit.
    apply off_div_wnr_indirect_lt_addrlen_N.
    omega.
    Search (_ +_ < _ + _).
    apply plus_lt_compat_l.
    Search nr_indirect.
    rewrite nr_in_dindirect_eq_nr_indirect.
    unfold wnr_indirect.
    apply lt_word_lt_nat.
    unfold wmod, wordBin.
    apply Nomega.Nlt_in.
    repeat rewrite wordToN_nat.
    repeat rewrite N2Nat_word.
    rewrite Ninj_mod.
    repeat rewrite N2Nat.id;
    repeat rewrite Nat2N.id.
    Search Nat.modulo.
    apply Nat.mod_bound_pos. omega. compute. omega. compute. intuition.
    admit.
  Admitted.

(*
  Fix group A (l : list A) (s : list A) (n : nat) (k : nat) : list (list A) :=
    match l with
    | nil => [ [] ]
    | x :: l' => 
      match k with
      | n => group A l' [x] n 0
      | else => 
*)
    Theorem concat_eq_nil : forall T (l : list (list T)), concat l = [] -> Forall (eq []) l.
    Proof.
      intros. induction l; eauto. destruct a; eauto. simpl in H. inversion H.
    Qed.

    Theorem concat_repeat_nil : forall A n, @concat A (repeat [] n) = [].
    Proof. induction n; eauto.
    Qed.

    Theorem concat_eq_nil_eq_repeat : forall T (l : list (list T)) n, concat l = [] -> length l = n -> l = repeat [] n.
    Proof.
      intros. subst. apply concat_eq_nil in H.
      induction l; auto.
      inversion H. subst. simpl. rewrite <- IHl; auto.
    Qed.

(*
  Theorem dindrep_big_split_length : forall m bxp bn indlist ,
    (dindrep_big bxp bn indlist ) m ->
    (ngth  = nr_dindirect).
  Proof.
    intros. unfold dindrep_big in H. destruct_lift H.
    Search (_ /\ _). assumption.
  Qed.

Search Forall.
*)
(*
  Definition dindrep_total bxp bn ( : list addr) :=
    (exists indlist indaddr,
      (dindrep bxp bn bn_indlist)
     [[ (ind |-> indaddr)%pred (list2mem bn_indlist) ]]
     * (indrep bxp indaddr indlist)
     * [[ (ind_off |-> baddr)%pred (list2mem indlist) ]]
     * [[ (off |-> baddr) (list2mem ) ]]
     * [[ ((ind ^* wnr_ind_in_dindirect ^+ ind_off) |-> baddr)%pred (list2mem ) ]])%pred.
*)
(*
  Definition dindrep_again bxp bn ( : list addr) :=
    (exists bn_indlist ind indaddr indlist baddr, (dindrep bxp bn bn_indlist)
     * [[ (ind |-> indaddr)%pred (list2mem bn_indlist) ]]
     * (indrep bxp indaddr indlist)
     * [[ (ind_off |-> baddr)%pred (list2mem indlist) ]]
     * [[ (off |-> baddr) (list2mem ) ]]
     * [[ ((ind ^* wnr_ind_in_dindirect ^+ ind_off) |-> baddr)%pred (list2mem ) ]])%pred.
*)
Opaque nr_ind_in_dindirect.
(* 
  Theorem dindrep_down : forall F G bxp dindaddr indlist  indindex indaddr indblocks index v0 m,
    (dindrep_big bxp dindaddr indlist ) m ->
    (F * indindex |-> indaddr)%pred (list2nmem indlist) ->
    (indrep bxp indaddr indblocks) m ->
    (G * index |-> v0)%pred (list2nmem indblocks) ->
    (((index + nr_ind_in_dindirect * indindex) |-> v0)%pred (list2nmem )).
  Proof.
    intros.
    unfold dindrep_big in H.
    apply dindrep_big_split in 
    Print pred_apply.
    apply dindrep_big_split in H.
    unfold dindrep_big in H. destruct_lift H.
    SearchAbout list2nmem.
    eapply list2nmem_sel in H0.
    eapply list2nmem_sel in H2.
    unfold indrep in H1. destruct_lift H1.
    unfold indrep in H.
    Search concat.


    destruct_lift H. *)

  Definition dindget T lxp a off mscs rx : prog T :=
    let^ (mscs, v) <- RecArray.get dindtype wnr_ind_in_dindirect dindsz_ok
         lxp (dindxp a) off mscs;
    rx ^(mscs, v).

  Definition dindput T lxp a off v mscs rx : prog T :=
    mscs <- RecArray.put dindtype wnr_ind_in_dindirect dindsz_ok
           lxp (dindxp a) off v mscs;
    rx mscs.

  Theorem dindirect_length : forall Fm bxp bn l m,
    (Fm * dindrep bxp bn l)%pred m -> length l = nr_ind_in_dindirect.
  Proof.
    unfold dindrep; intros.
    destruct_lift H. auto.
  Qed.

  Theorem wordToNat_wnr_ind_in_dindirect : # wnr_ind_in_dindirect = nr_ind_in_dindirect.
  Proof.
    compute. auto.
  Qed.

  Theorem dindirect_bound : forall Fm bxp bn l m,
    (Fm * dindrep bxp bn l)%pred m -> length l <= wordToNat wnr_ind_in_dindirect.
  Proof.
    rewrite wordToNat_wnr_ind_in_dindirect.
    intros.
    erewrite dindirect_length; eauto.
  Qed.

  Theorem dindget_ok : forall lxp bxp a off mscs,
    {< F Fm A mbase m indlist indblocks blist bn,
    PRE           LOG.rep lxp F (ActiveTxn mbase m) mscs *
                  [[ (Fm * dindrep_big bxp a indlist indblocks blist)%pred (list2mem m) ]] *
                  [[ (A * #off |-> bn)%pred (list2nmem indlist) ]]
    POST RET:^(mscs,r)
                  LOG.rep lxp F (ActiveTxn mbase m) mscs *
                  [[ r = bn ]]
    CRASH         LOG.would_recover_old lxp F mbase
    >} dindget lxp a off mscs.
  Proof.
    unfold dindget.
    hoare.
    unfold dindrep_big, dindrep. cancel.
    rewrite wmult_unit.
    unfold dindrep_big, dindrep in H.
    destruct_lift H.
    apply list2nmem_inbound in H4.
    unfold indrep in H.
    apply lt_wlt.
    rewrite wordToNat_wnr_ind_in_dindirect. omega.
  Qed.

  Theorem dindput_ok : forall lxp bxp a off bn mscs,
    {< F Fm A mbase m indlist indblocks blist indblk_in v0,
    PRE       LOG.rep lxp F (ActiveTxn mbase m) mscs *
              [[ (Fm * dindrep_big bxp a indlist indblocks blist * indrep bxp bn indblk_in)%pred (list2mem m) ]] *
              [[ (A * #off |-> v0)%pred (list2nmem indlist) ]]
    POST RET:mscs
              exists m' indlist' indblocks' blist' indblk_out, LOG.rep lxp F (ActiveTxn mbase m') mscs *
              [[ (Fm * dindrep_big bxp a indlist' indblocks' blist' * indrep bxp v0 indblk_out)%pred (list2mem m') ]] *
              [[ (A * #off |-> bn)%pred (list2nmem indlist')]]
    CRASH     LOG.would_recover_old lxp F mbase
    >} dindput lxp a off bn mscs.
  Proof.
    unfold dindput.
    hoare.
    instantiate (ilist := indlist).
    unfold dindrep_big, dindrep, dindxp.
    Focus 3.
    unfold dindrep_big, dindrep, dindxp, upd.
    rewrite length_updN.
    instantiate (indblk_out := (selN indblocks # (off) nil)).
    instantiate (indblocks' := (updN indblocks #(off) indblk_in)).
    instantiate (blist' := concat (updN indblocks # (off) indblk_in)).
    cancel.
    unfold dindrep_big, dindrep in H; destruct_lift H; assumption.
    unfold dindrep_big, dindrep in H; destruct_lift H; assumption.
    unfold dindrep_big, dindrep, listmatch in H; destruct_lift H.
    assert ((Fm * listmatch (indrep bxp) (updN indlist # (off) bn) (updN indblocks # (off) indblk_in) *
      indrep bxp v9 (selN indblocks # (off) nil) *
      array_item dindtype wnr_ind_in_dindirect dindsz_ok (dindxp a) (updN indlist # off bn))
      =p=> (Fm * indrep bxp v9 (selN indblocks # (off) nil) *
      array_item dindtype wnr_ind_in_dindirect dindsz_ok (dindxp a) (updN indlist # off bn) *
      listmatch (indrep bxp) (updN indlist # (off) bn) (updN indblocks # (off) indblk_in))) by cancel.
    apply H3 in H7.
    eapply listmatch_lift_r in H7.
    apply concat_hom_length in H7.
    rewrite H7.
    rewrite length_updN.
    rewrite <- H6.
    rewrite H0.
    unfold nr_dindirect.
    rewrite mult_comm. reflexivity.
    intros. unfold indrep.
    instantiate (1 := fun x y => (lift_empty (BALLOC.valid_block bxp x) * array_item indtype wnr_indirect indsz_ok (indxp x) y)%pred).
    unfold piff; split; cancel.
    cancel.
    rewrite sep_star_comm.
    eapply list2nmem_sel in H4 as H5.
    rewrite H5.
    apply list2nmem_inbound in H4.
    apply listmatch_swap; auto.
    unfold dindrep_big, listmatch in H. destruct_lift H. omega.
    rewrite wmult_unit.
    apply lt_wlt. rewrite wordToNat_wnr_ind_in_dindirect.
    unfold dindrep_big, dindrep, listmatch in H.
    apply list2nmem_inbound in H4.
    destruct_lift H.
    omega.
    Grab Existential Variables.
    auto.
  Qed.

  Hint Extern 1 ({{_}} progseq (dindget _ _ _ _) _) => apply dindget_ok : prog.
  Hint Extern 1 ({{_}} progseq (dindput _ _ _ _ _) _) => apply dindput_ok : prog.

  Definition blocks_per_inode := nr_direct + nr_indirect + nr_dindirect.

  Fact nr_dindirect_bound : nr_dindirect <= wordToNat wnr_dindirect.
  Proof.
    unfold wnr_dindirect. 
    rewrite wordToNat_natToWord_idempotent. auto.
    unfold nr_dindirect. rewrite Nat2N.inj_mul. compute; auto.
  Qed.

  Fact nr_indirect_bound : nr_indirect <= wordToNat wnr_indirect.
  Proof.
    rewrite wordToNat_wnr_indirect.
    auto.
  Qed.

  Fact nr_direct_bound : nr_direct <= wordToNat wnr_direct.
  Proof.
    auto.
  Qed.

  Local Hint Resolve nr_dindirect_bound.
  Local Hint Resolve nr_indirect_bound.
  Local Hint Resolve nr_direct_bound.
  Local Hint Resolve wlt_lt.
  Local Hint Resolve wle_le.
  Hint Rewrite removeN_updN : core.

  Definition indlist0 := repeat (natToWord inditemsz 0) nr_indirect.

  Theorem ind_ptsto : forall bxp a vs,
    indrep bxp a vs
    =p=> (a |-> (rep_block indsz_ok vs))%pred.
  Proof.
    unfold indrep, array_item, array_item_pairs, indxp.
    cancel.
    destruct vs_nested; inversion H0.
    pose proof (length_nil vs_nested) as Hx.
    apply Hx in H4; subst; simpl in *.
    rewrite app_nil_r; subst.
    cancel.
  Qed.

Opaque wnr_indirect.

  Theorem ind_ptsto_zero : forall a,
    (a |-> $0)%pred =p=>
    array_item indtype wnr_indirect indsz_ok (indxp a) indlist0.
  Proof.
    intros.
    unfold array_item, array_item_pairs, indxp.
    norm.
    instantiate (vs_nested := [ RecArray.block_zero indtype wnr_indirect ]).
    unfold rep_block, block_zero, wreclen_to_valu; simpl.
    rewrite Rec.to_of_id.
    rewrite indsz_ok; auto.

    unfold block_zero.
    rewrite wordToNat_wnr_indirect. unfold nr_indirect.
    rewrite Forall_forall.
    intuition.
    simpl in H; intuition; subst; auto.
    rewrite Forall_forall; auto.
  Qed.


  Theorem indlist0_length : length indlist0 = nr_indirect.
  Proof.
    unfold indlist0; apply repeat_length.
  Qed.

  Local Hint Resolve indlist0_length.

  Definition dindlist0 := repeat (natToWord dinditemsz 0) nr_ind_in_dindirect.

  Theorem dind_ptsto : forall bxp a vs,
    dindrep bxp a vs
    =p=> (a |-> (rep_block dindsz_ok vs))%pred.
  Proof.
    unfold dindrep, array_item, array_item_pairs, dindxp.
    cancel.
    destruct vs_nested. inversion H0.
    simpl.
    pose proof (length_nil vs_nested) as Hx.
    inversion H0.
    apply Hx in H4. subst. simpl in *.
    rewrite app_nil_r. cancel.
  Qed.

  Theorem dind_ptsto_zero : forall a,
    (a |-> $0)%pred =p=>
    array_item dindtype wnr_ind_in_dindirect dindsz_ok (dindxp a) dindlist0.
  Proof.
    intros.
    unfold array_item, array_item_pairs, dindxp.
    norm.
    instantiate (vs_nested := [ RecArray.block_zero indtype wnr_ind_in_dindirect ]).
    unfold rep_block, block_zero, wreclen_to_valu; simpl.
    rewrite Rec.to_of_id.
    rewrite dindsz_ok; auto.

    unfold block_zero.
    rewrite Forall_forall.
    intuition.
    simpl in H; intuition; subst; auto.
    rewrite Forall_forall; auto.
  Qed.

  Theorem dindlist0_length : length dindlist0 = nr_ind_in_dindirect.
  Proof.
    unfold dindlist0; apply repeat_length.
  Qed.

  Local Hint Resolve dindlist0_length.

  (* separation logic based theorems *)

  Record inode := {
    IBlocks : list addr;
    IAttr : iattr
  }.

  Definition inode0 := Build_inode nil iattr0.

  Definition ilen T lxp xp inum mscs rx : prog T := Eval compute_rec in
    let^ (mscs, (i : irec)) <- irget lxp xp inum mscs;
    rx ^(mscs, (i :-> "len") : addr).

  Definition igetattr T lxp xp inum mscs rx : prog T := Eval compute_rec in
    let^ (mscs, (i : irec)) <- irget lxp xp inum mscs;
    rx ^(mscs, unpack_attr (i :-> "attr")).

  Definition isetattr T lxp xp inum attr mscs rx : prog T := Eval compute_rec in
    let^ (mscs, (i : irec)) <- irget lxp xp inum mscs;
    mscs <- irput lxp xp inum (i :=> "attr" := pack_attr attr) mscs;
    rx mscs.

  Definition iget T lxp xp inum off mscs rx : prog T := Eval compute_rec in
    let^ (mscs, (i : irec)) <- irget lxp xp inum mscs;
    If (wlt_dec off wnr_direct) {
      rx ^(mscs, sel (i :-> "blocks") off $0)
    } else {
      If (wlt_dec off (wnr_direct ^+ wnr_indirect)) {
        let^ (mscs, v) <- indget lxp (i :-> "indptr") (off ^- wnr_direct) mscs;
        rx ^(mscs, v)
      } else {
        let^ (mscs, ind) <- dindget lxp (i :-> "dindptr") ((off ^- wnr_direct ^- wnr_indirect) ^/ wnr_indirect) mscs;
        let^ (mscs, v) <- indget lxp ind ((off ^- wnr_direct ^- wnr_indirect) ^% wnr_indirect) mscs;
        rx ^(mscs, v)
      }
    }.

  Definition igrow_ind_alloc T lxp bxp xp (i0 : irec) inum a mscs rx : prog T := Eval compute_rec in
    let off := i0 :-> "len" in
    let i := i0 :=> "len" := (off ^+ $1) in
    let^ (mscs, bn) <- BALLOC.alloc lxp bxp mscs;
    match bn with
    | None => rx ^(mscs, false)
    | Some bnum =>
        let i' := (i :=> "indptr" := bnum) in
        mscs <- LOG.write lxp bnum $0 mscs;
        mscs <- indput lxp bnum (off ^- wnr_direct) a mscs;
        mscs <- irput lxp xp inum i' mscs;
        rx ^(mscs, true)
    end.

  Definition igrow_indirect T lxp bxp xp (i0 : irec) inum a mscs rx : prog T := Eval compute_rec in
    let off := i0 :-> "len" in
    let off' := off ^+ $1 in
    let i := i0 :=> "len" := off' in
    If (weq off wnr_direct) {
      let^ (mscs, r) <- igrow_ind_alloc lxp bxp xp i0 inum a mscs;
      rx ^(mscs, r)
    } else {
      mscs <- indput lxp (i :-> "indptr") (off ^- wnr_direct) a mscs;
      mscs <- irput lxp xp inum i mscs;
      rx ^(mscs, true)
    }.

  Definition igrow_dind_alloc_ind T lxp bxp xp (i0 : irec) inum a mscs rx : prog T := Eval compute_rec in
    let off := i0 :-> "len" in
    let i := i0 :=> "len" := (off ^+ $1) in
    let^ (mscs, bn) <- BALLOC.alloc lxp bxp mscs;
    match bn with
    | None => rx ^(mscs, false)
    | Some bnum =>
        mscs <- LOG.write lxp bnum $0 mscs;
        mscs <- dindput lxp (i0 :-> "dindptr") ((off ^- wnr_direct ^- wnr_indirect) ^/ wnr_indirect) bnum mscs;
        mscs <- indput lxp bnum ((off ^- wnr_direct ^- wnr_indirect) ^% wnr_indirect) a mscs;
        mscs <- irput lxp xp inum i mscs;
        rx ^(mscs, true)
    end.

  Definition igrow_dind_alloc T lxp bxp xp (i0 : irec) inum a mscs rx : prog T := Eval compute_rec in
    let off := i0 :-> "len" in
    let i := i0 :=> "len" := (off ^+ $1) in
    let^ (mscs, bn0) <- BALLOC.alloc lxp bxp mscs;
    let^ (mscs, bn1) <- BALLOC.alloc lxp bxp mscs;
    match (bn0, bn1) with
    | (None, None) => rx ^(mscs, false)
    | (None, Some bnum) => 
        mscs <- BALLOC.free lxp bxp bnum mscs;
        rx ^(mscs, false)
    | (Some bnum, None) => 
        mscs <- BALLOC.free lxp bxp bnum mscs;
        rx ^(mscs, false)
    | (Some bnum_dind, Some bnum_ind) =>
        let i' := (i :=> "dindptr" := bnum_dind) in
        mscs <- LOG.write lxp bnum_dind $0 mscs;
        mscs <- LOG.write lxp bnum_ind $0 mscs;
        mscs <- dindput lxp (i :-> "dindptr") ((off ^- wnr_direct ^- wnr_indirect) ^% wnr_indirect) bnum_ind mscs;
        mscs <- indput lxp bnum_ind ((off ^- wnr_direct ^- wnr_indirect) ^% wnr_indirect) a mscs;
        mscs <- irput lxp xp inum i' mscs;
        rx ^(mscs, true)
    end.

  Definition igrow_dindirect T lxp bxp xp (i0 : irec) inum a mscs rx : prog T := Eval compute_rec in
    let off := i0 :-> "len" in
    let off' := off ^+ $1 in
    let i := i0 :=> "len" := off' in
    If (weq off (wnr_direct ^+ wnr_indirect)) {
      let^ (mscs, r) <- igrow_dind_alloc lxp bxp xp i0 inum a mscs;
      rx ^(mscs, r)
    } else {
      let dind_off := (off ^- wnr_direct ^- wnr_indirect) in
      If (weq dind_off $0) {
        let^ (mscs, r) <- igrow_dind_alloc lxp bxp xp i0 inum a mscs;
        rx ^(mscs, r)
      } else {
        If (weq (dind_off ^% wnr_indirect) $0) {
          let^ (mscs, r) <- igrow_dind_alloc_ind lxp bxp xp i0 inum a mscs;
          rx ^(mscs, r)
        } else {
          let^ (mscs, ind) <- dindget lxp (i :-> "dindptr") (dind_off ^/ wnr_indirect) mscs;
          mscs <- indput lxp ind (dind_off ^% wnr_indirect) a mscs;
          mscs <- irput lxp xp inum i mscs;
          rx ^(mscs, true)
        }
      }
    }.

  Definition igrow_direct T lxp xp (i0 : irec) inum a mscs rx : prog T := Eval compute_rec in
    let off := i0 :-> "len" in
    let i := i0 :=> "len" := (off ^+ $1) in
    let i' := i :=> "blocks" := (upd (i0 :-> "blocks") off a) in
    mscs <- irput lxp xp inum i' mscs;
    rx ^(mscs, true).

  Definition igrow T lxp bxp xp inum a mscs rx : prog T := Eval compute_rec in
    let^ (mscs, (i0 : irec)) <- irget lxp xp inum mscs;
    let off := i0 :-> "len" in
    If (wlt_dec off wnr_direct) {
      let^ (mscs, r) <- igrow_direct lxp xp i0 inum a mscs;
      rx ^(mscs, r)
    } else {
        If (wlt_dec off (wnr_indirect ^+ wnr_direct)) {
          let^ (mscs, r) <- igrow_indirect lxp bxp xp i0 inum a mscs;
          rx ^(mscs, r)
        } else {
          let^ (mscs, r) <- igrow_dindirect lxp bxp xp i0 inum a mscs;
          rx ^(mscs, r)
      }
    }.

  Definition ishrink T lxp bxp xp inum mscs rx : prog T := Eval compute_rec in
    let^ (mscs, (i0 : irec)) <- irget lxp xp inum mscs;
    let i := i0 :=> "len" := (i0 :-> "len" ^- $1) in
    If (wlt_dec (i :-> "len") (wnr_direct ^+ wnr_indirect)) {
      If (weq (i :-> "len") wnr_direct) {
        mscs <- BALLOC.free lxp bxp (i0 :-> "indptr") mscs;
        mscs <- irput lxp xp inum i mscs;
        rx mscs
      } else {
        mscs <- irput lxp xp inum i mscs;
        rx mscs
      }
    } else {
      If (weq ((i :-> "len" ^- wnr_indirect ^- wnr_direct) ^% wnr_indirect) $0) {
        let^ (mscs, ind) <- dindget lxp (i :-> "dindptr") ((i :-> "len" ^- wnr_indirect ^- wnr_direct) ^/ wnr_indirect) mscs;
        mscs <- BALLOC.free lxp bxp ind mscs;
        If (weq (i :-> "len") (wnr_indirect ^+ wnr_direct)) {
          mscs <- BALLOC.free lxp bxp (i0 :-> "dindptr") mscs;
          mscs <- irput lxp xp inum i mscs;
          rx mscs
        } else {
          mscs <- irput lxp xp inum i mscs;
          rx mscs
        }
      } else {
        mscs <- irput lxp xp inum i mscs;
        rx mscs
      }
    }.


  Definition indirect_valid bxp n bn blist :=
     ([[ n <= nr_direct ]] \/ [[ n > nr_direct]] * indrep bxp bn blist)%pred.


  Lemma indirect_valid_r : forall bxp n bn blist,
    n > nr_direct
    -> indirect_valid bxp n bn blist <=p=> indrep bxp bn blist.
  Proof.
    intros; unfold indirect_valid, piff; split; cancel.
    omega.
  Qed.

  Lemma indirect_valid_l : forall bxp n bn blist,
    n <= nr_direct
    -> indirect_valid bxp n bn blist <=p=> emp.
  Proof.
    intros; unfold indirect_valid, piff; split; cancel.
    omega.
  Qed.

  Lemma indirect_valid_r_off : forall bxp n off bn blist,
    wordToNat off < n
    -> (off >= wnr_direct)%word
    -> indirect_valid bxp n bn blist <=p=> indrep bxp bn blist.
  Proof.
    auto; intros.
    apply indirect_valid_r.
    apply wle_le in H0.
    replace (wordToNat wnr_direct) with nr_direct in * by auto.
    omega.
  Qed.

  Lemma indirect_valid_off_bound : forall F bxp n off bn blist m,
    (F * indirect_valid bxp n bn blist)%pred m
    -> wordToNat off < n
    -> n <= nr_direct + nr_indirect
    -> (off >= wnr_direct)%word
    -> wordToNat (off ^- wnr_direct) < length blist.
  Proof.
    intros.
    erewrite indirect_valid_r_off in H; eauto.
    unfold indrep in H; destruct_lift H.
    rewrite H5.
    rewrite wminus_minus; auto.
    apply wle_le in H2.
    replace (wordToNat wnr_direct) with nr_direct in * by auto.
    apply plus_lt_reg_l with nr_direct.
    rewrite Nat.add_sub_assoc by assumption.
    simpl. omega.
  Qed.


  Definition dindirect_valid bxp n bn indlist :=
     ([[ n <= nr_direct + nr_indirect ]] \/ [[ n > nr_direct + nr_indirect]] * dindrep bxp bn indlist)%pred.

  Lemma dindirect_valid_r : forall bxp n bn indlist,
    n > nr_direct + nr_indirect
    -> dindirect_valid bxp n bn indlist <=p=> dindrep bxp bn indlist.
  Proof.
    intros. unfold dindirect_valid, piff; split; cancel.
    omega.
  Qed.

  Lemma dindirect_valid_l : forall bxp n bn indlist,
    n <= nr_direct + nr_indirect
    -> dindirect_valid bxp n bn indlist <=p=> emp.
  Proof.
    intros. unfold dindirect_valid, piff; split; cancel.
    omega.
  Qed.

  Lemma dindirect_valid_r_off : forall bxp n off bn indlist,
    wordToNat off < n
    -> (off >= wnr_direct ^+ wnr_indirect)%word
    -> dindirect_valid bxp n bn indlist <=p=> dindrep bxp bn indlist.
  Proof.
    auto; intros.
    apply dindirect_valid_r.
    apply wle_le in H0.
    replace (wordToNat (wnr_direct ^+ wnr_indirect)) with (nr_direct + nr_indirect) in * by auto.
    omega.
  Qed.

  Print dindrep_again.

  Definition dindirect_internal_valid bxp n bn off blist ind indaddr off baddr :=
     ([[ n <= nr_direct + nr_indirect ]] \/ 
      [[ n > nr_direct + nr_indirect]] * 
      dindrep_again bxp bn bn_indlist indlist blist ind indaddr off baddr)%pred.

  Lemma dindirect_internal_valid_r : forall bxp n bn bn_indlist indlist blist ind indaddr off baddr,
    n > nr_direct + nr_indirect
    -> dindirect_internal_valid bxp n bn bn_indlist indlist blist ind indaddr off baddr
        <=p=> dindrep_again bxp bn bn_indlist indlist blist ind indaddr off baddr.
  Proof.
    intros. unfold dindirect_internal_valid, piff; split; cancel.
    omega.
  Qed.

  Lemma dindirect_internal_valid_l : forall bxp n bn bn_indlist indlist blist ind indaddr off baddr,
    n <= nr_direct + nr_indirect
    -> dindirect_internal_valid bxp n bn bn_indlist indlist blist ind indaddr off baddr
        <=p=> emp.
  Proof.
    intros. unfold dindirect_internal_valid, piff; split; cancel.
    omega.
  Qed.

  Fact wordToNat_wnr_direct_plus_wnr_indirect : # (wnr_direct ^+ wnr_indirect) = nr_direct + nr_indirect.
  Proof. auto. Qed.

  Lemma dindirect_internal_valid_r_off : forall bxp n (off : nat) bn bn_indlist indlist blist ind indaddr off baddr,
    wordToNat off < n
    -> (off >= wnr_direct ^+ wnr_indirect)%word
    -> dindirect_internal_valid bxp n bn bn_indlist indlist blist ind indaddr off baddr
        <=p=> dindrep_again bxp bn bn_indlist indlist blist ind indaddr off baddr.
  Proof.
    auto; intros.
    apply dindirect_internal_valid_r.
    apply wle_le in H0. Search (wnr_direct ^+ wnr_indirect).
    rewrite wordToNat_wnr_direct_plus_wnr_indirect in H0.
    omega.
  Qed.

  (** The inode `ino` is equivalent to the on-disk record `rec` *)
  Definition inode_match bxp (ino : inode) (rec : irec) : @pred addr (@weq addrlen) valu := (
    [[ length (IBlocks ino) = wordToNat (rec :-> "len") ]] *
    [[ length (IBlocks ino) <= blocks_per_inode ]] *
    [[ iattr_match (IAttr ino) (rec :-> "attr") ]] *
    exists indlist, indirect_valid bxp (length (IBlocks ino)) (rec :-> "indptr") indlist *
    exists dindlist, dindirect_total_valid bxp (length (IBlocks ino)) (rec :-> "dindptr") dindlist *
    [[ IBlocks ino = firstn (length (IBlocks ino)) ((rec :-> "blocks") ++ indlist ++ dindlist) ]]
    )%pred.

  (** the list `ilist` of inodes is valid *)
  Definition rep bxp xp (ilist : list inode) := (
     exists reclist, irrep xp reclist *
     listmatch (inode_match bxp) ilist reclist)%pred.

  Definition inode_match_direct ino (rec : irec) : @pred addr (@weq addrlen) valu := (
    [[ length (IBlocks ino) = wordToNat (rec :-> "len") ]] *
    [[ iattr_match (IAttr ino) (rec :-> "attr") ]] *
    [[ length (IBlocks ino) <= nr_direct ]] *
    [[ IBlocks ino = firstn (length (IBlocks ino)) (rec :-> "blocks") ]]
    )%pred.

  Lemma inode_well_formed : forall Fm xp l i inum m def,
    (Fm * irrep xp l)%pred m
    -> inum < length l
    -> i = selN l inum def
    -> Rec.well_formed i.
  Proof.
    unfold irrep.
    setoid_rewrite RecArray.array_item_well_formed'.
    setoid_rewrite Forall_forall.
    intros.
    destruct_lift H.
    apply H4.
    subst.
    apply Array.in_selN; auto.
  Qed.

  Lemma direct_blocks_length: forall (i : irec),
    Rec.well_formed i
    -> length (i :-> "blocks") = nr_direct.
  Proof.
    intros.
    simpl in H.
    destruct i; repeat destruct p.
    unfold Rec.recget'; simpl.
    intuition.
  Qed.

  Lemma inode_blocks_length: forall m xp l inum Fm,
    (Fm * irrep xp l)%pred m ->
    inum < length l ->
    length (selN l inum irec0 :-> "blocks") = nr_direct.
  Proof.
    intros.
    apply direct_blocks_length.
    eapply inode_well_formed; eauto.
  Qed.

  Lemma inode_blocks_length': forall m xp l inum Fm len attr dindptr indptr blocks u,
    (Fm * irrep xp l)%pred m ->
    inum < length l ->
    (len, (attr, (dindptr, (indptr, (blocks, u))))) = selN l inum irec0 ->
    length blocks = nr_direct.
  Proof.
    intros.
    unfold irrep in H.
    rewrite RecArray.array_item_well_formed' in H.
    destruct_lift H.
    rewrite Forall_forall in *.
    apply (H4 (len, (attr, (dindptr, (indptr, (blocks, tt)))))).
    rewrite H1.
    apply Array.in_selN; intuition.
  Qed.

  Arguments Rec.well_formed : simpl never.

  Lemma wle_eq_le: forall sz (a : word sz) b c,
    b <= wordToNat (natToWord sz b)
    -> (a <= natToWord sz b)%word -> wordToNat a = c -> c <= b.
  Proof.
    intros; apply wle_le in H0.
    erewrite wordToNat_natToWord_bound in H0; eauto.
    omega.
  Qed.

  Lemma inode_match_is_direct: forall bxp ino (rec : irec),
    (rec :-> "len" <= wnr_direct)%word
    -> Rec.well_formed rec
    -> inode_match bxp ino rec <=p=> inode_match_direct ino rec.
  Proof.
    unfold piff, inode_match, inode_match_direct; split; intros.
    apply wle_le in H.
    cancel.
    rewrite indirect_valid_l; try (rewrite H2; unfold nr_direct in *; simpl; omega).
    rewrite dindirect_valid_l; try (rewrite H2; unfold nr_direct in *; simpl; omega).

    rewrite dindirect_internal_valid_l; try (rewrite H2; unfold nr_direct in *; simpl; omega).
    cancel.
    unfold nr_direct; omega.
    rewrite firstn_app_l in H8. assumption.

    rewrite direct_blocks_length by auto. unfold nr_direct; omega.

    cancel.
    instantiate (indlist := nil). instantiate (dindlist := nil). instantiate (dind_indlist := nil).
    rewrite indirect_valid_l; auto; try omega.
    rewrite dindirect_valid_l by omega.
    rewrite dindirect_internal_valid_l by omega.
    cancel.
    unfold blocks_per_inode; omega.
    rewrite app_nil_r; auto.
  Qed.


  (* Hints for resolving default values *)

  Fact resolve_sel_irec0 : forall l i d,
    d = irec0 -> sel l i d = sel l i irec0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_irec0 : forall l i d,
    d = irec0 -> selN l i d = selN l i irec0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_sel_inode0 : forall l i d,
    d = inode0 -> sel l i d = sel l i inode0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_inode0 : forall l i d,
    d = inode0 -> selN l i d = selN l i inode0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_sel_addr0 : forall l i (d : addr),
    d = $0 -> sel l i d = sel l i $0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_addr0 : forall l i (d : addr),
    d = $0 -> selN l i d = selN l i $0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_sel_valu0 : forall l i (d : valu),
    d = $0 -> sel l i d = sel l i $0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_valu0 : forall l i (d : valu),
    d = $0 -> selN l i d = selN l i $0.
  Proof.
    intros; subst; auto.
  Qed.


  Hint Rewrite resolve_sel_irec0  using reflexivity : defaults.
  Hint Rewrite resolve_selN_irec0 using reflexivity : defaults.
  Hint Rewrite resolve_sel_inode0   using reflexivity : defaults.
  Hint Rewrite resolve_selN_inode0  using reflexivity : defaults.
  Hint Rewrite resolve_sel_addr0    using reflexivity : defaults.
  Hint Rewrite resolve_selN_addr0   using reflexivity : defaults.
  Hint Rewrite resolve_sel_valu0    using reflexivity : defaults.
  Hint Rewrite resolve_selN_valu0   using reflexivity : defaults.

  Lemma rep_bound: forall Fm bxp xp l m,
    (Fm * rep bxp xp l)%pred m
    -> length l <= wordToNat (IXLen xp ^* items_per_valu).
  Proof.
    unfold rep, irrep; intros.
    destruct_lift H.
    erewrite listmatch_length_r; eauto; omega.
  Qed.

    Lemma wordToNat_natToWord_blocks_per_inode : wordToNat (natToWord addrlen blocks_per_inode) = blocks_per_inode.
    Proof.
      apply wordToNat_natToWord_idempotent.
      unfold blocks_per_inode, nr_dindirect.
      repeat rewrite Nat2N.inj_add.
      rewrite Nat2N.inj_mul.
      compute. auto.
    Qed.

  Lemma blocks_bound: forall Fm bxp xp l m i,
    (Fm * rep bxp xp l)%pred m
    -> length (IBlocks (sel l i inode0)) <= wordToNat (natToWord addrlen blocks_per_inode).
  Proof.
    unfold rep, sel; intros.
    destruct_lift' H.
    rewrite wordToNat_natToWord_blocks_per_inode in *.
    destruct (lt_dec (wordToNat i) (length l)).
    extract_listmatch_at i; unfold nr_direct in *. assumption.
    apply not_lt in n.
    destruct_lift H.
    rewrite selN_oob by omega.
    simpl; omega.
  Qed.

  Ltac inode_bounds' := match goal with
    | [ H : context [ (irrep _ ?l) ] |- length ?l <= _ ] =>
        unfold irrep in H; destruct_lift H
    | [ H : context [ (indrep _ _ ?l) ] |- length ?l <= _ ] =>
        unfold indrep in H; destruct_lift H
  end.

  Ltac inode_bounds := eauto; try list2nmem_bound; try solve_length_eq;
                       repeat (inode_bounds'; solve_length_eq);
                       try list2nmem_bound; eauto.

  Ltac destruct_irec' x :=
    match type of x with
    | irec => let b := fresh in destruct x as [? b] eqn:?; destruct_irec' b
    | (Rec.data iattrtype) => let b := fresh in destruct x as [? b] eqn:?; destruct_irec' b
    | prod _ _ => let b := fresh in destruct x as [? b] eqn:?; destruct_irec' b
    | _ => idtac
    end.

  Ltac destruct_irec x :=
    match x with
    | (?a, ?b) => (destruct_irec a || destruct_irec b)
    | fst ?a => destruct_irec a
    | snd ?a => destruct_irec a
    | _ => destruct_irec' x; simpl
    end.

  Ltac smash_rec_well_formed' :=
    match goal with
    | [ |- Rec.well_formed ?x ] => destruct_irec x
    end.

  Ltac smash_rec_well_formed :=
    unfold sel, upd; autorewrite with core;
    repeat smash_rec_well_formed';
    unfold Rec.well_formed; simpl;
    try rewrite Forall_forall; intuition.

  Ltac irec_well_formed :=
    smash_rec_well_formed;
    match goal with
      | [ H : ?p %pred ?mm |- length ?d = nr_direct ] =>
      match p with
        | context [ irrep _ ?ll ] => 
          autorewrite with core;
          eapply inode_blocks_length' with (m := mm) (l := ll); inode_bounds;
          pred_apply; cancel
      end
    end.


  Hint Extern 0 (okToUnify (irrep _ _) (irrep _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (indrep _ _ _) (indrep _ _ _)) => constructor : okToUnify.

  Theorem ilen_ok : forall lxp bxp xp inum mscs,
    {< F Fm A mbase m ilist ino,
    PRE            LOG.rep lxp F (ActiveTxn mbase m) mscs *
                   [[ (Fm * rep bxp xp ilist)%pred (list2mem m) ]] *
                   [[ (A * #inum |-> ino)%pred (list2nmem ilist) ]]
    POST RET:^(mscs,r)
                   LOG.rep lxp F (ActiveTxn mbase m) mscs * [[ r = $ (length (IBlocks ino)) ]]
    CRASH          LOG.would_recover_old lxp F mbase
    >} ilen lxp xp inum mscs.
  Proof.
    unfold ilen, rep.
    hoare.
    list2nmem_ptsto_cancel; list2nmem_bound.

    rewrite_list2nmem_pred.
    destruct_listmatch_n.
    subst; apply wordToNat_inj.
    erewrite wordToNat_natToWord_bound by inode_bounds.
    auto.
  Qed.


  Lemma iattr_match_unpack : forall ia iar,
    iattr_match ia iar
    -> unpack_attr iar = ia.
  Proof.
    unfold iattr_match, unpack_attr; rec_simpl.
    intros ia iar H; destruct ia.
    repeat match goal with
    | [ H : _ /\ _ |- _ ] => destruct H
    end.
    repeat match goal with
    | [ H : ?a = ?b |- context [ ?b ] ] => rewrite <- H
    end.
    simpl; auto.
  Qed.

  Lemma iattr_match_pack : forall ia,
    iattr_match ia (pack_attr ia).
  Proof.
    unfold iattr_match, pack_attr; intros.
    rec_simpl; simpl; auto.
  Qed.

  Local Hint Resolve iattr_match_unpack.
  Local Hint Resolve iattr_match_pack.

  Theorem igetattr_ok : forall lxp bxp xp inum mscs,
    {< F Fm A mbase m ilist ino,
    PRE            LOG.rep lxp F (ActiveTxn mbase m) mscs *
                   [[ (Fm * rep bxp xp ilist)%pred (list2mem m) ]] *
                   [[ (A * #inum |-> ino)%pred (list2nmem ilist) ]]
    POST RET:^(mscs,r)
                   LOG.rep lxp F (ActiveTxn mbase m) mscs * [[ r = IAttr ino ]]
    CRASH          LOG.would_recover_old lxp F mbase
    >} igetattr lxp xp inum mscs.
  Proof.
    unfold igetattr, rep.
    hoare.
    list2nmem_ptsto_cancel; list2nmem_bound.

    rewrite_list2nmem_pred.
    destruct_listmatch_n.
    rec_simpl; subst; auto.
  Qed.

  Theorem isetattr_ok : forall lxp bxp xp inum attr mscs,
    {< F Fm A mbase m ilist ino,
    PRE        LOG.rep lxp F (ActiveTxn mbase m) mscs *
               [[ (Fm * rep bxp xp ilist)%pred (list2mem m) ]] *
               [[ (A * #inum |-> ino)%pred (list2nmem ilist) ]]
    POST RET:mscs
               exists m' ilist' ino',
               LOG.rep lxp F (ActiveTxn mbase m') mscs *
               [[ (Fm * rep bxp xp ilist')%pred (list2mem m') ]] *
               [[ (A * #inum |-> ino')%pred (list2nmem ilist') ]] *
               [[ ino' = Build_inode (IBlocks ino) attr ]]
    CRASH      LOG.would_recover_old lxp F mbase
    >} isetattr lxp xp inum attr mscs.
  Proof.
    unfold isetattr, rep.
    hoare.

    list2nmem_ptsto_cancel; list2nmem_bound.
    list2nmem_ptsto_cancel; list2nmem_bound.
    irec_well_formed.

    repeat rewrite_list2nmem_pred; try list2nmem_bound.
    eapply listmatch_updN_selN; autorewrite with defaults; inode_bounds.
    unfold inode_match; rec_simpl.
    cancel.
    instantiate (dindlist1:=dindlist). instantiate (indlist1:=indlist). instantiate (dind_indlist0:=dind_indlist).
    cancel.
    assumption.
  Qed.


  Theorem iget_ok : forall lxp bxp xp inum off mscs,
    {< F Fm A B mbase m ilist ino a,
    PRE            LOG.rep lxp F (ActiveTxn mbase m) mscs *
                   [[ (Fm * rep bxp xp ilist)%pred (list2mem m) ]] *
                   [[ (A * #inum |-> ino)%pred (list2nmem ilist) ]] *
                   [[ (B * #off |-> a)%pred (list2nmem (IBlocks ino)) ]]
    POST RET:^(mscs,r)
                   LOG.rep lxp F (ActiveTxn mbase m) mscs * [[ r = a ]]
    CRASH          LOG.would_recover_old lxp F mbase
    >} iget lxp xp inum off mscs.
  Proof.
    unfold iget, rep.
    hoare.
    admit.
    
    Search listmatch.



    step.
    list2nmem_ptsto_cancel; inode_bounds.

    step.
    step.

    (* from direct blocks *)
    repeat rewrite_list2nmem_pred.
    destruct_listmatch_n.
    rewrite H21.
    rewrite selN_firstn by inode_bounds.
    rewrite selN_app; [ inode_bounds |].
    erewrite inode_blocks_length with (m := list2mem m); inode_bounds.
    apply wlt_lt in H8; auto.
    pred_apply; cancel.

    (* from indirect blocks *)
    repeat rewrite_list2nmem_pred.
    destruct_listmatch_n.
    step. step.
    erewrite indirect_valid_r_off; eauto.
    cancel. 
    list2nmem_ptsto_cancel.
    Search dummy0.
    eapply indirect_valid_off_bound; eauto.
    erewrite indirect_valid_r_off; eauto.
    step.
    subst.
    rewrite H19.
    rewrite selN_firstn; inode_bounds.
    rewrite selN_app2.
    erewrite inode_blocks_length with (m := list2mem m); inode_bounds.
    rewrite wminus_minus; auto.
    pred_apply; cancel.
    erewrite inode_blocks_length with (m := list2mem m); inode_bounds.
    apply wle_le in H11; auto.
    pred_apply; cancel.
  Qed.


  (* small helpers *)

  Lemma wlt_plus_one_le: forall sz (a : word sz) b,
    b <= wordToNat (natToWord sz b)
    -> (a < natToWord sz b)%word
    -> wordToNat a + 1 <= b.
  Proof.
    intros.
    apply wlt_lt in H0.
    erewrite wordToNat_natToWord_bound in H0; eauto.
    omega.
  Qed.

  Lemma wlt_plus_one_wle: forall sz (a b: word sz),
    (a < b)%word
    -> (a ^+ $1 <= b)%word.
  Proof.
    intros.
    apply wlt_lt in H as X.
    apply le_wle.
    erewrite wordToNat_plusone; eauto.
  Qed.

  Lemma wle_eq_le' : forall sz (a : word sz) b c,
    b <= wordToNat (natToWord sz b)
    -> (natToWord sz b <= a)%word -> wordToNat a = c -> b <= c.
  Proof.
    intros.
    apply wle_le in H0.
    erewrite wordToNat_natToWord_bound in H0; eauto.
    omega.
  Qed.

  Lemma add_one_eq_wplus_one: forall sz (n : word sz) b,
    b + 1 <= wordToNat (natToWord sz (b + 1))
    -> wordToNat n <= b
    -> wordToNat n + 1 = wordToNat (n ^+ $1)%word.
  Proof.
    intros.
    erewrite wordToNat_plusone with (w' := (natToWord sz (b + 1))).
    rewrite Nat.add_1_r; auto.
    apply lt_wlt.
    erewrite wordToNat_natToWord_bound; eauto.
    omega.
  Qed.

  Fact len_plus_one_eq1: forall (n : addr),
    wordToNat n <= nr_direct
    -> wordToNat n + 1 = wordToNat (n ^+ $1)%word.
  Proof.
    intros.
    eapply add_one_eq_wplus_one; eauto.
    simpl; auto.
  Qed.

  Local Hint Resolve len_plus_one_eq1.

  Lemma firstn_plusone_app_selN: forall T n a b (def : T),
    n = length a -> length b > 0
    -> firstn (n + 1) (a ++ b) = a ++ (selN b 0 def) :: nil.
  Proof.
    intros.
    erewrite firstn_plusone_selN; eauto.
    rewrite firstn_app by auto.
    rewrite selN_app2 by omega.
    replace (n - length a) with 0 by omega; auto.
    rewrite app_length; omega.
  Qed.

  Lemma weq_wminus_0 : forall sz (a b : word sz),
    (a = b)%word -> wordToNat (a ^- b)%word = 0.
  Proof.
    intros; subst.
    rewrite wminus_minus.
    omega.
    apply le_wle.
    omega.
  Qed.


  Theorem igrow_direct_ok : forall lxp bxp xp (i0 : irec) inum a mscs,
    {< F Fm A B mbase m ilist (reclist : list irec) ino,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ length (IBlocks ino) < blocks_per_inode ]] *
             [[ i0 = sel reclist inum irec0 ]] *
             [[ i0 :-> "len" < wnr_direct ]]%word *
             [[ (Fm * irrep xp reclist *
                 listmatch (inode_match bxp) ilist reclist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> ino)%pred (list2nmem ilist) ]] *
             [[  B (list2nmem (IBlocks ino)) ]]
    POST RET:^(mscs,r)
             exists m' ilist' ino',
             LOG.rep lxp F (ActiveTxn mbase m') mscs *
             [[ r = true ]] *
             [[ (Fm * rep bxp xp ilist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> ino')%pred (list2nmem ilist') ]] *
             [[ (B * length (IBlocks ino) |-> a)%pred (list2nmem (IBlocks ino')) ]] *
             [[ ino' = Build_inode ((IBlocks ino) ++ [a]) (IAttr ino) ]]
    CRASH    LOG.would_recover_old lxp F mbase
    >} igrow_direct lxp xp i0 inum a mscs.
  Proof.
    unfold igrow_direct, rep.
    step.

    list2nmem_ptsto_cancel; inode_bounds.
    irec_well_formed.
    step.
    2: simpl; eapply list2nmem_app; eauto.

    repeat rewrite_list2nmem_pred; inode_bounds.
    destruct_listmatch_n.

    eapply listmatch_updN_selN; autorewrite with defaults; inode_bounds.
    repeat rewrite inode_match_is_direct; eauto.
    unfold inode_match_direct.
    simpl; unfold sel; autorewrite with core.
    rewrite H10; simpl.
    rec_simpl; cancel.

    eapply wlt_plus_one_le; eauto.
    rewrite <- firstn_app_updN_eq.
    f_equal; auto.

    pose proof (@inode_blocks_length (list2mem m)) as Hibl.
    cbn in Hibl.
    erewrite Hibl; inode_bounds.
    apply wlt_lt in H7; auto.
    pred_apply; cancel.

    apply wlt_plus_one_wle; auto.

    eapply inode_well_formed with (m := list2mem m'); eauto.
    erewrite selN_updN_eq by inode_bounds; eauto.

    eapply inode_well_formed with (m := list2mem m) (l := reclist); eauto.
    pred_apply; cancel.
    inode_bounds.

    Grab Existential Variables.
    exact irec0.
  Qed.


  Lemma wlt_lt_nr_direct: forall (a c : addr) b,
    (wnr_direct < a)%word -> (wordToNat a = b) -> (nr_direct < b).
  Proof.
    intros; subst.
    apply wlt_lt in H; simpl in H.
    simpl; auto.
  Qed.

  Lemma gt_plusone_gt: forall n c,
    n > c -> n + 1 > c.
  Proof.
    intros; omega.
  Qed.

  Lemma indirect_valid_eq : forall l (wl : addr),
    l < nr_direct + nr_indirect
    -> (wl > wnr_direct)%word
    -> l = wordToNat wl
    -> wordToNat wl - nr_direct < nr_indirect.
  Proof.
    intros; subst.
    apply wlt_lt in H0.
    unfold wnr_direct in H0.
    erewrite wordToNat_natToWord_bound in H0; eauto.
    omega.
  Qed.

  Local Hint Resolve wlt_lt_nr_direct.
  Local Hint Resolve gt_plusone_gt.

  Ltac resolve_length_bound := try solve [
    repeat match goal with
    | [ |- context [ length (_ ++ _) ] ] => rewrite app_length
    | [ |- _ >= _ ] => apply Nat.lt_le_incl
    | [ H: length ?a = _ |- context [ length ?a ] ] => setoid_rewrite H
    | [ H: length ?a = _, H2: context [ length ?a ] |- _ ] => rewrite H in H2
    end; eauto; simpl; try omega ].


  Theorem igrow_indirect_ok : forall lxp bxp xp (i0 : irec) inum a mscs,
    {< F Fm A B mbase m ilist (reclist : list irec) ino,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ length (IBlocks ino) < blocks_per_inode ]] *
             [[ i0 :-> "len" > wnr_direct ]]%word *
             [[ i0 = sel reclist inum irec0 ]] *
             [[ (Fm * irrep xp reclist *
                 listmatch (inode_match bxp) ilist reclist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> ino)%pred (list2nmem ilist) ]] *
             [[  B (list2nmem (IBlocks ino)) ]]
    POST RET:^(mscs,r)
             exists m' ilist' ino',
             LOG.rep lxp F (ActiveTxn mbase m') mscs *
             [[ r = true ]] *
             [[ (Fm * rep bxp xp ilist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> ino')%pred (list2nmem ilist') ]] *
             [[ (B * length (IBlocks ino) |-> a)%pred (list2nmem (IBlocks ino')) ]] *
             [[ ino' = Build_inode ((IBlocks ino) ++ [a]) (IAttr ino) ]]
    CRASH    LOG.would_recover_old lxp F mbase
    >} igrow_indirect lxp xp i0 inum a mscs.
  Proof.
    unfold igrow_indirect, rep.
    intros; eapply pimpl_ok2; eauto with prog; intros; norm'l.
    destruct_listmatch_n; rec_simpl.
    rewrite indirect_valid_r in H.
    cancel.

    list2nmem_ptsto_cancel; inode_bounds.
    rewrite wminus_minus; auto.
    erewrite indirect_length; eauto.
    rewrite_list2nmem_pred; inode_bounds.
    eapply indirect_valid_eq; eauto.

    step.
    list2nmem_ptsto_cancel; inode_bounds.
    irec_well_formed.
    step.
    2: simpl; eapply list2nmem_app; eauto.

    (* prove representation invariant *)
    repeat rewrite_list2nmem_pred; inode_bounds.
    unfold upd, sel; unfold sel in *.
    assert (length dummy = nr_indirect) by (eapply indirect_length; eauto).
    assert (length blist' = nr_indirect) by (eapply indirect_length; eauto).
    assert (length ((selN reclist (wordToNat inum) irec0 : Rec.data inodetype) :-> "blocks") = nr_direct) as Hdeq.
    erewrite inode_blocks_length with (m := list2mem m); inode_bounds.
    pred_apply; cancel.

    rec_simpl.
    rewrite listmatch_updN_removeN; inode_bounds; cancel_exact.
    unfold inode_match; autorewrite with core.
    simpl; rewrite app_length; simpl.
    rewrite H17; rewrite H3.
    rewrite firstn_length_l by resolve_length_bound.
    cancel.

    rewrite indirect_valid_r.
    cancel.
    eauto.

    eapply add_one_eq_wplus_one with (b := blocks_per_inode); eauto.
    setoid_rewrite <- H3; auto.

    rewrite firstn_app_updN_eq by resolve_length_bound.
    rewrite updN_app2 by resolve_length_bound.
    repeat f_equal.
    setoid_rewrite Hdeq.
    replace nr_direct with (wordToNat wnr_direct) by auto.
    rewrite <- wminus_minus; auto.
    setoid_rewrite list2nmem_array_updN; inode_bounds.
    resolve_length_bound.

    unfold sel in *; subst; eauto.
  Qed.


  Lemma weq_eq : forall sz a b,
    b = wordToNat (natToWord sz b)
    -> a = natToWord sz b
    -> wordToNat a = b.
  Proof.
    intros; subst a; auto.
  Qed.

  Ltac resolve_length_eq := try solve [erewrite weq_eq; eauto; try omega; eauto].

  Theorem igrow_alloc_ok : forall lxp bxp xp (i0 : irec) inum a mscs,
    {< F Fm A B mbase m ilist (reclist : list irec) freelist ino,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ length (IBlocks ino) < blocks_per_inode ]] *
             [[ i0 = sel reclist inum irec0 ]] *
             [[ i0 :-> "len" = wnr_direct ]]%word *
             [[ (Fm * irrep xp reclist * BALLOC.rep bxp freelist *
                 listmatch (inode_match bxp) ilist reclist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> ino)%pred (list2nmem ilist) ]] *
             [[  B (list2nmem (IBlocks ino)) ]]
    POST RET:^(mscs,r)
            exists m', LOG.rep lxp F (ActiveTxn mbase m') mscs *
            ([[ r = false ]] \/
             [[ r = true ]] * exists ilist' ino' freelist',
             [[ (Fm * rep bxp xp ilist' * BALLOC.rep bxp freelist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> ino')%pred (list2nmem ilist') ]] *
             [[ (B * length (IBlocks ino) |-> a)%pred (list2nmem (IBlocks ino')) ]] *
             [[ ino' = Build_inode ((IBlocks ino) ++ [a]) (IAttr ino) ]])
    CRASH    LOG.would_recover_old lxp F mbase
    >} igrow_alloc lxp bxp xp i0 inum a mscs.
  Proof.
    unfold igrow_alloc, rep.
    rec_simpl.
    step.

    destruct_listmatch_n; rec_simpl.
    destruct_branch; subst; simpl.

    (* CASE 1: indirect block allocating success *)
    step; subst; inv_option_eq; subst; try cancel.
    step.

    (* constructing new indirect list *)
    instantiate (blist := indlist0).
    unfold indrep.
    rewrite ind_ptsto_zero.
    cancel. eauto.

    repeat rewrite_list2nmem_pred; unfold upd; inode_bounds.
    list2nmem_ptsto_cancel; inode_bounds.
    rewrite wminus_minus; auto.
    unfold sel in *; setoid_rewrite H7; simpl; omega.
    step.

    list2nmem_ptsto_cancel; inode_bounds.
    irec_well_formed.
    step.
    eapply pimpl_or_r; right; cancel.
    2: eapply list2nmem_updN; eauto.
    2: simpl; eapply list2nmem_app; eauto.

    (* prove representation invariant *)
    repeat rewrite_list2nmem_pred; unfold upd; inode_bounds.
    eapply listmatch_updN_selN_r; autorewrite with defaults; inode_bounds.
    unfold inode_match; rec_simpl.
    simpl; rewrite app_length; rewrite H6; simpl.
    cancel.

    rewrite indirect_valid_l by resolve_length_eq.
    rewrite indirect_valid_r by (setoid_rewrite H7; auto).

    cancel.
    eapply add_one_eq_wplus_one; eauto; simpl; auto.

    rewrite H18.
    rewrite firstn_app.
    erewrite firstn_plusone_app_selN; autorewrite with defaults.
    rewrite weq_wminus_0; auto.

    (* clean up goals about bounds *)
    unfold sel.
    pose proof (@inode_blocks_length (list2mem a3)) as Hlen; rec_simpl.
    simpl in Hlen; erewrite Hlen; inode_bounds.
    resolve_length_eq.

    pred_apply; cancel.
    erewrite indirect_length with (m := list2mem m'0).
    unfold nr_indirect; omega.
    pred_apply; cancel.

    pose proof (@inode_blocks_length (list2mem a3)) as Hlen; rec_simpl.
    simpl in Hlen; erewrite Hlen; inode_bounds.
    rewrite H6; resolve_length_eq.
    pred_apply; cancel.
    apply LOG.activetxn_would_recover_old.

    (* CASE 2: indirect block allocation failed *)
    step; inv_option_eq; subst; try cancel.

    (* XXX: so many unused existentials ! *)
    Grab Existential Variables.
    exact $0.
    exact emp.
  Qed.


  Theorem igrow_dindirect_ok : forall lxp bxp xp (i0 : irec) inum a mscs,
    {< F Fm A B mbase m ilist (reclist : list irec) ino,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ length (IBlocks ino) < blocks_per_inode ]] *
             [[ i0 :-> "len" > wnr_direct + wnr_indirect ]]%word *
             [[ i0 = sel reclist inum irec0 ]] *
             [[ (Fm * irrep xp reclist *
                 listmatch (inode_match bxp) ilist reclist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> ino)%pred (list2nmem ilist) ]] *
             [[  B (list2nmem (IBlocks ino)) ]]
    POST RET:^(mscs,r)
             exists m' ilist' ino',
             LOG.rep lxp F (ActiveTxn mbase m') mscs *
             [[ r = true ]] *
             [[ (Fm * rep bxp xp ilist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> ino')%pred (list2nmem ilist') ]] *
             [[ (B * length (IBlocks ino) |-> a)%pred (list2nmem (IBlocks ino')) ]] *
             [[ ino' = Build_inode ((IBlocks ino) ++ [a]) (IAttr ino) ]]
    CRASH    LOG.would_recover_old lxp F mbase
    >} igrow_dindirect lxp bxp xp i0 inum a mscs.


  Hint Extern 1 ({{_}} progseq (igrow_direct _ _ _ _ _ _) _) => apply igrow_direct_ok : prog.
  Hint Extern 1 ({{_}} progseq (igrow_indirect _ _ _ _ _ _) _) => apply igrow_indirect_ok : prog.
  Hint Extern 1 ({{_}} progseq (igrow_alloc _ _ _ _ _ _ _) _) => apply igrow_alloc_ok : prog.

  Hint Extern 0 (okToUnify (listmatch _ ?a ?b) (listmatch _ ?a ?b)) => constructor : okToUnify.

  Theorem igrow_ok : forall lxp bxp xp inum a mscs,
    {< F Fm A B mbase m ilist ino freelist,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ length (IBlocks ino) < blocks_per_inode ]] *
             [[ (Fm * rep bxp xp ilist * BALLOC.rep bxp freelist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> ino)%pred (list2nmem ilist) ]] *
             [[  B (list2nmem (IBlocks ino)) ]]
    POST RET:^(mscs,r)
            exists m', LOG.rep lxp F (ActiveTxn mbase m') mscs *
            ([[ r = false ]] \/
             [[ r = true ]] * exists ilist' ino' freelist',
             [[ (Fm * rep bxp xp ilist' * BALLOC.rep bxp freelist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> ino')%pred (list2nmem ilist') ]] *
             [[ (B * length (IBlocks ino) |-> a)%pred (list2nmem (IBlocks ino')) ]] *
             [[ ino' = Build_inode ((IBlocks ino) ++ [a]) (IAttr ino) ]])
    CRASH    LOG.would_recover_old lxp F mbase
    >} igrow lxp bxp xp inum a mscs.
  Proof.
    unfold igrow, rep.
    hoare.

    destruct_listmatch_n.
    list2nmem_ptsto_cancel; inode_bounds.

    unfold rep in H10; destruct_lift H10.
    eapply pimpl_or_r; right; cancel; eauto.

    unfold rep in H11; destruct_lift H11.
    eapply pimpl_or_r; right; cancel; eauto.
  Qed.


  Lemma helper_minus1_nr_direct_gt : forall w n,
    n > 0 -> n = wordToNat w
    -> w ^- $1 = wnr_direct
    -> n > nr_direct.
  Proof.
    intros; subst.
    eapply wlt_lt_nr_direct; eauto.
    eapply weq_minus1_wlt; auto.
  Qed.

  Lemma helper_minus1_nr_direct_eq : forall w n,
    n > 0 -> n = wordToNat w
    -> w ^- $1 = wnr_direct
    -> n - 1 = nr_direct.
  Proof.
    intros; subst.
    erewrite <- roundTrip_1; eauto.
    setoid_rewrite <- wminus_minus.
    unfold wnr_direct in H1.
    apply weq_eq; auto.
    apply le_wle; auto.
  Qed.

  Lemma indirect_valid_shrink: forall bxp n bn l,
    n > 0 -> n - 1 <> nr_direct
    -> indirect_valid bxp n bn l =p=> indirect_valid bxp (n - 1) bn l.
  Proof.
    intros; unfold indirect_valid; cancel.
  Qed.

  Lemma helper_minus1_nr_direct_neq : forall w n,
    n > 0 -> n = wordToNat w
    -> w ^- $1 <> wnr_direct
    -> n - 1 <> nr_direct.
  Proof.
    intros; subst.
    erewrite <- roundTrip_1; eauto.
    setoid_rewrite <- wminus_minus.
    replace nr_direct with (wordToNat wnr_direct) by auto.
    apply wordToNat_neq_inj; auto.
    apply le_wle; auto.
  Qed.

  Local Hint Resolve length_not_nil.
  Local Hint Resolve length_not_nil'.
  Local Hint Resolve wordnat_minus1_eq.
  Local Hint Resolve wordToNat_neq_inj.
  Local Hint Resolve gt0_wneq0.
  Local Hint Resolve neq0_wneq0.

  Theorem ishrink_ok : forall lxp bxp xp inum mscs,
    {< F Fm A B mbase m ilist bn ino freelist,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ length (IBlocks ino) > 0 ]] *
             [[ (Fm * rep bxp xp ilist * BALLOC.rep bxp freelist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> ino)%pred (list2nmem ilist) ]] *
             [[ (B * (length (IBlocks ino) - 1) |-> bn )%pred (list2nmem (IBlocks ino)) ]]
    POST RET:mscs
             exists m' ilist' ino' freelist',
             LOG.rep lxp F (ActiveTxn mbase m') mscs *
             [[ (Fm * rep bxp xp ilist' * BALLOC.rep bxp freelist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> ino')%pred (list2nmem ilist') ]] *
             [[  B (list2nmem (IBlocks ino')) ]] *
             [[ ino' = Build_inode (removelast (IBlocks ino)) (IAttr ino) ]]
    CRASH    LOG.would_recover_old lxp F mbase
    >} ishrink lxp bxp xp inum mscs.
  Proof.
    unfold ishrink, rep.
    step.
    destruct_listmatch_n; rec_simpl.
    list2nmem_ptsto_cancel; inode_bounds.
    step.

    (* CASE 1 : free the indirect block *)
    destruct_listmatch_n; rec_simpl.
    step.

    repeat rewrite_list2nmem_pred.
    rewrite indirect_valid_r.
    rewrite ind_ptsto; cancel.
    eapply helper_minus1_nr_direct_gt; eauto.
    rewrite indirect_valid_r in H.
    unfold indrep, BALLOC.valid_block in H.
    destruct_lift H; auto.
    repeat rewrite_list2nmem_pred.
    eapply helper_minus1_nr_direct_gt; eauto.
    step.

    list2nmem_ptsto_cancel; inode_bounds.
    irec_well_formed.
    step.
    2: simpl; eapply list2nmem_removelast; eauto.

    repeat rewrite_list2nmem_pred; unfold upd; inode_bounds.
    rewrite length_updN in *.
    setoid_rewrite listmatch_isolate with (i := wordToNat inum)
      (ad := inode0) (bd := irec0) at 2; inode_bounds.
    autorewrite with core; cancel.
    rewrite inode_match_is_direct.
    2: auto.
    unfold inode_match_direct; rec_simpl.
    simpl; autorewrite with core; simpl.
    rewrite length_removelast; auto.
    cancel.

    erewrite wordnat_minus1_eq; eauto.
    replace nr_direct with (wordToNat wnr_direct); auto.


    (* extract facts about length *)
    rewrite indirect_valid_r in H.
    2: eapply helper_minus1_nr_direct_gt; eauto.
    assert (length dummy0 = nr_indirect) as Hieq.
    eapply indirect_length with (m := list2mem m); pred_apply; cancel.
    assert (length ((selN dummy (wordToNat inum) irec0) :-> "blocks") = nr_direct) as Hdeq.
    erewrite inode_blocks_length with (m := list2mem m'); inode_bounds.
    pred_apply; cancel.
    assert (length (IBlocks (selN ilist (wordToNat inum) inode0)) - 1 = nr_direct).
    eapply helper_minus1_nr_direct_eq; eauto.

    rewrite H19 at 1.
    rewrite removelast_firstn_sub; auto.
    rewrite firstn_app_l; auto.
    setoid_rewrite Hdeq; omega.
    rewrite app_length.
    setoid_rewrite Hdeq; rewrite Hieq; unfold nr_indirect; omega.
    apply length_not_nil; auto.
    irec_well_formed.
    apply length_not_nil; auto.

    (* CASE 2 *)
    destruct_listmatch_n; rec_simpl.
    step.
    list2nmem_ptsto_cancel; inode_bounds.
    irec_well_formed.
    step.
    2: simpl; eapply list2nmem_removelast; eauto.

    repeat rewrite_list2nmem_pred; unfold upd; inode_bounds.
    rewrite length_updN in *.
    setoid_rewrite listmatch_isolate with (i := #inum)
      (ad := inode0) (bd := irec0) at 2; inode_bounds.
    autorewrite with core; cancel.
    unfold inode_match; rec_simpl.
    simpl; autorewrite with core; simpl.
    rewrite length_removelast.
    cancel.

    apply indirect_valid_shrink; auto.
    eapply helper_minus1_nr_direct_neq; eauto.

    rewrite H19 at 1.
    rewrite removelast_firstn_sub; auto.
    rewrite H19.
    rewrite firstn_length.
    apply Min.le_min_r.
    apply length_not_nil; auto.
    apply length_not_nil; auto.
  Qed.

  Hint Extern 1 ({{_}} progseq (ilen _ _ _ _) _) => apply ilen_ok : prog.
  Hint Extern 1 ({{_}} progseq (igetattr _ _ _ _) _) => apply igetattr_ok : prog.
  Hint Extern 1 ({{_}} progseq (isetattr _ _ _ _ _) _) => apply isetattr_ok : prog.
  Hint Extern 1 ({{_}} progseq (iget _ _ _ _ _) _) => apply iget_ok : prog.
  Hint Extern 1 ({{_}} progseq (igrow _ _ _ _ _ _) _) => apply igrow_ok : prog.
  Hint Extern 1 ({{_}} progseq (ishrink _ _ _ _ _) _) => apply ishrink_ok : prog.

  Definition init T lxp (ibxp : balloc_xparams) ixp mscs rx : prog T :=
    mscs <- RecArray.init inodetype items_per_valu itemsz_ok lxp (xp_to_raxp ixp) mscs;
    rx mscs.

  Theorem listmatch_inode0 : forall xp l,
    Forall (fun i => i = item_zero inodetype) l ->
    emp =p=> listmatch (inode_match xp) (repeat inode0 (length l)) l.
  Proof.
    unfold listmatch; cancel; try rewrite repeat_length; auto.
    induction l.
    cancel.
    simpl; fold repeat.
    rewrite Forall_forall in H.
    assert (H' := H).
    specialize (H' a). specialize (H' (@in_eq _ _ _)).
    simpl in *. subst.
    rewrite IHl. cancel.
    unfold inode_match.
    simpl.
    cancel.
    instantiate (blist := nil). unfold indirect_valid. unfold indrep. unfold array_item.
    cancel.
    unfold iattr_match. intuition.
    rewrite Forall_forall in *; intros.
    apply H.
    eauto.
  Qed.

  Theorem init_ok : forall lxp ibxp ixp mscs,
    {< F Fm mbase m,
    PRE      exists ai, LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ (Fm * array (IXStart ixp) ai $1)%pred (list2mem m) ]] *
             [[ length ai = # (IXLen ixp) ]] *
             [[ goodSize addrlen (# (IXLen ixp) * # (items_per_valu)) ]]
    POST RET:mscs
             exists m' ilist,
             LOG.rep lxp F (ActiveTxn mbase m') mscs *
             [[ (Fm * rep ibxp ixp ilist)%pred (list2mem m') ]]
    CRASH    LOG.would_recover_old lxp F mbase
    >} init lxp ibxp ixp mscs.
  Proof.
    unfold init.
    step.
    step.
    unfold rep, irrep. cancel.
    instantiate (reclist := l); cancel.
    instantiate (ilist := (repeat inode0 (length l))).
    rewrite <- listmatch_inode0; eauto.
    unfold irec; simpl.
    replace (length l).
    word2nat_auto.
  Qed.

  Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.

End INODE.
