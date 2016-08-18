Require Import CoopConcur.
Require Import CoopConcurAuto.
Require Import Protocols.
Require Import ConcurrentCache.
Require Import DiskReaders.
Require Import Omega.
Import Hlist.
Import Hlist.HlistNotations.
Open Scope hlist_scope.

(* somewhat oddly, Sigma now refers to the cache state - would have hidden that
and referred to it qualified if Coq let me do so cleanly *)

(** TODO: give copy a non-trivial protocol and prove retrying for this specific
example. *)

(** Copy example

Each thread tid copies from address 0 to the location (tid+1). *)

Module CopyState <: GlobalState.
  Definition Sigma := Sigma.
End CopyState.

Module CopyCacheProj <: CacheProj CopyState.
  Hint Constructors List.NoDup.
  Hint Extern 4 False => omega.
  Definition stateProj : StateProj CopyState.Sigma Sigma.
    unshelve econstructor; simpl.
    exact [( HFirst; (HNext HFirst) )].
    exact [( HFirst;
             HNext HFirst;
             HNext (HNext HFirst);
             HNext (HNext (HNext HFirst)) )].
    repeat (constructor; simpl; intuition auto).
    repeat (constructor; simpl; intuition auto).
  Defined.
End CopyCacheProj.

Module CacheProtocol := MakeCacheProtocol CopyState CopyCacheProj.

Definition destinations_readonly tid (s s': abstraction CopyState.Sigma) :=
  forall a, a <> tid + 1 ->
       get CacheProtocol.vdisk s' a = get CacheProtocol.vdisk s a.

Theorem destinations_readonly_preorder : forall tid,
    PreOrder (destinations_readonly tid).
Proof.
  unfold destinations_readonly; intros.
  constructor; hnf; intros; eauto.
  rewrite <- H by auto.
  eauto.
Qed.

Module App <: GlobalProtocol.
  Module St := CopyState.
  Definition Sigma := St.Sigma.

  Definition copyGuar tid (s s': abstraction Sigma) :=
    guar CacheProtocol.delta tid s s' /\
    destinations_readonly tid s s'.

  Theorem copyGuar_preorder : forall tid, PreOrder (copyGuar tid).
  Proof.
    intros.
    (* TODO: move and_preorder somewhere else *)
    apply CacheProtocol.and_preorder.
    apply guar_preorder.
    apply destinations_readonly_preorder.
  Qed.

  Definition delta :=
    {| invariant := invariant CacheProtocol.delta;
       guar := copyGuar;
       guar_preorder := copyGuar_preorder |}.
End App.

Theorem vdisk_not_cache_or_disk0 :
  HIn CacheProtocol.vdisk [(CacheProtocol.vCache; CacheProtocol.vDisk0)] -> False.
Proof.
  rewrite (hin_iff_index_in CacheProtocol.vdisk); simpl.
  unfold CacheProtocol.vCache, CacheProtocol.vdisk, CacheProtocol.vDisk0.
  simpl.
  repeat (rewrite get_first; simpl) ||
         (rewrite get_next; simpl).
  intuition.
Qed.

Hint Resolve vdisk_not_cache_or_disk0.

Module CacheSub <: CacheSubProtocol.
  Module App := App.
  Module Proj := CopyCacheProj.

  Module CacheProtocol := CacheProtocol.

  Definition protocolProj:SubProtocol App.delta CacheProtocol.delta.
  Proof.
    constructor.
    - auto.
    - intros.
      apply H.
  Qed.

  Definition protocolRespectsPrivateVars :
    forall tid s s',
      guar CacheProtocol.delta tid s s' ->
      modified [( CacheProtocol.vCache; CacheProtocol.vDisk0 )] s s' ->
      guar App.delta tid s s'.
  Proof.
    simpl; intros.
    unfold App.copyGuar; split; auto.
    unfold destinations_readonly; intros.
    assert (get CacheProtocol.vdisk s = get CacheProtocol.vdisk s').
    apply H0; auto.
    congruence.
  Qed.

  Definition invariantRespectsPrivateVars :
    forall d m s d' m' s',
      invariant App.delta d m s ->
      modified [( CacheProtocol.vCache; CacheProtocol.vDisk0 )] s s' ->
      modified [( CacheProtocol.mCache )] m m' ->
      invariant CacheProtocol.delta d' m' s' ->
      invariant App.delta d' m' s'.
  Proof.
    simpl; intros; auto.
  Qed.

End CacheSub.

Module ConcurrentCache := MakeConcurrentCache CacheSub.
Import ConcurrentCache.

Definition copy :=
  tid <- GetTID;
  opt_v <- cache_read 0;
    match opt_v with
    | None => _ <- cache_abort;
               Ret false
    | Some v => ok <- cache_write (tid+1) v;
                 if ok then
                   Ret true
                 else
                   _ <- cache_abort;
                 Ret false
    end.
(* TODO: add a yield after aborts *)

Hint Extern 1 {{cache_read _; _}} => apply cache_read_ok : prog.

(* gives all cache variables *)
Import CacheSub.CacheProtocol.

Theorem copy_ok :
    SPEC App.delta, tid |-
                {{ v v',
                 | PRE d m s_i s:
                     invariant App.delta d m s /\
                     get vdisk s 0 = Some v /\
                     get vdisk s (tid+1) = Some v'
                 | POST d' m' s_i' s' r:
                     invariant App.delta d' m' s' /\
                     (r = true ->
                      get vdisk s' = upd (get vdisk s) (tid+1) v) /\
                     (r = false ->
                      get vdisk s' = hide_readers (get vDisk0 s))
                       (* TODO: promise rely/guar *)
                }} copy.
Proof.
  hoare.
  eexists; simplify; finish.
  hoare.
  assert (w = v).
  { match goal with
    | [ H: forall _, Some ?w = Some _ -> _ |- _ ] =>
      specialize (H w)
    end; eauto. }
  subst.

  assert (get vdisk s = get vdisk s0) as Hvdiskeq.
  match goal with
  | [ H: modified _ s s0 |- _ ] =>
    apply H; auto
  end.
  eexists; simplify; finish.
  (* TODO: get vdisk s0's are different - probably something module-related *)
  Set Printing Implicit.
  (* Hvdisk is about variable in CopyState.Sigma whereas goal is about
  CacheSub.App.Sigma *)
  unfold CacheSub.App.Sigma.
  unfold CacheSub.App.St.Sigma.
  unfold CopyState.Sigma in Hvdiskeq.
  rewrite <- Hvdiskeq.
  Unset Printing Implicit.

  eauto.
  hoare.
Qed.

(* Local Variables: *)
(* company-coq-local-symbols: (("delta" . ?δ) ("Sigma" . ?Σ)) *)
(* End: *)