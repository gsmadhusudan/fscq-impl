Require Import CpdtTactics.
Require Import Closures.

(*
 * XXX
 * We should have more complete definitions of forward and backward
 * simulation, including initial and final states, and a progress
 * condition for backward simulation.  Compcert's definitions:
 *
 *    http://compcert.inria.fr/doc/html/Smallstep.html
 *
 * XXX
 * Do we need the order part of compcert's fsim/bsim?
 * Yes, for fsim->bsim.
 *
 * XXX
 * We should copy over a proof of backward simulation from forward
 * simulation and determinism.
 *)

Definition forward_simulation {StateA StateB:Type} (SA:StateA->StateA->Prop) (SB:StateB->StateB->Prop) :=
  exists (MATCH:StateA->StateB->Prop),
  forall A1 A2, SA A1 A2 -> 
  forall B1, MATCH A1 B1 ->
  exists B2, star SB B1 B2 /\ MATCH A2 B2.

Definition bsim_simulation {StateA StateB:Type} (StepA:StateA->StateA->Prop) (StepB:StateB->StateB->Prop) :=
  exists (Match:StateA->StateB->Prop),
  forall B1 B2, StepB B1 B2 ->
  forall A1, Match A1 B1 ->
  exists A2, Match A2 B2 /\ plus StepA A1 A2.


(* Common infrastructure for nested programs *)

Inductive progstate {R:Type} {P:Type->Type} {S:Type} :=
  | PS (p:P R) (s:S).

Inductive progreturns {R:Type} {P:Type->Type} {S:Type}
                      (STEP:@progstate R P S -> @progstate R P S -> Prop)
                      (RET:R->P R):
                      P R -> S -> S -> R -> Prop :=
  | ProgRet: forall (p:P R) (s:S) (s':S) (r:R)
    (STAR: star STEP (PS p s) (PS (RET r) s')),
    progreturns STEP RET p s s' r.

Inductive progmatch {R:Type} {P1 P2:Type->Type} {S1 S2:Type}
                    (COMPILE:P1 R->P2 R)
                    (MATCH:S1->S2->Prop) :
                    @progstate R P1 S1 ->
                    @progstate R P2 S2 -> Prop :=
  | ProgMatch: forall (p1:P1 R) (p2:P2 R) (s1:S1) (s2:S2)
    (C: COMPILE p1 = p2)
    (M: MATCH s1 s2),
    progmatch COMPILE MATCH (PS p1 s1) (PS p2 s2).
Hint Constructors progmatch.


Module Type SmallStepLang.

Parameter Prog: Type->Type.
Parameter ReturnOp: forall (R:Type), R->(Prog R).
Parameter State: Type.
Parameter Step: forall (R:Type), @progstate R (@Prog) State ->
                                 @progstate R (@Prog) State -> Prop.

End SmallStepLang.


Module Type Refines (L1 L2: SmallStepLang).

Parameter Compile: forall (R:Type), L1.Prog R -> L2.Prog R.
Parameter StateMatch: L1.State -> L2.State -> Prop.
Axiom FSim: forall R, forward_simulation (L1.Step R) (L2.Step R).

End Refines.


Module RefineSelf (L: SmallStepLang) <: Refines L L.

Definition Compile (R:Type) (p:L.Prog R) := p.

Inductive statematch : L.State -> L.State -> Prop :=
  | Match: forall s, statematch s s.
Definition StateMatch := statematch.
Hint Constructors statematch.

Theorem FSim:
  forall R,
  forward_simulation (L.Step R) (L.Step R).
Proof.
  intros; exists (@progmatch R L.Prog L.Prog L.State L.State (Compile R) statematch); intros.

  repeat match goal with
  | [ x: progmatch _ _ _ _ |- _ ] => inversion x; clear x; subst
  | [ x: statematch _ _ |- _ ] => inversion x; clear x; subst
  end.

  exists A2; split.
  - eapply star_step; [ apply H | apply star_refl ].
  - destruct A2. crush.
Qed.

End RefineSelf.


Module FSimReturn (L1 L2: SmallStepLang)
                  (Ref12: Refines L1 L2).

(* XXX need to prove that forward simulation implies same return value *)

Theorem fsim_implies_returns:
  forall (R:Type) p s1 s1' s2 r,
  progreturns (L1.Step R) (L1.ReturnOp R) p s1 s1' r ->
  exists s2',
  progreturns (L2.Step R) (L2.ReturnOp R) (Ref12.Compile R p) s2 s2' r /\
  Ref12.StateMatch s1' s2'.
Proof.
  admit.
Qed.

End FSimReturn.
