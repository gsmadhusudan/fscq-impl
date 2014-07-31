Require Import List.
Require Import Arith.
Require Import NPeano.
Import ListNotations.
Require Import CpdtTactics.
Require Import FsTactics.
Require Import Util.
Require Import InodeRWMod.
Require Import Closures.
Require Import FsLayout.
Require Import InodeLayout.
Require Import Program.Utils.

(*
 * DirApp keeps, in a file, a mapping from file name to i-number.
 * It's a toy directory.
 *)

Definition filename := nat. (* for now, a file name is really a number. *)

Inductive daproc :=
| DASet (di: inodenum) (name: filename) (inumber: inodenum) (rx: daproc)
| DAGet (di: inodenum) (name: filename) (rx: inodenum -> daproc).

(* XXX what is R? *)
(* XXX what is Return? *)
(* XXX what is Program? *)
(* XXX if off is iblocknum, can't guess decreasing argument *)
(* XXX if off is nat, do_set think do_set_iter is undefined *)
(* Program, off:ilength, { measure off } *)
(* passing (len+1) to grow causes do_set_iter to be undefined *)
(*   maybe len+1 is no longer clearly an ilength (i.e. <=NBlockPerInode) *)

Program Definition append_entry (di : inodenum)
   (name : filename) (inumber : nat)
   (len : ilength)
   (rx: InodeRW.Prog nat) : (InodeRW.Prog nat) :=
if dec (leb (len + 2) NBlockPerInode) then
  ok1 <- InodeRW.Grow di (len + 1) ; 
  ok2 <- InodeRW.Grow di (len + 2)  ; 
  ok3 <- InodeRW.Write di len name ;
  ok4 <- InodeRW.Write di (len + 1) inumber ;
  rx
else
  rx. (* XXX error *)

Obligation 1.
Admitted.
Obligation 2.
Admitted.
Obligation 3.
Admitted.
Obligation 4.
Admitted.

Program Fixpoint do_set_iter (di : inodenum)
   (name : filename) (inumber : nat)
   (len : ilength) (off : ilength) 
   (rx: InodeRW.Prog nat) { measure off } : (InodeRW.Prog nat) :=
match off with
| O => append_entry di name inumber len rx
| S (S n) => 
      nx <- InodeRW.Read di (off - 2) ;
      if eq_nat_dec nx name then
        InodeRW.Write di (off - 1) inumber (fun _ => rx)
      else
        do_set_iter di name inumber len n rx
| (S n) => rx
end.

Obligation 1.
Admitted.
Obligation 2.
Admitted.
Obligation 3.
Admitted.

Program Definition do_set (di: inodenum) (name: filename) (inumber: inodenum)
                          (rx: InodeRW.Prog nat) : (InodeRW.Prog nat) :=
  lll <- InodeRW.GetLen di ;
  do_set_iter di name inumber lll lll rx.

Program Fixpoint do_get_iter (di: inodenum)
                     (name: filename)
                     (len: ilength) (off: ilength)
                     (rx: inodenum -> InodeRW.Prog nat)
                     { measure off }
                     : InodeRW.Prog nat :=
match off with
| O => rx 0
| S (S n) =>
      nx <- InodeRW.Read di (off - 2) ;
      ix <- InodeRW.Read di (off - 1) ;
      if eq_nat_dec nx name then
        rx ix
      else
        do_get_iter di name len n rx
| S n => rx 0
end.

Obligation 1.
Admitted.
Obligation 2.
Admitted.
Obligation 3.
Admitted.
Obligation 4.
Admitted.
Obligation 5.
Admitted.
Obligation 7.
Admitted.

Program Definition do_get (di: inodenum) (name: filename)
                          (rx: inodenum -> InodeRW.Prog nat)
                          : InodeRW.Prog nat :=
  lll <- InodeRW.GetLen di ;
  do_get_iter di name lll lll rx.

Program Definition do_init rx : InodeRW.Prog nat :=
  InodeRW.Alloc (fun o =>
    match o with
    | None => rx 0 (* XXX error *)
    | Some di => rx di
    end ).

Program Fixpoint compile_da (p: daproc) : InodeRW.Prog nat :=
match p with
| DASet di name inumber rx => do_set di name inumber (compile_da rx)
| DAGet di name rx => do_get di name (fun v => compile_da (rx v))
end.
