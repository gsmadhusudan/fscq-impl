Require Import List.
Require Import Arith.
Require Import NPeano.
Import ListNotations.
Require Import CpdtTactics.
Require Import FsTactics.
Require Import FileSpec.
Require Import Util.
Require Import Closures.
Require Import FsLayout.

(*
 * DirApp keeps, in a file, a mapping from file name to i-number.
 * It's a toy directory.
 *)

Open Scope fscq_scope.

Definition filename := nat. (* for now, a file name is really a number. *)

Inductive daproc :=
| DAHalt
| DASet (di: inodenum) (name: filename) (inumber: inodenum) (rx: daproc)
| DAGet (di: inodenum) (name: filename) (rx: inodenum -> daproc).

Fixpoint do_set_iter (di: inodenum) (off: blockoffset) (len: blockoffset)
                     (name: filename) (inumber: inodenum)
                     (rx: fprog) : fprog :=
match off with
| O => FCommon (FTrunc di (len + 2))
        (fun _ => FCommon (FWrite di len name) 
          (fun _ => FCommon (FWrite di (len + 1) inumber) 
            (fun _ => rx)))
| S (S n) =>
      nx <- FCommon (FRead di (off - 2)) ;
      if eq_nat_dec nx name then
        FCommon (FWrite di (off - 1) inumber) (fun _ => rx)
      else
        do_set_iter di n len name inumber rx
| S n => rx
end.

Program Definition do_set (di: inodenum) (name: filename) (inumber: inodenum)
                          (rx: fprog) : fprog :=
  lll <- FCommon (FGetLen di) ;
  do_set_iter di lll lll name inumber rx.

Fixpoint do_get_iter (di: inodenum) (off: blockoffset) (len: blockoffset)
                     (name: filename) (rx: inodenum -> fprog) : fprog :=
match off with
| O => rx 0
| S (S n) =>
      nx <- FCommon (FRead di (off - 2)) ;
      ix <- FCommon (FRead di (off - 1)) ;
      if eq_nat_dec nx name then
        rx ix
      else
        do_get_iter di n len name rx
| S n => rx 0
end.

Program Definition do_get (di: inodenum) (name: filename)
                          (rx: inodenum -> fprog) : fprog :=
  lll <- FCommon (FGetLen di) ;
  do_get_iter di lll lll name rx.

Definition do_init rx : fprog :=
  FCommon FAlloc (fun o =>
    match o with
    | None => FHalt
    | Some di => rx di
    end ).

(* 
 * compile a DirApp script to a FileSpec script.
 *)
Fixpoint compile_da (p: daproc) : fprog :=
match p with
| DAHalt => FHalt
| DASet di name inumber rx => do_set di name inumber (compile_da rx)
| DAGet di name rx => do_get di name (fun v => compile_da (rx v))
end.
