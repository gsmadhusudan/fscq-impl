open FsLayout
open InodeRWMod
open DirApp
open EndToEnd
open Printf
open Sys

let disk_fn = "disk.img"

let read_disk b =
  let ic = open_in_gen [Open_rdonly;Open_creat] 0o666 disk_fn in
  seek_in ic b;
  try
    let v = input_byte ic in
    close_in ic;
    v
  with
    End_of_file -> close_in ic; 0

let write_disk b v =
  let oc = open_out_gen [Open_wronly;Open_creat] 0o666 disk_fn in
  seek_out oc b;
  output_byte oc v;
  close_out oc

let rec run_dcode_real p =
  match p with
  | FsLayout.FsDisk.Read (b, rx) ->
    let v = read_disk b in
    Printf.printf "read(%d): %d\n" b v;
    run_dcode_real (rx v)
  | FsLayout.FsDisk.Write (b, v, rx) ->
    Printf.printf "write(%d, %d)\n" b v;
    write_disk b v; run_dcode_real (rx ())
  | FsLayout.FsDisk.Return r ->
    Printf.printf "return(%d)\n" r

let dacode = 
  DirApp.DAAlloc (fun di ->
  DirApp.DASet (di, 22, 23,
  DirApp.DAGet (di, 22, (fun v ->
  DirApp.DAReturn v
  )))) ;;

let fcode = DirApp.compile_da dacode;;

let xxx =
  InodeRW.Alloc (fun o -> match Obj.magic o with
  | None -> InodeRW.Return (-1)
  | Some f ->
  InodeRW.Grow (f, 1, fun ok -> match ok with
  | false -> InodeRW.Return (-2)
  | true ->
  InodeRW.Write (f, 0, 35, fun _ ->
  InodeRW.Grow (f, 2, fun ok -> match ok with
  | false -> InodeRW.Return (-3)
  | true ->
  InodeRW.Write (f, 1, 36, fun _ ->
  InodeRW.Read (f, 0, fun va ->
  InodeRW.Read (f, 1, fun vb ->
  InodeRW.Return (va+vb)
  )))))));;

let dcode =
  InodeRWToDisk.coq_Compile fcode;;

Printf.printf "Running fcode..\n";;
try Sys.remove disk_fn with Sys_error _ -> ();;
run_dcode_real dcode;;

