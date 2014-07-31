Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import EndToEnd.
Require Import DirApp.

Extraction Blacklist List String Int.

Cd "codegen".
Recursive Extraction Library EndToEnd.
Recursive Extraction Library DirApp.
