Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import EndToEnd.

Extraction Blacklist List String Int.

Cd "codegen".
Recursive Extraction Library EndToEnd.
