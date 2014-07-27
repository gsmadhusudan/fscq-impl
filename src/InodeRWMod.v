Require Import CpdtTactics.
Require Import FsTactics.
Require Import Util.
Require Import Smallstep.
Require Import Closures.
Require Import Tactics.
Require Import InodeAllocMod.
Require Import BmapAllocMod.
Require Import DiskMod.
Require Import FsPartsMod.
Require Import FsLayout.
Open Scope fscq.


Module InodeRW <: SmallStepLang.

End InodeRW.


Module FsPartsTop := FsParts InodeAlloc BmapAlloc BlocksPartDisk.
Module InodeRWToFsPartsTop <: Refines InodeRW FsPartsTop.

End InodeRWToFsPartsTop.
