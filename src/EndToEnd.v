Require Import Util.
Require Import Smallstep.
Require Import DiskMod.
Require Import FsLayout.
Require Import FsPartsMod.
Require Import BmapLayout.
Require Import BmapAllocOneMod.
Require Import BmapAllocPairMod.
Require Import BmapAllocMod.
Require Import InodeLayout.
Require Import InodeAllocMod.
Require Import InodeRWMod.

Module BmapAllocOneToDisk := RefineChain BmapAllocOne BmapStore BmapPartDisk BmapAllocOneToStore BmapToDisk.
Module BmapAllocPairToDisk := RefineChain BmapAllocPair BmapAllocOne BmapPartDisk BmapAllocPairToAllocOne BmapAllocOneToDisk.
Module BmapAllocToDisk := RefineChain BmapAlloc BmapAllocPair BmapPartDisk BmapAllocToAllocPair BmapAllocPairToDisk.

Module InodeAllocToDisk := RefineChain InodeAlloc InodeStore InodePartDisk InodeAllocToStore InodeToDisk.

Module BlocksSelf := RefineSelf BlocksPartDisk.

Module FsPartsTopToFsPartsDisk := RefineFsParts InodeAlloc BmapAlloc BlocksPartDisk
                                                InodePartDisk BmapPartDisk BlocksPartDisk
                                                FsPartsTop FsPartsDisk
                                                InodeAllocToDisk
                                                BmapAllocToDisk
                                                BlocksSelf.
Module FsPartsTopToDisk := RefineChain FsPartsTop FsPartsDisk FsDisk FsPartsTopToFsPartsDisk FsPartsOnDisk.

Module InodeRWToDisk := RefineChain InodeRW FsPartsTop FsDisk InodeRWToFsPartsTop FsPartsTopToDisk.
