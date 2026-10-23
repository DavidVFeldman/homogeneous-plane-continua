### Table 1. Closures

| target | raw closure (constants) | used declarations | share | modules with a used declaration | share | lines covered | share |
|---|---:|---:|---:|---:|---:|---:|---:|
| **primary** (`ho16_classification_plane₄`, `ho16_classification₄`) | 17643 | 4689 | 40.1 % | 446 | 51.7 % | 92845 | 36.3 % |
| `HPC.BJ59.ho16_classification_atomic'` | 16078 | 4176 | 35.7 % | 419 | 48.6 % | 87172 | 34.1 % |
| `HPC.BJ59.bjThm10` | 4669 | 526 | 4.5 % | 82 | 9.5 % | 14014 | 5.5 % |
| `HPC.BJ59.bjPlaneExample` | 2663 | 395 | 3.4 % | 32 | 3.7 % | 4473 | 1.7 % |
| `HPC.Plane.isPseudoArc_plane` | 1742 | 213 | 1.8 % | 21 | 2.4 % | 2312 | 0.9 % |

The library (the three `lean_lib`s): 11697 counted declarations, 863 modules, 255835 source lines.

### Table 2. By directory (primary closure)

| directory | modules | with a used declaration | declarations | used | share | lines | lines covered | share |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| root files (`HPC.lean`, `HPCArchive.lean`, `HPCCensus.lean`) | 3 | 0 | 0 | 0 | – | 337 | 0 | 0.0 % |
| `HPC/Archive` | 25 | 0 | 570 | 0 | 0.0 % | 6356 | 0 | 0.0 % |
| `HPC/BJ59` | 73 | 54 | 770 | 594 | 77.1 % | 17210 | 11319 | 65.8 % |
| `HPC/Census` | 2 | 0 | 58 | 0 | 0.0 % | 408 | 0 | 0.0 % |
| `HPC/Chains` | 5 | 4 | 98 | 62 | 63.3 % | 1933 | 971 | 50.2 % |
| `HPC/Covers` | 1 | 1 | 48 | 46 | 95.8 % | 450 | 357 | 79.3 % |
| `HPC/Effros` | 4 | 4 | 64 | 46 | 71.9 % | 918 | 587 | 63.9 % |
| `HPC/Fold` | 172 | 21 | 3123 | 120 | 3.8 % | 57265 | 3130 | 5.5 % |
| `HPC/HO16` | 50 | 43 | 826 | 707 | 85.6 % | 14444 | 10783 | 74.7 % |
| `HPC/Hagopian` | 193 | 74 | 1449 | 517 | 35.7 % | 48855 | 13146 | 26.9 % |
| `HPC/Jones` | 54 | 49 | 751 | 579 | 77.1 % | 16195 | 10250 | 63.3 % |
| `HPC/Moore` | 124 | 103 | 1070 | 858 | 80.2 % | 31040 | 19954 | 64.3 % |
| `HPC/Plane` | 117 | 68 | 2434 | 913 | 37.5 % | 48162 | 16537 | 34.3 % |
| `HPC/PseudoArc` | 29 | 14 | 308 | 129 | 41.9 % | 8542 | 2641 | 30.9 % |
| `HPC/Span` | 11 | 11 | 128 | 118 | 92.2 % | 3720 | 3170 | 85.2 % |
| **total** | 863 | 446 | 11697 | 4689 | 40.1 % | 255835 | 92845 | 36.3 % |

### Table 3. Unused modules by directory

| directory | unused modules | of which import-only | their declarations | their lines |
|---|---:|---:|---:|---:|
| `.` | 3 | 0 | 0 | 337 |
| `HPC/Archive` | 25 | 0 | 570 | 6356 |
| `HPC/BJ59` | 19 | 11 | 131 | 2995 |
| `HPC/Census` | 2 | 0 | 58 | 408 |
| `HPC/Chains` | 1 | 0 | 15 | 166 |
| `HPC/Fold` | 151 | 57 | 2889 | 50990 |
| `HPC/HO16` | 7 | 5 | 86 | 1309 |
| `HPC/Hagopian` | 119 | 115 | 769 | 27723 |
| `HPC/Jones` | 5 | 5 | 46 | 1021 |
| `HPC/Moore` | 21 | 21 | 85 | 3290 |
| `HPC/Plane` | 49 | 36 | 1159 | 18444 |
| `HPC/PseudoArc` | 15 | 13 | 125 | 4316 |
| **total** | 417 | 263 | 5933 | 117355 |

Module lists (import-only modules marked †):

* `.`: `HPC`, `HPCArchive`, `HPCCensus`
* `HPC/Archive`: `Audit50`, `Audit51`, `Audit55`, `CeilNarrow`, `ClosureFWitness`, `CoverL5`, `CoverL5Low`, `CrossServed`, `CrossValley`, `DecideWitness`, `Descent73`, `FloorFar`, `Glue76`, `LinkFold`, `MixedThin`, `Most51Geom`, `Recon86End`, `Recon87`, `Reflect`, `Target73`, `Target74`, `Target75`, `ThinSpan9`, `ThreeWalksThin`, `ValleyNarrow`
* `HPC/BJ59`: `BJ59C`†, `DP61`†, `NonVac198`, `NonVac199`, `NonVac200`†, `NonVac200b`†, `NonVac201`†, `NonVac201b`†, `NonVac202`, `NonVac202b`, `NonVac202c`, `Sweep3`, `Taut`, `Thm5Cert`, `Thm9`†, `Thm9Base`†, `Thm9Class`†, `Thm9D`†, `Thm9E`†
* `HPC/Census`: `Census87`, `Census87Checks`
* `HPC/Chains`: `Counterexample`
* `HPC/Fold`: `Agree`†, `ArmReflect`, `ArmReflectGap`, `Audit52`, `Audit57`, `Audit58`, `Audit59`, `Audit71`, `Audit72`, `Audit76`, `Bing9`, `Bing9Shave`, `Bing9ShaveWitness`, `Bing9Witness`, `BingLocal`†, `Bump`†, `Ceil68`, `Ceil69`, `CeilArm`, `CeilCross`, `CeilFar`, `Choice`†, `Closure`†, `ClosureF`†, `ClosureTight`†, `CoverL5Land`, `Crook`, `CrossArm`, `CrossCeil`, `CrossMid2Fail65`, `CrossPair62`, `CrossPair63`, `CrossPartner64`, `CrossW71`, `CrossWitness`, `Cut`†, `CutRoute`†, `Decide`, `Deep70`, `Dichotomy`†, `DichotomyFaithful`†, `DichotomyWitness`†, `Distance71`, `ExitReach`†, `ExitReachFWitness`, `Exits`†, `General`, `Interior`†, `Interval`†, `IntervalWitness`†, `Itinerary`†, `LandList`, `LandLowAt`, `LandTri`, `LandWalkBase64`, `LandWalkFail`, `LandWalkFail64`, `LandWalkFail65`, `LandWalkFail69`, `LandWalkSuff`, `Landmark`, `LandmarkChain`, `LandmarkW`, `Leaf`, `Leg3`, `Leg3Deep`, `Leg3Mid`, `Leg3Profile`, `Leg4`, `Leg4Crit`, `Leg4Land`, `Leg4Scan`, `Leg4Wide`, `Lift82`†, `Lift82Main`†, `Mid2Ascent66`, `Mid2Cross66`, `Mid2Fold66`, `Mid2FoldG66`, `Mid2Index67`, `Mid2Mixed67`, `Mid2MixedG67`, `Mid2Slack67`, `Mid2Wb66`, `Minimal2`†, `Mixed`, `MixedWitness`, `Open`†, `Pair`†, `PairCheck`, `Phase`†, `Profile`, `ProfileK`, `ProfileP`, `Raise`, `Reading70`, `Recon121`†, `Recon122`†, `Recon122General`†, `Recon122Model`†, `Recon122Special`†, `Recon87End`, `Reduction`†, `ReflectMiss`, `Refutations`†, `Relaxed`, `Shave`, `Shrink`†, `Span`†, `Span6`, `Span7`, `Span8`, `Span8Full`, `Span8Mid`, `Span8Mid4`, `Span9`, `Span9Mid`, `Span9Mid5`, `Span9Profile`, `SpanWitness`, `Step`†, `Symmetry`†, `Sync`†, `T7Assemble`†, `T7Profile`†, `T8Tight`†, `T9Blocks`†, `T9Ends`†, `T9Fold`†, `T9Main`†, `Target76`, `Theorem3Bing`†, `Theorem3Pair`†, `Theorem3PairInduction`†, `Theorem3PairModel`†, `Theorem4`†, `Theorem4Ge4`†, `Theorem4Only`†, `Theorem4Two`†, `Theorem4TwoModel`†, `Theorem7`†, `Theorem8Counter`, `ThreeWalks`, `Timing`, `Unserved`, `Valley72`, `ValleyFWitness`†, `ValleyFar`, `Witnesses`†, `ZigFree`†, `Zigzag`†
* `HPC/HO16`: `FoldExample`†, `HO16B`†, `HO16C`†, `NonVac196`, `NonVac197`, `P208`†, `StairExample`†
* `HPC/Hagopian`: `H75Counter`†, `H75Jones`†, `H75Sine`†, `H75Thm1C`†, `H76Above`†, `H76AboveAcc`†, `H76AdaptHalf`†, `H76AdaptMain`†, `H76BDefs`†, `H76Block3c`†, `H76Blocks`†, `H76Bottom`†, `H76Cap`†, `H76CapLow`†, `H76ChainInter`†, `H76ChainSep`†, `H76Comp`†, `H76Composant`†, `H76Cond4`†, `H76Cons`†, `H76Cover`†, `H76CrossClosed`†, `H76CrossEss`†, `H76CrossSep`†, `H76Crossing`†, `H76Cut`†, `H76DCollar`†, `H76Dichot`†, `H76EndElement`†, `H76EndLayer`†, `H76Eps1`†, `H76Eps3`†, `H76Final179`†, `H76Follows`†, `H76Generic`†, `H76GenericComp`†, `H76Glue`†, `H76InnerCollar`†, `H76JXs`†, `H76K0Dense`†, `H76Last`†, `H76Lemma7`†, `H76Lemma7Ray`†, `H76Lemma8`†, `H76Lemma8Caps`†, `H76Lemma8Sep`†, `H76Meagre`†, `H76Mid`†, `H76NoBelow`†, `H76NoBelowCore`†, `H76NoBelowMain`†, `H76NoHair`†, `H76Nondeg`†, `H76Order`†, `H76OrderConcrete`†, `H76Orient`†, `H76PieceB`†, `H76Pocket`†, `H76Prop1`†, `H76Prop3`†, `H76Prop3L3`†, `H76Prop4`†, `H76Quot`†, `H76RPiece`†, `H76Rect`†, `H76Reparam`†, `H76Sat182`†, `H76Sat185`†, `H76Schoen2`†, `H76SepCross`†, `H76Setup`†, `H76Sides`†, `H76Split185`†, `H76Step8`†, `H76Strand`†, `H76StrandUse`†, `H76Swallow`†, `H76T12`, `H76T12Exists`†, `H76T12Sides`†, `H76T9`†, `H76T9Full`†, `H76Thin`†, `H76Thm1Setup`†, `H76Tight`†, `H76Tip`†, `H76TipRel`†, `H76TranslateIn`†, `H76TranslateMain`†, `H76TwoComposants`†, `H76USC`†, `H76Unicoh`†, `H76Uniform`†, `H76Uniform2`†, `H76Uniform3`, `H76X2n`†, `Hagopian76AA`†, `Hagopian76AB`†, `Hagopian76F`†, `Hagopian76G`†, `Hagopian76H`†, `Hagopian76I`†, `Hagopian76J`†, `Hagopian76K`†, `Hagopian76L`†, `Hagopian76M`, `Hagopian76N`†, `Hagopian76O`†, `Hagopian76P`†, `Hagopian76Q`†, `Hagopian76R`†, `Hagopian76S`†, `Hagopian76T`†, `Hagopian76U`†, `Hagopian76V`†, `Hagopian76W`†, `Hagopian76X`, `Hagopian76Y`†, `Hagopian76Z`†
* `HPC/Jones`: `CutPoints`†, `Jones48`†, `Theorem13`†, `Theorem13Aux`†, `Theorem6`†
* `HPC/Moore`: `FA`†, `FA6`†, `FA7`†, `M19AB`†, `M19B`†, `M19Bstep`†, `M19CD`†, `M19CRefute`†, `M19EF`†, `M19EThm`†, `M19GCor`†, `M25A`†, `M25B`†, `M25BRefute`†, `M43`†, `M43Comp`†, `M43Dual`†, `M43Pocket`†, `Mullikin4`†, `Refute`†, `Sec7Th37`†
* `HPC/Plane`: `Atriodic51`†, `Atriodic51B`†, `Atriodic51BCounter`†, `Atriodic51BElt`†, `Atriodic51Counter`†, `Atriodic51CounterArc`†, `Atriodic51CounterBing`†, `Atriodic51Props`†, `Band`, `BandAux`, `BandChain`, `BandN`, `BandNAux`, `BandNPath`, `CSide`†, `CantorOrgan`†, `CantorOrganBing`†, `CantorOrganCont`†, `CantorOrganLayers`†, `CantorOrganOrder`†, `Counter`, `CubeCycle`, `CubeCycleAux`, `CubeLoop`, `DescrM`†, `Fugate66B`†, `Fugate66BLemma2`†, `Fugate66BLemma4`†, `Fugate66Cor1`†, `Fugate66Cor1Proof`†, `LatticeCycle`, `LatticeCycleAux`, `Layers51`†, `Monotone51Comb`†, `NonCut51`†, `NonCut51Counter`, `Organ98`†, `OrganZig98`†, `PA51Counter`†, `Recon91`†, `Sorgenfrey`†, `SorgenfreyMain`†, `T4`†, `Theorem9B`†, `Theorem9BGen`†, `Thm12B`†, `Thm5`†, `Tree6Thread`†, `Windows91`†
* `HPC/PseudoArc`: `Lehner`†, `LehnerCore`†, `PatRuns`†, `Recon86`†, `Recon86Chain`†, `Recon86Model`, `Recon87Model`, `T14Glue`†, `T5Assemble`†, `T5Chain`†, `T5Gen`†, `T5Main`†, `T5Read`†, `T5Runs`†, `Thm14`†

### Table 4. Partly used modules (fewer than half of the declarations used)

| module | used / declarations | fraction |
|---|---:|---:|
| `HPC.BJ59.BJ59B` | 4 / 11 | 36.4 % |
| `HPC.BJ59.Order` | 1 / 4 | 25.0 % |
| `HPC.BJ59.Thm56` | 2 / 6 | 33.3 % |
| `HPC.Fold.Faithful` | 3 / 42 | 7.1 % |
| `HPC.Fold.Minimal` | 2 / 13 | 15.4 % |
| `HPC.Fold.OffCenter` | 3 / 42 | 7.1 % |
| `HPC.Fold.Splice78` | 3 / 12 | 25.0 % |
| `HPC.HO16.HO16D` | 1 / 3 | 33.3 % |
| `HPC.Hagopian.H75Thm1B` | 1 / 3 | 33.3 % |
| `HPC.Hagopian.H76Descent` | 1 / 17 | 5.9 % |
| `HPC.Hagopian.H76E24` | 1 / 13 | 7.7 % |
| `HPC.Hagopian.H76Essential` | 1 / 9 | 11.1 % |
| `HPC.Hagopian.H76HalfRay` | 2 / 10 | 20.0 % |
| `HPC.Hagopian.H76IFinite` | 1 / 17 | 5.9 % |
| `HPC.Hagopian.H76PairSep` | 1 / 4 | 25.0 % |
| `HPC.Hagopian.H76T7` | 1 / 3 | 33.3 % |
| `HPC.Hagopian.H76Translate` | 3 / 7 | 42.9 % |
| `HPC.Hagopian.H84Rigid` | 1 / 3 | 33.3 % |
| `HPC.Hagopian.Hagopian75` | 9 / 20 | 45.0 % |
| `HPC.Hagopian.Hagopian76A` | 5 / 16 | 31.2 % |
| `HPC.Hagopian.Hagopian76AC` | 1 / 14 | 7.1 % |
| `HPC.Hagopian.Hagopian76B` | 1 / 9 | 11.1 % |
| `HPC.Hagopian.Hagopian76C` | 2 / 9 | 22.2 % |
| `HPC.Hagopian.Hagopian76D` | 1 / 4 | 25.0 % |
| `HPC.Hagopian.Hagopian76E` | 1 / 7 | 14.3 % |
| `HPC.Jones.Basic` | 7 / 22 | 31.8 % |
| `HPC.Jones.Jones49C` | 2 / 8 | 25.0 % |
| `HPC.Jones.Jones49CMoore` | 2 / 9 | 22.2 % |
| `HPC.Jones.Jones55Core` | 22 / 49 | 44.9 % |
| `HPC.Jones.Jones75L` | 1 / 3 | 33.3 % |
| `HPC.Jones.Moore22` | 2 / 8 | 25.0 % |
| `HPC.Jones.Moore22T4` | 1 / 4 | 25.0 % |
| `HPC.Moore.M19CD2` | 1 / 7 | 14.3 % |
| `HPC.Moore.M19CDMain` | 4 / 10 | 40.0 % |
| `HPC.Moore.M19G` | 1 / 7 | 14.3 % |
| `HPC.Moore.M25B5` | 2 / 5 | 40.0 % |
| `HPC.Moore.M25BPts` | 7 / 23 | 30.4 % |
| `HPC.Moore.Sec6Th29` | 2 / 6 | 33.3 % |
| `HPC.Moore.Sec7Chord` | 1 / 3 | 33.3 % |
| `HPC.Moore.Sec7Th38` | 1 / 5 | 20.0 % |
| `HPC.Plane.Atriodic51Defs` | 5 / 16 | 31.2 % |
| `HPC.Plane.EndPoints51` | 2 / 11 | 18.2 % |
| `HPC.Plane.EndPointsT15` | 2 / 9 | 22.2 % |
| `HPC.Plane.Fugate66` | 5 / 28 | 17.9 % |
| `HPC.Plane.Fugate66BHU` | 2 / 6 | 33.3 % |
| `HPC.Plane.Fugate66BMiller` | 2 / 15 | 13.3 % |
| `HPC.Plane.Fugate66BThm1` | 1 / 13 | 7.7 % |
| `HPC.Plane.Ingram68Core` | 2 / 9 | 22.2 % |
| `HPC.Plane.Ingram68Star` | 1 / 10 | 10.0 % |
| `HPC.Plane.Most51` | 5 / 27 | 18.5 % |
| `HPC.Plane.PA51Lift` | 10 / 24 | 41.7 % |
| `HPC.Plane.PseudoArc51` | 7 / 19 | 36.8 % |
| `HPC.Plane.Snake51` | 4 / 11 | 36.4 % |
| `HPC.Plane.SorgenfreyDefs` | 7 / 24 | 29.2 % |
| `HPC.Plane.SorgenfreyLemmas` | 1 / 13 | 7.7 % |
| `HPC.Plane.Surgery91` | 1 / 3 | 33.3 % |
| `HPC.Plane.Theorem11` | 7 / 20 | 35.0 % |
| `HPC.Plane.Theorem11B` | 9 / 28 | 32.1 % |
| `HPC.Plane.Theorem11Gen` | 3 / 16 | 18.8 % |
| `HPC.Plane.Tree6Trim` | 1 / 18 | 5.6 % |
| `HPC.Plane.TreeLikeNS` | 9 / 19 | 47.4 % |
| `HPC.PseudoArc.Statements79` | 5 / 13 | 38.5 % |
| `HPC.PseudoArc.T14Irred` | 1 / 14 | 7.1 % |
| `HPC.PseudoArc.Theorem13` | 1 / 4 | 25.0 % |
| `HPC.PseudoArc.Theorem14` | 2 / 12 | 16.7 % |
| `HPC.PseudoArc.Theorem5` | 3 / 12 | 25.0 % |

66 modules.

### Table 5. Headlines by source paper

| paper | headlines | used | numbered theorems named in used headlines | numbered theorems named only in unused headlines |
|---|---:|---:|---|---|
| Bing 1948 | 1219 | 85 | 1 2 4 5 6 10 11 12 | 3 7 8 9 13 14 15 |
| Bing 1951 | 410 | 146 | 1 6 7 | 2 3 4 5 8 9 10 11 12 13 14 15 16 |
| Bing 1960 | 4 | 1 |  |  |
| Bing–Jones 1959 | 161 | 109 | 3 4 5 6 7 8 10 | 2 9 |
| Cook 1967 | 4 | 3 | 4 |  |
| Domokos–Prajs 2022 | 11 | 6 |  | 6 10 |
| Effros 1965 | 32 | 22 | 1 |  |
| Fugate 1966/1969 | 89 | 17 | 10 44 | 1 11 13 |
| Hagopian 1975 | 64 | 34 | 1 2 3 4 76 135 138 139 |  |
| Hagopian 1976 | 645 | 86 | 1 8 | 2 |
| Hagopian 1984 | 99 | 88 | 1 |  |
| Hoehn–Oversteegen 2016 | 154 | 124 | 1 4 8 15 20 |  |
| Ingram 1968 | 12 | 3 |  | 2 |
| Jones | 5 | 5 |  |  |
| Jones 1941 | 2 | 2 | 4 |  |
| Jones 1948 | 43 | 7 | 0 1 3 8 | 2 4 5 6 7 9 10 11 12 13 14 15 16 17 18 19 |
| Jones 1949 | 43 | 40 | 1 2 |  |
| Jones 1951 | 4 | 2 |  | 1 |
| Jones 1955 | 35 | 14 | 1 2 |  |
| Jones 1975 | 38 | 35 |  |  |
| Krasinkiewicz–Minc 1977 | 1 | 1 |  |  |
| Lehner | 18 | 1 |  | 14 15 |
| Menger (Kurventheorie) | 6 | 6 |  |  |
| Moore | 67 | 60 | 3 11 19 20 41 | 1 28 |
| Moore 1916 | 134 | 90 | 1 2 3 4 6 10 11 12 13 15 16 17 18 19 20 21 24 25 26 27 28 31 32 33 34 35 36 41 42 | 5 7 8 9 14 22 23 29 30 37 38 39 40 43 |
| Moore 1919 | 111 | 82 | 33 |  |
| Moore 1920 | 2 | 1 | 4 |  |
| Moore 1922 | 20 | 3 |  | 1 2 3 4 |
| Moore 1925 | 35 | 25 | 2 3 4 6 9 10 11 12 13 14 19 21 22 36 | 5 7 8 |
| Moore 1962 | 17 | 13 | 73 76 84 | 28 |
| Mullikin 1922 | 14 | 7 | 5 | 2 4 7 10 11 |
| Oversteegen–Tymchatyn 1982 | 31 | 31 | 1 2 3 |  |
| Sorgenfrey (Nadler) | 50 | 21 |  | 3 |
| Whyburn 1939/1942 | 33 | 27 | 14 |  |
| other | 107 | 0 |  |  |

### Table 6. The spine: used headlines per directory, and the ten most depended upon

The number before each name is the number of used headlines whose closure contains it.

* **`HPC/BJ59`** — 117 used headlines:
  * 39 — `HPC.BJ59.exists_epsMap_of_chain`: **An `ε`-chain gives an `ε`-map.** If `K` is covered by an `ε`-chain `D`, the weighted mean of
  * 38 — `HPC.BJ59.isHereditarilyIndecomposable_of_homeomorph`: **Hereditary indecomposability is topological**: a set homeomorphic to a hereditarily
  * 38 — `HPC.BJ59.isSnakeLike_of_homeomorph`: **Snake-likeness is topological** (into a compact space): a set homeomorphic to a snake-like
  * 37 — `HPC.BJ59.isPseudoArc_of_homeomorph`: **Being a pseudo-arc is topological** (into a compact space).
  * 36 — `HPC.BJ59.isPreconnected_preimage_of_monotone'`: **Preimages under a monotone map** (as `HPC.Hagopian.isPreconnected_preimage_of_monotone`,
  * 34 — `HPC.BJ59.IsContArcPA`: **A continuous arc of pseudo-arcs** (Bing–Jones p. 173): a continuous open map of `X` onto
  * 22 — `HPC.BJ59.IsChainMap`: **A chain map** (Bing–Jones p. 173), on indices: images of adjacent links are adjacent.
  * 21 — `HPC.BJ59.IsBJChain`: **A chain in Bing–Jones's sense** (p. 172): nonadjacent links are at positive distance.
  * 20 — `HPC.BJ59.BJThm10`: **Bing–Jones, Theorem 10** (pp. 181–182), fibre-preserving form: between two continuous
  * 19 — `HPC.BJ59.chain_assembly`: **The chain of Theorem 3, assembled** (see the module docstring).
* **`HPC/Chains`** — 14 used headlines:
  * 165 — `HPC.Chain`: **D1.** A chain of length `n`: open links, with `link i` meeting `link j` iff `|i - j| ≤ 1`.
  * 117 — `HPC.Chain.union`: **D2.** The union of the links.
  * 82 — `HPC.Chain.Refines`: **D5.** `E` refines `D`: every link of `E` lies inside some link of `D`.
  * 69 — `HPC.Chain.IsCrookedIn'`: **D9.** Crookedness, 1948 form (Bing, *A homogeneous indecomposable plane continuum*, §1).
  * 54 — `HPC.Chain.IsFrom`: **D4.** A chain from `P` to `Q`: `P` in the first link only, `Q` in the last link only.
  * 51 — `HPC.Chain.sub`: **D3.** The subchain from index `i` to index `j` (inclusive), for `i ≤ j`.
  * 42 — `HPC.Chain.IsConsolidationOf`: **D6.** `F` is a consolidation of `D`: `D` refines `F` and every link of `F` is a union of
  * 40 — `HPC.Chain.exists_value_between`: **Interpolation along a chain.**  If every link of `F` lies in the link of `D` named by
  * 37 — `HPC.Chain.FollowsPattern`: **D7.** `D` follows the pattern `x` in `E`: `D.link i ⊆ E.link (x i)`.
  * 37 — `HPC.Chain.diam_le_length_mul`: **T7.** A chain of bounded links of diameter `< ε` covering a set `A` has at least
* **`HPC/Covers`** — 10 used headlines:
  * 29 — `HPC.closure_fat_subset_fat`: **The nesting lemma.** If `B` has diameter `≤ ε (i+1)`, and some point of `B` is within
  * 28 — `HPC.MatchingCovers.step1₂`: **Step 1.** If two elements of consecutive levels meet on side 1, the corresponding
  * 26 — `HPC.MatchingCovers.exists_limit_point`: **Step 4.** For an index sequence whose consecutive elements meet, the nested sequence of
  * 25 — `HPC.MatchingCovers.toFun`: **Steps 4 and 5.** Bing's map `T`, defined on points of `M₁` via a chosen tracking
  * 24 — `HPC.MatchingCovers.toFun_mem_y₂`: **Step 5.** The value of `T` at `p` lies in *every* fattened element containing `p`, not
  * 22 — `HPC.MatchingCovers.continuous_toMap`: **Step 6.** `T` is continuous.
  * 22 — `HPC.MatchingCovers.step2₂`: **Step 2.** If an element of level `i` and one of a later level `j` meet in a point of `M₁`,
  * 21 — `HPC.MatchingCovers.injective_toMap`: **Step 8.** `T` is injective.
  * 21 — `HPC.MatchingCovers.surjective_toMap`: **Step 7.** `T` is surjective.
  * 20 — `HPC.MatchingCovers.exists_homeomorph`: **Bing 1948, Theorem 11**, with the point-tracking clause Theorem 12 needs.
* **`HPC/Effros`** — 18 used headlines:
  * 131 — `HPC.Effros.homeoGroup`: **C.1.** The group of self-homeomorphisms; multiplication is composition.
  * 131 — `HPC.Effros.homeoTopology`: **C.1.** The topology of the homeomorphism group: induced by `homeoEmb` (Arens).
  * 130 — `HPC.Effros.vanMill_3_2`: **van Mill, Lemma 3.2.** If the action is transitive and `X` is a nonempty Baire space, then
  * 129 — `HPC.Effros.exists_eq_of_core`: **The nested construction of Proposition 2.2.** `P`, `Q` complete metric spaces, `α`, `β`
  * 129 — `HPC.Effros.exists_reduced_param`: **The reduction of Proposition 2.2.** Let `f : (ℕ → ℕ) → Y` be any map (continuity is not needed here). Rem…
  * 129 — `HPC.Effros.vanMill_3_1`: **van Mill, Lemma 3.1.** Suppose `V` is open and `z ∈ V ∩ U n • x`. Then
  * 128 — `HPC.Effros.vanMill_3_4`: **van Mill, Lemma 3.4, second sentence.** `x` lies in the interior of `closure (U n • x)`.
  * 128 — `HPC.Effros.inter_nonempty_of_nowhereMeagre`: **van Mill, Proposition 2.2, relative form.** Two analytic nowhere meager subsets `S`, `T`
  * 128 — `HPC.Effros.vanMill_3_3`: **van Mill, Corollary 3.3.** `U n • x` is nowhere meager. (The hypothesis `U 0 = univ` of the
  * 127 — `HPC.Effros.vanMill_3_5`: **van Mill, Proposition 3.5** (as printed, with the closure bar). `interior (closure (U (n+1) • x)) ⊆ U n •…
* **`HPC/Fold`** — 31 used headlines:
  * 49 — `HPC.Fold.Z77.CrkOn.reverse`: **Crookedness read backwards.**
  * 48 — `HPC.Fold.Z77.transfer`: **The transfer of one arm.** If every drop below `b - 1` is preceded by a visit to `t - 1`,
  * 48 — `HPC.Fold.Z77.up_core`: **The up core.** The left arm, from its time `τ` on, stays at `a - 1` or below until it
  * 47 — `HPC.Fold.Z77.Fit`: **The phase condition.** `Fit f m τ a ts`: from time `τ`, the arm `f` (read on `[0, m)`) runs
  * 47 — `HPC.Fold.Z77.up_step`: **One up phase, two arms.**
  * 47 — `HPC.Fold.Z77.down_core`: **The down core.** The left arm is at `b` or above before `τb`, at `a - 2` or below on
  * 46 — `HPC.Fold.Z77.down_step`: **One down phase, two arms**: the reflection of `up_step`.
  * 46 — `HPC.Fold.Z77.nofail_down`: **A down phase is never stuck.**
  * 46 — `HPC.Fold.Z77.nofail_up`: **An up phase is never stuck.**
  * 45 — `HPC.Fold.Z77.main_up`: **The greedy zigzag, from an up phase.** From a state at bottom `b` (previous top `a`) in
* **`HPC/HO16`** — 118 used headlines:
  * 101 — `HPC.HO16.IsPLGraph`: **PL graph** (H–O p. 183, "graph", in piecewise linear form): a finite union of
  * 71 — `HPC.HO16.Subdiv.exists_piece_cover`: **Covering**: every point of a segment of `T` lies on a piece inside it, and is an endpoint
  * 71 — `HPC.HO16.Subdiv.piece_cross`: **Cross lemma**: a piece in `t` sharing an inner point with `t'` lies in `t'`.
  * 71 — `HPC.HO16.Subdiv.piece_same`: **Same-line lemma**: two pieces in the same segment sharing a point inner to the first are
  * 70 — `HPC.HO16.Subdiv.exists_common_subdivision`: **Common subdivision** (commission 194, §3.1, in the form used for §3.0).
  * 63 — `HPC.HO16.IsPLGraph.exists_refinement`: **§3.0, refinement**: a decomposition of `G` in which each of finitely many PL subgraphs
  * 61 — `HPC.HO16.isPLGraph_biUnion`: **§3.1**: a finite union of nondegenerate segments is a PL graph (common subdivision).
  * 60 — `HPC.HO16.IsPLGraph.union`: **§3.2**
  * 60 — `HPC.HO16.IsFoldTriple`: **H–O Definition 5, (F1)–(F3)**, with "regular" read as "PL graph": the sets `G₁, G₂, G₃` of
  * 59 — `HPC.HO16.HasConsCompl`: **H–O Definition 9, first bullet** (p. 189): `A` has consistent complement relative to `B` if
* **`HPC/Hagopian`** — 227 used headlines:
  * 132 — `HPC.Hagopian.IsAdmissibleMap.isPreconnected_preimage`: **Preimages of preconnected sets are preconnected** under an admissible map of a compact set
  * 126 — `HPC.Hagopian.layer_subset_of_meets'`: **The interval lemma** (both orientations of the ends). A subcontinuum of an irreducible `E`
  * 119 — `HPC.Hagopian.composant_isMeagre'`: **Moore 136–137.**
  * 118 — `HPC.Hagopian.composant_dense'`: **Moore 135.**
  * 117 — `HPC.Hagopian.composant_eq_or_disjoint'`: **Moore 138.**
  * 105 — `HPC.Hagopian.uncountable_composants'`: **Moore 139.**
  * 102 — `HPC.Hagopian.disjoint_components_missing`: **Disjoint complementary domains.** Let `F₁`, `F₂` be disjoint subsets of `M` (`F₁` closed and
  * 96 — `HPC.Hagopian.exists_leg`: **A leg reaching the boundary.** If `T = Z ∪ P ∪ R` with `P`, `R` separated, the core `Z` inside
  * 96 — `HPC.Hagopian.interlace`: **The interlacing lemma** (Moore 1962, Theorem 76, p. 220, separation form). Let `J` be a closed
  * 96 — `HPC.Hagopian.eq_of_meets_ends`: **End sets with type A′ layers.** A subcontinuum meeting both end layers is everything.
* **`HPC/Jones`** — 146 used headlines:
  * 112 — `HPC.Jones.exists_continuum_bump_compact`: **Boundary bumping for a compact piece of a connected set.** If `F` is a compact proper subset
  * 107 — `HPC.Jones.tarc_of_isSimplePolyArc'`: **Item A.** A simple polygonal arc is a topological arc.
  * 90 — `HPC.Jones.LSCAt`: **Lower semicontinuity at an element** ("`G` is continuous at `g`" for an u.s.c. `G`): every
  * 75 — `HPC.Jones.IsUSCDecomp`: **Upper semicontinuous decomposition into closed sets** (Moore 1925, p. 416, restated with open
  * 63 — `HPC.Jones.AposAt`: **`X` is aposyndetic at `x` with respect to `y`** (Jones 1941, 1948 p. 404). There are a
  * 47 — `HPC.Jones.exists_finite_apos_cover`: **Heine–Borel, first form.** If `X` is aposyndetic at every point of the compact `K` with
  * 47 — `HPC.Jones.exists_open_subset_component`: **Finitely many components.** If an open `O ∋ x` is covered by finitely many components of a
  * 46 — `HPC.Jones.glue_circle`: **Gluing two arcs along their ends** gives a copy of `Circle`.
  * 44 — `HPC.Jones.jordan_curve_theorem`: **The Jordan curve theorem**, from `m25_theorem11` for the decomposition into points and the
  * 43 — `HPC.Jones.theorem0`: **Theorem 0.** `X` is semi-locally-connected at `p` iff it is aposyndetic at each point of
* **`HPC/Moore`** — 260 used headlines:
  * 242 — `HPC.Moore.Gen.TArc.union`: **Gluing.** Two arcs `PQ`, `QR` meeting only in `Q` form an arc `PR`.
  * 194 — `HPC.Moore.ac_exists_strictMono`: **The map to `[0, 1]`.** A compact connected separable space with a linear order whose open
  * 193 — `HPC.Moore.ac_homeomorph`: **An irreducible continuum is an arc** (in the subspace form): a compact, connected, separable
  * 192 — `HPC.Moore.isIrreducibleConnected_iff_arc`: **Arc characterization (topological form).** In a metrizable space, a compact connected set
  * 189 — `HPC.Moore.exists_exp_lift_of_homotopy`: **Homotopy lifting from the constant `1`.** If `Hg` is a homotopy of nonvanishing maps with
  * 186 — `HPC.Moore.exists_log_pt`: **Every continuous nonvanishing map of the plane to `ℂ` has a continuous logarithm.**
  * 185 — `HPC.Moore.exists_log_of_mem_component`: **Same component ⇒ logarithm.** If `y` lies in the component of `x` in `Kᶜ` (`K` closed),
  * 175 — `HPC.Moore.Space.Axiom1`: **Axiom 1.** There is a sequence of regions `K₁, K₂, …` such that (1) every point lies in `Kₙ`
  * 170 — `HPC.Moore.fa_theorem6`: **Theorem 6.** Two regions with a common point `P` contain a common region about `P`.
  * 167 — `HPC.Moore.isTopologicalBasis_region`: **The regions form a basis** (Axiom 1: Theorem 6 and condition (1)).
* **`HPC/Plane`** — 192 used headlines:
  * 187 — `HPC.Plane.exists_exp_lift`: **Lifting through `exp`** on a space contracted to a point by a homotopy `Hc`: every continuous
  * 181 — `HPC.Plane.CrossesEast`: **The half-open east-ray crossing rule** for the segment from `a` to `b` and the point `x`:
  * 181 — `HPC.Plane.sub_const_of_exp_eq`: **Two continuous logarithms differ by a constant** on a preconnected set: `f − g` is
  * 173 — `HPC.Plane.crossesEast_jump`: **The vertex rule** (the statement proved for item 2 of the commission). For a single segment
  * 165 — `HPC.Plane.isConnected_diff_singleton_of_isOpen`: **An open connected subset of the plane minus a point is connected.** Take a punctured ball
  * 162 — `HPC.Plane.IsProper`: **Proper position**: every segment nondegenerate, two distinct segments have distinct point
  * 162 — `HPC.Plane.isSimplePolyArc_iff`: **The list form and the vertex-function form of simple polygonal arcs agree.**
  * 159 — `HPC.Plane.parity_eventually_eq`: **The parity is locally constant on `Γᶜ`** (eventually form). No simplicity is needed.
  * 157 — `HPC.Plane.parity_far`: **Parity is `0` far to the east**: beyond the largest abscissa of a vertex no edge is crossed.
  * 156 — `HPC.Plane.ball_diff_rays`: **Two rays cut a square into (at most) two connected pieces.** For `w`, nonzero `a`, `b` not
* **`HPC/PseudoArc`** — 23 used headlines:
  * 204 — `HPC.T13.clopen_meets_closure_diff`: **Boundary bumping, clopen form.** A nonempty subset `W` of a proper subset `L` of a
  * 141 — `HPC.T13.false_of_interior`: **A proper subcontinuum of an indecomposable continuum has empty interior** relative to the
  * 85 — `HPC.exists_irreducible`: **Irreducible subcontinua exist.** A continuum containing `A` and `B` contains a subcontinuum
  * 45 — `HPC.T13.isPreconnected_limSup`: **Limits of finely chained sets are connected.**
  * 38 — `HPC.Chain.inter_link_nonempty_between`: **Separation by a link.** A preconnected set inside the union of a chain that meets the links
  * 33 — `HPC.Chain.exists_blockChain`: **Theorem 4 applied to a subchain from `R` to `S`.**
  * 32 — `HPC.Description.eventually_thick`: **Thick readings.** For every `w`, at every deep enough level `m`, each position `p` has a
  * 32 — `HPC.PatCore.realize`: **The combinatorial core of pattern following.** Let `x` be a pattern of length `N`
  * 31 — `HPC.Description.theorem6Pos_of_ne`: **Theorem 6 with `j > 0`**, for every description with `P ≠ Q` of a compact space.
  * 30 — `HPC.T13.exists_not_mem_proper_subcontinua`: **Some point of an indecomposable continuum lies in no proper subcontinuum through `p`**
* **`HPC/Span`** — 41 used headlines:
  * 24 — `HPC.Span.SurjSemiSpanPos`: **Positive surjective semi-span** of `A` (`σ₀*(A) > 0`): the first projection onto `A`.
  * 24 — `HPC.Span.isContinuum_sInter_chain`: **§4.1, helper**: the intersection of a nonempty chain of continua is a continuum, and
  * 23 — `HPC.Span.SurjSpanPos`: **Positive surjective span** of `A` (O–T p. 129, `σ*(A) > 0`), topological form: a continuum
  * 22 — `HPC.Span.plPath_piece`: **The piece formula**: on `[j/s, (j+1)/s]`, `plPath a` is affine.
  * 22 — `HPC.Span.HOSpanZero`: **Span zero in the sense of Hoehn–Oversteegen** (2016, p. 184): every subcontinuum
  * 22 — `HPC.Span.parity_eq_zero_of_not_mem_convex`: **§3.1**: the parity vanishes off a compact convex set containing the vertices.
  * 22 — `HPC.Span.brouwer_reduction`: **§4.1, Brouwer reduction.**
  * 21 — `HPC.Span.cook67_theorem4`: **Cook 1967, Theorem 4** (p. 243).
  * 20 — `HPC.Span.parity_eq_of_perturb`: **§3.2, vertex perturbation**: moving every vertex by at most `ρ` does not change the parity at
  * 19 — `HPC.Span.OTThm32`: **O–T Theorem 3.2, strip form** (commission §6.3), as a named claim: copies of `Y` hanging from

