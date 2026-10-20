# Overview of the proof development

This directory contains the 3007 modules of the proof of Theorems 1, 2 and 3 of Duminil-Copin, Sidoravicius and Tassion (arXiv:1505.04159v1), abbreviated DCST in module headers; "TeX line N" there refers to the file `pottsPhaseTransition.tex` of the arXiv v1 e-print source, and equations are cited, as `eq. (N)` or `eq:N`, by their TeX labels, which can differ from the numbers printed in the paper. The statements are in `Frozen/`, one theorem per file, and the 22 definitions they use are in `Frozen/Defs.lean`; the same text is in `Challenge.lean`. `Provider/` assembles each main theorem from the results below. The paper's numbering is used throughout (Propositions 1-4, Lemmas 1-8, Theorems 4, 9 and 10); some intermediate statements are formalized in corrected or partial form, as listed in the repository README.

## How the proof is organized

```text
Theorem 3 (P1-P5 equivalent, q >= 1)
  easy implications P1 => P2 => P3 => P4 and P5 => P1      Thm3/Easy
  P4 => P5: Proposition 3 (dichotomy) and Proposition 4     Thm3/RSW, Thm3/Push, Thm3/OuterCircuit, Thm3/Prop4
    Lemma 2 (strip RSW), Lemma 3 (push)                     Thm3/Push, PlanarMixed/StripRSWSelectors
    Lemma 4, Lemma 5 (exterior circuits)                  Thm3/RSW, Thm3/OuterCircuit, PlanarMixed/Lemma4*
    Lemma 6 (touching the wired arc), Lemma 7            Thm3/Touch, Thm3/Prop4, PlanarMixed/TiltedHalfHeight*
  assembly                                                  Assembly, Provider/Theorem3
Theorem 4 (sub-exponential one-arm decay at p_c, 1 <= q <= 4)
  parafermionic observable, Theorem 10 (summed form),
  Lemma 8 (polynomial lower bound)                          FKC/Medial, FKC/FiniteFK, Thm4
  slit-domain screens, side and connector factors          Thm4Plane, Thm4Records, Thm4Side, Thm4SideEuler, PlanarMixed/Thm4SideFactor
Theorem 2 (= P1 at q in [1, 4]) from Theorems 3 and 4      Thm4Plane, Provider/Theorem2
Theorem 1 from Theorem 2 (Edwards-Sokal coupling)          Thm1, Provider/Theorem1
Critical points and infinite-volume measures
  existence and uniqueness                                  Critical, Foundations, WellDefined, PD/FK
  p_c = sqrt(q)/(1 + sqrt q), Theorem 9 (RSW at p_c)        BD12, Coincidence, PlanarTopology
Shared infrastructure                                       PD, FKC, Infinite, Exploration, DualityExt, PlanarTopology, PlanarMixed
```

## Directories

Each directory has a `README.md` listing its modules with a one-line summary taken from the module docstring.

| Directory | Part | Modules | Lines | Contents |
|---|---|---:|---:|---|
| [`Frozen/`](Frozen/README.md) | statements | 8 | 504 | The seven main theorems, one per file, and the 22 definitions they use in `Defs.lean` (one module, in the order of `Challenge.lean`, so that both elaborate to the same terms); the same text is in `Challenge.lean`. |
| [`Provider/`](Provider/README.md) | assembly | 7 | 271 | Proofs of the seven main theorems from the results of the other directories. |
| [`Assembly/`](Assembly/README.md) | Theorem 3 | 6 | 714 | Assembly of Theorem 3 from Lemma 6 and the implications between P1-P5. |
| [`Thm3/`](Thm3/README.md) | Theorem 3 | 1107 | 85,721 | The proof of Theorem 3 (Section 3 of the paper): `Easy/` the easy implications, `RSW/` the renormalisation of Section 3.3 (Lemma 4, Proposition 3), `Push/` Lemmas 2 and 3, `OuterCircuit/` outermost circuits in Lemma 4, `Prop4/` Proposition 4 with Lemma 7, `Touch/` Lemma 6, `StripDual/` self-duality of strips. |
| [`Thm4/`](Thm4/README.md) | Theorem 4 | 95 | 13,110 | Lemma 8 and the proof of Theorem 4 from the parafermionic observable (Section 4 of the paper). |
| [`Thm4Plane/`](Thm4Plane/README.md) | Theorem 4 | 41 | 4,882 | Theorem 4 in the plane via slit-domain screens, and the derivation of Theorems 1 and 2 from Theorem 4 and Theorem 3. |
| [`Thm4Records/`](Thm4Records/README.md) | Theorem 4 | 32 | 3,321 | Exploration records for the screen events of the proof of Theorem 4 and the connector factor. |
| [`Thm4Side/`](Thm4Side/README.md) | Theorem 4 | 9 | 1,782 | Side factor of the screen estimate: conditioned laws and stochastic domination. |
| [`Thm4SideEuler/`](Thm4SideEuler/README.md) | Theorem 4 | 3 | 404 | Exact dual laws of the residual half-domains used for the side factor. |
| [`Thm1/`](Thm1/README.md) | Theorem 1 | 52 | 9,059 | The Edwards-Sokal coupling in finite and infinite volume, Potts infinite-volume limits, the magnetisation identity and the transfer of critical points; Theorem 1 from Theorem 2. |
| [`BD12/`](BD12/README.md) | critical point | 224 | 14,549 | The value p_c(q) = sqrt(q)/(1 + sqrt q) for q >= 1 (from [BD12a], by the sharp-threshold method of Duminil-Copin-Raoufi-Tassion) and crossing estimates at p_c (Theorem 9). |
| [`Coincidence/`](Coincidence/README.md) | critical point | 6 | 1,101 | Equality of free and wired measures for all but countably many p, via continuity of the pressure. |
| [`Critical/`](Critical/README.md) | critical point | 9 | 1,841 | Existence of the critical point: monotonicity in p, Peierls bounds, threshold construction. |
| [`WellDefined/`](WellDefined/README.md) | statements | 1 | 87 | Uniqueness of the random-cluster infinite-volume measures and critical points; the Potts counterparts are proved in `Thm1/`. |
| [`Foundations/`](Foundations/README.md) | infrastructure | 4 | 825 | Bridges between the definitions of `Frozen/` and the FK library of `PD/`; existence of limits along every exhaustion. |
| [`Infinite/`](Infinite/README.md) | infrastructure | 13 | 2,291 | FKG inequality, comparison, domain Markov property, translation and lattice symmetries for the infinite-volume measures. |
| [`Exploration/`](Exploration/README.md) | infrastructure | 17 | 2,248 | Explorations of random-cluster configurations, stopping sets and their domain Markov property. |
| [`DualityExt/`](DualityExt/README.md) | infrastructure | 59 | 10,147 | Planar duality for general finite domains and annuli. |
| [`PlanarTopology/`](PlanarTopology/README.md) | infrastructure | 220 | 17,853 | Discrete planar topology: Jordan-type separation, circuits and crossings, planar non-coexistence, crossing corridors. |
| [`PlanarMixed/`](PlanarMixed/README.md) | infrastructure | 259 | 24,838 | Mixed boundary conditions and the crossing estimate (3) on squares (`Square/`), the corrected connector events of Lemma 4 (`Lemma4Connectors/`, `Lemma4StoppingRecords/`, `Lemma4RecordCarrier/`), local selectors for Lemma 2 (`StripRSWSelectors/`), the half-height bound of Lemma 6 (`TiltedHalfHeight/`, `TiltedHalfHeightConsumers/`) and the side factor of Theorem 4 (`Thm4SideFactor/`). |
| [`PD/`](PD/README.md) | infrastructure | 190 | 25,597 | Finite and infinite-volume FK measures, FKG and comparison inequalities, finite energy and planar duality on rectangles, adapted from the PottsDiscontinuity formalization; 26 of the 44 modules of `RCInfinite/` (Burton–Keane uniqueness) come from the development version of PottsDiscontinuity, not from its public repository. |
| [`FKC/`](FKC/README.md) | infrastructure | 645 | 94,347 | Finite FK measures on graphs, discrete domains, medial graphs and the parafermionic observable with its contour identities (Theorem 10), adapted from the FKconvergence formalization; `SLEWrap/` (3 modules) is taken from the SLE development of openai/math. |
