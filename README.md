# PottsContinuity-lean

[![Build and axiom audit](https://github.com/zijie123123/PottsContinuity-lean/actions/workflows/build.yml/badge.svg)](https://github.com/zijie123123/PottsContinuity-lean/actions/workflows/build.yml)
[![Comparator](https://github.com/zijie123123/PottsContinuity-lean/actions/workflows/comparator.yml/badge.svg)](https://github.com/zijie123123/PottsContinuity-lean/actions/workflows/comparator.yml)

A complete Lean 4 / Mathlib formalization of the three main theorems of

> H. Duminil-Copin, V. Sidoravicius and V. Tassion,
> **Continuity of the phase transition for planar random-cluster and Potts models with 1 ≤ q ≤ 4**,
> [arXiv:1505.04159v1](https://arxiv.org/abs/1505.04159v1); published in
> Comm. Math. Phys. **349** (2017), no. 1, 47–107.

Theorem 1 (the q-state Potts model for q = 2, 3, 4), Theorem 2 (the random-cluster model for
1 ≤ q ≤ 4) and Theorem 3 (the equivalence of five properties of the critical random-cluster model
for every real q ≥ 1) are proved in Lean with no `sorry` and no axioms beyond Lean's three standard
ones (`propext`, `Classical.choice`, `Quot.sound`).

The critical points in the statements are the genuine phase-transition thresholds, not explicit
values: the theorems assert that they exist, and four further theorems show that they (and the
infinite-volume measures) are unique. Beyond this statement surface, the development proves
`p_c(q) = √q/(1+√q)` for every q ≥ 1 (`PottsContinuity.BD12.isRCCriticalPoint_sqrt`) and
`β_c(q) = log(1+√q)` for every integer q ≥ 2 (`PottsContinuity.Thm1.isPottsCriticalPoint_log_sqrt`).
These identifications are proved in Lean, with the standard axioms only, but are not part of
`Challenge.lean`, so Comparator does not check them.

The results the paper cites and the proof uses are proved here or taken from Mathlib, the vendored
libraries or Tau Ceti (below); nothing is assumed. These include (citation keys are those of the paper's bibliography: [BD12a], titled
there "Critical point and duality in planar lattice models", is identified by its content with
arXiv:1006.5073v2, [Dum12] is arXiv:1208.3787v2, [Dum13] is the monograph *Parafermionic
observables and their applications to planar statistical physics models*, Ensaios Matemáticos 25,
2013):
- the value of `p_c(q)` from [BD12a] and the crossing estimates at `p_c` (Theorem 9 of the paper,
  [BD12a, Corollary 9]; `PottsContinuity.BD12.wired_weakRSW_uniform_at_selfDual`), proved along the
  sharp-threshold route of Duminil-Copin–Raoufi–Tassion together with the crossing estimates of
  Köhler-Schindler–Tassion and planar non-coexistence (Theorem 1.5 of Duminil-Copin–Raoufi–Tassion,
  by its proof; `PottsContinuity.PlanarTopology.planar_noncoexistence`);
- the vanishing of contour integrals of the parafermionic observable (Theorem 10 of the paper,
  which cites it from [Dum13]) in the form used in Section 4, on finite boxes of the universal
  cover: for 1 ≤ q < 4, the summed identity
  `PottsContinuity.FKC.FiniteFK.parafermionicCoverPathPhaseExpectation_contour_edge_identity`
  together with `PottsContinuity.FKC.FiniteFK.parafermionicCoverContourFiniteEdgeDefect_eq_zero`
  (every edge term vanishes); for q = 4, with the winding observable,
  `PottsContinuity.Thm4.modifiedPathExpectation_four_bulk_zero` (the bulk term vanishes) and
  `PottsContinuity.Thm4.exterior_signed_winding_mean` (the boundary sum equals 2π);
- Theorem 4 (sub-exponential decay of the free one-arm probability at `p_c` for 1 ≤ q ≤ 4,
  originally [Dum12]), by the proof of Section 4 of the paper through the polynomial lower bound of
  Lemma 8 (`PottsContinuity.Thm4Plane.theorem_four_at_self_dual_of_sideFactor`, whose hypothesis is
  proved as `PottsContinuity.PlanarMixed.Thm4SideFactor.slitScreen_sideFactor`);
- the Edwards–Sokal coupling, FKG and comparison inequalities and the domain Markov property;
- the existence of the infinite-volume measures;
- planar duality and planar topology.

The Jordan–Schoenflies theorem and Brouwer's fixed-point theorem come from the vendored libraries
`vendor/schoenflies-lean` and `vendor/fixed-point-theorems`; circle degree and Jordan-curve facts
come from the pinned dependency [Tau Ceti](https://github.com/TauCetiProject/TauCeti).

Formalized by Zijie Zhuang ([GitHub: zijie123123](https://github.com/zijie123123)), with AI
agents; see [Provenance](#provenance-and-use-of-ai).

## The results

Below, `φ^0`/`φ^1` are the free/wired infinite-volume random-cluster measures on ℤ², `μ^{(i)}` is
the infinite-volume Potts Gibbs measure with monochromatic boundary condition `i`, and `Λ_n = [−n, n]²`.

**Theorem 1 (paper, p. 5).** Let q ∈ {2, 3, 4}. Then for every colour i,
`μ^{(i)}_{ℤ², β_c(q)}[σ_0 = i] = 1/q`. That is, the phase transition of the q-state Potts model
is continuous.

**Theorem 2 (paper, p. 6).** Let q ∈ [1, 4]. Then `φ^1_{ℤ², p_c(q), q}[0 ⟷ ∞] = 0`.

**Theorem 3 (paper, p. 7).** Let q ≥ 1. The following assertions are equivalent (the theorem does
not assert that they hold):
- **P1** `φ^1_{p_c,q}[0 ⟷ ∞] = 0`;
- **P2** `φ^0_{p_c,q} = φ^1_{p_c,q}`;
- **P3** `Σ_{x ∈ ℤ²} φ^0_{p_c,q}[0 ⟷ x] = ∞`;
- **P4** `lim_n (1/n) log φ^0_{p_c,q}[0 ⟷ ∂Λ_n] = 0`;
- **P5** for every α > 0 there is c > 0 with
  `φ^0_{[−n,(α+1)n]×[−n,2n], p_c, q}[C_h([0, αn] × [0, n])] ≥ c` for all n ≥ 1.

### The Lean statements

The trusted statement surface is [`Challenge.lean`](Challenge.lean) (Mathlib only). It contains the
seven theorems below and the 22 definitions they use, each with a docstring. The same declarations
are proved in [`PottsContinuity/`](PottsContinuity/) and exposed by [`Solution.lean`](Solution.lean).
Comparator checks that names, types and definitions agree.

```lean
/-- **Theorem 1** (p. 5). -/
theorem theorem_1 (q : ℕ) (hq : q ∈ Set.Icc 2 4) :
    ∃ βc : ℝ, IsPottsCriticalPoint q βc ∧
      ∀ i : Fin q, ∃ μ : Measure (ℤ × ℤ → Fin q),
        IsPottsInfiniteVolumeLimit q βc i μ ∧ μ.real {σ | σ (0, 0) = i} = 1 / (q : ℝ)

/-- **Theorem 2** (p. 6). -/
theorem theorem_2 (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 4) :
    ∃ (pc : Set.Icc (0 : ℝ) 1) (φ₁ : Measure (squareLattice.edgeSet → Bool)),
      IsRCCriticalPoint ⟨q, hq.1⟩ pc ∧
      IsRCInfiniteVolumeLimit pc ⟨q, lt_of_lt_of_le one_pos hq.1⟩ 1 φ₁ ∧
      φ₁ {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} = 0

/-- **Theorem 3** (p. 7). -/
theorem theorem_3 (q : ℝ) (hq : 1 ≤ q) :
    ∃ (pc : Set.Icc (0 : ℝ) 1) (φ : Fin 2 → Measure (squareLattice.edgeSet → Bool)),
      IsRCCriticalPoint ⟨q, hq⟩ pc ∧
      (∀ i, IsRCInfiniteVolumeLimit pc ⟨q, lt_of_lt_of_le one_pos hq⟩ i (φ i)) ∧
      List.TFAE
        [ φ 1 {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} = 0,          -- P1
          φ 0 = φ 1,                                                                          -- P2
          ∑' x : ℤ × ℤ, φ 0 {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) x} = ∞,           -- P3
          Tendsto                                                                             -- P4
            (fun n : ℕ => 1 / (n : ℝ) * Real.log ((φ 0).real
              {ω | ∃ y ∈ vertexBoundary (box n), (rcInfiniteOpenGraph ω).Reachable (0, 0) y}))
            atTop (𝓝 0),
          ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →                                 -- P5
            c ≤ rcEventProb
              (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * n⌋ (-(n : ℤ)) (2 * n))
              pc ⟨q, lt_of_lt_of_le one_pos hq⟩ 0
              (horizontalCrossing
                (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * n⌋ (-(n : ℤ)) (2 * n))
                0 ⌊α * n⌋ 0 n)]

/-- The infinite-volume limits and the critical points are unique when they exist. -/
theorem isRCInfiniteVolumeLimit_unique (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (i : Fin 2) (μ ν : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q i μ) (hν : IsRCInfiniteVolumeLimit p q i ν) : μ = ν
theorem isRCCriticalPoint_unique (q : Set.Ici (1 : ℝ)) (a b : ℝ)
    (ha : IsRCCriticalPoint q a) (hb : IsRCCriticalPoint q b) : a = b
theorem isPottsInfiniteVolumeLimit_unique (q : ℕ) (β : ℝ) (i : Fin q)
    (μ ν : Measure (ℤ × ℤ → Fin q))
    (hμ : IsPottsInfiniteVolumeLimit q β i μ) (hν : IsPottsInfiniteVolumeLimit q β i ν) : μ = ν
theorem isPottsCriticalPoint_unique (q : ℕ) (hq : 2 ≤ q) (βc βc' : ℝ)
    (h : IsPottsCriticalPoint q βc) (h' : IsPottsCriticalPoint q βc') : βc = βc'
```

All seven live in the namespace `PottsContinuity`; `Challenge.lean` carries the same statements with
their full docstrings.

### How the paper's objects are represented

These choices were fixed before any proof was written, reviewed against the paper by two
independent reviewer agents, and approved by the author together with the exact Lean text. Most of
them are also stated in the docstrings of `Challenge.lean`.

- **Finite volumes.** A finite volume is the subgraph of ℤ² induced by a finite vertex set `V`. Its
  vertex boundary `∂G` is taken literally: the vertices of `V` with fewer than four neighbours in
  `V`. Random-cluster weights are `p^{o(ω)} (1−p)^{c(ω)} q^{k_i(ω)}`, with `k_1` counting all
  clusters that meet `∂G` as one. The Potts Hamiltonian sums over the edges meeting `V`, with
  monochromatic boundary colour `i` outside `V`. The weight is `exp(β · #agreeing edges)`.
- **Infinite-volume measures** (`IsRCInfiniteVolumeLimit`, `IsPottsInfiniteVolumeLimit`).
  - A measure `μ` qualifies if it is a probability measure and is the limit of the finite-volume
    measures along *every* increasing sequence of finite vertex sets exhausting ℤ². This is the
    paper's "G ↗ ℤ²", which implies the box limit.
  - Convergence is tested on every finite-dimensional cylinder event, which is weak convergence on
    these compact product spaces.
  - The existence of these limits, which the paper takes from the literature, is proved.
- **Critical points** (`IsRCCriticalPoint`, `IsPottsCriticalPoint`).
  - They are defined by the phase transition itself (p. 6 and p. 4). For p_c ∈ (0, 1): for every
    p ∈ [0, 1] the wired limit exists, the origin lies in an infinite cluster with probability 0 for
    p < p_c, and with positive probability for p > p_c.
  - Likewise for β_c > 0 and every β ≥ 0: the magnetization `μ^{(i)}_β[σ_0 = i]` equals `1/q` for
    β < β_c and exceeds it for β > β_c.
  - That these thresholds equal `√q/(1+√q)` and `log(1+√q)` is proved inside the development
    (`PottsContinuity.BD12.isRCCriticalPoint_sqrt`, `PottsContinuity.Thm1.isPottsCriticalPoint_log_sqrt`)
    but is not part of `Challenge.lean`.
- **Existence packaging.** Each theorem asserts the existence of a critical point and of the
  infinite-volume measures with the stated properties. The four uniqueness theorems show that these
  objects are uniquely determined, so the existential form says exactly what the paper says.
  - Theorem 1 uses one βc for all colours.
  - Theorem 3 uses the free and the wired measure at the same critical point.
- **Parameters and encodings.**
  - Random-cluster parameters are subtypes: `p ∈ [0, 1]`; `q > 0` in finite volume, and `q ≥ 1`
    for the critical point and the theorems.
  - Boundary conditions are `Fin 2` (0 free, 1 wired).
  - Potts colours `{1, …, q}` are `Fin q` and q is a natural number. The finite-volume Potts
    measures and their limits are defined for every real β; the definition of β_c quantifies over
    β ≥ 0.
- **P3** is a sum in `ℝ≥0∞` over ℤ².
- **P4** uses `Real.log` of the real probability (positive here, so `Real.log 0 = 0` never matters).
- **P5 rounding.**
  - `[0, αn] × [0, n]` is the set of lattice points `{0, …, ⌊αn⌋} × {0, …, n}`.
  - Its left and right sides are the columns `x = 0` and `x = ⌊αn⌋`.
  - The outer free rectangle is `{−n, …, ⌊(α+1)n⌋} × {−n, …, 2n}`, so the margin is exactly n on
    every side.
  - An open path in a rectangle is a walk of open edges whose vertices stay in it; paths need not
    be self-avoiding (p. 15).
- **Structure.** Theorems 2 and 3 are not split. Theorem 3 is a single `List.TFAE [P1, …, P5]`.

### Corrected intermediate statements and repairs of proof steps

Theorems 1–3 are proved as stated (with the representation above); the repairs below do not change
them. Some intermediate statements of the paper are formalized in corrected or partial form:

- **Theorem 10** (cited from [Dum13]) only in the summed form used in Section 4, on finite boxes of
  the universal cover (for 1 ≤ q < 4 with the parafermionic observable, for q = 4 with the winding
  observable; see the list above), not for general Dobrushin domains.
- **Proposition 2** only in the directions the proof uses: P5 implies P5a, and P5b with R = 8
  implies P5.
- **P5a** for n ≥ 2: for n = 1 the annulus in P5a is empty and the printed bound fails
  (`PottsContinuity.Thm3.Easy.p5_implies_p5a`).
- **Proposition 1** (the domain Markov property) for 0 < p < 1 rather than p ∈ [0, 1].
- **Proposition 3**, second alternative, as `exp(−c n^β)` with some c > 0, stated as a
  disjunction of the two alternatives (their exclusivity, which the paper also states, is not
  formalized). The printed `exp(−n^α)` for all n ≥ 1 can fail at small n.
  It is proved with the inputs of its proof (the recurrence of Lemma 4 and a reflected-FKG
  construction) as hypotheses, which the proof of Theorem 3 supplies
  (`PottsContinuity.RSW.selfDual_dualityP_corrected_of_induction1_reflectedFKG`).
- **Proposition 4** with the hypothesis `exp(−c₀ n^α)` for some c₀ > 0, proved with the estimate of
  Lemma 6 as a hypothesis, which the proof of Theorem 3 supplies
  (`PottsContinuity.Thm3.Prop4.dualityQ_corrected_of_touch`).
- **Lemma 6** with the uniform constant `1/(20 m² n²)` instead of `1/(5 m² n²)`; all its uses need
  only some fixed polynomial bound (`PottsContinuity.Provider.touch_lower_bound`). The printed
  constant is not formalized in this release, and whether it holds in general is not settled here.
- **Lemma 7** with the hypothesis `exp(−c₀ n^α)` for some c₀ > 0 (as for Proposition 4), proved with
  the estimate of Lemma 6 as a hypothesis, which the proof of Theorem 3 supplies
  (`PottsContinuity.Thm3.Prop4.evenSquarePairKernel_of_touch`).
- **The estimate `φ⁰[u ⟷_D v] ≥ (1 − 4n^{1+ε} e^{−n^{αε}}) φ⁰[𝓔]` in the proof of Lemma 7** (p. 36,
  unnumbered in the printed paper) is not formalized in this form. The proof uses instead
  `φ¹_{Λₙ}[tube crossing] · φ⁰_{Λₙ}[𝓔] ≤ φ⁰_{Λₙ}[u ⟷_D v]` for a tube D around the segment from u to
  v (`PottsContinuity.Thm3.Prop4.between_trace_core_probability_mul_le_confined`), together with a
  lower bound 1/2 on the wired tube-crossing probability for all large n
  (`PottsContinuity.Thm3.Prop4.selfDual_wired_box_strict_core_uniform_ge_half`), which is all
  Lemma 7 needs.
- **Equation (3)** (cited by the paper from [BD12a]) in the form of [BD12a, Lemma 7] and of its three
  uses in the paper (proofs of Lemmas 2 and 4 and of Theorem 4): for a square with two opposite
  sides wired separately and the other two free, the two wired sides are joined by an open path
  with probability at least 1/(1+q²)
  (`PottsContinuity.PlanarMixed.Square.square_wiredBottomTop_lower_bound`,
  `PottsContinuity.PlanarMixed.Square.square_wiredLeftRight_lower_bound`). The printed (3) writes
  `C_h(Λ_n)`, a crossing between the two free sides of a square wired on top and bottom; that form
  is not formalized.

Proof steps that are repaired include:

- **Lemma 4 (proof).** The paper derives dual circuits `F_n` from the connection events
  `C_n`, `D_n`, `E_n` of eq. (15). For the formal definitions this deduction fails: during the
  development a configuration with n = 3 was found for which the events hold but no such dual
  circuit exists (the configuration is not included in this repository). The proof therefore replaces the three connection events by decreasing
  primal-blocking events on the residual domain. These keep the bound `(1+q²)^{−3}` and force
  the required circuits (`PottsContinuity/PlanarMixed/Lemma4Connectors/`,
  `PottsContinuity/PlanarMixed/Lemma4RecordCarrier/`).
- **Lemma 6.** The candidate set in the proof has at most `(n+1)(2nm²+1)` points, with equality
  for θ = 0, rather than the printed `n(2nm²+1)`; the proof uses this bound. The
  half-height bound used in the proof is proved for the infinite tilted strip, with an exactly
  self-dual carrier and an almost-sure cover by fully open columns
  (`PottsContinuity/PlanarMixed/TiltedHalfHeight/`).
- **Lemma 7 (proof).** The deterministic covering step behind the estimate above is carried out
  with integer radii; with the real radius `n^ε` the printed covering statement fails for some
  configurations (found during the development; the configuration is not included in this
  repository).
- **Proposition 3 (proof).** The proof chains fifteen translated events (j ∈ {−7, …, 7}) but uses the
  exponent 1/14; the formal proof uses an arbitrary positive gluing power
  (`PottsContinuity/Thm3/RSW/Prop3Conditional.lean`).
- **Edwards–Sokal identity (p. 7).** The paper writes `μ^{(i)}_{G,β}[σ_0 = i] = 1/q + φ^1[0 ⟷ ∂G]`;
  the proof uses the correct identity `1/q + (1 − 1/q) φ^1[0 ⟷ ∞]` in infinite volume
  (`PottsContinuity.Thm1.pottsInfiniteLimit_magnetisation_identity_all`).
- **Proposition 4 (final induction).** The rate `max_{n₀^ε ≤ n ≤ n₀} −(1/n) log Q_n` has to be a
  minimum for the base of the induction; the proof takes the minimum
  (`PottsContinuity/Thm3/Prop4/Recursion.lean`).
- **Cited proof of sharpness** (Duminil-Copin–Raoufi–Tassion, arXiv:1705.03104v2). The derivative
  (Russo) formula in the proof of its Theorem 1.2 has the coefficient `J/(e^{βJ} − 1)`, omitting a
  factor `e^{βJ}`; the formal proof uses the correct coefficient `J e^{βJ}/(e^{βJ} − 1)`, proved
  for every finite graph (`PottsContinuity.BD12.drt_russo_corrected`), and the printed lower bound
  remains valid for nonnegative covariances. An endpoint update in the exploration is misprinted
  and corrected (`PottsContinuity/BD12/SeedClusterRevealTree.lean`).
- **Unstated bridges.** Several steps the paper leaves implicit are proved:
  - limit passages from finite to infinite volume for FKG, comparison and the domain Markov property;
  - rounding, margins and small scales in the RSW arguments of Section 3;
  - the planar-topology facts used without proof (circuits, crossings, duality on annuli);
  - a reversed inequality in the final computation of Lemma 1.

## Repository layout

| Path | Contents |
|---|---|
| `Challenge.lean` | statement surface: the 7 theorems and 22 definitions, proofs `sorry` |
| `Solution.lean` | imports the proof development; does not import `Challenge` |
| `comparator.json` | Comparator configuration (the seven theorem names; no definition holes) |
| `Axioms.lean` | prints the axioms of the seven theorems |
| `PottsContinuity.lean` | entry point; imports exactly the seven theorems |
| `PottsContinuity/` | the proof development; [`PottsContinuity/OVERVIEW.md`](PottsContinuity/OVERVIEW.md) describes every directory, and each directory's `README.md` lists its modules |
| `PottsContinuity/Frozen/` | the seven theorems, one per file, and the 22 definitions in `Defs.lean` (one module, in the order of `Challenge.lean`, so that both elaborate to the same terms) |
| `vendor/schoenflies-lean/` | 128 modules of schoenflies-lean (Jordan–Schoenflies theorem), Apache-2.0, see its `PROVENANCE.md` |
| `vendor/fixed-point-theorems/` | 5 modules of fixed-point-theorems (Brouwer's theorem), MIT, see its `PROVENANCE.md` |
| `paper/` | how to obtain the paper (not redistributed) |
| `formalization.yaml` | Palomar metadata |

Module headers cite the paper as DCST and refer to its TeX source (`pottsPhaseTransition.tex` of the
arXiv v1 e-print) by line number. Equations are cited there, as `eq. (N)` or `eq:N`, by their TeX
labels, which can differ from the printed numbers, since the printed paper numbers only the equations it refers to
(for example, the TeX label `eq:31` is an unnumbered display on p. 36); this README uses the
printed numbers.

## Building and checking

Requirements: [elan](https://github.com/leanprover/elan). The toolchain is Lean `v4.35.0-rc3`.
Mathlib is pinned to master commit `b63f6e8a68d220e3b3bc4f3792bb53650d375f24` (toolchain
`v4.35.0-rc3`, 38 commits after the `v4.35.0-rc3` tag), the revision that the pinned Tau Ceti commit
itself pins, so that `lake-manifest.json` keeps every dependency of Tau Ceti at Tau Ceti's own pin.

```bash
lake exe cache get        # Mathlib build cache
lake build                # PottsContinuity, Challenge and Solution
lake env lean Axioms.lean # each theorem: [propext, Classical.choice, Quot.sound]
```

Further checks:

```bash
python3 scripts/check-lean-sources.py        # every .lean file is a module and has ≤ 10,000 lines
ruby scripts/validate-formalization.rb       # formalization.yaml has no template values
./scripts/verify-comparator.sh               # Comparator, with the toolchain's NanoDa and con-ron
                                             # kernels (Linux; needs bubblewrap)
```

`Challenge.lean` is expected to report seven `declaration uses 'sorry'` warnings; nothing else in
the repository uses `sorry`, and the build reports no other warnings.

## Provenance and use of AI

The formalization was produced on 2026-10-19/20 by an agent workflow directed by the author:
- Claude Code (Claude Opus 5.5) as orchestrator;
- OpenAI Codex agents (gpt-6-luna, gpt-6.1-sol) as proof workers;
- Claude Sonnet agents as independent reviewers, and Claude Opus agents for extracting the source
  dependency graph.

The statements of the main theorems and their 22 definitions were transcribed from the paper,
reviewed independently against the paper, approved by the author, and then frozen. Eight of the
definitions (`box`, `squareLattice`, `rcOpenGraph`, `rcFreeClusterCount`, `rcWiredClusterCount`,
`rcWeight`, `rcProb`, `rcInfiniteOpenGraph`) have the same Lean code as the definitions of the same
names in the `Challenge.lean` of PottsDiscontinuity-lean (their docstrings differ, and
`vertexBoundary`, which `rcWiredClusterCount` uses, is written differently there but equivalently), and `IsRCInfiniteVolumeLimit` uses its
cylinder-event form with every exhaustion in place of boxes; only proofs were
developed afterwards. Each main theorem received an independent audit after its proof was
assembled. The status is **agent-reviewed**: the Lean proofs are checked by Lean (and, via
Comparator, by independent kernels), but no human mathematician has refereed the formal development.

Parts of the code are adapted from earlier formalizations; each adapted module says so in its
header, and `formalization.yaml` records them under `related_formalizations`:
- 739 modules (mainly `PottsContinuity/FKC/`: finite FK measures, medial graphs, the
  parafermionic observable and its contour identities, discrete domains) are adapted from
  **FKconvergence**, an earlier formalization by the same author that is not publicly accessible.
- 191 modules (`PottsContinuity/PD/`: finite and infinite FK measures, comparison and FKG
  inequalities, planar duality on rectangles) are adapted from the author's
  [PottsDiscontinuity-lean](https://github.com/zijie123123/PottsDiscontinuity-lean) (at commit
  `435fb57856860eda7a65c8fec9e5fb29eff2b46b`); 190 of them are in `PottsContinuity/PD/` and one in
  `PottsContinuity/Thm4/`. 165 of them come from files of that public repository; the other 26
  (26 of the 44 modules of `PottsContinuity/PD/RCInfinite/`, the Burton–Keane uniqueness of the
  infinite cluster, about 4,300 lines) come from the development version of that formalization and are not in its public
  repository. 101 of the 191 had been adapted there, in whole or in part, from FKconvergence.
- 3 modules (`PottsContinuity/FKC/SLEWrap/`) are taken from the SLE development in
  [openai/math](https://github.com/openai/math) (Apache-2.0): the declarations used here are copied
  unchanged (namespace `OAI` kept); the files were ported to the module system and three
  declarations not used here were omitted. The Lean v4.34.1 compatibility edits of the two vendored
  libraries are those of `lean/patches/schoenflies-lean-lean4341.patch` and
  `lean/patches/fixed-point-theorems-lean4341.patch` of openai/math at commit `fd4aeeb2ee4f`
  (Apache-2.0), including their rewritten docstrings and the rename of `Graph.IsBridge` to
  `Graph.IsSchoenfliesBridge`.

The development was carried out on Lean v4.34.1 and ported for this release to Lean
v4.35.0-rc3 (Mathlib first at the `v4.35.0-rc3` tag, then at Tau Ceti's pin `b63f6e8`, a move that
needed no source change) and the Lean module system. Before the port, a cleanup removed
modules unreachable from the main theorems and unused declarations in many of the others (some
modules still contain declarations that the main theorems do not use). The port changed no statement of the main theorems or of
their 22 definitions: their text is identical up to the namespace prefix
`Research.PottsContinuity` → `PottsContinuity`. It did the following:
- made helper declarations public where the module system requires it;
- renamed internal modules and helpers whose names carried development labels;
- adapted a number of proofs to the new Lean and Mathlib versions and to linter warnings;
- placed the 22 definitions in one module, `PottsContinuity/Frozen/Defs.lean`, in the order of
  `Challenge.lean`, so that both elaborate to identical terms (including the auxiliary proofs Lean
  shares between definitions of one module), as Comparator requires; a few references to
  same-named helper definitions were qualified accordingly;
- split one case analysis inherited from FKconvergence into nine lemmas, so that no file raises
  `maxHeartbeats`.

## Licence and citation

The code in this repository is released under the Apache License 2.0 ([`LICENSE`](LICENSE)), except
for the vendored libraries, which keep their own licences (`vendor/schoenflies-lean/LICENSE`,
Apache-2.0; `vendor/fixed-point-theorems/LICENSE`, MIT). The three modules of
`PottsContinuity/FKC/SLEWrap/` and the compatibility patches applied to both vendored libraries are
taken from [openai/math](https://github.com/openai/math), which is licensed under the Apache License
2.0. The paper is not redistributed; see
[`paper/README.md`](paper/README.md).

If you use this formalization, please cite the paper above and this repository. The formalization
is prepared for submission to the [Palomar registry](https://palomar-registry.org/).
