-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/ClusterThresholds.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import PottsContinuity.PD.RCInfinite.ErgodicLimits
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

open MeasureTheory Set

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

/-- At least `n` distinct infinite actual open components, witnessed by their
vertices. This includes the vacuous threshold `n = 0`. -/
def atLeastInfiniteClusters (n : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ xs : Fin n → LatticeVertex,
    (∀ j, ω ∈ infiniteAt (xs j)) ∧
      ∀ j k, j ≠ k → ¬(rcInfiniteOpenGraph ω).Reachable (xs j) (xs k)}

theorem measurableSet_atLeastInfiniteClusters (n : ℕ) :
    MeasurableSet (atLeastInfiniteClusters n) := by
  have hsep (xs : Fin n → LatticeVertex) (j k : Fin n) :
      MeasurableSet {ω : LatticeConfiguration | j = k ∨
        ¬(rcInfiniteOpenGraph ω).Reachable (xs j) (xs k)} := by
    by_cases hjk : j = k
    · simp [hjk]
    · have heq : {ω : LatticeConfiguration | j = k ∨
          ¬(rcInfiniteOpenGraph ω).Reachable (xs j) (xs k)} =
          {ω : LatticeConfiguration | (rcInfiniteOpenGraph ω).Reachable (xs j) (xs k)}ᶜ := by
        ext ω
        simp only [mem_ofPred_eq, mem_compl_iff, hjk, false_or]
      rw [heq]
      exact (measurableSet_open_reachable (xs j) (xs k)).compl
  have h := MeasurableSet.iUnion fun xs : Fin n → LatticeVertex =>
    (MeasurableSet.iInter fun j => measurableSet_infiniteAt (xs j)).inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => hsep xs j k)
  convert h using 1
  ext ω
  simp only [atLeastInfiniteClusters, mem_ofPred_eq, mem_iUnion, mem_iInter, mem_inter_iff,
    imp_iff_not_or, not_not]

theorem atLeastInfiniteClusters_zero (ω : LatticeConfiguration) : ω ∈ atLeastInfiniteClusters 0 :=
  ⟨Fin.elim0, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩

theorem atLeastInfiniteClusters_antitone : Antitone atLeastInfiniteClusters := by
  intro m n hmn ω hω
  obtain ⟨xs, hinf, hsep⟩ := hω
  let f : Fin m ↪ Fin n :=
    { toFun := fun j => ⟨j.val, lt_of_lt_of_le j.isLt hmn⟩
      inj' := fun j k h => Fin.ext (congrArg (fun z : Fin n => z.val) h) }
  exact ⟨fun j => xs (f j), fun j => hinf (f j),
    fun j k hjk => hsep (f j) (f k) (fun h => hjk (f.injective h))⟩

theorem atLeastInfiniteClusters_translate (a : LatticeVertex) {ω : LatticeConfiguration} {n : ℕ}
    (hω : ω ∈ atLeastInfiniteClusters n) : edgeTranslate a ω ∈ atLeastInfiniteClusters n := by
  obtain ⟨xs, hinf, hsep⟩ := hω
  refine ⟨fun j => latticeTranslate a (xs j), ?_, ?_⟩
  · intro j
    exact (infiniteAt_translation a ω (xs j)).mpr (hinf j)
  · intro j k hjk hreach
    exact hsep j k hjk ((openGraphTranslationIso a ω).reachable_iff.mp hreach)

theorem atLeastInfiniteClusters_invariant (n : ℕ) (a : LatticeVertex) :
    (edgeTranslate a) ⁻¹' atLeastInfiniteClusters n = atLeastInfiniteClusters n := by
  ext ω
  constructor
  · intro h
    have hb := atLeastInfiniteClusters_translate (-a) h
    rwa [← edgeTranslate_add, neg_add_cancel, edgeTranslate_zero] at hb
  · exact atLeastInfiniteClusters_translate a

theorem atLeastTwo_iff_not_atMostOne (ω : LatticeConfiguration) :
    ω ∈ atLeastInfiniteClusters 2 ↔ ¬atMostOneInfiniteCluster ω := by
  constructor
  · rintro ⟨xs, hinf, hsep⟩ huni
    exact hsep 0 1 (by decide) (huni (xs 0) (xs 1) (hinf 0) (hinf 1))
  · intro h
    change ¬(∀ x y, ω ∈ infiniteAt x → ω ∈ infiniteAt y →
      (rcInfiniteOpenGraph ω).Reachable x y) at h
    push Not at h
    obtain ⟨x, y, hx, hy, hxy⟩ := h
    refine ⟨![x, y], ?_, ?_⟩
    · intro j
      fin_cases j
      · exact hx
      · exact hy
    · intro j k hjk
      fin_cases j <;> fin_cases k
      · exact (hjk rfl).elim
      · simpa using hxy
      · intro hreach
        exact hxy hreach.symm
      · exact (hjk rfl).elim

theorem atLeastInfiniteClusters_zero_one
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit p q i μ) (n : ℕ) :
    μ (atLeastInfiniteClusters n) = 0 ∨ μ (atLeastInfiniteClusters n) = 1 := by
  have : IsProbabilityMeasure μ := hμ.1
  exact (isRCInfiniteVolumeLimit_edge_ergodic p q hq i μ hμ).zero_one
    (measurableSet_atLeastInfiniteClusters n) (atLeastInfiniteClusters_invariant n)

/-- All thresholds, simultaneously outside one null set, are deterministic.
Thus the number of infinite components has a deterministic extended-natural
value, without choosing representatives of the random components. -/
theorem infinite_cluster_thresholds_ae_deterministic
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit p q i μ) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ, ω ∈ atLeastInfiniteClusters n ↔ μ (atLeastInfiniteClusters n) = 1 := by
  have : IsProbabilityMeasure μ := hμ.1
  apply ae_all_iff.mpr
  intro n
  rcases atLeastInfiniteClusters_zero_one p q hq i μ hμ n with hz | ho
  · have hAE : ∀ᵐ ω ∂μ, ω ∉ atLeastInfiniteClusters n := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_mem_eq] using hz
    filter_upwards [hAE] with ω hω
    simp only [hω, hz, zero_ne_one]
  · have hc : μ (atLeastInfiniteClusters n)ᶜ = 0 := by
      rw [measure_compl (measurableSet_atLeastInfiniteClusters n)
        (measure_ne_top μ _), measure_univ, ho, tsub_self]
    have hAE : ∀ᵐ ω ∂μ, ω ∈ atLeastInfiniteClusters n := ae_iff.mpr hc
    filter_upwards [hAE] with ω hω
    simp only [hω, ho]

def exactInfiniteClusters (n : ℕ) : Set LatticeConfiguration :=
  atLeastInfiniteClusters n \ atLeastInfiniteClusters (n + 1)

theorem measurableSet_exactInfiniteClusters (n : ℕ) : MeasurableSet (exactInfiniteClusters n) := by
  simpa only [exactInfiniteClusters, sdiff_eq_compl_inter, inter_comm] using
    (measurableSet_atLeastInfiniteClusters n).inter (measurableSet_atLeastInfiniteClusters (n + 1)).compl

/-- The infinite-cluster count is either a fixed finite number almost surely,
or exceeds every finite threshold almost surely. Finite-energy surgery is
needed separately to exclude finite values greater than one. -/
theorem infinite_cluster_count_finite_or_unbounded
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit p q i μ) :
    (∃ n : ℕ, μ (exactInfiniteClusters n) = 1) ∨
      (∀ᵐ ω ∂μ, ∀ n : ℕ, ω ∈ atLeastInfiniteClusters n) := by
  have : IsProbabilityMeasure μ := hμ.1
  by_cases hzero : ∃ n : ℕ, μ (atLeastInfiniteClusters n) = 0
  · left
    cases hk : Nat.find hzero with
    | zero =>
      have h0 := Nat.find_spec hzero
      rw [hk, show atLeastInfiniteClusters 0 = univ from Set.eq_univ_of_forall atLeastInfiniteClusters_zero,
        measure_univ] at h0
      exact (one_ne_zero h0).elim
    | succ n =>
      have hnext : μ (atLeastInfiniteClusters (n + 1)) = 0 := by
        simpa only [hk] using Nat.find_spec hzero
      have hprev : μ (atLeastInfiniteClusters n) = 1 := by
        rcases atLeastInfiniteClusters_zero_one p q hq i μ hμ n with hz | ho
        · exact (Nat.find_min hzero (show n < Nat.find hzero by rw [hk]; omega) hz).elim
        · exact ho
      have hAEprev : ∀ᵐ ω ∂μ, ω ∈ atLeastInfiniteClusters n := by
        apply ae_iff.mpr
        change μ (atLeastInfiniteClusters n)ᶜ = 0
        rw [measure_compl (measurableSet_atLeastInfiniteClusters n) (measure_ne_top μ _),
          measure_univ, hprev, tsub_self]
      have hAEnext : ∀ᵐ ω ∂μ, ω ∉ atLeastInfiniteClusters (n + 1) := by
        apply ae_iff.mpr
        simpa only [not_not, Set.ofPred_mem_eq] using hnext
      have hAE : ∀ᵐ ω ∂μ, ω ∈ exactInfiniteClusters n := by
        filter_upwards [hAEprev, hAEnext] with ω hprev hnext
        exact ⟨hprev, hnext⟩
      have hc : μ (exactInfiniteClusters n)ᶜ = 0 := ae_iff.mp hAE
      refine ⟨n, ?_⟩
      simpa only [hc, add_zero, measure_univ] using
        measure_add_measure_compl (μ := μ) (measurableSet_exactInfiniteClusters n)
  · right
    filter_upwards [infinite_cluster_thresholds_ae_deterministic p q hq i μ hμ] with ω hω
    intro n
    apply (hω n).mpr
    exact (atLeastInfiniteClusters_zero_one p q hq i μ hμ n).resolve_left (fun hn => hzero ⟨n, hn⟩)

end
end PottsContinuity.PD.RCInfinite
