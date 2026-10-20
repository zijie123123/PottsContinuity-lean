-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/FiniteClusterExclusion.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.GraphModification
public import PottsContinuity.PD.RCInfinite.ClusterThresholds
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

open MeasureTheory Set

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

def infiniteClusterWitnesses {n : ℕ} (xs : Fin n → LatticeVertex) : Set LatticeConfiguration :=
  {ω | (∀ j, ω ∈ infiniteAt (xs j)) ∧
    ∀ j k, j ≠ k → ¬(rcInfiniteOpenGraph ω).Reachable (xs j) (xs k)}

theorem measurableSet_infiniteClusterWitnesses {n : ℕ} (xs : Fin n → LatticeVertex) :
    MeasurableSet (infiniteClusterWitnesses xs) := by
  have hsep (j k : Fin n) : MeasurableSet {ω : LatticeConfiguration |
      j ≠ k → ¬(rcInfiniteOpenGraph ω).Reachable (xs j) (xs k)} := by
    by_cases hjk : j = k
    · simp only [hjk, ne_eq, not_true_eq_false, false_implies, Set.ofPred_true, MeasurableSet.univ]
    · have heq : {ω : LatticeConfiguration | j ≠ k →
          ¬(rcInfiniteOpenGraph ω).Reachable (xs j) (xs k)} =
          {ω : LatticeConfiguration | (rcInfiniteOpenGraph ω).Reachable (xs j) (xs k)}ᶜ := by
        ext ω
        simp only [mem_ofPred_eq, mem_compl_iff, hjk, ne_eq, not_false_eq_true, true_implies]
      rw [heq]
      exact (measurableSet_open_reachable (xs j) (xs k)).compl
  convert (MeasurableSet.iInter fun j => measurableSet_infiniteAt (xs j)).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => hsep j k)
  ext ω
  simp only [infiniteClusterWitnesses, mem_ofPred_eq, mem_inter_iff, mem_iInter]

theorem witnesses_exhaust {n : ℕ} {xs : Fin n → LatticeVertex} {ω : LatticeConfiguration}
    (hxs : ω ∈ infiniteClusterWitnesses xs) (hnext : ω ∉ atLeastInfiniteClusters (n + 1))
    (z : LatticeVertex) (hz : ω ∈ infiniteAt z) :
    ∃ j, (rcInfiniteOpenGraph ω).Reachable (xs j) z := by
  by_contra! hnone
  apply hnext
  refine ⟨Fin.snoc xs z, ?_, ?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hz
    · simpa using hxs.1 j
  · intro j k hjk
    revert hjk
    refine Fin.lastCases ?_ (fun j => ?_) j
    · refine Fin.lastCases ?_ (fun k => ?_) k
      · exact fun h => (h rfl).elim
      · intro _ hr
        exact hnone k (by simpa using hr.symm)
    · refine Fin.lastCases ?_ (fun k => ?_) k
      · intro _ hr
        exact hnone j (by simpa using hr)
      · intro hjk hr
        apply hxs.2 j k (fun h => hjk (congrArg Fin.castSucc h))
        simpa using hr

theorem opening_witnesses_unique {n : ℕ} {xs : Fin n → LatticeVertex}
    (F : Finset Edge)
    (hconnect : ∀ ω : LatticeConfiguration, ∀ j k : Fin n,
      (rcInfiniteOpenGraph (setEdges F (fun _ => true) ω)).Reachable (xs j) (xs k))
    {ω : LatticeConfiguration} (hxs : ω ∈ infiniteClusterWitnesses xs)
    (hnext : ω ∉ atLeastInfiniteClusters (n + 1)) :
    atMostOneInfiniteCluster (setEdges F (fun _ => true) ω) := by
  intro x y hx hy
  obtain ⟨u, hxu, hu⟩ := opening_infinite_component_contains_old F ω x hx
  obtain ⟨v, hyv, hv⟩ := opening_infinite_component_contains_old F ω y hy
  obtain ⟨j, hju⟩ := witnesses_exhaust hxs hnext u hu
  obtain ⟨k, hkv⟩ := witnesses_exhaust hxs hnext v hv
  exact (hxu.trans (hju.mono (opening_graph_mono F ω)).symm).trans
    ((hconnect ω j k).trans ((hkv.mono (opening_graph_mono F ω)).trans hyv.symm))

/-- Finite energy excludes an almost surely fixed finite number of infinite
components greater than one. The infinite-count case requires the separate
encounter-point counting argument. -/
theorem exactInfiniteClusters_measure_ne_one (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (n : ℕ) (hn : 2 ≤ n) : μ (exactInfiniteClusters n) ≠ 1 := by
  have : IsProbabilityMeasure μ := hμ.1
  intro hcount
  let A (xs : Fin n → LatticeVertex) := exactInfiniteClusters n ∩ infiniteClusterWitnesses xs
  have hA (xs : Fin n → LatticeVertex) : MeasurableSet (A xs) :=
    (measurableSet_exactInfiniteClusters n).inter (measurableSet_infiniteClusterWitnesses xs)
  have hunion : (⋃ xs, A xs) = exactInfiniteClusters n := by
    ext ω
    constructor
    · intro hω
      obtain ⟨xs, hxs⟩ := mem_iUnion.mp hω
      exact hxs.1
    · intro hω
      obtain ⟨xs, hxs⟩ := hω.1
      exact mem_iUnion.mpr ⟨xs, hω, hxs⟩
  have hpos : ∃ xs, 0 < μ.real (A xs) := by
    by_contra! hz
    have hz' : ∀ xs, μ (A xs) = 0 := by
      intro xs
      apply (ENNReal.toReal_eq_zero_iff _).mp ?_ |>.resolve_right (measure_ne_top μ _)
      exact le_antisymm (hz xs) (measureReal_nonneg)
    have h := measure_iUnion_null hz'
    rw [hunion, hcount] at h
    exact one_ne_zero h
  obtain ⟨xs, hpos⟩ := hpos
  obtain ⟨F, hF⟩ := exists_finite_opening_connects n xs
  have himage := setEdges_image_real_pos θ i μ hμ F (fun _ => true) (hA xs) hpos
  have hsub : setEdges F (fun _ => true) '' A xs ⊆ (exactInfiniteClusters n)ᶜ := by
    rintro η ⟨ω, hω, rfl⟩ hη
    have huni := opening_witnesses_unique F hF hω.2 hω.1.2
    have htwo := atLeastInfiniteClusters_antitone hn hη.1
    exact ((atLeastTwo_iff_not_atMostOne _).mp htwo) huni
  have hc : μ (exactInfiniteClusters n)ᶜ = 0 := by
    rw [measure_compl (measurableSet_exactInfiniteClusters n) (measure_ne_top μ _),
      measure_univ, hcount, tsub_self]
  have hle : μ.real (setEdges F (fun _ => true) '' A xs) ≤ 0 := by
    have := measureReal_mono (μ := μ) hsub
    simpa only [Measure.real, hc, ENNReal.toReal_zero] using this
  exact (not_lt_of_ge hle) himage

theorem infinite_cluster_count_zero_one_or_unbounded (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) :
    μ (exactInfiniteClusters 0) = 1 ∨ μ (exactInfiniteClusters 1) = 1 ∨
      (∀ᵐ ω ∂μ, ∀ n : ℕ, ω ∈ atLeastInfiniteClusters n) := by
  rcases infinite_cluster_count_finite_or_unbounded θ.toP θ.toQ θ.property i μ hμ with
    ⟨n, hn⟩ | h
  · by_cases h0 : n = 0
    · exact Or.inl (h0 ▸ hn)
    · by_cases h1 : n = 1
      · exact Or.inr (Or.inl (h1 ▸ hn))
      · exact (exactInfiniteClusters_measure_ne_one θ i μ hμ n (by omega) hn).elim
  · exact Or.inr (Or.inr h)

end
end PottsContinuity.PD.RCInfinite
