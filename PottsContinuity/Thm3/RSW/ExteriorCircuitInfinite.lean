module

public import PottsContinuity.Thm3.RSW.ClosedExtension

/-!
# Lemma 5 in the infinite-volume free measure

The finite statement passes to every genuine free infinite-volume limit by
Portmanteau on the open one-arm event. In particular no hypothesis that the
root cluster is finite, and no infinite-volume circuit selector, is needed.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK PD.RCInfinite Filter Topology
noncomputable section

/-- The infinite-volume form consumed by Propositions 3 and 4, for any free
infinite-volume limit at independent interior p and every real q≥1. -/
theorem exterior_circuit_infinite (θ : Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (k : ℕ) (hk : 1 ≤ k) :
    ENNReal.ofReal (oneArmProbability μ k) ≤
      ∑' m : {m : ℕ // k ≤ m},
        ENNReal.ofReal (72 * (m.val : ℝ)^4 * maxSquarePairProbability θ m.val) := by
  let μPD : Measure LatticeConfiguration := μ
  let E : Set LatticeConfiguration := infiniteArmEvent k
  have hPD : PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μPD :=
    free_limit_to_PD θ.toP θ.toQ μ hμ
  let : IsProbabilityMeasure μPD := hPD.1
  have hnest : ∀ n, box n ⊆ box (n + 1) := by
    intro n z hz
    simp only [box, Finset.mem_product, Finset.mem_Icc] at hz ⊢
    constructor <;> constructor <;> omega
  have hexhaust : ∀ z : ℤ × ℤ, ∃ n, z ∈ box n := by
    intro z
    refine ⟨z.1.natAbs + z.2.natAbs, ?_⟩
    simp only [box, Finset.mem_product, Finset.mem_Icc, Nat.cast_add, Int.natCast_natAbs]
    have hx := (abs_le.mp (le_refl |z.1|))
    have hy := (abs_le.mp (le_refl |z.2|))
    have hx0 := abs_nonneg z.1
    have hy0 := abs_nonneg z.2
    constructor <;> constructor <;> omega
  have hweak := finiteInducedSubgraphExhaustion_tendsto θ 0 μPD hPD box hnest hexhaust
  have hopen : IsOpen E := infiniteArmEvent_isOpen k
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hopen
  have hfinite : ∀ᶠ N : ℕ in atTop,
      (finiteSubgraphProbabilityMeasure θ (box N) 0).toMeasure E ≤
        ∑' m : {m : ℕ // k ≤ m},
          ENNReal.ofReal (72 * (m.val : ℝ)^4 * maxSquarePairProbability θ m.val) := by
    filter_upwards [eventually_ge_atTop k] with N hN
    have heq := finiteClosedExtension_arm_probability θ N k hN
    change (finiteSubgraphProbabilityMeasure θ (box N) 0).toMeasure E = _ at heq
    rw [heq]
    exact exterior_circuit_finite θ k N hk
  have hbound := hport.trans (Filter.liminf_le_of_frequently_le' hfinite.frequently)
  change ENNReal.ofReal (μPD E).toReal ≤ _
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact hbound

end
end PottsContinuity.RSW
