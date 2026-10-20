module

public import PottsContinuity.Thm4.SideWitnessAllScales
public import PottsContinuity.Thm4.FiniteWitnessEndpoint
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverSideToSlitComparison

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK
noncomputable section
local instance (n : ℕ) : Fintype (PottsContinuity.FKC.FiniteFK.SlitBoxVertex n) :=
  Fintype.ofFinite _

/-- Actual connection to the wired arc in the literal slit-box graph, under
the genuine PD finite measure at the explicit self-dual parameter. -/
def slitArcConnectionProbability (n : ℕ) (q : Set.Ici (1 : ℝ))
    (u : PottsContinuity.FKC.FiniteFK.SlitBoxVertex n) : ℝ :=
  (measure (PottsContinuity.FKC.FiniteFK.slitBoxGraph n) (selfDualParameters q)
    (fkcBoundaryToPD (PottsContinuity.FKC.FiniteFK.slitBoxBoundary n))
    (PottsContinuity.FKC.FiniteFK.slitBoxWiredArcConnectionEvent n u)).toReal

theorem continuous_slitArcConnectionProbability (n : ℕ)
    (u : PottsContinuity.FKC.FiniteFK.SlitBoxVertex n) :
    Continuous (fun q => slitArcConnectionProbability n q u) :=
  continuous_selfDual_eventProbability _ _ _

/-- The actual side-to-slit comparison with a uniform three-edge cost in the
strict range. The geometry uses a rotated enlargement, not box invariance. -/
theorem cover_side_to_slit_strict (n : ℕ) (hn : 1 ≤ n)
    (q : PottsContinuity.FKC.ClusterWeight) (v : ParafermionicAmbientVertex n)
    (hv : v ∈ coverSideBoundary n) :
    ∃ u : PottsContinuity.FKC.FiniteFK.SlitBoxVertex (n + 1),
      u.val.2 = -((n + 1 : ℕ) : ℤ) ∧
      (1 / 27 : ℝ) * coverOriginConnectionProbability n ⟨q, q.2.1⟩ v ≤
        slitArcConnectionProbability (n + 1) ⟨q, q.2.1⟩ u := by
  classical
  have hv' := Finset.mem_image_of_mem Subtype.val hv
  rw [coverSideBoundary_image] at hv'
  obtain ⟨u, hu, hbound⟩ :=
    PottsContinuity.FKC.FiniteFK.parafermionicCoverBoxOriginConnectionWeight_le_slitBoxArcHit_of_side
      n hn q hv'
  rw [fkc_measure_eq, fkc_coverOriginConnectionWeight_eq] at hbound
  have hthird : (1 / 3 : ℝ) ≤ 1 / (1 + PottsContinuity.FKC.loopWeight q) := by
    apply (div_le_div_iff₀ (by norm_num)
      (PottsContinuity.FKC.one_add_loopWeight_pos q)).mpr
    nlinarith [PottsContinuity.FKC.loopWeight_lt_two q]
  have hcost : (1 / 27 : ℝ) ≤ (1 / (1 + PottsContinuity.FKC.loopWeight q))^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 3) hthird 3
    norm_num at h ⊢
    exact h
  refine ⟨u, hu, ?_⟩
  exact (mul_le_mul_of_nonneg_right hcost ENNReal.toReal_nonneg).trans hbound

/-- The same actual side-to-slit comparison at q=4, obtained by finite-volume
continuity and a finite bottom-boundary witness set. -/
theorem cover_side_to_slit_four (n : ℕ) (hn : 1 ≤ n)
    (v : ParafermionicAmbientVertex n) (hv : v ∈ coverSideBoundary n) :
    ∃ u : PottsContinuity.FKC.FiniteFK.SlitBoxVertex (n + 1),
      u.val.2 = -((n + 1 : ℕ) : ℤ) ∧
      (1 / 27 : ℝ) * coverOriginConnectionProbability n ⟨4, by norm_num⟩ v ≤
        slitArcConnectionProbability (n + 1) ⟨4, by norm_num⟩ u := by
  classical
  let S := Finset.univ.filter fun u : PottsContinuity.FKC.FiniteFK.SlitBoxVertex (n + 1) =>
    u.val.2 = -((n + 1 : ℕ) : ℤ)
  have h := continuous_finite_witness_at_four S
    (fun q => (1 / 27 : ℝ) * coverOriginConnectionProbability n q v)
    (fun u q => slitArcConnectionProbability (n + 1) q u)
    (continuous_const.mul (continuous_selfDual_eventProbability _ _ _))
    (fun u _ => continuous_slitArcConnectionProbability (n + 1) u)
    (fun q hq => by
      obtain ⟨u, hu, hbound⟩ := cover_side_to_slit_strict n hn ⟨q.val, q.property, hq⟩ v hv
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, hbound⟩)
  obtain ⟨u, hu, hbound⟩ := h
  exact ⟨u, (Finset.mem_filter.mp hu).2, hbound⟩

/-- Full closed-range side-to-slit transfer, with one uniform three-edge cost. -/
theorem cover_side_to_slit (n : ℕ) (hn : 1 ≤ n) (q : Set.Icc (1 : ℝ) 4)
    (v : ParafermionicAmbientVertex n) (hv : v ∈ coverSideBoundary n) :
    ∃ u : PottsContinuity.FKC.FiniteFK.SlitBoxVertex (n + 1),
      u.val.2 = -((n + 1 : ℕ) : ℤ) ∧
      (1 / 27 : ℝ) * coverOriginConnectionProbability n ⟨q, q.2.1⟩ v ≤
        slitArcConnectionProbability (n + 1) ⟨q, q.2.1⟩ u := by
  by_cases hq : q.val = 4
  · have heq : q = ⟨4, by norm_num⟩ := Subtype.ext hq
    subst q
    exact cover_side_to_slit_four n hn v hv
  · exact cover_side_to_slit_strict n hn ⟨q.val, q.2.1, lt_of_le_of_ne q.2.2 hq⟩ v hv

end
end PottsContinuity.Thm4
