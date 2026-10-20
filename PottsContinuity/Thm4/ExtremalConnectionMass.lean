module

public import PottsContinuity.Thm4.UniformBoundaryLower
public import PottsContinuity.Thm4.FarLayerEndpoint
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverExtremalSheets
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverExtremalDecayLimit

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK Filter Topology
noncomputable section

/-- Uniform exponential decay to either extreme sheet throughout the closed
real range [1,4], for the actual finite free law at the explicit parameter. -/
theorem coverOriginConnectionProbability_le_exp_extremal
    (q : Set.Icc (1 : ℝ) 4) (n : ℕ) (hn : 1 ≤ n)
    (v : ParafermionicAmbientVertex n)
    (hv : v.val.2 = ((n ^ 5 : ℕ) : ℤ) ∨ v.val.2 = -((n ^ 5 : ℕ) : ℤ)) :
    coverOriginConnectionProbability n ⟨q, q.2.1⟩ v ≤
      Real.exp (-((n : ℝ) - 1) / 60) := by
  by_cases hq : q.val = 4
  · have heq : q = ⟨4, by norm_num⟩ := Subtype.ext hq
    subst q
    rcases hv with hv | hv
    · exact cover_connection_four_le_exp_positive n hn rfl hv
    · exact cover_connection_four_le_exp_negative n hn rfl hv
  · have hlt : q.val < 4 := lt_of_le_of_ne q.2.2 hq
    let q' : PottsContinuity.FKC.ClusterWeight := ⟨q.val, q.2.1, hlt⟩
    have h : PottsContinuity.FKC.FiniteFK.parafermionicCoverBoxOriginConnectionWeight
        n q' v.val ≤ Real.exp (-((n : ℝ) - 1) / 60) := by
      erw [PottsContinuity.FKC.FiniteFK.parafermionicCoverBoxOriginConnectionWeight_subtype]
      rcases hv with hv | hv
      · exact PottsContinuity.FKC.FiniteFK.parafermionicCoverConnection_probability_le_exp_positive
          n hn q' (u := PottsContinuity.FKC.FiniteFK.parafermionicCoverBoxOrigin n)
          (v := v) rfl hv
      · exact PottsContinuity.FKC.FiniteFK.parafermionicCoverConnection_probability_le_exp_negative
          n hn q' (u := PottsContinuity.FKC.FiniteFK.parafermionicCoverBoxOrigin n)
          (v := v) rfl hv
    rw [fkc_coverOriginConnectionWeight_eq] at h
    exact h

/-- Actual connection probability mass on both complete extreme sheets. -/
def coverExtremalConnectionMass (n : ℕ) (q : Set.Icc (1 : ℝ) 4) : ℝ :=
  ∑ v ∈ PottsContinuity.FKC.FiniteFK.parafermionicCoverExtremalSheetVertices n,
    coverOriginConnectionProbability n ⟨q, q.2.1⟩ v

theorem coverExtremalConnectionMass_le (q : Set.Icc (1 : ℝ) 4) (n : ℕ) (hn : 1 ≤ n) :
    coverExtremalConnectionMass n q ≤
      2 * (2 * (n : ℝ) + 1)^2 * Real.exp (-((n : ℝ) - 1) / 60) := by
  unfold coverExtremalConnectionMass
  calc
    _ ≤ ∑ v ∈ PottsContinuity.FKC.FiniteFK.parafermionicCoverExtremalSheetVertices n,
        Real.exp (-((n : ℝ) - 1) / 60) := by
      apply Finset.sum_le_sum
      intro v hv
      exact coverOriginConnectionProbability_le_exp_extremal q n hn v
        ((PottsContinuity.FKC.FiniteFK.mem_parafermionicCoverExtremalSheetVertices n v).mp hv)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul,
        PottsContinuity.FKC.FiniteFK.parafermionicCoverExtremalSheetVertices_card n hn]
      push_cast
      ring

/-- Extreme-sheet mass tends to zero for every real 1 <= q <= 4. -/
theorem tendsto_coverExtremalConnectionMass (q : Set.Icc (1 : ℝ) 4) :
    Tendsto (fun n : ℕ => coverExtremalConnectionMass n q) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    PottsContinuity.FKC.FiniteFK.tendsto_parafermionicCover_extremalLayer_envelope
  · exact Eventually.of_forall fun n =>
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  · exact eventually_atTop.2 ⟨1, fun n hn => coverExtremalConnectionMass_le q n hn⟩

end
end PottsContinuity.Thm4
