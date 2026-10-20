module

public import PottsContinuity.Thm3.Prop4.TiltedCylinderUpper
public import PottsContinuity.Thm3.Prop4.TiltedSideComparison

/-! # Cylinder convergence independent of the artificial side wiring -/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.RCInfinite

noncomputable section

/-- Weak convergence of the top-only law supplies its actual real cylinders. -/
theorem tilted_top_allOpen_real_tendsto (θ : Parameters) (n : ℕ) (t : ℝ)
    (ν : ProbabilityMeasure LatticeConfiguration)
    (hν : Tendsto (tiltedWindowPlaneProbabilityMeasure θ n t 0) atTop (𝓝 ν))
    (F : Finset squareLattice.edgeSet) :
    Tendsto (fun M => (tiltedWindowPlaneProbabilityMeasure θ n t 0 M).toMeasure.real
      (LatticeConfiguration.allOpen F)) atTop (𝓝 (ν.toMeasure.real (LatticeConfiguration.allOpen F))) := by
  have hNN := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν
    (LatticeConfiguration.allOpen_isClopen F)
  simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn,Function.comp_def] using
    NNReal.continuous_coe.continuousAt.tendsto.comp hNN

/-- All actual finite cylinders have the same limit for top-only or top-plus-
side wiring. The proof includes cylinders containing edges outside the strip;
those are identically zero under the literal closed plane extensions. -/
theorem tilted_side_allOpen_real_tendsto (θ : Parameters) (n : ℕ) (t : ℝ) (ht : |t| ≤ 1)
    (ν : ProbabilityMeasure LatticeConfiguration)
    (hν : Tendsto (tiltedWindowPlaneProbabilityMeasure θ n t 0) atTop (𝓝 ν))
    (side : Fin 2) (F : Finset squareLattice.edgeSet) :
    Tendsto (fun M => (tiltedWindowPlaneProbabilityMeasure θ n t side M).toMeasure.real
      (LatticeConfiguration.allOpen F)) atTop (𝓝 (ν.toMeasure.real (LatticeConfiguration.allOpen F))) := by
  classical
  have htop := tilted_top_allOpen_real_tendsto θ n t ν hν F
  by_cases hsupp : ∃ R : ℕ, ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding (tiltedWindow n R t))
  · obtain ⟨R,hF⟩ := hsupp
    have hg : Tendsto (fun K : ℕ => n+R+K) atTop atTop := by
      apply tendsto_atTop.mpr
      intro N
      filter_upwards [eventually_ge_atTop N] with K hK
      omega
    have hupper : Tendsto (fun K : ℕ => ν.toMeasure.real (LatticeConfiguration.allOpen F)+
        2*(1-(1-edgeParameter θ)^(n+1))^K) atTop
        (𝓝 (ν.toMeasure.real (LatticeConfiguration.allOpen F))) := by
      simpa only [add_zero] using (tilted_scan_error_tendsto_zero θ n).const_add
        (ν.toMeasure.real (LatticeConfiguration.allOpen F))
    have hshift : Tendsto (fun K : ℕ =>
        (tiltedWindowPlaneProbabilityMeasure θ n t side (n+R+K)).toMeasure.real
          (LatticeConfiguration.allOpen F)) atTop (𝓝 (ν.toMeasure.real (LatticeConfiguration.allOpen F))) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le (htop.comp hg) hupper
      · intro K
        exact tiltedWindowPlane_top_allOpen_le_side θ n (n+R+K) t side F
      · intro K
        dsimp only
        rw [tiltedWindowPlane_allOpen_eq]
        exact tilted_window_allOpen_le_limit_add_error θ n (n+R+K) R K rfl t ht side ν hν F hF
    apply (tendsto_add_atTop_iff_nat (n+R)).mp
    simpa only [Nat.add_comm (n+R)] using hshift
  · have hzero (M : ℕ) (side : Fin 2) :
        (tiltedWindowPlaneProbabilityMeasure θ n t side M).toMeasure.real (LatticeConfiguration.allOpen F) = 0 := by
      have hempty : finiteSubgraphOpenEvent (tiltedWindow n M t) F = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro A hA
        apply hsupp
        refine ⟨M,?_⟩
        intro e he
        obtain ⟨x,_,hxe⟩ := Finset.mem_map.mp (hA he)
        exact ⟨x,hxe⟩
      rw [tiltedWindowPlane_allOpen_eq,hempty,measure_empty,ENNReal.toReal_zero]
    have hzlim : Tendsto (fun M => (tiltedWindowPlaneProbabilityMeasure θ n t 0 M).toMeasure.real
        (LatticeConfiguration.allOpen F)) atTop (𝓝 0) := by
      simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    have hνzero := tendsto_nhds_unique htop hzlim
    rw [hνzero]
    simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end

end PottsContinuity.Thm3.Prop4
