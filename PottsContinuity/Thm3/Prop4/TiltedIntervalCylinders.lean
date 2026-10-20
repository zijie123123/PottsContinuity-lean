module

public import PottsContinuity.Thm3.Prop4.TiltedInterval
public import PottsContinuity.Thm3.Prop4.TiltedLaw
public import PottsContinuity.Thm3.Prop4.InducedCylinders

/-! # Dominating the actual interval cylinders by the top-only strip limit -/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.RCInfinite

noncomputable section

local instance intervalCylinderEdgeFintype (n M : ℕ) (t : ℝ) (lo hi : ℤ) :
    Fintype (squareLattice.induce (tiltedInterval n M t lo hi : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _

/-- The literal closed plane extension reads exactly the actual all-open
finite induced cylinder, including when some queried edge is absent. -/
theorem tiltedWindowPlane_allOpen_eq (θ : Parameters) (n M : ℕ) (t : ℝ) (i : Fin 2)
    (F : Finset squareLattice.edgeSet) :
    (tiltedWindowPlaneProbabilityMeasure θ n t i M).toMeasure.real (LatticeConfiguration.allOpen F) =
      (measure (finiteLatticeGraph (tiltedWindow n M t)) θ (tiltedWindowBoundary n M t i)
        (finiteSubgraphOpenEvent (tiltedWindow n M t) F)).toReal := by
  unfold Measure.real
  rw [tiltedWindowPlaneProbabilityMeasure_apply θ n t i M _
    (LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet]
  congr 2
  ext A
  simp only [tiltedWindowPlaneConfiguration,LatticeConfiguration.allOpen,finiteSubgraphOpenEvent,
    Set.mem_ofPred_eq,decide_eq_true_eq]
  rfl

/-- Compare the intrinsic-top interval to any larger top-only tilted window. -/
theorem tiltedIntervalTop_allOpen_le_window (θ : Parameters) (n M N : ℕ) (t : ℝ)
    (lo hi : ℤ) (hMN : M ≤ N) (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding (tiltedInterval n M t lo hi))) :
    (measure (finiteLatticeGraph (tiltedInterval n M t lo hi)) θ
      (tiltedIntervalTopBoundary n M t lo hi)
      (finiteSubgraphOpenEvent (tiltedInterval n M t lo hi) F)).toReal ≤
        (measure (finiteLatticeGraph (tiltedWindow n N t)) θ (tiltedWindowBoundary n N t 0)
          (finiteSubgraphOpenEvent (tiltedWindow n N t) F)).toReal := by
  classical
  let S := tiltedInterval n M t lo hi
  let T := tiltedWindow n N t
  let G := finiteLatticeGraph S
  let H := finiteLatticeGraph T
  let f : (S : Set (ℤ × ℤ)) ↪ (T : Set (ℤ × ℤ)) :=
    (tiltedIntervalEmbedding n M t lo hi).trans (tiltedWindowEmbedding (n := n) (t := t) hMN)
  have hf : ∀ u, (f u).val = u.val := fun _ => rfl
  have hmap : G.map f ≤ H := by
    rw [SimpleGraph.map_le_iff_le_comap]
    intro u v huv
    exact huv
  have hpart : (isolatedExtensionPullbackBoundary f (tiltedWindowBoundary n N t 0)).partition =
      (tiltedIntervalTopBoundary n M t lo hi).partition := by
    apply Setoid.ext
    intro u v
    change (f u = f v ∨ (tiltedTop n t (f u).val ∨ _) ∧ (tiltedTop n t (f v).val ∨ _)) ↔
      (u = v ∨ tiltedTop n t u.val ∧ tiltedTop n t v.val)
    simp only [Fin.zero_ne_one,false_and,or_false,hf,f.injective.eq_iff]
  let E := finiteSubgraphOpenEvent S F
  have hE : IsUpperSet E := fun _ _ hAB hA => hA.trans (Finset.map_subset_map.mpr hAB)
  have hcomp := RSW.embedded_boundary_probability_le G H f hmap θ (tiltedWindowBoundary n N t 0) E hE
  have hmeasure : measure G θ (isolatedExtensionPullbackBoundary f (tiltedWindowBoundary n N t 0)) =
      measure G θ (tiltedIntervalTopBoundary n M t lo hi) := by
    unfold PD.FK.measure
    rw [law_eq_of_boundary_partition_eq θ _ _ hpart]
  have hsets : {A | embeddedConfigurationRestriction G H f hmap A ∈ E} = finiteSubgraphOpenEvent T F := by
    ext A
    exact (induced_openEvent_restriction_iff f hf hmap F hF A).symm
  rw [hmeasure,hsets] at hcomp
  exact hcomp

/-- Every actual top-only interval cylinder is dominated by the genuine
plane weak limit of top-only strip windows. -/
theorem tiltedIntervalTop_allOpen_le_limit (θ : Parameters) (n M : ℕ) (t : ℝ) (lo hi : ℤ)
    (ν : ProbabilityMeasure LatticeConfiguration)
    (hν : Tendsto (tiltedWindowPlaneProbabilityMeasure θ n t 0) atTop (𝓝 ν))
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding (tiltedInterval n M t lo hi))) :
    (measure (finiteLatticeGraph (tiltedInterval n M t lo hi)) θ
      (tiltedIntervalTopBoundary n M t lo hi)
      (finiteSubgraphOpenEvent (tiltedInterval n M t lo hi) F)).toReal ≤
        ν.toMeasure.real (LatticeConfiguration.allOpen F) := by
  have hNN := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν
    (LatticeConfiguration.allOpen_isClopen F)
  have hreal : Tendsto (fun N => (tiltedWindowPlaneProbabilityMeasure θ n t 0 N).toMeasure.real
      (LatticeConfiguration.allOpen F)) atTop (𝓝 (ν.toMeasure.real (LatticeConfiguration.allOpen F))) := by
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn,Function.comp_def] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hNN
  apply ge_of_tendsto hreal
  filter_upwards [eventually_ge_atTop M] with N hMN
  rw [tiltedWindowPlane_allOpen_eq]
  exact tiltedIntervalTop_allOpen_le_window θ n M N t lo hi hMN F hF

end

end PottsContinuity.Thm3.Prop4
