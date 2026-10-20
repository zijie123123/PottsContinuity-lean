module

public import PottsContinuity.BD12.WiredSquare
public import PottsContinuity.PD.FK.CylinderDetermination

/-! Stochastic order and equality of single-edge intensities imply equality
of the whole laws. This is the elementary uniqueness step for the pressure route. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite MeasureTheory
noncomputable section
open scoped Classical

/-- Ordered laws with matching edge marginals agree on every finite cylinder
and hence on the complete product measurable space. -/
theorem lattice_measures_eq_of_domination_of_edge_marginals
    (μ ν : Measure LatticeConfiguration) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set LatticeConfiguration, IsCylinder A → IsUpperSet A → μ.real A ≤ ν.real A)
    (hedge : ∀ e : PD.squareLattice.edgeSet, μ.real {ω | ω e = true} = ν.real {ω | ω e = true}) : μ = ν := by
  have hupper (F : Finset PD.squareLattice.edgeSet) : IsUpperSet (LatticeConfiguration.allOpen F) := by
    intro ω η hωη hω e he
    have h := hωη e
    rw [hω e he] at h
    exact top_le_iff.mp h
  have hall : ∀ F : Finset PD.squareLattice.edgeSet,
      μ.real (LatticeConfiguration.allOpen F) = ν.real (LatticeConfiguration.allOpen F) := by
    intro F
    induction F using Finset.induction_on with
    | empty => simp [LatticeConfiguration.allOpen,Measure.real]
    | @insert e F he ih =>
      let A := LatticeConfiguration.allOpen F
      let B := LatticeConfiguration.allOpen {e}
      have hA : IsCylinder A := isCylinder_allOpen F
      have hB : IsCylinder B := isCylinder_allOpen {e}
      have hU : IsCylinder (A ∪ B) := by
        simpa only [Set.compl_inter,compl_compl] using (hA.compl.inter hB.compl).compl
      have hi := hdom (A ∩ B) (hA.inter hB) ((hupper F).inter (hupper {e}))
      have hu := hdom (A ∪ B) hU ((hupper F).union (hupper {e}))
      have hsingle : μ.real B = ν.real B := by simpa [B,LatticeConfiguration.allOpen] using hedge e
      have hμ := measureReal_union_add_inter (μ := μ) (s := A) hB.measurableSet
      have hν := measureReal_union_add_inter (μ := ν) (s := A) hB.measurableSet
      have hset : LatticeConfiguration.allOpen (insert e F) = A ∩ B := by
        ext ω
        simp [A,B,LatticeConfiguration.allOpen,and_comm]
      have hEq : μ.real (A ∩ B) = ν.real (A ∩ B) := by
        have hEqA : μ.real A = ν.real A := ih
        linarith only [hi,hu,hsingle,hμ,hν,hEqA]
      exact (congrArg (fun C => μ.real C) hset).trans (hEq.trans (congrArg (fun C => ν.real C) hset).symm)
  let μ' : ProbabilityMeasure LatticeConfiguration := ⟨μ,inferInstance⟩
  let ν' : ProbabilityMeasure LatticeConfiguration := ⟨ν,inferInstance⟩
  have heq : μ' = ν' := by
    apply LatticeConfiguration.probabilityMeasure_eq_of_allOpen
    intro F
    apply NNReal.coe_injective
    have h : (μ' : Measure LatticeConfiguration).real (LatticeConfiguration.allOpen F) =
        (ν' : Measure LatticeConfiguration).real (LatticeConfiguration.allOpen F) := hall F
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using h
  exact congrArg (fun ρ : ProbabilityMeasure LatticeConfiguration => ρ.toMeasure) heq

/-- Matching free and wired edge marginals suffice for uniqueness at an
interior parameter; no dense-set or pressure assertion is presumed. -/
theorem free_eq_wired_of_edge_marginals (θ : Parameters) (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ₁)
    (hedge : ∀ e : PD.squareLattice.edgeSet, μ₀.real {ω | ω e = true} = μ₁.real {ω | ω e = true}) : μ₀ = μ₁ := by
  let : IsProbabilityMeasure μ₀ := hμ₀.1
  let : IsProbabilityMeasure μ₁ := hμ₁.1
  exact lattice_measures_eq_of_domination_of_edge_marginals μ₀ μ₁
    (fun _ hA hu => free_limit_le_wired_cylinder θ μ₀ μ₁ hμ₀ hμ₁ hA hu) hedge

end
end PottsContinuity.BD12
