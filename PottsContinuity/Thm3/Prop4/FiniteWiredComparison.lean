module

public import PottsContinuity.Infinite.InducedDMP

/-!
# Lower-event comparison for a genuine finite wired induced domain

This is the complement of the increasing-event DMP comparison of `Infinite.InducedDMP`, with
an unconditional exterior event. Both laws are genuine probability measures.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.RCInfinite
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The identity-coordinate embedding of an arbitrary finite induced domain. -/
def finiteDomainEmbedding (S : Finset LatticeVertex) : (S : Set LatticeVertex) ↪ LatticeVertex :=
  ⟨Subtype.val,Subtype.val_injective⟩

/-- Every induced original edge remains an original whole-plane edge. -/
theorem finiteDomainEmbedding_map_le (S : Finset LatticeVertex) :
    (finiteLatticeGraph S).map (finiteDomainEmbedding S) ≤ PD.FK.squareLattice := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  obtain ⟨a,b,hab,rfl,rfl⟩ := hxy
  exact hab

/-- Finite wired laws bound every decreasing event by its genuine wired-plane restriction event. -/
theorem wired_induced_lower_event_le_infinite (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (S : Finset LatticeVertex) (A : Set (Configuration (finiteLatticeGraph S)))
    (hA : IsLowerSet A) :
    (measure (finiteLatticeGraph S) θ (frozenBoundaryCondition S 1) A).toReal ≤
      μ.real (Infinite.latticeGraphEvent (finiteLatticeGraph S)
        (finiteDomainEmbedding S) (finiteDomainEmbedding_map_le S) A) := by
  classical
  let : IsProbabilityMeasure μ := hμ.1
  let ν := measure (finiteLatticeGraph S) θ (frozenBoundaryCondition S 1)
  let E := Infinite.latticeGraphEvent (finiteLatticeGraph S)
    (finiteDomainEmbedding S) (finiteDomainEmbedding_map_le S) A
  have hμPD := Infinite.isRCInfiniteVolumeLimit_to_PD_box _ _ _ _ hμ
  have hupper : IsUpperSet Aᶜ := hA.compl
  have h := Infinite.wired_infinite_DMP_induced_measurable θ μ hμPD S Aᶜ hupper
    Set.univ MeasurableSet.univ
  have hpre : Infinite.latticeGraphEvent (finiteLatticeGraph S)
      (finiteDomainEmbedding S) (finiteDomainEmbedding_map_le S) Aᶜ = Eᶜ := rfl
  have hupperbound : μ.real Eᶜ ≤ ν.real Aᶜ := by
    change μ.real (Infinite.latticeGraphEvent (finiteLatticeGraph S)
      (finiteDomainEmbedding S) (finiteDomainEmbedding_map_le S) Aᶜ ∩ Set.univ) ≤
        ν.real Aᶜ * μ.real Set.univ at h
    rw [Set.inter_univ,probReal_univ,mul_one,hpre] at h
    exact h
  have hE : MeasurableSet E := (Infinite.latticeGraphEvent_isCylinder _ _ _ A).measurableSet
  have hν : IsProbabilityMeasure ν := inferInstance
  rw [probReal_compl_eq_one_sub hE,
    probReal_compl_eq_one_sub (μ := ν) MeasurableSpace.measurableSet_top] at hupperbound
  change ν.real A ≤ μ.real E
  linarith only [hupperbound]

end
end PottsContinuity.Thm3.Prop4
