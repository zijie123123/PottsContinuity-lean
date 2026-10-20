module

public import PottsContinuity.Thm3.OuterCircuit.ResidualAnnulusSupport

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.RSW

universe u

noncomputable section

def outerCircuitLiftedResidualGraph {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    SimpleGraph (ULift.{u,0} (OuterCircuitResidualVertices n C)) :=
  (outerCircuitResidualGraph C).map (Equiv.ulift.{u,0}.symm)

def outerCircuitLiftedResidualGraphIso {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    (outerCircuitResidualGraph C) ≃g outerCircuitLiftedResidualGraph C :=
  SimpleGraph.Iso.map (Equiv.ulift.{u,0}.symm) (outerCircuitResidualGraph C)

def outerCircuitLiftedResidualEmbedding {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    ULift.{u,0} (OuterCircuitResidualVertices n C) ↪ OuterCircuitHostVertex n :=
  ⟨fun x => outerCircuitResidualEmbedding C x.down, by
    intro x y h
    apply ULift.ext
    exact (outerCircuitResidualEmbedding C).injective h⟩

def outerCircuitLiftedResidualBoundarySet {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    Set (ULift.{u,0} (OuterCircuitResidualVertices n C)) :=
  {x | (outerCircuitLiftedResidualGraphIso C).symm x ∈
    outerCircuitResidualBoundarySet C}

noncomputable def outerCircuitLiftedResidualConfigurationToBase {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (A : Configuration (outerCircuitLiftedResidualGraph C)) :
    Configuration (outerCircuitResidualGraph C) :=
  A.map ((outerCircuitLiftedResidualGraphIso C).mapEdgeSet).symm.toEmbedding

theorem outerCircuitLiftedResidualConfigurationToBase_mem_iff {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (A : Configuration (outerCircuitLiftedResidualGraph C))
    (e : (outerCircuitResidualGraph C).edgeSet) :
    e ∈ outerCircuitLiftedResidualConfigurationToBase C A ↔
      (outerCircuitLiftedResidualGraphIso C).mapEdgeSet e ∈ A := by
  simp only [outerCircuitLiftedResidualConfigurationToBase, Finset.mem_map]
  constructor
  · rintro ⟨e', he', heq⟩
    have heq' : e' = (outerCircuitLiftedResidualGraphIso C).mapEdgeSet e := by
      change (outerCircuitLiftedResidualGraphIso C).mapEdgeSet.symm e' = e at heq
      calc
        e' = (outerCircuitLiftedResidualGraphIso C).mapEdgeSet
            ((outerCircuitLiftedResidualGraphIso C).mapEdgeSet.symm e') :=
          (Equiv.apply_symm_apply
            (outerCircuitLiftedResidualGraphIso C).mapEdgeSet e').symm
        _ = (outerCircuitLiftedResidualGraphIso C).mapEdgeSet e :=
          congrArg (outerCircuitLiftedResidualGraphIso C).mapEdgeSet heq
    simpa only [heq'] using he'
  · intro he
    refine ⟨(outerCircuitLiftedResidualGraphIso C).mapEdgeSet e, he, ?_⟩
    change (outerCircuitLiftedResidualGraphIso C).mapEdgeSet.symm
      ((outerCircuitLiftedResidualGraphIso C).mapEdgeSet e) = e
    exact Equiv.symm_apply_apply
      (outerCircuitLiftedResidualGraphIso C).mapEdgeSet e

def outerCircuitLiftedResidualAnnulusPairEvent {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    Set (Configuration (outerCircuitLiftedResidualGraph C)) :=
  {A | outerCircuitLiftedResidualConfigurationToBase C A ∈
    outerCircuitResidualAnnulusPairEvent C}

theorem outerCircuitLiftedResidualAnnulusPairEvent_isUpperSet {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    IsUpperSet (outerCircuitLiftedResidualAnnulusPairEvent C) := by
  intro A B hAB hA
  apply outerCircuitResidualAnnulusPairEvent_isUpperSet C
  · exact Finset.map_subset_map.mpr hAB
  · exact hA

end
end PottsContinuity.OuterCircuit
