module

public import PottsContinuity.Thm3.RSW.SeedSeparatedProduct
public import PottsContinuity.Thm3.RSW.SeedAvoidingAnnulus
public import PottsContinuity.Thm3.RSW.AnnulusScreenProduct
public import PottsContinuity.Thm3.RSW.AnnulusSeedRecord

/-! # The screened-annulus product for overlapping source reference boxes -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section
local instance overlappingAnnulusScreensRegionFintype
    (V : Finset (ℤ × ℤ)) (z : ℤ × ℤ) (r : ℕ) :
    Fintype (vertexBoxRegion V z r) := Fintype.ofFinite _

/-- Reference boxes may overlap. It is enough that the first box lies to the
left of the second annulus center. Closed screens confine the whole first core;
the second actual polygon therefore supplies a seed-avoiding witness. -/
theorem screenedAnnulusPair_probability_le_local_product_of_rightSeparation
    (V U₁ U₂ : Finset (ℤ × ℤ)) (hU₁ : U₁ ⊆ V) (hU₂ : U₂ ⊆ V)
    (θ : Parameters) (z₁ z₂ : ℤ × ℤ) (n₁ n₂ : ℕ)
    (hleft : ∀ v ∈ U₁, v.1 ≤ z₂.1) :
    (measure (squareLattice.induce (V : Set (ℤ × ℤ))) θ (BoundaryCondition.free ∅)
      (screenedAnnulusPairEvent V U₁ U₂ z₁ z₂ n₁ n₂)).toReal ≤
    finiteBoundaryEventProbability U₁ θ (frozenBoundaryCondition U₁ 0)
      (fun ω => ω ∈ annulusCircuitEvent U₁ z₁ n₁) *
    finiteBoundaryEventProbability U₂ θ (frozenBoundaryCondition U₂ 0)
      (fun ω => ω ∈ annulusCircuitEvent U₂ z₂ n₂) := by
  classical
  let G := squareLattice.induce (V : Set (ℤ × ℤ))
  let W₁ := finiteVertexRegion U₁ V
  let W₂ := finiteVertexRegion U₂ V
  let S := (vertexBoxRegion V z₁ (2*n₁)).toFinset
  let E₁ := finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z₁ n₁)
  let E₂ := finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z₂ n₂)
  have hrooted : ∀ B : Configuration G,
      B ∈ E₁ ↔ inducedConfigurationErasure (S : Set (V : Set (ℤ × ℤ))) B ∈ E₁ := by
    intro B
    simpa only [S,Set.coe_toFinset] using annulusEvent_inner_erasure_iff V z₁ n₁ B
  have h := free_seedSeparated_confined_product_of_rootedSupport G θ S W₁ W₂ E₁ E₂
    (finiteBoolEvent_isUpperSet V _ (annulusCircuitEvent_isUpperSet V z₁ n₁))
    (finiteBoolEvent_isUpperSet V _ (annulusCircuitEvent_isUpperSet V z₂ n₂)) hrooted
  change _ ≤ inducedAnnulusProbability V W₁ θ z₁ n₁ *
    inducedAnnulusProbability V W₂ θ z₂ n₂ at h
  rw [inducedAnnulusProbability_eq_local U₁ V hU₁,
    inducedAnnulusProbability_eq_local U₂ V hU₂] at h
  refine (measureReal_mono ?_).trans h
  rintro A ⟨h₁,h₂,hs₁,hs₂⟩
  refine ⟨?_,shieldedAnnulus_of_dualCircuitScreen V W₁ z₁ n₁ A h₁ hs₁⟩
  apply seedAvoidingAnnulus_of_coreShield_and_rightExit V S W₁ W₂ z₂ n₂ A h₂
  · intro s hs v hc
    exact dualCircuitScreen_full_inner_shield V _ W₁ A hs₁ s (Set.mem_toFinset.mp hs) v hc
  · intro v hv
    exact hleft v.val hv
  · exact dualCircuitScreen_full_inner_shield V _ W₂ A hs₂

end
end PottsContinuity.RSW
