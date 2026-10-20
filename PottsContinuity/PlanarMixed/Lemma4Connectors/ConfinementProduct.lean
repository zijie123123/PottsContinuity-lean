module

public import PottsContinuity.Thm3.RSW.Lemma4ScreenUpper

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK RSW MeasureTheory
noncomputable section

/-- Every cluster meeting the entire core stays in the prescribed region. -/
def fullCoreConfined (V : Finset (ℤ × ℤ)) (W : Set (V : Set (ℤ × ℤ)))
    (z : ℤ × ℤ) (n : ℕ) :
    Set (Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) :=
  {A | ∀ v ∈ vertexBoxRegion V z (2*n), ∀ w,
    ActualConnected (squareLattice.induce (V : Set (ℤ × ℤ))) A v w → w ∈ W}

/-- The repaired upper-product event records the two annuli and full cores. -/
def confinedAnnulusPairEvent (V U₁ U₂ : Finset (ℤ × ℤ))
    (z₁ z₂ : ℤ × ℤ) (n₁ n₂ : ℕ) :
    Set (Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) :=
  {A | A ∈ finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z₁ n₁) ∧
    A ∈ finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z₂ n₂) ∧
    A ∈ fullCoreConfined V (finiteVertexRegion U₁ V) z₁ n₁ ∧
    A ∈ fullCoreConfined V (finiteVertexRegion U₂ V) z₂ n₂}

/-- Root-seed conditioning handles overlapping boxes without extracting
additional circuits. The first box only needs to lie left of the second center. -/
theorem confinedAnnulusPair_probability_le_local_product
    (V U₁ U₂ : Finset (ℤ × ℤ)) (hU₁ : U₁ ⊆ V) (hU₂ : U₂ ⊆ V)
    (θ : Parameters) (z₁ z₂ : ℤ × ℤ) (n₁ n₂ : ℕ)
    (hleft : ∀ v ∈ U₁, v.1 ≤ z₂.1) :
    (measure (squareLattice.induce (V : Set (ℤ × ℤ))) θ (BoundaryCondition.free ∅)
      (confinedAnnulusPairEvent V U₁ U₂ z₁ z₂ n₁ n₂)).toReal ≤
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
  refine ⟨?_,shieldedAnnulus_of_full_inner_shield V W₁ z₁ n₁ A h₁ hs₁⟩
  apply seedAvoidingAnnulus_of_coreShield_and_rightExit V S W₁ W₂ z₂ n₂ A h₂
  · intro s hs v hc
    exact hs₁ s (Set.mem_toFinset.mp hs) v hc
  · intro v hv
    exact hleft v.val hv
  · exact hs₂

/-- The source centers give precisely the unchanged square upper bound. -/
theorem lemma4_confined_annulus_pair_probability_le_square (θ : Parameters) (n : ℕ) :
    (measure (squareLattice.induce (box (56*n) : Set (ℤ × ℤ))) θ (BoundaryCondition.free ∅)
      (confinedAnnulusPairEvent (box (56*n))
        (latticeBox (-5*(n:ℤ),0) (8*n)) (latticeBox (5*(n:ℤ),0) (8*n))
        (-5*(n:ℤ),0) (5*(n:ℤ),0) n n)).toReal ≤ (annulusProbability θ 8 n)^2 := by
  have hU₁ := lemma4_reference_subset_ambient n (-5*(n:ℤ),0) (by
    constructor
    · change |(-5:ℤ)*(n:ℤ)| ≤ 5*(n:ℤ)
      rw [abs_of_nonpos (by omega)]
      omega
    · change |(0:ℤ)| ≤ 5*(n:ℤ)
      rw [abs_zero]
      omega)
  have hU₂ := lemma4_reference_subset_ambient n (5*(n:ℤ),0) (by
    constructor
    · change |(5:ℤ)*(n:ℤ)| ≤ 5*(n:ℤ)
      rw [abs_of_nonneg (by omega)]
    · change |(0:ℤ)| ≤ 5*(n:ℤ)
      rw [abs_zero]
      omega)
  have hleft : ∀ v ∈ latticeBox (-5*(n:ℤ),0) (8*n), v.1 ≤ (5*(n:ℤ),0).1 := by
    intro v hv
    rw [mem_latticeBox] at hv
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hv
    change v.1 ≤ 5*(n:ℤ)
    omega
  have h := confinedAnnulusPair_probability_le_local_product
    (box (56*n)) (latticeBox (-5*(n:ℤ),0) (8*n)) (latticeBox (5*(n:ℤ),0) (8*n))
    hU₁ hU₂ θ (-5*(n:ℤ),0) (5*(n:ℤ),0) n n hleft
  rw [translated_box_annulus_probability_eq,translated_box_annulus_probability_eq] at h
  rw [pow_two]
  exact h

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
