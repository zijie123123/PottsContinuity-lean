module

public import PottsContinuity.Thm3.RSW.AnnulusPositivity
public import PottsContinuity.Thm3.RSW.SampledAnnulus

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section

/-- A literal translated all-open square supplies the genuine annulus circuit
inside any ambient domain containing the translated reference box. -/
theorem all_true_mem_annulusCircuitEvent_translated (V : Finset LatticeVertex)
    (z : LatticeVertex) (n : ℕ) (hn : 1 ≤ n)
    (hwindow : ∀ v ∈ box (8*n), (v.1+z.1,v.2+z.2) ∈ V) :
    (fun _ => true) ∈ annulusCircuitEvent V z n := by
  apply translatedAnnulusEvent_subset_actualAnnulus V n z hwindow
  simp only [translatedAnnulusEvent,Set.mem_ofPred_eq]
  exact all_true_mem_annulusCircuitEvent 8 n (by norm_num) hn

/-- Two genuine translated annuli have strictly positive probability under
any finite FK boundary partition, with no uniform-scale conclusion assumed. -/
theorem finite_annulus_pair_pos_of_reference_containment
    (V : Finset LatticeVertex) (θ : Parameters) (ξ : BoundaryCondition (V : Set LatticeVertex))
    (z₁ z₂ : LatticeVertex) (n : ℕ) (hn : 1 ≤ n)
    (h₁ : ∀ v ∈ box (8*n), (v.1+z₁.1,v.2+z₁.2) ∈ V)
    (h₂ : ∀ v ∈ box (8*n), (v.1+z₂.1,v.2+z₂.2) ∈ V) :
    0 < finiteBoundaryEventProbability V θ ξ
      (fun ω => ω ∈ annulusCircuitEvent V z₁ n ∧ ω ∈ annulusCircuitEvent V z₂ n) := by
  apply (finiteBoundaryEventProbability_pos_iff V θ ξ _).mpr
  exact ⟨fun _ => true,all_true_mem_annulusCircuitEvent_translated V z₁ n hn h₁,
    all_true_mem_annulusCircuitEvent_translated V z₂ n hn h₂⟩

end
end PottsContinuity.RSW
