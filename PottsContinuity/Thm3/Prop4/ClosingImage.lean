module

public import PottsContinuity.Thm3.Prop4.ClosedCutEnergy
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Finite-energy closing surgery on arbitrary events

Unlike an edge-stable conditional event, the source connection event can be
destroyed by closing the cut. Its image still has a uniform probability
lower bound. The saturation argument retains every possible preimage and
requires no independence or stability assumption on the original event.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance closingImageEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance closingImageEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- Closing a prescribed set of original edges costs at most (1-p)^|F|,
for every finite FK event, even if the event itself is destroyed by the surgery. -/
theorem finite_closing_image_energy (θ : Parameters) (ξ : BoundaryCondition V)
    (F : Finset G.edgeSet) (B : Set (Configuration G)) :
    (1-edgeParameter θ)^F.card*(measure G θ ξ B).toReal ≤
      (measure G θ ξ ((fun A => A \ F) '' B)).toReal := by
  classical
  let S : Set (Configuration G) := {A | ∃ C ∈ B, A \ F = C \ F}
  have hstable : ∀ e ∈ F, ∀ A, A ∈ S ↔ A.erase e ∈ S := by
    intro e he A
    have he' : e ∉ A \ F := by simp [he]
    have hdiff : A.erase e \ F = A \ F := by
      rw [Finset.erase_sdiff_comm, Finset.erase_eq_of_notMem he']
    change (∃ C ∈ B, A \ F = C \ F) ↔ (∃ C ∈ B, A.erase e \ F = C \ F)
    rw [hdiff]
  have hsubset : B ⊆ S := fun A hA => ⟨A,hA,rfl⟩
  have hset : S ∩ {A | Disjoint A F} = (fun A => A \ F) '' B := by
    ext A
    constructor
    · rintro ⟨⟨C,hC,hEq⟩,hdisj⟩
      refine ⟨C,hC,?_⟩
      rw [Finset.sdiff_eq_self_iff_disjoint.mpr hdisj] at hEq
      exact hEq.symm
    · rintro ⟨C,hC,rfl⟩
      refine ⟨⟨C,hC,?_⟩,?_⟩
      · ext e
        simp
      · apply Finset.disjoint_left.mpr
        intro e he hf
        exact (Finset.mem_sdiff.mp he).2 hf
  calc
    _ ≤ (1-edgeParameter θ)^F.card*(measure G θ ξ S).toReal :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
        (pow_nonneg (one_sub_edgeParameter_pos θ).le _)
    _ ≤ (measure G θ ξ (S ∩ {A | Disjoint A F})).toReal :=
      finite_closed_cut_energy G θ ξ F S hstable
    _ = _ := by rw [hset]

end

end PottsContinuity.Thm3.Prop4
