module

public import PottsContinuity.Thm3.RSW.AnnulusShielding

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section
local instance annulusRecordedSupportEdgeEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

/-- Recording all bonds inside the outer box suffices to determine the
original annulus event, without choosing or modifying its polygon witness. -/
theorem annulus_event_inter_recorded_outerBonds_iff
    (V : Finset (ℤ × ℤ)) (z : ℤ × ℤ) (n : ℕ)
    (R A : Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    (hR : ∀ e : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet,
      (∀ v ∈ e.val, v ∈ vertexBoxRegion V z (2*n)) → e ∈ R) :
    A ∈ finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n) ↔
      A ∩ R ∈ finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n) := by
  have hupper := finiteBoolEvent_isUpperSet V _ (annulusCircuitEvent_isUpperSet V z n)
  constructor
  · intro hA
    apply hupper (b := A ∩ R) ?_ (annulus_mem_inner_erasure V z n A hA)
    intro e he
    obtain ⟨heA,heV⟩ := (mem_inducedConfigurationErasure _ A e).mp he
    exact Finset.mem_inter.mpr ⟨heA,hR e heV⟩
  · exact fun hA => hupper Finset.inter_subset_left hA

/-- Equality of the recorded original states gives equality of the genuine
annulus event whenever all outer-box bonds were recorded. -/
theorem annulus_event_visible_in_recorded_outerBonds
    (V : Finset (ℤ × ℤ)) (z : ℤ × ℤ) (n : ℕ)
    (R : Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    (hR : ∀ e : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet,
      (∀ v ∈ e.val, v ∈ vertexBoxRegion V z (2*n)) → e ∈ R)
    (A A' : Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    (hstate : A ∩ R = A' ∩ R) :
    A ∈ finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n) ↔
      A' ∈ finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n) := by
  rw [annulus_event_inter_recorded_outerBonds_iff V z n R A hR,
    annulus_event_inter_recorded_outerBonds_iff V z n R A' hR,hstate]

end
end PottsContinuity.RSW
