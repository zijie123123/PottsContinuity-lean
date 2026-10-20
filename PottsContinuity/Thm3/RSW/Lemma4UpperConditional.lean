module

public import PottsContinuity.PD.FK.IsolatedExtension
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Data.Finset.Sum
public import PottsContinuity.PD.FK.ProbabilityProduct
public import Mathlib.Tactic
public import PottsContinuity.Thm3.RSW.InducedConfiguration
public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import PottsContinuity.Thm3.RSW.InducedComparison
public import PottsContinuity.Thm3.RSW.StoppingUpper
public import PottsContinuity.Thm3.RSW.InducedAnnulusLaw
public import PottsContinuity.Thm3.RSW.AnnulusTranslationLaw
public import PottsContinuity.Foundations.BoxBoundary

/-!
# Lemma-4 upper product with the exact source centers and probability a_n²

All probability steps are proved. The remaining premises are the actual
complete stopping record, its two disjoint random interiors inside overlapping
reference boxes, the induced free boundary, and the retained sampled polygons.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK Exploration
noncomputable section
local instance lemma4UpperEdgeDecidableEq
    (V : Finset (ℤ × ℤ)) : DecidableEq (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet :=
  Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- Radius-8n local boxes at centers of coordinate modulus at most 5n are
contained in the genuine ambient box of radius 56n. -/
theorem lemma4_reference_subset_ambient (n : ℕ) (c : ℤ × ℤ)
    (hc : |c.1| ≤ 5*(n:ℤ) ∧ |c.2| ≤ 5*(n:ℤ)) :
    latticeBox c (8*n) ⊆ box (56*n) := by
  intro v hv
  rw [mem_latticeBox] at hv
  rw [Foundations.mem_box_iff_interval]
  rcases hc with ⟨hc₁,hc₂⟩
  rw [abs_le] at hc₁ hc₂
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hv ⊢
  omega

end
end PottsContinuity.RSW
