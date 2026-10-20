module

public import PottsContinuity.Thm3.RSW.Lemma4DualBands

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.RCInfinite

/-- A primal bond crossed by a dual edge wholly above the middle band has
both endpoints above its base and at least one strictly above it. -/
theorem lemma4_upper_dualBond_endpoint_geometry (n : ℕ) (c : LatticeBond)
    (hf : 2*(n:ℤ) ≤ (c.faceBase false).2)
    (ht : 2*(n:ℤ) ≤ (c.faceBase true).2) :
    2*(n:ℤ) ≤ c.source.2 ∧ 2*(n:ℤ) ≤ c.target.2 ∧
      (2*(n:ℤ) < c.source.2 ∨ 2*(n:ℤ) < c.target.2) := by
  rcases c with ⟨⟨x,y⟩,ax⟩
  cases ax <;> simp only [LatticeBond.faceBase,LatticeBond.source,LatticeBond.target] at * <;> omega

/-- The corresponding lower band keeps both primal endpoints below its
base and at least one strictly below, with the original dual face offset. -/
theorem lemma4_lower_dualBond_endpoint_geometry (n : ℕ) (c : LatticeBond)
    (hf : (c.faceBase false).2 ≤ -2*(n:ℤ)-1)
    (ht : (c.faceBase true).2 ≤ -2*(n:ℤ)-1) :
    c.source.2 ≤ -2*(n:ℤ) ∧ c.target.2 ≤ -2*(n:ℤ) ∧
      (c.source.2 < -2*(n:ℤ) ∨ c.target.2 < -2*(n:ℤ)) := by
  rcases c with ⟨⟨x,y⟩,ax⟩
  cases ax <;> simp only [LatticeBond.faceBase,LatticeBond.source,LatticeBond.target] at * <;> omega

/-- Every actual endpoint of a recorded original edge lies in the closed
middle band after its literal inclusion into the whole lattice. -/
theorem lemma4MiddleReveal_image_endpoint (n : ℕ) (e : (lemma4AmbientGraph n).edgeSet)
    (he : e ∈ lemma4MiddleReveal n) (v : LatticeVertex)
    (hv : v ∈ (frozenEdgeEmbedding (box (56*n)) e).val) : |v.2| ≤ 2*(n:ℤ) := by
  change v ∈ Sym2.map Subtype.val e.val at hv
  obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
  exact lemma4MiddleReveal_endpoint n he hw

end PottsContinuity.RSW
