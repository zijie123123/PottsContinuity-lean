module

public import PottsContinuity.Thm3.RSW.FiniteDualRectangleErasure
public import PottsContinuity.Thm3.RSW.Lemma4SideBandProduct
public import PottsContinuity.Thm3.RSW.Lemma4BandBondGeometry

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- Each source dual crossing reads only bonds in its literal upper/lower
side. Erasure preserves the full sampled crossing, with the face offset intact. -/
theorem lemma4DualBandEvent_side_erasure_iff (n : ℕ) (i : Fin 2)
    (A : Configuration (lemma4AmbientGraph n)) :
    A ∈ lemma4DualBandEvent n i ↔
      inducedConfigurationErasure (lemma4SideVertices n (lemma4SideSign i)) A ∈
        lemma4DualBandEvent n i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · apply finiteClosedDualHorizontalRectangle_erasure_iff
    intro c hf ht e heq v hv
    have hgeo := lemma4_upper_dualBond_endpoint_geometry n c hf.2.2.1 ht.2.2.1
    have hm : v.val ∈ (frozenEdgeEmbedding (box (56*n)) e).val := Sym2.mem_map.mpr ⟨v,hv,rfl⟩
    rw [heq] at hm
    change v.val ∈ s(c.source,c.target) at hm
    change 2*(n:ℤ) ≤ (1:ℤ)*v.val.2
    simp only [one_mul]
    rcases (Sym2.mem_iff').mp hm with h | h
    · rw [h]
      exact hgeo.1
    · rw [h]
      exact hgeo.2.1
  · apply finiteClosedDualHorizontalRectangle_erasure_iff
    intro c hf ht e heq v hv
    have hgeo := lemma4_lower_dualBond_endpoint_geometry n c hf.2.2.2 ht.2.2.2
    have hm : v.val ∈ (frozenEdgeEmbedding (box (56*n)) e).val := Sym2.mem_map.mpr ⟨v,hv,rfl⟩
    rw [heq] at hm
    change v.val ∈ s(c.source,c.target) at hm
    change 2*(n:ℤ) ≤ (-1:ℤ)*v.val.2
    simp only [neg_one_mul]
    rcases (Sym2.mem_iff').mp hm with h | h
    · rw [h]
      omega
    · rw [h]
      omega

end
end PottsContinuity.RSW
