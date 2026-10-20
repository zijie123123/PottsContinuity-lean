module

public import PottsContinuity.Thm3.RSW.Lemma4BandBondGeometry

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- No original edge recorded in the closed middle band can be crossed by
an upper-band dual step. This includes the base-row endpoint case. -/
theorem lemma4MiddleReveal_excludes_upper_dualBond (n : ℕ) (c : LatticeBond)
    (hf : 2*(n:ℤ) ≤ (c.faceBase false).2)
    (ht : 2*(n:ℤ) ≤ (c.faceBase true).2) :
    latticeBondEdge c ∉ (lemma4MiddleReveal n).map (frozenEdgeEmbedding (box (56*n))) := by
  intro hm
  obtain ⟨e,he,heq⟩ := Finset.mem_map.mp hm
  have hs := lemma4MiddleReveal_image_endpoint n e he c.source (by
    rw [heq]
    change c.source ∈ s(c.source,c.target)
    exact (Sym2.mem_iff').mpr (Or.inl rfl))
  have ht' := lemma4MiddleReveal_image_endpoint n e he c.target (by
    rw [heq]
    change c.target ∈ s(c.source,c.target)
    exact (Sym2.mem_iff').mpr (Or.inr rfl))
  rw [abs_le] at hs ht'
  have hgeo := lemma4_upper_dualBond_endpoint_geometry n c hf ht
  omega

/-- The same exclusion for the original lower-band face convention. -/
theorem lemma4MiddleReveal_excludes_lower_dualBond (n : ℕ) (c : LatticeBond)
    (hf : (c.faceBase false).2 ≤ -2*(n:ℤ)-1)
    (ht : (c.faceBase true).2 ≤ -2*(n:ℤ)-1) :
    latticeBondEdge c ∉ (lemma4MiddleReveal n).map (frozenEdgeEmbedding (box (56*n))) := by
  intro hm
  obtain ⟨e,he,heq⟩ := Finset.mem_map.mp hm
  have hs := lemma4MiddleReveal_image_endpoint n e he c.source (by
    rw [heq]
    change c.source ∈ s(c.source,c.target)
    exact (Sym2.mem_iff').mpr (Or.inl rfl))
  have ht' := lemma4MiddleReveal_image_endpoint n e he c.target (by
    rw [heq]
    change c.target ∈ s(c.source,c.target)
    exact (Sym2.mem_iff').mpr (Or.inr rfl))
  rw [abs_le] at hs ht'
  have hgeo := lemma4_lower_dualBond_endpoint_geometry n c hf ht
  omega

end
end PottsContinuity.RSW
