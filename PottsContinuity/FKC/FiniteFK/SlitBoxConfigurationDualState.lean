-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxConfigurationDualState.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxConfigurationExtension
public import PottsContinuity.FKC.Medial.WholePlanePairing

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

/-- The actual crossed primal bond belongs to the slit-box edge image exactly
when it has an actual slit-box preimage. -/
theorem slitScreenPrimalBondInSlit_iff_edgeImage
    (n : ℕ) (b : LatticeBond) :
    slitScreenPrimalBondInSlit n b ↔
      latticeBondEdge b ∈ Set.range (slitBoxEdgeEmbedding n) := by
  constructor
  · rintro ⟨u, v, hu, hv, hedge⟩
    let e : (slitBoxGraph n).edgeSet := ⟨s(u, v), hedge⟩
    refine ⟨e, ?_⟩
    apply Subtype.ext
    change Sym2.map Subtype.val (s(u, v)) = b.toSym2
    rw [Sym2.map_mk]
    simp [hu, hv, LatticeBond.toSym2]
  · rintro ⟨e, he⟩
    have hsym : Sym2.map Subtype.val e.val = b.toSym2 :=
      congrArg Subtype.val he
    let u : SlitBoxVertex n := (Quot.out e.val).1
    let v : SlitBoxVertex n := (Quot.out e.val).2
    have hrepr : s(u, v) = e.val := by
      change Quot.mk _ (u, v) = e.val
      exact Quot.out_eq e.val
    have hpair : s(u.val, v.val) = s(b.source, b.target) := by
      calc
        s(u.val, v.val) = Sym2.map Subtype.val (s(u, v)) := by rw [Sym2.map_mk]
        _ = Sym2.map Subtype.val e.val := by rw [hrepr]
        _ = b.toSym2 := hsym
        _ = s(b.source, b.target) := rfl
    have hedge : s(u, v) ∈ (slitBoxGraph n).edgeSet := hrepr.symm ▸ e.property
    rcases Sym2.eq_iff.mp hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact ⟨u, v, hu, hv, hedge⟩
    · exact ⟨v, u, hv, hu, by simpa only [Sym2.eq_swap] using hedge⟩

/-- The corresponding closed-state statement at an actual slit-box edge. -/
theorem slitBoxConfigurationBondState_false_iff
    (n : ℕ) (A : Configuration (slitBoxGraph n)) (b : LatticeBond)
    (e : (slitBoxGraph n).edgeSet)
    (he : latticeBondEdge b = slitBoxEdgeEmbedding n e) :
    latticeConfigurationBondState (slitBoxConfigurationExtension n A) b = false ↔
      e ∉ A := by
  rw [latticeConfigurationBondState, he]
  rw [slitBoxConfigurationExtension_at]
  simp

end
end PottsContinuity.FKC.FiniteFK

