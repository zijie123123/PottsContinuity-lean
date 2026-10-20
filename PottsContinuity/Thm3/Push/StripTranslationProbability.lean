module

public import PottsContinuity.Thm3.Push.StripTranslationWindowComparison

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory Filter Topology
noncomputable section

/-- Opposite horizontal translations restore the full strip state. -/
theorem stripTranslation_neg_cancel (n : ℕ) (a : ℤ) (ω : RSW.StripConfiguration n) :
    stripTranslation n a (stripTranslation n (-a) ω) = ω := by
  funext e
  change ω ((stripTranslationIso n (-a)).mapEdgeSet ((stripTranslationIso n a).mapEdgeSet e)) = ω e
  congr 1
  apply Subtype.ext
  change Sym2.map (stripTranslationIso n (-a)) (Sym2.map (stripTranslationIso n a) e.val) = e.val
  rw [Sym2.map_map]
  have hf : (fun w => stripTranslationIso n (-a) (stripTranslationIso n a w)) = id := by
    funext w
    apply Subtype.ext
    change (w.val.1+a+(-a),w.val.2) = w.val
    simp only [add_neg_cancel_right,Prod.eta]
  change Sym2.map (fun w => stripTranslationIso n (-a) (stripTranslationIso n a w)) e.val = e.val
  rw [hf,Sym2.map_id]
  rfl

/-- Translated larger-window comparison passes to increasing clopen strip
events with no finite-window symmetry assumption. -/
theorem strip_limit_clopen_le_translation (θ : Parameters) (n : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ)
    (a : ℤ) (E : Set (RSW.StripConfiguration n)) (hE : IsClopen E) (hEu : IsUpperSet E) :
    μ.real E ≤ μ.real ((stripTranslation n a) ⁻¹' E) := by
  have h₁ := RSW.stripWindowEventProbability_tendsto θ n μ hμ E hE
  have h₂ := RSW.stripWindowEventProbability_tendsto θ n μ hμ
    ((stripTranslation n a) ⁻¹' E) (hE.preimage (stripTranslation_continuous n a))
  apply le_of_tendsto_of_tendsto h₁ (h₂.comp (tendsto_add_atTop_nat a.natAbs))
  apply Eventually.of_forall
  intro m
  apply stripWindowEventProbability_le_translation θ n m (m+a.natAbs) a _ E hEu
  rw [Nat.cast_add,Int.natCast_natAbs]
  omega

/-- The actual top-only strip limit is invariant under every integer
horizontal translation on increasing clopen events. -/
theorem strip_limit_clopen_translation (θ : Parameters) (n : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ)
    (a : ℤ) (E : Set (RSW.StripConfiguration n)) (hE : IsClopen E) (hEu : IsUpperSet E) :
    μ.real E = μ.real ((stripTranslation n a) ⁻¹' E) := by
  apply le_antisymm (strip_limit_clopen_le_translation θ n μ hμ a E hE hEu)
  have hpreu : IsUpperSet ((stripTranslation n a) ⁻¹' E) := by
    intro ω η h hω
    exact hEu (stripTranslation_monotone n a h) hω
  have h := strip_limit_clopen_le_translation θ n μ hμ (-a)
    ((stripTranslation n a) ⁻¹' E) (hE.preimage (stripTranslation_continuous n a)) hpreu
  have hcancel : (stripTranslation n (-a)) ⁻¹' ((stripTranslation n a) ⁻¹' E) = E := by
    ext ω
    change stripTranslation n a (stripTranslation n (-a) ω) ∈ E ↔ ω ∈ E
    rw [stripTranslation_neg_cancel]
  rw [hcancel] at h
  exact h

end
end PottsContinuity.Push
