module

public import PottsContinuity.Thm3.Push.StripMapSymmetry
public import PottsContinuity.Thm3.RSW.StripHorizontalTranslation
public import PottsContinuity.Thm3.RSW.StripHorizontalReflection

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory
noncomputable section

/-- The forward state relabelling `RSW.stripHorizontalTranslationConfiguration` is the
opposite original-bond pullback. -/
theorem stripHorizontalTranslationConfiguration_eq_pullback (n : ℕ) (c : ℤ)
    (ω : RSW.StripConfiguration n) :
    RSW.stripHorizontalTranslationConfiguration n c ω = stripTranslation n (-c) ω := by
  funext e
  have hc : (RSW.stripHorizontalTranslationIso n c).mapEdgeSet
      ((RSW.stripHorizontalTranslationIso n (-c)).mapEdgeSet e) = e := by
    simpa only [neg_neg] using RSW.stripHorizontalTranslation_edge_neg_cancel n (-c) e
  calc
    _ = RSW.stripHorizontalTranslationConfiguration n c ω
        ((RSW.stripHorizontalTranslationIso n c).mapEdgeSet
          ((RSW.stripHorizontalTranslationIso n (-c)).mapEdgeSet e)) := by rw [hc]
    _ = ω ((RSW.stripHorizontalTranslationIso n (-c)).mapEdgeSet e) :=
      RSW.stripHorizontalTranslationConfiguration_edge n c ω _
    _ = _ := rfl

/-- The affine reflection `RSW.stripHorizontalReflectionConfiguration` is the composition of
actual strip translation
and origin reflection on the entire sampled bond carrier. -/
theorem stripHorizontalReflectionConfiguration_eq_pullback (n : ℕ) (c : ℤ)
    (ω : RSW.StripConfiguration n) :
    RSW.stripHorizontalReflectionConfiguration n c ω =
      stripHorizontalReflection n (stripTranslation n c ω) := by
  funext e
  have hedge : (RSW.stripHorizontalReflectionIso n c).mapEdgeSet e =
      (stripTranslationIso n c).mapEdgeSet ((stripHorizontalReflectionIso n).mapEdgeSet e) := by
    apply Subtype.ext
    change Sym2.map (RSW.stripHorizontalReflectionIso n c) e.val =
      Sym2.map (stripTranslationIso n c) (Sym2.map (stripHorizontalReflectionIso n) e.val)
    rw [Sym2.map_map]
    have hf : (RSW.stripHorizontalReflectionIso n c : RSW.stripVertices n → RSW.stripVertices n) =
        (stripTranslationIso n c) ∘ (stripHorizontalReflectionIso n) := by
      funext u
      apply Subtype.ext
      change (c-u.val.1,u.val.2) = (-u.val.1+c,u.val.2)
      congr 1
      omega
    rw [hf]
  change RSW.stripHorizontalReflectionConfiguration n c ω e =
    ω ((stripTranslationIso n c).mapEdgeSet ((stripHorizontalReflectionIso n).mapEdgeSet e))
  rw [← hedge]
  calc
    _ = RSW.stripHorizontalReflectionConfiguration n c ω
      ((RSW.stripHorizontalReflectionIso n c).mapEdgeSet
        ((RSW.stripHorizontalReflectionIso n c).mapEdgeSet e)) := by
          rw [RSW.stripHorizontalReflection_edge_involutive n c e]
    _ = _ := RSW.stripHorizontalReflectionConfiguration_edge n c ω _

/-- Whole-law translation invariance of the top-wired strip limit, in the form used in `RSW`. -/
theorem strip_limit_map_RSW_translation (θ : Parameters) (n : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ) (c : ℤ) :
    μ.map (RSW.stripHorizontalTranslationConfiguration n c) = μ := by
  have hf : (RSW.stripHorizontalTranslationConfiguration n c :
      RSW.StripConfiguration n → RSW.StripConfiguration n) = stripTranslation n (-c) :=
    funext (stripHorizontalTranslationConfiguration_eq_pullback n c)
  rw [hf]
  exact strip_limit_map_translation θ n μ hμ (-c)

/-- Whole-law affine reflection invariance of the top-wired strip limit, in the form used in
`RSW`, including reflection about half-integer vertical axes. -/
theorem strip_limit_map_RSW_reflection (θ : Parameters) (n : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ) (c : ℤ) :
    μ.map (RSW.stripHorizontalReflectionConfiguration n c) = μ := by
  have hf : (RSW.stripHorizontalReflectionConfiguration n c :
      RSW.StripConfiguration n → RSW.StripConfiguration n) =
        (stripHorizontalReflection n) ∘ (stripTranslation n c) :=
    funext (stripHorizontalReflectionConfiguration_eq_pullback n c)
  rw [hf,← Measure.map_map (stripHorizontalReflection_continuous n).measurable
    (stripTranslation_continuous n c).measurable,strip_limit_map_translation θ n μ hμ c]
  exact strip_limit_map_reflection θ n μ hμ

end
end PottsContinuity.Push
