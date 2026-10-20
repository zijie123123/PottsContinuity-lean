-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/JordanBridge.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Schoenflies.Curve
public import TauCeti.Topology.JordanCurve.Path

/-!
# Compatibility of the two Jordan-curve predicates

Schoenflies presents a curve by a continuous loop on the real unit interval,
injective before its endpoint. TauCeti presents the same notion as a set
homeomorphic to the circle. The forward bridge restricts the given loop to a
closed `Path` and proves TauCeti's exact endpoint-repetition criterion.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set

/-- An interval-parametrized Schoenflies Jordan curve is a TauCeti Jordan curve. -/
theorem isJordanCurve_of_schoenflies {C : Set Schoenflies.Plane}
    (hC : Schoenflies.IsJordanCurve C) : TauCeti.IsJordanCurve C := by
  obtain ⟨f, hf, hfC⟩ := hC
  let γ : Path (f 0) (f 0) :=
    { toFun := fun t => f t
      continuous_toFun := hf.continuousOn.domRestrict
      source' := rfl
      target' := hf.closes.symm }
  have hrange : range γ = C := by
    rw [← hfC]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  rw [← hrange]
  apply TauCeti.isJordanCurve_range_of_eq_or_eq_endpoints γ
  intro s t hst
  change f s = f t at hst
  have hlt {u : unitInterval} (hu : u ≠ 1) : (u : ℝ) < 1 :=
    lt_of_le_of_ne u.property.2 (fun he => hu (Subtype.ext he))
  by_cases hs : s = 1
  · subst s
    by_cases ht : t = 1
    · exact Or.inl ht.symm
    · have ht0 : t = 0 := by
        apply Subtype.ext
        exact hf.injOn ⟨t.property.1, hlt ht⟩ ⟨le_rfl, zero_lt_one⟩
          (hst.symm.trans hf.closes.symm)
      exact Or.inr (Or.inr ⟨rfl, ht0⟩)
  · by_cases ht : t = 1
    · subst t
      have hs0 : s = 0 := by
        apply Subtype.ext
        exact hf.injOn ⟨s.property.1, hlt hs⟩ ⟨le_rfl, zero_lt_one⟩
          (hst.trans hf.closes.symm)
      exact Or.inr (Or.inl ⟨hs0, rfl⟩)
    · exact Or.inl (Subtype.ext (hf.injOn ⟨s.property.1, hlt hs⟩
        ⟨t.property.1, hlt ht⟩ hst))

end PottsContinuity.FKC
