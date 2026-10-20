-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/JordanParametrization.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.WindingCircle
public import PottsContinuity.FKC.SLEWrap.Geometry.ComplexJordanExtension

/-!
# A plane homeomorphism matching a simple closed path's parameters

Every continuous closed complex path that is injective before its endpoint is
obtained from the standard circle by a self-homeomorphism of the whole plane,
with the same parameter at every point. The boundary homeomorphism is proved
from the two loop parametrizations and then extended by Jordan–Schoenflies.
This asserts no orientation or winding-number value for the homeomorphism.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set OAI.SLEExactGauge
open scoped unitInterval

/-- The standard circle has no repeated point before its closing endpoint. -/
theorem standardCircleLoop_injOn :
    InjOn standardCircleLoop (Ico (0 : I) 1) := by
  intro s hs t ht h
  have hexp : Circle.exp (2 * Real.pi * s) = Circle.exp (2 * Real.pi * t) :=
    Subtype.ext h
  have hs' : 2 * Real.pi * (s : ℝ) ∈ Ico 0 (2 * Real.pi) := by
    constructor
    · exact mul_nonneg (by positivity) s.property.1
    · nlinarith [Real.pi_pos, show (s : ℝ) < 1 from hs.2]
  have ht' : 2 * Real.pi * (t : ℝ) ∈ Ico 0 (2 * Real.pi) := by
    constructor
    · exact mul_nonneg (by positivity) t.property.1
    · nlinarith [Real.pi_pos, show (t : ℝ) < 1 from ht.2]
  have he := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by linarith) hs' ht' hexp
  apply Subtype.ext
  exact mul_left_cancel₀ (by positivity : 2 * Real.pi ≠ 0) he

/-- A simple closed path gives the same loop in Schoenflies' real parameter convention. -/
theorem isLoop_complexCoordinates_extend {a : ℂ} (γ : Path a a)
    (hγ : InjOn γ (Ico (0 : I) 1)) :
    Schoenflies.IsLoop (complexPlaneCoordinates ∘ γ.extend) := by
  refine ⟨(complexPlaneCoordinates.continuous.comp γ.continuous_extend).continuousOn,
    ?_, ?_⟩
  · simp only [Function.comp_apply, Path.extend_zero, Path.extend_one]
  · intro s hs t ht h
    have he := complexPlaneCoordinates.injective h
    let s' : I := ⟨s, hs.1, hs.2.le⟩
    let t' : I := ⟨t, ht.1, ht.2.le⟩
    have hs' : s' ∈ Ico (0 : I) 1 := ⟨hs.1, hs.2⟩
    have ht' : t' ∈ Ico (0 : I) 1 := ⟨ht.1, ht.2⟩
    have hst : γ s' = γ t' := by
      simpa only [← γ.extend_extends' s', ← γ.extend_extends' t'] using he
    exact congrArg Subtype.val (hγ hs' ht' hst)

/-- Jordan–Schoenflies supplies a whole-plane homeomorphism matching every parameter
of the original simple closed path with the standard circle's parameter. -/
theorem exists_planeHomeomorph_standardCircleLoop {a : ℂ} (γ : Path a a)
    (hγ : InjOn γ (Ico (0 : I) 1)) :
    ∃ H : ℂ ≃ₜ ℂ, ∀ t : I, H (standardCircleLoop t) = γ t := by
  let f := complexPlaneCoordinates ∘ standardCircleLoop.extend
  let g := complexPlaneCoordinates ∘ γ.extend
  have hf : Schoenflies.IsLoop f :=
    isLoop_complexCoordinates_extend standardCircleLoop standardCircleLoop_injOn
  have hg : Schoenflies.IsLoop g := isLoop_complexCoordinates_extend γ hγ
  obtain ⟨e, he⟩ := hf.exists_homeomorph hg
  obtain ⟨F, hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    (show Schoenflies.IsJordanCurve (f '' Icc 0 1) from ⟨f, hf, rfl⟩)
    (show Schoenflies.IsJordanCurve (g '' Icc 0 1) from ⟨g, hg, rfl⟩) e
  refine ⟨(complexPlaneCoordinates.trans F).trans complexPlaneCoordinates.symm, ?_⟩
  intro t
  have hmatch := (hF ⟨f t, mem_image_of_mem f t.2⟩).trans (he t t.2)
  apply complexPlaneCoordinates.injective
  simpa only [Homeomorph.trans_apply, Homeomorph.apply_symm_apply,
    f, g, Function.comp_apply, Path.extend_extends'] using hmatch

end PottsContinuity.FKC
