-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/JordanChart.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.UpperHalfPlane
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Conformal coordinates for a marked Jordan domain

The domain carrier contains exactly a bounded Jordan domain and two distinct
boundary marks. Carathéodory's theorem supplies an upper-half-plane map; a real
translation normalizes its finite marked preimage to zero. These are existence
statements about conformal coordinates, not about SLE traces or their laws.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Bornology Complex Filter Function Set Topology UpperHalfPlane

/-- An arbitrary bounded Jordan domain with two distinct ordered boundary marks. -/
structure MarkedJordanDomain where
  domain : Set ℂ
  isJordanDomain : TauCeti.IsJordanDomain domain
  a : ℂ
  b : ℂ
  a_mem_frontier : a ∈ frontier domain
  b_mem_frontier : b ∈ frontier domain
  a_ne_b : a ≠ b

namespace MarkedJordanDomain

/-- Translation by a real number preserves every condition on the imaginary part. -/
private theorem bijOn_add_real (r : ℝ) (P : ℝ → Prop) :
    BijOn (fun z : ℂ => z + (r : ℂ)) {z | P z.im} {z | P z.im} := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    simpa using hz
  · intro z hz w hw h
    exact add_right_cancel h
  · intro z hz
    refine ⟨z - (r : ℂ), ?_, by simp⟩
    simpa using hz

/-- Real translation preserves escape to infinity within the closed half-plane. -/
private theorem tendsto_add_real_closedHalfPlane_infinity (r : ℝ) :
    Tendsto (fun z : ℂ => z + (r : ℂ))
      (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im})
      (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) := by
  have hi : Isometry (fun z : ℂ => z + (r : ℂ)) :=
    Isometry.of_dist_eq fun z w => dist_add_right z w (r : ℂ)
  exact hi.antilipschitzWith.tendsto_cobounded.inf
    (tendsto_principal_principal.mpr (bijOn_add_real r (0 ≤ ·)).mapsTo)

/-- A conformal coordinate with infinity at `b` and zero at `a`, including the
full Carathéodory boundary correspondence. No particular chart is selected. -/
theorem exists_upperHalfPlane_chart (D : MarkedJordanDomain) :
    ∃ f : ℂ → ℂ,
      ContinuousOn f {z : ℂ | 0 ≤ z.im} ∧
      DifferentiableOn ℂ f upperHalfPlaneSet ∧
      BijOn f upperHalfPlaneSet D.domain ∧
      BijOn f {z : ℂ | 0 ≤ z.im} (closure D.domain \ {D.b}) ∧
      BijOn f {z : ℂ | z.im = 0} (frontier D.domain \ {D.b}) ∧
      f 0 = D.a ∧
      Tendsto f (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 D.b) := by
  obtain ⟨g, hgc, hgd, hgH, hgcl, hgR, hgb⟩ :=
    TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier
      D.isJordanDomain.isOpen D.isJordanDomain.isConnected D.isJordanDomain.isBounded
      D.isJordanDomain.isJordanCurve_frontier D.b_mem_frontier
  obtain ⟨x, hxR, hxa⟩ := hgR.surjOn ⟨D.a_mem_frontier, D.a_ne_b⟩
  have hx : (x.re : ℂ) = x := Complex.ext (by simp) (by simpa using hxR.symm)
  have htcl := bijOn_add_real x.re (0 ≤ ·)
  have htH := bijOn_add_real x.re (0 < ·)
  have htR := bijOn_add_real x.re (· = 0)
  refine ⟨fun z => g (z + (x.re : ℂ)), ?_, ?_, hgH.comp htH, hgcl.comp htcl,
    hgR.comp htR, ?_, ?_⟩
  · exact hgc.comp (continuous_id.add continuous_const).continuousOn htcl.mapsTo
  · exact hgd.comp (differentiable_id.add_const _).differentiableOn htH.mapsTo
  · simpa [hx] using hxa
  · exact hgb.comp (tendsto_add_real_closedHalfPlane_infinity x.re)

end MarkedJordanDomain

end PottsContinuity.FKC
