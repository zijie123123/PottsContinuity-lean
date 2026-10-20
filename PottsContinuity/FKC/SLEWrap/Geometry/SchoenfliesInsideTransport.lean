-- Taken from the SLE development in https://github.com/openai/math (commit
-- fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, file `lean/OAI/Probability/SLE/Geometry/SchoenfliesInsideTransport.lean`):
-- module relocated and ported to the module system; the declarations kept are unchanged
-- (the declaration `plane_homeomorph_jordan`, not used here, is omitted).
module

public import PottsContinuity.FKC.SLEWrap.Geometry.ComplexJordanExtension

@[expose] public section

namespace OAI

/-! Plane homeomorphisms preserve the bounded complementary region.
This identifies the side selected by a relative Schoenflies extension. -/
noncomputable section
open Set

namespace SLEExactGauge

lemma plane_homeomorph_bounded_image (h : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    {S : Set Schoenflies.Plane} (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (h '' S) :=
  (hS.isCompact_closure.image h.continuous).isBounded.subset (image_mono subset_closure)

lemma plane_homeomorph_bounded_image_iff (h : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    (S : Set Schoenflies.Plane) : Bornology.IsBounded (h '' S) ↔ Bornology.IsBounded S := by
  refine ⟨fun hs => ?_,plane_homeomorph_bounded_image h⟩
  have hh := plane_homeomorph_bounded_image h.symm hs
  simpa only [image_image,h.symm_apply_apply,image_id'] using hh

theorem plane_homeomorph_inside (h : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    (C : Set Schoenflies.Plane) : h '' Schoenflies.inside C = Schoenflies.inside (h '' C) := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hxC : x ∈ Cᶜ := hx.1
    refine ⟨?_,?_⟩
    · rintro ⟨y,hy,he⟩
      exact hx.1 (h.injective he ▸ hy)
    have hh := h.image_connectedComponentIn hxC
    rw [h.image_compl] at hh
    rw [← hh]
    exact plane_homeomorph_bounded_image h hx.2
  · intro hz
    refine ⟨h.symm z,?_,h.apply_symm_apply z⟩
    have hxC : h.symm z ∉ C := by
      intro hc
      apply hz.1
      exact ⟨h.symm z,hc,h.apply_symm_apply z⟩
    refine ⟨hxC,?_⟩
    have hh := h.image_connectedComponentIn (s := Cᶜ) (x := h.symm z) hxC
    rw [h.image_compl,h.apply_symm_apply] at hh
    apply (plane_homeomorph_bounded_image_iff h _).mp
    rw [hh]
    exact hz.2

theorem separating_inside_eq_open
    {C U : Set Schoenflies.Plane} (hC : Schoenflies.IsSeparating C)
    (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (hbounded : Bornology.IsBounded U) (hfront : frontier U=C) :
    Schoenflies.inside C=U := by
  have hsub : U ⊆ Cᶜ := by
    intro z hz hzC
    have hh : z ∈ frontier U := hfront.symm ▸ hzC
    rw [hU.frontier_eq] at hh
    exact hh.2 hz
  obtain ⟨x,hx⟩ := hne
  have hcomp := Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint
    hU hconn hsub (by simp only [hfront,inter_compl_self]) hx
  have hxin : x ∈ Schoenflies.inside C := ⟨hsub hx,hcomp.symm ▸ hbounded⟩
  exact (hC.connectedComponentIn_eq_inside hxin).symm.trans hcomp

end SLEExactGauge

end

end OAI
