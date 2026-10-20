-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/MarkedHalfArcs.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.MarkedBoundary
public import PottsContinuity.FKC.Curves.WindingReparam
public import Schoenflies.MatchedArc

/-!
# The directed half-arcs do not depend on the marked CCW parametrization

The two half-images of each admissible simple loop are actual complementary
arcs. Their unordered uniqueness is topological; their directed uniqueness
uses continuous inverse parametrizations and the geometric winding sign.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set OAI.SLEExactGauge
open scoped unitInterval

private theorem loop_injOn_lower {f : ℝ → Schoenflies.Plane}
    (hf : Schoenflies.IsLoop f) : InjOn f (Icc (0 : ℝ) (1 / 2)) := by
  intro s hs t ht h
  exact hf.injOn ⟨hs.1, by linarith only [hs.2]⟩
    ⟨ht.1, by linarith only [ht.2]⟩ h

private theorem loop_injOn_upper {f : ℝ → Schoenflies.Plane}
    (hf : Schoenflies.IsLoop f) : InjOn f (Icc (1 / 2 : ℝ) 1) := by
  intro s hs t ht h
  rcases hf.param_eq_or ⟨by linarith only [hs.1], hs.2⟩
    ⟨by linarith only [ht.1], ht.2⟩ h with h | ⟨h, -⟩ | ⟨-, h⟩
  · exact h
  · linarith only [h, hs.1]
  · linarith only [h, ht.1]

private theorem loop_half_arcs {f : ℝ → Schoenflies.Plane}
    (hf : Schoenflies.IsLoop f) :
    Schoenflies.IsArcBetween (f '' Icc (0 : ℝ) (1 / 2)) (f 0) (f (1 / 2)) ∧
    Schoenflies.IsArcBetween (f '' Icc (1 / 2 : ℝ) 1) (f 0) (f (1 / 2)) ∧
    (f '' Icc (0 : ℝ) (1 / 2)) ∪ (f '' Icc (1 / 2 : ℝ) 1) = f '' Icc (0 : ℝ) 1 ∧
    (f '' Icc (0 : ℝ) (1 / 2)) ∩ (f '' Icc (1 / 2 : ℝ) 1) = {f 0, f (1 / 2)} := by
  have hl := Schoenflies.isArcBetween_subarc hf.continuousOn
    (show InjOn f (uIcc (0 : ℝ) (1 / 2)) by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using loop_injOn_lower hf)
    (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by norm_num : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) ≠ 1 / 2)
  have hu := Schoenflies.isArcBetween_subarc hf.continuousOn
    (show InjOn f (uIcc (1 / 2 : ℝ) 1) by
      simpa only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] using loop_injOn_upper hf)
    (by norm_num : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num : (1 / 2 : ℝ) ≠ 1)
  refine ⟨by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hl,
    by simpa only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1), ← hf.closes] using hu.reverse,
    ?_, ?_⟩
  · rw [← image_union, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
  · ext z
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, ⟨t, ht, h⟩⟩
      rcases hf.param_eq_or ⟨hs.1, by linarith only [hs.2]⟩
        ⟨by linarith only [ht.1], ht.2⟩ h.symm with hst | ⟨hs0, -⟩ | ⟨hs1, -⟩
      · have hsH : s = 1 / 2 := by linarith only [hst, hs.2, ht.1]
        exact Or.inr (congrArg f hsH)
      · exact Or.inl (congrArg f hs0)
      · linarith only [hs1, hs.2]
    · rintro (rfl | rfl)
      · exact ⟨⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, hf.closes.symm⟩⟩
      · exact ⟨⟨1 / 2, by norm_num, rfl⟩, ⟨1 / 2, by norm_num, rfl⟩⟩

/-- Matching half-images gives an actual continuous change of parameter. The
inverse is taken separately on the two injective compact half-intervals. -/
private theorem loop_half_reparam {f g : ℝ → Schoenflies.Plane}
    (hf : Schoenflies.IsLoop f) (hg : Schoenflies.IsLoop g)
    (hzero : f 0 = g 0) (hhalf : f (1 / 2) = g (1 / 2))
    (hlower : f '' Icc (0 : ℝ) (1 / 2) = g '' Icc (0 : ℝ) (1 / 2))
    (hupper : f '' Icc (1 / 2 : ℝ) 1 = g '' Icc (1 / 2 : ℝ) 1) :
    ∃ r : I → I, Continuous r ∧ r 0 = 0 ∧ r 1 = 1 ∧
      r midpointUnitInterval = midpointUnitInterval ∧ ∀ t : I, g (r t) = f t := by
  classical
  let l (t : I) : ℝ := Function.invFunOn g (Icc (0 : ℝ) (1 / 2)) (f t)
  let u (t : I) : ℝ := Function.invFunOn g (Icc (1 / 2 : ℝ) 1) (f t)
  have hlmem (t : I) (ht : (t : ℝ) ≤ 1 / 2) :
      f t ∈ g '' Icc (0 : ℝ) (1 / 2) := by
    rw [← hlower]
    exact ⟨t, ⟨t.property.1, ht⟩, rfl⟩
  have humem (t : I) (ht : 1 / 2 ≤ (t : ℝ)) :
      f t ∈ g '' Icc (1 / 2 : ℝ) 1 := by
    rw [← hupper]
    exact ⟨t, ⟨ht, t.property.2⟩, rfl⟩
  have hgl := loop_injOn_lower hg
  have hgu := loop_injOn_upper hg
  have hcl : ContinuousOn l {t : I | (t : ℝ) ≤ 1 / 2} :=
    (Schoenflies.continuousOn_invFunOn_image' isCompact_Icc
      (hg.continuousOn.mono (fun t ht => ⟨ht.1, by linarith only [ht.2]⟩)) hgl).comp
      hf.continuousOn.domRestrict.continuousOn hlmem
  have hcu : ContinuousOn u {t : I | 1 / 2 ≤ (t : ℝ)} :=
    (Schoenflies.continuousOn_invFunOn_image' isCompact_Icc
      (hg.continuousOn.mono (fun t ht => ⟨by linarith only [ht.1], ht.2⟩)) hgu).comp
      hf.continuousOn.domRestrict.continuousOn humem
  have hlhalf : l midpointUnitInterval = 1 / 2 := by
    change Function.invFunOn g _ (f (1 / 2)) = _
    rw [hhalf]
    exact hgl.leftInvOn_invFunOn (by norm_num)
  have huhalf : u midpointUnitInterval = 1 / 2 := by
    change Function.invFunOn g _ (f (1 / 2)) = _
    rw [hhalf]
    exact hgu.leftInvOn_invFunOn (by norm_num)
  let R (t : I) : ℝ := if (t : ℝ) ≤ 1 / 2 then l t else u t
  have hRcont : Continuous R := by
    apply continuous_if_le continuous_subtype_val continuous_const hcl hcu
    intro t ht
    have ht' : t = midpointUnitInterval := Subtype.ext ht
    rw [ht', hlhalf, huhalf]
  have hRmem (t : I) : R t ∈ Icc (0 : ℝ) 1 := by
    dsimp [R]
    split_ifs with ht
    · have h := Function.invFunOn_mem (hlmem t ht)
      exact ⟨h.1, by linarith only [h.2]⟩
    · have h := Function.invFunOn_mem (humem t (le_of_lt (lt_of_not_ge ht)))
      exact ⟨by linarith only [h.1], h.2⟩
  let r (t : I) : I := ⟨R t, hRmem t⟩
  have hrzero : r 0 = 0 := by
    apply Subtype.ext
    change (if (0 : ℝ) ≤ 1 / 2 then Function.invFunOn g _ (f 0) else _) = 0
    rw [ite_eq_left (by norm_num), hzero]
    exact hgl.leftInvOn_invFunOn (by norm_num)
  have hrone : r 1 = 1 := by
    apply Subtype.ext
    change (if (1 : ℝ) ≤ 1 / 2 then _ else Function.invFunOn g _ (f 1)) = 1
    rw [ite_eq_right (by norm_num), ← hf.closes, hzero, hg.closes]
    exact hgu.leftInvOn_invFunOn (by norm_num)
  have hrhalf : r midpointUnitInterval = midpointUnitInterval := by
    apply Subtype.ext
    change (if (1 / 2 : ℝ) ≤ 1 / 2 then l midpointUnitInterval else _) = 1 / 2
    rw [ite_eq_left le_rfl, hlhalf]
  refine ⟨r, hRcont.subtype_mk hRmem, hrzero, hrone, hrhalf, ?_⟩
  intro t
  change g (if (t : ℝ) ≤ 1 / 2 then l t else u t) = f t
  split_ifs with ht
  · exact Function.invFunOn_eq (hlmem t ht)
  · exact Function.invFunOn_eq (humem t (le_of_lt (lt_of_not_ge ht)))

/-- Simple marked paths with equal corresponding half-images differ by an
actual continuous endpoint- and midpoint-preserving reparametrization. -/
theorem exists_path_reparam_of_half_images_eq {a : ℂ} (γ η : Path a a)
    (hγ : InjOn γ (Ico (0 : I) 1)) (hη : InjOn η (Ico (0 : I) 1))
    (hhalf : γ midpointUnitInterval = η midpointUnitInterval)
    (hlower : γ.extend '' Icc (0 : ℝ) (1 / 2) = η.extend '' Icc (0 : ℝ) (1 / 2))
    (hupper : γ.extend '' Icc (1 / 2 : ℝ) 1 = η.extend '' Icc (1 / 2 : ℝ) 1) :
    ∃ (r : I → I) (hr : Continuous r) (hr0 : r 0 = 0) (hr1 : r 1 = 1),
      r midpointUnitInterval = midpointUnitInterval ∧ γ = η.reparam r hr hr0 hr1 := by
  have hh : (complexPlaneCoordinates ∘ γ.extend) (1 / 2) =
      (complexPlaneCoordinates ∘ η.extend) (1 / 2) := by
    simpa only [Function.comp_apply, ← midpointUnitInterval_coe, Path.extend_extends'] using
      congrArg complexPlaneCoordinates hhalf
  have hl := congrArg (fun S : Set ℂ => complexPlaneCoordinates '' S) hlower
  have hu := congrArg (fun S : Set ℂ => complexPlaneCoordinates '' S) hupper
  obtain ⟨r, hr, hr0, hr1, hrhalf, heq⟩ := loop_half_reparam
    (isLoop_complexCoordinates_extend γ hγ) (isLoop_complexCoordinates_extend η hη)
    (by simp only [Function.comp_apply, Path.extend_zero]) hh
    (by simpa only [image_comp] using hl) (by simpa only [image_comp] using hu)
  refine ⟨r, hr, hr0, hr1, hrhalf, ?_⟩
  ext t
  have h := complexPlaneCoordinates.injective (heq t)
  change γ t = η (r t)
  simpa only [Function.comp_apply, Path.extend_extends'] using h.symm

/-- Matching directed half-images preserves the genuine winding number. -/
theorem windingNumber_eq_of_half_images_eq {a : ℂ} (γ η : Path a a)
    (hγ : InjOn γ (Ico (0 : I) 1)) (hη : InjOn η (Ico (0 : I) 1))
    (hhalf : γ midpointUnitInterval = η midpointUnitInterval)
    (hlower : γ.extend '' Icc (0 : ℝ) (1 / 2) = η.extend '' Icc (0 : ℝ) (1 / 2))
    (hupper : γ.extend '' Icc (1 / 2 : ℝ) 1 = η.extend '' Icc (1 / 2 : ℝ) 1)
    (z : ℂ) (hzγ : z ∉ range γ) (hzη : z ∉ range η) :
    windingNumber γ z hzγ = windingNumber η z hzη := by
  obtain ⟨r, hr, hr0, hr1, -, heq⟩ :=
    exists_path_reparam_of_half_images_eq γ η hγ hη hhalf hlower hupper
  subst γ
  exact windingNumber_reparam η z hzη r hr hr0 hr1

private theorem path_symm_half_images {a b : ℂ} (γ : Path a b) :
    γ.symm.extend '' Icc (0 : ℝ) (1 / 2) = γ.extend '' Icc (1 / 2 : ℝ) 1 ∧
    γ.symm.extend '' Icc (1 / 2 : ℝ) 1 = γ.extend '' Icc (0 : ℝ) (1 / 2) := by
  have hext : (γ.symm.extend : ℝ → ℂ) = γ.extend ∘ (fun t : ℝ => 1 - t) :=
    funext γ.extend_symm_apply
  constructor <;> rw [hext, image_comp, image_const_sub_Icc] <;> norm_num

namespace MarkedBoundaryParametrization

variable {D : MarkedJordanDomain}

/-- The closed boundary half traversed from the first mark to the second. -/
def lowerHalf (β : MarkedBoundaryParametrization D) : Set ℂ :=
  β.path.extend '' Icc (0 : ℝ) (1 / 2)

/-- The complementary closed half traversed from the second mark to the first. -/
def upperHalf (β : MarkedBoundaryParametrization D) : Set ℂ :=
  β.path.extend '' Icc (1 / 2 : ℝ) 1

private theorem coordinates_half_arcs (β : MarkedBoundaryParametrization D) :
    Schoenflies.IsArcBetween (complexPlaneCoordinates '' β.lowerHalf)
      (complexPlaneCoordinates D.a) (complexPlaneCoordinates D.b) ∧
    Schoenflies.IsArcBetween (complexPlaneCoordinates '' β.upperHalf)
      (complexPlaneCoordinates D.a) (complexPlaneCoordinates D.b) ∧
    (complexPlaneCoordinates '' β.lowerHalf) ∪ (complexPlaneCoordinates '' β.upperHalf) =
      complexPlaneCoordinates '' frontier D.domain ∧
    (complexPlaneCoordinates '' β.lowerHalf) ∩ (complexPlaneCoordinates '' β.upperHalf) =
      {complexPlaneCoordinates D.a, complexPlaneCoordinates D.b} := by
  have h := loop_half_arcs (isLoop_complexCoordinates_extend β.path β.simple)
  have hh : β.path.extend (1 / 2) = D.b := by
    simpa only [← midpointUnitInterval_coe, Path.extend_extends'] using β.midpoint_eq
  have hfull : β.path.extend '' Icc (0 : ℝ) 1 = frontier D.domain := by
    rw [β.path.image_extend_of_subset (Subset.rfl), β.range_eq_frontier]
  simp only [image_comp] at h
  simpa only [Function.comp_apply, Path.extend_zero, hh, hfull,
    lowerHalf, upperHalf] using h

/-- Each first half is a genuine simple arc between the specified marked points. -/
theorem isArcBetween_lowerHalf (β : MarkedBoundaryParametrization D) :
    Schoenflies.IsArcBetween (complexPlaneCoordinates '' β.lowerHalf)
      (complexPlaneCoordinates D.a) (complexPlaneCoordinates D.b) :=
  β.coordinates_half_arcs.1

/-- The second half is the other genuine arc between the same marked points. -/
theorem isArcBetween_upperHalf (β : MarkedBoundaryParametrization D) :
    Schoenflies.IsArcBetween (complexPlaneCoordinates '' β.upperHalf)
      (complexPlaneCoordinates D.a) (complexPlaneCoordinates D.b) :=
  β.coordinates_half_arcs.2.1

theorem lowerHalf_union_upperHalf (β : MarkedBoundaryParametrization D) :
    β.lowerHalf ∪ β.upperHalf = frontier D.domain := by
  apply complexPlaneCoordinates.injective.image_injective
  simpa only [image_union] using β.coordinates_half_arcs.2.2.1

theorem lowerHalf_inter_upperHalf (β : MarkedBoundaryParametrization D) :
    β.lowerHalf ∩ β.upperHalf = {D.a, D.b} := by
  apply complexPlaneCoordinates.injective.image_injective
  simpa only [image_inter complexPlaneCoordinates.injective, image_pair] using
    β.coordinates_half_arcs.2.2.2

/-- Before using orientation, two boundary parametrizations have the same pair
of actual arcs, possibly exchanged. -/
theorem half_arcs_eq_or_swap (β γ : MarkedBoundaryParametrization D) :
    (β.lowerHalf = γ.lowerHalf ∧ β.upperHalf = γ.upperHalf) ∨
      (β.lowerHalf = γ.upperHalf ∧ β.upperHalf = γ.lowerHalf) := by
  have h := Schoenflies.two_arcs_unique β.coordinates_half_arcs.2.2.1
    β.coordinates_half_arcs.2.2.2 γ.coordinates_half_arcs.2.2.1
    γ.coordinates_half_arcs.2.2.2 β.isArcBetween_lowerHalf β.isArcBetween_upperHalf
    γ.isArcBetween_lowerHalf γ.isArcBetween_upperHalf
  rcases h with ⟨hl, hu⟩ | ⟨hl, hu⟩
  · exact Or.inl ⟨complexPlaneCoordinates.injective.image_injective hl,
      complexPlaneCoordinates.injective.image_injective hu⟩
  · exact Or.inr ⟨complexPlaneCoordinates.injective.image_injective hl,
      complexPlaneCoordinates.injective.image_injective hu⟩

/-- The geometric CCW condition determines the directed halves for every
admissible parametrization, without any extra reparametrization hypothesis. -/
theorem half_arcs_eq (β γ : MarkedBoundaryParametrization D) :
    β.lowerHalf = γ.lowerHalf ∧ β.upperHalf = γ.upperHalf := by
  rcases β.half_arcs_eq_or_swap γ with h | h
  · exact h
  · exfalso
    obtain ⟨z, hz⟩ := D.isJordanDomain.nonempty
    have hsym := path_symm_half_images γ.path
    have hh : β.path midpointUnitInterval = γ.path.symm midpointUnitInterval := by
      rw [path_symm_apply_midpoint γ.path midpointUnitInterval midpointUnitInterval_coe,
        β.midpoint_eq, γ.midpoint_eq]
    have hw := windingNumber_eq_of_half_images_eq β.path γ.path.symm
      β.simple (jordanPath_symm_injOn γ.path γ.simple) hh
      (h.1.trans hsym.1.symm) (h.2.trans hsym.2.symm) z
      (β.domain_subset_complement_range hz)
      (not_mem_range_symm γ.path (γ.domain_subset_complement_range hz))
    have hrev := windingNumber_symm γ.path z (γ.domain_subset_complement_range hz)
    rw [β.windingNumber_domain_eq_one hz, hrev, γ.windingNumber_domain_eq_one hz] at hw
    norm_num at hw

/-- The free first-to-second boundary half is independent of the admissible
counterclockwise parametrization. -/
theorem lowerHalf_eq (β γ : MarkedBoundaryParametrization D) :
    β.lowerHalf = γ.lowerHalf := (β.half_arcs_eq γ).1

/-- The wired second-to-first boundary half is likewise independent of speed. -/
theorem upperHalf_eq (β γ : MarkedBoundaryParametrization D) :
    β.upperHalf = γ.upperHalf := (β.half_arcs_eq γ).2

/-- In particular every two admissible parametrizations are related by a real
continuous change of parameter fixing both marked times. -/
theorem exists_reparam (β γ : MarkedBoundaryParametrization D) :
    ∃ (r : I → I) (hr : Continuous r) (hr0 : r 0 = 0) (hr1 : r 1 = 1),
      r midpointUnitInterval = midpointUnitInterval ∧ β.path = γ.path.reparam r hr hr0 hr1 :=
  exists_path_reparam_of_half_images_eq β.path γ.path β.simple γ.simple
    (β.midpoint_eq.trans γ.midpoint_eq.symm) (β.lowerHalf_eq γ) (β.upperHalf_eq γ)

end MarkedBoundaryParametrization

end PottsContinuity.FKC
