module

public import PottsContinuity.PlanarTopology.HalfPlaneExitFKG
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite
noncomputable section

/-- Vertical translation transports every genuine first-exit bond and the
sole allowed exterior terminal, without introducing boundary edges. -/
theorem halfPlaneExitEvent_translate_vertical (k : ℤ) (S : Set LatticeVertex) (L : Set ℤ)
    (ω : LatticeConfiguration) (hω : ω ∈ halfPlaneExitEvent S L) :
    edgeTranslate (0,k) ω ∈ halfPlaneExitEvent
      (latticeTranslate (0,k) '' S) ((fun y : ℤ => y+k) '' L) := by
  obtain ⟨y,hy,u,hu,huH,p,hp⟩ := halfPlaneExitEvent_original_walk S L ω hω
  let e := openGraphTranslationIso (0,k) ω
  have htarget : e (-1,y) = (-1,y+k) := by
    change (-1+0,y+k) = (-1,y+k)
    simp
  let q := (p.map e.toHom).copy rfl htarget
  apply halfPlaneExitEvent_of_original_walk (latticeTranslate (0,k) '' S)
    ((fun y : ℤ => y+k) '' L) (edgeTranslate (0,k) ω) (y+k)
    ⟨y,hy,rfl⟩ (e u) ⟨u,hu,rfl⟩
    (by change 0 ≤ u.1+0; omega) q
  intro z hz
  have hs : q.support = p.support.map e := by
    dsimp [q]
    rw [SimpleGraph.Walk.support_copy]
    exact SimpleGraph.Walk.support_map e.toHom p
  have hz' : z ∈ p.support.map e := Eq.mp (congrArg (fun xs : List LatticeVertex => z ∈ xs) hs) hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz'
  rcases hp w hw with h | rfl
  · left
    change 0 ≤ w.1+0
    omega
  · right
    exact htarget

/-- The translated first-exit event has exactly the original pullback. -/
theorem halfPlaneExitEvent_vertical_preimage (k : ℤ) (S : Set LatticeVertex) (L : Set ℤ) :
    edgeTranslate (0,k) ⁻¹' halfPlaneExitEvent
      (latticeTranslate (0,k) '' S) ((fun y : ℤ => y+k) '' L) = halfPlaneExitEvent S L := by
  have hS : latticeTranslate (0,-k) '' (latticeTranslate (0,k) '' S) = S := by
    rw [Set.image_image]
    have hf : latticeTranslate (0,-k) ∘ latticeTranslate (0,k) = id := by
      funext z
      ext <;> dsimp [latticeTranslate] <;> omega
    change (latticeTranslate (0,-k) ∘ latticeTranslate (0,k)) '' S = S
    rw [hf,Set.image_id]
  have hL : (fun y : ℤ => y-k) '' ((fun y : ℤ => y+k) '' L) = L := by
    rw [Set.image_image]
    have hf : (fun y : ℤ => y-k) ∘ (fun y : ℤ => y+k) = id := by funext y; dsimp; omega
    change ((fun y : ℤ => y-k) ∘ (fun y : ℤ => y+k)) '' L = L
    rw [hf,Set.image_id]
  ext ω
  constructor
  · intro h
    have hh := halfPlaneExitEvent_translate_vertical (-k) _ _ (edgeTranslate (0,k) ω) h
    have hzero : (0,-k)+(0,k) = (0 : LatticeVertex) := by ext <;> simp
    rw [← edgeTranslate_add,hzero,edgeTranslate_zero,hS] at hh
    have hL' : (fun y : ℤ => y + -k) '' ((fun y : ℤ => y+k) '' L) = L := by
      simpa only [sub_eq_add_neg] using hL
    rwa [hL'] at hh
  · exact halfPlaneExitEvent_translate_vertical k S L ω

/-- Translation invariance identifies the probabilities of the exact shifted
source and target first-exit events. -/
theorem measure_halfPlaneExitEvent_vertical_translate (μ : Measure LatticeConfiguration)
    (k : ℤ) (hμ : μ.map (edgeTranslate (0,k)) = μ) (S : Set LatticeVertex) (L : Set ℤ) :
    μ (halfPlaneExitEvent (latticeTranslate (0,k) '' S) ((fun y : ℤ => y+k) '' L)) =
      μ (halfPlaneExitEvent S L) := by
  have hh := congrArg (fun ν : Measure LatticeConfiguration =>
    ν (halfPlaneExitEvent (latticeTranslate (0,k) '' S) ((fun y : ℤ => y+k) '' L))) hμ
  rw [Measure.map_apply (edgeTranslate_measurable _) (halfPlaneExitEvent_measurableSet _ _),
    halfPlaneExitEvent_vertical_preimage] at hh
  exact hh.symm

end
end PottsContinuity.PlanarTopology
