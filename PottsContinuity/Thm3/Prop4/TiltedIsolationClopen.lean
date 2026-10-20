module

public import PottsContinuity.Thm3.Prop4.TiltedClosedExtension
public import PottsContinuity.Thm3.Prop4.TranslatedContainment

/-! # Clopenness and exact finite-extension preimage of the original A(x) -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- The full source isolation event is a clopen event on the original infinite strip. -/
theorem isClopen_tiltedTouchIsolationEvent (N n m : ℕ) (t : ℝ)
    (x : tiltedStripVertices N t) :
    IsClopen {ω : TiltedConfiguration N t | tiltedTouchIsolationEvent N n m t ω x} := by
  obtain ⟨R,hxR⟩ := lattice_point_mem_some_box x.val
  let D : Set (tiltedStripVertices N t) := {z | z.val ∈ translatedTiltedWindow n m t x.val}
  let W : Set (tiltedStripVertices N t) := {z | translatedTiltedWired n m t x.val z.val}
  have hWD : W ⊆ D := by
    rintro z ⟨hz,_⟩
    exact hz
  have hxD : x ∈ D := mem_translatedTiltedWindow_self n m t x.val
  have hD : ∀ z ∈ D, z.val ∈ box (R+m) := by
    intro z hz
    exact translatedTiltedWindow_subset_box n m R t x.val hxR hz
  exact isClopen_tilted_graphArcIsolation N t D W hWD x hxD (R+m) hD

/-- A full finite-window extension has exactly the original finite isolation event as preimage. -/
theorem tiltedTouchIsolationEvent_closedExtension_iff (N M n m : ℕ) (t : ℝ)
    (x : tiltedStripVertices N t)
    (hcontain : translatedTiltedWindow n m t x.val ⊆ (tiltedWindow N M t : Set (ℤ × ℤ)))
    (A : Configuration (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ)))) :
    let hxM := hcontain (mem_translatedTiltedWindow_self n m t x.val)
    tiltedTouchIsolationEvent N n m t
      (tiltedPlaneRestriction N t (tiltedWindowPlaneConfiguration N M t A)) x ↔
      A ∈ finiteArcIsolationEvent (translatedWindowDomain N M n m t x.val)
        (translatedWindowArc N M n m t x.val) ⟨x.val,hxM⟩ := by
  dsimp only
  let D : Set (tiltedStripVertices N t) := {z | z.val ∈ translatedTiltedWindow n m t x.val}
  let W : Set (tiltedStripVertices N t) := {z | translatedTiltedWired n m t x.val z.val}
  let f := (tiltedWindowStripEmbedding N M t).toEmbedding
  have hW : W ⊆ Set.range f := by
    rintro z ⟨hz,_⟩
    exact ⟨⟨z.val,hcontain hz⟩,Subtype.ext rfl⟩
  let xM : (tiltedWindow N M t : Set (ℤ × ℤ)) :=
    ⟨x.val,hcontain (mem_translatedTiltedWindow_self n m t x.val)⟩
  change graphArcIsolation (tiltedOpenGraph N t
      (tiltedPlaneRestriction N t (tiltedWindowPlaneConfiguration N M t A))) D W (f xM) ↔
    graphArcIsolation (openGraph _ A) (f ⁻¹' D) (f ⁻¹' W) xM
  rw [tiltedClosedExtension_openGraph]
  exact graphArcIsolation_map_iff f D W hW xM

end
end PottsContinuity.Thm3.Prop4
