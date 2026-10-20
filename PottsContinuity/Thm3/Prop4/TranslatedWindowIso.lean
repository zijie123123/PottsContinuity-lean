module

public import PottsContinuity.Thm3.Prop4.TranslatedArcSupport
public import PottsContinuity.Thm3.Prop4.WiredTargetIso
public import PottsContinuity.PD.FK.ConfigurationBridge

/-!
# Actual translated-window graph and wired-target law

Translation identifies the entire target with its nested induced graph once
the ambient truncation contains it. The Boolean event is transported to the
actual finite-edge connection event, without boundary-identification paths.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- Literal integer translation into the full target inside an ambient truncation. -/
def translatedTiltedWindowIso (N M n m : ℕ) (t : ℝ) (x : ℤ × ℤ)
    (hcontain : translatedTiltedWindow n m t x ⊆ (tiltedWindow N M t : Set (ℤ × ℤ))) :
    (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))) ≃g
      (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))).induce
        (translatedWindowDomain N M n m t x) where
  toEquiv :=
    { toFun := fun z =>
        ⟨⟨x+z.val,hcontain (by
          change x+z.val-x ∈ tiltedWindow n m t
          rw [add_sub_cancel_left]
          exact z.property)⟩,by
          change x+z.val-x ∈ tiltedWindow n m t
          rw [add_sub_cancel_left]
          exact z.property⟩
      invFun := fun z => ⟨z.val.val-x,z.property⟩
      left_inv := by
        intro z
        apply Subtype.ext
        exact add_sub_cancel_left x z.val
      right_inv := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        exact add_sub_cancel x z.val.val }
  map_rel_iff' := by
    intro a b
    change |(x.1+a.val.1)-(x.1+b.val.1)|+|(x.2+a.val.2)-(x.2+b.val.2)|=1 ↔
      |a.val.1-b.val.1|+|a.val.2-b.val.2|=1
    simp only [add_sub_add_left_eq_sub]

/-- The entire digital wired arc, including corners, pulls back to its original arc. -/
theorem translatedTiltedWindowIso_arc (N M n m : ℕ) (t : ℝ) (x : ℤ × ℤ)
    (hcontain : translatedTiltedWindow n m t x ⊆ (tiltedWindow N M t : Set (ℤ × ℤ))) :
    (translatedTiltedWindowIso N M n m t x hcontain) ⁻¹'
      (Subtype.val ⁻¹' translatedWindowArc N M n m t x) = tiltedWindowWiredVertices n m t 1 := by
  ext z
  change (∃ hz : x+z.val-x ∈ tiltedWindow n m t,
    (⟨x+z.val-x,hz⟩ : (tiltedWindow n m t : Set (ℤ × ℤ))) ∈
      tiltedWindowWiredVertices n m t 1) ↔ z ∈ tiltedWindowWiredVertices n m t 1
  simp only [add_sub_cancel_left]
  exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨z.property,h⟩⟩

/-- The source Boolean touch probability is exactly the actual finite target-event probability. -/
theorem tiltedTouchProbability_eq_target_measure (θ : Parameters) (n m : ℕ) (t : ℝ) :
    tiltedTouchProbability θ n m t =
      (measure (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))) θ
        (BoundaryCondition.wired (tiltedWindowWiredVertices n m t 1))
        (targetConnectionEvent (tiltedWindowOrigin n m t) (tiltedWindowWiredVertices n m t 1))).toReal := by
  unfold tiltedTouchProbability RSW.finiteBoundaryEventProbability
  congr 2
  ext A
  change (∃ z ∈ tiltedWindowWiredVertices n m t 1,
    (rcOpenGraph (tiltedWindow n m t) ((boolConfigurationEquiv _).symm A)).Reachable _ z) ↔ _
  have hgraph := openGraph_boolConfigurationEquiv
    (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))) ((boolConfigurationEquiv _).symm A)
  rw [Equiv.apply_symm_apply] at hgraph
  change (∃ z ∈ tiltedWindowWiredVertices n m t 1,
    (SimpleGraph.fromEdgeSet {e | ∃ h : e ∈
      (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))).edgeSet,
      (boolConfigurationEquiv _).symm A ⟨e,h⟩ = true}).Reachable (tiltedWindowOrigin n m t) z) ↔ _
  rw [← hgraph]
  rfl

/-- Exact translated finite target law at every independent FK parameter. -/
theorem translatedWindow_target_probability_eq (θ : Parameters)
    (N M n m : ℕ) (t : ℝ) (x : ℤ × ℤ)
    (hcontain : translatedTiltedWindow n m t x ⊆ (tiltedWindow N M t : Set (ℤ × ℤ))) :
    let e := translatedTiltedWindowIso N M n m t x hcontain
    (measure ((squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))).induce
        (translatedWindowDomain N M n m t x)) θ
      (BoundaryCondition.wired (Subtype.val ⁻¹' translatedWindowArc N M n m t x))
      (targetConnectionEvent (e (tiltedWindowOrigin n m t))
        (Subtype.val ⁻¹' translatedWindowArc N M n m t x))).toReal =
      tiltedTouchProbability θ n m t := by
  dsimp only
  rw [tiltedTouchProbability_eq_target_measure]
  have h := wired_target_probability_iso (translatedTiltedWindowIso N M n m t x hcontain)
    θ (Subtype.val ⁻¹' translatedWindowArc N M n m t x) (tiltedWindowOrigin n m t)
  rw [translatedTiltedWindowIso_arc] at h
  exact h.symm

end
end PottsContinuity.Thm3.Prop4
