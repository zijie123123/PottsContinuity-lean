module

public import PottsContinuity.Thm3.Prop4.TiltedConnectionEvents

/-!
# Actual point reflection of the tilted strip

Reflection through (0,N/2) preserves the original lattice and exchanges its
digital top and bottom. This supplies the primal reflection part of the
half-height argument; no statement about a dual measure is inferred.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
noncomputable section

/-- Integer-lattice point reflection through the midpoint of the strip's central column. -/
def tiltedReflection (N : ℕ) (z : ℤ × ℤ) : ℤ × ℤ := (-z.1,(N : ℤ)-z.2)

/-- Reflection complements the exact supporting-line height. -/
theorem tiltedHeight_reflection (N : ℕ) (t : ℝ) (z : ℤ × ℤ) :
    tiltedHeight t (tiltedReflection N z) = (N : ℝ)-tiltedHeight t z := by
  dsimp [tiltedReflection,tiltedHeight]
  push_cast
  ring

/-- The actual lattice reflection is an involution on its whole carrier. -/
theorem tiltedReflection_involutive (N : ℕ) : Function.Involutive (tiltedReflection N) := by
  intro z
  apply Prod.ext <;> dsimp [tiltedReflection] <;> omega

/-- Reflection preserves exactly the original induced strip carrier. -/
theorem tiltedReflection_mem_strip_iff (N : ℕ) (t : ℝ) (z : ℤ × ℤ) :
    tiltedReflection N z ∈ tiltedStripVertices N t ↔ z ∈ tiltedStripVertices N t := by
  change (0 ≤ tiltedHeight t (tiltedReflection N z) ∧ tiltedHeight t (tiltedReflection N z) ≤ N) ↔ _
  rw [tiltedHeight_reflection]
  constructor <;> intro h <;> constructor <;> linarith only [h.1,h.2]

end
end PottsContinuity.Thm3.Prop4
