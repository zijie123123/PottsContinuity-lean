module

public import PottsContinuity.PlanarTopology.AlphaCoreFiveCover
public import PottsContinuity.PlanarTopology.AlphaCoreBottomGluing
public import PottsContinuity.PlanarTopology.AlphaCoreRectangleGluing

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Every genuine odd-core candidate glues to the same long crossing. -/
theorem alpha_core_cover_piece_gluing (a : ℕ) (ha : 1 ≤ a) (i : Fin 5) :
    ∃ e : Fin 2000 → (PD.squareLattice ≃g PD.squareLattice),
      (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
      (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹' alphaCoreCoverPiece a i) ⊆
        horizontalRectangle (-512*(a : ℤ)-1,-64*(a : ℤ)) (1024*a+1) (128*a-1) := by
  have hE := alpha_core_to_bottom_long_gluing a ha
  fin_cases i
  · exact isometric_gluing_pad (by decide : 1 ≤ 1024) (by decide : 1024 ≤ 2000) hE
  · exact isometric_gluing_pad (by decide : 1 ≤ 1024) (by decide : 1024 ≤ 2000)
      (isometric_gluing_iso_preimage alphaCoreReflectionYIso alphaCoreReflectionYIso_box hE)
  · exact isometric_gluing_pad (by decide : 1 ≤ 1024) (by decide : 1024 ≤ 2000)
      (isometric_gluing_iso_preimage alphaCoreReflectionXIso alphaCoreReflectionXIso_box hE)
  · exact isometric_gluing_pad (by decide : 1 ≤ 1024) (by decide : 1024 ≤ 2000)
      (isometric_gluing_iso_preimage alphaCoreReflectionBothIso alphaCoreReflectionBothIso_box hE)
  · exact isometric_gluing_pad (by decide : 1 ≤ 897) (by decide : 897 ≤ 2000)
      (alpha_core_rectangle_long_gluing a ha)

end
end PottsContinuity.PlanarTopology
