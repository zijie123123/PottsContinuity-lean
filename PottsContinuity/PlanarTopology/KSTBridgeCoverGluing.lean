module

public import PottsContinuity.PlanarTopology.KSTBridgeFiveCover
public import PottsContinuity.PlanarTopology.KSTBridgeBottomGluing
public import PottsContinuity.PlanarTopology.KSTSkinnyGluing

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Every one of the five source candidates has a genuine isometric gluing to
the long crossing, using at most 192 factors and then padding to 2000. -/
theorem kst_bridge_cover_piece_gluing (a : ℕ) (ha : 1 ≤ a) (i : Fin 5) :
    ∃ e : Fin 2000 → (PD.squareLattice ≃g PD.squareLattice),
      (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
      (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹' kstBridgeCoverPiece a i) ⊆
        horizontalRectangle (-96*(a : ℤ),-12*(a : ℤ)) (192*a) (24*a) := by
  have hE := kst_bridge_to_bottom_long_gluing a ha
  fin_cases i
  · exact isometric_gluing_pad (by decide : 1 ≤ 192) (by decide : 192 ≤ 2000) hE
  · exact isometric_gluing_pad (by decide : 1 ≤ 192) (by decide : 192 ≤ 2000)
      (isometric_gluing_iso_preimage kstReflectionYIso kstReflectionYIso_box hE)
  · exact isometric_gluing_pad (by decide : 1 ≤ 192) (by decide : 192 ≤ 2000)
      (isometric_gluing_iso_preimage kstReflectionXIso kstReflectionXIso_box hE)
  · exact isometric_gluing_pad (by decide : 1 ≤ 192) (by decide : 192 ≤ 2000)
      (isometric_gluing_iso_preimage kstReflectionBothIso kstReflectionBothIso_box hE)
  · have hC := kst_skinny_rectangle_gluing 84 (12*a) a (by decide)
    have h13 : 12*a+a = 13*a := by omega
    have h96 : 12*a+84*a = 96*a := by omega
    have h26 : 2*(13*a) = 26*a := by omega
    have h24 : 2*(12*a) = 24*a := by omega
    have h192 : 2*(96*a) = 192*a := by omega
    rw [h13,h96,h26,h24,h192] at hC
    have hC' : ∃ e : Fin 167 → (PD.squareLattice ≃g PD.squareLattice),
        (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
        (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹'
          horizontalRectangle (-13*(a : ℤ),-12*(a : ℤ)) (26*a) (24*a)) ⊆
          horizontalRectangle (-96*(a : ℤ),-12*(a : ℤ)) (192*a) (24*a) := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat,neg_mul] using hC
    exact isometric_gluing_pad (by decide : 1 ≤ 167) (by decide : 167 ≤ 2000) hC'

end
end PottsContinuity.PlanarTopology
