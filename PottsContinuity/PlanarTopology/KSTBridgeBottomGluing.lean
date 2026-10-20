module

public import PottsContinuity.PlanarTopology.IsometricGluing

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Pair each beta bottom-arc translate with its reflected source E factor.
There are 96 pairs, hence 192 genuine E factors. -/
theorem kst_bridge_to_bottom_long_gluing (a : ℕ) (ha : 1 ≤ a) :
    ∃ e : Fin 192 → (PD.squareLattice ≃g PD.squareLattice),
      (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
      (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹' kstBridgeToBottom (12*a)) ⊆
        horizontalRectangle (-96*(a : ℤ),-12*(a : ℤ)) (192*a) (24*a) := by
  obtain ⟨f,hf,hglue⟩ := kst_beta_bottom_arc_long_gluing a ha
  let e : Fin 192 → (PD.squareLattice ≃g PD.squareLattice) := fun j =>
    if j.val % 2 = 0 then f ⟨j.val/2,by omega⟩
    else (f ⟨j.val/2,by omega⟩).trans kstReflectionXIso
  refine ⟨e,?_,?_⟩
  · intro j
    dsimp [e]
    split
    · exact hf _
    · exact latticeBox_iso_trans _ kstReflectionXIso (hf _) kstReflectionXIso_box
  · intro ω hω
    apply hglue
    apply Set.mem_iInter.mpr
    intro j
    apply kst_bridge_to_bottom_reflected_glue a ha
    have heven : e ⟨2*j.val,by omega⟩ = f j := by
      dsimp [e]
      rw [ite_eq_left (by omega : 2*j.val % 2 = 0)]
      congr 1
      exact Fin.ext (show 2*j.val/2 = j.val by omega)
    have hodd : e ⟨2*j.val+1,by omega⟩ = (f j).trans kstReflectionXIso := by
      dsimp [e]
      rw [ite_eq_right (by omega : ¬(2*j.val+1) % 2 = 0)]
      congr 1
      congr 1
      exact Fin.ext (show (2*j.val+1)/2 = j.val by omega)
    constructor
    · have hh := Set.mem_iInter.mp hω (⟨2*j.val,by omega⟩ : Fin 192)
      rwa [heven] at hh
    · have hh := Set.mem_iInter.mp hω (⟨2*j.val+1,by omega⟩ : Fin 192)
      rw [hodd] at hh
      change latticeConfigurationIsoHomeomorph ((f j).trans kstReflectionXIso) ω ∈ kstBridgeToBottom (12*a) at hh
      rw [latticeConfigurationIsoHomeomorph_trans_apply] at hh
      exact hh

end
end PottsContinuity.PlanarTopology
