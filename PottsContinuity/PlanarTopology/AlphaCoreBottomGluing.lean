module

public import PottsContinuity.PlanarTopology.IsometricGluing
public import PottsContinuity.PlanarTopology.AlphaCoreToBottom

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Pair the 512 offset bottom-arc translates with reflected source factors. -/
theorem alpha_core_to_bottom_long_gluing (a : ℕ) (ha : 1 ≤ a) :
    ∃ e : Fin 1024 → (PD.squareLattice ≃g PD.squareLattice),
      (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
      (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹' alphaCoreToBottom a) ⊆
        horizontalRectangle (-512*(a : ℤ)-1,-64*(a : ℤ)) (1024*a+1) (128*a-1) := by
  obtain ⟨f,hf,hglue⟩ := alpha_core_bottom_arc_long_gluing a ha
  let e : Fin 1024 → (PD.squareLattice ≃g PD.squareLattice) := fun j =>
    if j.val % 2 = 0 then f ⟨j.val/2,by omega⟩
    else (f ⟨j.val/2,by omega⟩).trans alphaCoreReflectionXIso
  refine ⟨e,?_,?_⟩
  · intro j
    dsimp [e]
    split
    · exact hf _
    · exact latticeBox_iso_trans _ alphaCoreReflectionXIso (hf _) alphaCoreReflectionXIso_box
  · intro ω hω
    apply hglue
    apply Set.mem_iInter.mpr
    intro j
    apply alpha_core_to_bottom_reflected_glue a ha
    have heven : e ⟨2*j.val,by omega⟩ = f j := by
      dsimp [e]
      rw [ite_eq_left (by omega : 2*j.val % 2 = 0)]
      congr 1
      exact Fin.ext (show 2*j.val/2 = j.val by omega)
    have hodd : e ⟨2*j.val+1,by omega⟩ = (f j).trans alphaCoreReflectionXIso := by
      dsimp [e]
      rw [ite_eq_right (by omega : ¬(2*j.val+1) % 2 = 0)]
      congr 1
      congr 1
      exact Fin.ext (show (2*j.val+1)/2 = j.val by omega)
    constructor
    · have hh := Set.mem_iInter.mp hω (⟨2*j.val,by omega⟩ : Fin 1024)
      rwa [heven] at hh
    · have hh := Set.mem_iInter.mp hω (⟨2*j.val+1,by omega⟩ : Fin 1024)
      rw [hodd] at hh
      change latticeConfigurationIsoHomeomorph ((f j).trans alphaCoreReflectionXIso) ω ∈ alphaCoreToBottom a at hh
      rw [latticeConfigurationIsoHomeomorph_trans_apply] at hh
      exact hh

end
end PottsContinuity.PlanarTopology
