module

public import PottsContinuity.PlanarTopology.AlphaCoreBridgeWitness
public import PottsContinuity.PlanarTopology.AlphaCoreSymmetries
public import PottsContinuity.PlanarTopology.AlphaCoreRectangleFactors

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Four genuine boundary connections and the complete odd rectangle crossing. -/
def alphaCoreCoverPiece (k : ℕ) : Fin 5 → Set LatticeConfiguration :=
  ![alphaCoreToBottom k,
    latticeConfigurationIsoHomeomorph alphaCoreReflectionYIso ⁻¹' alphaCoreToBottom k,
    latticeConfigurationIsoHomeomorph alphaCoreReflectionXIso ⁻¹' alphaCoreToBottom k,
    latticeConfigurationIsoHomeomorph alphaCoreReflectionBothIso ⁻¹' alphaCoreToBottom k,
    alphaCoreRectangle k]

theorem alphaCoreCoverPiece_isCylinder (k : ℕ) (i : Fin 5) :
    PD.RCInfinite.IsCylinder (alphaCoreCoverPiece k i) := by
  fin_cases i
  · exact alphaCoreToBottom_isCylinder _
  · exact isCylinder_iso_preimage _ (alphaCoreToBottom_isCylinder _)
  · exact isCylinder_iso_preimage _ (alphaCoreToBottom_isCylinder _)
  · exact isCylinder_iso_preimage _ (alphaCoreToBottom_isCylinder _)
  · exact horizontalRectangle_isCylinder _ _ _

theorem alphaCoreCoverPiece_isUpperSet (k : ℕ) (i : Fin 5) :
    IsUpperSet (alphaCoreCoverPiece k i) := by
  fin_cases i
  · exact alphaCoreToBottom_isUpperSet _
  · exact isUpperSet_iso_preimage _ (alphaCoreToBottom_isUpperSet _)
  · exact isUpperSet_iso_preimage _ (alphaCoreToBottom_isUpperSet _)
  · exact isUpperSet_iso_preimage _ (alphaCoreToBottom_isUpperSet _)
  · exact horizontalRectangle_isUpperSet _ _ _

/-- Every actual core bridge belongs to one of five geometric candidates. -/
theorem alpha_core_bridge_five_cover (k : ℕ) (hk : 1 ≤ k) :
    alphaCoreBridge k ⊆ ⋃ i, alphaCoreCoverPiece k i := by
  intro ω hω
  obtain ⟨u,v,p,hp,hu,hv,hbox⟩ := alpha_core_bridge_walk_witness k hk ω hω
  by_cases hvBottom : v.2 = -64*(k : ℤ)
  · exact Set.mem_iUnion.mpr ⟨0,by exact ⟨u,v,p,hp,hu,hv,hvBottom,hbox⟩⟩
  by_cases hvTop : v.2 = 64*(k : ℤ)-1
  · apply Set.mem_iUnion.mpr
    refine ⟨1,?_⟩
    change latticeConfigurationIsoHomeomorph alphaCoreReflectionYIso ω ∈ alphaCoreToBottom k
    refine ⟨_,_,p.map alphaCoreReflectionYIso.toHom,kstPathOpen_map_iso _ ω p hp,
      (alphaCoreLeftTargets_y_map _ _).mpr hu,(alphaCoreRightTargets_y_map _ _).mpr hv,?_,?_⟩
    · change -v.2+ -1 = -64*(k : ℤ)
      omega
    · apply alpha_core_bounds_map k _ _ p hbox
      intro z hz
      change -65*(k : ℤ) ≤ z.1+0 ∧ z.1+0 ≤ 65*(k : ℤ)-1 ∧
        -64*(k : ℤ) ≤ -z.2+ -1 ∧ -z.2+ -1 ≤ 64*(k : ℤ)-1
      omega
  have hpR : kstPathOpen ω p.reverse := (kstPathOpen_reverse_iff ω p).mpr hp
  have hboxR : kstPathIn p.reverse (-65*(k : ℤ)) (65*(k : ℤ)-1) (-64*(k : ℤ)) (64*(k : ℤ)-1) := by
    intro z hz
    apply hbox z
    simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz
  by_cases huBottom : u.2 = -64*(k : ℤ)
  · apply Set.mem_iUnion.mpr
    refine ⟨2,?_⟩
    change latticeConfigurationIsoHomeomorph alphaCoreReflectionXIso ω ∈ alphaCoreToBottom k
    refine ⟨_,_,p.reverse.map alphaCoreReflectionXIso.toHom,kstPathOpen_map_iso _ ω p.reverse hpR,
      (alphaCoreLeftTargets_x_map _ _).mpr hv,(alphaCoreRightTargets_x_map _ _).mpr hu,?_,?_⟩
    · change u.2+0 = -64*(k : ℤ)
      omega
    · apply alpha_core_bounds_map k _ _ p.reverse hboxR
      intro z hz
      change -65*(k : ℤ) ≤ -z.1+ -1 ∧ -z.1+ -1 ≤ 65*(k : ℤ)-1 ∧
        -64*(k : ℤ) ≤ z.2+0 ∧ z.2+0 ≤ 64*(k : ℤ)-1
      omega
  by_cases huTop : u.2 = 64*(k : ℤ)-1
  · apply Set.mem_iUnion.mpr
    refine ⟨3,?_⟩
    change latticeConfigurationIsoHomeomorph alphaCoreReflectionBothIso ω ∈ alphaCoreToBottom k
    refine ⟨_,_,p.reverse.map alphaCoreReflectionBothIso.toHom,kstPathOpen_map_iso _ ω p.reverse hpR,?_,?_,?_,?_⟩
    · exact (alphaCoreLeftTargets_y_map _ _).mpr ((alphaCoreLeftTargets_x_map _ _).mpr hv)
    · exact (alphaCoreRightTargets_y_map _ _).mpr ((alphaCoreRightTargets_x_map _ _).mpr hu)
    · change -(u.2+0)+ -1 = -64*(k : ℤ)
      omega
    · apply alpha_core_bounds_map k _ _ p.reverse hboxR
      intro z hz
      change -65*(k : ℤ) ≤ (-z.1+ -1)+0 ∧ (-z.1+ -1)+0 ≤ 65*(k : ℤ)-1 ∧
        -64*(k : ℤ) ≤ -(z.2+0)+ -1 ∧ -(z.2+0)+ -1 ≤ 64*(k : ℤ)-1
      omega
  have hux : u.1 = -65*(k : ℤ) := by rcases hu.2.2 with h | h | h <;> omega
  have hvx : v.1 = 65*(k : ℤ)-1 := by rcases hv.2.2 with h | h | h <;> omega
  apply Set.mem_iUnion.mpr
  refine ⟨4,?_⟩
  apply horizontalRectangle_of_kst_open_walk _ _ _ ω p hp hux
  · change v.1 = -65*(k : ℤ)+(130*k-1 : ℕ)
    omega
  · intro z hz
    have hh := hbox z hz
    change -65*(k : ℤ) ≤ z.1 ∧ z.1 ≤ -65*(k : ℤ)+(130*k-1 : ℕ) ∧
      -64*(k : ℤ) ≤ z.2 ∧ z.2 ≤ -64*(k : ℤ)+(128*k-1 : ℕ)
    exact ⟨hh.1,by omega,hh.2.2.1,by omega⟩

end
end PottsContinuity.PlanarTopology
