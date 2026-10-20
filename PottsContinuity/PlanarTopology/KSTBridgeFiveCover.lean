module

public import PottsContinuity.PlanarTopology.KSTBridgeSymmetries

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Four literal boundary-connection alternatives and the rectangle crossing.
Every index of Fin 5 denotes one genuine source event. -/
def kstBridgeCoverPiece (a : ℕ) : Fin 5 → Set LatticeConfiguration :=
  ![kstBridgeToBottom (12*a),
    latticeConfigurationIsoHomeomorph kstReflectionYIso ⁻¹' kstBridgeToBottom (12*a),
    latticeConfigurationIsoHomeomorph kstReflectionXIso ⁻¹' kstBridgeToBottom (12*a),
    latticeConfigurationIsoHomeomorph kstReflectionBothIso ⁻¹' kstBridgeToBottom (12*a),
    horizontalRectangle (-13*(a : ℤ),-12*(a : ℤ)) (26*a) (24*a)]

theorem kstBridgeCoverPiece_isCylinder (a : ℕ) (i : Fin 5) :
    PD.RCInfinite.IsCylinder (kstBridgeCoverPiece a i) := by
  fin_cases i
  · exact kstBridgeToBottom_isCylinder _
  · exact isCylinder_iso_preimage _ (kstBridgeToBottom_isCylinder _)
  · exact isCylinder_iso_preimage _ (kstBridgeToBottom_isCylinder _)
  · exact isCylinder_iso_preimage _ (kstBridgeToBottom_isCylinder _)
  · exact horizontalRectangle_isCylinder _ _ _

theorem kstBridgeCoverPiece_isUpperSet (a : ℕ) (i : Fin 5) :
    IsUpperSet (kstBridgeCoverPiece a i) := by
  fin_cases i
  · exact kstBridgeToBottom_isUpperSet _
  · exact isUpperSet_iso_preimage _ (kstBridgeToBottom_isUpperSet _)
  · exact isUpperSet_iso_preimage _ (kstBridgeToBottom_isUpperSet _)
  · exact isUpperSet_iso_preimage _ (kstBridgeToBottom_isUpperSet _)
  · exact horizontalRectangle_isUpperSet _ _ _

/-- A bridge either ends on a top/bottom target, starts on one, or joins the
true vertical sides. This is the full geometric five-event cover. -/
theorem kst_bridge_five_cover (a : ℕ) :
    kstBridge (12*a) ⊆ ⋃ i, kstBridgeCoverPiece a i := by
  rintro ω ⟨u,v,p,_,hp,hu,hv,hbox⟩
  by_cases hvBottom : v.2 = -((12*a : ℕ) : ℤ)
  · exact Set.mem_iUnion.mpr ⟨0,by exact ⟨u,v,p,hp,hu,hv,hvBottom,hbox⟩⟩
  by_cases hvTop : v.2 = ((12*a : ℕ) : ℤ)
  · apply Set.mem_iUnion.mpr
    refine ⟨1,?_⟩
    change latticeConfigurationIsoHomeomorph kstReflectionYIso ω ∈ kstBridgeToBottom (12*a)
    refine ⟨_,_,p.map kstReflectionYIso.toHom,kstPathOpen_map_iso _ ω p hp,
      (kstBridgeLeft_y_reflection_iff _ _).mpr hu,
      (kstBridgeRight_y_reflection_iff _ _).mpr hv,?_,?_⟩
    · change -v.2 = -((12*a : ℕ) : ℤ)
      omega
    · exact kst_bridge_bounds_map_of_abs_coordinates kstReflectionYIso
        (fun z => by change |z.1| = |z.1| ∧ |-z.2| = |z.2|; simp only [abs_neg,and_self]) _ p hbox
  have hpR : kstPathOpen ω p.reverse := (kstPathOpen_reverse_iff ω p).mpr hp
  have hboxR : ∀ z ∈ p.reverse.support, 12*|z.1| ≤ 13*((12*a : ℕ) : ℤ) ∧ |z.2| ≤ ((12*a : ℕ) : ℤ) := by
    simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hbox
  by_cases huBottom : u.2 = -((12*a : ℕ) : ℤ)
  · apply Set.mem_iUnion.mpr
    refine ⟨2,?_⟩
    change latticeConfigurationIsoHomeomorph kstReflectionXIso ω ∈ kstBridgeToBottom (12*a)
    refine ⟨_,_,p.reverse.map kstReflectionXIso.toHom,kstPathOpen_map_iso _ ω p.reverse hpR,
      (kstBridgeRight_reflection_iff _ _).mpr hv,
      (kstBridgeLeft_reflection_iff _ _).mpr hu,huBottom,?_⟩
    exact kst_bridge_bounds_map_of_abs_coordinates kstReflectionXIso
      (fun z => by change |-z.1| = |z.1| ∧ |z.2| = |z.2|; simp only [abs_neg,and_self]) _ p.reverse hboxR
  by_cases huTop : u.2 = ((12*a : ℕ) : ℤ)
  · apply Set.mem_iUnion.mpr
    refine ⟨3,?_⟩
    change latticeConfigurationIsoHomeomorph kstReflectionBothIso ω ∈ kstBridgeToBottom (12*a)
    refine ⟨_,_,p.reverse.map kstReflectionBothIso.toHom,kstPathOpen_map_iso _ ω p.reverse hpR,?_,?_,?_,?_⟩
    · exact (kstBridgeLeft_y_reflection_iff _ _).mpr ((kstBridgeRight_reflection_iff _ _).mpr hv)
    · exact (kstBridgeRight_y_reflection_iff _ _).mpr ((kstBridgeLeft_reflection_iff _ _).mpr hu)
    · change -u.2 = -((12*a : ℕ) : ℤ)
      omega
    · exact kst_bridge_bounds_map_of_abs_coordinates kstReflectionBothIso
        (fun z => by change |-z.1| = |z.1| ∧ |-z.2| = |z.2|; simp only [abs_neg,and_self]) _ p.reverse hboxR
  have hdiv : 13*(12*a)/12 = 13*a := by omega
  have hux : u.1 = -13*(a : ℤ) := by
    rcases hu.2.2.2 with h | h
    · by_cases hz : 0 ≤ u.2
      · rw [abs_of_nonneg hz] at h
        exact (huTop h).elim
      · rw [abs_of_neg (by omega : u.2 < 0)] at h
        exact (huBottom (by omega)).elim
    · rw [hdiv] at h
      push_cast at h
      exact h
  have hvx : v.1 = 13*(a : ℤ) := by
    rcases hv.2.2.2 with h | h
    · by_cases hz : 0 ≤ v.2
      · rw [abs_of_nonneg hz] at h
        exact (hvTop h).elim
      · rw [abs_of_neg (by omega : v.2 < 0)] at h
        exact (hvBottom (by omega)).elim
    · rw [hdiv] at h
      push_cast at h
      exact h
  apply Set.mem_iUnion.mpr
  refine ⟨4,?_⟩
  apply horizontalRectangle_of_kst_open_walk _ _ _ ω p hp hux
  · change v.1 = -13*(a : ℤ)+(26*a : ℕ)
    push_cast
    omega
  · intro z hz
    have hh := hbox z hz
    push_cast at hh
    have habsx : |z.1| ≤ 13*(a : ℤ) := by omega
    have hxb := abs_le.mp habsx
    have hyb := abs_le.mp hh.2
    change -13*(a : ℤ) ≤ z.1 ∧ z.1 ≤ -13*(a : ℤ)+(26*a : ℕ) ∧
      -12*(a : ℤ) ≤ z.2 ∧ z.2 ≤ -12*(a : ℤ)+(24*a : ℕ)
    push_cast
    omega

end
end PottsContinuity.PlanarTopology
