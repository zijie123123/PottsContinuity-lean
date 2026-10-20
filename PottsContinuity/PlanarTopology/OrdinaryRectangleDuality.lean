module

public import PottsContinuity.PlanarTopology.WholePlaneRectangleExclusion
public import PottsContinuity.PlanarTopology.OpenWalkEmbedding
public import PottsContinuity.PlanarTopology.RectangleTranspose
public import PottsContinuity.BD12.WholePlaneRectangleDuality

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.RCInfinite BD12
noncomputable section

/-- An ordinary vertical crossing gives an original open lattice walk with
literal rectangle bounds and both sampled side endpoints retained. -/
theorem kst_vertical_crossing_witness (a : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) (hω : ω ∈ verticalRectangle a w h) :
    ∃ (u v : LatticeVertex) (p : PD.squareLattice.Walk u v),
      kstPathOpen ω p ∧ u.2 = a.2 ∧ v.2 = a.2+(h:ℤ) ∧
      kstPathIn p a.1 (a.1+(w:ℤ)) a.2 (a.2+(h:ℤ)) := by
  obtain ⟨u,v,hu,hv,⟨p⟩⟩ := hω
  let f : (PD.rcInfiniteOpenGraph ω).induce (PD.FK.latticeRectangle a w h : Set LatticeVertex) →g
      PD.rcInfiniteOpenGraph ω := { toFun := Subtype.val, map_rel' := fun h => h }
  refine ⟨u.val,v.val,(p.map f).mapLe (rcOpenGraph_le_squareLattice ω),
    kstPathOpen_of_rcOpen_walk ω (p.map f),hu,hv,?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_mapLe_eq_support,SimpleGraph.Walk.support_map] at hz
  obtain ⟨q,_,hq⟩ := List.mem_map.mp hz
  have hh := (mem_latticeRectangle a q.val w h).mp q.property
  change q.val = z at hq
  rw [← hq]
  exact ⟨hh.1.1,hh.1.2,hh.2⟩

/-- The complement of an actual horizontal crossing is an ordinary dual
vertical crossing of the exact expanded face strip, including the offsets. -/
theorem horizontalRectangle_compl_eq_dual_vertical (a : LatticeVertex) (n h : ℕ) :
    (horizontalRectangle a (n+1) h)ᶜ = wholePlaneDualConfigurationHomeomorph ⁻¹'
      verticalRectangle (a.1,a.2-1) n (h+1) := by
  ext ω
  constructor
  · intro hn
    rw [horizontalRectangle_compl] at hn
    exact dualPortRectangle_subset_vertical a n h hn
  · intro hv hp
    obtain ⟨u,v,p,_,hpo,hu,hv',hpB⟩ := kst_horizontal_crossing_witness a (n+1) h ω hp
    obtain ⟨x,y,q,hqo,hx,hy,hqB⟩ := kst_vertical_crossing_witness (a.1,a.2-1) n (h+1)
      (wholePlaneDualConfigurationHomeomorph ω) hv
    apply wholePlane_rectangle_crossings_exclusive a (n+1) h (by omega) ω p q hpo hqo hpB
      _ hu hv' hx _
    · intro z hz
      have hh := hqB z hz
      dsimp at hh ⊢
      omega
    · dsimp at hy ⊢
      omega

/-- The vertical complement uses the transposed exact strip, with the left
face-base offset and the two unequal integral side lengths. -/
theorem verticalRectangle_compl_eq_dual_horizontal (a : LatticeVertex) (w n : ℕ) :
    (verticalRectangle a w (n+1))ᶜ = wholePlaneDualConfigurationHomeomorph ⁻¹'
      horizontalRectangle (a.1-1,a.2) (w+1) n := by
  have htrans : (verticalRectangle a w (n+1))ᶜ =
      latticeConfigurationIsoHomeomorph latticeTransposeIso ⁻¹'
        (horizontalRectangle a.swap (n+1) w)ᶜ := by
    rw [Set.preimage_compl,horizontalRectangle_transpose_preimage]
  rw [htrans,horizontalRectangle_compl_eq_dual_vertical]
  ext ω
  change wholePlaneDualConfigurationHomeomorph
      (latticeConfigurationIsoHomeomorph latticeTransposeIso ω) ∈
      verticalRectangle (a.2,a.1-1) n (w+1) ↔ _
  rw [wholePlaneDualConfiguration_transpose]
  exact Set.ext_iff.mp (verticalRectangle_transpose_preimage (a.1-1,a.2) (w+1) n)
    (wholePlaneDualConfigurationHomeomorph ω)

end
end PottsContinuity.PlanarTopology
