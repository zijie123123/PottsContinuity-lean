module

public import PottsContinuity.PlanarTopology.RectanglePolygonDomain
public import PottsContinuity.PlanarTopology.RotatedPolygon
public import PottsContinuity.PlanarTopology.PolygonFourArcExistence

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- The KST rectangle [-13k,13k] x [-12k,12k], starting at (-k,-12k)
and ordered counterclockwise in unit steps. -/
def centralTargetRectanglePolygon (k : ℕ) (hk : 1 ≤ k) :
    FKC.LatticePolygon (2*(26*k)+2*(24*k)-3) :=
  rotateLatticePolygon
    (rectangleLatticePolygon (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k)
      (by omega) (by omega)) (12*k)

/-- Exact Jordan interior of the central-target polygon. -/
theorem centralTargetRectanglePolygon_domain (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh) :
    (centralTargetRectanglePolygon k hk).domain δ =
      complexOpenRectangle (δ.val*(-13*(k : ℤ) : ℤ)) (δ.val*(13*(k : ℤ) : ℤ))
        (δ.val*(-12*(k : ℤ) : ℤ)) (δ.val*(12*(k : ℤ) : ℤ)) := by
  unfold centralTargetRectanglePolygon
  rw [rotateLatticePolygon_domain,
    rectangleLatticePolygon_domain _ _ _ (by omega) (by omega)]
  congr 1 <;> push_cast <;> ring

/-- Exact cyclic index shift from the central lower mark to the lower-left
rectangle corner convention, including the wrap at the left side's end. -/
theorem centralTargetRectangle_index_val (k : ℕ) (hk : 1 ≤ k)
    (i : ZMod ((2*(26*k)+2*(24*k)-3)+3)) :
    ((12*k : ZMod ((2*(26*k)+2*(24*k)-3)+3))+i).val =
      if i.val < 88*k then i.val+12*k else i.val-88*k := by
  have : NeZero ((2*(26*k)+2*(24*k)-3)+3) := ⟨by omega⟩
  have hn : (2*(26*k)+2*(24*k)-3)+3 = 100*k := by omega
  have hi := ZMod.val_lt i
  rw [ZMod.val_add]
  have h12 : (12*k : ℕ) < (2*(26*k)+2*(24*k)-3)+3 := by omega
  rw [show (12*k : ZMod ((2*(26*k)+2*(24*k)-3)+3)).val = 12*k by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using ZMod.val_natCast_of_lt h12]
  conv_lhs => arg 2; rw [hn]
  split_ifs with hlt
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    omega

/-- The first 2k edges run exactly along the central lower target. -/
theorem centralTargetRectangle_bottom_vertex (k : ℕ) (hk : 1 ≤ k)
    (i : ZMod ((2*(26*k)+2*(24*k)-3)+3)) (hi : i.val ≤ 2*k) :
    (centralTargetRectanglePolygon k hk).vertex i =
      (-(k : ℤ)+(i.val : ℤ),-12*(k : ℤ)) := by
  change rectanglePolygonVertex (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k)
    (by omega) (by omega) ((12*k : ZMod ((2*(26*k)+2*(24*k)-3)+3))+i) = _
  simp only [rectanglePolygonVertex,centralTargetRectangle_index_val k hk i]
  have hlt : i.val < 88*k := by omega
  rw [ite_eq_left hlt]
  split_ifs <;> apply Prod.ext <;> dsimp <;> omega

/-- Indices 50k through 52k run from the right to the left endpoint of the
central upper target. -/
theorem centralTargetRectangle_top_vertex (k : ℕ) (hk : 1 ≤ k)
    (i : ZMod ((2*(26*k)+2*(24*k)-3)+3))
    (hi0 : 50*k ≤ i.val) (hi1 : i.val ≤ 52*k) :
    (centralTargetRectanglePolygon k hk).vertex i =
      (51*(k : ℤ)-(i.val : ℤ),12*(k : ℤ)) := by
  change rectanglePolygonVertex (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k)
    (by omega) (by omega) ((12*k : ZMod ((2*(26*k)+2*(24*k)-3)+3))+i) = _
  simp only [rectanglePolygonVertex,centralTargetRectangle_index_val k hk i]
  have hlt : i.val < 88*k := by omega
  rw [ite_eq_left hlt]
  split_ifs <;> apply Prod.ext <;> dsimp <;> omega

/-- The initial wired vertex arc is exactly the central lower target,
including its two endpoints. -/
theorem centralTargetRectangle_bottom_arc_iff (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh)
    (v : FKC.DomainVertex δ ((centralTargetRectanglePolygon k hk).domain δ)) :
    v ∈ (centralTargetRectanglePolygon k hk).forwardArcVertices δ 0 (2*k) ↔
      v.val.2 = -12*(k : ℤ) ∧ -(k : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (k : ℤ) := by
  let P := centralTargetRectanglePolygon k hk
  rw [P.mem_forwardArcVertices_iff δ 0 (by omega)]
  constructor
  · rintro ⟨t,ht,hv⟩
    have htn : t < (2*(26*k)+2*(24*k)-3)+3 := by omega
    have htv : (t : ZMod ((2*(26*k)+2*(24*k)-3)+3)).val = t :=
      ZMod.val_natCast_of_lt htn
    have hc := centralTargetRectangle_bottom_vertex k hk (t : ZMod _) (by rw [htv]; exact ht)
    have he : P.vertex (t : ZMod _) = v.val := by
      simpa only [FKC.LatticePolygon.boundaryVertex_val,zero_add] using congrArg Subtype.val hv
    change (centralTargetRectanglePolygon k hk).vertex _ = _ at he
    rw [hc] at he
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp only [Prod.fst,Prod.snd] at hx hy
    rw [htv] at hx
    omega
  · rintro ⟨hy,hx0,hx1⟩
    let t := (v.val.1+(k : ℤ)).toNat
    have ht : t ≤ 2*k := by dsimp [t]; omega
    have htn : t < (2*(26*k)+2*(24*k)-3)+3 := by omega
    have htv : (t : ZMod ((2*(26*k)+2*(24*k)-3)+3)).val = t :=
      ZMod.val_natCast_of_lt htn
    refine ⟨t,ht,Subtype.ext ?_⟩
    simp only [FKC.LatticePolygon.boundaryVertex_val,zero_add]
    change (centralTargetRectanglePolygon k hk).vertex _ = _
    rw [centralTargetRectangle_bottom_vertex k hk _ (by rw [htv]; exact ht),htv]
    apply Prod.ext <;> dsimp [t] <;> omega

/-- The second closed cyclic vertex interval is exactly the central upper
target, including its two endpoints. -/
theorem centralTargetRectangle_top_arc_iff (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh)
    (v : FKC.DomainVertex δ ((centralTargetRectanglePolygon k hk).domain δ)) :
    v ∈ polygonBoundaryVertices (centralTargetRectanglePolygon k hk) δ
      {j | 50*k ≤ j.val ∧ j.val ≤ 52*k} ↔
      v.val.2 = 12*(k : ℤ) ∧ -(k : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (k : ℤ) := by
  constructor
  · rintro ⟨i,hi,hv⟩
    have hc := centralTargetRectangle_top_vertex k hk i hi.1 hi.2
    have he : (centralTargetRectanglePolygon k hk).vertex i = v.val := congrArg Subtype.val hv
    rw [hc] at he
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp only [Prod.fst,Prod.snd] at hx hy
    change 50*k ≤ i.val ∧ i.val ≤ 52*k at hi
    omega
  · rintro ⟨hy,hx0,hx1⟩
    let t := (51*(k : ℤ)-v.val.1).toNat
    have ht0 : 50*k ≤ t := by dsimp [t]; omega
    have ht1 : t ≤ 52*k := by dsimp [t]; omega
    have htn : t < (2*(26*k)+2*(24*k)-3)+3 := by omega
    have htv : (t : ZMod ((2*(26*k)+2*(24*k)-3)+3)).val = t :=
      ZMod.val_natCast_of_lt htn
    refine ⟨(t : ZMod _),⟨by simpa only [htv] using ht0,by simpa only [htv] using ht1⟩,
      Subtype.ext ?_⟩
    change (centralTargetRectanglePolygon k hk).vertex _ = _
    rw [centralTargetRectangle_top_vertex k hk _ (by rw [htv]; exact ht0)
      (by rw [htv]; exact ht1),htv]
    apply Prod.ext <;> dsimp [t] <;> omega

/-- Central-target dual existence on the IDENTIFIED rectangle domain graph.
The dual endpoint arcs are still expressed by their exact cyclic edge indices;
identifying these faces with the PD rectangle's explicit B/D coordinate ports
is a separate consumer bridge. -/
theorem centralTargetRectangle_indexed_dual_exists (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh)
    (C : FKC.FiniteFK.Configuration
      (FKC.domainLatticeGraph δ ((centralTargetRectanglePolygon k hk).domain δ)))
    (hno : ¬∃ u : FKC.DomainVertex δ ((centralTargetRectanglePolygon k hk).domain δ),
      (u.val.2 = -12*(k : ℤ) ∧ -(k : ℤ) ≤ u.val.1 ∧ u.val.1 ≤ (k : ℤ)) ∧
      ∃ v : FKC.DomainVertex δ ((centralTargetRectanglePolygon k hk).domain δ),
        (v.val.2 = 12*(k : ℤ) ∧ -(k : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (k : ℤ)) ∧
        FKC.FiniteFK.ActualConnected _ C u v) :
    ∃ x ∈ polygonExteriorFaces (centralTargetRectanglePolygon k hk) δ
        {i | 52*k ≤ i.val},
      ∃ y ∈ polygonExteriorFaces (centralTargetRectanglePolygon k hk) δ
        {i | 2*k ≤ i.val ∧ i.val < 50*k}, (domainClosedDualGraph C).Reachable x y := by
  apply polygon_four_arc_dual_exists_of_no_primal (centralTargetRectanglePolygon k hk)
    δ (2*k) (50*k) (52*k) (by omega) (by omega) (by omega) (by omega) C
  rintro ⟨u,hu,v,hv,huv⟩
  exact hno ⟨u,(centralTargetRectangle_bottom_arc_iff k hk δ u).mp hu,
    v,(centralTargetRectangle_top_arc_iff k hk δ v).mp hv,huv⟩

/-- The five half-open unit-step sides in the central-mark convention.
The lower side is split by the cyclic start; the other three sides are whole. -/
theorem centralTargetRectangle_vertex (k : ℕ) (hk : 1 ≤ k)
    (i : ZMod ((2*(26*k)+2*(24*k)-3)+3)) :
    (centralTargetRectanglePolygon k hk).vertex i =
      if i.val < 14*k then (-(k : ℤ)+(i.val : ℤ),-12*(k : ℤ))
      else if i.val < 38*k then (13*(k : ℤ),(i.val : ℤ)-26*(k : ℤ))
      else if i.val < 64*k then (51*(k : ℤ)-(i.val : ℤ),12*(k : ℤ))
      else if i.val < 88*k then (-13*(k : ℤ),76*(k : ℤ)-(i.val : ℤ))
      else ((i.val : ℤ)-101*(k : ℤ),-12*(k : ℤ)) := by
  have : NeZero ((2*(26*k)+2*(24*k)-3)+3) := ⟨by omega⟩
  have hi := ZMod.val_lt i
  change rectanglePolygonVertex (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k)
    (by omega) (by omega) ((12*k : ZMod ((2*(26*k)+2*(24*k)-3)+3))+i) = _
  simp only [rectanglePolygonVertex,centralTargetRectangle_index_val k hk i]
  split_ifs <;> apply Prod.ext <;> dsimp <;> omega

end PottsContinuity.PlanarTopology
