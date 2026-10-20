/- Specializes the same explicit rectangle/Jordan construction as CentralTargetRectangle
   to KST alpha=1/64. All boundary indices and coordinates are recomputed. -/
module

public import PottsContinuity.PlanarTopology.RectanglePolygonDomain
public import PottsContinuity.PlanarTopology.RotatedPolygon
public import PottsContinuity.PlanarTopology.PolygonFourArcExistence

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- The alpha-target KST rectangle [-13k,13k] x [-12k,12k], starting at (-k,-12k)
and ordered counterclockwise in unit steps. -/
def alphaTargetRectanglePolygon (k : ℕ) (hk : 1 ≤ k) :
    FKC.LatticePolygon (2*(130*k)+2*(128*k)-3) :=
  rotateLatticePolygon
    (rectangleLatticePolygon (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k)
      (by omega) (by omega)) (64*k)

/-- Exact Jordan interior of the central-target polygon. -/
theorem alphaTargetRectanglePolygon_domain (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh) :
    (alphaTargetRectanglePolygon k hk).domain δ =
      complexOpenRectangle (δ.val*(-65*(k : ℤ) : ℤ)) (δ.val*(65*(k : ℤ) : ℤ))
        (δ.val*(-64*(k : ℤ) : ℤ)) (δ.val*(64*(k : ℤ) : ℤ)) := by
  unfold alphaTargetRectanglePolygon
  rw [rotateLatticePolygon_domain,
    rectangleLatticePolygon_domain _ _ _ (by omega) (by omega)]
  congr 1 <;> push_cast <;> ring

/-- Exact cyclic index shift from the central lower mark to the lower-left
rectangle corner convention, including the wrap at the left side's end. -/
theorem alphaTargetRectangle_index_val (k : ℕ) (hk : 1 ≤ k)
    (i : ZMod ((2*(130*k)+2*(128*k)-3)+3)) :
    ((64*k : ZMod ((2*(130*k)+2*(128*k)-3)+3))+i).val =
      if i.val < 452*k then i.val+64*k else i.val-452*k := by
  have : NeZero ((2*(130*k)+2*(128*k)-3)+3) := ⟨by omega⟩
  have hn : (2*(130*k)+2*(128*k)-3)+3 = 516*k := by omega
  have hi := ZMod.val_lt i
  rw [ZMod.val_add]
  have h12 : (64*k : ℕ) < (2*(130*k)+2*(128*k)-3)+3 := by omega
  rw [show (64*k : ZMod ((2*(130*k)+2*(128*k)-3)+3)).val = 64*k by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using ZMod.val_natCast_of_lt h12]
  conv_lhs => arg 2; rw [hn]
  split_ifs with hlt
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    omega

/-- The first 2k edges run exactly along the central lower target. -/
theorem alphaTargetRectangle_bottom_vertex (k : ℕ) (hk : 1 ≤ k)
    (i : ZMod ((2*(130*k)+2*(128*k)-3)+3)) (hi : i.val ≤ 2*k) :
    (alphaTargetRectanglePolygon k hk).vertex i =
      (-(k : ℤ)+(i.val : ℤ),-64*(k : ℤ)) := by
  change rectanglePolygonVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k)
    (by omega) (by omega) ((64*k : ZMod ((2*(130*k)+2*(128*k)-3)+3))+i) = _
  simp only [rectanglePolygonVertex,alphaTargetRectangle_index_val k hk i]
  have hlt : i.val < 452*k := by omega
  rw [ite_eq_left hlt]
  split_ifs <;> apply Prod.ext <;> dsimp <;> omega

/-- Indices 50k through 52k run from the right to the left endpoint of the
central upper target. -/
theorem alphaTargetRectangle_top_vertex (k : ℕ) (hk : 1 ≤ k)
    (i : ZMod ((2*(130*k)+2*(128*k)-3)+3))
    (hi0 : 258*k ≤ i.val) (hi1 : i.val ≤ 260*k) :
    (alphaTargetRectanglePolygon k hk).vertex i =
      (259*(k : ℤ)-(i.val : ℤ),64*(k : ℤ)) := by
  change rectanglePolygonVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k)
    (by omega) (by omega) ((64*k : ZMod ((2*(130*k)+2*(128*k)-3)+3))+i) = _
  simp only [rectanglePolygonVertex,alphaTargetRectangle_index_val k hk i]
  have hlt : i.val < 452*k := by omega
  rw [ite_eq_left hlt]
  split_ifs <;> apply Prod.ext <;> dsimp <;> omega

/-- The initial wired vertex arc is exactly the central lower target,
including its two endpoints. -/
theorem alphaTargetRectangle_bottom_arc_iff (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh)
    (v : FKC.DomainVertex δ ((alphaTargetRectanglePolygon k hk).domain δ)) :
    v ∈ (alphaTargetRectanglePolygon k hk).forwardArcVertices δ 0 (2*k) ↔
      v.val.2 = -64*(k : ℤ) ∧ -(k : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (k : ℤ) := by
  let P := alphaTargetRectanglePolygon k hk
  rw [P.mem_forwardArcVertices_iff δ 0 (by omega)]
  constructor
  · rintro ⟨t,ht,hv⟩
    have htn : t < (2*(130*k)+2*(128*k)-3)+3 := by omega
    have htv : (t : ZMod ((2*(130*k)+2*(128*k)-3)+3)).val = t :=
      ZMod.val_natCast_of_lt htn
    have hc := alphaTargetRectangle_bottom_vertex k hk (t : ZMod _) (by rw [htv]; exact ht)
    have he : P.vertex (t : ZMod _) = v.val := by
      simpa only [FKC.LatticePolygon.boundaryVertex_val,zero_add] using congrArg Subtype.val hv
    change (alphaTargetRectanglePolygon k hk).vertex _ = _ at he
    rw [hc] at he
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp only [Prod.fst,Prod.snd] at hx hy
    rw [htv] at hx
    omega
  · rintro ⟨hy,hx0,hx1⟩
    let t := (v.val.1+(k : ℤ)).toNat
    have ht : t ≤ 2*k := by dsimp [t]; omega
    have htn : t < (2*(130*k)+2*(128*k)-3)+3 := by omega
    have htv : (t : ZMod ((2*(130*k)+2*(128*k)-3)+3)).val = t :=
      ZMod.val_natCast_of_lt htn
    refine ⟨t,ht,Subtype.ext ?_⟩
    simp only [FKC.LatticePolygon.boundaryVertex_val,zero_add]
    change (alphaTargetRectanglePolygon k hk).vertex _ = _
    rw [alphaTargetRectangle_bottom_vertex k hk _ (by rw [htv]; exact ht),htv]
    apply Prod.ext <;> dsimp [t] <;> omega

/-- The second closed cyclic vertex interval is exactly the central upper
target, including its two endpoints. -/
theorem alphaTargetRectangle_top_arc_iff (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh)
    (v : FKC.DomainVertex δ ((alphaTargetRectanglePolygon k hk).domain δ)) :
    v ∈ polygonBoundaryVertices (alphaTargetRectanglePolygon k hk) δ
      {j | 258*k ≤ j.val ∧ j.val ≤ 260*k} ↔
      v.val.2 = 64*(k : ℤ) ∧ -(k : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (k : ℤ) := by
  constructor
  · rintro ⟨i,hi,hv⟩
    have hc := alphaTargetRectangle_top_vertex k hk i hi.1 hi.2
    have he : (alphaTargetRectanglePolygon k hk).vertex i = v.val := congrArg Subtype.val hv
    rw [hc] at he
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp only [Prod.fst,Prod.snd] at hx hy
    change 258*k ≤ i.val ∧ i.val ≤ 260*k at hi
    omega
  · rintro ⟨hy,hx0,hx1⟩
    let t := (259*(k : ℤ)-v.val.1).toNat
    have ht0 : 258*k ≤ t := by dsimp [t]; omega
    have ht1 : t ≤ 260*k := by dsimp [t]; omega
    have htn : t < (2*(130*k)+2*(128*k)-3)+3 := by omega
    have htv : (t : ZMod ((2*(130*k)+2*(128*k)-3)+3)).val = t :=
      ZMod.val_natCast_of_lt htn
    refine ⟨(t : ZMod _),⟨by simpa only [htv] using ht0,by simpa only [htv] using ht1⟩,
      Subtype.ext ?_⟩
    change (alphaTargetRectanglePolygon k hk).vertex _ = _
    rw [alphaTargetRectangle_top_vertex k hk _ (by rw [htv]; exact ht0)
      (by rw [htv]; exact ht1),htv]
    apply Prod.ext <;> dsimp [t] <;> omega

/-- Alpha-target dual existence on the IDENTIFIED rectangle domain graph.
The dual endpoint arcs are still expressed by their exact cyclic edge indices;
identifying these faces with the PD rectangle's explicit B/D coordinate ports
is a separate consumer bridge. -/
theorem alphaTargetRectangle_indexed_dual_exists (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh)
    (C : FKC.FiniteFK.Configuration
      (FKC.domainLatticeGraph δ ((alphaTargetRectanglePolygon k hk).domain δ)))
    (hno : ¬∃ u : FKC.DomainVertex δ ((alphaTargetRectanglePolygon k hk).domain δ),
      (u.val.2 = -64*(k : ℤ) ∧ -(k : ℤ) ≤ u.val.1 ∧ u.val.1 ≤ (k : ℤ)) ∧
      ∃ v : FKC.DomainVertex δ ((alphaTargetRectanglePolygon k hk).domain δ),
        (v.val.2 = 64*(k : ℤ) ∧ -(k : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (k : ℤ)) ∧
        FKC.FiniteFK.ActualConnected _ C u v) :
    ∃ x ∈ polygonExteriorFaces (alphaTargetRectanglePolygon k hk) δ
        {i | 260*k ≤ i.val},
      ∃ y ∈ polygonExteriorFaces (alphaTargetRectanglePolygon k hk) δ
        {i | 2*k ≤ i.val ∧ i.val < 258*k}, (domainClosedDualGraph C).Reachable x y := by
  apply polygon_four_arc_dual_exists_of_no_primal (alphaTargetRectanglePolygon k hk)
    δ (2*k) (258*k) (260*k) (by omega) (by omega) (by omega) (by omega) C
  rintro ⟨u,hu,v,hv,huv⟩
  exact hno ⟨u,(alphaTargetRectangle_bottom_arc_iff k hk δ u).mp hu,
    v,(alphaTargetRectangle_top_arc_iff k hk δ v).mp hv,huv⟩

/-- The five half-open unit-step sides in the central-mark convention.
The lower side is split by the cyclic start; the other three sides are whole. -/
theorem alphaTargetRectangle_vertex (k : ℕ) (hk : 1 ≤ k)
    (i : ZMod ((2*(130*k)+2*(128*k)-3)+3)) :
    (alphaTargetRectanglePolygon k hk).vertex i =
      if i.val < 66*k then (-(k : ℤ)+(i.val : ℤ),-64*(k : ℤ))
      else if i.val < 194*k then (65*(k : ℤ),(i.val : ℤ)-130*(k : ℤ))
      else if i.val < 324*k then (259*(k : ℤ)-(i.val : ℤ),64*(k : ℤ))
      else if i.val < 452*k then (-65*(k : ℤ),388*(k : ℤ)-(i.val : ℤ))
      else ((i.val : ℤ)-517*(k : ℤ),-64*(k : ℤ)) := by
  have : NeZero ((2*(130*k)+2*(128*k)-3)+3) := ⟨by omega⟩
  have hi := ZMod.val_lt i
  change rectanglePolygonVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k)
    (by omega) (by omega) ((64*k : ZMod ((2*(130*k)+2*(128*k)-3)+3))+i) = _
  simp only [rectanglePolygonVertex,alphaTargetRectangle_index_val k hk i]
  split_ifs <;> apply Prod.ext <;> dsimp <;> omega

end PottsContinuity.PlanarTopology
