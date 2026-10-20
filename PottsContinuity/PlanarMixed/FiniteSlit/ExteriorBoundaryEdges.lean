module

public import PottsContinuity.PlanarMixed.FiniteSlit.SourceExteriorGraph

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK
noncomputable section

/-- A reference bond from a source vertex to the left exterior meets exactly
the left or upper-left source boundary. -/
theorem left_exterior_neighbor_portal (M : ℕ) (x y : ℤ) (w h : ℕ) (hM : 2 ≤ M)
    (_hx : 1 ≤ x) (hxw : x ≤ (w:ℤ)) (a b : Vertex M x)
    (u : RectangleVertex (0,0) w h) (ha : a.val = u.val)
    (hab : (graph M x y).Adj a b)
    (hb : exteriorProjection M x w h b = Sum.inr false) :
    u ∈ sourceLeftPortal w h x := by
  have hu := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
  have hb' := (exteriorProjection_eq_left_iff M x w h b).mp hb
  have hout := (outside_source_iff M x w h (by omega) b).mp hb'.1
  have hsq := hab.1
  change PD.FK.squareLattice.Adj a.val b.val at hsq
  rw [ha,PD.FK.squareLattice_adj_iff] at hsq
  change u.val.1 = 0 ∨ (u.val.2 = (h:ℤ) ∧ u.val.1 < x)
  dsimp at hu
  omega

/-- The right exterior attaches precisely at the right or upper-right boundary. -/
theorem right_exterior_neighbor_portal (M : ℕ) (x y : ℤ) (w h : ℕ) (hM : 2 ≤ M)
    (hx : 1 ≤ x) (_hxw : x ≤ (w:ℤ)) (a b : Vertex M x)
    (u : RectangleVertex (0,0) w h) (ha : a.val = u.val)
    (hab : (graph M x y).Adj a b)
    (hb : exteriorProjection M x w h b = Sum.inr true) :
    u ∈ sourceRightPortal w h x := by
  have hu := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
  have hb' := (exteriorProjection_eq_right_iff M x w h b).mp hb
  have hout := (outside_source_iff M x w h (by omega) b).mp hb'.1
  have hsq := hab.1
  change PD.FK.squareLattice.Adj a.val b.val at hsq
  rw [ha,PD.FK.squareLattice_adj_iff] at hsq
  change u.val.1 = (w:ℤ) ∨ (u.val.2 = (h:ℤ) ∧ x ≤ u.val.1)
  dsimp at hu
  omega

/-- Once the slit reaches the source top, no retained bond joins the two
outside components. The omitted seam bond is strictly above the tip. -/
theorem opposite_exteriors_not_adj (M : ℕ) (x y : ℤ) (w h : ℕ) (hM : 2 ≤ M)
    (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ)) (hyh : y ≤ (h:ℤ)) (a b : Vertex M x)
    (ha : exteriorProjection M x w h a = Sum.inr false)
    (hb : exteriorProjection M x w h b = Sum.inr true) :
    ¬ (graph M x y).Adj a b := by
  intro hab
  have ha' := (exteriorProjection_eq_left_iff M x w h a).mp ha
  have hb' := (exteriorProjection_eq_right_iff M x w h b).mp hb
  have hout := (outside_source_iff M x w h (by omega) a).mp ha'.1
  have hsq := hab.1
  have hcut := hab.2
  change PD.FK.squareLattice.Adj a.val b.val at hsq
  rw [PD.FK.squareLattice_adj_iff] at hsq
  change ¬ (y < a.val.2 ∧ y < b.val.2 ∧
    ((a.val.1 = x-1 ∧ b.val.1 = x) ∨ (b.val.1 = x-1 ∧ a.val.1 = x))) at hcut
  omega

/-- The collapsed graph retains exactly the original source slit bonds
between original source vertices. -/
theorem exteriorProjection_map_source_adj_iff (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 1 ≤ M) (hleft : x-(M:ℤ) ≤ 0) (hright : (w:ℤ) ≤ x+(M:ℤ)-1)
    (hheight : h ≤ M) (u v : RectangleVertex (0,0) w h) :
    ((graph M x y).map (exteriorProjection M x w h)).Adj (Sum.inl u) (Sum.inl v) ↔
      (sourceRetainedGraph w h x y).Adj u v := by
  constructor
  · intro hadj
    obtain ⟨_,a,b,hab,ha,hb⟩ := (SimpleGraph.map_adj' _ _ _ _).mp hadj
    have hau := (exteriorProjection_eq_inl_iff M x w h a u).mp ha
    have hbv := (exteriorProjection_eq_inl_iff M x w h b v).mp hb
    have hh := (graph_adj_iff_retained M x y a b).mp hab
    change (slitRetainedBondGraph x y).Adj u.val v.val
    simpa only [hau,hbv] using hh
  · intro huv
    let f := rectangleIntoReference M x w h hM hleft hright hheight
    apply (SimpleGraph.map_adj' _ _ _ _).mpr
    refine ⟨?_,f u,f v,?_,?_,?_⟩
    · intro he
      exact huv.ne (Sum.inl.inj he)
    · exact (graph_adj_iff_retained M x y (f u) (f v)).mpr huv
    · exact exteriorProjection_rectangleIntoReference M x w h hM hleft hright hheight u
    · exact exteriorProjection_rectangleIntoReference M x w h hM hleft hright hheight v

end
end PottsContinuity.PlanarMixed.FiniteSlit
