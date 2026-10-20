module

public import PottsContinuity.Thm3.RSW.PolygonHorizontalExtent
public import PottsContinuity.Thm3.RSW.PolygonOuterBox
public import PottsContinuity.Thm3.RSW.PolygonPaths

@[expose] public section

namespace PottsContinuity.RSW

/-- A genuine surrounding annulus circuit contains two sampled connected
vertices whose horizontal separation exceeds the inner radius. -/
theorem annulusCircuitEvent_has_long_connection
    (V : Finset (ℤ × ℤ)) (n : ℕ)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool)
    (hω : ω ∈ annulusCircuitEvent V (0,0) n) :
    ∃ x ∈ box (2*n), ∃ y ∈ box (2*n),
      ω ∈ finiteConnectionEvent V x y ∧ (n:ℤ) < y.1-x.1 := by
  obtain ⟨m,P,hcenter,hradial,hopen⟩ := hω
  have hinner := latticePolygon_closed_inner_box_subset_domain P (0,0) n hcenter
    (fun i => (hradial i).1)
  have hpoint : FKC.latticeEmbed ⟨1,zero_lt_one⟩ ((n:ℤ),0) ∈
      P.domain ⟨1,zero_lt_one⟩ := by
    apply hinner
    apply latticeEmbed_mem_complexClosedBox (0,0) ((n:ℤ),0) n
    simp only [sub_zero,abs_of_nonneg (Int.natCast_nonneg n),
      abs_zero,max_eq_left (Int.natCast_nonneg n)]
    exact le_rfl
  obtain ⟨i,hi⟩ := latticePolygon_exists_vertex_right_of_center P ((n:ℤ),0) hpoint
  obtain ⟨j,hj⟩ := latticePolygon_exists_vertex_left_of_center P (0,0) hcenter
  have hV : ∀ i, P.vertex i ∈ V := fun i => (hopen i).choose
  have hbox : ∀ i, P.vertex i ∈ box (2*n) := by
    intro i
    apply (Foundations.mem_box_iff_abs_le (2*n) _).mpr
    have h := (hradial i).2
    simp only [sub_zero] at h
    have h' : max |(P.vertex i).1| |(P.vertex i).2| ≤ ((2*n:ℕ):ℤ) := by
      exact_mod_cast h
    exact ⟨(le_max_left _ _).trans h',(le_max_right _ _).trans h'⟩
  refine ⟨P.vertex j,hbox j,P.vertex i,hbox i,?_,?_⟩
  · exact finitePathEvent_subset_connection V V _ _
      (open_polygon_finitePathEvent V V ω P hopen hV j i)
  · simp only at hi hj
    omega

end PottsContinuity.RSW
