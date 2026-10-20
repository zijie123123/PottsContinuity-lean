module

public import PottsContinuity.Thm3.RSW.PathInterlacing
public import PottsContinuity.PD.FK.Lattice
public import PottsContinuity.Frozen.Defs

/-!
# Interpolation and actual lattice-vertex intersections

The interpolation follows PD/Duality/LatticeWalkInterpolation.lean, using real
coordinate pairs instead of complex numbers. For unit horizontal/vertical bonds,
intersecting segments have a common endpoint. Thus a continuous intersection
of the interpolated walks yields a vertex of both original supports.
-/

@[expose] public section

namespace PottsContinuity.RSW

open Set

/-- The literal coordinate embedding into the real plane. -/
def latticePairEmbed (v : ℤ × ℤ) : ℝ × ℝ := ((v.1 : ℝ), (v.2 : ℝ))

/-- Linear interpolation retaining the order and repeated visits of a walk. -/
noncomputable def latticePairWalkPath : {u v : ℤ × ℤ} →
    squareLattice.Walk u v → Path (latticePairEmbed u) (latticePairEmbed v)
  | _, _, .nil => Path.refl _
  | u, _, .cons (v := v) _ p =>
      (Path.segment (latticePairEmbed u) (latticePairEmbed v)).trans
        (latticePairWalkPath p)

/-- Every interpolated point is on a unit bond or a degenerate vertex segment
whose endpoints are both visited by the actual walk. -/
theorem latticePairWalkPath_range_segments {u v : ℤ × ℤ}
    (p : squareLattice.Walk u v) {z : ℝ × ℝ}
    (hz : z ∈ Set.range (latticePairWalkPath p)) :
    ∃ x y : ℤ × ℤ, x ∈ p.support ∧ y ∈ p.support ∧
      (x = y ∨ squareLattice.Adj x y) ∧
      z ∈ Set.range (Path.segment (latticePairEmbed x) (latticePairEmbed y)) := by
  induction p with
  | @nil u0 =>
    obtain ⟨t, rfl⟩ := hz
    refine ⟨u0, u0, by simp, by simp, Or.inl rfl, ?_⟩
    rw [Path.range_segment]
    exact left_mem_segment ℝ _ _
  | @cons u v w h p ih =>
    change z ∈ Set.range ((Path.segment (latticePairEmbed u) (latticePairEmbed v)).trans
      (latticePairWalkPath p)) at hz
    rw [Path.trans_range] at hz
    rcases hz with hz | hz
    · exact ⟨u, v, by simp, by simp [p.start_mem_support], Or.inr h, hz⟩
    · obtain ⟨x, y, hx, hy, hxy, hz⟩ := ih hz
      exact ⟨x, y, by simp [hx], by simp [hy], hxy, hz⟩

/-- Support coordinate bounds are retained throughout linear interpolation. -/
theorem latticePairWalkPath_bounds {u v : ℤ × ℤ} (p : squareLattice.Walk u v)
    (l r bot top : ℝ)
    (hp : ∀ x ∈ p.support, l ≤ (x.1 : ℝ) ∧ (x.1 : ℝ) ≤ r ∧
      bot ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ top) :
    ∀ z ∈ Set.range (latticePairWalkPath p),
      l ≤ z.1 ∧ z.1 ≤ r ∧ bot ≤ z.2 ∧ z.2 ≤ top := by
  intro z hz
  obtain ⟨x, y, hx, hy, _, hz⟩ := latticePairWalkPath_range_segments p hz
  exact segment_xy_bounds (hp x hx) (hp y hy) hz

private theorem unit_bond_boxes_common_endpoint (u v s t : ℤ × ℤ)
    (huv : u = v ∨ squareLattice.Adj u v) (hst : s = t ∨ squareLattice.Adj s t)
    (hx : min u.1 v.1 ≤ max s.1 t.1) (hx' : min s.1 t.1 ≤ max u.1 v.1)
    (hy : min u.2 v.2 ≤ max s.2 t.2) (hy' : min s.2 t.2 ≤ max u.2 v.2) :
    u = s ∨ u = t ∨ v = s ∨ v = t := by
  have horient (x y : ℤ × ℤ) (h : x = y ∨ squareLattice.Adj x y) :
      (x.1 = y.1 ∧ x.2 = y.2) ∨
      ((x.1 + 1 = y.1 ∨ y.1 + 1 = x.1) ∧ x.2 = y.2) ∨
      (x.1 = y.1 ∧ (x.2 + 1 = y.2 ∨ y.2 + 1 = x.2)) := by
    rcases h with rfl | h
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ((PD.FK.squareLattice_adj_iff x y).mp h)
  have hu := horient u v huv
  have hs := horient s t hst
  simp only [Prod.ext_iff]
  rcases hu with ⟨hux, huy⟩ | ⟨hux | hux, huy⟩ | ⟨hux, huy | huy⟩
  all_goals rcases hs with ⟨hsx, hsy⟩ | ⟨hsx | hsx, hsy⟩ | ⟨hsx, hsy | hsy⟩
  all_goals omega

/-- Intersection of interpolated lattice walks forces a common actual vertex,
not merely a crossing of edges at a non-lattice point. -/
theorem latticePairWalkPath_common_vertex {u v s t : ℤ × ℤ}
    (p : squareLattice.Walk u v) (q : squareLattice.Walk s t)
    (z : ℝ × ℝ) (hp : z ∈ Set.range (latticePairWalkPath p))
    (hq : z ∈ Set.range (latticePairWalkPath q)) :
    ∃ x, x ∈ p.support ∧ x ∈ q.support := by
  obtain ⟨a, b, ha, hb, hab, hp⟩ := latticePairWalkPath_range_segments p hp
  obtain ⟨c, d, hc, hd, hcd, hq⟩ := latticePairWalkPath_range_segments q hq
  have hpbox := segment_xy_bounds
    (l := min (a.1 : ℝ) b.1) (r := max (a.1 : ℝ) b.1)
    (bot := min (a.2 : ℝ) b.2) (top := max (a.2 : ℝ) b.2)
    ⟨min_le_left _ _, le_max_left _ _, min_le_left _ _, le_max_left _ _⟩
    ⟨min_le_right _ _, le_max_right _ _, min_le_right _ _, le_max_right _ _⟩ hp
  have hqbox := segment_xy_bounds
    (l := min (c.1 : ℝ) d.1) (r := max (c.1 : ℝ) d.1)
    (bot := min (c.2 : ℝ) d.2) (top := max (c.2 : ℝ) d.2)
    ⟨min_le_left _ _, le_max_left _ _, min_le_left _ _, le_max_left _ _⟩
    ⟨min_le_right _ _, le_max_right _ _, min_le_right _ _, le_max_right _ _⟩ hq
  have hx : min a.1 b.1 ≤ max c.1 d.1 := by exact_mod_cast le_trans hpbox.1 hqbox.2.1
  have hx' : min c.1 d.1 ≤ max a.1 b.1 := by exact_mod_cast le_trans hqbox.1 hpbox.2.1
  have hy : min a.2 b.2 ≤ max c.2 d.2 := by exact_mod_cast le_trans hpbox.2.2.1 hqbox.2.2.2
  have hy' : min c.2 d.2 ≤ max a.2 b.2 := by exact_mod_cast le_trans hqbox.2.2.1 hpbox.2.2.2
  rcases unit_bond_boxes_common_endpoint a b c d hab hcd hx hx' hy hy' with h | h | h | h
  · exact ⟨a, ha, h ▸ hc⟩
  · exact ⟨a, ha, h ▸ hd⟩
  · exact ⟨b, hb, h ▸ hc⟩
  · exact ⟨b, hb, h ▸ hd⟩

end PottsContinuity.RSW
