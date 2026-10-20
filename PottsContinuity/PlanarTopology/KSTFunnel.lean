module

public import PottsContinuity.PlanarTopology.RectangleExit
public import PottsContinuity.PlanarTopology.KSTBridgeIntersection
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12

/-- A simple arm starting between the lower endpoints of two flanking walls
and reaching above the box either hits an original wall or has an actual
contiguous central m-path. This is the deterministic funnel used to turn the
long arms in KST §4.3 into attached m-paths. -/
theorem kst_funnel_extract (k : ℕ) (hk : 1 ≤ k) (a : ℤ)
    (_ha : 0 ≤ a ∧ a ≤ (k : ℤ))
    {l₁ l₂ r₁ r₂ u v : LatticeVertex}
    (L : PD.squareLattice.Walk l₁ l₂) (R : PD.squareLattice.Walk r₁ r₂)
    (p : PD.squareLattice.Walk u v)
    (hL : kstPathIn L (-13*(k : ℤ)) (13*(k : ℤ)) (-12*(k : ℤ)) (12*(k : ℤ)))
    (hR : kstPathIn R (-13*(k : ℤ)) (13*(k : ℤ)) (-12*(k : ℤ)) (12*(k : ℤ)))
    (hLt : l₁.2 = 12*(k : ℤ)) (hLb : l₂.2 = -12*(k : ℤ))
    (hRt : r₁.2 = 12*(k : ℤ)) (hRb : r₂.2 = -12*(k : ℤ))
    (hLx : -(k : ℤ) ≤ l₁.1 ∧ l₁.1 ≤ -a)
    (hLx' : -(k : ℤ) ≤ l₂.1 ∧ l₂.1 ≤ -a)
    (hRx : a ≤ r₁.1 ∧ r₁.1 ≤ (k : ℤ))
    (hRx' : a ≤ r₂.1 ∧ r₂.1 ≤ (k : ℤ))
    (hp : p.IsPath) (hu : u.2 = -12*(k : ℤ) ∧ -a ≤ u.1 ∧ u.1 ≤ a)
    (hv : 12*(k : ℤ) ≤ v.2)
    (hlow : ∀ z ∈ p.support, -12*(k : ℤ) ≤ z.2) :
    (∃ (x y : LatticeVertex) (q : PD.squareLattice.Walk x y),
      kstMPath (12*k) q ∧ q.reverse.IsSubwalk p) ∨
    (∃ z ∈ p.support, z ∈ L.support ∨ z ∈ R.support) := by
  have hf : ∀ x y, PD.squareLattice.Adj x y → |x.1-y.1| ≤ 1 := by
    intro x y h
    change |x.1-y.1|+|x.2-y.2| = 1 at h
    have := abs_nonneg (x.2-y.2)
    omega
  have hg : ∀ x y, PD.squareLattice.Adj x y → |x.2-y.2| ≤ 1 := by
    intro x y h
    change |x.1-y.1|+|x.2-y.2| = 1 at h
    have := abs_nonneg (x.1-y.1)
    omega
  obtain ⟨z,q,s,he,hz,hq⟩ := walk_prefix_to_three_sides
    (fun z : LatticeVertex => z.1) (fun z : LatticeVertex => z.2) hf hg p
    (-13*(k : ℤ)) (13*(k : ℤ)) (-12*(k : ℤ)) (12*(k : ℤ))
    ⟨by omega,by omega,by omega⟩ hlow (Or.inr (Or.inr hv))
  have hqp : q.IsSubwalk p := SimpleGraph.Walk.isSubwalk_of_append_left he
  have left_contact (hx : z.1 ≤ -(k : ℤ))
      (hb : z.1 = -13*(k : ℤ) ∨ z.2 = 12*(k : ℤ)) :
      ∃ w ∈ p.support, w ∈ L.support ∨ w ∈ R.support := by
    have hqr : kstPathIn q.reverse (-13*(k : ℤ)) (13*(k : ℤ))
        (-12*(k : ℤ)) (12*(k : ℤ)) := by
      intro w hw
      exact hq w (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hw)
    obtain ⟨w,hwL,hwq⟩ := rectangle_three_arc_paths_intersect
      (-13*(k : ℤ)) (13*(k : ℤ)) (-12*(k : ℤ)) (12*(k : ℤ))
      (-(k : ℤ)) (-a) L q.reverse hL hqr hLt hLb hLx hLx'
      ⟨hx,hb.elim Or.inl (fun h => Or.inr (Or.inr h))⟩
      ⟨hu.2.1,Or.inr (Or.inl hu.1)⟩
    have hwq' : w ∈ q.support := by
      simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hwq
    exact ⟨w,hqp.support_subset hwq',Or.inl hwL⟩
  have right_contact (hx : (k : ℤ) ≤ z.1)
      (hb : z.1 = 13*(k : ℤ) ∨ z.2 = 12*(k : ℤ)) :
      ∃ w ∈ p.support, w ∈ L.support ∨ w ∈ R.support := by
    obtain ⟨w,hwR,hwq⟩ := rectangle_three_arc_paths_intersect
      (-13*(k : ℤ)) (13*(k : ℤ)) (-12*(k : ℤ)) (12*(k : ℤ))
      a (k : ℤ) R q hR hq hRt hRb hRx hRx'
      ⟨hu.2.2,Or.inr (Or.inl hu.1)⟩
      ⟨hx,hb.elim Or.inl (fun h => Or.inr (Or.inr h))⟩
    exact ⟨w,hqp.support_subset hwq,Or.inr hwR⟩
  rcases hz with hz | hz | hz
  · exact Or.inr (left_contact (by omega) (Or.inl hz))
  · exact Or.inr (right_contact (by omega) (Or.inl hz))
  · by_cases hzx : z.1 < -(k : ℤ)
    · exact Or.inr (left_contact (by omega) (Or.inr hz))
    by_cases hzx' : (k : ℤ) < z.1
    · exact Or.inr (right_contact (by omega) (Or.inr hz))
    left
    refine ⟨z,u,q.reverse,?_,by simpa only [SimpleGraph.Walk.reverse_reverse] using hqp⟩
    have hqa := SimpleGraph.Walk.isPath_of_isSubwalk hqp hp
    have hzabs : |z.1| ≤ (k : ℤ) := abs_le.mpr ⟨by omega,by omega⟩
    have huabs : |u.1| ≤ (k : ℤ) := abs_le.mpr ⟨by omega,by omega⟩
    refine ⟨hqa.reverse,?_,?_,?_,?_,?_⟩
    · simpa only [Nat.cast_mul,Nat.cast_ofNat] using hz
    · simpa only [Nat.cast_mul,Nat.cast_ofNat,neg_mul] using hu.1
    · push_cast; omega
    · push_cast; omega
    · intro w hw
      have hh := hq w (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hw)
      have hwx : |w.1| ≤ 13*(k : ℤ) := abs_le.mpr ⟨hh.1,hh.2.1⟩
      have hwy : |w.2| ≤ 12*(k : ℤ) := abs_le.mpr hh.2.2
      push_cast
      constructor <;> omega

end PottsContinuity.PlanarTopology
