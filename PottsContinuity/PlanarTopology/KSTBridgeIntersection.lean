module

public import PottsContinuity.PlanarTopology.ThreeArcIntersection
public import PottsContinuity.BD12.KSTEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12

/-- An m-path meets every bridge at the same scale, including all integral
rounding cases in the literal KST target definitions. -/
theorem kst_mpath_bridge_intersect (m : ℕ) {a b u v : LatticeVertex}
    (p : PD.squareLattice.Walk a b) (q : PD.squareLattice.Walk u v)
    (hp : kstMPath m p)
    (hu : kstBridgeLeft m u) (hv : kstBridgeRight m v)
    (hq : ∀ z ∈ q.support, 12*|z.1| ≤ 13*(m : ℤ) ∧ |z.2| ≤ (m : ℤ)) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  obtain ⟨hpPath, ha, hb, hax, hbx, hpB⟩ := hp
  obtain ⟨huX, huY, huL, huSide⟩ := hu
  obtain ⟨hvX, hvY, hvR, hvSide⟩ := hv
  have hbox {z : LatticeVertex}
      (hz : 12*|z.1| ≤ 13*(m : ℤ) ∧ |z.2| ≤ (m : ℤ)) :
      -((13*m/12 : ℕ) : ℤ) ≤ z.1 ∧ z.1 ≤ ((13*m/12 : ℕ) : ℤ) ∧
        -(m : ℤ) ≤ z.2 ∧ z.2 ≤ (m : ℤ) := by
    have hx := abs_le.mp (show |z.1| ≤ ((13*m/12 : ℕ) : ℤ) by omega)
    exact ⟨hx.1,hx.2,(abs_le.mp hz.2).1,(abs_le.mp hz.2).2⟩
  apply rectangle_three_arc_paths_intersect
    (-((13*m/12 : ℕ) : ℤ)) ((13*m/12 : ℕ) : ℤ) (-(m : ℤ)) (m : ℤ)
    (-((m/12 : ℕ) : ℤ)) ((m/12 : ℕ) : ℤ) p q
    (fun z hz => hbox (hpB z hz)) (fun z hz => hbox (hq z hz)) ha hb
  · have h : |a.1| ≤ ((m/12 : ℕ) : ℤ) := by omega
    exact abs_le.mp h
  · have h : |b.1| ≤ ((m/12 : ℕ) : ℤ) := by omega
    exact abs_le.mp h
  · constructor
    · omega
    · rcases huSide with hy | hx
      · have h := (abs_eq (by omega : (0 : ℤ) ≤ (m : ℤ))).mp hy
        rcases h with h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
      · exact Or.inl hx
  · constructor
    · omega
    · rcases hvSide with hy | hx
      · have h := (abs_eq (by omega : (0 : ℤ) ≤ (m : ℤ))).mp hy
        rcases h with h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
      · exact Or.inl hx

end PottsContinuity.PlanarTopology
