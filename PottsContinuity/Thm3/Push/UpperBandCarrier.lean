module

public import PottsContinuity.Thm3.Push.RectangleBondPullback
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
noncomputable section

/-- Actual vertices of the upper band, with its original top left fixed. -/
theorem rectangle_upper_band_subset (a : LatticeVertex) (w H t : ℕ) (ht : t ≤ H) :
    PD.FK.latticeRectangle (a.1,a.2+(t : ℤ)) w (H-t) ⊆ PD.FK.latticeRectangle a w H := by
  intro v hv
  rw [mem_latticeRectangle] at hv ⊢
  have hsub : ((H-t : ℕ) : ℤ)=(H : ℤ)-(t : ℤ) := Nat.cast_sub ht
  simp only at hv
  exact ⟨hv.1,by omega,by omega⟩

/-- Expanded face inclusion for the upper band. This does NOT claim that
its true dual graph is the induced expanded subgraph of the larger dual. -/
theorem rectangle_dual_upper_band_subset (a : LatticeVertex) (w H t : ℕ) (ht : t ≤ H) :
    rectangleDualExpanded (a.1,a.2+(t : ℤ)) w (H-t) ⊆ rectangleDualExpanded a w H := by
  intro v hv
  rw [rectangleDualExpanded,mem_latticeRectangle] at hv ⊢
  have hsub : ((H-t : ℕ) : ℤ)=(H : ℤ)-(t : ℤ) := Nat.cast_sub ht
  simp only [Nat.cast_add,Nat.cast_one] at hv ⊢
  exact ⟨hv.1,by omega,by omega⟩

/-- A true-dual step above the band's bottom face row crosses a bond of the
actual upper primal band, provided it is not an edge ALONG that bottom row.
The latter edges are exactly the extra induced-expanded-graph edges which
first-arrival truncation must discard. -/
theorem upper_band_crossed_bond_endpoints_mem (a : LatticeVertex) (w H t : ℕ) (ht : t ≤ H)
    (f : (rectangleGraph a w H).edgeSet) (u v : LatticeVertex)
    (hpair : s(u,v)=s((rectanglePrimalEdgeBond a w H f).faceBase false,
      (rectanglePrimalEdgeBond a w H f).faceBase true))
    (hu : a.2+(t : ℤ)-1 ≤ u.2) (hv : a.2+(t : ℤ)-1 ≤ v.2)
    (hnot : ¬ (u.2=a.2+(t : ℤ)-1 ∧ v.2=a.2+(t : ℤ)-1)) :
    (rectanglePrimalEdgeBond a w H f).source ∈ PD.FK.latticeRectangle (a.1,a.2+(t : ℤ)) w (H-t) ∧
    (rectanglePrimalEdgeBond a w H f).target ∈ PD.FK.latticeRectangle (a.1,a.2+(t : ℤ)) w (H-t) := by
  have hends := rectanglePrimalEdgeBond_endpoints_mem_public a w H f
  have hsub : ((H-t : ℕ) : ℤ)=(H : ℤ)-(t : ℤ) := Nat.cast_sub ht
  generalize hb : rectanglePrimalEdgeBond a w H f = b at hpair hends ⊢
  rcases b with ⟨⟨x,y⟩,axis⟩
  rcases u with ⟨ux,uy⟩
  rcases v with ⟨vx,vy⟩
  simp only [mem_latticeRectangle] at hends ⊢
  cases axis <;>
    simp only [LatticeBond.faceBase,LatticeBond.source,LatticeBond.target,
      Sym2.eq_iff,Prod.mk.injEq] at * <;> omega

end
end PottsContinuity.Push
