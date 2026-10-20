module

public import PottsContinuity.PD.Duality.RayIndexSeparation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.Duality
noncomputable section

/-- The index of an open dual arch is unchanged across an uncrossed primal
edge above both arch endpoints. -/
theorem open_arch_rayIndex_eq_of_avoiding_adj {s t u v : LatticeVertex}
    (p : PD.squareLattice.Walk s t) (hadj : PD.squareLattice.Adj u v)
    (hs : s.2 < min u.2 v.2) (ht : t.2 < min u.2 v.2)
    (havoid : ∀ b : LatticeBond, b.toSym2 = s(u,v) →
      (dualBondOfPrimal b).toSym2 ∉ p.edges) :
    rayIndex u p = rayIndex v p := by
  rcases u with ⟨a,b⟩
  rcases v with ⟨c,d⟩
  have hcoords := (squareLattice_adj_iff _ _).mp hadj
  dsimp only at hcoords hs ht
  rcases hcoords with ⟨hx | hx,hy⟩ | ⟨hx,hy | hy⟩
  · subst c; subst d
    exact rayIndex_horizontal_invariant a b p
      (by simpa [dualBondOfPrimal,LatticeBond.toSym2,LatticeBond.source,
        LatticeBond.target] using havoid ⟨(a,b),.horizontal⟩ rfl)
  · subst a; subst d
    exact (rayIndex_horizontal_invariant c b p
      (by simpa [dualBondOfPrimal,LatticeBond.toSym2,LatticeBond.source,
        LatticeBond.target] using havoid ⟨(c,b),.horizontal⟩ Sym2.eq_swap)).symm
  · subst c; subst d
    have hd := rayIndex_vertical_difference a b p
      (by simpa [dualBondOfPrimal,LatticeBond.toSym2,LatticeBond.source,
        LatticeBond.target] using havoid ⟨(a,b),.vertical⟩ rfl)
    change rayIndex (a,b+1) p - rayIndex (a,b) p =
      (if s.2 = b ∧ a ≤ s.1 then 1 else 0) -
      (if t.2 = b ∧ a ≤ t.1 then 1 else 0) at hd
    rw [ite_eq_right (by omega),ite_eq_right (by omega)] at hd
    omega
  · subst c; subst b
    have hd := rayIndex_vertical_difference a d p
      (by simpa [dualBondOfPrimal,LatticeBond.toSym2,LatticeBond.source,
        LatticeBond.target] using havoid ⟨(a,d),.vertical⟩ Sym2.eq_swap)
    change rayIndex (a,d+1) p - rayIndex (a,d) p =
      (if s.2 = d ∧ a ≤ s.1 then 1 else 0) -
      (if t.2 = d ∧ a ≤ t.1 then 1 else 0) at hd
    rw [ite_eq_right (by omega),ite_eq_right (by omega)] at hd
    omega

/-- If no vertex just left of the marked ray occurs below its starting row,
the index telescopes as the product of the endpoint half-plane indicators. -/
theorem rayIndex_telescope_of_low_column_absent (v : LatticeVertex)
    {s t : LatticeVertex} (p : PD.squareLattice.Walk s t)
    (hp : ∀ z ∈ p.support, z.2 < v.2 → z.1 ≠ v.1-1) :
    rayIndex v p =
      (if s.2 < v.2 then 1 else 0) * (if v.1 ≤ s.1 then 1 else 0) -
      (if t.2 < v.2 then 1 else 0) * (if v.1 ≤ t.1 then 1 else 0) := by
  induction p with
  | nil => simp [rayIndex]
  | @cons s z t hadj p ih =>
    have hs := hp s (by simp)
    have hz := hp z (by simp)
    have hstep : rayStep v s z =
        (if s.2 < v.2 then 1 else 0) * (if v.1 ≤ s.1 then 1 else 0) -
        (if z.2 < v.2 then 1 else 0) * (if v.1 ≤ z.1 then 1 else 0) := by
      have hcoord := (squareLattice_adj_iff _ _).mp hadj
      rcases hcoord with ⟨hx | hx,hy⟩ | ⟨hx,hy⟩ <;>
        dsimp [rayStep] <;> split_ifs <;> omega
    rw [rayIndex,hstep,ih (fun z hz => hp z (by simp [hz]))]
    omega

end
end PottsContinuity.PlanarTopology
