module

public import PottsContinuity.Thm3.Push.IntervalArmSeedIndex
public import PottsContinuity.Thm3.Push.RayIndexBelowBounds
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.Duality

/-- A closed walk may enter the lower half plane inside the SOURCE interval.
All prescribed left seed marks still have zero index; its other vertices need
only stay between the physical left and right square sides. -/
theorem rayIndex_lower_collar_left_seed_zero
    (N : ℕ) (l r : ℤ) {z : LatticeVertex} (p : PD.FK.squareLattice.Walk z z)
    (hstrip : ∀ x ∈ p.support, 0 ≤ x.1 ∧ x.1 ≤ (N : ℤ))
    (hbelow : ∀ x ∈ p.support, x.2 < 0 → l ≤ x.1 ∧ x.1 ≤ r)
    (b : RectangleDualVertex (0,0) N N) (hb : b ∈ intervalArmLeftDualPorts N l) :
    rayIndex (faceIndexMark b.val) p=0 := by
  rcases (mem_intervalArmLeftDualPorts N l b).mp hb with hb | ⟨hb,hbl⟩
  · have hi := rayIndex_left_telescope (faceIndexMark b.val) p (by
      intro x hx
      have hh := hstrip x hx
      change b.val.1+1 ≤ x.1
      omega)
    exact hi.trans (sub_self _)
  · have hi := rayIndex_telescope_of_below_left_bound (faceIndexMark b.val) p (by
      intro x hx hxm
      change x.2 < b.val.2+1 at hxm
      have hh := hbelow x hx (by omega)
      change b.val.1+1 ≤ x.1
      omega)
    exact hi.trans (sub_self _)

/-- The analogous right seed index vanishes even when the closed walk uses a
cap below the square, provided that cap's columns stay in the source interval. -/
theorem rayIndex_lower_collar_right_seed_zero
    (N : ℕ) (l r : ℤ) {z : LatticeVertex} (p : PD.FK.squareLattice.Walk z z)
    (hstrip : ∀ x ∈ p.support, 0 ≤ x.1 ∧ x.1 ≤ (N : ℤ))
    (hbelow : ∀ x ∈ p.support, x.2 < 0 → l ≤ x.1 ∧ x.1 ≤ r)
    (b : RectangleDualVertex (0,0) N N) (hb : b ∈ intervalArmRightDualPorts N r) :
    rayIndex (faceIndexMark b.val) p=0 := by
  rcases (mem_intervalArmRightDualPorts N r b).mp hb with hb | ⟨hb,hrb⟩
  · apply rayIndex_zero_of_right
    intro x hx
    have hh := hstrip x hx
    change x.1 < b.val.1+1
    omega
  · apply rayIndex_zero_of_below_right_bound
    intro x hx hxm
    change x.2 < b.val.2+1 at hxm
    have hh := hbelow x hx (by omega)
    change x.1 < b.val.1+1
    omega

/-- Lower source-interval caps cannot create an edge-simple closed walk
through the actual filled frontier's original square bonds. -/
theorem lower_collar_closed_trail_avoids_interval_square_bonds
    (N : ℕ) (l r : ℤ) (A : Configuration (rectangleGraph (0,0) N N))
    {z : LatticeVertex} (p : PD.FK.squareLattice.Walk z z) (hn : p.edges.Nodup)
    (hstrip : ∀ x ∈ p.support, 0 ≤ x.1 ∧ x.1 ≤ (N : ℤ))
    (hbelow : ∀ x ∈ p.support, x.2 < 0 → l ≤ x.1 ∧ x.1 ≤ r)
    (hedges : ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∈ p.edges →
        f ∈ intervalArmFilledLeftFrontier N l r A)
    (f : (rectangleGraph (0,0) N N).edgeSet) :
    (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∉ p.edges :=
  closed_trail_avoids_interval_square_bonds_of_seed_zero N l r A p hn
    (rayIndex_lower_collar_left_seed_zero N l r p hstrip hbelow)
    (rayIndex_lower_collar_right_seed_zero N l r p hstrip hbelow) hedges f

end PottsContinuity.Push
