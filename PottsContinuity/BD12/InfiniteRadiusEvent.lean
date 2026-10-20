module

public import PottsContinuity.BD12.FiniteDomainOneArm
public import PottsContinuity.BD12.RectangleOpenGraphs
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder

/-! Whole-plane radius-shell events and their literal finite restrictions.
First-hit truncation proves that these are cylinder events. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical

/-- An actual whole-plane open connection to the exact coordinate radius. -/
def infiniteRadiusEvent (c : LatticeVertex) (n : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ v, latticeRadius c v = n ∧ (PD.rcInfiniteOpenGraph ω).Reachable c v}

/-- Each open bond changes the coordinate radius by at most one. -/
theorem infinite_open_radius_step (c : LatticeVertex) (ω : LatticeConfiguration)
    {u v : LatticeVertex} (h : (PD.rcInfiniteOpenGraph ω).Adj u v) :
    latticeRadius c v ≤ latticeRadius c u + 1 := by
  obtain ⟨he, _⟩ := (rcInfiniteOpenGraph_adj ω u v).mp h
  exact latticeRadius_step c (PD.squareLattice.mem_edgeSet.mp he)

/-- The whole-plane event agrees with its original-edge restriction to the ball. -/
theorem infiniteRadiusEvent_eq_preimage (c : LatticeVertex) (n : ℕ) :
    infiniteRadiusEvent c n =
      embeddedRestriction (finiteLatticeGraph (latticeBox c n)) (frozenEdgeEmbedding (latticeBox c n)) ⁻¹'
        finiteDomainOneArmEvent (latticeBox c n) c (radiusBoxCenter c n) n := by
  ext ω
  have hgraph := embeddedRestriction_domainGraph (latticeBox c n) ω
  constructor
  · rintro ⟨v, hv, ⟨p⟩⟩
    obtain ⟨z, q, hz, hq⟩ := walk_reaches_radius_inside_ball (latticeRadius c)
      (infinite_open_radius_step c ω) p n (by simp) hv.ge
    have hzmem : z ∈ latticeBox c n := (latticeRadius_le_iff_mem_box c z n).mp hz.le
    have hall : ∀ v ∈ q.support, v ∈ (latticeBox c n : Set LatticeVertex) :=
      fun v hv => (latticeRadius_le_iff_mem_box c v n).mp (hq v hv)
    have hconn : ((PD.rcInfiniteOpenGraph ω).induce (latticeBox c n : Set LatticeVertex)).Reachable
        (radiusBoxCenter c n) ⟨z,hzmem⟩ := ⟨q.induce _ hall⟩
    refine ⟨⟨z,hzmem⟩,hz,?_⟩
    rw [← hgraph] at hconn
    exact hconn
  · rintro ⟨v, hv, hconn⟩
    have hconn' : ((PD.rcInfiniteOpenGraph ω).induce (latticeBox c n : Set LatticeVertex)).Reachable
        (radiusBoxCenter c n) v := by
      rw [← hgraph]
      exact hconn
    let f : (PD.rcInfiniteOpenGraph ω).induce (latticeBox c n : Set LatticeVertex) →g
        PD.rcInfiniteOpenGraph ω := { toFun := Subtype.val, map_rel' := fun h => h }
    exact ⟨v.val,hv,hconn'.map f⟩

theorem infiniteRadiusEvent_isCylinder (c : LatticeVertex) (n : ℕ) :
    IsCylinder (infiniteRadiusEvent c n) := by
  rw [infiniteRadiusEvent_eq_preimage]
  exact embeddedRestriction_isCylinder _ _ _

/-- Actual whole-plane shell connections decrease with their radius. -/
theorem infiniteRadiusEvent_antitone (c : LatticeVertex) : Antitone (infiniteRadiusEvent c) := by
  intro m n hmn ω hω
  obtain ⟨v,hv,⟨p⟩⟩ := hω
  obtain ⟨z,q,hz,_⟩ := walk_reaches_radius_inside_ball (latticeRadius c)
    (infinite_open_radius_step c ω) p m (by simp) (by omega)
  exact ⟨z,hz,⟨q⟩⟩

end
end PottsContinuity.BD12
