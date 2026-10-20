module

public import PottsContinuity.PlanarMixed.OrderedCutActive
public import PottsContinuity.PD.FK.ConditionalLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PottsContinuity.PlanarMixed.CanonicalCutCarrier
public import PottsContinuity.PlanarMixed.SlitActiveReflection
public import PottsContinuity.PD.Duality.WholePlaneDualConfiguration
public import PottsContinuity.PD.Duality.ConnectionSymmetry
public import PottsContinuity.PlanarMixed.Square.Consumers
public import PottsContinuity.PD.RCInfinite.Cylinders
public import PottsContinuity.PD.FK.IsolatedBoundaryLaw
public import PottsContinuity.PD.FK.EmbeddedClosedInteriorOuterBoundary
public import PottsContinuity.Infinite.MeasurableApprox
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.Sequences
public import PottsContinuity.PD.FK.EmbeddedBoundaryUpper
public import PottsContinuity.PD.FK.CylinderConvergence

/-! The actual unbounded slit graph and its exact sampled finite restrictions.
The underlying retained graph already exists; no boundary links are added. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK PD.FK.Medial PD.Duality
noncomputable section
local instance slitGlobalOpenGraphEdgeFintype {V : Type*} [Finite V] (G : SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite _
local instance slitGlobalOpenGraphEdgeDecidableEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

private theorem retained_bond_coordinates (x y : ℤ) (b : LatticeBond) :
    SlitRetainedBond x y b ↔
      0 ≤ b.source.2 ∧ 0 ≤ b.target.2 ∧
      ¬ (y < b.source.2 ∧ y < b.target.2 ∧
        ((b.source.1 = x-1 ∧ b.target.1 = x) ∨
         (b.target.1 = x-1 ∧ b.source.1 = x))) := by
  rcases b with ⟨⟨a,k⟩,ax⟩
  cases ax <;> simp [SlitRetainedBond,LatticeBond.source,LatticeBond.target] <;> omega

/-- Exact coordinate adjacency on the entire retained carrier, including
isolation of all vertices below the physical bottom. -/
theorem slitRetainedBondGraph_adj_iff (x y : ℤ) (u v : LatticeVertex) :
    (slitRetainedBondGraph x y).Adj u v ↔
      PD.FK.squareLattice.Adj u v ∧ 0 ≤ u.2 ∧ 0 ≤ v.2 ∧
      ¬ (y < u.2 ∧ y < v.2 ∧
        ((u.1 = x-1 ∧ v.1 = x) ∨ (v.1 = x-1 ∧ u.1 = x))) := by
  classical
  constructor
  · intro h
    obtain ⟨⟨b,hret,hpair⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp h
    have hc := (retained_bond_coordinates x y b).mp hret
    rcases Sym2.eq_iff.mp hpair with he | he
    · have hs := b.adjacent
      rw [he.1,he.2] at hs hc
      exact ⟨hs,hc⟩
    · have hs := b.adjacent.symm
      rw [he.1,he.2] at hs hc
      refine ⟨hs,hc.2.1,hc.1,?_⟩
      rintro ⟨hu,hv,hcross⟩
      exact hc.2.2 ⟨hv,hu,hcross.symm⟩
  · rintro ⟨hsq,hu,hv,hcut⟩
    obtain ⟨b,hpair⟩ := LatticeBond.exists_of_adj hsq
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨⟨b,?_,hpair⟩,hsq.ne⟩
    apply (retained_bond_coordinates x y b).mpr
    rcases Sym2.eq_iff.mp hpair with he | he
    · rw [he.1,he.2]
      exact ⟨hu,hv,hcut⟩
    · rw [he.1,he.2]
      refine ⟨hv,hu,?_⟩
      rintro ⟨hv',hu',hcross⟩
      exact hcut ⟨hu',hv',hcross.symm⟩

end
end PottsContinuity.PlanarMixed
