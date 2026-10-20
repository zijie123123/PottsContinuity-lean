module

public import PottsContinuity.PlanarMixed.FiniteSlit.ActiveCarrier
public import PottsContinuity.PlanarMixed.OrderedCutActive
public import PottsContinuity.PD.FK.ConditionalLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PottsContinuity.PlanarMixed.CanonicalCutCarrier

/-! Exact finite outer-arc prewiring. Boundary-internal states can be fixed
open before rectangular duality without changing whole-arc connectivity. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial BD12 MeasureTheory
noncomputable section
local instance finiteSlitPrewiringEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

/-- All and only the sampled bonds internal to alpha or beta. -/
def internalEdges (M : ℕ) (x y : ℤ) : Configuration (graph M x y) :=
  internalBonds (graph M x y) (alpha M x) ∪ internalBonds (graph M x y) (beta M x y)

/-- Every endpoint pair removed from the sampled carrier is already wired. -/
theorem internalEdges_prewired (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    (u v : Vertex M x) (huv : (graph M x y).Adj u v)
    (he : (⟨s(u,v),(graph M x y).mem_edgeSet.mpr huv⟩ : (graph M x y).edgeSet) ∈
      internalEdges M x y) : (boundary M x y hM hy hyM).partition.r u v := by
  rw [internalEdges,Finset.mem_union,mem_internalBonds_pair _ _ u v huv,
    mem_internalBonds_pair _ _ u v huv] at he
  apply (twoBlockBoundary_partition_rel _ _ _ u v).mpr
  exact Or.inr he

/-- Normalized edge membership is the literal finite boundary-internal predicate. -/
theorem mem_internalEdges_bond_iff (M : ℕ) (x y : ℤ) (b : LatticeBond)
    (hs : b.source ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M)
    (ht : b.target ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M)
    (hb : (graph M x y).Adj ⟨b.source,hs⟩ ⟨b.target,ht⟩) :
    (⟨s(⟨b.source,hs⟩,⟨b.target,ht⟩),(graph M x y).mem_edgeSet.mpr hb⟩ :
      (graph M x y).edgeSet) ∈ internalEdges M x y ↔ boundaryInternal M x y b := by
  rw [internalEdges,Finset.mem_union,mem_internalBonds_pair _ _ _ _ hb,
    mem_internalBonds_pair _ _ _ _ hb]
  constructor
  · exact fun h => ⟨hs,ht,h⟩
  · rintro ⟨_,_,h⟩
    exact h

/-- Actual finite source graph after internal arc-state marginalization. -/
def activeGraph (M : ℕ) (x y : ℤ) : SimpleGraph (Vertex M x) :=
  edgeRestriction (graph M x y) (internalEdges M x y)

/-- The actual remaining-edge graph is exactly the normalized active predicate. -/
theorem activeGraph_bond_adj_iff (M : ℕ) (x y : ℤ) (b : LatticeBond)
    (hs : b.source ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M)
    (ht : b.target ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M) :
    (activeGraph M x y).Adj ⟨b.source,hs⟩ ⟨b.target,ht⟩ ↔ ActiveBond M x y b := by
  rw [activeGraph,edgeRestriction_adj_exists_not_mem]
  have hret : (graph M x y).Adj ⟨b.source,hs⟩ ⟨b.target,ht⟩ ↔ SlitRetainedBond x y b := by
    rw [graph_adj_iff_retained]
    constructor
    · intro h
      obtain ⟨⟨c,hc,hpair⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp h
      have hcb : c = b := LatticeBond.toSym2_injective hpair
      exact hcb ▸ hc
    · intro h
      exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨b,h,rfl⟩,b.adjacent.ne⟩
  constructor
  · rintro ⟨hb,hn⟩
    exact ⟨hs,ht,hret.mp hb,fun hi => hn ((mem_internalEdges_bond_iff M x y b hs ht hb).mpr hi)⟩
  · rintro ⟨_,_,hr,hn⟩
    exact ⟨hret.mpr hr,fun hi => hn ((mem_internalEdges_bond_iff M x y b hs ht
      (hret.mpr hr)).mp hi)⟩

end
end PottsContinuity.PlanarMixed.FiniteSlit
