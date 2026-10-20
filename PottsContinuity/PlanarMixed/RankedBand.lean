module

public import PottsContinuity.PlanarMixed.ExteriorPartition
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Order.CompletePartialOrder

/-!
# An induced domain between two ordered graph cuts

Vertices have integer labels: the first marked cut has label 1, the middle
has label 2 and the second cut has label 3. Exterior vertices lie below 1 or
above 3. The local edge condition permits every edge within the band,
INCLUDING a direct edge between the two cuts. It forbids bypassing a cut.
This is a domain class, not a claim that arbitrary polygon arcs have such labels.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12
noncomputable section

/-- The entire closed band between the two marked levels. -/
def rankedBandVertices {V : Type*} (r : V → ℤ) : Set V := {v | 1 ≤ r v ∧ r v ≤ 3}

def rankedBandGraph {V : Type*} (G : SimpleGraph V) (r : V → ℤ) :=
  G.induce (rankedBandVertices r)

def rankedBandEmbedding {V : Type*} (r : V → ℤ) : rankedBandVertices r ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem rankedBandGraph_map_le {V : Type*} (G : SimpleGraph V) (r : V → ℤ) :
    (rankedBandGraph G r).map (rankedBandEmbedding r) ≤ G := by
  intro u v h
  obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp h
  exact huv

def rankedBandFirstArc {V : Type*} (r : V → ℤ) : Set (rankedBandVertices r) :=
  {v | r v.val = 1}

def rankedBandSecondArc {V : Type*} (r : V → ℤ) : Set (rankedBandVertices r) :=
  {v | r v.val = 3}

theorem rankedBand_arcs_disjoint {V : Type*} (r : V → ℤ) :
    Disjoint (rankedBandFirstArc r) (rankedBandSecondArc r) := by
  apply Set.disjoint_left.mpr
  intro v h1 h3
  change r v.val = 1 at h1
  change r v.val = 3 at h3
  omega

def rankedBandBoundary {V : Type*} [Finite V] (r : V → ℤ) :=
  twoBlockBoundary (rankedBandFirstArc r) (rankedBandSecondArc r)
    (rankedBand_arcs_disjoint r)

/-- Each edge stays in the left closed region, the band, or the right closed
region. Adjacent marked cuts are expressly allowed by the middle alternative. -/
def RankedBandEdges {V : Type*} (G : SimpleGraph V) (r : V → ℤ) : Prop :=
  ∀ u v, G.Adj u v →
    (r u ≤ 1 ∧ r v ≤ 1) ∨
    ((1 ≤ r u ∧ r u ≤ 3) ∧ (1 ≤ r v ∧ r v ≤ 3)) ∨
    (3 ≤ r u ∧ 3 ≤ r v)

 theorem rankedBand_outer_disjoint {V : Type*} (r : V → ℤ) :
    Disjoint {v | r v ≤ 1} {v | 3 ≤ r v} := by
  apply Set.disjoint_left.mpr
  intro v h1 h3
  change r v ≤ 1 at h1
  change 3 ≤ r v at h3
  omega

def rankedBandOuterBoundary {V : Type*} [Finite V] (r : V → ℤ) :=
  twoBlockBoundary {v | r v ≤ 1} {v | 3 ≤ r v} (rankedBand_outer_disjoint r)

private theorem rankedBand_exterior_edge {V : Type*} [Finite V]
    (G : SimpleGraph V) (r : V → ℤ) (hstep : RankedBandEdges G r)
    {u v : V}
    (huv : (openGraph G (subgraphRemovedEdges ((rankedBandGraph G r).map
      (rankedBandEmbedding r)) G)).Adj u v) :
    (rankedBandOuterBoundary r).partition.r u v := by
  have hG := openGraph_le G _ huv
  rcases hstep u v hG with hleft | hband | hright
  · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr (Or.inr (Or.inl hleft))
  · obtain ⟨e, he, heq⟩ := (openGraph_adj G _ u v).mp huv
    have hnot := (mem_subgraphRemovedEdges e).mp he
    apply False.elim
    apply hnot
    rw [heq]
    apply ((rankedBandGraph G r).map (rankedBandEmbedding r)).mem_edgeSet.mpr
    exact (SimpleGraph.map_adj _ _ _ _).mpr
      ⟨⟨u, hband.1⟩, ⟨v, hband.2⟩, hG, rfl, rfl⟩
  · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr (Or.inr (Or.inr hright))

private theorem rankedBand_outer_pullback {V : Type*} [Finite V] (r : V → ℤ) :
    Setoid.comap (rankedBandEmbedding r) (rankedBandOuterBoundary r).partition ≤
      (rankedBandBoundary r).partition := by
  intro u v huv
  change (rankedBandOuterBoundary r).partition.r u.val v.val at huv
  rcases (twoBlockBoundary_partition_rel _ _ (rankedBand_outer_disjoint r) u.val v.val).mp huv
    with h | hleft | hright
  · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr (Or.inl (Subtype.ext h))
  · change r u.val ≤ 1 ∧ r v.val ≤ 1 at hleft
    have hu : 1 ≤ r u.val ∧ r u.val ≤ 3 := u.property
    have hv : 1 ≤ r v.val ∧ r v.val ≤ 3 := v.property
    exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr
      (Or.inr (Or.inl ⟨by change r u.val = 1; omega, by change r v.val = 1; omega⟩))
  · change 3 ≤ r u.val ∧ 3 ≤ r v.val at hright
    have hu : 1 ≤ r u.val ∧ r u.val ≤ 3 := u.property
    have hv : 1 ≤ r v.val ∧ r v.val ≤ 3 := v.property
    exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr
      (Or.inr (Or.inr ⟨by change r u.val = 3; omega, by change r v.val = 3; omega⟩))

/-- The entire exterior-state boundary interface is proved from local edges
and labels on the two reference-square sides. No partition comparison premise
is left to the consumer of this theorem. -/
theorem rankedBand_extremalBoundaryComparison
    (a : LatticeVertex) (N : ℕ) (hN : 1 ≤ N)
    (r : RectangleVertex a N N → ℤ) (hstep : RankedBandEdges (rectangleGraph a N N) r)
    (hleft : ∀ v ∈ Square.squareLeftArc a N, r v ≤ 1)
    (hright : ∀ v ∈ Square.squareRightArc a N, 3 ≤ r v) :
    ExtremalBoundaryComparison a N hN (rankedBandGraph (rectangleGraph a N N) r)
      (rankedBandEmbedding r) (rankedBandBoundary r) := by
  apply extremalBoundaryComparison_of_exteriorSeparation a N hN _ _ _
    (rankedBandOuterBoundary r).partition
  · intro u v huv
    rcases (twoBlockBoundary_partition_rel _ _ _ u v).mp huv with h | hL | hR
    · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr (Or.inl h)
    · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr
        (Or.inr (Or.inl ⟨by have := hleft u hL.1; change r u ≤ 1; omega,
          by have := hleft v hL.2; change r v ≤ 1; omega⟩))
    · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr
        (Or.inr (Or.inr ⟨by have := hright u hR.1; change 3 ≤ r u; omega,
          by have := hright v hR.2; change 3 ≤ r v; omega⟩))
  · exact fun _ _ huv => rankedBand_exterior_edge _ r hstep huv
  · exact rankedBand_outer_pullback r

end
end PottsContinuity.PlanarMixed
