module

public import PottsContinuity.PlanarMixed.RankedBandPaths
public import PottsContinuity.PlanarMixed.OmegaConditional
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Tactic
public import Mathlib.Order.CompletePartialOrder

/-!
# Reachability regions of two ordered vertex cuts

The three hypotheses are ordinary deterministic walk-separation facts. They
contain no FK law, conditional probability, exterior partition or RSW bound.
For the ordered crosscuts used in the proof they are derived in
`PlanarMixed.CrosscutOrderedPair` (`orderedCutPair_of_square_crosscuts`) and
`PlanarMixed.FiniteSlit.CrosscutSeparation` (`orderedCutPair_of_slit_crosscuts`).
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
noncomputable section

/-- The union of components accessible from K by walks avoiding S, with every
vertex of the witnessing walk (including its endpoints) required outside S. -/
def cutReachRegion {V : Type*} (G : SimpleGraph V) (S K : Set V) : Set V :=
  {v | ∃ u ∈ K, ∃ p : G.Walk u v, ∀ z ∈ p.support, z ∉ S}

/-- Ordered disjoint cuts A,C between the designated left/right sets L,R. -/
structure OrderedCutPair {V : Type*} (G : SimpleGraph V) (L R A C : Set V) : Prop where
  disjoint : Disjoint A C
  left_right : ∀ l ∈ L, ∀ r ∈ R, ∀ p : G.Walk l r, ∃ z ∈ p.support, z ∈ A
  left_second : ∀ l ∈ L, ∀ c ∈ C, ∀ p : G.Walk l c, ∃ z ∈ p.support, z ∈ A
  first_right : ∀ a ∈ A, ∀ r ∈ R, ∀ p : G.Walk a r, ∃ z ∈ p.support, z ∈ C

theorem cutReachRegion_avoids_cut {V : Type*} {G : SimpleGraph V}
    {S K : Set V} {v : V} (hv : v ∈ cutReachRegion G S K) : v ∉ S := by
  obtain ⟨u, hu, p, hp⟩ := hv
  exact hp v p.end_mem_support

theorem cutReachRegion_contains {V : Type*} (G : SimpleGraph V)
    {S K : Set V} {v : V} (hv : v ∈ K) (havoid : v ∉ S) : v ∈ cutReachRegion G S K :=
  ⟨v, hv, .nil, by simpa using havoid⟩

theorem cutReachRegion_edge_closed {V : Type*} {G : SimpleGraph V}
    {S K : Set V} {u v : V} (hu : u ∈ cutReachRegion G S K)
    (h : G.Adj u v) (hv : v ∉ S) : v ∈ cutReachRegion G S K := by
  obtain ⟨l, hl, p, hp⟩ := hu
  refine ⟨l, hl, p.concat h, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hz
  rcases hz with hz | rfl
  · exact hp z hz
  · exact hv

theorem OrderedCutPair.leftRegion_avoids_second {V : Type*} {G : SimpleGraph V}
    {L R A C : Set V} (h : OrderedCutPair G L R A C)
    {v : V} (hv : v ∈ cutReachRegion G A L) : v ∉ C := by
  intro hvC
  obtain ⟨l, hl, p, hp⟩ := hv
  obtain ⟨z, hz, hzA⟩ := h.left_second l hl v hvC p
  exact hp z hz hzA

theorem OrderedCutPair.rightRegion_avoids_first {V : Type*} {G : SimpleGraph V}
    {L R A C : Set V} (h : OrderedCutPair G L R A C)
    {v : V} (hv : v ∈ cutReachRegion G C R) : v ∉ A := by
  intro hvA
  obtain ⟨r, hr, p, hp⟩ := hv
  obtain ⟨z, hz, hzC⟩ := h.first_right v hvA r hr p.reverse
  exact hp z (by simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz) hzC

theorem OrderedCutPair.regions_disjoint {V : Type*} {G : SimpleGraph V}
    {L R A C : Set V} (h : OrderedCutPair G L R A C) :
    Disjoint (cutReachRegion G A L) (cutReachRegion G C R) := by
  classical
  apply Set.disjoint_left.mpr
  intro v hvL hvR
  obtain ⟨l, hl, p, hp⟩ := hvL
  obtain ⟨r, hr, q, hq⟩ := hvR
  have hqA : ∀ z ∈ q.support, z ∉ A := by
    intro z hz hzA
    obtain ⟨w, hw, hwC⟩ := h.first_right z hzA r hr (q.takeUntil z hz).reverse
    have hwq : w ∈ q.support := q.support_takeUntil_subset_support hz (by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hw)
    exact hq w hwq hwC
  obtain ⟨z, hz, hzA⟩ := h.left_right l hl r hr (p.append q.reverse)
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz | hz
  · exact hp z hz hzA
  · exact hqA z (by simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz) hzA

end
end PottsContinuity.PlanarMixed
