-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripClosedCutOpenSupport.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutExploration
public import PottsContinuity.FKC.FiniteFK.RectangleFlowDimension

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC
open Finset PottsContinuity.FKC.FiniteFK

noncomputable section

local instance horizontalStripOpenSupportEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance horizontalStripOpenSupportEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _

/-- If an actual rectangle edge has endpoints in columns `k` and `k+1`, it
belongs to the literal finite cut carrier. -/
theorem horizontalStripRectangleCutEdges_mem_of_endpoint_columns
    (N n : ℕ) (k : ℤ) (hleft : -(N : ℤ) ≤ k) (hright : k < N)
    (e : (horizontalStripCutRectangle N n).edgeSet)
    (u v : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))
    (hu : u ∈ e.val) (hv : v ∈ e.val)
    (hux : u.val.1 = k) (hvx : v.val.1 = k + 1) :
    e ∈ horizontalStripRectangleCutEdges N n k hleft hright := by
  let p := e.val.out
  have hrepr : s(p.1, p.2) = e.val := Quot.out_eq _
  have hu' : u = p.1 ∨ u = p.2 := by
    change u ∈ e.val at hu
    rw [← hrepr] at hu
    exact (Sym2.mem_iff').mp hu
  have hv' : v = p.1 ∨ v = p.2 := by
    change v ∈ e.val at hv
    rw [← hrepr] at hv
    exact (Sym2.mem_iff').mp hv
  have hcols : (p.1.val.1 = k ∧ p.2.val.1 = k + 1) ∨
      (p.1.val.1 = k + 1 ∧ p.2.val.1 = k) := by
    rcases hu' with hu1 | hu2 <;> rcases hv' with hv1 | hv2
    · have h1 : p.1.val.1 = k := by simpa [hu1] using hux
      have h2 : p.1.val.1 = k + 1 := by simpa [hv1] using hvx
      omega
    · exact Or.inl ⟨by simpa [hu1] using hux, by simpa [hv2] using hvx⟩
    · exact Or.inr ⟨by simpa [hv1] using hvx, by simpa [hu2] using hux⟩
    · have h1 : p.2.val.1 = k := by simpa [hu2] using hux
      have h2 : p.2.val.1 = k + 1 := by simpa [hv2] using hvx
      omega
  have hpAdj : (horizontalStripCutRectangle N n).Adj p.1 p.2 :=
    (horizontalStripCutRectangle N n).mem_edgeSet.mp
      (by rw [hrepr]; exact e.property)
  have hpEdge : squareLattice.Adj p.1.val p.2.val :=
    (rectangleGraph_adj_iff _ _ _ _ _).mp hpAdj
  have hpY : p.1.val.2 = p.2.val.2 := by
    have h := (squareLattice_adj_iff _ _).mp hpEdge
    rcases h with ⟨_, hy⟩ | ⟨hx, _⟩
    · exact hy
    · rcases hcols with h | h <;> omega
  have hp1Rect := p.1.property
  rw [mem_latticeRectangle] at hp1Rect
  let y : ℕ := p.1.val.2.toNat
  have hyInt : (y : ℤ) = p.1.val.2 := by
    dsimp [y]
    exact Int.toNat_of_nonneg hp1Rect.2.1
  have hyBound : y ≤ 2 * n := by
    have h' : (y : ℤ) ≤ (2 * n : ℤ) := by
      simpa [hyInt] using hp1Rect.2.2
    exact_mod_cast h'
  let b := rectanglePrimalEdgeBond (-(N : ℤ), 0) (2 * N) (2 * n) e
  have hbPair : b.toSym2 = s(p.1.val, p.2.val) := by
    have ht := rectanglePrimalEdgeBond_toSym2_public
      (-(N : ℤ), 0) (2 * N) (2 * n) e
    change b.toSym2 = Sym2.map
      (fun z : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => z.val) e.val at ht
    rw [← hrepr] at ht
    simpa using ht
  have hcutPair : (horizontalStripCutBond k y).toSym2 = s(p.1.val, p.2.val) := by
    rcases hcols with h | h
    · apply Sym2.eq_iff.mpr
      left
      constructor <;> ext <;> simp [LatticeBond.source,
        LatticeBond.target, horizontalStripCutBond, h.1, h.2, hpY, hyInt]
    · apply Sym2.eq_iff.mpr
      right
      constructor <;> ext <;> simp [LatticeBond.source,
        LatticeBond.target, horizontalStripCutBond, h.1, h.2, hpY, hyInt]
  have hb : b = horizontalStripCutBond k y :=
    LatticeBond.toSym2_injective (hbPair.trans hcutPair.symm)
  have hOriginal : horizontalStripRectangleOriginalEdge N n e =
      latticeBondEdge b := by
    apply Subtype.ext
    rw [horizontalStripRectangleOriginalEdge_val]
    change Sym2.map (fun z : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => z.val)
      e.val = b.toSym2
    exact (rectanglePrimalEdgeBond_toSym2_public (-(N : ℤ), 0) (2 * N) (2 * n) e).symm
  have hcut : latticeBondEdge (horizontalStripCutBond k y) ∈
      horizontalStripCutEdges n k := by
    unfold horizontalStripCutEdges
    apply Finset.mem_image.mpr
    exact ⟨y, Finset.mem_range.mpr (by omega), rfl⟩
  have himage : horizontalStripRectangleOriginalEdge N n e ∈
      (horizontalStripRectangleCutEdges N n k hleft hright).image
        (horizontalStripRectangleOriginalEdge N n) := by
    rw [horizontalStripRectangleCutEdges_original_image]
    simpa [hOriginal, hb] using hcut
  obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp himage
  have hef : f = e := horizontalStripRectangleOriginalEdge_injective N n hfe
  simpa [hef] using hf


private theorem horizontalStripCutWindowGraph_edge_of_endpoints
    (N n : ℕ) (lo hi : ℤ)
    (e : (horizontalStripCutRectangle N n).edgeSet)
    (p q : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))
    (hpq : s(p, q) = e.val)
    (hp : p ∈ horizontalStripCutWindow N n lo hi)
    (hq : q ∈ horizontalStripCutWindow N n lo hi) :
    e.val ∈ (horizontalStripCutWindowGraph N n lo hi).edgeSet := by
  let u : {x : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) //
      x ∈ horizontalStripCutWindow N n lo hi} := ⟨p, hp⟩
  let v : {x : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) //
      x ∈ horizontalStripCutWindow N n lo hi} := ⟨q, hq⟩
  have hadj : (horizontalStripCutRectangle N n).Adj p q := by
    apply (horizontalStripCutRectangle N n).mem_edgeSet.mp
    rw [hpq]
    exact e.property
  have hindAdj : ((horizontalStripCutRectangle N n).induce
      (horizontalStripCutWindow N n lo hi)).Adj u v := hadj
  let d : ((horizontalStripCutRectangle N n).induce
      (horizontalStripCutWindow N n lo hi)).edgeSet :=
    ⟨s(u, v), ((horizontalStripCutRectangle N n).induce
      (horizontalStripCutWindow N n lo hi)).mem_edgeSet.mpr hindAdj⟩
  rw [horizontalStripCutWindowGraph, SimpleGraph.edgeSet_map, Set.mem_image]
  refine ⟨d, d.property, ?_⟩
  simp [d, u, v, hpq]

private theorem horizontalStripCutWindowReveal_other_endpoint_outside
    (N n : ℕ) (lo hi : ℤ)
    (e : (horizontalStripCutRectangle N n).edgeSet)
    (p q : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))
    (hpq : s(p, q) = e.val)
    (heR : e ∈ horizontalStripCutWindowReveal N n lo hi)
    (hp : p ∈ horizontalStripCutWindow N n lo hi) :
    q ∉ horizontalStripCutWindow N n lo hi := by
  have hnot : e.val ∉ (horizontalStripCutWindowGraph N n lo hi).edgeSet :=
    (mem_subgraphRemovedEdges _).mp heR
  intro hq
  exact hnot (horizontalStripCutWindowGraph_edge_of_endpoints
    N n lo hi e p q hpq hp hq)

private theorem horizontalStripCutWindow_crossing_edge_mem_cut
    (N n : ℕ) (lo hi : ℤ)
    (e : (horizontalStripCutRectangle N n).edgeSet)
    (p q : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))
    (hpq : s(p, q) = e.val)
    (hp : p ∈ horizontalStripCutWindow N n lo hi)
    (hq : q ∉ horizontalStripCutWindow N n lo hi)
    (hLlo : -(N : ℤ) ≤ lo - 1) (hLhi : lo - 1 < N)
    (hRlo : -(N : ℤ) ≤ hi) (hRhi : hi < N) :
    e ∈ horizontalStripRectangleCutEdges N n (lo - 1) hLlo hLhi ∨
      e ∈ horizontalStripRectangleCutEdges N n hi hRlo hRhi := by
  have hpMem : p ∈ e.val := by rw [← hpq]; simp
  have hqMem : q ∈ e.val := by rw [← hpq]; simp
  have hAdj : (horizontalStripCutRectangle N n).Adj p q :=
    (horizontalStripCutRectangle N n).mem_edgeSet.mp
      (by rw [hpq]; exact e.property)
  have hSq : squareLattice.Adj p.val q.val :=
    (rectangleGraph_adj_iff _ _ _ _ _).mp hAdj
  have hpX : lo ≤ p.val.1 ∧ p.val.1 ≤ hi := by simpa [horizontalStripCutWindow] using hp
  have hqX : q.val.1 < lo ∨ hi < q.val.1 := by
    by_cases hqlo : lo ≤ q.val.1
    · have hqhi : ¬ q.val.1 ≤ hi := by
        intro hqhi
        exact hq ⟨hqlo, hqhi⟩
      omega
    · exact Or.inl (lt_of_not_ge hqlo)
  have hcoords := (squareLattice_adj_iff _ _).mp hSq
  rcases hcoords with ⟨hhor, hy⟩ | ⟨hx, hvert⟩
  · rcases hhor with hpqStep | hqpStep
    · have hright : p.val.1 = hi ∧ q.val.1 = hi + 1 := by omega
      right
      exact horizontalStripRectangleCutEdges_mem_of_endpoint_columns
        N n hi hRlo hRhi e p q hpMem hqMem hright.1 hright.2
    · have hleft : q.val.1 = lo - 1 ∧ p.val.1 = lo := by omega
      left
      exact horizontalStripRectangleCutEdges_mem_of_endpoint_columns
        N n (lo - 1) hLlo hLhi e q p hqMem hpMem hleft.1 (by omega)
  · have hxEq : p.val.1 = q.val.1 := hx
    rcases hqX with hbelow | habove <;> omega

/-- The surviving window endpoints lie strictly between the two outer columns. -/
theorem horizontalStripClosedCutReveal_window_strict_outer_ends
    (N n K : ℕ) (A : Finset (horizontalStripCutRectangle N n).edgeSet)
    {i j : ℕ}
    (hL : (horizontalStripLeftBlockScan N n K A).2 = some i)
    (hR : (horizontalStripRightBlockScan N n K A).2 = some j) :
    -(N : ℤ) < -(N : ℤ) + (i : ℤ) + 1 ∧
      (N : ℤ) - 1 - (j : ℤ) < N := by
  have hiMem := (firstClosedBlockScan_hit (horizontalStripLeftCutBlock N n K) A
    (List.range (N - K)) i hL).1
  have hjMem := (firstClosedBlockScan_hit (horizontalStripRightCutBlock N n K) A
    (List.range (N - K)) j hR).1
  have hi : i < N - K := List.mem_range.mp hiMem
  have hj : j < N - K := List.mem_range.mp hjMem
  constructor
  · have hi0 : 0 ≤ (i : ℤ) := by exact_mod_cast (Nat.zero_le i)
    omega
  · have hj0 : 0 ≤ (j : ℤ) := by exact_mod_cast (Nat.zero_le j)
    omega

/-- Recorded open edges cannot touch the surviving induced window: any such
edge would cross one of the selected cuts, whose entire finite block is closed. -/
theorem horizontalStripClosedCutReveal_open_endpoints_outside
    (N n K : ℕ) (A : Finset (horizontalStripCutRectangle N n).edgeSet)
    {i j : ℕ}
    (hL : (horizontalStripLeftBlockScan N n K A).2 = some i)
    (hR : (horizontalStripRightBlockScan N n K A).2 = some j)
    (e : (horizontalStripCutRectangle N n).edgeSet)
    (heA : e ∈ A)
    (heR : e ∈ horizontalStripClosedCutReveal N n K A)
    (v : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))
    (hv : v ∈ e.val) :
    v ∉ horizontalStripCutWindow N n
      (-(N : ℤ) + (i : ℤ) + 1) ((N : ℤ) - 1 - (j : ℤ)) := by
  have hiMem := (firstClosedBlockScan_hit (horizontalStripLeftCutBlock N n K) A
    (List.range (N - K)) i hL).1
  have hjMem := (firstClosedBlockScan_hit (horizontalStripRightCutBlock N n K) A
    (List.range (N - K)) j hR).1
  have hi : i < N - K := List.mem_range.mp hiMem
  have hj : j < N - K := List.mem_range.mp hjMem
  have hKN : K ≤ N := by omega
  have hiN : i < N := lt_of_lt_of_le hi (Nat.sub_le N K)
  have hjN : j < N := lt_of_lt_of_le hj (Nat.sub_le N K)
  have hLlo : -(N : ℤ) ≤ -(N : ℤ) + (i : ℤ) := by
    have hi0 : 0 ≤ (i : ℤ) := by exact_mod_cast (Nat.zero_le i)
    omega
  have hLhi : -(N : ℤ) + (i : ℤ) < N := by
    have hiZ : (i : ℤ) < (N : ℤ) := by exact_mod_cast hiN
    omega
  have hRlo : -(N : ℤ) ≤ (N : ℤ) - 1 - (j : ℤ) := by
    have hjZ : (j : ℤ) < (N : ℤ) := by exact_mod_cast hjN
    omega
  have hRhi : (N : ℤ) - 1 - (j : ℤ) < N := by
    have hj0 : 0 ≤ (j : ℤ) := by exact_mod_cast (Nat.zero_le j)
    omega
  have hClosed := horizontalStripClosedCutReveal_selected_blocks_closed
    N n K A hKN hL hR
  have hReveal : e ∈ horizontalStripCutWindowReveal N n
      (-(N : ℤ) + (i : ℤ) + 1) ((N : ℤ) - 1 - (j : ℤ)) := by
    simpa [horizontalStripClosedCutReveal, hL, hR] using heR
  let p := e.val.out
  have hrepr : s(p.1, p.2) = e.val := Quot.out_eq _
  have hv' : v = p.1 ∨ v = p.2 := by
    change v ∈ e.val at hv
    rw [← hrepr] at hv
    exact (Sym2.mem_iff').mp hv
  intro hvWindow
  rcases hv' with hv1 | hv2
  · have hp : p.1 ∈ horizontalStripCutWindow N n
        (-(N : ℤ) + (i : ℤ) + 1) ((N : ℤ) - 1 - (j : ℤ)) := by
      simpa [hv1] using hvWindow
    have hq := horizontalStripCutWindowReveal_other_endpoint_outside
      N n _ _ e p.1 p.2 hrepr hReveal hp
    have hcuts := horizontalStripCutWindow_crossing_edge_mem_cut
      N n _ _ e p.1 p.2 hrepr hp hq
      (by simp) (by omega) hRlo hRhi
    rcases hcuts with hcut | hcut
    · have hcut' : e ∈ horizontalStripRectangleCutEdges N n
          (-(N : ℤ) + (i : ℤ)) hLlo hLhi := by
        simpa only [show (-(N : ℤ) + (i : ℤ) + 1) - 1 =
          -(N : ℤ) + (i : ℤ) by omega] using hcut
      exact (Finset.disjoint_left.mp hClosed.1) heA hcut'
    · exact (Finset.disjoint_left.mp hClosed.2) heA hcut
  · have hp : p.2 ∈ horizontalStripCutWindow N n
        (-(N : ℤ) + (i : ℤ) + 1) ((N : ℤ) - 1 - (j : ℤ)) := by
      simpa [hv2] using hvWindow
    have hswap : s(p.2, p.1) = e.val := by
      rw [Sym2.eq_swap]
      exact hrepr
    have hq := horizontalStripCutWindowReveal_other_endpoint_outside
      N n _ _ e p.2 p.1 hswap hReveal hp
    have hcuts := horizontalStripCutWindow_crossing_edge_mem_cut
      N n _ _ e p.2 p.1 hswap hp hq
      (by simp) (by omega) hRlo hRhi
    rcases hcuts with hcut | hcut
    · have hcut' : e ∈ horizontalStripRectangleCutEdges N n
          (-(N : ℤ) + (i : ℤ)) hLlo hLhi := by
        simpa only [show (-(N : ℤ) + (i : ℤ) + 1) - 1 =
          -(N : ℤ) + (i : ℤ) by omega] using hcut
      exact (Finset.disjoint_left.mp hClosed.1) heA hcut'
    · exact (Finset.disjoint_left.mp hClosed.2) heA hcut

end
end PottsContinuity.FKC.Medial
