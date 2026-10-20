-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripClosedCutExploration.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripCutRectangle
public import PottsContinuity.FKC.FiniteFK.FirstClosedBlockScan
public import PottsContinuity.FKC.FiniteFK.SubgraphComparison

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC
open Finset PottsContinuity.FKC.FiniteFK

noncomputable section

local instance horizontalStripCutExplorationEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance horizontalStripCutExplorationEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _

/-- The inclusive horizontal vertex interval bounded by two closed cuts. -/
def horizontalStripCutWindow (N n : ℕ) (lo hi : ℤ) :
    Set (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)) :=
  {v | lo ≤ v.1.1 ∧ v.1.1 ≤ hi}

/-- A finite edge is internal to a horizontal window when both endpoints are. -/
def horizontalStripEdgeInsideColumns (N n : ℕ) (lo hi : ℤ)
    (e : (horizontalStripCutRectangle N n).edgeSet) : Prop :=
  ∀ v, v ∈ e.val → lo ≤ v.1.1 ∧ v.1.1 ≤ hi

/-- The actual outer-graph subgraph carried by the surviving window. -/
def horizontalStripCutWindowGraph (N n : ℕ) (lo hi : ℤ) :
    SimpleGraph (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)) :=
  ((horizontalStripCutRectangle N n).induce (horizontalStripCutWindow N n lo hi)).map
    (Function.Embedding.subtype _)

/-- Membership in the mapped induced window forces both edge endpoints into
its vertex interval. -/
private theorem horizontalStripEdgeInsideColumns_of_windowGraph_mem (N n : ℕ)
    (lo hi : ℤ) (e : (horizontalStripCutRectangle N n).edgeSet)
    (he : e.val ∈ (horizontalStripCutWindowGraph N n lo hi).edgeSet) :
    horizontalStripEdgeInsideColumns N n lo hi e := by
  rw [horizontalStripCutWindowGraph, SimpleGraph.edgeSet_map, Set.mem_image] at he
  rcases he with ⟨d, hd, hdeq⟩
  intro v hv
  have hv0 : v ∈ e.val := by exact hv
  rw [← hdeq] at hv0
  have hv' : v ∈ (Function.Embedding.subtype
      (fun z : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => z ∈ horizontalStripCutWindow N n lo hi)).sym2Map d := hv0
  rcases Sym2.mem_map.mp hv' with ⟨w, hw, hval⟩
  have hw' : lo ≤ w.val.val.1 ∧ w.val.val.1 ≤ hi := by
    exact w.property
  have hcoord : w.val.val.1 = v.val.1 := by
    exact congrArg (fun z : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => z.val.1) hval
  exact ⟨by simpa [hcoord] using hw'.1, by simpa [hcoord] using hw'.2⟩

/-- The window reveal is the exact set of outer edges removed by restricting to
its induced subgraph. -/
def horizontalStripCutWindowReveal (N n : ℕ) (lo hi : ℤ) :
    Configuration (horizontalStripCutRectangle N n) :=
  subgraphRemovedEdges (horizontalStripCutWindowGraph N n lo hi)
    (horizontalStripCutRectangle N n)

/-- Every cut edge has its left-column endpoint. -/
private theorem horizontalStripRectangleCutEdge_has_left_endpoint (N n : ℕ) (k : ℤ)
    (hleft : -(N : ℤ) ≤ k) (hright : k < N)
    (e : (horizontalStripCutRectangle N n).edgeSet)
    (he : e ∈ horizontalStripRectangleCutEdges N n k hleft hright) :
    ∃ v, v ∈ e.val ∧ v.1.1 = k := by
  have hmem : horizontalStripRectangleOriginalEdge N n e ∈ horizontalStripCutEdges n k := by
    have him : horizontalStripRectangleOriginalEdge N n e ∈
        (horizontalStripRectangleCutEdges N n k hleft hright).image
          (horizontalStripRectangleOriginalEdge N n) := Finset.mem_image.mpr ⟨e, he, rfl⟩
    rw [horizontalStripRectangleCutEdges_original_image] at him
    exact him
  rcases Finset.mem_image.mp hmem with ⟨y, hy, hbond⟩
  have hsym : Sym2.map (fun x : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => x.1)
      e.val = (latticeBondEdge (horizontalStripCutBond k y)).val := by
    have h := congrArg Subtype.val hbond
    change Sym2.map (fun x : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => x.1) e.val = _
    exact h.symm
  have hs : (horizontalStripCutBond k y).source ∈
      Sym2.map (fun x : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => x.1) e.val := by
    rw [hsym]
    exact (Sym2.mem_iff').2 (Or.inl rfl)
  rcases Sym2.mem_map.mp hs with ⟨v, hv, hval⟩
  refine ⟨v, hv, ?_⟩
  have hx := congrArg Prod.fst hval
  simpa [horizontalStripCutBond, LatticeBond.source] using hx

private theorem horizontalStripRectangleCutEdge_has_right_endpoint (N n : ℕ) (k : ℤ)
    (hleft : -(N : ℤ) ≤ k) (hright : k < N)
    (e : (horizontalStripCutRectangle N n).edgeSet)
    (he : e ∈ horizontalStripRectangleCutEdges N n k hleft hright) :
    ∃ v, v ∈ e.val ∧ v.1.1 = k + 1 := by
  have hmem : horizontalStripRectangleOriginalEdge N n e ∈ horizontalStripCutEdges n k := by
    have him : horizontalStripRectangleOriginalEdge N n e ∈
        (horizontalStripRectangleCutEdges N n k hleft hright).image
          (horizontalStripRectangleOriginalEdge N n) := Finset.mem_image.mpr ⟨e, he, rfl⟩
    rw [horizontalStripRectangleCutEdges_original_image] at him
    exact him
  rcases Finset.mem_image.mp hmem with ⟨y, hy, hbond⟩
  have hsym : Sym2.map (fun x : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => x.1)
      e.val = (latticeBondEdge (horizontalStripCutBond k y)).val := by
    have h := congrArg Subtype.val hbond
    change Sym2.map (fun x : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => x.1) e.val = _
    exact h.symm
  have ht : (horizontalStripCutBond k y).target ∈
      Sym2.map (fun x : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => x.1) e.val := by
    rw [hsym]
    exact (Sym2.mem_iff').2 (Or.inr rfl)
  rcases Sym2.mem_map.mp ht with ⟨v, hv, hval⟩
  refine ⟨v, hv, ?_⟩
  have hx := congrArg Prod.fst hval
  simpa [horizontalStripCutBond, LatticeBond.target] using hx

private theorem horizontalStripCutEdge_not_inside_left (N n : ℕ)
    (lo hi k : ℤ) (hk : k < lo)
    (hleft : -(N : ℤ) ≤ k) (hright : k < N)
    (e : (horizontalStripCutRectangle N n).edgeSet)
    (he : e ∈ horizontalStripRectangleCutEdges N n k hleft hright) :
    ¬ horizontalStripEdgeInsideColumns N n lo hi e := by
  intro hinside
  obtain ⟨v, hv, hx⟩ := horizontalStripRectangleCutEdge_has_left_endpoint N n k hleft hright e he
  exact (not_le_of_gt hk) (by simpa [hx] using (hinside v hv).1)

private theorem horizontalStripCutEdge_not_inside_right (N n : ℕ)
    (lo hi k : ℤ) (hk : hi ≤ k)
    (hleft : -(N : ℤ) ≤ k) (hright : k < N)
    (e : (horizontalStripCutRectangle N n).edgeSet)
    (he : e ∈ horizontalStripRectangleCutEdges N n k hleft hright) :
    ¬ horizontalStripEdgeInsideColumns N n lo hi e := by
  intro hinside
  obtain ⟨v, hv, hx⟩ := horizontalStripRectangleCutEdge_has_right_endpoint N n k hleft hright e he
  exact (not_le_of_gt (by omega : hi < k + 1)) (by simpa [hx] using (hinside v hv).2)

/-- Candidate left cuts are scanned inward, with the actual finite rectangle edge carrier. -/
def horizontalStripLeftCutBlock (N n K i : ℕ) :
    Finset (horizontalStripCutRectangle N n).edgeSet := by
  classical
  by_cases hi : i < N - K
  · exact horizontalStripRectangleCutEdges N n (-(N : ℤ) + (i : ℤ)) (by omega) (by omega)
  · exact ∅

/-- Candidate right cuts are scanned inward, with the actual finite rectangle edge carrier. -/
def horizontalStripRightCutBlock (N n K i : ℕ) :
    Finset (horizontalStripCutRectangle N n).edgeSet := by
  classical
  by_cases hi : i < N - K
  · exact horizontalStripRectangleCutEdges N n ((N : ℤ) - 1 - (i : ℤ)) (by omega) (by omega)
  · exact ∅

def horizontalStripLeftBlockScan (N n K : ℕ)
    (A : Finset (horizontalStripCutRectangle N n).edgeSet) :
    Finset (horizontalStripCutRectangle N n).edgeSet × Option ℕ :=
  firstClosedBlockScan (horizontalStripLeftCutBlock N n K) A (List.range (N - K))

def horizontalStripRightBlockScan (N n K : ℕ)
    (A : Finset (horizontalStripCutRectangle N n).edgeSet) :
    Finset (horizontalStripCutRectangle N n).edgeSet × Option ℕ :=
  firstClosedBlockScan (horizontalStripRightCutBlock N n K) A (List.range (N - K))

private theorem firstClosedBlockUnion_mem_iff {E ι : Type*} [DecidableEq E]
    (D : ι → Finset E) (js : List ι) (e : E) :
    e ∈ firstClosedBlockUnion D js ↔ ∃ i, i ∈ js ∧ e ∈ D i := by
  induction js with
  | nil => simp [firstClosedBlockUnion]
  | cons j js ih =>
      simp only [firstClosedBlockUnion, Finset.mem_union, ih, List.mem_cons]
      constructor
      · rintro (he | ⟨i, hi, he⟩)
        · exact ⟨j, Or.inl rfl, he⟩
        · exact ⟨i, Or.inr hi, he⟩
      · rintro ⟨i, hi, he⟩
        rcases hi with rfl | hi
        · exact Or.inl he
        · exact Or.inr ⟨i, hi, he⟩

private theorem list_range_prefix_lt {m : ℕ} {pre post : List ℕ} {j : ℕ}
    (hdecomp : List.range m = pre ++ j :: post) {i : ℕ} (hi : i ∈ pre) : i < j := by
  have hpair : (List.range m).Pairwise (· < ·) := List.pairwise_lt_range
  rw [hdecomp] at hpair
  have hcross := (List.pairwise_append.mp hpair).2.2 i hi j (by simp)
  exact hcross

private theorem horizontalStripLeftScan_tested_subset_windowReveal (N n K : ℕ)
    (A : Finset (horizontalStripCutRectangle N n).edgeSet) (hKN : K ≤ N)
    {j r : ℕ} (hHit : (horizontalStripLeftBlockScan N n K A).2 = some j)
    (_hR : (horizontalStripRightBlockScan N n K A).2 = some r) :
    (horizontalStripLeftBlockScan N n K A).1 ⊆
      horizontalStripCutWindowReveal N n
        (-(N : ℤ) + (j : ℤ) + 1) ((N : ℤ) - 1 - (r : ℤ)) := by
  intro e he
  obtain ⟨pre, post, hdecomp, hpre, hclosed, htested⟩ :=
    firstClosedBlockScan_hit_prefix (horizontalStripLeftCutBlock N n K) A
      (List.range (N - K)) j hHit
  change e ∈ (firstClosedBlockScan (horizontalStripLeftCutBlock N n K) A
    (List.range (N - K))).1 at he
  rw [htested] at he
  obtain ⟨i, hi, heblock⟩ :=
    (firstClosedBlockUnion_mem_iff (horizontalStripLeftCutBlock N n K)
      (pre ++ [j]) e).mp he
  have hmemRange : i ∈ List.range (N - K) := by
    rcases List.mem_append.mp hi with hpreI | hsingle
    · rw [hdecomp]
      exact List.mem_append.mpr (Or.inl hpreI)
    · have : i = j := List.mem_singleton.mp hsingle
      subst i
      rw [hdecomp]
      exact List.mem_append.mpr (Or.inr (by simp))
  have hiLt : i < N - K := List.mem_range.mp hmemRange
  have hij : i ≤ j := by
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hipre | hij
    · exact le_of_lt (list_range_prefix_lt hdecomp hipre)
    · exact le_of_eq hij
  have hblock : e ∈ horizontalStripRectangleCutEdges N n
      (-(N : ℤ) + (i : ℤ)) (by omega) (by omega) := by
    simpa [horizontalStripLeftCutBlock, hiLt] using heblock
  have hnotInside := horizontalStripCutEdge_not_inside_left N n
    (-(N : ℤ) + (j : ℤ) + 1) ((N : ℤ) - 1 - (r : ℤ))
    (-(N : ℤ) + (i : ℤ)) (by omega) (by omega) (by omega) e hblock
  change e ∈ subgraphRemovedEdges
    (horizontalStripCutWindowGraph N n
      (-(N : ℤ) + (j : ℤ) + 1) ((N : ℤ) - 1 - (r : ℤ)))
    (horizontalStripCutRectangle N n)
  rw [mem_subgraphRemovedEdges]
  intro hwindow
  exact hnotInside (horizontalStripEdgeInsideColumns_of_windowGraph_mem N n _ _ e hwindow)

private theorem horizontalStripRightScan_tested_subset_windowReveal (N n K : ℕ)
    (A : Finset (horizontalStripCutRectangle N n).edgeSet) (hKN : K ≤ N)
    {l j : ℕ} (_hL : (horizontalStripLeftBlockScan N n K A).2 = some l)
    (hHit : (horizontalStripRightBlockScan N n K A).2 = some j) :
    (horizontalStripRightBlockScan N n K A).1 ⊆
      horizontalStripCutWindowReveal N n
        (-(N : ℤ) + (l : ℤ) + 1) ((N : ℤ) - 1 - (j : ℤ)) := by
  intro e he
  obtain ⟨pre, post, hdecomp, hpre, hclosed, htested⟩ :=
    firstClosedBlockScan_hit_prefix (horizontalStripRightCutBlock N n K) A
      (List.range (N - K)) j hHit
  change e ∈ (firstClosedBlockScan (horizontalStripRightCutBlock N n K) A
    (List.range (N - K))).1 at he
  rw [htested] at he
  obtain ⟨i, hi, heblock⟩ :=
    (firstClosedBlockUnion_mem_iff (horizontalStripRightCutBlock N n K)
      (pre ++ [j]) e).mp he
  have hmemRange : i ∈ List.range (N - K) := by
    rcases List.mem_append.mp hi with hpreI | hsingle
    · rw [hdecomp]
      exact List.mem_append.mpr (Or.inl hpreI)
    · have : i = j := List.mem_singleton.mp hsingle
      subst i
      rw [hdecomp]
      exact List.mem_append.mpr (Or.inr (by simp))
  have hiLt : i < N - K := List.mem_range.mp hmemRange
  have hij : i ≤ j := by
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hipre | hij
    · exact le_of_lt (list_range_prefix_lt hdecomp hipre)
    · exact le_of_eq hij
  have hblock : e ∈ horizontalStripRectangleCutEdges N n
      ((N : ℤ) - 1 - (i : ℤ)) (by omega) (by omega) := by
    simpa [horizontalStripRightCutBlock, hiLt] using heblock
  have hnotInside := horizontalStripCutEdge_not_inside_right N n
    (-(N : ℤ) + (l : ℤ) + 1) ((N : ℤ) - 1 - (j : ℤ))
    ((N : ℤ) - 1 - (i : ℤ)) (by omega) (by omega) (by omega) e hblock
  change e ∈ subgraphRemovedEdges
    (horizontalStripCutWindowGraph N n
      (-(N : ℤ) + (l : ℤ) + 1) ((N : ℤ) - 1 - (j : ℤ)))
    (horizontalStripCutRectangle N n)
  rw [mem_subgraphRemovedEdges]
  intro hwindow
  exact hnotInside (horizontalStripEdgeInsideColumns_of_windowGraph_mem N n _ _ e hwindow)

/-- A two-sided scan record reveals the exact edges removed by the interval
between its first closed cuts; any failed scan reveals the whole outer graph. -/
def horizontalStripClosedCutReveal (N n K : ℕ)
    (A : Finset (horizontalStripCutRectangle N n).edgeSet) :
    Configuration (horizontalStripCutRectangle N n) := by
  classical
  match (horizontalStripLeftBlockScan N n K A).2,
      (horizontalStripRightBlockScan N n K A).2 with
  | some i, some j =>
      exact horizontalStripCutWindowReveal N n
        (-(N : ℤ) + (i : ℤ) + 1) ((N : ℤ) - 1 - (j : ℤ))
  | _, _ => exact Finset.univ

/-- Both two-sided scans test only edges that the reveal removes from the
surviving interval. -/
theorem horizontalStripClosedCutReveal_contains_tested (N n K : ℕ)
    (A : Finset (horizontalStripCutRectangle N n).edgeSet) (hKN : K ≤ N) :
    (horizontalStripLeftBlockScan N n K A).1 ∪
      (horizontalStripRightBlockScan N n K A).1 ⊆ horizontalStripClosedCutReveal N n K A := by
  classical
  by_cases hLnone : (horizontalStripLeftBlockScan N n K A).2 = none
  · simp [horizontalStripClosedCutReveal, hLnone]
  · obtain ⟨l, hLrev⟩ := Option.ne_none_iff_exists.mp hLnone
    have hL : (horizontalStripLeftBlockScan N n K A).2 = some l := hLrev.symm
    by_cases hRnone : (horizontalStripRightBlockScan N n K A).2 = none
    · simp [horizontalStripClosedCutReveal, hL, hRnone]
    · obtain ⟨r, hRrev⟩ := Option.ne_none_iff_exists.mp hRnone
      have hR : (horizontalStripRightBlockScan N n K A).2 = some r := hRrev.symm
      simp only [horizontalStripClosedCutReveal, hL, hR]
      exact Finset.union_subset
        (horizontalStripLeftScan_tested_subset_windowReveal N n K A hKN hL hR)
        (horizontalStripRightScan_tested_subset_windowReveal N n K A hKN hL hR)

private theorem finset_inter_eq_of_subset_agree {E : Type*} [DecidableEq E]
    (A B R T : Finset E) (hT : T ⊆ R) (hAgree : B ∩ R = A ∩ R) :
    B ∩ T = A ∩ T := by
  ext e
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨heB, heT⟩
    have heR := hT heT
    have hiff := congrArg (fun S : Finset E => e ∈ S) hAgree
    have heA : e ∈ A := by
      have : e ∈ B ∩ R := Finset.mem_inter.mpr ⟨heB, heR⟩
      have hmem := hiff.mp this
      exact (Finset.mem_inter.mp hmem).1
    exact ⟨heA, heT⟩
  · rintro ⟨heA, heT⟩
    have heR := hT heT
    have hiff := congrArg (fun S : Finset E => e ∈ S) hAgree
    have heB : e ∈ B := by
      have : e ∈ A ∩ R := Finset.mem_inter.mpr ⟨heA, heR⟩
      have hmem := hiff.mpr this
      exact (Finset.mem_inter.mp hmem).1
    exact ⟨heB, heT⟩

/-- Agreement on the literal revealed outer-edge state fixes both cut scans and
therefore fixes the reveal set. -/
theorem horizontalStripClosedCutReveal_eq_of_agree (N n K : ℕ)
    (A B : Finset (horizontalStripCutRectangle N n).edgeSet) (hKN : K ≤ N)
    (hAgree : B ∩ horizontalStripClosedCutReveal N n K A =
      A ∩ horizontalStripClosedCutReveal N n K A) :
    horizontalStripClosedCutReveal N n K B = horizontalStripClosedCutReveal N n K A := by
  classical
  by_cases hLnone : (horizontalStripLeftBlockScan N n K A).2 = none
  · have hAB : B = A := by
      ext e
      have hmem := congrArg (fun S : Finset (horizontalStripCutRectangle N n).edgeSet => e ∈ S)
        hAgree
      simpa [horizontalStripClosedCutReveal, hLnone] using hmem
    subst B
    rfl
  · obtain ⟨l, hLrev⟩ := Option.ne_none_iff_exists.mp hLnone
    have hL : (horizontalStripLeftBlockScan N n K A).2 = some l := hLrev.symm
    by_cases hRnone : (horizontalStripRightBlockScan N n K A).2 = none
    · have hAB : B = A := by
        ext e
        have hmem := congrArg (fun S : Finset (horizontalStripCutRectangle N n).edgeSet => e ∈ S)
          hAgree
        simpa [horizontalStripClosedCutReveal, hL, hRnone] using hmem
      subst B
      rfl
    · obtain ⟨r, hRrev⟩ := Option.ne_none_iff_exists.mp hRnone
      have hR : (horizontalStripRightBlockScan N n K A).2 = some r := hRrev.symm
      have hTest := horizontalStripClosedCutReveal_contains_tested N n K A hKN
      have hLeftSubset : (horizontalStripLeftBlockScan N n K A).1 ⊆
          horizontalStripClosedCutReveal N n K A := by
        intro e he
        exact hTest (Finset.mem_union.mpr (Or.inl he))
      have hRightSubset : (horizontalStripRightBlockScan N n K A).1 ⊆
          horizontalStripClosedCutReveal N n K A := by
        intro e he
        exact hTest (Finset.mem_union.mpr (Or.inr he))
      have hAgreeL := finset_inter_eq_of_subset_agree A B
        (horizontalStripClosedCutReveal N n K A) (horizontalStripLeftBlockScan N n K A).1
        hLeftSubset hAgree
      have hAgreeR := finset_inter_eq_of_subset_agree A B
        (horizontalStripClosedCutReveal N n K A) (horizontalStripRightBlockScan N n K A).1
        hRightSubset hAgree
      have hScanL := firstClosedBlockScan_eq_of_agree
        (horizontalStripLeftCutBlock N n K) A B (List.range (N - K)) hAgreeL
      have hScanR := firstClosedBlockScan_eq_of_agree
        (horizontalStripRightCutBlock N n K) A B (List.range (N - K)) hAgreeR
      have hScanL' : horizontalStripLeftBlockScan N n K B =
          horizontalStripLeftBlockScan N n K A := hScanL
      have hScanR' : horizontalStripRightBlockScan N n K B =
          horizontalStripRightBlockScan N n K A := hScanR
      unfold horizontalStripClosedCutReveal
      rw [hScanL', hScanR']

/-- When both scans hit, each selected actual cut block is closed in the open
finite-rectangle edge configuration. -/
theorem horizontalStripClosedCutReveal_selected_blocks_closed (N n K : ℕ)
    (A : Finset (horizontalStripCutRectangle N n).edgeSet) (_hKN : K ≤ N)
    {i j : ℕ}
    (hL : (horizontalStripLeftBlockScan N n K A).2 = some i)
    (hR : (horizontalStripRightBlockScan N n K A).2 = some j) :
    Disjoint A (horizontalStripRectangleCutEdges N n
      (-(N : ℤ) + (i : ℤ))
      (by
        have hiMem := (firstClosedBlockScan_hit (horizontalStripLeftCutBlock N n K) A
          (List.range (N - K)) i hL).1
        have _hi : i < N - K := List.mem_range.mp hiMem
        have _hi0 : 0 ≤ (i : ℤ) := by exact_mod_cast (Nat.zero_le i)
        omega)
      (by
        have hiMem := (firstClosedBlockScan_hit (horizontalStripLeftCutBlock N n K) A
          (List.range (N - K)) i hL).1
        have hi : i < N - K := List.mem_range.mp hiMem
        have hiN : i < N := lt_of_lt_of_le hi (Nat.sub_le N K)
        have _hiZ : (i : ℤ) < (N : ℤ) := by exact_mod_cast hiN
        omega)) ∧
    Disjoint A (horizontalStripRectangleCutEdges N n
      ((N : ℤ) - 1 - (j : ℤ))
      (by
        have hjMem := (firstClosedBlockScan_hit (horizontalStripRightCutBlock N n K) A
          (List.range (N - K)) j hR).1
        have hj : j < N - K := List.mem_range.mp hjMem
        have hjN : j < N := lt_of_lt_of_le hj (Nat.sub_le N K)
        have _hjZ : (j : ℤ) < (N : ℤ) := by exact_mod_cast hjN
        omega)
      (by
        have hjMem := (firstClosedBlockScan_hit (horizontalStripRightCutBlock N n K) A
          (List.range (N - K)) j hR).1
        have _hj : j < N - K := List.mem_range.mp hjMem
        have _hj0 : 0 ≤ (j : ℤ) := by exact_mod_cast (Nat.zero_le j)
        omega)) := by
  have hiMem := (firstClosedBlockScan_hit (horizontalStripLeftCutBlock N n K) A
    (List.range (N - K)) i hL).1
  have hjMem := (firstClosedBlockScan_hit (horizontalStripRightCutBlock N n K) A
    (List.range (N - K)) j hR).1
  have hi : i < N - K := List.mem_range.mp hiMem
  have hj : j < N - K := List.mem_range.mp hjMem
  have hiN : i < N := lt_of_lt_of_le hi (Nat.sub_le N K)
  have hjN : j < N := lt_of_lt_of_le hj (Nat.sub_le N K)
  have hNi : -(N : ℤ) ≤ -(N : ℤ) + (i : ℤ) := by omega
  have hNj : -(N : ℤ) ≤ (N : ℤ) - 1 - (j : ℤ) := by omega
  have hKi : -(N : ℤ) + (i : ℤ) < N := by
    have hiNz : (i : ℤ) < (N : ℤ) := by exact_mod_cast hiN
    omega
  have hKj : (N : ℤ) - 1 - (j : ℤ) < N := by
    have hjNz : (j : ℤ) < (N : ℤ) := by exact_mod_cast hjN
    omega
  have hleft := (firstClosedBlockScan_hit (horizontalStripLeftCutBlock N n K) A
    (List.range (N - K)) i hL).2
  have hright := (firstClosedBlockScan_hit (horizontalStripRightCutBlock N n K) A
    (List.range (N - K)) j hR).2
  constructor
  · simpa [horizontalStripLeftCutBlock, hi, hNi, hKi] using hleft
  · simpa [horizontalStripRightCutBlock, hj, hNj, hKj] using hright

/-- The two selected cuts leave the whole central horizontal interval inside
surviving vertices. -/
theorem horizontalStripClosedCutReveal_window_contains_center (N n K : ℕ)
    (A : Finset (horizontalStripCutRectangle N n).edgeSet) (hKN : K ≤ N)
    {i j : ℕ}
    (hL : (horizontalStripLeftBlockScan N n K A).2 = some i)
    (hR : (horizontalStripRightBlockScan N n K A).2 = some j) :
    -(N : ℤ) + (i : ℤ) + 1 ≤ -(K : ℤ) ∧
      (K : ℤ) ≤ (N : ℤ) - 1 - (j : ℤ) := by
  have hiMem := (firstClosedBlockScan_hit (horizontalStripLeftCutBlock N n K) A
    (List.range (N - K)) i hL).1
  have hjMem := (firstClosedBlockScan_hit (horizontalStripRightCutBlock N n K) A
    (List.range (N - K)) j hR).1
  have hi : i < N - K := List.mem_range.mp hiMem
  have hj : j < N - K := List.mem_range.mp hjMem
  have hiAdd : i + K < N := by
    have h := Nat.add_lt_add_right hi K
    simpa [Nat.sub_add_cancel hKN] using h
  have hjAdd : j + K < N := by
    have h := Nat.add_lt_add_right hj K
    simpa [Nat.sub_add_cancel hKN] using h
  have hiAddZ : (i : ℤ) + (K : ℤ) < (N : ℤ) := by exact_mod_cast hiAdd
  have hjAddZ : (j : ℤ) + (K : ℤ) < (N : ℤ) := by exact_mod_cast hjAdd
  omega

end
end PottsContinuity.FKC.Medial
