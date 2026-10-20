-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripCutRectangle.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripCutGeometry
public import PottsContinuity.FKC.Rectangle
public import PottsContinuity.FKC.FiniteFK.SubgraphComparison
public import PottsContinuity.FKC.FiniteFK.Graph

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC
open Finset

noncomputable section

/-- The finite rectangle containing the strip portion with columns `-M,...,M`
and rows `0,...,2*n`. -/
def horizontalStripCutRectangle (M n : ℕ) :=
  rectangleGraph (-(M : ℤ), 0) (2 * M) (2 * n)

def horizontalStripRectangleVertexEmbedding (M n : ℕ) :
    RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n) ↪ LatticeVertex where
  toFun := fun v => v.1
  inj' := Subtype.val_injective

/-- The actual original unordered edge carried by a rectangle edge. -/
def horizontalStripRectangleOriginalEdge (M n : ℕ)
    (e : (horizontalStripCutRectangle M n).edgeSet) : squareLattice.edgeSet :=
  FiniteFK.embeddedEdgeEmbedding (horizontalStripCutRectangle M n) squareLattice
    (horizontalStripRectangleVertexEmbedding M n) (by
      intro x y hxy
      rw [SimpleGraph.map_adj] at hxy
      rcases hxy with ⟨u, v, huv, rfl, rfl⟩
      exact (rectangleGraph_adj_iff (-(M : ℤ), 0) (2 * M) (2 * n) u v).mp huv) e

@[simp] theorem horizontalStripRectangleOriginalEdge_val (M n : ℕ)
    (e : (horizontalStripCutRectangle M n).edgeSet) :
    (horizontalStripRectangleOriginalEdge M n e).val = Sym2.map
    (horizontalStripRectangleVertexEmbedding M n) e.val := by
  rfl

def horizontalStripRectangleCutSource (M n : ℕ) (k : ℤ)
    (hleft : -(M : ℤ) ≤ k) (hright : k < M) (y : ℕ) (hy : y < 2 * n + 1) :
    RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n) :=
  ⟨(k, (y : ℤ)), by
    rw [mem_latticeRectangle]
    change (-(M : ℤ) ≤ k ∧ k ≤ -(M : ℤ) + (2 * M : ℕ)) ∧
      (0 ≤ (y : ℤ) ∧ (y : ℤ) ≤ 0 + (2 * n : ℕ))
    constructor
    · constructor
      · exact hleft
      · omega
    · constructor
      · exact_mod_cast (Nat.zero_le y)
      · have : y ≤ 2 * n := by omega
        simpa using (show (y : ℤ) ≤ 2 * (n : ℤ) by exact_mod_cast this)⟩

def horizontalStripRectangleCutTarget (M n : ℕ) (k : ℤ)
    (hleft : -(M : ℤ) ≤ k) (hright : k < M) (y : ℕ) (hy : y < 2 * n + 1) :
    RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n) :=
  ⟨(k + 1, (y : ℤ)), by
    rw [mem_latticeRectangle]
    change (-(M : ℤ) ≤ k + 1 ∧ k + 1 ≤ -(M : ℤ) + (2 * M : ℕ)) ∧
      (0 ≤ (y : ℤ) ∧ (y : ℤ) ≤ 0 + (2 * n : ℕ))
    constructor
    · constructor
      · omega
      · omega
    · constructor
      · exact_mod_cast (Nat.zero_le y)
      · have : y ≤ 2 * n := by omega
        simpa using (show (y : ℤ) ≤ 2 * (n : ℤ) by exact_mod_cast this)⟩

def horizontalStripRectangleCutEdge (M n : ℕ) (k : ℤ)
    (hleft : -(M : ℤ) ≤ k) (hright : k < M) (y : ℕ) (hy : y < 2 * n + 1) :
    (horizontalStripCutRectangle M n).edgeSet := by
  let u := horizontalStripRectangleCutSource M n k hleft hright y hy
  let v := horizontalStripRectangleCutTarget M n k hleft hright y hy
  refine ⟨s(u, v), ?_⟩
  apply (horizontalStripCutRectangle M n).mem_edgeSet.mpr
  apply (rectangleGraph_adj_iff (-(M : ℤ), 0) (2 * M) (2 * n) u v).2
  rw [squareLattice_adj_iff]
  left
  constructor
  · left
    simp [u, v, horizontalStripRectangleCutSource, horizontalStripRectangleCutTarget]
  · rfl

private theorem horizontalStripRectangleCutEdge_original (M n : ℕ) (k : ℤ)
    (hleft : -(M : ℤ) ≤ k) (hright : k < M) (y : ℕ) (hy : y < 2 * n + 1) :
    horizontalStripRectangleOriginalEdge M n
      (horizontalStripRectangleCutEdge M n k hleft hright y hy) =
        latticeBondEdge (horizontalStripCutBond k y) := by
  apply Subtype.ext
  change (horizontalStripRectangleVertexEmbedding M n).sym2Map
      (horizontalStripRectangleCutEdge M n k hleft hright y hy).val = _
  simp [horizontalStripRectangleCutEdge, horizontalStripRectangleCutSource,
    horizontalStripRectangleCutTarget, horizontalStripRectangleVertexEmbedding,
    horizontalStripCutBond, latticeBondEdge, LatticeBond.toSym2,
    LatticeBond.source, LatticeBond.target]

/-- The finite-rectangle cut, using the original unordered edges. -/
def horizontalStripRectangleCutEdges (M n : ℕ) (k : ℤ)
    (hleft : -(M : ℤ) ≤ k) (hright : k < M) :
    Finset (horizontalStripCutRectangle M n).edgeSet := by
  classical
  exact (Finset.univ : Finset (Fin (2 * n + 1))).image (fun y =>
    horizontalStripRectangleCutEdge M n k hleft hright y.val y.isLt)

private theorem horizontalStripRectangleCutEdge_injective (M n : ℕ) (k : ℤ)
    (hleft : -(M : ℤ) ≤ k) (hright : k < M) :
    Function.Injective (fun y : Fin (2 * n + 1) =>
      horizontalStripRectangleCutEdge M n k hleft hright y.val y.isLt) := by
  intro y z heq
  have hglobal := congrArg (horizontalStripRectangleOriginalEdge M n) heq
  rw [horizontalStripRectangleCutEdge_original, horizontalStripRectangleCutEdge_original] at hglobal
  have hb : horizontalStripCutBond k y.val = horizontalStripCutBond k z.val :=
    LatticeBond.toSym2_injective (congrArg Subtype.val hglobal)
  have hyz := congrArg (fun b : LatticeBond => b.base.2) hb
  apply Fin.ext
  have hyz' : (y.val : ℤ) = z.val := by simpa [horizontalStripCutBond] using hyz
  exact_mod_cast hyz' 

theorem horizontalStripRectangleCutEdges_card (M n : ℕ) (k : ℤ)
    (hleft : -(M : ℤ) ≤ k) (hright : k < M) :
    (horizontalStripRectangleCutEdges M n k hleft hright).card = 2 * n + 1 := by
  rw [horizontalStripRectangleCutEdges,
    Finset.card_image_of_injective _ (horizontalStripRectangleCutEdge_injective M n k hleft hright)]
  simp

theorem horizontalStripRectangleOriginalEdge_injective (M n : ℕ) :
    Function.Injective (horizontalStripRectangleOriginalEdge M n) := by
  intro e f hef
  exact (FiniteFK.embeddedEdgeEmbedding (horizontalStripCutRectangle M n) squareLattice
    (horizontalStripRectangleVertexEmbedding M n) (by
      intro x y hxy
      rw [SimpleGraph.map_adj] at hxy
      rcases hxy with ⟨u, v, huv, rfl, rfl⟩
      exact (rectangleGraph_adj_iff (-(M : ℤ), 0) (2 * M) (2 * n) u v).mp huv)).injective hef

theorem horizontalStripRectangleCutEdges_original_image (M n : ℕ) (k : ℤ)
    (hleft : -(M : ℤ) ≤ k) (hright : k < M) :
    (horizontalStripRectangleCutEdges M n k hleft hright).image
      (horizontalStripRectangleOriginalEdge M n) = horizontalStripCutEdges n k := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨f, hf, hfe⟩
    rcases Finset.mem_image.mp hf with ⟨y, hy, rfl⟩
    rw [horizontalStripRectangleCutEdge_original] at hfe
    subst e
    exact Finset.mem_image.mpr ⟨y.val, Finset.mem_range.mpr y.isLt, rfl⟩
  · intro he
    rcases Finset.mem_image.mp he with ⟨y, hy, rfl⟩
    let z : Fin (2 * n + 1) := ⟨y, Finset.mem_range.mp hy⟩
    refine Finset.mem_image.mpr ⟨horizontalStripRectangleCutEdge M n k hleft hright z.val z.isLt,
      ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩
    · rw [horizontalStripRectangleCutEdge_original]

theorem horizontalStripRectangleCutEdges_disjoint_of_ne (M n : ℕ) {k l : ℤ}
    (hleftK : -(M : ℤ) ≤ k) (hrightK : k < M)
    (hleftL : -(M : ℤ) ≤ l) (hrightL : l < M) (hkl : k ≠ l) :
    Disjoint (horizontalStripRectangleCutEdges M n k hleftK hrightK)
      (horizontalStripRectangleCutEdges M n l hleftL hrightL) := by
  rw [Finset.disjoint_left]
  intro e heK heL
  have hKmem : horizontalStripRectangleOriginalEdge M n e ∈ horizontalStripCutEdges n k := by
    have hm : horizontalStripRectangleOriginalEdge M n e ∈
        (horizontalStripRectangleCutEdges M n k hleftK hrightK).image
          (horizontalStripRectangleOriginalEdge M n) :=
      Finset.mem_image.mpr ⟨e, heK, rfl⟩
    rwa [horizontalStripRectangleCutEdges_original_image] at hm
  have hLmem : horizontalStripRectangleOriginalEdge M n e ∈ horizontalStripCutEdges n l := by
    have hm : horizontalStripRectangleOriginalEdge M n e ∈
        (horizontalStripRectangleCutEdges M n l hleftL hrightL).image
          (horizontalStripRectangleOriginalEdge M n) :=
      Finset.mem_image.mpr ⟨e, heL, rfl⟩
    rwa [horizontalStripRectangleCutEdges_original_image] at hm
  have hnot := (Finset.disjoint_left.mp (horizontalStripCutEdges_disjoint_of_ne n hkl))
    hKmem
  exact hnot hLmem

/-- The whole-plane open graph restricted to the finite strip rectangle. -/
def horizontalStripRectangleOpenGraph (M n : ℕ) (ω : LatticeConfiguration) :
    SimpleGraph (RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)) where
  Adj u v := (wholePlaneOpenPrimalGraph ω).Adj u.1 v.1
  symm := ⟨by
    intro u v h
    exact h.symm⟩
  loopless := ⟨by
    intro u h
    exact (wholePlaneOpenPrimalGraph ω).loopless.irrefl u h⟩

