module

public import PottsContinuity.Thm3.RSW.StripWindow
public import PottsContinuity.Thm3.RSW.EmbeddedComparison
public import PottsContinuity.PD.FK.BoundaryPartitionLaw

/-!
# Increasing-width comparison for top-wired strip windows

The argument follows FKconvergence, an earlier formalization by the same author that is not
publicly accessible (see `related_formalizations` in formalization.yaml), file
`FiniteFK/HorizontalStripTopBoundary.lean`, adapted to the actual frozen induced graph on
[-m,m]×[-n,3n], arbitrary interior edge parameter, all q≥1, and the explicit `i=0` lateral
convention.
-/

@[expose] public section

namespace PottsContinuity.RSW

open PD.FK PD.FK.FiniteProbability

noncomputable section

local instance stripMonotoneEdgeFintype (n m : ℕ) :
    Fintype (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))).edgeSet :=
  Fintype.ofFinite _

/-- Increasing the horizontal radius enlarges the actual finite strip window. -/
theorem stripWindow_mono (n : ℕ) : Monotone (stripWindow n) := by
  intro M N hMN v hv
  simp only [stripWindow, latticeRectangle, Finset.mem_product, Finset.mem_Icc] at hv ⊢
  constructor
  · constructor <;> omega
  · exact hv.2

/-- Literal inclusion of the window vertex carriers, retaining all coordinates. -/
def stripWindowEmbedding {n M N : ℕ} (hMN : M ≤ N) :
    (stripWindow n M : Set (ℤ × ℤ)) ↪ (stripWindow n N : Set (ℤ × ℤ)) where
  toFun v := ⟨v.1, stripWindow_mono n hMN v.2⟩
  inj' := fun _u _v h => Subtype.ext
    (congrArg (fun w : (stripWindow n N : Set (ℤ × ℤ)) => w.val) h)

/-- The window embedding maps every original edge into the larger induced graph. -/
theorem stripWindow_map_le {n M N : ℕ} (hMN : M ≤ N) :
    (squareLattice.induce (stripWindow n M : Set (ℤ × ℤ))).map
        (stripWindowEmbedding (n := n) hMN) ≤
      squareLattice.induce (stripWindow n N : Set (ℤ × ℤ)) := by
  rw [SimpleGraph.map_le_iff_le_comap]
  intro u v huv
  exact huv

/-- Top-only wiring pulls back exactly to top-only wiring in every smaller
window. This assertion intentionally does not include lateral wiring. -/
theorem stripWindow_top_pullback_partition {n M N : ℕ} (hMN : M ≤ N) :
    (isolatedExtensionPullbackBoundary (stripWindowEmbedding (n := n) hMN)
      (stripWindowBoundary n N 0)).partition = (stripWindowBoundary n M 0).partition := by
  apply Setoid.ext
  intro u v
  change (stripWindowBoundary n N 0).partition.r
      (stripWindowEmbedding hMN u) (stripWindowEmbedding hMN v) ↔
    (stripWindowBoundary n M 0).partition.r u v
  change (stripWindowEmbedding hMN u = stripWindowEmbedding hMN v ∨
    stripWindowEmbedding hMN u ∈ stripWindowWiredVertices n N 0 ∧
      stripWindowEmbedding hMN v ∈ stripWindowWiredVertices n N 0) ↔
    (u = v ∨ u ∈ stripWindowWiredVertices n M 0 ∧ v ∈ stripWindowWiredVertices n M 0)
  simp only [stripWindowWiredVertices, Set.mem_ofPred_eq, Fin.zero_ne_one,
    false_and, or_false]
  constructor
  · rintro (h | ⟨hu, hv⟩)
    · exact Or.inl ((stripWindowEmbedding hMN).injective h)
    · exact Or.inr ⟨hu, hv⟩
  · rintro (h | ⟨hu, hv⟩)
    · exact Or.inl (congrArg (stripWindowEmbedding hMN) h)
    · exact Or.inr ⟨hu, hv⟩

end

end PottsContinuity.RSW
