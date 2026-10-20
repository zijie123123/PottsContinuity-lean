module

public import PottsContinuity.PlanarMixed.ClippedCutCarrier
public import PottsContinuity.PlanarMixed.FiniteSlit.SourceRectangleEmbedding

/-! The source rectangle clipped from the balanced slit reference. Missing
reference bonds are exactly the original slit-crossing bonds above the tip. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK
noncomputable section
local instance rectangleClippingEdgeDecidableEq {U : Type*} (G : SimpleGraph U) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Literal coordinate inclusion of an entire source rectangle in the finite
reference vertex carrier. This asserts no source-edge inclusion in the slit. -/
def rectangleIntoReference (M : ℕ) (x : ℤ) (w h : ℕ) (hM : 1 ≤ M)
    (hleft : x-(M:ℤ) ≤ 0) (hright : (w:ℤ) ≤ x+(M:ℤ)-1) (hheight : h ≤ M) :
    RectangleVertex (0,0) w h ↪ Vertex M x where
  toFun v := ⟨v.val,by
    rw [mem_rectangle_iff M x hM]
    have hv := (PD.FK.mem_latticeRectangle _ _ _ _).mp v.property
    dsimp at hv
    omega⟩
  inj' := fun u v huv => Subtype.ext (congrArg (fun z : Vertex M x => z.val) huv)

/-- All original rectangle bonds removed by the strict-above-tip slit. -/
def rectangleSlitBonds (w h : ℕ) (x y : ℤ) :
    Configuration (rectangleGraph (0,0) w h) :=
  subgraphRemovedEdges ((slitRetainedBondGraph x y).comap Subtype.val)
    (rectangleGraph (0,0) w h)

/-- The source slit carrier is independent of the containing reference size. -/
theorem rectangle_missing_reference_eq_slit (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 1 ≤ M) (hleft : x-(M:ℤ) ≤ 0) (hright : (w:ℤ) ≤ x+(M:ℤ)-1)
    (hheight : h ≤ M) :
    subgraphRemovedEdges
      ((graph M x y).comap (rectangleIntoReference M x w h hM hleft hright hheight))
      (rectangleGraph (0,0) w h) = rectangleSlitBonds w h x y := by
  classical
  apply Finset.ext
  rintro ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [rectangleSlitBonds,mem_subgraphRemovedEdges,mem_subgraphRemovedEdges]
    change (¬ (graph M x y).Adj _ _) ↔ ¬ (slitRetainedBondGraph x y).Adj u.val v.val
    rw [graph_adj_iff_retained]
    rfl

namespace CrosscutData
variable {M : ℕ} {x y : ℤ} (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y)
  (w h : ℕ) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
  (hp : ∀ v ∈ D.first.support, 0 ≤ v.val.1 ∧ v.val.1 ≤ (w:ℤ) ∧ v.val.2 ≤ (h:ℤ))
  (hq : ∀ v ∈ D.second.support, 0 ≤ v.val.1 ∧ v.val.1 ≤ (w:ℤ) ∧ v.val.2 ≤ (h:ℤ))
  (hleft : x-(M:ℤ) ≤ 0) (hright : (w:ℤ) ≤ x+(M:ℤ)-1) (hheight : h ≤ M)
local notation "f" => rectangleIntoReference M x w h (by omega) hleft hright hheight
local notation "r" => D.rank hM hy
local notation "k" => D.sourceRectangleEmbedding hM hy w h hx hxw hp hq

/-- Both inclusions retain exactly the original lattice coordinates. -/
theorem sourceRectangle_reference_comp (v : rankedBandVertices r) : f (k v) = v.val :=
  Subtype.ext rfl

/-- Exact source complement: every deleted slit bond and both closed
exteriors are exposed. No other source bond is removed. -/
theorem sourceRectangle_active_complement :
    subgraphRemovedEdges
      ((edgeRestriction (rankedBandGraph (graph M x y) r)
        (bandArcBonds (graph M x y) r)).map k) (rectangleGraph (0,0) w h) =
      rectangleSlitBonds w h x y ∪ outerCutReveal (rectangleGraph (0,0) w h) (r ∘ f) := by
  have hc := clipped_active_complement (graph M x y) (rectangleGraph (0,0) w h) r
    (orderedCutRank_edges (D.orderedCuts hM hy)) f k
    (D.sourceRectangle_reference_comp hM hy w h hx hxw hp hq hleft hright hheight)
  rw [rectangle_missing_reference_eq_slit] at hc
  exact hc

end CrosscutData
end
end PottsContinuity.PlanarMixed.FiniteSlit
