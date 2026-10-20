-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/BoundaryWiring.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.PolygonDomain
public import PottsContinuity.FKC.FiniteFK.Model
public import Schoenflies.PrePolygonArc

/-!
# Wiring a specified forward arc of a lattice polygon

The wired vertices are exactly the vertices of the full closure graph whose
Euclidean positions lie on the specified geometric closed arc. They form one
boundary block; every other vertex is a singleton. Finiteness comes from the
bounded polygonal domain and supplies an actual critical FK probability law.

This file uses the polygon's supplied cyclic order, without asserting geometric
counterclockwise orientation or approximation convergence. In the source's
Dobrushin convention the free arc runs from the first mark to the second; the
wired arc is the complementary forward arc, so its eventual call has starting
index `a + k` and length `m + 3 - k`. The law here samples the full closure graph;
removing wired-arc edges is a separate marginal construction.
-/

@[expose] public section

namespace PottsContinuity.FKC.LatticePolygon

noncomputable section

open Set OAI.SLEExactGauge FiniteFK

variable {m : ℕ} (P : LatticePolygon m)

/-- Actual closure-graph vertices lying on the specified geometric forward arc. -/
def forwardArcVertices (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ) :
    Set (DomainVertex δ (P.domain δ)) :=
  {v | complexPlaneCoordinates (domainVertexEmbed δ (P.domain δ) v) ∈
    (P.toPrePolygon δ).arc a k}

/-- The starting marked vertex belongs to every nonempty forward arc. -/
theorem boundaryVertex_mem_forwardArc_start (δ : PositiveMesh) (a : ZMod (m + 3))
    {k : ℕ} (hk : 1 ≤ k) : P.boundaryVertex δ a ∈ P.forwardArcVertices δ a k :=
  (P.toPrePolygon δ).vertex_mem_arc a hk

/-- The ending marked vertex is included in the closed wired arc. -/
theorem boundaryVertex_mem_forwardArc_finish (δ : PositiveMesh) (a : ZMod (m + 3))
    {k : ℕ} (hk : 1 ≤ k) : P.boundaryVertex δ (a + k) ∈ P.forwardArcVertices δ a k :=
  (P.toPrePolygon δ).vertex_add_mem_arc a hk

/-- Every initial vertex of an edge in the forward arc is wired. -/
theorem boundaryVertex_mem_forwardArc_of_lt (δ : PositiveMesh) (a : ZMod (m + 3))
    {k t : ℕ} (ht : t < k) :
    P.boundaryVertex δ (a + t) ∈ P.forwardArcVertices δ a k := by
  apply Schoenflies.PrePolygon.mem_arc_iff.mpr
  exact ⟨t, ht, left_mem_segment ℝ _ _⟩

/-- The geometric wired vertices are exactly the cyclic vertices from `a`
through `a + k`, including both endpoints. Unit edges contain no other lattice points. -/
theorem mem_forwardArcVertices_iff (δ : PositiveMesh) (a : ZMod (m + 3))
    {k : ℕ} (hk : 1 ≤ k) (v : DomainVertex δ (P.domain δ)) :
    v ∈ P.forwardArcVertices δ a k ↔
      ∃ t : ℕ, t ≤ k ∧ P.boundaryVertex δ (a + t) = v := by
  constructor
  · intro hv
    obtain ⟨t, ht, hmem⟩ := Schoenflies.PrePolygon.mem_arc_iff.mp hv
    change complexPlaneCoordinates (latticeEmbed δ v.val) ∈
      segment ℝ (complexPlaneCoordinates (latticeEmbed δ (P.vertex (a + t))))
        (complexPlaneCoordinates (latticeEmbed δ (P.vertex (a + t + 1)))) at hmem
    rw [← complexPlaneCoordinates_image_segment] at hmem
    have hseg := complexPlaneCoordinates.injective.mem_set_image.mp hmem
    rcases (latticeEmbed_mem_segment_iff δ (P.adjacent (a + t))).mp hseg with h | h
    · exact ⟨t, ht.le, Subtype.ext h.symm⟩
    · refine ⟨t + 1, ht, Subtype.ext ?_⟩
      simpa only [boundaryVertex_val, Nat.cast_add, Nat.cast_one, ← add_assoc] using h.symm
  · rintro ⟨t, ht, rfl⟩
    rcases lt_or_eq_of_le ht with ht | rfl
    · exact P.boundaryVertex_mem_forwardArc_of_lt δ a ht
    · exact P.boundaryVertex_mem_forwardArc_finish δ a hk

/-- Wire precisely the geometric forward-arc vertices, leaving all others singleton. -/
def forwardArcBoundary (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ) :
    BoundaryCondition (DomainVertex δ (P.domain δ)) :=
  BoundaryCondition.wired (P.forwardArcVertices δ a k)

/-- More generally, any original geometric edge contained in this arc has
identified endpoints. This statement adds no edge to an actual open path. -/
theorem forwardArcBoundary_related_of_segment_subset (δ : PositiveMesh)
    (a : ZMod (m + 3)) (k : ℕ) {u v : DomainVertex δ (P.domain δ)}
    (hsegment : complexPlaneCoordinates ''
      segment ℝ (domainVertexEmbed δ (P.domain δ) u) (domainVertexEmbed δ (P.domain δ) v) ⊆
        (P.toPrePolygon δ).arc a k) :
    (P.forwardArcBoundary δ a k).partition.r u v :=
  Or.inr ⟨hsegment (mem_image_of_mem _ (left_mem_segment ℝ _ _)),
    hsegment (mem_image_of_mem _ (right_mem_segment ℝ _ _))⟩

local instance polygonDomainVertexFinite (δ : PositiveMesh) :
    Finite (DomainVertex δ (P.domain δ)) := P.finite_domainVertex δ

/-- The actual critical FK probability on every original edge of the full closure graph,
with exactly the specified geometric forward arc wired. -/
def forwardArcLaw (δ : PositiveMesh) (q : ClusterWeight) (a : ZMod (m + 3)) (k : ℕ) :
    PMF (Configuration (domainLatticeGraph δ (P.domain δ))) :=
  law (domainLatticeGraph δ (P.domain δ)) q (P.forwardArcBoundary δ a k)

end

end PottsContinuity.FKC.LatticePolygon
