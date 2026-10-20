-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/WiredArcEdges.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.WiredSampling
public import PottsContinuity.FKC.Medial.DomainBondSides

/-!
# Exact original-edge enumeration of a geometric wired arc

The whole closed segment of a unit bond lies in the forward arc precisely
when that bond is one of the cyclic edges indexed by `a + t`, with `t < k`.
The reverse enumeration uses a strict midpoint and actual unit-edge
intersection geometry, not merely membership of both endpoints in the wired
vertex block. The statements work for every length; in particular they apply
to each proper nonempty arc used for marked boundaries. The supplied cyclic
order is not asserted to be geometrically counterclockwise here.
-/

@[expose] public section

namespace PottsContinuity.FKC.LatticePolygon

open Set OAI.SLEExactGauge Medial

noncomputable section

variable {m : ℕ} (P : LatticePolygon m)

/-- A complete unit segment belongs to the arc exactly when it is one of the
arc's original cyclic edges. Strict midpoint geometry proves the reverse implication. -/
theorem bond_segment_subset_arc_iff (δ : PositiveMesh) (a : ZMod (m + 3))
    (k : ℕ) (e : LatticeBond) :
    complexPlaneCoordinates '' segment ℝ (latticeEmbed δ e.source)
      (latticeEmbed δ e.target) ⊆ (P.toPrePolygon δ).arc a k ↔
      ∃ t : ℕ, t < k ∧ e = P.boundaryBond (a + t) := by
  constructor
  · intro h
    obtain ⟨t, ht, hmid⟩ := Schoenflies.PrePolygon.mem_arc_iff.mp
      (h (mem_image_of_mem _ (e.midpoint_mem_segment δ)))
    change complexPlaneCoordinates (e.midpoint δ) ∈
      segment ℝ (complexPlaneCoordinates (latticeEmbed δ (P.vertex (a + t))))
        (complexPlaneCoordinates (latticeEmbed δ (P.vertex (a + t + 1)))) at hmid
    rw [← complexPlaneCoordinates_image_segment] at hmid
    have hmid := complexPlaneCoordinates.injective.mem_set_image.mp hmid
    refine ⟨t, ht, ?_⟩
    apply (P.eq_boundaryBond_iff (a + t) e).mpr
    by_contra hne
    have he := (mem_inter_lattice_segments_endpoints δ e.adjacent
      (P.adjacent (a + t)) hne ⟨e.midpoint_mem_segment δ, hmid⟩).1
    exact he.elim (e.midpoint_ne_source δ) (e.midpoint_ne_target δ)
  · rintro ⟨t, ht, rfl⟩
    have hs : segment ℝ (latticeEmbed δ (P.boundaryBond (a + t)).source)
        (latticeEmbed δ (P.boundaryBond (a + t)).target) =
        segment ℝ (latticeEmbed δ (P.vertex (a + t)))
          (latticeEmbed δ (P.vertex (a + t + 1))) := by
      rcases Sym2.eq_iff.mp (P.boundaryBond_toSym2 (a + t)) with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · rw [hs, ht]
      · rw [hs, ht, segment_symm]
    rw [hs, complexPlaneCoordinates_image_segment]
    intro z hz
    exact Schoenflies.PrePolygon.mem_arc_iff.mpr ⟨t, ht, hz⟩

/-- The original removal predicate is equivalent to the exact normalized bond enumeration. -/
theorem domainBond_mem_forwardArcRemovedEdges_iff (δ : PositiveMesh)
    (a : ZMod (m + 3)) (k : ℕ) (e : DomainBond δ (P.domain δ)) :
    e.toGraphEdge ∈ P.forwardArcRemovedEdges δ a k ↔
      ∃ t : ℕ, t < k ∧ e.val = P.boundaryBond (a + t) :=
  (P.mem_forwardArcRemovedEdges_iff δ a k e.source e.target
    ⟨e.val.adjacent, e.property⟩).trans (P.bond_segment_subset_arc_iff δ a k e.val)

end
end PottsContinuity.FKC.LatticePolygon
