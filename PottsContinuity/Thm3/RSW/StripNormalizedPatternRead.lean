module

public import PottsContinuity.Thm3.RSW.StripWindowPatternComparison
public import PottsContinuity.Thm3.RSW.StripLimit
public import PottsContinuity.Thm3.Prop4.FKCRectangleDualLift

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory Filter Topology FKC.Medial
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The literal physical normalization of every original infinite-strip edge. -/
def stripNormalizedEmbedding (n : ℕ) : stripGraph n ↪g FKC.squareLattice :=
  Thm3.Prop4.fkcOriginalLatticeIso.symm.toEmbedding.comp
    ((latticeTranslationIso (0,(n:ℤ))).toEmbedding.comp (stripPlaneEmbedding n))

/-- Every original window edge keeps its physical endpoints under normalization. -/
theorem stripNormalizedEmbedding_window_edge (n M : ℕ)
    (e : (stripGraph n).edgeSet)
    (f : (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).edgeSet)
    (hf : Sym2.map Subtype.val f.val = Sym2.map Subtype.val e.val) :
    horizontalStripRectangleOriginalEdge M (2*n)
      (configurationIsoEdgeEquiv (stripWindowCutIso n M) f) =
        (stripNormalizedEmbedding n).mapEdgeSet e := by
  apply Subtype.ext
  rw [horizontalStripRectangleOriginalEdge_val]
  change Sym2.map _ (Sym2.map (stripWindowCutIso n M) f.val) =
    Sym2.map (stripNormalizedEmbedding n) e.val
  rw [Sym2.map_map]
  have h := congrArg (Sym2.map (fun v : ℤ×ℤ => (v.1,v.2+(n:ℤ)))) hf
  rw [Sym2.map_map,Sym2.map_map] at h
  convert h using 1 <;> congr 1; funext v;
    simp [stripNormalizedEmbedding,stripPlaneEmbedding,
      latticeTranslationIso,Thm3.Prop4.fkcOriginalLatticeIso]
  change (v.val.1+0,v.val.2+(n:ℤ))=(v.val.1,v.val.2+(n:ℤ))
  simp only [add_zero]


/-- Membership of a normalized sampled bond is exactly the state of its
original window bond. -/
theorem stripNormalizedEmbedding_open_iff (n M : ℕ)
    (e : (stripGraph n).edgeSet)
    (f : (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).edgeSet)
    (hf : Sym2.map Subtype.val f.val = Sym2.map Subtype.val e.val)
    (A : Configuration (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ)))) :
    (stripNormalizedEmbedding n).mapEdgeSet e ∈
      (configurationIso (stripWindowCutIso n M) A).image
        (horizontalStripRectangleOriginalEdge M (2*n)) ↔ f ∈ A := by
  classical
  rw [← stripNormalizedEmbedding_window_edge n M e f hf]
  rw [Finset.mem_image]
  constructor
  · rintro ⟨g,hg,hgf⟩
    have hgf' := FKC.Medial.horizontalStripRectangleOriginalEdge_injective M (2*n) hgf
    subst g
    change configurationIsoEdgeEquiv (stripWindowCutIso n M) f ∈
      A.map (configurationIsoEdgeEquiv (stripWindowCutIso n M)).toEmbedding at hg
    exact Finset.mem_map.mp hg |>.elim fun h hh => by
      have heq := (configurationIsoEdgeEquiv (stripWindowCutIso n M)).injective hh.2
      simpa only [heq] using hh.1
  · intro hfA
    refine ⟨configurationIsoEdgeEquiv (stripWindowCutIso n M) f,?_,rfl⟩
    change configurationIsoEdgeEquiv (stripWindowCutIso n M) f ∈
      A.map (configurationIsoEdgeEquiv (stripWindowCutIso n M)).toEmbedding
    exact Finset.mem_map.mpr ⟨f,hfA,rfl⟩

end
end PottsContinuity.RSW
