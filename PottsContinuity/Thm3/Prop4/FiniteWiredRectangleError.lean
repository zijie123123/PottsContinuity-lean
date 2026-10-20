module

public import PottsContinuity.Thm3.Prop4.RectangleWiredCrossing
public import PottsContinuity.Thm3.Prop4.FiniteWiredComparison

/-!
# Actual finite wired rectangle error

The finite induced-domain restriction and the original rectangle restriction
read the same original edge states. The decreasing-event comparison of
`FiniteWiredComparison` therefore
transfers the proved wired-plane error with no geometric containment premise.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.RCInfinite
noncomputable section

/-- Two existing finite restriction APIs agree on the entire original induced sample. -/
theorem induced_original_restriction_eq (S : Finset LatticeVertex) (ω : LatticeConfiguration) :
    Infinite.latticeGraphRestriction (finiteLatticeGraph S) (finiteDomainEmbedding S)
      (finiteDomainEmbedding_map_le S) ω =
    BD12.embeddedRestriction (finiteLatticeGraph S) (frozenEdgeEmbedding S) ω := by
  classical
  ext e
  simp only [Infinite.latticeGraphRestriction,BD12.embeddedRestriction,
    Finset.mem_filter,Finset.mem_univ,true_and]
  have he : embeddedEdgeEmbedding (finiteLatticeGraph S) PD.FK.squareLattice
      (finiteDomainEmbedding S) (finiteDomainEmbedding_map_le S) e = frozenEdgeEmbedding S e := by
    apply Subtype.ext
    rfl
  exact Iff.of_eq (congrArg (fun e : PD.FK.squareLattice.edgeSet => ω e = true) he)

end
end PottsContinuity.Thm3.Prop4
