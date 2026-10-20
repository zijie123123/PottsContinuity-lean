module

public import PottsContinuity.Thm3.Prop4.MarkedUpperRecordedPath
public import PottsContinuity.Thm3.Prop4.MarkedJointRawReveal

/-! # Both concrete recorded paths persist in the raw two-sided source record -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section
local instance markedJointRawPathsEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _

/-- The raw two-sided actual record retains prescribed open walks with the WHOLE
supports of the same nonempty concrete upper and lower traces. -/
theorem markedJointBoxRawReveal_recorded_paths (n : ℕ)
    (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n)))
    (hL : (markedLowerBoxTrace n u v A).Nonempty)
    (hU : (markedUpperBoxTrace n u v A).Nonempty) :
    ∃ pU pL : (openGraph (finiteLatticeGraph (box n))
      (Exploration.revealRecordConfiguration (markedJointBoxRawReveal n u v) A).val).Walk u v,
      pU.support.toFinset = markedUpperBoxTrace n u v A ∧
        pL.support.toFinset = markedLowerBoxTrace n u v A := by
  classical
  obtain ⟨pL,hpL⟩ := markedLowerBoxTrace_recorded_walk n u v A hL
  obtain ⟨pU,hpU⟩ := markedUpperBoxTrace_recorded_walk n u v A hU
  have subL : A ∩ markedLowerBoxRawReveal n u v A ⊆
      (Exploration.revealRecordConfiguration (markedJointBoxRawReveal n u v) A).val := by
    intro e he
    refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp he).1,?_⟩
    exact Finset.mem_union_left _ (Finset.mem_inter.mp he).2
  have subU : A ∩ markedUpperBoxRawReveal n u v A ⊆
      (Exploration.revealRecordConfiguration (markedJointBoxRawReveal n u v) A).val := by
    intro e he
    refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp he).1,?_⟩
    exact Finset.mem_union_right _ (Finset.mem_inter.mp he).2
  refine ⟨pU.mapLe (openGraph_mono subU),pL.mapLe (openGraph_mono subL),?_,?_⟩
  · simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hpU
  · simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hpL

end
end PottsContinuity.Thm3.Prop4
