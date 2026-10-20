-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxSplitBoundaryLift.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxSplitCoverDomain
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- The original slit-box vertex underlying either kind of split vertex. -/
def slitBoxSplitBaseVertex (n : ℕ) : SlitBoxSplitCoverVertex n → SlitBoxVertex n :=
  Sum.elim (fun v => v.1) (fun v => v.1.1)

theorem slitBoxSplitCoverMap_projection_base (n : ℕ)
    (v : SlitBoxSplitCoverVertex n) :
    (slitBoxSplitCoverMap n v).1 = (slitBoxSplitBaseVertex n v).val := by
  cases v with
  | inl x => rfl
  | inr x => rfl

/-- An interior neighbor of the arc lifts to its selected side in the cover.
The side records whether the interior vertex lies to the right of the slit. -/
theorem slitBoxInteriorCoverLift_adj_arcSide (n : ℕ)
    (u : SlitBoxInteriorVertex n) (v : SlitBoxVertex n)
    (hv : v ∈ slitBoxWiredArc n)
    (hadj : (slitBoxGraph n).Adj u.1 v) :
    parafermionicCoverGraph.Adj (slitBoxInteriorCoverLift n u)
      (slitBoxSplitCoverMap n
        (Sum.inr (⟨v, hv⟩, decide (0 < u.1.val.1)))) := by
  have hbase := (slitBoxGraph_adj_iff n u.1 v).mp hadj |>.1
  have hv' := (mem_slitBoxWiredArc_iff n v).mp hv
  have hshift : parafermionicCoverSheetShift u.1.val v.val = 0 := by
    unfold parafermionicCoverSheetShift
    split_ifs <;> omega
  change squareLattice.Adj u.1.val v.val ∧ _
  refine ⟨hbase, ?_⟩
  simp [slitBoxInteriorCoverLift, slitBoxSplitCoverMap, hshift]

theorem slitBoxSplitCoverGraph_interior_arc_adj (n : ℕ)
    (u : SlitBoxInteriorVertex n) (v : SlitBoxVertex n)
    (hv : v ∈ slitBoxWiredArc n)
    (hadj : (slitBoxGraph n).Adj u.1 v) :
    (slitBoxSplitCoverGraph n).Adj (Sum.inl u)
      (Sum.inr (⟨v, hv⟩, decide (0 < u.1.val.1))) := by
  rw [slitBoxSplitCoverGraph_adj_iff]
  refine ⟨slitBoxInteriorCoverLift_adj_arcSide n u v hv hadj, ?_⟩
  intro hboth
  exact (slitBoxSplitCoverMap_inl_not_boundary n u) hboth.1

/-- Every actual slit edge has a split-graph representative with exactly the
same ordered pair of underlying slit-box vertices. -/
theorem slitBoxSplitCoverGraph_lifts_slit_edge (n : ℕ)
    (u v : SlitBoxVertex n) (hadj : (slitBoxGraph n).Adj u v) :
    ∃ x y : SlitBoxSplitCoverVertex n,
      (slitBoxSplitCoverGraph n).Adj x y ∧
      slitBoxSplitBaseVertex n x = u ∧ slitBoxSplitBaseVertex n y = v := by
  by_cases hu : u ∈ slitBoxWiredArc n
  · by_cases hv : v ∈ slitBoxWiredArc n
    · exact (slitBoxGraph_no_adj_on_wiredArc n hu hv hadj).elim
    · let vi : SlitBoxInteriorVertex n := ⟨v, hv⟩
      refine ⟨Sum.inr (⟨u, hu⟩, decide (0 < v.val.1)), Sum.inl vi, ?_, ?_, ?_⟩
      · exact (slitBoxSplitCoverGraph_interior_arc_adj n vi u hu hadj.symm).symm
      · rfl
      · rfl
  · by_cases hv : v ∈ slitBoxWiredArc n
    · let ui : SlitBoxInteriorVertex n := ⟨u, hu⟩
      refine ⟨Sum.inl ui, Sum.inr (⟨v, hv⟩, decide (0 < u.val.1)), ?_, ?_, ?_⟩
      · exact slitBoxSplitCoverGraph_interior_arc_adj n ui v hv hadj
      · rfl
      · rfl
    · let ui : SlitBoxInteriorVertex n := ⟨u, hu⟩
      let vi : SlitBoxInteriorVertex n := ⟨v, hv⟩
      refine ⟨Sum.inl ui, Sum.inl vi, ?_, rfl, rfl⟩
      exact (slitBoxSplitCoverGraph_interior_adj_iff n ui vi).2 hadj

end PottsContinuity.FKC.FiniteFK
