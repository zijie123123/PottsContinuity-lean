-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverWalkFillingPropagation.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceMembershipPropagation
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

/-- Along an actual cover walk whose vertices all index retained faces, the
same finite filling has constant membership whenever the walk avoids the
cycle support. -/
theorem parafermionicCoverSimpleCycleFillingSet_mem_iff_along_walk
    {n : ℕ} (hn : 1 ≤ n) {a : ParafermionicCoverBoxVertex n}
    (C : (parafermionicCoverBoxGraph n).Walk a a) (hC : C.IsCycle)
    {u v : ParafermionicCoverVertex}
    (w : parafermionicCoverGraph.Walk u v)
    (hbase : ∀ z ∈ w.support,
      ∃ i : ParafermionicCoverFiniteFaceTopIndex n, i.1 = z)
    (havoid : ∀ z ∈ w.support, ∀ x ∈ C.support, z ≠ x.1) :
    (∃ i : ParafermionicCoverFiniteFaceTopIndex n, i.1 = u ∧
        i ∈ parafermionicCoverSimpleCycleFillingSet hn C hC) ↔
      (∃ j : ParafermionicCoverFiniteFaceTopIndex n, j.1 = v ∧
        j ∈ parafermionicCoverSimpleCycleFillingSet hn C hC) := by
  induction w with
  | nil =>
      simp
  | @cons x y z hxy w ih =>
      have hxmem : x ∈ (SimpleGraph.Walk.cons hxy w).support := by simp
      have hymem : y ∈ (SimpleGraph.Walk.cons hxy w).support := by
        simp [SimpleGraph.Walk.support_cons, w.start_mem_support]
      obtain ⟨ix, hix⟩ := hbase x hxmem
      obtain ⟨iy, hiy⟩ := hbase y hymem
      have habs_ix : ∀ t ∈ C.support, t.1 ≠ ix.1 := by
        intro t ht
        exact (havoid ix.1 (hix ▸ hxmem) t ht).symm
      have habs_iy : ∀ t ∈ C.support, t.1 ≠ iy.1 := by
        intro t ht
        exact (havoid iy.1 (hiy ▸ hymem) t ht).symm
      have hxy' : parafermionicCoverGraph.Adj ix.1 iy.1 := by
        simpa [hix, hiy] using hxy
      have hstep :=
        parafermionicCoverSimpleCycleFillingSet_mem_iff_of_adjacent_base_absent
          hn C hC ix iy hxy' habs_ix habs_iy
      have htailbase : ∀ t ∈ w.support,
          ∃ i : ParafermionicCoverFiniteFaceTopIndex n, i.1 = t := by
        intro t ht
        exact hbase t (by simp [SimpleGraph.Walk.support_cons, ht])
      have htailavoid : ∀ t ∈ w.support, ∀ q ∈ C.support, t ≠ q.1 := by
        intro t ht q hq
        exact havoid t (by simp [SimpleGraph.Walk.support_cons, ht]) q hq
      have htail := ih htailbase htailavoid
      have hstart :
          (∃ i : ParafermionicCoverFiniteFaceTopIndex n, i.1 = x ∧
            i ∈ parafermionicCoverSimpleCycleFillingSet hn C hC) ↔
          (∃ i : ParafermionicCoverFiniteFaceTopIndex n, i.1 = y ∧
            i ∈ parafermionicCoverSimpleCycleFillingSet hn C hC) := by
        constructor
        · rintro ⟨i, hiX, hi⟩
          have hieq : i = ix := Subtype.ext (hiX.trans hix.symm)
          subst i
          exact ⟨iy, hiy, hstep.mp hi⟩
        · rintro ⟨i, hi, hiS⟩
          have hieq : i = iy := Subtype.ext (hi.trans hiy.symm)
          subst i
          have hiyS : iy ∈ parafermionicCoverSimpleCycleFillingSet hn C hC :=
            hiS
          exact ⟨ix, hix, hstep.mpr hiyS⟩
      exact hstart.trans htail

end PottsContinuity.FKC.Medial
