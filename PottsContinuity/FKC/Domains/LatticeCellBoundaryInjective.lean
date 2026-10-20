-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticeCellBoundaryInjective.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticeCellBoundary
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC

open Medial

theorem latticeCellBoundaryBonds_injective :
    Function.Injective latticeCellBoundaryBonds := by
  classical
  intro S T hboundaryEq
  by_contra hST
  let U : Finset LatticeVertex := S \ T ∪ T \ S
  have hUne : U.Nonempty := by
    by_contra h
    have hUempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    apply hST
    ext c
    have hcnot : c ∉ U := by rw [hUempty]; simp
    have hdisj : c ∉ S \ T ∧ c ∉ T \ S := by
      simpa [U, Finset.mem_union, Finset.mem_sdiff] using hcnot
    by_cases hs : c ∈ S <;> by_cases ht : c ∈ T
    · simp [hs, ht]
    · exact False.elim (hdisj.1 (Finset.mem_sdiff.mpr ⟨hs, ht⟩))
    · exact False.elim (hdisj.2 (Finset.mem_sdiff.mpr ⟨ht, hs⟩))
    · simp [hs, ht]
  obtain ⟨c, hc, hmax⟩ := U.exists_max_image (fun x => x.1) hUne
  let east : LatticeVertex := (c.1 + 1, c.2)
  have heastNot : east ∉ U := by
    intro heast
    have hcoord := hmax east heast
    simp only [east] at hcoord
    omega
  have heastAgree : (east ∈ S) ↔ (east ∈ T) := by
    by_cases hs : east ∈ S
    · by_cases ht : east ∈ T
      · exact iff_of_true hs ht
      · exfalso
        apply heastNot
        simp [U, hs, ht]
    · by_cases ht : east ∈ T
      · exfalso
        apply heastNot
        simp [U, hs, ht]
      · exact iff_of_false hs ht
  have hcellDiff : (c ∈ S) ≠ (c ∈ T) := by
    rcases Finset.mem_union.mp hc with h | h
    · have hs : c ∈ S := (Finset.mem_sdiff.mp h).1
      have ht : c ∉ T := (Finset.mem_sdiff.mp h).2
      intro heq
      exact ht (heq ▸ hs)
    · have ht : c ∈ T := (Finset.mem_sdiff.mp h).1
      have hs : c ∉ S := (Finset.mem_sdiff.mp h).2
      intro heq
      exact hs (heq.symm ▸ ht)
  let e : LatticeBond := ⟨east, LatticeAxis.vertical⟩
  have hbondMember :
      ((e.faceBase true ∈ S) ≠ (e.faceBase false ∈ S)) ↔
        ((e.faceBase true ∈ T) ≠ (e.faceBase false ∈ T)) := by
    have heqMem : e ∈ latticeCellBoundaryBonds S ↔
        e ∈ latticeCellBoundaryBonds T := by
      have heq : (e ∈ latticeCellBoundaryBonds S) =
          (e ∈ latticeCellBoundaryBonds T) := congrArg (fun B => e ∈ B) hboundaryEq
      exact Iff.of_eq heq
    exact (mem_latticeCellBoundaryBonds S e).symm.trans
      (heqMem.trans (mem_latticeCellBoundaryBonds T e))
  have hcellAgree : (c ∈ S) ↔ (c ∈ T) := by
    simp only [e, LatticeBond.faceBase, east] at hbondMember
    by_cases hs : east ∈ S
    · have ht : east ∈ T := heastAgree.mp hs
      have hn : ¬(c ∈ S) ↔ ¬(c ∈ T) := by simpa [east, hs, ht] using hbondMember
      exact not_iff_not.mp hn
    · have ht : east ∉ T := fun h => hs (heastAgree.mpr h)
      simpa [east, hs, ht] using hbondMember
  exact hcellDiff (propext hcellAgree)

end PottsContinuity.FKC
