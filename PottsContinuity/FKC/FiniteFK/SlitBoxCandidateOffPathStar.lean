-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateOffPathStar.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCellIncidentStar
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- A box vertex off the retained first-hit path and off the wired arc is not
on the support of the actual candidate cycle. -/
theorem slitBoxFirstHitCandidateCycle_off_path_arc_not_mem_support
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p : SlitBoxFirstHitBaseCandidates n u) (v : SlitBoxVertex n)
    (hvPath : v ∉ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support)
    (hvArc : v ∉ slitBoxWiredArc n) :
    v.val ∉ (slitBoxFirstHitCandidateCycle n hn u huY huX p).support := by
  classical
  let : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
  let A : Configuration (slitBoxGraph n) := Finset.univ
  have hA : A = Finset.univ := rfl
  let f : slitBoxGraph n →g openGraph (slitBoxGraph n) A := {
    toFun := id
    map_rel' := by
      intro x y hxy
      apply (openGraph_adj (slitBoxGraph n) A x y).2
      change s(x, y) ∈ Subtype.val '' (↑A : Set (slitBoxGraph n).edgeSet)
      rw [hA]
      refine ⟨⟨s(x, y), (slitBoxGraph n).mem_edgeSet.mpr hxy⟩, ?_, rfl⟩
      exact Finset.mem_univ _ }
  let preWalk := ((p.val.2 : (slitBoxGraph n).Walk u p.val.1).map f).map
    (slitBoxOpenGraphToSquareLatticeHom n A)
  let ret := slitBoxCanonicalReturnWalk n u huY huX p.val.1 p.property.1
  have hcycle : slitBoxFirstHitCandidateCycle n hn u huY huX p = preWalk.append ret := by
    rfl
  intro hz
  have hsplit : v.val ∈ preWalk.support ∨ v.val ∈ ret.support := by
    rw [hcycle] at hz
    have hsupp := SimpleGraph.Walk.support_append preWalk ret
    have hzMem : v.val ∈ preWalk.support ++ ret.support.tail := hsupp ▸ hz
    rw [List.mem_append] at hzMem
    rcases hzMem with hpre | htail
    · exact Or.inl hpre
    · exact Or.inr (List.mem_of_mem_tail htail)
  rcases hsplit with hpre | hret
  · rw [SimpleGraph.Walk.support_map] at hpre
    obtain ⟨a, ha, hva⟩ := List.mem_map.mp hpre
    rw [SimpleGraph.Walk.support_map] at ha
    obtain ⟨b, hb, hvb⟩ := List.mem_map.mp ha
    have hab : b = v := by
      apply Subtype.ext
      have hvb' : b = a := by
        change b = a at hvb
        exact hvb
      have hva' : a.val = v.val := by
        simpa [slitBoxOpenGraphToSquareLatticeHom] using hva
      exact (congrArg Subtype.val hvb').trans hva'
    exact hvPath (hab ▸ hb)
  · have hvBox : v.val ∈
        latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) := by
      exact v.property
    have hclass := slitBoxCanonicalReturnWalk_support_in_box
      n u huY huX p.val.1 p.property.1 hret hvBox
    rcases hclass with hu | harc
    · have huv : v = u := Subtype.ext hu
      exact hvPath (huv ▸ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).start_mem_support)
    · apply hvArc
      exact (mem_slitBoxWiredArc_iff n v).mpr harc

/-- At an off-path, off-arc box vertex of an actual candidate cycle, all
incident slit edges have the same reveal status for its genuine filling. -/
theorem slitBoxCellIncidentEdges_all_or_none_at_candidate_off_path_arc
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    (v : SlitBoxVertex n)
    (hvPath : v ∉ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support)
    (hvArc : v ∉ slitBoxWiredArc n)
    (e f : (slitBoxGraph n).edgeSet)
    (he : v ∈ e.val) (hf : v ∈ f.val) :
    (e ∈ slitBoxCellIncidentEdges n
      ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ)) ↔
    (f ∈ slitBoxCellIncidentEdges n
      ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ)) := by
  exact slitBoxCellIncidentEdges_all_or_none_at_candidate_off_support
    n hn u huY huX δ p v
    (slitBoxFirstHitCandidateCycle_off_path_arc_not_mem_support
      n hn u huY huX p v hvPath hvArc) e f he hf

end PottsContinuity.FKC.FiniteFK
