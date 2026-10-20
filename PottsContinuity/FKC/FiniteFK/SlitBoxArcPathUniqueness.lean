-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxArcPathUniqueness.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCanonicalReturnArcSplit
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- Two simple square-lattice paths on one vertical line and with the same
endpoints are equal as walks. -/
theorem squareLattice_vertical_simple_path_unique
    {x : ℤ} {u v : LatticeVertex} (p q : squareLattice.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath)
    (hpx : ∀ z ∈ p.support, z.1 = x)
    (hqx : ∀ z ∈ q.support, z.1 = x) : p = q := by
  by_contra hne
  obtain ⟨u, v, p', q', hpSub, hqSub, hc⟩ := hp.exists_isCycle_of_ne hq hne
  have hcx : ∀ z ∈ (p'.append q'.reverse).support, z.1 = x := by
    intro z hz
    rw [SimpleGraph.Walk.support_append] at hz
    have hz' : z ∈ p'.support ∨ z ∈ q'.reverse.support.tail :=
      List.mem_append.mp hz
    rcases hz' with hz' | hz'
    · exact hpx z (hpSub.support_subset hz')
    · have hzrev : z ∈ q'.reverse.support := List.mem_of_mem_tail hz'
      have hzq : z ∈ q'.support := by
        rw [SimpleGraph.Walk.support_reverse] at hzrev
        exact List.mem_reverse.mp hzrev
      exact hqx z (hqSub.support_subset hzq)
  let c := p'.append q'.reverse
  have hc' : c.IsCycle := by simpa [c] using hc
  have hcnonempty : c.support.toFinset.Nonempty := by
    refine ⟨u, ?_⟩
    simp [c]
  obtain ⟨vmax, hvmax, hmax⟩ := c.support.toFinset.exists_max_image Prod.snd hcnonempty
  have hvSupport : vmax ∈ c.support := by simpa using hvmax
  have hneighborMax : ∀ w ∈ c.toSubgraph.neighborSet vmax, w.2 ≤ vmax.2 := by
    intro w hw
    have hwmem : w ∈ c.support :=
      c.mem_support_of_adj_toSubgraph (c.toSubgraph.adj_symm hw)
    have hmaxw := hmax w (by simpa using hwmem)
    exact hmaxw
  have hvmaxX : vmax.1 = x := hcx vmax hvSupport
  have hneighborX : ∀ w ∈ c.toSubgraph.neighborSet vmax, w.1 = x := by
    intro w hw
    exact hcx w (c.mem_support_of_adj_toSubgraph (c.toSubgraph.adj_symm hw))
  have hneighbors : c.toSubgraph.neighborSet vmax ⊆ {(x, vmax.2 - 1)} := by
    intro w hw
    have hx := hneighborX w hw
    have hy := hneighborMax w hw
    have hadj : squareLattice.Adj vmax w := c.toSubgraph.adj_sub hw
    have hcoords := (squareLattice_adj_iff vmax w).mp hadj
    rcases hcoords with ⟨⟨h | h, _⟩⟩ | ⟨hxx, hvert⟩
    · have hwx := h
      omega
    · have hwx := h
      omega
    · have hwx := hxx
      rcases hvert with h | h
      · omega
      · have hs : w.2 + 1 = vmax.2 := h
        refine Set.mem_singleton_iff.mpr ?_
        exact Prod.ext hx (by omega)
  have hcard := hc'.ncard_neighborSet_toSubgraph_eq_two hvSupport
  have hsmall : (c.toSubgraph.neighborSet vmax).ncard ≤ 1 := by
    calc
      (c.toSubgraph.neighborSet vmax).ncard ≤ ({(x, vmax.2 - 1)} : Set (ℤ × ℤ)).ncard :=
        Set.ncard_le_ncard hneighbors
      _ = 1 := by simp
  omega

/-- Any simple path supported on the actual wired arc is the literal vertical
walk from its initial vertex to the top of that arc. -/
theorem slitBoxWiredArc_simple_path_eq_literal
    (n : ℕ) (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n)
    (q : squareLattice.Walk t.val (slitBoxTopArcVertex n).val)
    (hq : q.IsPath)
    (hqs : ∀ x ∈ q.support,
      ∃ v : SlitBoxVertex n, v ∈ slitBoxWiredArc n ∧ v.val = x) :
    q = slitBoxArcVerticalWalk n t ht := by
  have htArc := (mem_slitBoxWiredArc_iff n t).mp ht
  have hqline : ∀ z ∈ q.support, z.1 = 0 := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hqs z hz
    exact (mem_slitBoxWiredArc_iff n v).mp hv |>.1
  have hpline : ∀ z ∈ (slitBoxArcVerticalWalk n t ht).support, z.1 = 0 := by
    intro z hz
    obtain ⟨v, hv, heq⟩ := slitBoxArcVerticalWalk_support_in_wiredArc n t ht z hz
    exact (mem_slitBoxWiredArc_iff n v).mp hv |>.1 ▸ heq ▸ rfl
  exact squareLattice_vertical_simple_path_unique
    q (slitBoxArcVerticalWalk n t ht)
    hq (slitBoxArcVerticalWalk_isPath n t ht) hqline hpline

end PottsContinuity.FKC.FiniteFK
