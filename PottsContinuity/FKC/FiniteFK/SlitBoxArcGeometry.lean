-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxArcGeometry.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxDomain
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- The retained wired arc always contains its actual origin vertex. -/
theorem slitBoxWiredArc_nonempty (n : ℕ) : (slitBoxWiredArc n).Nonempty := by
  refine ⟨⟨(0, 0), ?_⟩, ?_⟩
  · rw [mem_latticeRectangle]
    norm_num
    omega
  · rw [mem_slitBoxWiredArc_iff]
    simp

/-- Every lattice edge with both endpoints on the wired arc is removed. -/
theorem slitBoxGraph_no_adj_on_wiredArc (n : ℕ) {u v : SlitBoxVertex n}
    (hu : u ∈ slitBoxWiredArc n) (hv : v ∈ slitBoxWiredArc n) :
    ¬ (slitBoxGraph n).Adj u v := by
  intro hadj
  exact (slitBoxGraph_adj_iff n u v).mp hadj |>.2 ⟨
    (mem_slitBoxWiredArc_iff n u).mp hu,
    (mem_slitBoxWiredArc_iff n v).mp hv⟩

/-- An outside vertex has at most one nearest-neighbor on the retained wired arc. -/
theorem slitBoxGraph_adj_wiredArc_unique (n : ℕ) {u v w : SlitBoxVertex n}
    (hu : u ∉ slitBoxWiredArc n) (hv : v ∈ slitBoxWiredArc n)
    (hw : w ∈ slitBoxWiredArc n)
    (huv : (slitBoxGraph n).Adj u v) (huw : (slitBoxGraph n).Adj u w) : v = w := by
  have hv' := (mem_slitBoxWiredArc_iff n v).mp hv
  have hw' := (mem_slitBoxWiredArc_iff n w).mp hw
  have hu' : ¬ (u.val.1 = 0 ∧ 0 ≤ u.val.2 ∧ u.val.2 ≤ n) := by
    intro h
    exact hu ((mem_slitBoxWiredArc_iff n u).mpr h)
  have huv' := (slitBoxGraph_adj_iff n u v).mp huv |>.1
  have huw' := (slitBoxGraph_adj_iff n u w).mp huw |>.1
  apply Subtype.ext
  have hA := (squareLattice_adj_iff u.val v.val).mp huv'
  have hB := (squareLattice_adj_iff u.val w.val).mp huw'
  rcases hA with hhorA | hverA
  · rcases hhorA with ⟨hstepA, hya⟩
    rcases hB with hhorB | hverB
    · rcases hhorB with ⟨hstepB, hyb⟩
      apply Prod.ext <;> omega
    · rcases hverB with ⟨hxb, _⟩
      exfalso
      rcases hstepA with ha | ha <;> rcases hxb with hb <;> omega
  · rcases hverA with ⟨hxa, _⟩
    rcases hB with hhorB | hverB
    · rcases hhorB with ⟨hstepB, _⟩
      exfalso
      rcases hxa with ha; rcases hstepB with hb | hb <;> omega
    · rcases hverB with ⟨hxb, hstepB⟩
      apply Prod.ext <;> omega

end PottsContinuity.FKC.FiniteFK
