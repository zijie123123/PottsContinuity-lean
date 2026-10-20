module

public import PottsContinuity.Thm3.Push.TopCapPath
public import PottsContinuity.PD.Duality.ConnectionSymmetry
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK

/-- The reflected simple cap lies below the square. Its only vertices at
nonnegative height are its endpoints, and it uses no bond with BOTH endpoints
at nonnegative height. Endpoint columns control its complete horizontal range. -/
theorem exists_bottom_cap_path (x y : ℤ) (hxy : x ≠ y) :
    ∃ p : PD.FK.squareLattice.Walk (x,0) (y,0),
      p.IsPath ∧ 1 < p.length ∧
      (∀ z ∈ p.support, min x y ≤ z.1 ∧ z.1 ≤ max x y ∧ -1 ≤ z.2 ∧ z.2 ≤ 0) ∧
      (∀ z ∈ p.support, 0 ≤ z.2 → z=(x,0) ∨ z=(y,0)) ∧
      ∀ a b : LatticeVertex, 0 ≤ a.2 → 0 ≤ b.2 → s(a,b) ∉ p.edges := by
  obtain ⟨q,hq,hqlen,hqs,hqtop,hqedges⟩ := exists_top_cap_path 0 x y hxy
  let j := PD.Duality.latticeFlipYIso
  let p : PD.FK.squareLattice.Walk (x,0) (y,0) := q.map j.toHom
  refine ⟨p,hq.map j.injective,?_,?_,?_,?_⟩
  · have hlen : p.length=q.length := q.length_map j.toHom
    omega
  · intro z hz
    change z ∈ (q.map j.toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    have hh := hqs w hw
    change min x y ≤ w.1 ∧ w.1 ≤ max x y ∧ -1 ≤ -w.2 ∧ -w.2 ≤ 0
    exact ⟨hh.1,hh.2.1,by omega,by omega⟩
  · intro z hz hz0
    change z ∈ (q.map j.toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    change 0 ≤ -w.2 at hz0
    rcases hqtop w hw (by omega) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro a b ha hb he
    change s(a,b) ∈ (q.map j.toHom).edges at he
    rw [SimpleGraph.Walk.edges_map] at he
    obtain ⟨e,he,heq⟩ := List.mem_map.mp he
    have hpair : e=s(j.symm a,j.symm b) := by
      apply Sym2.map.injective j.injective
      simpa [Sym2.map_mk,j,PD.Duality.latticeFlipYIso] using heq
    apply hqedges (j.symm a) (j.symm b)
    · change -a.2 ≤ (0 : ℕ)
      omega
    · change -b.2 ≤ (0 : ℕ)
      omega
    · rw [← hpair]
      exact he

end PottsContinuity.Push
