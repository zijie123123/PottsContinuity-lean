module

public import PottsContinuity.PlanarTopology.ExteriorBottomExtension
public import PottsContinuity.PlanarTopology.BottomSpan
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Opposed connections from the left/right non-bottom boundary to opposite
bottom targets intersect on their original supports. The target gap is strict;
walks need not be simple. -/
theorem opposed_boundary_bottom_walks_intersect
    (left right bottom top cL cR : ℤ) (hgap : cL < cR)
    {u v x y : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (q : PD.squareLattice.Walk x y)
    (hp : kstPathIn p left right bottom top) (hq : kstPathIn q left right bottom top)
    (hu : u.1 ≤ cL ∧ (u.1 = left ∨ u.2 = bottom ∨ u.2 = top))
    (hy : cR ≤ y.1 ∧ (y.1 = right ∨ y.2 = bottom ∨ y.2 = top))
    (hv : v.2 = bottom) (hx : x.2 = bottom)
    (hvx : cR ≤ v.1) (hxx : x.1 ≤ cL)
    (huNot : u.2 ≠ bottom) (hyNot : y.2 ≠ bottom) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  have huB := hp u p.start_mem_support
  have hvB := hp v p.end_mem_support
  have hxB := hq x q.start_mem_support
  have hyB := hq y q.end_mem_support
  have hlr : left ≤ right := huB.1.trans huB.2.1
  have hbt : bottom ≤ top := huB.2.2.1.trans huB.2.2.2
  obtain ⟨L,hL⟩ := left_boundary_to_lower_line left right bottom top u huB hu.2 huNot
  obtain ⟨R,hR⟩ := right_boundary_to_lower_line left right bottom top y hyB hy.2 hyNot
  have hd : PD.squareLattice.Adj v (v.1,bottom-1) := by
    rw [squareLattice_adj_iff]
    dsimp
    omega
  have hu' : PD.squareLattice.Adj (x.1,bottom-1) x := by
    rw [squareLattice_adj_iff]
    dsimp
    omega
  let P := (L.append p).append hd.toWalk
  let Q := hu'.toWalk.append (q.append R.reverse)
  have hP (z : LatticeVertex) (hz : z ∈ P.support) :
      z ∈ p.support ∨ z.1 < left ∨ (top < z.2 ∧ z.1 ≤ u.1) ∨
        (z.2 = bottom-1 ∧ z.1 = v.1) := by
    change z ∈ ((L.append p).append hd.toWalk).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hz | hz) | hz
    · rcases (hL z hz).2 with rfl | hz | hz
      · exact Or.inl p.start_mem_support
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inl hz
    · have he : z = v ∨ z = (v.1,bottom-1) := by simpa using hz
      rcases he with rfl | rfl
      · exact Or.inl p.end_mem_support
      · exact Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))
  have hQ (z : LatticeVertex) (hz : z ∈ Q.support) :
      z ∈ q.support ∨ right < z.1 ∨ (top < z.2 ∧ y.1 ≤ z.1) ∨
        (z.2 = bottom-1 ∧ z.1 = x.1) := by
    change z ∈ (hu'.toWalk.append (q.append R.reverse)).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz | hz
    · have he : z = (x.1,bottom-1) ∨ z = x := by simpa using hz
      rcases he with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))
      · exact Or.inl q.start_mem_support
    · exact Or.inl hz
    · have hz' : z ∈ R.support := by
        simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz
      rcases (hR z hz').2 with rfl | hz | hz
      · exact Or.inl q.end_mem_support
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr (Or.inl hz))
  have hPlow : ∀ z ∈ P.support, bottom-1 ≤ z.2 := by
    intro z hz
    change z ∈ ((L.append p).append hd.toWalk).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hz | hz) | hz
    · exact (hL z hz).1
    · have := (hp z hz).2.2.1
      omega
    · have he : z = v ∨ z = (v.1,bottom-1) := by simpa using hz
      rcases he with rfl | rfl <;> omega
  have hQlow : ∀ z ∈ Q.support, bottom-1 ≤ z.2 := by
    intro z hz
    change z ∈ (hu'.toWalk.append (q.append R.reverse)).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz | hz
    · have he : z = (x.1,bottom-1) ∨ z = x := by simpa using hz
      rcases he with rfl | rfl <;> omega
    · have := (hq z hz).2.2.1
      omega
    · apply (hR z _).1
      simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz
  obtain ⟨z,hzp,hzq⟩ := band_interlaced_walks_intersect (bottom-1) P Q
    rfl rfl rfl rfl (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) hPlow hQlow
  rcases hP z hzp with hzp | hzp | hzp | hzp
  · rcases hQ z hzq with hzq | hzq | hzq | hzq
    · exact ⟨z,hzp,hzq⟩
    · have := hp z hzp; omega
    · have := hp z hzp; omega
    · have := hp z hzp; omega
  · rcases hQ z hzq with hzq | hzq | hzq | hzq
    · have := hq z hzq; omega
    · omega
    · omega
    · omega
  · rcases hQ z hzq with hzq | hzq | hzq | hzq
    · have := hq z hzq; omega
    · omega
    · omega
    · omega
  · rcases hQ z hzq with hzq | hzq | hzq | hzq
    · have := hq z hzq; omega
    · omega
    · omega
    · omega

end
end PottsContinuity.PlanarTopology
