module

public import PottsContinuity.PlanarTopology.RectangleIntersection
public import PottsContinuity.PlanarTopology.ExteriorBottomExtension
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PlanarTopology
noncomputable section

/-- A bottom-to-right walk disjoint from the later bottom-to-tip walk must
visit the free left slit boundary. Only the original walk supports are used. -/
theorem disjoint_bottom_right_walk_hits_left_slit
    (a b B t x y H : ℤ) (ha : 0 ≤ a) (hab : a < b) (hbB : b ≤ B)
    (hx : 1 ≤ x) (hxa : x ≤ a) (hy : 0 < y) (hyH : y ≤ H)
    (p : squareLattice.Walk (a,0) (B,t))
    (q : squareLattice.Walk (b,0) (x,y))
    (hp : ∀ z ∈ p.support, 0 ≤ z.1 ∧ z.1 ≤ B ∧ 0 ≤ z.2 ∧ z.2 ≤ H)
    (hq : ∀ z ∈ q.support, 0 ≤ z.1 ∧ z.1 ≤ B ∧ 0 ≤ z.2 ∧ z.2 ≤ H)
    (hdis : ∀ z ∈ p.support, z ∉ q.support) :
    ∃ z ∈ p.support, z.1 = x-1 ∧ y ≤ z.2 := by
  obtain ⟨L,hL⟩ := horizontal_walk_between 0 a (-1)
  obtain ⟨R,hR⟩ := vertical_walk_between (x-1) y H
  have hup : squareLattice.Adj (a,-1) (a,0) := by
    rw [squareLattice_adj_iff]; dsimp; omega
  have hdown : squareLattice.Adj (b,-1) (b,0) := by
    rw [squareLattice_adj_iff]; dsimp; omega
  have hleft : squareLattice.Adj (x,y) (x-1,y) := by
    rw [squareLattice_adj_iff]; dsimp; omega
  let P := (L.append hup.toWalk).append p
  let Q := (hdown.toWalk.append q).append (hleft.toWalk.append R)
  have hP : ∀ z ∈ P.support,
      z ∈ p.support ∨ (z.2 = -1 ∧ 0 ≤ z.1 ∧ z.1 ≤ a) := by
    intro z hz
    change z ∈ ((L.append hup.toWalk).append p).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hz | hz) | hz
    · have hh := hL z hz
      exact Or.inr ⟨hh.2.2,by simpa only [min_eq_left ha] using hh.1,
        by simpa only [max_eq_right ha] using hh.2.1⟩
    · have he : z = (a,-1) ∨ z = (a,0) := by simpa using hz
      rcases he with rfl | rfl
      · exact Or.inr ⟨rfl,ha,le_rfl⟩
      · exact Or.inl p.start_mem_support
    · exact Or.inl hz
  have hQ : ∀ z ∈ Q.support,
      z ∈ q.support ∨ (z.1 = x-1 ∧ y ≤ z.2 ∧ z.2 ≤ H) ∨ z = (b,-1) := by
    intro z hz
    change z ∈ ((hdown.toWalk.append q).append (hleft.toWalk.append R)).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hz | hz) | (hz | hz)
    · have he : z = (b,-1) ∨ z = (b,0) := by simpa using hz
      rcases he with rfl | rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl q.start_mem_support
    · exact Or.inl hz
    · have he : z = (x,y) ∨ z = (x-1,y) := by simpa using hz
      rcases he with rfl | rfl
      · exact Or.inl q.end_mem_support
      · exact Or.inr (Or.inl ⟨rfl,le_rfl,hyH⟩)
    · have hh := hR z hz
      exact Or.inr (Or.inl ⟨hh.1,by simpa only [min_eq_left hyH] using hh.2.1,
        by simpa only [max_eq_right hyH] using hh.2.2⟩)
  have hPB : ∀ z ∈ P.support, 0 ≤ z.1 ∧ z.1 ≤ B ∧ -1 ≤ z.2 ∧ z.2 ≤ H := by
    intro z hz
    rcases hP z hz with hz | hz
    · have hh := hp z hz
      exact ⟨hh.1,hh.2.1,by omega,hh.2.2.2⟩
    · exact ⟨hz.2.1,by omega,by omega,by omega⟩
  have hQB : ∀ z ∈ Q.support, 0 ≤ z.1 ∧ z.1 ≤ B ∧ -1 ≤ z.2 ∧ z.2 ≤ H := by
    intro z hz
    rcases hQ z hz with hz | hz | rfl
    · have hh := hq z hz
      exact ⟨hh.1,hh.2.1,by omega,hh.2.2.2⟩
    · exact ⟨by omega,by omega,by omega,hz.2.2⟩
    · exact ⟨by omega,hbB,le_rfl,by omega⟩
  obtain ⟨z,hzp,hzq⟩ := rectangle_walks_common_vertex P Q
    (by omega : (0:ℤ) ≤ B) (by omega : (-1:ℤ) ≤ H)
    hPB hQB rfl rfl rfl rfl
  rcases hP z hzp with hzp | hzp
  · rcases hQ z hzq with hzq | hzq | rfl
    · exact (hdis z hzp hzq).elim
    · exact ⟨z,hzp,hzq.1,hzq.2.1⟩
    · have hh := hp (b,-1) hzp
      omega
  · rcases hQ z hzq with hzq | hzq | rfl
    · have hh := hq z hzq
      omega
    · omega
    · omega

end
end PottsContinuity.RSW
