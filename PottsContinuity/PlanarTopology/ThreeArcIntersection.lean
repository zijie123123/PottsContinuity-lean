module

public import PottsContinuity.PlanarTopology.BoundaryExtension
public import PottsContinuity.PlanarTopology.RectangleIntersection
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK

/-- A path between central top/bottom targets meets every path between the
complementary left/right three-piece boundary arcs of the same rectangle. -/
theorem rectangle_three_arc_paths_intersect
    (left right bottom top cL cR : ℤ) {a b u v : LatticeVertex}
    (p : squareLattice.Walk a b) (q : squareLattice.Walk u v)
    (hp : ∀ z ∈ p.support,
      left ≤ z.1 ∧ z.1 ≤ right ∧ bottom ≤ z.2 ∧ z.2 ≤ top)
    (hq : ∀ z ∈ q.support,
      left ≤ z.1 ∧ z.1 ≤ right ∧ bottom ≤ z.2 ∧ z.2 ≤ top)
    (ha : a.2 = top) (hb : b.2 = bottom)
    (hax : cL ≤ a.1 ∧ a.1 ≤ cR) (hbx : cL ≤ b.1 ∧ b.1 ≤ cR)
    (hu : u.1 ≤ cL ∧ (u.1 = left ∨ u.2 = bottom ∨ u.2 = top))
    (hv : cR ≤ v.1 ∧ (v.1 = right ∨ v.2 = bottom ∨ v.2 = top)) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  by_contra hno
  have hdis : ∀ z ∈ q.support, z ∉ p.support := by
    intro z hz hzp
    exact hno ⟨z, hzp, hz⟩
  have haB := hp a p.start_mem_support
  have hbB := hp b p.end_mem_support
  have huB := hq u q.start_mem_support
  have hvB := hq v q.end_mem_support
  have hlr : left ≤ right := haB.1.trans haB.2.1
  have hbt : bottom ≤ top := haB.2.2.1.trans haB.2.2.2
  obtain ⟨s,L,hs,hL,hLo⟩ := left_boundary_extension left right bottom top u huB hu.2
  obtain ⟨t,R,ht,hR,hRo⟩ := right_boundary_extension left right bottom top v hvB hv.2
  have htop : squareLattice.Adj (a.1,top+1) a := by
    rw [squareLattice_adj_iff]
    dsimp
    omega
  have hbottom : squareLattice.Adj b (b.1,bottom-1) := by
    rw [squareLattice_adj_iff]
    dsimp
    omega
  let P := (htop.toWalk.append p).append hbottom.toWalk
  let Q := (L.append q).append R.reverse
  have hPs (z : LatticeVertex) (hz : z ∈ P.support) :
      z ∈ p.support ∨ z = (a.1,top+1) ∨ z = (b.1,bottom-1) := by
    change z ∈ ((htop.toWalk.append p).append hbottom.toWalk).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hz | hz) | hz
    · have hz' : z = (a.1,top+1) ∨ z = a := by simpa using hz
      rcases hz' with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl p.start_mem_support
    · exact Or.inl hz
    · have hz' : z = b ∨ z = (b.1,bottom-1) := by simpa using hz
      rcases hz' with rfl | rfl
      · exact Or.inl p.end_mem_support
      · exact Or.inr (Or.inr rfl)
  have hLAvoid : ∀ z ∈ L.support, z ∉ P.support := by
    intro z hz hzp
    have hout := hLo z hz
    rcases hPs z hzp with hzp | rfl | rfl
    · have hzB := hp z hzp
      rcases hout with rfl | hout | ⟨_, hout⟩
      · exact hdis _ q.start_mem_support hzp
      · omega
      · rcases hout with ⟨_, hout⟩ | ⟨_, hout⟩ <;> omega
    · rcases hout with he | hout | ⟨hx,hout⟩
      · have h := congrArg Prod.snd he
        dsimp at h
        omega
      · dsimp at hout
        omega
      · have hua : u = a := by
          apply Prod.ext <;> dsimp at hx hout ⊢ <;> omega
        exact hdis _ q.start_mem_support (hua.symm ▸ p.start_mem_support)
    · rcases hout with he | hout | ⟨hx,hout⟩
      · have h := congrArg Prod.snd he
        dsimp at h
        omega
      · dsimp at hout
        omega
      · have hub : u = b := by
          apply Prod.ext <;> dsimp at hx hout ⊢ <;> omega
        exact hdis _ q.start_mem_support (hub.symm ▸ p.end_mem_support)
  have hRAvoid : ∀ z ∈ R.support, z ∉ P.support := by
    intro z hz hzp
    have hout := hRo z hz
    rcases hPs z hzp with hzp | rfl | rfl
    · have hzB := hp z hzp
      rcases hout with rfl | hout | ⟨_, hout⟩
      · exact hdis _ q.end_mem_support hzp
      · omega
      · rcases hout with ⟨_, hout⟩ | ⟨_, hout⟩ <;> omega
    · rcases hout with he | hout | ⟨hx,hout⟩
      · have h := congrArg Prod.snd he
        dsimp at h
        omega
      · dsimp at hout
        omega
      · have hva : v = a := by
          apply Prod.ext <;> dsimp at hx hout ⊢ <;> omega
        exact hdis _ q.end_mem_support (hva.symm ▸ p.start_mem_support)
    · rcases hout with he | hout | ⟨hx,hout⟩
      · have h := congrArg Prod.snd he
        dsimp at h
        omega
      · dsimp at hout
        omega
      · have hvb : v = b := by
          apply Prod.ext <;> dsimp at hx hout ⊢ <;> omega
        exact hdis _ q.end_mem_support (hvb.symm ▸ p.end_mem_support)
  have hPbox : ∀ z ∈ P.support,
      left-1 ≤ z.1 ∧ z.1 ≤ right+1 ∧ bottom-1 ≤ z.2 ∧ z.2 ≤ top+1 := by
    intro z hz
    rcases hPs z hz with hz | rfl | rfl
    · have h := hp z hz
      omega
    · dsimp
      omega
    · dsimp
      omega
  have hQbox : ∀ z ∈ Q.support,
      left-1 ≤ z.1 ∧ z.1 ≤ right+1 ∧ bottom-1 ≤ z.2 ∧ z.2 ≤ top+1 := by
    intro z hz
    change z ∈ ((L.append q).append R.reverse).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hz | hz) | hz
    · exact hL z hz
    · have h := hq z hz
      omega
    · apply hR z
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
  obtain ⟨z,hzQ,hzP⟩ := rectangle_walks_common_vertex Q P.reverse
    (by omega : left-1 ≤ right+1) (by omega : bottom-1 ≤ top+1) hQbox
    (by simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hPbox)
    hs ht rfl rfl
  have hzP' : z ∈ P.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzP
  change z ∈ ((L.append q).append R.reverse).support at hzQ
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hzQ
  rcases hzQ with (hz | hz) | hz
  · exact hLAvoid z hz hzP'
  · rcases hPs z hzP' with hzp | he | he
    · exact hdis z hz hzp
    · have h := hq z hz
      have hy := congrArg Prod.snd he
      dsimp at hy
      omega
    · have h := hq z hz
      have hy := congrArg Prod.snd he
      dsimp at hy
      omega
  · exact hRAvoid z (by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz) hzP'

end PottsContinuity.PlanarTopology
