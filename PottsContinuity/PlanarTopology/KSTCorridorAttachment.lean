module

public import PottsContinuity.PlanarTopology.KSTCascadeConnections
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Reversing both walks preserves a genuinely contiguous subwalk. -/
theorem isSubwalk_reverse_walk {V : Type*} {G : SimpleGraph V} {a b c d : V}
    {p : G.Walk a b} {q : G.Walk c d} (h : p.IsSubwalk q) :
    p.reverse.IsSubwalk q.reverse := by
  obtain ⟨r,s,he⟩ := h
  refine ⟨s.reverse,r.reverse,?_⟩
  rw [he,SimpleGraph.Walk.reverse_append,SimpleGraph.Walk.reverse_append,
    SimpleGraph.Walk.append_assoc]

/-- The unoriented contiguous-path alternative is unchanged when the crossing
walk is traversed backwards. -/
theorem kst_contained_mpath_reverse (m : ℕ) {u v : LatticeVertex}
    (p : PD.squareLattice.Walk u v)
    (h : ∃ x y, ∃ q : PD.squareLattice.Walk x y,
      kstMPath m q ∧ (q.IsSubwalk p ∨ q.reverse.IsSubwalk p)) :
    ∃ x y, ∃ q : PD.squareLattice.Walk x y,
      kstMPath m q ∧ (q.IsSubwalk p.reverse ∨ q.reverse.IsSubwalk p.reverse) := by
  obtain ⟨x,y,q,hq,hsub⟩ := h
  refine ⟨x,y,q,hq,?_⟩
  rcases hsub with hsub | hsub
  · exact Or.inr (isSubwalk_reverse_walk hsub)
  · exact Or.inl (by simpa only [SimpleGraph.Walk.reverse_reverse] using isSubwalk_reverse_walk hsub)

/-- Actual corridor alternatives suffice to attach an open m-path to the side
where the crossing starts. This is only the open-walk gluing step; the corridor
alternatives themselves are proved separately by the planar corridor lemmas. -/
theorem kst_attached_of_corridor_cases (n m : ℕ) (left : Bool) (ω : LatticeConfiguration)
    {a b c d s t u v : LatticeVertex}
    (g : PD.squareLattice.Walk a b) (g' : PD.squareLattice.Walk c d)
    (L : PD.squareLattice.Walk s a) (R : PD.squareLattice.Walk t c)
    (p : PD.squareLattice.Walk u v)
    (hg : kstMPath m g) (hg' : kstMPath m g')
    (hgO : kstPathOpen ω g) (hgO' : kstPathOpen ω g')
    (hLO : kstPathOpen ω L) (hRO : kstPathOpen ω R) (hpO : kstPathOpen ω p)
    (hside : if left then u.1 = -((5*n/4 : ℕ) : ℤ) else u.1 = ((5*n/4 : ℕ) : ℤ))
    (hspace : ∀ z, z ∈ g.support ∨ z ∈ g'.support ∨ z ∈ L.support ∨
      z ∈ R.support ∨ z ∈ p.support → 4*|z.1| ≤ 5*(n : ℤ) ∧ |z.2| ≤ (n : ℤ))
    (hcases : (∃ x y, ∃ q : PD.squareLattice.Walk x y,
      kstMPath m q ∧ (q.IsSubwalk p ∨ q.reverse.IsSubwalk p)) ∨
      (∃ z ∈ p.support, z ∈ g.support ∨ z ∈ g'.support ∨ z ∈ L.support ∨ z ∈ R.support)) :
    kstAttached n m left ω := by
  have hpB : ∀ z ∈ p.support, 4*|z.1| ≤ 5*(n : ℤ) ∧ |z.2| ≤ (n : ℤ) :=
    fun z hz => hspace z (Or.inr (Or.inr (Or.inr (Or.inr hz))))
  have huB := hpB u p.start_mem_support
  rcases hcases with hpath | ⟨z,hzp,hzw⟩
  · obtain ⟨x,y,q,hq,hsub⟩ := hpath
    apply kstAttached_of_contained_path n m left ω p .nil hpO
      (by intro e he; simp at he) hside huB.2 _ hpB q hq hsub
    intro z hz
    have he : z = u := by simpa using hz
    exact he ▸ huB
  · have pathIn {x y : LatticeVertex} (q : PD.squareLattice.Walk x y)
        (hqb : ∀ z ∈ q.support, 4*|z.1| ≤ 5*(n : ℤ) ∧ |z.2| ≤ (n : ℤ)) :
        kstPathIn q (-((5*n/4 : ℕ) : ℤ)) ((5*n/4 : ℕ) : ℤ) (-(n : ℤ)) n := by
      intro z hz
      have hb := hqb z hz
      have hx : |z.1| ≤ ((5*n/4 : ℕ) : ℤ) := by omega
      exact ⟨(abs_le.mp hx).1,(abs_le.mp hx).2,(abs_le.mp hb.2).1,(abs_le.mp hb.2).2⟩
    have wall_case {x y w : LatticeVertex} (G : PD.squareLattice.Walk x y)
        (C : PD.squareLattice.Walk w x) (hG : kstMPath m G)
        (hGO : kstPathOpen ω G) (hCO : kstPathOpen ω C)
        (hGB : ∀ z ∈ G.support, 4*|z.1| ≤ 5*(n : ℤ) ∧ |z.2| ≤ (n : ℤ))
        (hCB : ∀ z ∈ C.support, 4*|z.1| ≤ 5*(n : ℤ) ∧ |z.2| ≤ (n : ℤ))
        (hz : z ∈ G.support ∨ z ∈ C.support) : kstAttached n m left ω := by
      obtain ⟨W,hWO,hWB⟩ := kst_wall_contact_connection ω _ _ _ _ G C p
        hGO hCO hpO (pathIn G hGB) (pathIn C hCB) (pathIn p hpB) hzp hz
      let A := W.reverse.append C
      have hAO : kstPathOpen ω A := kstPathOpen_append W.reverse C
        ((kstPathOpen_reverse_iff ω W).mpr hWO) hCO
      refine ⟨x,y,u,G,A,hG,hGO,hAO,hside,huB.2,?_,hGB⟩
      intro w hw
      simp only [A,SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse,List.mem_reverse] at hw
      rcases hw with hw | hw
      · have hb := hWB w hw
        have hx : |w.1| ≤ ((5*n/4 : ℕ) : ℤ) := abs_le.mpr ⟨hb.1,hb.2.1⟩
        exact ⟨by omega,abs_le.mpr hb.2.2⟩
      · exact hCB w hw
    have hgB := fun z hz => hspace z (Or.inl hz)
    have hgB' := fun z hz => hspace z (Or.inr (Or.inl hz))
    have hLB := fun z hz => hspace z (Or.inr (Or.inr (Or.inl hz)))
    have hRB := fun z hz => hspace z (Or.inr (Or.inr (Or.inr (Or.inl hz))))
    rcases hzw with hz | hz | hz | hz
    · exact wall_case g L hg hgO hLO hgB hLB (Or.inl hz)
    · exact wall_case g' R hg' hgO' hRO hgB' hRB (Or.inl hz)
    · exact wall_case g L hg hgO hLO hgB hLB (Or.inr hz)
    · exact wall_case g' R hg' hgO' hRO hgB' hRB (Or.inr hz)

end
end PottsContinuity.PlanarTopology
