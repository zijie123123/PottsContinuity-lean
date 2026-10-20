module

public import PottsContinuity.PlanarTopology.HalfPlaneExitBoundary
public import PottsContinuity.PlanarTopology.HalfPlaneLocalUniqueness
public import PottsContinuity.PlanarTopology.HalfPlaneArchScreen
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.RCInfinite BD12
noncomputable section

/-- Opposite first exits joined by actual half-plane local uniqueness yield
an original open arch with both genuine exterior crossing end bonds retained. -/
theorem opposite_halfplane_first_exits_give_arch
    (η : LatticeConfiguration) (S T U : Set LatticeVertex) (hSU : S ⊆ U) (hTU : T ⊆ U)
    (hS : η ∈ halfPlaneExitEvent S {y : ℤ | y ≤ -1})
    (hT : η ∈ halfPlaneExitEvent T {y : ℤ | 1 ≤ y})
    (hlocal : η ∈ halfPlaneLocalUniquenessEvent U) :
    ∃ l : ℤ, l ≤ -1 ∧ ∃ u : ℤ, 1 ≤ u ∧
      ∃ q : PD.squareLattice.Walk (-1,l) (-1,u), kstPathOpen η q ∧
        ∀ z ∈ q.support, 0 ≤ z.1 ∨ z = (-1,l) ∨ z = (-1,u) := by
  obtain ⟨l,hl,a,ha,haH,p,hp⟩ := halfPlaneExitEvent_original_walk _ _ η hS
  obtain ⟨u,hu,b,hb,hbH,q,hq⟩ := halfPlaneExitEvent_original_walk _ _ η hT
  have haB := exterior_terminal_walk_has_boundary_connection η a haH l p hp
  have hbB := exterior_terminal_walk_has_boundary_connection η b hbH u q hq
  obtain ⟨r⟩ := hlocal ⟨a,haH⟩ ⟨b,hbH⟩ (hSU ha) (hTU hb) haB hbB
  let f := (SimpleGraph.Embedding.induce (G := PD.rcInfiniteOpenGraph η) {z : LatticeVertex | 0 ≤ z.1}).toHom
  let t := r.map f
  have ht : ∀ z ∈ t.support, 0 ≤ z.1 := by
    intro z hz
    have hs : t.support = r.support.map Subtype.val := SimpleGraph.Walk.support_map f r
    have hz' : z ∈ r.support.map Subtype.val := Eq.mp (congrArg (fun xs : List LatticeVertex => z ∈ xs) hs) hz
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz'
    exact v.property
  let P := p.reverse.append (t.append q)
  have hP : ∀ z ∈ P.support, 0 ≤ z.1 ∨ z = (-1,l) ∨ z = (-1,u) := by
    intro z hz
    change z ∈ (p.reverse.append (t.append q)).support at hz
    rcases (SimpleGraph.Walk.mem_support_append_iff p.reverse (t.append q)).mp hz with hz | hz
    · have hz' : z ∈ p.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz
      rcases hp z hz' with hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
    · rcases (SimpleGraph.Walk.mem_support_append_iff t q).mp hz with hz | hz
      · exact Or.inl (ht z hz)
      · rcases hq z hz with hh | hh
        · exact Or.inl hh
        · exact Or.inr (Or.inr hh)
  refine ⟨l,hl,u,hu,P.mapLe (rcOpenGraph_le_squareLattice η),kstPathOpen_of_rcOpen_walk η P,?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hz
  exact hP z hz

/-- Opposite complementary-dual first exits and dual local uniqueness screen
both original primal boundary vertices inside the actual right half-plane. -/
theorem opposite_dual_first_exits_screen_unit_segment
    (ω : LatticeConfiguration) (S T U : Set LatticeVertex) (hSU : S ⊆ U) (hTU : T ⊆ U)
    (hS : wholePlaneDualConfigurationHomeomorph ω ∈ halfPlaneExitEvent S {y : ℤ | y ≤ -1})
    (hT : wholePlaneDualConfigurationHomeomorph ω ∈ halfPlaneExitEvent T {y : ℤ | 1 ≤ y})
    (hlocal : wholePlaneDualConfigurationHomeomorph ω ∈ halfPlaneLocalUniquenessEvent U) :
    ∀ y : ℤ, (y = 0 ∨ y = 1) →
      {z : {z : LatticeVertex // 0 ≤ z.1} |
        ((PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1}).Reachable
          ⟨(0,y),by norm_num⟩ z}.Finite := by
  obtain ⟨l,hl,u,hu,q,hq,hgeom⟩ := opposite_halfplane_first_exits_give_arch
    (wholePlaneDualConfigurationHomeomorph ω) S T U hSU hTU hS hT hlocal
  exact boundary_attached_dual_arch_screens_unit_segment ω l u hl hu q hq hgeom

end
end PottsContinuity.PlanarTopology
