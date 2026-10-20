module

public import PottsContinuity.Thm1.FiniteESMagnetisation
public import PottsContinuity.Thm1.ShellBoxComparison
public import PottsContinuity.PD.FK.Graph
public import PottsContinuity.PD.FK.Wiring

@[expose] public section

namespace PottsContinuity.Thm1

open PottsContinuity
open PottsContinuity.PD.FK

noncomputable section

def reachesWiredBoundary (V : Finset (ℤ × ℤ))
    (A : Configuration (pottsESGraph V)) (x : PottsESVertex V) : Prop :=
  ∃ b, b ∈ pottsESBoundary V ∧ ActualConnected (pottsESGraph V) A x b

def boundaryReachRelation (V : Finset (ℤ × ℤ))
    (A : Configuration (pottsESGraph V)) : Setoid (PottsESVertex V) where
  r x y := ActualConnected (pottsESGraph V) A x y ∨
    (reachesWiredBoundary V A x ∧ reachesWiredBoundary V A y)
  iseqv := {
    refl := fun x => Or.inl (SimpleGraph.Reachable.refl x)
    symm := by
      intro x y hxy
      rcases hxy with hxy | ⟨hx, hy⟩
      · exact Or.inl hxy.symm
      · exact Or.inr ⟨hy, hx⟩
    trans := by
      intro x y z hxy hyz
      rcases hxy with hxy | ⟨hx, hy⟩
      · rcases hyz with hyz | ⟨hy', hz⟩
        · exact Or.inl (hxy.trans hyz)
        · exact Or.inr ⟨by
            obtain ⟨b, hb, hyb⟩ := hy'
            exact ⟨b, hb, hxy.trans hyb⟩, hz⟩
      · rcases hyz with hyz | ⟨hy', hz⟩
        · exact Or.inr ⟨hx, by
            obtain ⟨b, hb, hyb⟩ := hy
            exact ⟨b, hb, hyz.symm.trans hyb⟩⟩
        · exact Or.inr ⟨hx, hz⟩ }

private theorem componentSetoid_le_boundaryReachRelation
    (V : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V)) :
    componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A ≤
      boundaryReachRelation V A := by
  apply componentSetoid_le
  · intro x y hxy
    exact Or.inl hxy
  · intro x y hxy
    rcases (BoundaryCondition.wired_rel (pottsESBoundary V) x y).mp hxy with hEq | ⟨hx, hy⟩
    · subst y
      exact Or.inl (SimpleGraph.Reachable.refl x)
    · exact Or.inr
        ⟨⟨x, hx, SimpleGraph.Reachable.refl x⟩,
          ⟨y, hy, SimpleGraph.Reachable.refl y⟩⟩

/-- In the shell graph, reaching the ghost boundary class is equivalent to an
actual open path from the origin to one of the exterior boundary vertices. -/
theorem pottsESOriginExteriorConnected_iff_reachesBoundary
    (V : Finset (ℤ × ℤ)) (h0 : (0, 0) ∈ V)
    (A : Configuration (pottsESGraph V)) :
    pottsESOriginExteriorConnected V h0 A ↔
      ∃ b, b ∈ pottsESBoundary V ∧
        ActualConnected (pottsESGraph V) A (pottsESOriginVertex V h0) b := by
  constructor
  · intro h
    have hrel := componentSetoid_le_boundaryReachRelation V A h
    rcases hrel with hpath | ⟨hleft, _⟩
    · exact ⟨none, by simp [pottsESBoundary], hpath⟩
    · exact hleft
  · rintro ⟨b, hb, hpath⟩
    apply (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).trans
    · exact actualConnected_component (pottsESGraph V)
        (pottsESBoundaryCondition V) A hpath
    · apply boundary_component
      exact (BoundaryCondition.wired_rel (pottsESBoundary V) b none).2
        (Or.inr ⟨hb, by simp [pottsESBoundary]⟩)

private theorem pottsESGraph_no_adjacent_to_ghost (V : Finset (ℤ × ℤ))
    {x : PottsESVertex V} (h : (pottsESGraph V).Adj x none) : False := by
  obtain ⟨u, v, _, hv, _⟩ := pottsESGraph_adj_endpoints V h
  cases hv

theorem pottsESGraph_no_actual_path_to_ghost (V : Finset (ℤ × ℤ))
    (A : Configuration (pottsESGraph V)) (x : PottsESVertex V)
    (hx : x ≠ none) :
    ¬ ActualConnected (pottsESGraph V) A x none := by
  have hIso : (openGraph (pottsESGraph V) A).IsIsolated none := by
    intro y hy
    exact pottsESGraph_no_adjacent_to_ghost V (openGraph_le _ _ hy).symm
  exact SimpleGraph.not_reachable_of_neighborSet_right_eq_empty hx
    (SimpleGraph.IsIsolated.neighborSet_eq_empty
      (openGraph (pottsESGraph V) A) hIso)

/-- Every origin connection to the wired exterior has an actual path to a
physical exterior endpoint; the isolated ghost itself cannot be that endpoint. -/
theorem pottsESOriginExteriorConnected_iff_reachesExteriorSite
    (V : Finset (ℤ × ℤ)) (h0 : (0, 0) ∈ V)
    (A : Configuration (pottsESGraph V)) :
    pottsESOriginExteriorConnected V h0 A ↔
      ∃ y : PottsESSite V, y.1 ∉ V ∧
        ActualConnected (pottsESGraph V) A (pottsESOriginVertex V h0) (some y) := by
  rw [pottsESOriginExteriorConnected_iff_reachesBoundary]
  constructor
  · rintro ⟨b, hb, hpath⟩
    cases b with
    | none =>
      have hne : pottsESOriginVertex V h0 ≠ none := by
        simp [pottsESOriginVertex]
      exact (pottsESGraph_no_actual_path_to_ghost V A _ hne hpath).elim
    | some y =>
      refine ⟨y, ?_, hpath⟩
      change (some y = none ∨ ∃ z, some y = some z ∧ z.1 ∉ V) at hb
      rcases hb with hfalse | ⟨z, hzy, hz⟩
      · cases hfalse
      · have hyz : z = y := Option.some.inj hzy.symm
        subst z
        exact hz
  · rintro ⟨y, hy, hpath⟩
    refine ⟨some y, ?_, hpath⟩
    change (some y = none ∨ ∃ z, some y = some z ∧ z.1 ∉ V)
    exact Or.inr ⟨y, rfl, hy⟩

end

end PottsContinuity.Thm1
