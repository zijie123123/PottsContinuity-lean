module

public import PottsContinuity.Thm1.ShellGhostConnectivity
public import PottsContinuity.Thm1.ShellPathBridge
public import PottsContinuity.PD.FK.Wiring

@[expose] public section

namespace PottsContinuity.Thm1

open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

def pottsESReachesBoundary (V : Finset (ℤ × ℤ))
    (A : Configuration (pottsESGraph V)) (x : PottsESVertex V) : Prop :=
  ∃ b, b ∈ pottsESBoundary V ∧ ActualConnected (pottsESGraph V) A x b

def pottsESBoundaryReachRelation (V : Finset (ℤ × ℤ))
    (A : Configuration (pottsESGraph V)) : Setoid (PottsESVertex V) where
  r x y := ActualConnected (pottsESGraph V) A x y ∨
    (pottsESReachesBoundary V A x ∧ pottsESReachesBoundary V A y)
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

private theorem pottsESComponentSetoid_le_boundaryReachRelation
    (V : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V)) :
    componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A ≤
      pottsESBoundaryReachRelation V A := by
  apply componentSetoid_le
  · intro x y hxy
    exact Or.inl hxy
  · intro x y hxy
    rcases (BoundaryCondition.wired_rel (pottsESBoundary V) x y).mp hxy with heq | ⟨hx, hy⟩
    · subst y
      exact Or.inl (SimpleGraph.Reachable.refl x)
    · exact Or.inr
        ⟨⟨x, hx, SimpleGraph.Reachable.refl x⟩,
          ⟨y, hy, SimpleGraph.Reachable.refl y⟩⟩

/-- Two shell vertices are identified by the wired component relation exactly
when they are joined by an open shell path or both reach the wired exterior. -/
theorem pottsESComponentRelation_iff_pathOrBoundary
    (V : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V))
    (x y : PottsESVertex V) :
    (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r x y ↔
      ActualConnected (pottsESGraph V) A x y ∨
        (pottsESReachesBoundary V A x ∧ pottsESReachesBoundary V A y) := by
  constructor
  · intro h
    exact pottsESComponentSetoid_le_boundaryReachRelation V A h
  · intro h
    rcases h with hxy | ⟨hx, hy⟩
    · exact actualConnected_component (pottsESGraph V)
        (pottsESBoundaryCondition V) A hxy
    · obtain ⟨bx, hbx, hxb⟩ := hx
      obtain ⟨bY, hbY, hyb⟩ := hy
      have hxb' :
          (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r x bx :=
        actualConnected_component (pottsESGraph V)
          (pottsESBoundaryCondition V) A hxb
      have hby' :
          (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r bY y :=
        actualConnected_component (pottsESGraph V)
          (pottsESBoundaryCondition V) A hyb.symm
      have hbound :
          (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r bx bY := by
        apply boundary_component
        exact (BoundaryCondition.wired_rel (pottsESBoundary V) bx bY).2
          (Or.inr ⟨hbx, hbY⟩)
      exact (componentSetoid (pottsESGraph V)
        (pottsESBoundaryCondition V) A).trans
          ((componentSetoid (pottsESGraph V)
            (pottsESBoundaryCondition V) A).trans hxb' hbound) hby'

private theorem pottsESExteriorExit_iff_ghostComponent
    (V : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V))
    (x : ℤ × ℤ) (hx : x ∈ pottsESSupport V) (hxV : x ∈ V) :
    (∃ y, y ∉ V ∧
      (PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A)).Reachable x y) ↔
      (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r
        (some ⟨x, hx⟩) none := by
  constructor
  · rintro ⟨y, hy, hreach⟩
    have hne : x ≠ y := fun heq => hy (heq ▸ hxV)
    have hyGraph :
        y ∈ (PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A)).support :=
      SimpleGraph.mem_support_of_reachable hne.symm hreach.symm
    have hySupport := pottsESSupport_of_rcInfiniteSupport V A hyGraph
    have hpath := (pottsESActualConnected_iff_latticeReachable V A x y hx hySupport).2 hreach
    have hyBoundary : some ⟨y, hySupport⟩ ∈ pottsESBoundary V := by
      rw [pottsESBoundary]
      exact Or.inr ⟨⟨y, hySupport⟩, rfl, hy⟩
    have hactual := actualConnected_component (pottsESGraph V)
      (pottsESBoundaryCondition V) A hpath
    have hboundary := boundary_component (pottsESGraph V)
      (pottsESBoundaryCondition V) A
      ((BoundaryCondition.wired_rel (pottsESBoundary V)
        (some ⟨y, hySupport⟩) none).2
        (Or.inr ⟨hyBoundary, by simp [pottsESBoundary]⟩))
    exact (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).trans
      hactual hboundary
  · intro h
    have hparts := (pottsESComponentRelation_iff_pathOrBoundary V A
      (some ⟨x, hx⟩) none).mp h
    rcases hparts with hpath | ⟨hreach, _⟩
    · exact False.elim (pottsESGraph_no_actual_path_to_ghost V A
        (some ⟨x, hx⟩) (by simp) hpath)
    · rcases hreach with ⟨b, hb, hpath⟩
      have hb' : b = none ∨ ∃ z, b = some z ∧ z.1 ∉ V := by
        simpa [pottsESBoundary] using hb
      rcases hb' with hghost | ⟨z, hzb, hzV⟩
      · subst b
        exact False.elim (pottsESGraph_no_actual_path_to_ghost V A
          (some ⟨x, hx⟩) (by simp) hpath)
      · subst b
        have hreach' := (pottsESActualConnected_iff_latticeReachable V A
          x z.1 hx z.2).1 hpath
        exact ⟨z.1, hzV, hreach'⟩

/-- A wired shell relation between two physical vertices is an actual
whole-lattice connection, or both vertices reach the exterior of the shell. -/
theorem pottsESComponentRelation_iff_latticePathOrBothExit
    (V : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V))
    (x y : ℤ × ℤ) (hx : x ∈ pottsESSupport V) (hy : y ∈ pottsESSupport V)
    (hxV : x ∈ V) (hyV : y ∈ V) :
    (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r
        (some ⟨x, hx⟩) (some ⟨y, hy⟩) ↔
      (PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A)).Reachable x y ∨
        ((∃ z, z ∉ V ∧
          (PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A)).Reachable x z) ∧
         (∃ z, z ∉ V ∧
          (PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A)).Reachable y z)) := by
  rw [pottsESComponentRelation_iff_pathOrBoundary]
  constructor
  · rintro (hpath | ⟨hxBoundary, hyBoundary⟩)
    · exact Or.inl ((pottsESActualConnected_iff_latticeReachable
        V A x y hx hy).1 hpath)
    · exact Or.inr ⟨
        (pottsESExteriorExit_iff_ghostComponent V A x hx hxV).2
          ((pottsESComponentRelation_iff_pathOrBoundary V A
            (some ⟨x, hx⟩) none).2 (Or.inr ⟨hxBoundary, by
              exact ⟨none, by simp [pottsESBoundary], SimpleGraph.Reachable.refl _⟩⟩)),
        (pottsESExteriorExit_iff_ghostComponent V A y hy hyV).2
          ((pottsESComponentRelation_iff_pathOrBoundary V A
            (some ⟨y, hy⟩) none).2 (Or.inr ⟨hyBoundary, by
              exact ⟨none, by simp [pottsESBoundary], SimpleGraph.Reachable.refl _⟩⟩))⟩
  · rintro (hpath | ⟨hxExit, hyExit⟩)
    · exact Or.inl ((pottsESActualConnected_iff_latticeReachable
        V A x y hx hy).2 hpath)
    · have hxn := (pottsESExteriorExit_iff_ghostComponent V A x hx hxV).1 hxExit
      have hyn := (pottsESExteriorExit_iff_ghostComponent V A y hy hyV).1 hyExit
      let R := componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A
      have hny := R.iseqv.symm hyn
      have hxy := R.trans hxn hny
      exact (pottsESComponentRelation_iff_pathOrBoundary V A
        (some ⟨x, hx⟩) (some ⟨y, hy⟩)).mp hxy

end

end PottsContinuity.Thm1
