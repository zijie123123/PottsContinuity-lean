module

public import PottsContinuity.Thm3.Prop4.SourceMiddleDomain
public import PottsContinuity.Thm3.Prop4.TubeHalfTurn

/-! # Exact half-turn transport of trace-avoiding boundary access -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- Negation acts on the original unit lattice edges. -/
def traceAccessHalfTurnHom : PD.squareLattice →g PD.squareLattice where
  toFun := fun x => -x
  map_rel' := by
    intro x y hxy
    change |(-x.1)-(-y.1)|+|(-x.2)-(-y.2)| = 1
    change |x.1-y.1|+|x.2-y.2| = 1 at hxy
    simpa only [neg_sub_neg,abs_sub_comm] using hxy

/-- A bottom access avoiding an actual trace becomes top access avoiding
its exact negated trace; repeated walks and all boundary columns are retained. -/
theorem traceBottomAccessible_halfTurn (n : ℕ) (trace : Finset LatticeVertex)
    (z : LatticeVertex) (haccess : traceBottomAccessible n trace z) :
    traceTopAccessible n (trace.image fun w => -w) (-z) := by
  classical
  obtain ⟨t,ht,p,hp⟩ := haccess
  refine ⟨-t,by change -t.2 = (n : ℤ); omega,p.map traceAccessHalfTurnHom,?_⟩
  intro w hw
  erw [SimpleGraph.Walk.support_map] at hw
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
  obtain ⟨haB,haT⟩ := hp a ha
  refine ⟨(mem_box_neg_iff n a).mpr haB,?_⟩
  rintro hh
  obtain ⟨b,hb,hba⟩ := Finset.mem_image.mp hh
  have heq : b = a := neg_injective hba
  exact haT (heq ▸ hb)

/-- Absence of top access for the negated trace excludes original bottom access. -/
theorem traceBottomAccessible_not_of_halfTurn (n : ℕ) (trace : Finset LatticeVertex)
    (z : LatticeVertex) (hno : ¬traceTopAccessible n (trace.image fun w => -w) (-z)) :
    ¬traceBottomAccessible n trace z := fun h => hno (traceBottomAccessible_halfTurn n trace z h)

end
end PottsContinuity.Thm3.Prop4
