module

public import PottsContinuity.Thm3.Push.AuxiliaryLabelCut
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance filledRegionPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The union of the components of the complement of a region S which meet
one of the specified outside seeds. Filling all other components is literal
hole filling; no outside seed lying in S is admitted. -/
def outsideSeedRegion {W : Type*} (H : SimpleGraph W) (S : Set W) (T : Finset W) : Set W :=
  {v | ∃ b ∈ T, ∃ hb : b ∉ S, ∃ hv : v ∉ S,
    (H.induce Sᶜ).Reachable ⟨b,hb⟩ ⟨v,hv⟩}

theorem outsideSeedRegion_subset_compl {W : Type*} (H : SimpleGraph W)
    (S : Set W) (T : Finset W) : outsideSeedRegion H S T ⊆ Sᶜ := by
  rintro v ⟨b,hb,hbs,hvs,hpath⟩
  exact hvs

theorem mem_outsideSeedRegion_of_seed {W : Type*} (H : SimpleGraph W)
    (S : Set W) (T : Finset W) {b : W} (hb : b ∈ T) (hbs : b ∉ S) :
    b ∈ outsideSeedRegion H S T :=
  ⟨b,hb,hbs,hbs,SimpleGraph.Reachable.rfl⟩

/-- Neighbor closure in the complement is part of the construction, not an
assumption about the explored planar geometry. -/
theorem outsideSeedRegion_adj_closed {W : Type*} (H : SimpleGraph W)
    (S : Set W) (T : Finset W) {u v : W}
    (hu : u ∈ outsideSeedRegion H S T) (hv : v ∉ S) (huv : H.Adj u v) :
    v ∈ outsideSeedRegion H S T := by
  obtain ⟨b,hb,hbs,hus,hpath⟩ := hu
  exact ⟨b,hb,hbs,hv,hpath.trans (show (H.induce Sᶜ).Adj ⟨u,hus⟩ ⟨v,hv⟩ from huv).reachable⟩

/-- Every edge leaving the seed-connected complement enters the ORIGINAL
region S. Hole filling creates no new frontier edges. -/
theorem outsideSeedRegion_boundary_in_original {W : Type*} (H : SimpleGraph W)
    (S : Set W) (T : Finset W) {u v : W} (hu : u ∈ outsideSeedRegion H S T)
    (hv : v ∉ outsideSeedRegion H S T) (huv : H.Adj u v) : v ∈ S := by
  by_contra hvs
  exact hv (outsideSeedRegion_adj_closed H S T hu hvs huv)

/-- Filling components away from the outside seeds removes cut bonds; it
never adds a primal bond which was not in the original region's frontier. -/
theorem filled_region_labelCut_subset {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G.edgeSet ≃ H.edgeSet)
    (S : Set W) (T : Finset W) :
    auxiliaryLabelCut e (fun v => decide (v ∉ outsideSeedRegion H S T)) ⊆
      auxiliaryLabelCut e (fun v => decide (v ∈ S)) := by
  classical
  intro f hf
  let p := (e f).val.out
  have hp : (e f).val = s(p.1,p.2) := (Quot.out_eq _).symm
  have hadj : H.Adj p.1 p.2 := H.mem_edgeSet.mp (hp ▸ (e f).property)
  have hne := (mem_auxiliaryLabelCut_iff e _ f p.1 p.2 hp).mp hf
  apply (mem_auxiliaryLabelCut_iff e _ f p.1 p.2 hp).mpr
  by_cases hu : p.1 ∈ outsideSeedRegion H S T
  · have hv : p.2 ∉ outsideSeedRegion H S T := by
      intro hv
      exact hne (by simp only [hu,hv,not_true_eq_false,decide_false])
    have hus : p.1 ∉ S := outsideSeedRegion_subset_compl H S T hu
    have hvs := outsideSeedRegion_boundary_in_original H S T hu hv hadj
    simp only [hus,hvs,decide_true,decide_false,ne_eq,reduceCtorEq,not_false_eq_true]
  · have hv : p.2 ∈ outsideSeedRegion H S T := by
      by_contra hv
      exact hne (by simp only [hu,hv,not_false_eq_true,decide_true])
    have hvs : p.2 ∉ S := outsideSeedRegion_subset_compl H S T hv
    have hus := outsideSeedRegion_boundary_in_original H S T hv hu hadj.symm
    simp only [hus,hvs,decide_true,decide_false,ne_eq,reduceCtorEq,not_false_eq_true]

end
end PottsContinuity.Push
