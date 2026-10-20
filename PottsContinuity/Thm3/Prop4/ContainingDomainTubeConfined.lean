module

public import PottsContinuity.Thm3.Prop4.UniformCorridorTube
public import PottsContinuity.Thm3.Prop4.FiniteWiredRectangleError

/-!
# Tube-confined crossings in containing finite domains

The witness retains every visited vertex in the actual tube, even when the
sample is taken on a larger finite induced domain.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.RCInfinite
noncomputable section

/-- Original-edge horizontal crossing whose entire walk stays inside the tube. -/
def inducedTubeConfinedCrossingEvent (S : Finset LatticeVertex) (n : ℕ)
    (R : ℝ) (u v : LatticeVertex) : Set (Configuration (finiteLatticeGraph S)) :=
  {A | ∃ a b : (S : Set LatticeVertex), a.val.1 = -(n : ℤ) ∧ b.val.1 = (n : ℤ) ∧
    ∃ p : (openGraph (finiteLatticeGraph S) A).Walk a b,
      ∀ z ∈ p.support, z.val ∈ radiusTube n R u v}

/-- Adding original edges preserves the same tube-confined witness. -/
theorem inducedTubeConfinedCrossingEvent_isUpperSet (S : Finset LatticeVertex) (n : ℕ)
    (R : ℝ) (u v : LatticeVertex) : IsUpperSet (inducedTubeConfinedCrossingEvent S n R u v) := by
  rintro A B hAB ⟨a,b,ha,hb,p,hp⟩
  refine ⟨a,b,ha,hb,p.mapLe (openGraph_mono hAB),?_⟩
  simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hp

/-- A plane tube crossing gives a confined original-edge witness in any
containing domain, with exactly the same sampled states. -/
theorem tube_crossing_subset_containing_domain_confined (n : ℕ) (R : ℝ) (u v : LatticeVertex)
    (S : Finset LatticeVertex) (hS : radiusTube n R u v ⊆ S) :
    tubeHorizontalCrossingEvent n R u v ⊆
      Infinite.latticeGraphEvent (finiteLatticeGraph S)
        (finiteDomainEmbedding S) (finiteDomainEmbedding_map_le S)
        (inducedTubeConfinedCrossingEvent S n R u v) := by
  intro ω hω
  obtain ⟨a,b,ha,hb,hab⟩ := hω
  change (openGraph _ _).Reachable a b at hab
  rw [BD12.embeddedRestriction_domainGraph] at hab
  obtain ⟨p⟩ := hab
  change Infinite.latticeGraphRestriction (finiteLatticeGraph S) (finiteDomainEmbedding S)
    (finiteDomainEmbedding_map_le S) ω ∈ inducedTubeConfinedCrossingEvent S n R u v
  rw [induced_original_restriction_eq]
  change ∃ a b : (S : Set LatticeVertex), a.val.1 = -(n : ℤ) ∧ b.val.1 = (n : ℤ) ∧
    ∃ p : (openGraph (finiteLatticeGraph S)
      (BD12.embeddedRestriction (finiteLatticeGraph S) (frozenEdgeEmbedding S) ω)).Walk a b,
      ∀ z ∈ p.support, z.val ∈ radiusTube n R u v
  rw [BD12.embeddedRestriction_domainGraph]
  let f : ((PD.rcInfiniteOpenGraph ω).induce (radiusTube n R u v : Set LatticeVertex)) →g
      ((PD.rcInfiniteOpenGraph ω).induce (S : Set LatticeVertex)) :=
    ⟨fun z => ⟨z.val,hS z.property⟩,fun h => h⟩
  refine ⟨f a,f b,ha,hb,p.map f,?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  exact w.property

end
end PottsContinuity.Thm3.Prop4
