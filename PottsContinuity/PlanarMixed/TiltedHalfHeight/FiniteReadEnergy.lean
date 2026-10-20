module

public import PottsContinuity.PlanarMixed.TiltedHalfHeight.FiniteOpenBlockEnergy
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeight
open MeasureTheory PD.FK
noncomputable section
variable {V I : Type*} [Finite V] {G : SimpleGraph V}
local instance routeTwelveReadEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance routeTwelveReadEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- Pull back a finite original-edge block to its actual finite-volume indices. -/
def blockPullback (f : G.edgeSet → I) (F : Finset I) : Finset G.edgeSet := by
  classical
  exact Finset.univ.filter (fun e => f e∈F)

/-- An injective original-edge read does not increase a block's edge budget. -/
theorem blockPullback_card_le (f : G.edgeSet → I) (hf : Function.Injective f) (F : Finset I) :
    (blockPullback f F).card≤F.card := by
  classical
  let g : G.edgeSet ↪ I := ⟨f,hf⟩
  have hsub : (blockPullback f F).map g⊆F := by
    intro i hi
    obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hi
    exact (Finset.mem_filter.mp he).2
  exact (Finset.card_map g).symm.trans_le (Finset.card_le_card hsub)

/-- Disjoint original blocks have disjoint finite-volume pullbacks. -/
theorem blockPullback_disjoint (f : G.edgeSet → I) (F H : Finset I) (h : Disjoint F H) :
    Disjoint (blockPullback f F) (blockPullback f H) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hh
  exact (Finset.disjoint_left.mp h) (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hh).2

/-- Failure of all-open cylinders agrees with finite block failure once each
original block edge is supported, including every sampled closed edge. -/
theorem noOpenBlocks_read_iff (f : G.edgeSet → I)
    (read : Configuration G → I → Bool)
    (hread : ∀ A e, read A (f e)=decide (e∈A))
    (blocks : ℕ → Finset I) (k : ℕ)
    (hsupp : ∀ j<k, ∀ i∈blocks j, ∃ e, f e=i)
    (A : Configuration G) :
    (∀ j<k, ¬ (∀ i∈blocks j, read A i=true)) ↔
      A∈noOpenBlocks (fun j => blockPullback f (blocks j)) k := by
  classical
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  apply not_congr
  constructor
  · intro h e he
    have ho := h (f e) (Finset.mem_filter.mp he).2
    rw [hread] at ho
    exact of_decide_eq_true ho
  · intro h i hi
    obtain ⟨e,rfl⟩ := hsupp j hj i hi
    rw [hread]
    apply decide_eq_true
    exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)

/-- The finite many-block estimate transports through any literal original
edge read with eventual support; the boundary partition remains arbitrary. -/
theorem finite_noOpenBlocks_read_probability_le (θ : Parameters) (ξ : BoundaryCondition V)
    (f : G.edgeSet → I) (hf : Function.Injective f)
    (read : Configuration G → I → Bool)
    (hread : ∀ A e, read A (f e)=decide (e∈A))
    (blocks : ℕ → Finset I) (k M : ℕ)
    (hsupp : ∀ j<k, ∀ i∈blocks j, ∃ e, f e=i)
    (hdisjoint : ∀ i j, i<j → Disjoint (blocks i) (blocks j))
    (hcard : ∀ j<k, (blocks j).card≤M) :
    (measure G θ ξ {A | ∀ j<k, ¬ (∀ i∈blocks j, read A i=true)}).toReal ≤
      (1-(PD.RCInfinite.openEnergy θ)^M)^k := by
  have hevent : {A | ∀ j<k, ¬ (∀ i∈blocks j, read A i=true)} =
      noOpenBlocks (fun j => blockPullback f (blocks j)) k := by
    ext A
    exact noOpenBlocks_read_iff f read hread blocks k hsupp A
  rw [hevent]
  exact finite_noOpenBlocks_probability_le θ ξ _ k M
    (fun i j hij => blockPullback_disjoint f _ _ (hdisjoint i j hij))
    (fun j hj => (blockPullback_card_le f hf (blocks j)).trans (hcard j hj))

end
end PottsContinuity.PlanarMixed.TiltedHalfHeight
