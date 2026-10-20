module

public import PottsContinuity.PlanarTopology.HalfPlaneExitEvents
public import PottsContinuity.PlanarTopology.HalfPlaneFKG
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite
noncomputable section

/-- A first-exit walk realizes the exact one-terminal induced-domain event. -/
theorem halfPlaneExitEvent_of_original_walk (S : Set LatticeVertex) (L : Set ℤ)
    (ω : LatticeConfiguration) (y : ℤ) (hy : y ∈ L) (u : LatticeVertex) (hu : u ∈ S)
    (huH : 0 ≤ u.1) (p : (PD.rcInfiniteOpenGraph ω).Walk u (-1,y))
    (hp : ∀ z ∈ p.support, 0 ≤ z.1 ∨ z = (-1,y)) : ω ∈ halfPlaneExitEvent S L := by
  exact ⟨y,hy,⟨u,huH⟩,hu,⟨p.induce (halfPlaneExitDomain y) hp⟩⟩

theorem infiniteHit_opposite_subset_halfPlaneExit (S T : Set LatticeVertex)
    (hS : ∀ u ∈ S, 0 ≤ u.1) (hT : ∀ v ∈ T, v.1 ≤ -1)
    (ω : LatticeConfiguration) (hω : atMostOneInfiniteCluster ω)
    (hHit : ω ∈ infiniteHit S ∩ infiniteHit T) : ω ∈ halfPlaneExitEvent S Set.univ := by
  obtain ⟨⟨u,hu,hui⟩,⟨v,hv,hvi⟩⟩ := hHit
  obtain ⟨y,p,hp⟩ := open_connection_has_first_exterior_exit ω u v (hS u hu) (hT v hv) (hω u v hui hvi)
  exact halfPlaneExitEvent_of_original_walk S Set.univ ω y (Set.mem_univ _) u hu (hS u hu) p hp

/-- The FKG opposite-root product bound retains the actual crossing bond to
the exterior column, rather than stopping at the interior boundary line. -/
theorem halfPlaneExitEvent_ge_infiniteHit_product
    (μ : Measure LatticeConfiguration)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω)
    (S T : Set LatticeVertex) (hS : ∀ u ∈ S, 0 ≤ u.1) (hT : ∀ v ∈ T, v.1 ≤ -1) :
    μ (infiniteHit S) * μ (infiniteHit T) ≤ μ (halfPlaneExitEvent S Set.univ) := by
  apply (hFKG (infiniteHit S) (infiniteHit T) (infiniteHit_measurableSet S)
    (infiniteHit_measurableSet T) (infiniteHit_isUpperSet S) (infiniteHit_isUpperSet T)).trans
  apply measure_mono_ae
  filter_upwards [hunique] with ω hω
  exact infiniteHit_opposite_subset_halfPlaneExit S T hS hT ω hω

/-- With an opposite translate, the first-exit lower bound is the square of
the original marked-set infinite-cluster hit probability. -/
theorem halfPlaneExitEvent_ge_infiniteHit_square_of_translate
    (μ : Measure LatticeConfiguration)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω)
    (S : Set LatticeVertex) (a : LatticeVertex)
    (hμ : μ.map (latticeConfigurationTranslate a) = μ)
    (hS : ∀ u ∈ S, 0 ≤ u.1) (hT : ∀ v ∈ latticeTranslate a '' S, v.1 ≤ -1) :
    μ (infiniteHit S) ^ 2 ≤ μ (halfPlaneExitEvent S Set.univ) := by
  have hh := halfPlaneExitEvent_ge_infiniteHit_product μ hFKG hunique S (latticeTranslate a '' S) hS hT
  rw [measure_infiniteHit_translate μ a hμ S] at hh
  simpa only [pow_two] using hh

end
end PottsContinuity.PlanarTopology
