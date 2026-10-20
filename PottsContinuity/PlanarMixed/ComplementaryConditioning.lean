module

public import PottsContinuity.PlanarMixed.OrderedCutActive
public import PottsContinuity.PD.FK.ConditionalLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PottsContinuity.PlanarMixed.CanonicalCutCarrier
public import PottsContinuity.PlanarMixed.SlitActiveReflection
public import PottsContinuity.PD.Duality.WholePlaneDualConfiguration
public import PottsContinuity.PD.Duality.ConnectionSymmetry
public import PottsContinuity.PlanarMixed.Square.Consumers
public import PottsContinuity.PD.RCInfinite.Cylinders
public import PottsContinuity.PD.FK.IsolatedBoundaryLaw
public import PottsContinuity.Infinite.MeasurableApprox
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.Sequences
public import PottsContinuity.PD.FK.CylinderConvergence
public import PottsContinuity.PD.FK.EmbeddedClosedInteriorOuterBoundary
public import PottsContinuity.PD.FK.EmbeddedBoundaryUpper
public import PottsContinuity.PlanarMixed.OmegaInterfaces
public import PottsContinuity.FKC.FiniteFK.RectangleConnectivity
public import PottsContinuity.DualityExt.PositiveConnectedBoundaryPartition
public import PottsContinuity.PD.Duality.RectangleDualAmbient

/-! Exact conditioning transport for complementary finite edge bijections.
These identities concern fully specified frozen states and normalization;
they do not identify any induced planar boundary partition. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK PD.FK.FiniteProbability
noncomputable section

/-- Conditioning commutes with a bijective change of coordinates when the
two events have exactly the stated preimage relation. -/
theorem pmf_map_filter_equiv {α β : Type*} (p : PMF α) (d : α ≃ β)
    (S : Set α) (T : Set β) (hevent : S = d ⁻¹' T)
    (hS : ∃ a ∈ S, a ∈ p.support)
    (hT : ∃ b ∈ T, b ∈ (p.map d).support) :
    (p.filter S hS).map d = (p.map d).filter T hT := by
  classical
  have hf : S.indicator p = fun a => T.indicator (p.map d) (d a) := by
    funext a
    simp only [Set.indicator_apply,map_equiv_apply,Equiv.symm_apply_apply]
    simp only [hevent,Set.mem_preimage]
  have hmass : (∑' a, S.indicator p a) = ∑' b, T.indicator (p.map d) b := by
    rw [hf]
    exact d.tsum_eq _
  ext b
  rw [map_equiv_apply,PMF.filter_apply,PMF.filter_apply,hmass]
  have hb : d.symm b ∈ S ↔ b ∈ T := by simp only [hevent,Set.mem_preimage,Equiv.apply_symm_apply]
  simp only [Set.indicator_apply,hb,map_equiv_apply]

/-- Complementing a prescribed source pattern gives an exact prescribed
dual pattern on the crossing image of its whole frozen carrier. -/
theorem complementary_frozen_intersection_iff {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (f : α ≃ β) (d : Finset α ≃ Finset β)
    (hd : ∀ A a, f a ∈ d A ↔ a ∉ A)
    (R K C : Finset α) (hK : K ⊆ R) :
    C ∩ R = K ↔ d C ∩ R.map f.toEmbedding = d K ∩ R.map f.toEmbedding := by
  constructor
  · intro h
    apply Finset.ext
    intro b
    obtain ⟨a,rfl⟩ := f.surjective b
    have ha := iff_of_eq (congrArg (fun A => a ∈ A) h)
    by_cases hR : a ∈ R
    · have hCK : a ∈ C ↔ a ∈ K := by simpa only [Finset.mem_inter,hR,and_true] using ha
      simp only [Finset.mem_inter,Finset.mem_map_equiv,Equiv.symm_apply_apply,hd,hCK]
    · simp only [Finset.mem_inter,Finset.mem_map_equiv,Equiv.symm_apply_apply,hR,and_false]
  · intro h
    apply Finset.ext
    intro a
    by_cases hR : a ∈ R
    · have ha := iff_of_eq (congrArg (fun A => f a ∈ A) h)
      have hn : a ∉ C ↔ a ∉ K := by
        simpa only [Finset.mem_inter,Finset.mem_map_equiv,Equiv.symm_apply_apply,hd,hR,and_true] using ha
      simpa only [Finset.mem_inter,hR,and_true] using (not_iff_not.mp hn)
    · have hnK : a ∉ K := fun ha => hR (hK ha)
      simp only [Finset.mem_inter,hR,and_false,hnK]

end
end PottsContinuity.PlanarMixed
