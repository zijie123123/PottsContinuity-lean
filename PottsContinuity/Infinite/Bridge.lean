module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Foundations.Bridges
public import PottsContinuity.WellDefined.Uniqueness
public import PottsContinuity.PD.Defs.IsRCInfiniteVolumeLimit

/-!
# Bridges from the frozen every-exhaustion limit to the PD box limit

The PD library uses the same finite random-cluster probabilities, after the
proved boundary bridge in `Foundations.Bridges`. The frozen definition tests
all monotone exhaustive vertex sets, so its box specialization supplies the
box-only limit predicate consumed by the reusable PD results.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Infinite

open PottsContinuity
open Classical

noncomputable section

private theorem rcEventProb_box_eq_PD_pattern (n : ℕ)
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (i : Fin 2)
    (A : Finset squareLattice.edgeSet) (ξ : squareLattice.edgeSet → Bool) :
    rcEventProb (box n) p q i
      (fun ω => ∀ e ∈ A, ∃ f,
        Sym2.map Subtype.val f.1 = e.1 ∧ ω f = ξ e) =
    ∑ ω : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet → Bool,
      if ∀ e ∈ A, ∃ f : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet,
        Sym2.map Subtype.val f.1 = e.1 ∧ ω f = ξ e
      then PottsContinuity.PD.rcProb (box n) p q i ω else 0 := by
  classical
  simp only [rcEventProb, PottsContinuity.Foundations.rcProb_eq_PD]

/-- A frozen infinite-volume limit satisfies the box-only PD limit predicate.
This local specialization is the bridge for PD results that are formulated
using boxes; the public frozen hypothesis still quantifies over every
monotone exhaustive sequence. -/
theorem isRCInfiniteVolumeLimit_to_PD_box
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (i : Fin 2)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q i μ) :
    PottsContinuity.PD.IsRCInfiniteVolumeLimit p q i μ := by
  change IsProbabilityMeasure μ ∧ _
  refine ⟨hμ.1, ?_⟩
  intro A ξ
  have hbox := hμ.2 (fun n => box n)
    PottsContinuity.WellDefined.box_monotone
    PottsContinuity.WellDefined.box_exhausts A ξ
  refine hbox.congr' ?_
  filter_upwards with n
  exact rcEventProb_box_eq_PD_pattern n p q i A ξ

end
end PottsContinuity.Infinite
