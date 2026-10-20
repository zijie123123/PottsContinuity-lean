module

public import PottsContinuity.Thm3.Prop4.TranslatedInfiniteArm

/-!
# Exact real-radius rounding for square-lattice escape

A real square-radius escape is precisely a hit of the integer ceiling boundary.
The proof follows a first exit and does not require the sampled cluster to be finite.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK.Medial

/-- A path reaching square displacement at least n hits the exact translated frozen boundary. -/
theorem lattice_reachable_hits_square_boundary (G : SimpleGraph (ℤ × ℤ))
    (hG : G ≤ squareLattice) (x z : ℤ × ℤ) (n : ℕ)
    (hz : (n : ℤ) ≤ max |z.1-x.1| |z.2-x.2|) (hconn : G.Reachable x z) :
    ∃ d ∈ vertexBoundary (box n), G.Reachable x (d+x) := by
  obtain ⟨w⟩ := hconn
  let S : Set (ℤ × ℤ) := {v | max |v.1-x.1| |v.2-x.2| ≤ (n : ℤ)}
  have hstart : x ∈ S := by simp [S]
  by_cases hzin : z ∈ S
  · refine ⟨z-x,?_,?_⟩
    · rw [Foundations.vertexBoundary_box_eq]
      exact le_antisymm hzin hz
    · simpa only [sub_add_cancel] using (show G.Reachable x z from ⟨w⟩)
  · obtain ⟨d,hd,hdin,hdout⟩ := w.exists_boundary_dart S hstart hzin
    have hsq := hG d.adj
    change |d.fst.1-d.snd.1|+|d.fst.2-d.snd.2|=1 at hsq
    have hin : max |d.fst.1-x.1| |d.fst.2-x.2| ≤ (n : ℤ) := hdin
    have hout : ¬max |d.snd.1-x.1| |d.snd.2-x.2| ≤ (n : ℤ) := hdout
    refine ⟨d.fst-x,?_,?_⟩
    · rw [Foundations.vertexBoundary_box_eq]
      change max |d.fst.1-x.1| |d.fst.2-x.2| = (n : ℤ)
      simp only [abs_eq_max_neg] at hin hout hsq ⊢
      omega
    · simpa only [sub_add_cancel] using
        (show G.Reachable x d.fst from ⟨w.takeUntil d.fst (w.dart_fst_mem_support_of_mem_darts hd)⟩)

/-- Real square radii round upwards exactly, including radius zero. -/
theorem real_square_escape_iff_boundary_hit (G : SimpleGraph (ℤ × ℤ))
    (hG : G ≤ squareLattice) (x : ℤ × ℤ) (r : ℝ) (hr : 0 ≤ r) :
    (∃ z : ℤ × ℤ, r ≤ (max |z.1-x.1| |z.2-x.2| : ℤ) ∧ G.Reachable x z) ↔
      ∃ d ∈ vertexBoundary (box ⌈r⌉₊), G.Reachable x (d+x) := by
  constructor
  · rintro ⟨z,hz,hxz⟩
    apply lattice_reachable_hits_square_boundary G hG x z ⌈r⌉₊ _ hxz
    rw [Int.natCast_ceil_eq_ceil hr]
    exact Int.ceil_le.mpr hz
  · rintro ⟨d,hd,hxd⟩
    refine ⟨d+x,?_,hxd⟩
    have hrad := hd
    rw [Foundations.vertexBoundary_box_eq] at hrad
    change max |d.1| |d.2| = (⌈r⌉₊ : ℤ) at hrad
    have hradR : ((max |d.1| |d.2| : ℤ) : ℝ) = (⌈r⌉₊ : ℝ) := by exact_mod_cast hrad
    simpa only [Prod.fst_add,Prod.snd_add,add_sub_cancel_right,hradR] using Nat.le_ceil r

/-- Every actual whole-plane closed-dual edge is a nearest-neighbour face-label edge. -/
theorem wholePlaneClosedDualGraph_le_squareLattice (ω : PD.FK.LatticeConfiguration) :
    wholePlaneClosedDualGraph ω ≤ squareLattice := by
  rintro u v ⟨b,_,huv | huv⟩
  · rw [huv.1,huv.2]
    change PD.FK.squareLattice.Adj _ _
    simpa only [dualBondOfPrimal_source,dualBondOfPrimal_target] using
      (dualBondOfPrimal b).adjacent
  · rw [huv.1,huv.2]
    change PD.FK.squareLattice.Adj _ _
    exact PD.FK.squareLattice.adj_symm (by
      simpa only [dualBondOfPrimal_source,dualBondOfPrimal_target] using
        (dualBondOfPrimal b).adjacent)

/-- Closed-dual escape at a real square radius is the exact transformed free arm event. -/
theorem selfDual_wired_dual_square_escape_probability (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : MeasureTheory.Measure PD.FK.LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 1 μ₁) (x : ℤ × ℤ) (r : ℝ) (hr : 0 ≤ r) :
    μ₁.real {ω | ∃ z : ℤ × ℤ, r ≤ (max |z.1-x.1| |z.2-x.2| : ℤ) ∧
      (wholePlaneClosedDualGraph ω).Reachable x z} = RSW.oneArmProbability μ₀ ⌈r⌉₊ := by
  have heq : {ω : PD.FK.LatticeConfiguration | ∃ z : ℤ × ℤ,
      r ≤ (max |z.1-x.1| |z.2-x.2| : ℤ) ∧ (wholePlaneClosedDualGraph ω).Reachable x z} =
      {ω | ∃ d ∈ vertexBoundary (box ⌈r⌉₊), (wholePlaneClosedDualGraph ω).Reachable x (d+x)} := by
    ext ω
    exact real_square_escape_iff_boundary_hit _ (wholePlaneClosedDualGraph_le_squareLattice ω) x r hr
  rw [heq]
  exact selfDual_wired_translated_dual_oneArm_probability q μ₀ μ₁ hμ₀ hμ₁ x ⌈r⌉₊

end PottsContinuity.Thm3.Prop4
