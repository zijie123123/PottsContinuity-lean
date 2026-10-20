module

public import PottsContinuity.Thm3.RSW.ArmOpen
public import PottsContinuity.PD.RCInfinite.FiniteModification
public import PottsContinuity.PD.RCInfinite.ExteriorClusters

/-!
# A strict finite-energy upper bound for the frozen free arm

Closing the finite star of the origin excludes every positive-radius arm.
The finite-modification argument also appears in Easy/P5OneArmPower for the
wired law; here it is applied directly to the supplied free law.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK PD.RCInfinite

/-- Finite energy supplies a uniform positive gap below one for the actual
free infinite-volume arm at every positive radius. -/
theorem oneArmProbability_uniform_gap (θ : Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, 1 ≤ n → oneArmProbability μ n ≤ 1-δ := by
  classical
  let F := boxIncidentEdges 0
  let ξ : PD.squareLattice.edgeSet → Bool := fun _ => false
  let B : Set PD.FK.LatticeConfiguration := setEdges F ξ '' Set.univ
  let δ := energyBound θ ^ F.card
  have hδ : 0 < δ := pow_pos (energyBound_pos θ) _
  let ρ : Measure PD.FK.LatticeConfiguration := μ
  have : IsProbabilityMeasure ρ := hμ.1
  have huniv : ρ.real Set.univ = 1 := by simp [Measure.real]
  have hBmeas : MeasurableSet B := measurableSet_setEdges_image F ξ MeasurableSet.univ
  have henergy : δ ≤ ρ.real B := by
    simpa only [δ, huniv, mul_one] using
      setEdges_image_energy θ 0 ρ (free_limit_to_PD _ _ μ hμ) F ξ
        (A := Set.univ) MeasurableSet.univ
  refine ⟨δ, hδ, fun n hn => ?_⟩
  have hsub : infiniteArmEvent n ⊆ Bᶜ := by
    rintro ω ⟨y, hy, hreach⟩ ⟨η, _, rfl⟩
    have hyPD : y ∈ PD.vertexBoundary (latticeBox (0,0) n) := by
      simpa only [Foundations.vertexBoundary_eq_PD, latticeBox_origin_eq_box, Foundations.box_eq_PD] using hy
    have hreachPD : (PD.rcInfiniteOpenGraph (setEdges F ξ η)).Reachable (0,0) y := hreach
    obtain ⟨w⟩ := hreachPD
    cases w with
    | nil =>
        have hs := box_boundary_coordinate_edge n hyPD
        rcases hs with h | h | h | h <;> norm_num at h <;> omega
    | @cons u v y hadj tail =>
        obtain ⟨he, hstate⟩ := (rcInfiniteOpenGraph_adj (setEdges F ξ η) (0,0) v).mp hadj
        let e : PD.squareLattice.edgeSet := ⟨s((0,0),v), he⟩
        have heF : e ∈ F := by
          apply edge_incident_box_mem_boxIncidentEdges
          exact ⟨(0,0), center_mem_latticeBox (0,0) 0, by simp [e]⟩
        have hfalse : setEdges F ξ η e = false := by simp only [setEdges, heF, ite_eq_left, ξ]
        rw [hfalse] at hstate
        cases hstate
  calc
    oneArmProbability μ n ≤ ρ.real Bᶜ := measureReal_mono (μ := ρ) hsub
    _ = 1-ρ.real B := by rw [measureReal_compl hBmeas, huniv]
    _ ≤ 1-δ := sub_le_sub_left henergy 1

/-- In particular the positive-radius free arm is strictly below one. -/
theorem oneArmProbability_lt_one (θ : Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (n : ℕ) (hn : 1 ≤ n) :
    oneArmProbability μ n < 1 := by
  obtain ⟨δ, hδ, hbound⟩ := oneArmProbability_uniform_gap θ μ hμ
  exact (hbound n hn).trans_lt (sub_lt_self 1 hδ)

end PottsContinuity.RSW
