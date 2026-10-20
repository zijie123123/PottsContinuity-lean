module

public import PottsContinuity.BD12.KSTEventRegularity
public import PottsContinuity.PD.RCInfinite.FiniteEnergy
public import PottsContinuity.Infinite.Bridge

/-! Every prescribed finite all-open pattern has positive probability under
the actual frozen free and wired limits at interior parameters. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite MeasureTheory
noncomputable section
open scoped Classical

/-- Finite energy gives positive probability to every finite all-open event. -/
theorem infinite_allOpen_probability_pos (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (F : Finset PD.squareLattice.edgeSet) : 0 < μ.real (LatticeConfiguration.allOpen F) := by
  let : IsProbabilityMeasure μ := hμ.1
  have hPD := Infinite.isRCInfiniteVolumeLimit_to_PD_box _ _ _ _ hμ
  induction F using Finset.induction_on with
  | empty => simp [LatticeConfiguration.allOpen,Measure.real]
  | @insert e F he ih =>
    have hind : DependsOn ({e}ᶜ) (LatticeConfiguration.allOpen F) := by
      intro ω η hagree
      change (∀ f ∈ F, ω f = true) ↔ (∀ f ∈ F, η f = true)
      constructor
      · intro h f hf
        have hne : f ≠ e := by intro hfe; subst f; exact he hf
        exact (hagree f (by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hne)).symm.trans (h f hf)
      · intro h f hf
        have hne : f ≠ e := by intro hfe; subst f; exact he hf
        exact (hagree f (by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hne)).trans (h f hf)
    have hE := (cylinder_finite_energy θ i μ hPD e (isCylinder_allOpen F) hind).1
    have hset : LatticeConfiguration.allOpen (insert e F) =
        LatticeConfiguration.allOpen F ∩ {ω | ω e = true} := by
      ext ω
      simp [LatticeConfiguration.allOpen,and_comm]
    rw [← hset] at hE
    exact (mul_pos (openEnergy_pos θ) ih).trans_le hE

/-- Every fixed actual finite lattice walk is open with positive probability. -/
theorem infinite_kstPathOpen_probability_pos (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    {u v : LatticeVertex} (p : PD.squareLattice.Walk u v) :
    0 < μ.real {ω | kstPathOpen ω p} := by
  let F := p.edges.toFinset.subtype (· ∈ PD.squareLattice.edgeSet)
  have hset : {ω | kstPathOpen ω p} = LatticeConfiguration.allOpen F := by
    ext ω
    simp [kstPathOpen,LatticeConfiguration.allOpen,F]
  rw [hset]
  exact infinite_allOpen_probability_pos θ i μ hμ F

end
end PottsContinuity.BD12
