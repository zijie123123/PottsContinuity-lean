module

public import PottsContinuity.BD12.InfiniteRadiusTranslation
public import PottsContinuity.BD12.WiredSquare

/-! A square crossing starts a radius-n arm at one of its n+1 left-side
vertices. This supplies a polynomial one-arm lower bound at the self-dual point. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite MeasureTheory
noncomputable section
open scoped Classical

/-- An actual horizontal square crossing yields an arm rooted on its left side. -/
theorem square_crossing_subset_radius_union (n : ℕ) :
    horizontalRectangle (0,0) (n+1) n ⊆
      ⋃ i : Fin (n+1), infiniteRadiusEvent (0,((i : ℕ) : ℤ)) n := by
  rintro ω ⟨u,v,hu,hv,hconn⟩
  have hu1 : u.val.1 = 0 := (Finset.mem_filter.mp hu).2
  have hv1 : v.val.1 = 0 + ((n+1 : ℕ) : ℤ) := (Finset.mem_filter.mp hv).2
  have hu2 := (mem_latticeRectangle (0,0) u.val (n+1) n).mp u.property
  let i : Fin (n+1) := ⟨u.val.2.toNat, by omega⟩
  have hui : u.val = (0,((i : ℕ) : ℤ)) := by
    apply Prod.ext
    · exact hu1
    · dsimp only [i]
      omega
  have hr : n ≤ latticeRadius u.val v.val := by
    have hx : (v.val.1 - u.val.1).natAbs = n+1 := by rw [hu1,hv1,zero_add,sub_zero,Int.natAbs_natCast]
    rw [latticeRadius,hx]
    exact (Nat.le_succ n).trans (le_max_left _ _)
  have hgraph := embeddedRestriction_domainGraph (PD.FK.latticeRectangle (0,0) (n+1) n) ω
  have hconn' : ((PD.rcInfiniteOpenGraph ω).induce (PD.FK.latticeRectangle (0,0) (n+1) n : Set LatticeVertex)).Reachable u v := by
    rw [← hgraph]
    exact hconn
  let f : (PD.rcInfiniteOpenGraph ω).induce (PD.FK.latticeRectangle (0,0) (n+1) n : Set LatticeVertex) →g
      PD.rcInfiniteOpenGraph ω := { toFun := Subtype.val, map_rel' := fun h => h }
  obtain ⟨p⟩ := hconn'.map f
  obtain ⟨z,q,hz,_⟩ := walk_reaches_radius_inside_ball (latticeRadius u.val)
    (infinite_open_radius_step u.val ω) p n (by change latticeRadius u.val u.val ≤ n; simp) hr
  have hE : ω ∈ infiniteRadiusEvent u.val n := ⟨z,hz,⟨q⟩⟩
  rw [hui] at hE
  exact Set.mem_iUnion.mpr ⟨i,hE⟩

/-- Translation invariance and the union bound compare square and arm probabilities. -/
theorem wired_square_crossing_le_one_arm (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ) (n : ℕ) :
    μ.real (horizontalRectangle (0,0) (n+1) n) ≤
      (n+1 : ℕ) * μ.real (infiniteRadiusEvent (0,0) n) := by
  let : IsProbabilityMeasure μ := hμ.1
  have h := (measureReal_mono (μ := μ) (square_crossing_subset_radius_union n)).trans
    (measureReal_iUnion_fintype_le (μ := μ) (fun i : Fin (n+1) => infiniteRadiusEvent (0,((i : ℕ) : ℤ)) n))
  simpa only [wired_infiniteRadiusEvent_probability_eq_origin θ μ hμ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

/-- The wired square bound forces a polynomial actual one-arm lower bound. -/
theorem wired_selfDual_one_arm_polynomial_lower_bound (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP
      (criticalParameters q).toQ 1 μ) (n : ℕ) :
    (1/2 : ℝ) ≤ (n+1 : ℕ) * μ.real (infiniteRadiusEvent (0,0) n) :=
  (wired_square_crossing_ge_half q μ hμ (0,0) n).trans
    (wired_square_crossing_le_one_arm _ μ hμ n)

end
end PottsContinuity.BD12
