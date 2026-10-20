module

public import PottsContinuity.Thm3.Push.CrossingRestriction

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.RSW PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
noncomputable section

/-- Increasing the height of the domain weakens its top/side wiring as seen
by the unchanged bottom crossing event. All finite induced graphs and all
lattice floors are retained; the FK parameters need not be self-dual. -/
theorem top_wired_height_comparison_parameters (θ : Parameters) (k ℓ L : ℝ)
    (hk : 0 ≤ k) (hℓ : 1 ≤ ℓ) (hL : ℓ ≤ L) (n : ℕ) :
    finiteBoundaryEventProbability (topWiredRectangle k L n) θ
        (topWiredRectangleBoundary k L n)
        (horizontalCrossing (topWiredRectangle k L n) (-⌊k*n⌋) ⌊k*n⌋ 0 n) ≤
      finiteBoundaryEventProbability (topWiredRectangle k ℓ n) θ
        (topWiredRectangleBoundary k ℓ n)
        (horizontalCrossing (topWiredRectangle k ℓ n) (-⌊k*n⌋) ⌊k*n⌋ 0 n) := by
  let S := topWiredRectangle k ℓ n
  let T := topWiredRectangle k L n
  let hH := topWired_height_floor_mono ℓ L hL n
  let hST := topWiredRectangle_subset k ℓ L n hH
  let f := finiteLatticeVertexEmbedding hST
  let G := finiteLatticeGraph S
  let H := finiteLatticeGraph T
  let hGH := finiteLatticeGraph_map_le hST
  let B := (topWiredRectangleBoundary k ℓ n).boundary
  let E := finiteBoolEvent S (horizontalCrossing S (-⌊k*n⌋) ⌊k*n⌋ 0 n)
  have hE : IsUpperSet E :=
    finiteBoolEvent_isUpperSet S _ (horizontalCrossing_isUpperSet S _ _ _ _)
  have hcompare := embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    f hGH θ (topWiredRectangleBoundary k L n) B
    (fun _ hx _ hxy => topWiredHeightEmbedding_neighbor_closed k ℓ L n hH hx hxy)
    (fun _ hx => topWiredHeightEmbedding_boundary_avoid k ℓ L n hH hx) E hE
  have hw : 0 ≤ ⌊k * n⌋ := Int.floor_nonneg.mpr (mul_nonneg hk (Nat.cast_nonneg n))
  have hnH : (n : ℤ) ≤ ⌊ℓ * n⌋ := by
    apply Int.le_floor.mpr
    push_cast
    nlinarith only [hℓ, Nat.cast_nonneg (α := ℝ) n]
  have hRS : PD.FK.latticeRectangle (-⌊k*n⌋, 0)
      (⌊k*n⌋ - -⌊k*n⌋).toNat ((n : ℤ)-0).toNat ⊆ S := by
    rw [Foundations.pdRectangle_eq_frozenRectangle_of_corners _ _ _ _ (by omega) (by omega)]
    intro v hv
    have hv' : -⌊k*n⌋ ≤ v.1 ∧ v.1 ≤ ⌊k*n⌋ ∧ 0 ≤ v.2 ∧ v.2 ≤ n := by
      simpa only [PottsContinuity.latticeRectangle, Finset.mem_product,
        Finset.mem_Icc, and_assoc] using hv
    exact (mem_topWiredRectangle_iff k ℓ n v).mpr
      ⟨hv'.1, hv'.2.1, hv'.2.2.1, hv'.2.2.2.trans hnH⟩
  have hEvents : {A : Configuration H | embeddedConfigurationRestriction G H f hGH A ∈ E} =
      finiteBoolEvent T (horizontalCrossing T (-⌊k*n⌋) ⌊k*n⌋ 0 n) := by
    ext A
    exact horizontalCrossing_embeddedRestriction_iff S T hST _ _ _ _
      (by omega) (by omega) hRS A
  erw [hEvents] at hcompare
  exact hcompare

/-- Monotonicity in ℓ of the crossing probability in eq. (7) (Lemma 3), with the source
parameter range and the exact crossing probability `selfDualTopWiredCrossingProbability`.
This is unconditional and valid at every scale. -/
theorem top_wired_height_comparison
    (q : Set.Ici (1 : ℝ)) (k : ℝ) (hk : 0 < k)
    (ℓ L : ℝ) (hℓ : 4 / 3 ≤ ℓ) (hL : ℓ ≤ L)
    (n : ℕ) (_hn : 1 ≤ n) :
    selfDualTopWiredCrossingProbability q k L n ≤
      selfDualTopWiredCrossingProbability q k ℓ n :=
  top_wired_height_comparison_parameters (RSW.selfDualParameters q) k ℓ L
    hk.le (by linarith only [hℓ]) hL n

end
end PottsContinuity.Push
