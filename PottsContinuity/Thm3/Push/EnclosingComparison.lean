module

public import PottsContinuity.Thm3.Push.EnclosingGeometry
public import PottsContinuity.Thm3.Push.FiniteCrossingClipping

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.RSW PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite MeasureTheory
noncomputable section

/-- An actual crossing of an enclosing domain, at a smaller crossing height,
gives a lower bound for the smaller domain's crossing probability. Domain
wiring is compared only after clipping the path to the target width. -/
theorem top_wired_enclosing_comparison (θ : Parameters) (k ℓ K L : ℝ) (n N : ℕ)
    (hk : 0 ≤ k) (hℓ : 1 ≤ ℓ) (hN : N ≤ n)
    (hw : ⌊k*n⌋ ≤ ⌊K*N⌋) (hh : ⌊ℓ*n⌋ ≤ ⌊L*N⌋) :
    finiteBoundaryEventProbability (topWiredRectangle K L N) θ
      (topWiredRectangleBoundary K L N)
      (horizontalCrossing (topWiredRectangle K L N) (-⌊K*N⌋) ⌊K*N⌋ 0 N) ≤
    finiteBoundaryEventProbability (topWiredRectangle k ℓ n) θ
      (topWiredRectangleBoundary k ℓ n)
      (horizontalCrossing (topWiredRectangle k ℓ n) (-⌊k*n⌋) ⌊k*n⌋ 0 n) := by
  let S := topWiredRectangle k ℓ n
  let T := topWiredRectangle K L N
  let hST := topWiredRectangle_enclosing_subset k ℓ K L n N hw hh
  let f := finiteLatticeVertexEmbedding hST
  let G := finiteLatticeGraph S
  let H := finiteLatticeGraph T
  let hGH := finiteLatticeGraph_map_le hST
  let E := finiteBoolEvent S (horizontalCrossing S (-⌊k*n⌋) ⌊k*n⌋ 0 n)
  have hE : IsUpperSet E :=
    finiteBoolEvent_isUpperSet S _ (horizontalCrossing_isUpperSet S _ _ _ _)
  have hcompare := embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    f hGH θ (topWiredRectangleBoundary K L N)
    (topWiredRectangleBoundary k ℓ n).boundary
    (fun _ hx _ hxy => topWiredEnclosing_neighbor_closed k ℓ K L n N hw hh hx hxy)
    (fun _ hx => topWiredEnclosing_boundary_avoid k ℓ K L n N hw hh hx) E hE
  have hwidth : 0 ≤ ⌊k*n⌋ := Int.floor_nonneg.mpr (mul_nonneg hk (Nat.cast_nonneg n))
  have hheight : (n : ℤ) ≤ ⌊ℓ*n⌋ := by
    apply Int.le_floor.mpr
    push_cast
    nlinarith only [hℓ, Nat.cast_nonneg (α := ℝ) n]
  have hRS : PD.FK.latticeRectangle (-⌊k*n⌋, 0)
      (⌊k*n⌋ - -⌊k*n⌋).toNat ((n : ℤ)-0).toNat ⊆ S := by
    rw [Foundations.pdRectangle_eq_frozenRectangle_of_corners _ _ _ _ (by omega) (by omega)]
    intro z hz
    have hz' : -⌊k*n⌋ ≤ z.1 ∧ z.1 ≤ ⌊k*n⌋ ∧ 0 ≤ z.2 ∧ z.2 ≤ n := by
      simpa only [PottsContinuity.latticeRectangle, Finset.mem_product,
        Finset.mem_Icc, and_assoc] using hz
    exact (mem_topWiredRectangle_iff k ℓ n z).mpr
      ⟨hz'.1, hz'.2.1, hz'.2.2.1, hz'.2.2.2.trans hheight⟩
  apply le_trans _ hcompare
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro A hA
  apply (horizontalCrossing_embeddedRestriction_iff S T hST _ _ _ _
    (by omega) (by omega) hRS A).mpr
  exact horizontalCrossing_clip T ((boolConfigurationEquiv H).symm A)
    _ _ _ _ _ _ _ _ (by omega) (by omega) hw le_rfl (by exact_mod_cast hN) hA

end
end PottsContinuity.Push
