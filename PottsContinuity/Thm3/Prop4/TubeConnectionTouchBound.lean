module

public import PottsContinuity.Thm3.Prop4.CutReferenceArmsTouch

/-!
# A tube-confined connection is bounded by the infinite arm product

Both cuts use the same nonempty interval of central rows. Its endpoints are
unique. The touch and connector cost therefore applies to the exact roots
of the previously proved infinite-volume comparison.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

/-- Endpoints of a nonempty integer interval are determined by its row set. -/
theorem nonempty_integer_interval_endpoints {lo hi lo' hi' : ℤ}
    (h : lo ≤ hi) (h' : lo' ≤ hi') (heq : Finset.Icc lo hi = Finset.Icc lo' hi') :
    lo = lo' ∧ hi = hi' := by
  have hlo : lo ∈ Finset.Icc lo' hi' := heq ▸ Finset.mem_Icc.mpr ⟨le_rfl,h⟩
  have hhi : hi ∈ Finset.Icc lo' hi' := heq ▸ Finset.mem_Icc.mpr ⟨h,le_rfl⟩
  have hlo' : lo' ∈ Finset.Icc lo hi := heq.symm ▸ Finset.mem_Icc.mpr ⟨le_rfl,h'⟩
  have hhi' : hi' ∈ Finset.Icc lo hi := heq.symm ▸ Finset.mem_Icc.mpr ⟨h',le_rfl⟩
  simp only [Finset.mem_Icc] at hlo hhi hlo' hhi'
  omega

/-- At the explicit self-dual parameter, the literal tube connection times
its squared touch factor and both closing costs is bounded by a_n a_(n-1). -/
theorem tube_connection_arm_product_lower_of_touch (q : Set.Ici (1 : ℝ))
    {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (hr : 2 ≤ r)
    (a b : (box n : Set LatticeVertex))
    (ha : a.val.1 = -(n : ℤ)) (hb : b.val.1 = n)
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    Real.exp (-(2*tubeClosingCoefficient (RSW.selfDualParameters q))*r) *
      (1/(20*((4*n+2 : ℕ) : ℝ)^2*((4*n+2 : ℕ) : ℝ)^2))^2 *
      (measure (squareLattice.induce (box n : Set LatticeVertex)) (RSW.selfDualParameters q)
        (BoundaryCondition.free ∅) {A | ∃ p : (openGraph _ A).Walk a b,
          ∀ z ∈ p.support, z.val ∈ radiusTube n r a.val b.val}).toReal ≤
      RSW.oneArmProbability μ n * RSW.oneArmProbability μ (n-1) := by
  obtain ⟨t,c,ht,hat,hbt⟩ := inductionTube_supporting_line hn a.val b.val a.property b.property ha hb
  obtain ⟨lo,hi,hlohi,hrows,hcompare⟩ := tube_reference_probability_le_infinite_arm_product
    (RSW.selfDualParameters q) hn r hr a b ha hb (fun _ => True) (fun _ => True) μ hμ
  obtain ⟨lo',hi',hlohi',hrows',harms⟩ := cut_reference_arms_lower_of_touch q hn r hr
    a.val b.val a.property b.property ha hb t c ht hat hbt hTouch
  obtain ⟨heLo,heHi⟩ := nonempty_integer_interval_endpoints hlohi hlohi' (hrows.symm.trans hrows')
  rw [← heLo,← heHi] at harms
  have hexp : Real.exp (-(2*tubeClosingCoefficient (RSW.selfDualParameters q))*r) =
      Real.exp (-tubeClosingCoefficient (RSW.selfDualParameters q)*r)*
      Real.exp (-tubeClosingCoefficient (RSW.selfDualParameters q)*r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  rw [mul_assoc (Real.exp (-tubeClosingCoefficient (RSW.selfDualParameters q)*r))
    (Real.exp (-tubeClosingCoefficient (RSW.selfDualParameters q)*r))]
  apply le_trans _ hcompare
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left harms (Real.exp_pos _).le) ENNReal.toReal_nonneg

end
end PottsContinuity.Thm3.Prop4
