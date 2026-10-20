module

public import PottsContinuity.Thm3.RSW.TiltedReducedCoreRead
public import PottsContinuity.Thm3.Push.BoolUpperCylinderUniqueness

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial Thm3.Prop4 MeasureTheory Filter Topology
noncomputable section
attribute [local instance] configurationMeasurableSpace

local instance tiltedReducedMarginal_countable (N : ℕ) (t : ℝ) :
    Countable (tiltedStripReducedCarrier N t) := by
  let bondCountable : Countable LatticeBond :=
    (show Function.Injective (fun b : LatticeBond => (b.base,b.axis)) from by
      rintro ⟨b,ax⟩ ⟨c,ay⟩ h
      cases h
      rfl).countable
  unfold tiltedStripReducedCarrier TiltedBond
  infer_instance

/-- The two-stage finite-host/core limit identifies every reduced all-open
cylinder under the genuine complementary crossed transport. -/
theorem selfDual_tiltedStrip_reduced_allOpen_eq
    (q : Set.Ici (1 : ℝ)) (N : ℕ) (hN : 1 ≤ N) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (A : Finset (tiltedStripReducedCarrier N t)) :
    (selfDualTiltedStripMeasure q N t).real
      {ω | tiltedStripReducedDualTransport N t ht (tiltedStripReducedRestriction N t ω) ∈
        tiltedReducedAllOpen N t A} =
    (selfDualTiltedStripMeasure q N t).real
      {ω | tiltedStripReducedRestriction N t ω ∈ tiltedReducedAllOpen N t A} := by
  classical
  let E := tiltedReducedAllOpen N t A
  let μ := selfDualTiltedStripMeasure q N t
  let p := μ.real {ω | tiltedStripReducedRestriction N t ω ∈ E}
  let d := μ.real {ω | tiltedStripReducedDualTransport N t ht
    (tiltedStripReducedRestriction N t ω) ∈ E}
  let f (i : Fin 2) (L : ℕ) :=
    (measure (tiltedWindowReducedGraph N L t) (selfDualParameters q)
      (tiltedWindowBoundary N L t i) {C | tiltedReducedWindowRead N L t C ∈ E}).toReal
  have hE : IsClopen E := Push.boolConstantCylinder_isClopen A true
  have htop (i : Fin 2) (L : ℕ) : (tiltedWindowBoundary N L t 0).partition ≤
      (tiltedWindowBoundary N L t i).partition := by
    intro x y hxy
    rcases hxy with rfl | ⟨hx,hy⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨Or.inl (by simpa [tiltedWindowWiredVertices] using hx),
        Or.inl (by simpa [tiltedWindowWiredVertices] using hy)⟩
  have hlat (i : Fin 2) (L : ℕ) : (tiltedWindowBoundary N L t i).boundary ⊆
      tiltedWindowWiredVertices N L t 1 := by
    intro x hx
    rcases hx with hx | ⟨hi,hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨rfl,hx⟩
  have hf (i : Fin 2) : Tendsto (f i) atTop (𝓝 p) :=
    selfDual_tiltedReducedWindowRead_tendsto q N t ht
      (fun L => tiltedWindowBoundary N L t i) (htop i) (hlat i) E hE
  have hdual := selfDual_tiltedStrip_clopen_tendsto q N t ht
    (fun M => tiltedWindowBoundary N M t 0) (htop 0) (hlat 0)
    {ω | tiltedStripReducedDualTransport N t ht (tiltedStripReducedRestriction N t ω) ∈ E}
    (hE.preimage ((tiltedStripReducedDualTransport_continuous N t ht).comp
      (tiltedStripReducedRestriction_continuous N t)))
  have hsupp : ∀ᶠ L : ℕ in atTop, ∀ b ∈ A,
      ∃ e : (tiltedWindowReducedGraph N L t).edgeSet,
        Sym2.map Subtype.val e.val = b.val.val.toSym2 :=
    (eventually_all_finset A).mpr fun b _ => eventually_tiltedReducedWindow_edge_lift N t b
  let g (M : ℕ) := (measure (squareLattice.induce (tiltedWindow N M t : Set LatticeVertex))
    (selfDualParameters q) (tiltedWindowBoundary N M t 0)
    {C | tiltedStripReducedDualTransport N t ht
      (tiltedStripReducedRestriction N t (tiltedStripWindowOriginalRead N t M C)) ∈ E}).toReal
  change Tendsto g atTop (𝓝 d) at hdual
  have hbounds : ∀ᶠ L : ℕ in atTop, f 0 L ≤ d ∧ d ≤ f 1 L := by
    filter_upwards [hsupp] with L hL
    have hs : ∀ᶠ M : ℕ in atTop, f 0 L ≤ g M ∧ g M ≤ f 1 L := by
      filter_upwards [eventually_ge_atTop (L+N+3)] with M hM
      exact selfDual_tiltedReducedCore_allOpen_sandwich q N L M hN t ht hM A hL
    exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hdual (hs.mono fun _ h => h.1),
      le_of_tendsto_of_tendsto hdual tendsto_const_nhds (hs.mono fun _ h => h.2)⟩
  exact le_antisymm
    (le_of_tendsto_of_tendsto tendsto_const_nhds (hf 1) (hbounds.mono fun _ h => h.2))
    (le_of_tendsto_of_tendsto (hf 0) tendsto_const_nhds (hbounds.mono fun _ h => h.1))

/-- The canonical tilted-strip law is invariant under the genuine
complementary crossed half-turn on all bonds except intrinsic top-top bonds.
The digital staircase phase is retained for every slope in the stated range. -/
theorem selfDual_tiltedStrip_reflected_marginal
    (q : Set.Ici (1 : ℝ)) (N : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    Measure.map (tiltedStripReducedDualTransport N t ht)
      (Measure.map (tiltedStripReducedRestriction N t) (selfDualTiltedStripMeasure q N t)) =
      Measure.map (tiltedStripReducedRestriction N t) (selfDualTiltedStripMeasure q N t) := by
  by_cases hN : 1 ≤ N
  · apply Push.finite_bool_measure_eq_of_upper_cylinders
    intro A
    have hE : MeasurableSet (tiltedReducedAllOpen N t A) :=
      (Push.boolConstantCylinder_isClopen A true).isOpen.measurableSet
    have hpre : MeasurableSet ((tiltedStripReducedDualTransport N t ht) ⁻¹'
        tiltedReducedAllOpen N t A) :=
      (tiltedStripReducedDualTransport_continuous N t ht).measurable hE
    change (Measure.map (tiltedStripReducedDualTransport N t ht)
      (Measure.map (tiltedStripReducedRestriction N t) (selfDualTiltedStripMeasure q N t))).real
        (tiltedReducedAllOpen N t A) =
      (Measure.map (tiltedStripReducedRestriction N t) (selfDualTiltedStripMeasure q N t)).real
        (tiltedReducedAllOpen N t A)
    unfold Measure.real
    rw [Measure.map_apply (tiltedStripReducedDualTransport_continuous N t ht).measurable hE,
      Measure.map_apply (tiltedStripReducedRestriction_continuous N t).measurable hpre,
      Measure.map_apply (tiltedStripReducedRestriction_continuous N t).measurable hE]
    exact selfDual_tiltedStrip_reduced_allOpen_eq q N hN t ht A
  · have hz : N = 0 := by omega
    subst N
    exact selfDual_tiltedStrip_reflected_marginal_zero_height q t ht

end
end PottsContinuity.RSW
