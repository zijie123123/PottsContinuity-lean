module

public import PottsContinuity.Thm3.Prop4.UniformStrictInteriorTube
public import PottsContinuity.Thm3.Prop4.UniformConfinedTube

/-!
# A strict affine core crossing in the actual finite wired box

A smaller fractional tube supplies the crossing. Its support has a full
one-bond margin inside the larger affine band, uniformly over endpoints
and every real cluster weight at least one.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Original sampled crossing with both the tube and strict affine margin
retained on every support vertex of its actual open walk. -/
def inducedStrictInteriorTubeCrossingEvent (S : Finset LatticeVertex) (n : ℕ)
    (R : ℝ) (u v : LatticeVertex) (t b : ℝ) : Set (Configuration (finiteLatticeGraph S)) :=
  {A | ∃ a c : (S : Set LatticeVertex), a.val.1 = -(n : ℤ) ∧ c.val.1 = n ∧
    ∃ p : (openGraph _ A).Walk a c, ∀ z ∈ p.support,
      z.val ∈ radiusTube n R u v ∧ |(z.val.2 : ℝ)-(t*z.val.1+b)| < R-1}

/-- The actual smaller-tube walk already satisfies the larger strict core,
regardless of the ambient sampled finite domain. -/
theorem smaller_induced_tube_crossing_subset_strict_core (S : Finset LatticeVertex)
    (n : ℕ) (ε : ℝ) (u v : LatticeVertex) (t b : ℝ) (ht : |t| ≤ 1)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (hgap : 8*(n : ℝ)^(ε/2) ≤ 4*(n : ℝ)^ε-1) :
    inducedTubeConfinedCrossingEvent S n (4*(n : ℝ)^(ε/2)) u v ⊆
      inducedStrictInteriorTubeCrossingEvent S n (4*(n : ℝ)^ε) u v t b := by
  rintro A ⟨a,c,ha,hc,p,hp⟩
  refine ⟨a,c,ha,hc,p,?_⟩
  intro z hz
  obtain ⟨hzB,hzd⟩ := (mem_radiusTube n (4*(n : ℝ)^(ε/2)) u v z.val).mp (hp z hz)
  have hheight := tube_vertical_deviation_lt u v z.val t b (4*(n : ℝ)^(ε/2)) ht hu hv hzd
  have hrad : 4*(n : ℝ)^(ε/2) ≤ 4*(n : ℝ)^ε := by
    have hnonneg := Real.rpow_nonneg (Nat.cast_nonneg n) (ε/2)
    linarith only [hgap,hnonneg]
  exact ⟨(mem_radiusTube n (4*(n : ℝ)^ε) u v z.val).mpr ⟨hzB,hzd.trans_le hrad⟩,
    by linarith only [hheight,hgap]⟩

/-- One cutoff gives the strict-core crossing under the actual finite wired
box law, uniformly over all source marks and supporting slopes. -/
theorem selfDual_wired_box_strict_core_uniform_ge_half
    (c₀ α ε : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (q : Set.Ici (1 : ℝ)) (μ₀ : Measure LatticeConfiguration),
      IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ₀ →
      (∀ m : ℕ, 1 ≤ m → RSW.oneArmProbability μ₀ m ≤ Real.exp (-c₀*(m : ℝ)^α)) →
      ∀ n : ℕ, N ≤ n → ∀ u v : LatticeVertex, u ∈ box n → v ∈ box n →
      u.1 = -(n : ℤ) → v.1 = (n : ℤ) →
      ∀ t b : ℝ, |t| ≤ 1 → (u.2 : ℝ) = t*u.1+b → (v.2 : ℝ) = t*v.1+b →
      1/2 ≤ (measure (finiteLatticeGraph (box n)) (RSW.selfDualParameters q)
        (frozenBoundaryCondition (box n) 1)
        (inducedStrictInteriorTubeCrossingEvent (box n) n (4*(n : ℝ)^ε) u v t b)).toReal := by
  obtain ⟨N₀,hN₀,hbulk⟩ := selfDual_wired_containing_domain_confined_crossing_uniform_ge_half
    c₀ α (ε/2) hc₀ hα (by linarith only [hε]) (by linarith only [hε1])
  obtain ⟨N₁,_,hgap⟩ := exists_tube_strict_interior_scale ε hε
  refine ⟨max N₀ N₁,hN₀.trans (le_max_left _ _),?_⟩
  intro q μ₀ hμ₀ hdecay n hn u v huB hvB ha hb t b ht hu hv
  have hsub : radiusTube n (4*(n : ℝ)^(ε/2)) u v ⊆ box n :=
    fun z hz => ((mem_radiusTube n (4*(n : ℝ)^(ε/2)) u v z).mp hz).1
  exact (hbulk q μ₀ hμ₀ hdecay n ((le_max_left _ _).trans hn) u v huB hvB ha hb (box n) hsub).trans
    (measureReal_mono (smaller_induced_tube_crossing_subset_strict_core (box n) n ε u v t b ht hu hv
      (hgap n ((le_max_right _ _).trans hn))) (measure_ne_top _ _))

end
end PottsContinuity.Thm3.Prop4
