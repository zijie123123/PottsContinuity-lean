module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.SideReflection
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import PottsContinuity.Thm3.Prop4.FiniteFilterEquiv
public import PottsContinuity.Thm3.Prop4.IsoRawRecordProbability

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open FKC FKC.Medial FKC.FiniteFK
open MeasureTheory
noncomputable section
attribute [local instance] PD.FK.configurationMeasurableSpace PD.FK.remainingConfigurationMeasurableSpace
local instance sideReflectionLawEdgeEq (m : ℕ) : DecidableEq (slitBoxGraph (16*m)).edgeSet := Classical.decEq _

theorem slitSide_law_reflection (m : ℕ) (θ : PD.FK.Parameters) :
    (PD.FK.law (slitBoxGraph (16*m)) θ
      (Thm4.fkcBoundaryToPD (slitBoxBoundary (16*m)))).map (slitSideConfigurationReflection m) =
    PD.FK.law (slitBoxGraph (16*m)) θ
      (Thm4.fkcBoundaryToPD (slitBoxBoundary (16*m))) := by
  unfold slitSideConfigurationReflection
  rw [slitBoxBoundary,Thm4.fkcBoundaryToPD_wired,PD.FK.law_configurationIso_map]
  apply PD.FK.law_eq_of_boundary_partition_eq
  apply Setoid.ext
  intro u v
  let e := slitBoxGraphHorizontalReflectionIso (16*m)
  have hmem (z : SlitBoxVertex (16*m)) : e.symm z ∈ slitBoxWiredArc (16*m) ↔
      z ∈ slitBoxWiredArc (16*m) := by
    rw [mem_slitBoxWiredArc_iff,mem_slitBoxWiredArc_iff]
    change (-z.val.1=0 ∧ 0≤z.val.2 ∧ z.val.2≤(16*m:ℕ)) ↔
      (z.val.1=0 ∧ 0≤z.val.2 ∧ z.val.2≤(16*m:ℕ))
    omega
  change (e.symm u = e.symm v ∨
    e.symm u ∈ slitBoxWiredArc (16*m) ∧ e.symm v ∈ slitBoxWiredArc (16*m)) ↔
    (u=v ∨ u ∈ slitBoxWiredArc (16*m) ∧ v ∈ slitBoxWiredArc (16*m))
  simp only [e.symm.injective.eq_iff,hmem]

theorem slitSide_rightReveal_reflection (m : ℕ) :
    slitSideConfigurationReflection m (Thm4Side.slitRightDualRectangleRevealEdges m) =
      Thm4Side.slitLeftDualRectangleRevealEdges m := by
  classical
  ext e
  obtain ⟨g,rfl⟩ := (PD.FK.configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso (16*m))).surjective e
  rw [slitSideConfigurationReflection,PD.FK.configurationIso,Equiv.finsetCongr_apply,
    Finset.mem_map_equiv,Equiv.symm_apply_apply]
  simp only [Thm4Side.slitRightDualRectangleRevealEdges,Thm4Side.slitLeftDualRectangleRevealEdges,
    Thm4Side.slitRightHalfRevealEdges,Thm4Side.slitLeftHalfRevealEdges,
    Finset.mem_filter,Finset.mem_univ,true_and]
  change (∀ v ∈ g.val, v.val.1 ≤ (m:ℤ)) ∧ ¬ (∀ v ∈ g.val, v.val.1 = (m:ℤ)) ↔
    (∀ v ∈ Sym2.map (slitBoxGraphHorizontalReflectionIso (16*m)) g.val, -(m:ℤ) ≤ v.val.1) ∧
      ¬ (∀ v ∈ Sym2.map (slitBoxGraphHorizontalReflectionIso (16*m)) g.val, v.val.1 = -(m:ℤ))
  have hmap (P : SlitBoxVertex (16*m) → Prop) :
      (∀ v ∈ Sym2.map (slitBoxGraphHorizontalReflectionIso (16*m)) g.val, P v) ↔
        ∀ v ∈ g.val, P (slitBoxGraphHorizontalReflectionIso (16*m) v) := by
    constructor
    · intro h v hv
      exact h _ (Sym2.mem_map.mpr ⟨v,hv,rfl⟩)
    · intro h v hv
      obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
      exact h w hw
  rw [hmap,hmap]
  constructor
  · rintro ⟨h1,h2⟩
    refine ⟨?_,?_⟩
    · intro v hv
      have h := h1 v hv
      change -(m:ℤ) ≤ -v.val.1
      omega
    · intro h
      apply h2
      intro v hv
      have he := h v hv
      change -v.val.1 = -(m:ℤ) at he
      omega
  · rintro ⟨h1,h2⟩
    refine ⟨?_,?_⟩
    · intro v hv
      have h := h1 v hv
      change -(m:ℤ) ≤ -v.val.1 at h
      omega
    · intro h
      apply h2
      intro v hv
      have he := h v hv
      change -v.val.1 = -(m:ℤ)
      omega

local instance sideReflectionGenericEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

theorem fixedRemaining_reconstructed_probability_eq_filtered
    {V : Type*} [Finite V] (G : SimpleGraph V) (θ : PD.FK.Parameters)
    (ξ : PD.FK.BoundaryCondition V) (R : PD.FK.Configuration G)
    (H : PD.FK.RemovedConfiguration G R) (F : Set (PD.FK.Configuration G)) :
    (PD.FK.remainingLaw G θ (PD.FK.frozenBoundary ξ H.val) R).toMeasure
      {D | D.val ∪ H.val ∈ F} =
    ((PD.FK.law G θ ξ).filter (PD.FK.frozenStateEvent R H)
      (PD.FK.frozenStateEvent_support θ ξ R H)).toMeasure F := by
  classical
  let hs := PD.FK.frozenStateEvent_support θ ξ R H
  let ρ := (PD.FK.law G θ ξ).filter (PD.FK.frozenStateEvent R H) hs
  let D : Set (PD.FK.RemainingConfiguration G R) := {D | D.val ∪ H.val ∈ F}
  have hmap := PD.FK.law_filter_frozen_map_remaining θ ξ R H
  have hprob := congrArg (fun p => p.toMeasure D) hmap
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hprob
  rw [← hprob]
  apply PMF.toMeasure_apply_eq_of_inter_support_eq _
    MeasurableSpace.measurableSet_top MeasurableSpace.measurableSet_top
  ext C
  have hiff (hρ : C ∈ ρ.support) :
      (PD.FK.configurationSplitEquiv G R C).1.val ∪ H.val = C := by
    have hstate : C ∩ R = H.val := ((PMF.mem_support_filter_iff hs).mp hρ).1
    have hrestore := (PD.FK.configurationSplitEquiv G R).symm_apply_apply C
    change (PD.FK.configurationSplitEquiv G R C).1.val ∪
      (PD.FK.configurationSplitEquiv G R C).2.val = C at hrestore
    change (PD.FK.configurationSplitEquiv G R C).1.val ∪ (C ∩ R) = C at hrestore
    rwa [hstate] at hrestore
  constructor
  · rintro ⟨hC,hρ⟩
    refine ⟨?_,hρ⟩
    change (PD.FK.configurationSplitEquiv G R C).1.val ∪ H.val ∈ F at hC
    rwa [hiff hρ] at hC
  · rintro ⟨hC,hρ⟩
    refine ⟨?_,hρ⟩
    change (PD.FK.configurationSplitEquiv G R C).1.val ∪ H.val ∈ F
    rwa [hiff hρ]

theorem slitLeftResidualCrossingProbability_reflection
    (q : Set.Icc (1 : ℝ) 4) (m : ℕ) (hm : 1 ≤ m)
    (A : PD.FK.Configuration (slitBoxGraph (16*m))) :
    slitLeftResidualCrossingProbability q m A =
      slitRightResidualCrossingProbability q m (slitSideConfigurationReflection m A) := by
  classical
  let G := slitBoxGraph (16*m)
  let θ := PD.FK.criticalParameters (⟨q,q.2.1⟩ : Set.Ici (1:ℝ))
  let ξ := Thm4.fkcBoundaryToPD (slitBoxBoundary (16*m))
  let σ := slitSideConfigurationReflection m
  let Rl := Thm4Side.slitLeftDualRectangleRevealEdges m
  let Rr := Thm4Side.slitRightDualRectangleRevealEdges m
  let Hl : PD.FK.RemovedConfiguration G Rl := ⟨A ∩ Rl,Finset.inter_subset_right⟩
  let Hr : PD.FK.RemovedConfiguration G Rr := ⟨σ A ∩ Rr,Finset.inter_subset_right⟩
  have hσ : Function.Involutive σ := slitSideConfigurationReflection_involutive m
  have hsymm : σ.symm = σ := by
    apply Equiv.ext
    intro B
    apply σ.injective
    rw [σ.apply_symm_apply,hσ]
  have hcovR : σ Rl = Rr := by
    rw [show Rl = σ Rr from (slitSide_rightReveal_reflection m).symm,hσ]
  have hinter (B C : PD.FK.Configuration G) : σ (B ∩ C) = σ B ∩ σ C :=
    Push.configurationIso_inter (slitBoxGraphHorizontalReflectionIso (16*m)) B C
  have hfiber : σ.symm ⁻¹' PD.FK.frozenStateEvent Rl Hl =
      PD.FK.frozenStateEvent Rr Hr := by
    ext B
    change σ.symm B ∩ Rl = A ∩ Rl ↔ B ∩ Rr = σ A ∩ Rr
    rw [hsymm]
    calc
      σ B ∩ Rl = A ∩ Rl ↔ σ (σ B ∩ Rl) = σ (A ∩ Rl) := σ.injective.eq_iff.symm
      _ ↔ B ∩ Rr = σ A ∩ Rr := by rw [hinter,hinter,hσ,hcovR]
  have hmap := Thm3.Prop4.finite_pmf_filter_map_equiv (PD.FK.law G θ ξ) σ
    (PD.FK.frozenStateEvent Rl Hl) (PD.FK.frozenStateEvent_support θ ξ Rl Hl)
  have hlaw : (PD.FK.law G θ ξ).map σ = PD.FK.law G θ ξ := slitSide_law_reflection m θ
  simp only [hlaw,hfiber] at hmap
  have hpre : σ ⁻¹' slitScreenRightCrossingEvent m = slitScreenLeftCrossingEvent m := by
    ext B
    exact (slitScreenLeftCrossingEvent_reflection_iff m hm B).symm
  have hprob := congrArg (fun p => p.toMeasure (slitScreenRightCrossingEvent m)) hmap
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top,hpre] at hprob
  have hl := fixedRemaining_reconstructed_probability_eq_filtered G θ ξ Rl Hl
    (slitScreenLeftCrossingEvent m)
  have hr := fixedRemaining_reconstructed_probability_eq_filtered G θ ξ Rr Hr
    (slitScreenRightCrossingEvent m)
  change ((PD.FK.remainingLaw G θ (PD.FK.frozenBoundary ξ Hl.val) Rl).toMeasure
      {D | D.val ∪ Hl.val ∈ slitScreenLeftCrossingEvent m}).toReal =
    ((PD.FK.remainingLaw G θ (PD.FK.frozenBoundary ξ Hr.val) Rr).toMeasure
      {D | D.val ∪ Hr.val ∈ slitScreenRightCrossingEvent m}).toReal
  rw [hl,hr]
  exact congrArg ENNReal.toReal hprob

theorem slitScreenSideFactor_of_uniform_right_residual_bound
    (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 4)
    (hbound : ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      ∀ A : PD.FK.Configuration (slitBoxGraph (16*m)),
        c ≤ slitRightResidualCrossingProbability ⟨q,hq⟩ m A) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ m : ℕ, 1 ≤ m →
      c₂^2 * (Thm4Plane.slitScreenFiniteMeasure ⟨q,hq⟩ m).real (Thm4Plane.slitScreenEvent m) ≤
        (Thm4Plane.slitScreenFiniteMeasure ⟨q,hq⟩ m).real
          (Thm4Plane.slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m)) := by
  obtain ⟨c,hc,hb⟩ := hbound
  apply slitScreenSideFactor_of_uniform_residual_bounds q hq
  refine ⟨c,hc,?_⟩
  intro m hm A
  refine ⟨hb m hm A,?_⟩
  rw [slitLeftResidualCrossingProbability_reflection ⟨q,hq⟩ m hm A]
  exact hb m hm _

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
