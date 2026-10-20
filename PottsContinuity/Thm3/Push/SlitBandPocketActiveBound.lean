module

public import PottsContinuity.Thm3.Push.SlitBandPocketCrossing
public import PottsContinuity.PlanarMixed.EmbeddedBoundaryLower
public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutBand
public import PottsContinuity.PlanarMixed.EmbeddedOpenRestriction
public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutActive
public import PottsContinuity.PlanarMixed.CutExteriorReveals

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit MeasureTheory
noncomputable section
local instance slitBandPocketActiveEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

/-- The pocket-reduced band with all internal marked-arc bonds deleted. -/
def slitBandPocketArcBonds {M : ℕ} {x y : ℤ}
    (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y) :
    Configuration ((rankedBandGraph (graph M x y) (D.rank hM hy)).induce
      (slitBandPocketCarrier D hM hy)) :=
  internalBonds _ {v | D.rank hM hy v.val.val = 1} ∪
  internalBonds _ {v | D.rank hM hy v.val.val = 3}

/-- Deleting the exposed path bonds preserves the pocket-reduced crossing
bound on the literal remaining graph. -/
theorem slit_band_pockets_active_wiredArc_lower_bound
    (q : Set.Ici (1 : ℝ)) {M : ℕ} {x y : ℤ}
    (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M:ℤ)) :
    let H := (rankedBandGraph (graph M x y) (D.rank hM hy)).induce
      (slitBandPocketCarrier D hM hy)
    let ξ := isolatedExtensionPullbackBoundary (pocketInclusion (slitBandPocketCarrier D hM hy))
      (rankedBandBoundary (D.rank hM hy))
    1/(1+(q:ℝ)^2) ≤
      (measure (edgeRestriction H (slitBandPocketArcBonds D hM hy)) (criticalParameters q) ξ
        (arcsConnectionEvent _ {v | D.rank hM hy v.val.val = 1}
          {v | D.rank hM hy v.val.val = 3})).toReal := by
  classical
  let H := (rankedBandGraph (graph M x y) (D.rank hM hy)).induce
    (slitBandPocketCarrier D hM hy)
  let ξ := isolatedExtensionPullbackBoundary (pocketInclusion (slitBandPocketCarrier D hM hy))
    (rankedBandBoundary (D.rank hM hy))
  let A : Set (slitBandPocketCarrier D hM hy) := {v | D.rank hM hy v.val.val = 1}
  let B : Set (slitBandPocketCarrier D hM hy) := {v | D.rank hM hy v.val.val = 3}
  let R := slitBandPocketArcBonds D hM hy
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro v ha hb
    change D.rank hM hy v.val.val = 1 at ha
    change D.rank hM hy v.val.val = 3 at hb
    omega
  have hcross := slit_crosscuts_cross_seeded_exteriors D hM
  have hA : A.Nonempty := by
    let u := D.firstStartBand hM hy
    exact ⟨⟨u,Or.inr D.first.start_mem_support,hcross.1 D.first.start_mem_support⟩,
      (D.rank_first_iff hM hy D.firstStart).mpr D.first.start_mem_support⟩
  have hB : B.Nonempty := by
    let u := D.secondStartBand hM hy
    exact ⟨⟨u,hcross.2 D.second.start_mem_support,Or.inr D.second.start_mem_support⟩,
      (D.rank_second_iff hM hy D.secondStart).mpr D.second.start_mem_support⟩
  have hξ : (twoBlockBoundary A B hAB).partition ≤ ξ.partition := by
    intro u v huv
    change (rankedBandBoundary (D.rank hM hy)).partition.r u.val v.val
    apply (twoBlockBoundary_partition_rel _ _ _ _ _).mpr
    rcases (twoBlockBoundary_partition_rel A B hAB u v).mp huv with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hR : ∀ (u v : slitBandPocketCarrier D hM hy) (huv : H.Adj u v),
      (⟨s(u,v),H.mem_edgeSet.mpr huv⟩ : H.edgeSet) ∈ R →
        (twoBlockBoundary A B hAB).partition.r u v := by
    intro u v huv he
    apply (twoBlockBoundary_partition_rel A B hAB u v).mpr
    change _ ∈ internalBonds H A ∪ internalBonds H B at he
    rcases Finset.mem_union.mp he with ha | hb
    · exact Or.inr (Or.inl ((mem_internalBonds_pair H A u v huv).mp ha))
    · exact Or.inr (Or.inr ((mem_internalBonds_pair H B u v huv).mp hb))
  have hevent : (edgeRestrictionConfigurationEquiv H R) ⁻¹'
      {ω : RemainingConfiguration H R | ω.val ∈ arcsConnectionEvent H A B} =
      arcsConnectionEvent (edgeRestriction H R) A B := by
    ext C
    change (∃ u ∈ A, ∃ v ∈ B,
      (openGraph H (edgeRestrictionConfigurationEquiv H R C).val).Reachable u v) ↔ _
    rw [← openGraph_edgeRestriction H R C]
    rfl
  have heq := congrArg (fun μ : PMF (RemainingConfiguration H R) => μ.toMeasure
      {ω | ω.val ∈ arcsConnectionEvent H A B}) (law_edgeRestriction_map H (criticalParameters q) ξ R)
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top,
    hevent] at heq
  rw [arcsConnection_remainingLaw_eq H (criticalParameters q) A B hAB hA hB ξ hξ R hR] at heq
  exact (slit_band_pockets_wiredArc_lower_bound q D hM hy hyM).trans_eq
    (congrArg ENNReal.toReal heq.symm)

end
end PottsContinuity.Push
