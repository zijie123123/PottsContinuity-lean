module

public import PottsContinuity.Thm3.Push.SlitBandPocketActiveBound

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance slitBandPocketEmbeddedEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Every finite graph containing the pocket-reduced active band inherits
the mixed crossing bound, with its two actual cut supports wired separately. -/
theorem slit_band_pockets_embedded_active_lower_bound
    (q : Set.Ici (1 : ℝ)) {M : ℕ} {x y : ℤ}
    (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M:ℤ))
    {U : Type*} [Finite U] (G : SimpleGraph U)
    (f : slitBandPocketCarrier D hM hy ↪ U)
    (hmap : (edgeRestriction
      ((rankedBandGraph (graph M x y) (D.rank hM hy)).induce (slitBandPocketCarrier D hM hy))
      (slitBandPocketArcBonds D hM hy)).map f ≤ G)
    (I J : Set U) (hIJ : Disjoint I J)
    (hI : ∀ u : slitBandPocketCarrier D hM hy, u.val.val ∈ D.first.support → f u ∈ I)
    (hJ : ∀ u : slitBandPocketCarrier D hM hy, u.val.val ∈ D.second.support → f u ∈ J) :
    1/(1+(q:ℝ)^2) ≤
      (measure G (criticalParameters q) (twoBlockBoundary I J hIJ)
        (arcsConnectionEvent G I J)).toReal := by
  let H := (rankedBandGraph (graph M x y) (D.rank hM hy)).induce (slitBandPocketCarrier D hM hy)
  let ξ := isolatedExtensionPullbackBoundary (pocketInclusion (slitBandPocketCarrier D hM hy))
    (rankedBandBoundary (D.rank hM hy))
  let A := edgeRestriction H (slitBandPocketArcBonds D hM hy)
  let E := arcsConnectionEvent A {u | D.rank hM hy u.val.val = 1} {u | D.rank hM hy u.val.val = 3}
  have hpart : ξ.partition ≤ (isolatedExtensionPullbackBoundary f (twoBlockBoundary I J hIJ)).partition := by
    intro u v huv
    change (rankedBandBoundary (D.rank hM hy)).partition.r u.val v.val at huv
    change (twoBlockBoundary I J hIJ).partition.r (f u) (f v)
    apply (twoBlockBoundary_partition_rel I J hIJ _ _).mpr
    rcases (twoBlockBoundary_partition_rel _ _ _ u.val v.val).mp huv with heq | ha | hb
    · exact Or.inl (congrArg f (Subtype.ext heq))
    · exact Or.inr (Or.inl ⟨hI u ((D.rank_first_iff hM hy u.val.val).mp ha.1),
        hI v ((D.rank_first_iff hM hy v.val.val).mp ha.2)⟩)
    · exact Or.inr (Or.inr ⟨hJ u ((D.rank_second_iff hM hy u.val.val).mp hb.1),
        hJ v ((D.rank_second_iff hM hy v.val.val).mp hb.2)⟩)
  have hb := (slit_band_pockets_active_wiredArc_lower_bound q D hM hy hyM).trans
    (embedded_measure_lower_of_boundary_domination A G f hmap (criticalParameters q)
      (twoBlockBoundary I J hIJ) ξ hpart E (arcsConnectionEvent_isUpperSet _ _))
  apply hb.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  rintro C ⟨u,hu,v,hv,⟨p⟩⟩
  exact ⟨f u,hI u ((D.rank_first_iff hM hy u.val.val).mp hu),
    f v,hJ v ((D.rank_second_iff hM hy v.val.val).mp hv),
    ⟨p.map (embeddedOpenRestrictionHom A G f hmap C)⟩⟩

end
end PottsContinuity.Push
