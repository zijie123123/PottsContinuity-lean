-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxPairedCandidateComparison.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedCandidateComponent
public import PottsContinuity.FKC.FiniteFK.EmbeddedReferenceToRemainingComparison
public import PottsContinuity.FKC.FiniteFK.SlitBoxOpenCandidateFrozenWiring
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateReflection
public import PottsContinuity.FKC.FiniteFK.RemainingComparison
public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedCandidateRestoration
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial
open MeasureTheory

noncomputable section

private theorem slitBoxPairedCandidate_component_map_le_deleted
    (n : ℕ) (R : Configuration (slitBoxGraph n))
    (o : SlitBoxVertex n) :
    (edgeRestrictionReachableComponentGraph (slitBoxGraph n) R o).map
      (edgeRestrictionReachableComponentEmbedding (slitBoxGraph n) R o) ≤
        edgeRestriction (slitBoxGraph n) R := by
  intro a b hab
  obtain ⟨x, y, hxy, rfl, rfl⟩ :=
    (SimpleGraph.map_adj
      (edgeRestrictionReachableComponentEmbedding (slitBoxGraph n) R o)
      (edgeRestrictionReachableComponentGraph (slitBoxGraph n) R o) a b).mp hab
  exact SimpleGraph.induce_adj.mp hxy

private theorem slitBoxPairedCandidate_embedded_connection_mono
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {K : SimpleGraph W} (f : V ↪ W)
    (hGK : G.map f ≤ K) (A : Configuration K) {x y : V}
    (hconn : ActualConnected G
      (embeddedConfigurationRestriction G K f hGK A) x y) :
    ActualConnected K A (f x) (f y) := by
  let C : Configuration G := embeddedConfigurationRestriction G K f hGK A
  let I : Configuration K := embeddedConfigurationEmbedding G K f hGK C
  have hsub : I ⊆ A := embeddedConfigurationEmbedding_restriction_subset G K f hGK A
  let hhom : openGraph G C →g openGraph K A := {
    toFun := f
    map_rel' := by
      intro a b hab
      rcases (openGraph_adj G C a b).mp hab with ⟨e, he, heval⟩
      have hGadj : G.Adj a b := G.mem_edgeSet.mp (heval ▸ e.property)
      have hmapAdj : (G.map f).Adj (f a) (f b) :=
        (SimpleGraph.map_adj f G (f a) (f b)).mpr ⟨a, b, hGadj, rfl, rfl⟩
      have hKadj : K.Adj (f a) (f b) := hGK hmapAdj
      let eK : K.edgeSet := ⟨s(f a, f b), K.mem_edgeSet.mpr hKadj⟩
      have heI : embeddedEdgeEmbedding G K f hGK e ∈ I := by
        change embeddedEdgeEmbedding G K f hGK e ∈
          embeddedConfigurationEmbedding G K f hGK C
        rw [embeddedConfigurationEmbedding_eq_map]
        exact Finset.mem_map.mpr ⟨e, he, rfl⟩
      have heA : embeddedEdgeEmbedding G K f hGK e ∈ A := hsub heI
      rw [openGraph_adj]
      refine ⟨eK, ?_, ?_⟩
      · have hevalMap : (embeddedEdgeEmbedding G K f hGK e).val = s(f a, f b) := by
          rw [embeddedEdgeEmbedding_coe, heval]
          simp
        have heq : embeddedEdgeEmbedding G K f hGK e = eK := Subtype.ext hevalMap
        simpa [heq] using heA
      · rfl
  }
  change (openGraph G C).Reachable x y at hconn
  change (openGraph K A).Reachable (f x) (f y)
  have hhom_val (z : V) : hhom z = f z := rfl
  have hmapped := SimpleGraph.Reachable.map hhom hconn
  rw [hhom_val, hhom_val] at hmapped
  exact hmapped

private theorem slitBoxPairedCandidate_wired_subset_frozen
    (n : ℕ) (u v : SlitBoxVertex n)
    (p : SlitBoxFirstHitBaseCandidates n u)
    (q : SlitBoxFirstHitBaseCandidates n v)
    (K : Configuration (slitBoxGraph n))
    (hp : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ K)
    (hq : slitBoxCandidateOriginalPathEdgeSupport n v q ⊆ K) :
    (BoundaryCondition.wired (slitBoxCandidateWiredSupportSet n u p v q)).partition ≤
      (frozenBoundary (slitBoxBoundary n) K).partition := by
  exact slitBoxOpenCandidates_frozen_partition_dominates_wired_supports
    n u v p q K hp hq

/-- For an actual paired candidate whose two retained paths are open in the
same frozen configuration, the reference-square connection event is bounded
by the actual deleted-graph probability of reaching either retained path or
the wired slit arc. The only geometric exclusions are the two stated
bottom-center path-avoidance conditions. -/
theorem slitBoxPairedCandidate_reference_le_deleted_exception_connection
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 < u.val.1)
    (δ : PositiveMesh) (p qCandidate : SlitBoxFirstHitBaseCandidates n u)
    (hcenterP : slitBoxBottomCenterVertex n ∉
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support)
    (hcenterQ : slitBoxBottomCenterVertex n ∉
      (qCandidate.val.2 : (slitBoxGraph n).Walk u qCandidate.val.1).support)
    (Kfrozen : Configuration (slitBoxGraph n))
    (hpOpen : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ Kfrozen)
    (hqOpen : configurationIso (slitBoxGraphHorizontalReflectionIso n)
      (slitBoxCandidateOriginalPathEdgeSupport n u qCandidate) ⊆ Kfrozen)
    (q : ClusterWeight) :
    (measure (slitBoxReferenceGraph n) q
      (BoundaryCondition.wired (slitBoxReferenceOuterWiredSet n))
      (slitBoxReferenceBottomConnectionEvent n)).toReal ≤
    (measure (edgeRestriction (slitBoxGraph n)
      (slitBoxPairedCandidateReveal n hn u huY huX δ p qCandidate)) q
      (frozenBoundary (slitBoxBoundary n) Kfrozen)
      {A | ∃ y ∈ slitBoxPairedCandidateException n u p qCandidate,
        ActualConnected (edgeRestriction (slitBoxGraph n)
          (slitBoxPairedCandidateReveal n hn u huY huX δ p qCandidate)) A
          (slitBoxBottomCenterVertex n) y}).toReal := by
  classical
  let R := slitBoxPairedCandidateReveal n hn u huY huX δ p qCandidate
  let o := slitBoxBottomCenterVertex n
  let σ := slitBoxGraphHorizontalReflectionIso n
  let qRef := slitBoxReflectCandidate n u qCandidate
  let C := edgeRestrictionReachableComponentCarrier (slitBoxGraph n) R o
  let G := edgeRestrictionReachableComponentGraph (slitBoxGraph n) R o
  let f := edgeRestrictionReachableComponentEmbedding (slitBoxGraph n) R o
  let Kdel := edgeRestriction (slitBoxGraph n) R
  let B : Set C := {x | x.val ∈ slitBoxPairedCandidateException n u p qCandidate}
  let ξ : BoundaryCondition (SlitBoxVertex n) :=
    BoundaryCondition.wired (slitBoxReferenceOuterWiredSet n)
  let η : BoundaryCondition (SlitBoxVertex n) := frozenBoundary (slitBoxBoundary n) Kfrozen
  let x0 : C := ⟨o, by
    change (edgeRestriction (slitBoxGraph n) R).Reachable o o
    exact SimpleGraph.Reachable.refl _⟩
  have hmapH : G.map f ≤ slitBoxReferenceGraph n := by
    change (edgeRestrictionReachableComponentGraph (slitBoxGraph n) R o).map
      (edgeRestrictionReachableComponentEmbedding (slitBoxGraph n) R o) ≤ _
    exact slitBoxPairedCandidateComponent_map_le_reference n hn u huY huX δ p qCandidate
  have hmapK : G.map f ≤ Kdel := by
    simpa [G, f, Kdel, R, o] using
      slitBoxPairedCandidate_component_map_le_deleted n R o
  have hxB : x0 ∉ B := by
    have hfix : σ o = o := by
      apply Subtype.ext
      change (slitBoxReflectVertex n o).val = o.val
      rw [slitBoxReflectVertex_apply_val, slitBoxBottomCenterVertex_val]
      rfl
    change o ∉ slitBoxPairedCandidateException n u p qCandidate
    intro h
    rcases h with hp | hrest
    · exact hcenterP hp
    · rcases hrest with hq | harc
      · rw [hfix] at hq
        exact hcenterQ hq
      · exact slitBoxBottomCenterVertex_off_arc n hn harc
  have hclosed : ∀ ⦃v : C⦄, v ∉ B → ∀ ⦃z : SlitBoxVertex n⦄,
      (slitBoxReferenceGraph n).Adj (f v) z →
        ∃ w : C, f w = z ∧ G.Adj v w := by
    intro v hv z hz
    obtain ⟨w, hw, hadj⟩ :=
      slitBoxPairedCandidateComponent_closed_under_reference_neighbors
        n hn u huY huX δ p qCandidate hcenterP hcenterQ hv hz
    change w.val = z at hw
    exact ⟨w, hw, by simpa [G] using hadj⟩
  have havoid : ∀ ⦃v : C⦄, v ∉ B → f v ∉ ξ.boundary := by
    intro v hv
    have h := slitBoxPairedCandidateComponent_avoids_reference_outer_wired_set
      n hn u huY huX δ p qCandidate hcenterP hcenterQ v hv
    change v.val ∉ slitBoxReferenceOuterWiredSet n at h
    exact h
  have hBsupport : ∀ x : C, x ∈ B →
      f x ∈ slitBoxCandidateWiredSupportSet n u p (slitBoxReflectVertex n u) qRef := by
    intro x hx
    change x.val ∈ slitBoxPairedCandidateException n u p qCandidate at hx
    rcases hx with hp | hrest
    · exact Or.inl hp
    · rcases hrest with hq | harc
      · right; left
        change σ x.val ∈ finiteSimplePathSupport qCandidate.val at hq
        change x.val ∈ finiteSimplePathSupport qRef.val
        rw [slitBoxReflectCandidate_orderedSupport]
        apply List.mem_map.mpr
        exact ⟨σ x.val, hq, by
          have hσ := slitBoxReflectVertex_involutive n x.val
          simpa [σ, slitBoxReflectVertex] using hσ⟩
      · exact Or.inr (Or.inr harc)
  have hpart : (BoundaryCondition.wired B).partition ≤
      (isolatedExtensionPullbackBoundary f η).partition := by
    intro x y hxy
    rcases (BoundaryCondition.wired_rel _ _ _).mp hxy with hEq | ⟨hx, hy⟩
    · subst y
      exact (isolatedExtensionPullbackBoundary f η).partition.iseqv.refl x
    · change η.partition.r (f x) (f y)
      have hqRef : slitBoxCandidateOriginalPathEdgeSupport n (slitBoxReflectVertex n u)
          qRef ⊆ Kfrozen := by
        intro e he
        rw [← slitBoxReflectCandidate_edgeSupport n u qCandidate] at he
        exact hqOpen he
      have hdom := slitBoxPairedCandidate_wired_subset_frozen
        n u (slitBoxReflectVertex n u) p qRef Kfrozen hpOpen hqRef
      have hsrel := (BoundaryCondition.wired_rel _ _ _).2
        (Or.inr ⟨hBsupport x hx, hBsupport y hy⟩)
      exact hdom hsrel
  have hcmp := embedded_reference_connection_probability_le_remaining
    f hmapH hmapK q ξ η B x0
    hxB hclosed havoid hpart
  have hsubset :
      {A : Configuration Kdel | ∃ y ∈ B,
        ActualConnected G (embeddedConfigurationRestriction G Kdel f hmapK A) x0 y} ⊆
      {A : Configuration Kdel | ∃ y ∈ slitBoxPairedCandidateException n u p qCandidate,
        ActualConnected Kdel A o y} := by
    intro A hA
    obtain ⟨y, hyB, hconn⟩ := hA
    exact ⟨y.val, by simpa [B] using hyB,
      slitBoxPairedCandidate_embedded_connection_mono f hmapK A hconn⟩
  have hmeasure :
      (measure Kdel q η
        {A | ∃ y ∈ B,
          ActualConnected G (embeddedConfigurationRestriction G Kdel f hmapK A) x0 y}).toReal ≤
      (measure Kdel q η
        {A | ∃ y ∈ slitBoxPairedCandidateException n u p qCandidate,
          ActualConnected Kdel A o y}).toReal := by
    exact ENNReal.toReal_mono (measure_ne_top (measure Kdel q η) _)
      (measure_mono hsubset)
  exact hcmp.trans hmeasure

private theorem slitBoxReferenceScale_lower_bound_le_one
    (n : ℕ) (hn : 1 ≤ n) :
    (1 / (20 * (n : ℝ)^4) : ℝ) ≤ 1 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (1 : ℝ) ≤ (n : ℝ)^4 := one_le_pow₀ hnR
  have hden : (1 : ℝ) ≤ 20 * (n : ℝ)^4 := by nlinarith
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 20 * (n : ℝ)^4)).2
  simpa using hden

/-- The source lower bound for the reference square transfers to the actual
frozen paired-candidate law after restoring the revealed edges. If the center
lies on either retained path, restoration gives the arc connection directly;
otherwise the deleted-graph comparison and actual path restoration give the
same bound. -/
theorem slitBoxPairedCandidate_restored_arc_probability_lower_bound
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 < u.val.1)
    (δ : PositiveMesh) (p qCandidate : SlitBoxFirstHitBaseCandidates n u)
    (Kfrozen : Configuration (slitBoxGraph n))
    (hpOpen : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ Kfrozen)
    (hqOpen : configurationIso (slitBoxGraphHorizontalReflectionIso n)
      (slitBoxCandidateOriginalPathEdgeSupport n u qCandidate) ⊆ Kfrozen)
    (q : ClusterWeight) :
    (1 / (20 * (n : ℝ)^4) : ℝ) ≤
      (remainingMeasure (slitBoxGraph n) q (frozenBoundary (slitBoxBoundary n) Kfrozen)
        (slitBoxPairedCandidateReveal n hn u huY huX δ p qCandidate)
        {A | (A.val ∪ Kfrozen) ∈
          slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n)}).toReal := by
  classical
  let R := slitBoxPairedCandidateReveal n hn u huY huX δ p qCandidate
  let η := frozenBoundary (slitBoxBoundary n) Kfrozen
  let E : Set (RemainingConfiguration (slitBoxGraph n) R) :=
    {A | (A.val ∪ Kfrozen) ∈
      slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n)}
  have hcenterPOr : slitBoxBottomCenterVertex n ∈
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support ∨
      slitBoxBottomCenterVertex n ∉
        (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support :=
    em _
  rcases hcenterPOr with hpCenter | hpAvoid
  · have hE : E = Set.univ := by
      ext A
      constructor
      · intro _
        trivial
      · intro _
        let A' := (edgeRestrictionConfigurationEquiv (slitBoxGraph n) R).symm A
        have hrest := slitBoxPairedCandidate_center_path_restores_arc
          n u p qCandidate Kfrozen R A' hpOpen (by
            intro e he
            rw [← slitBoxReflectCandidate_edgeSupport n u qCandidate] at he
            exact hqOpen he) (Or.inl hpCenter)
        have hEq : edgeRestrictionConfigurationEquiv (slitBoxGraph n) R A' = A := by
          exact Equiv.apply_symm_apply _ _
        change ((edgeRestrictionConfigurationEquiv (slitBoxGraph n) R A').val ∪ Kfrozen) ∈
          slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n) at hrest
        rw [hEq] at hrest
        exact hrest
    change (1 / (20 * (n : ℝ)^4) : ℝ) ≤
      (remainingMeasure (slitBoxGraph n) q η R E).toReal
    rw [hE]
    simp only [measure_univ, ENNReal.toReal_one]
    exact slitBoxReferenceScale_lower_bound_le_one n hn
  · by_cases hqCenter : slitBoxGraphHorizontalReflectionIso n
        (slitBoxBottomCenterVertex n) ∈
          (qCandidate.val.2 : (slitBoxGraph n).Walk u qCandidate.val.1).support
    · have hE : E = Set.univ := by
        ext A
        constructor
        · intro _
          trivial
        · intro _
          let A' := (edgeRestrictionConfigurationEquiv (slitBoxGraph n) R).symm A
          have hrest := slitBoxPairedCandidate_center_path_restores_arc
            n u p qCandidate Kfrozen R A' hpOpen (by
                intro e he
                rw [← slitBoxReflectCandidate_edgeSupport n u qCandidate] at he
                exact hqOpen he) (Or.inr hqCenter)
          have hEq : edgeRestrictionConfigurationEquiv (slitBoxGraph n) R A' = A := by
            exact Equiv.apply_symm_apply _ _
          change ((edgeRestrictionConfigurationEquiv (slitBoxGraph n) R A').val ∪ Kfrozen) ∈
            slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n) at hrest
          rw [hEq] at hrest
          exact hrest
      change (1 / (20 * (n : ℝ)^4) : ℝ) ≤
        (remainingMeasure (slitBoxGraph n) q η R E).toReal
      rw [hE]
      simp only [measure_univ, ENNReal.toReal_one]
      exact slitBoxReferenceScale_lower_bound_le_one n hn
    · have hfix : slitBoxGraphHorizontalReflectionIso n
          (slitBoxBottomCenterVertex n) = slitBoxBottomCenterVertex n := by
        apply Subtype.ext
        change (-((slitBoxBottomCenterVertex n).val.1),
          (slitBoxBottomCenterVertex n).val.2) =
            (slitBoxBottomCenterVertex n).val
        simp [slitBoxBottomCenterVertex_val]
      have hqAvoid : slitBoxBottomCenterVertex n ∉
          (qCandidate.val.2 : (slitBoxGraph n).Walk u qCandidate.val.1).support := by
        intro hmem
        exact hqCenter (hfix ▸ hmem)
      have hcompare := slitBoxPairedCandidate_reference_le_deleted_exception_connection
        n hn u huY huX δ p qCandidate hpAvoid hqAvoid Kfrozen hpOpen hqOpen q
      have hreference :=
        PottsContinuity.FKC.Medial.slitBoxReferenceBottomConnection_probability_lower_bound q hn
      have hhitSubset :
          {A : Configuration (edgeRestriction (slitBoxGraph n) R) |
            ∃ y ∈ slitBoxPairedCandidateException n u p qCandidate,
              ActualConnected (edgeRestriction (slitBoxGraph n) R) A
                (slitBoxBottomCenterVertex n) y} ⊆
          (edgeRestrictionConfigurationEquiv (slitBoxGraph n) R) ⁻¹' E := by
        intro A hA
        change ((edgeRestrictionConfigurationEquiv (slitBoxGraph n) R A).val ∪ Kfrozen) ∈
          slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n)
        exact slitBoxPairedCandidate_remaining_hit_restores_arc
          n hn u huY huX δ p qCandidate Kfrozen hpOpen (by
            intro e he
            rw [← slitBoxReflectCandidate_edgeSupport n u qCandidate] at he
            exact hqOpen he) A hA
      have hmeasureHit := ENNReal.toReal_mono
        (measure_ne_top (measure (edgeRestriction (slitBoxGraph n) R) q η) _)
        (measure_mono hhitSubset)
      have hremain := remainingMeasure_eq_edgeRestriction
        (slitBoxGraph n) q η R E
      change (1 / (20 * (n : ℝ)^4) : ℝ) ≤
        (remainingMeasure (slitBoxGraph n) q η R E).toReal
      rw [hremain]
      exact hreference.trans (hcompare.trans hmeasureHit)

end
end PottsContinuity.FKC.FiniteFK
