module

public import PottsContinuity.Thm3.RSW.TiltedReducedWindowRead
public import PottsContinuity.Thm3.RSW.TiltedReducedFiniteSandwich

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.Duality DualityExt Thm3.Prop4
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- A crossed native edge, dualized and half-turned, is the unchanged core edge. -/
theorem tiltedReducedCoreDualEdge_eq_embedding
    (N L M : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hM : L+N+3 ≤ M)
    (e : (tiltedWindowReducedGraph N L t).edgeSet) :
    tiltedReducedFiniteDualEdge N M t (tiltedReducedCoreCrossedEdge N L M t ht hM e) =
      embeddedEdgeEmbedding _ _ (tiltedReducedCoreDualEmbedding N L M t hM)
        (tiltedReducedCoreDual_map_le N L M t ht hM) e := by
  apply Subtype.ext
  have hinj : Function.Injective (fun z : RectangleDualVertex
      (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) =>
        tiltedStripReducedDualVertex N t z.val) := by
    intro x y he
    apply Subtype.ext
    have hh := congrArg (tiltedStripReducedDualVertex N t) he
    change tiltedStripReducedDualVertex N t (tiltedStripReducedDualVertex N t x.val) =
      tiltedStripReducedDualVertex N t (tiltedStripReducedDualVertex N t y.val) at hh
    apply Prod.ext
    · have hx := congrArg Prod.fst hh
      dsimp [tiltedStripReducedDualVertex] at hx
      omega
    · have hy := congrArg Prod.snd hh
      dsimp [tiltedStripReducedDualVertex] at hy
      omega
  apply Sym2.map.injective hinj
  rw [tiltedReducedFiniteDualEdge_crossed_pair,tiltedReducedCoreCrossedEdge_sourceBond,
    tiltedStripReducedCrossedBond_involutive N t _,tiltedReducedFiniteSourceBond_pair]
  change Sym2.map Subtype.val e.val =
    Sym2.map (fun z => tiltedStripReducedDualVertex N t z.val)
      (Sym2.map (tiltedReducedCoreDualEmbedding N L M t hM) e.val)
  rw [Sym2.map_map]
  congr 1
  funext z
  exact (tiltedReducedCoreDualEmbedding_replay N L M t hM z).symm

/-- The actual reduced core read is exactly the complementary crossing-bond
read of the native finite source, with no clipping or boundary completion. -/
theorem tiltedReducedCoreRead_dual_source
    (N L M : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hM : L+N+3 ≤ M)
    (b : tiltedStripReducedCarrier N t) (e : (tiltedWindowReducedGraph N L t).edgeSet)
    (hp : Sym2.map Subtype.val e.val = b.val.val.toSym2)
    (C : Configuration (tiltedWindowReducedGraph N M t)) :
    tiltedReducedWindowRead N L t
      (embeddedConfigurationRestriction _ _ (tiltedReducedCoreDualEmbedding N L M t hM)
        (tiltedReducedCoreDual_map_le N L M t ht hM) (tiltedReducedFiniteDualEquiv N M t C)) b =
      tiltedStripReducedDualTransport N t ht (tiltedReducedWindowRead N M t C) b := by
  classical
  let g := tiltedReducedCoreCrossedEdge N L M t ht hM e
  have hb : tiltedReducedFiniteSourceBond N L t e = b.val.val := by
    apply LatticeBond.toSym2_injective
    rw [tiltedReducedFiniteSourceBond_pair,hp]
  have hg : Sym2.map Subtype.val g.val =
      (tiltedStripReducedBondEquiv N t ht b).val.val.toSym2 := by
    rw [tiltedReducedCoreCrossedEdge_pair,hb]
    rfl
  rw [tiltedReducedWindowRead_edge N L t b e hp]
  change _ = !(tiltedReducedWindowRead N M t C (tiltedStripReducedBondEquiv N t ht b))
  rw [tiltedReducedWindowRead_edge N M t _ g hg]
  apply Bool.eq_iff_iff.mpr
  simp only [boolConfigurationEquiv,Equiv.coe_fn_symm_mk,decide_eq_true_eq,
    Bool.not_eq_true',decide_eq_false_iff_not]
  rw [mem_embeddedConfigurationRestriction,← tiltedReducedCoreDualEdge_eq_embedding]
  exact tiltedReducedFiniteDualEquiv_edgeState N M t C g

/-- All-open cylinders on the retained infinite bond labels. -/
def tiltedReducedAllOpen (N : ℕ) (t : ℝ) (A : Finset (tiltedStripReducedCarrier N t)) :
    Set (tiltedStripReducedCarrier N t → Bool) := {ω | ∀ b ∈ A, ω b = true}

/-- The exact finite dual law transfers the core sandwich to the actual
complementary crossed-source read of every supported all-open cylinder. -/
theorem selfDual_tiltedReducedCore_allOpen_sandwich
    (q : Set.Ici (1 : ℝ)) (N L M : ℕ) (hN : 1 ≤ N) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hM : L+N+3 ≤ M)
    (A : Finset (tiltedStripReducedCarrier N t))
    (hA : ∀ b ∈ A, ∃ e : (tiltedWindowReducedGraph N L t).edgeSet,
      Sym2.map Subtype.val e.val = b.val.val.toSym2) :
    (measure (tiltedWindowReducedGraph N L t) (selfDualParameters q)
      (tiltedWindowBoundary N L t 0)
      {C | tiltedReducedWindowRead N L t C ∈ tiltedReducedAllOpen N t A}).toReal ≤
    (measure (squareLattice.induce (tiltedWindow N M t : Set LatticeVertex)) (selfDualParameters q)
      (tiltedWindowBoundary N M t 0)
      {C | tiltedStripReducedDualTransport N t ht
        (tiltedStripReducedRestriction N t (tiltedStripWindowOriginalRead N t M C)) ∈
          tiltedReducedAllOpen N t A}).toReal ∧
    (measure (squareLattice.induce (tiltedWindow N M t : Set LatticeVertex)) (selfDualParameters q)
      (tiltedWindowBoundary N M t 0)
      {C | tiltedStripReducedDualTransport N t ht
        (tiltedStripReducedRestriction N t (tiltedStripWindowOriginalRead N t M C)) ∈
          tiltedReducedAllOpen N t A}).toReal ≤
    (measure (tiltedWindowReducedGraph N L t) (selfDualParameters q)
      (tiltedWindowBoundary N L t 1)
      {C | tiltedReducedWindowRead N L t C ∈ tiltedReducedAllOpen N t A}).toReal := by
  classical
  let S : Set (Configuration (tiltedWindowReducedGraph N L t)) :=
    {C | tiltedReducedWindowRead N L t C ∈ tiltedReducedAllOpen N t A}
  have hS : IsUpperSet S := by
    intro C D hCD hC b hb
    exact Bool.le_iff_imp.mp (tiltedReducedWindowRead_monotone N L t hCD b) (hC b hb)
  have hsand := tiltedReducedFiniteDual_probability_sandwich N L M hN t ht hM
    (selfDualParameters q) S hS
  let T := {C | embeddedConfigurationRestriction _ _ (tiltedReducedCoreDualEmbedding N L M t hM)
    (tiltedReducedCoreDual_map_le N L M t ht hM) C ∈ S}
  have hlaw := congrArg (fun p => p.toMeasure T)
    (selfDual_tiltedWindowReducedDualConfiguration_law q N M t ht)
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hlaw
  have hpre : (tiltedWindowReducedDualConfiguration N M t) ⁻¹' T =
      {C | tiltedStripReducedDualTransport N t ht
        (tiltedStripReducedRestriction N t (tiltedStripWindowOriginalRead N t M C)) ∈
          tiltedReducedAllOpen N t A} := by
    ext C
    change (∀ b ∈ A, tiltedReducedWindowRead N L t
      (embeddedConfigurationRestriction _ _ (tiltedReducedCoreDualEmbedding N L M t hM)
        (tiltedReducedCoreDual_map_le N L M t ht hM)
        (tiltedReducedFiniteDualEquiv N M t (subgraphConfigurationRestriction _ C))) b = true) ↔ _
    have hbits (b) (hb : b ∈ A) := by
      let e := Classical.choose (hA b hb)
      have hp := Classical.choose_spec (hA b hb)
      have he := tiltedReducedCoreRead_dual_source N L M t ht hM b e hp
        (subgraphConfigurationRestriction (edgeRestriction_le _ (tiltedWindowTopTopEdges N M t)) C)
      rw [tiltedReducedWindowRead_restriction] at he
      exact he
    constructor <;> intro h b hb
    · exact (hbits b hb) ▸ h b hb
    · exact (hbits b hb).symm ▸ h b hb
  rw [hpre] at hlaw
  have heq := congrArg ENNReal.toReal hlaw
  exact ⟨hsand.1.trans_eq heq.symm,heq.le.trans hsand.2⟩

end
end PottsContinuity.RSW
