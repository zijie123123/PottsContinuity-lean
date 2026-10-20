module

public import PottsContinuity.PlanarMixed.TiltedHalfHeight.FiniteReadEnergy
public import PottsContinuity.PlanarMixed.TiltedHalfHeight.ColumnEvents
public import PottsContinuity.Thm3.Prop4.TiltedSelfDual

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeight
open MeasureTheory Filter Topology PD.FK Thm3.Prop4
noncomputable section

/-- Every one of finitely many original-edge blocks fails its all-open cylinder. -/
def noOpenBlockCylinder {I : Type*} (blocks : ℕ → Finset I) (k : ℕ) : Set (I→Bool) :=
  {ω | ∀ j<k, ¬ (∀ i∈blocks j, ω i=true)}

/-- A many-block failure is a clopen event on the original product carrier. -/
theorem isClopen_noOpenBlockCylinder {I : Type*} (blocks : ℕ → Finset I) (k : ℕ) :
    IsClopen (noOpenBlockCylinder blocks k) := by
  have hall (F : Finset I) : IsClopen {ω : I→Bool | ∀ i∈F, ω i=true} := by
    have heq : {ω : I→Bool | ∀ i∈F, ω i=true} = ⋂ i∈F, {ω : I→Bool | ω i=true} := by
      ext ω
      simp
    rw [heq]
    exact isClopen_biInter_finset fun i _ =>
      (isClopen_discrete ({true} : Set Bool)).preimage (continuous_apply i)
  have heq : noOpenBlockCylinder blocks k =
      ⋂ j∈Finset.range k, ({ω | ∀ i∈blocks j, ω i=true} : Set (I→Bool))ᶜ := by
    ext ω
    simp [noOpenBlockCylinder]
  rw [heq]
  exact isClopen_biInter_finset fun j _ => (hall (blocks j)).compl

/-- The finite read agrees with every actual embedded original window edge. -/
theorem tiltedWindowStripRead_at (N m : ℕ) (t : ℝ)
    (A : Configuration (squareLattice.induce (tiltedWindow N m t : Set (ℤ×ℤ))))
    (e : (squareLattice.induce (tiltedWindow N m t : Set (ℤ×ℤ))).edgeSet) :
    tiltedPlaneRestriction N t (tiltedWindowPlaneConfiguration N m t A)
        ((tiltedWindowStripEmbedding N m t).mapEdgeSet e) = decide (e∈A) := by
  classical
  have hidx : (tiltedPlaneEmbedding N t).mapEdgeSet
      ((tiltedWindowStripEmbedding N m t).mapEdgeSet e) =
      (tiltedWindowPlaneEmbedding N m t).mapEdgeSet e := by
    apply Subtype.ext
    change Sym2.map Subtype.val ((tiltedWindowStripEmbedding N m t).toEmbedding.sym2Map e.val) =
      Sym2.map Subtype.val e.val
    rw [Function.Embedding.sym2Map_apply,Sym2.map_map]
    rfl
  unfold tiltedPlaneRestriction
  rw [hidx]
  simp only [tiltedWindowPlaneConfiguration,decide_eq_decide]
  constructor
  · intro he
    obtain ⟨g,hg,hge⟩ := Finset.mem_map.mp he
    exact (tiltedWindowPlaneEmbedding N m t).mapEdgeSet.injective hge ▸ hg
  · intro he
    exact Finset.mem_map.mpr ⟨e,he,rfl⟩

/-- The finite-energy product estimate passes to every genuine tilted strip
cylinder limit, uniformly in the slope and in the disjoint block family. -/
theorem tiltedStrip_noOpenBlockCylinder_probability_le (θ : Parameters) (N : ℕ) (t : ℝ)
    (μ : Measure (TiltedConfiguration N t)) (hμ : IsTiltedStripLimit θ N t 0 μ)
    (blocks : ℕ → Finset (tiltedStripGraph N t).edgeSet) (k M : ℕ)
    (hdisjoint : ∀ i j, i<j → Disjoint (blocks i) (blocks j))
    (hcard : ∀ j<k, (blocks j).card≤M) :
    μ.real (noOpenBlockCylinder blocks k) ≤ (1-(PD.RCInfinite.openEnergy θ)^M)^k := by
  classical
  obtain ⟨ν,hν,_⟩ := tiltedWindowPlaneProbabilityMeasure_top_existsUnique_limit θ N t
  have hmap : IsTiltedStripLimit θ N t 0 (ν.map (tiltedPlaneRestriction N t)).toMeasure :=
    isTiltedStripLimit_of_plane_tendsto θ N t 0 ν hν
  have heq := isTiltedStripLimit_unique θ N t 0 μ _ hμ hmap
  let E := noOpenBlockCylinder blocks k
  let P := (tiltedPlaneRestriction N t) ⁻¹' E
  have hP : IsClopen P :=
    (isClopen_noOpenBlockCylinder blocks k).preimage (tiltedPlaneRestriction_continuous N t)
  have hconv : Tendsto (fun m =>
      (tiltedWindowPlaneProbabilityMeasure θ N t 0 m).toMeasure.real P)
      atTop (𝓝 (ν.toMeasure.real P)) := by
    have hNN := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν hP
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn,Function.comp_def] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hNN
  have heventual : ∀ᶠ m : ℕ in atTop,
      (tiltedWindowPlaneProbabilityMeasure θ N t 0 m).toMeasure.real P ≤
        (1-(PD.RCInfinite.openEnergy θ)^M)^k := by
    let F := (Finset.range k).biUnion blocks
    filter_upwards [eventually_tiltedWindow_finset_edge_lift N t F] with m hm
    let f := (tiltedWindowStripEmbedding N m t).mapEdgeSet
    have hsupp : ∀ j<k, ∀ i∈blocks j, ∃ e, f e=i := by
      intro j hj i hi
      obtain ⟨e,he⟩ := hm i (Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr hj,hi⟩)
      refine ⟨e,?_⟩
      apply Subtype.ext
      apply Sym2.map.injective Subtype.val_injective
      change Sym2.map Subtype.val ((tiltedWindowStripEmbedding N m t).toEmbedding.sym2Map e.val) =
        Sym2.map Subtype.val i.val
      rw [Function.Embedding.sym2Map_apply,Sym2.map_map]
      exact he
    unfold Measure.real
    rw [tiltedWindowPlaneProbabilityMeasure_apply θ N t 0 m P hP.isOpen.measurableSet]
    exact finite_noOpenBlocks_read_probability_le θ (tiltedWindowBoundary N m t 0)
      f (tiltedWindowStripEmbedding N m t).mapEdgeSet.injective
      (fun A => tiltedPlaneRestriction N t (tiltedWindowPlaneConfiguration N m t A))
      (fun A e => by rw [tiltedWindowStripRead_at N m t]; simp only [decide_eq_decide])
      blocks k M hsupp hdisjoint hcard
  have hbound := le_of_tendsto hconv heventual
  rw [heq]
  change (ν.toMeasure.map (tiltedPlaneRestriction N t)).real E ≤ _
  unfold Measure.real
  rw [Measure.map_apply (tiltedPlaneRestriction_continuous N t).measurable
    (isClopen_noOpenBlockCylinder blocks k).isOpen.measurableSet]
  exact hbound

/-- The cost of opening a whole column, with a uniform original-edge budget. -/
def openColumnCost (q : Set.Ici (1 : ℝ)) (N : ℕ) : ℝ :=
  (PD.RCInfinite.openEnergy (RSW.selfDualParameters q))^(N+1)

theorem openColumnCost_pos (q : Set.Ici (1 : ℝ)) (N : ℕ) : 0<openColumnCost q N :=
  pow_pos (PD.RCInfinite.openEnergy_pos _) _

theorem openColumnCost_lt_one (q : Set.Ici (1 : ℝ)) (N : ℕ) : openColumnCost q N<1 := by
  exact pow_lt_one₀ (PD.RCInfinite.openEnergy_pos _).le (openEnergy_lt_one _) (by omega)

/-- Many actual tilted-strip columns fail to be fully open with an exponential
upper bound, for every real slope and every admissible cluster weight. -/
theorem selfDualTiltedStrip_noOpenColumns_le (q : Set.Ici (1 : ℝ))
    (N : ℕ) (t : ℝ) (a : ℤ) (L : ℕ) :
    (selfDualTiltedStripMeasure q N t).real
      {ω | ∀ j<L, ¬ FullyOpenColumn N t (a+(j:ℤ)) ω} ≤ (1-openColumnCost q N)^L := by
  have hevent : {ω | ∀ j<L, ¬ FullyOpenColumn N t (a+(j:ℤ)) ω} =
      noOpenBlockCylinder (fun j => verticalColumnEdges N t (a+(j:ℤ))) L := by
    ext ω
    simp only [noOpenBlockCylinder,Set.mem_ofPred_eq,fullyOpenColumn_iff_edges]
  rw [hevent]
  exact tiltedStrip_noOpenBlockCylinder_probability_le (RSW.selfDualParameters q) N t
    _ (selfDualTiltedStripMeasure_isLimit q N t) _ L (N+1)
    (fun i j hij => verticalColumnEdges_disjoint N t (by omega))
    (fun j _ => verticalColumnEdges_card_le N t (a+(j:ℤ)))

end
end PottsContinuity.PlanarMixed.TiltedHalfHeight
