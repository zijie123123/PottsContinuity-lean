module

public import PottsContinuity.Thm3.RSW.TiltedStripReducedLimit
public import PottsContinuity.Thm3.RSW.TiltedStripFiniteReadEdges
public import PottsContinuity.Thm3.RSW.TiltedReducedActiveGeometry

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial Thm3.Prop4 MeasureTheory Filter Topology
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Closed extension of a native reduced sample to the infinite reduced carrier. -/
def tiltedReducedWindowRead (N M : ℕ) (t : ℝ)
    (C : Configuration (tiltedWindowReducedGraph N M t)) : tiltedStripReducedCarrier N t → Bool :=
  tiltedStripReducedRestriction N t (tiltedStripWindowOriginalRead N t M
    (subgraphConfigurationEmbedding (edgeRestriction_le _ (tiltedWindowTopTopEdges N M t)) C))

/-- A retained native edge is read at its literal physical bond. -/
theorem tiltedReducedWindowRead_edge (N M : ℕ) (t : ℝ)
    (b : tiltedStripReducedCarrier N t) (e : (tiltedWindowReducedGraph N M t).edgeSet)
    (hp : Sym2.map Subtype.val e.val = b.val.val.toSym2)
    (C : Configuration (tiltedWindowReducedGraph N M t)) :
    tiltedReducedWindowRead N M t C b = (boolConfigurationEquiv _).symm C e := by
  classical
  let h := edgeRestriction_le (squareLattice.induce (tiltedWindow N M t : Set LatticeVertex))
    (tiltedWindowTopTopEdges N M t)
  have hf := tiltedStripWindowOriginalRead_edge N t M (tiltedBondEdge N t b.val)
    (subgraphEdgeEmbedding h e) hp (subgraphConfigurationEmbedding h C)
  change tiltedStripWindowOriginalRead N t M (subgraphConfigurationEmbedding h C)
    (tiltedBondEdge N t b.val) = _
  rw [hf]
  simp only [boolConfigurationEquiv,Equiv.coe_fn_symm_mk,subgraphConfigurationEmbedding]
  congr 1
  apply propext
  exact Finset.mem_map' (subgraphEdgeEmbedding h)

/-- Forgetting the top-top states commutes with the original reduced read. -/
theorem tiltedReducedWindowRead_restriction (N M : ℕ) (t : ℝ)
    (C : Configuration (squareLattice.induce (tiltedWindow N M t : Set LatticeVertex))) :
    tiltedReducedWindowRead N M t
      (subgraphConfigurationRestriction (edgeRestriction_le _ (tiltedWindowTopTopEdges N M t)) C) =
      tiltedStripReducedRestriction N t (tiltedStripWindowOriginalRead N t M C) := by
  classical
  funext b
  let h := edgeRestriction_le (squareLattice.induce (tiltedWindow N M t : Set LatticeVertex))
    (tiltedWindowTopTopEdges N M t)
  have hread (A : Configuration (squareLattice.induce (tiltedWindow N M t : Set LatticeVertex))) :
      tiltedStripReducedRestriction N t (tiltedStripWindowOriginalRead N t M A) b =
        decide ((tiltedPlaneEmbedding N t).mapEdgeSet (tiltedBondEdge N t b.val) ∈
          A.map (tiltedWindowPlaneEmbedding N M t).mapEdgeSet) := by
    simp only [tiltedStripReducedRestriction,tiltedStripWindowOriginalRead,tiltedPlaneRestriction,
      tiltedWindowPlaneConfiguration,decide_eq_decide]
    rfl
  rw [tiltedReducedWindowRead,hread,hread]
  congr 1
  apply propext
  constructor
  · intro he
    obtain ⟨f,hf,hfe⟩ := Finset.mem_map.mp he
    obtain ⟨g,hg,hgf⟩ := Finset.mem_map.mp hf
    have hg' := (mem_subgraphConfigurationRestriction h C g).mp hg
    have hf' : f ∈ C := hgf ▸ hg'
    exact Finset.mem_map.mpr ⟨f,hf',hfe⟩
  · intro he
    obtain ⟨f,hf,hfe⟩ := Finset.mem_map.mp he
    have hpair : Sym2.map Subtype.val f.val = b.val.val.toSym2 := congrArg Subtype.val hfe
    have hnot : f ∉ tiltedWindowTopTopEdges N M t := by
      intro htop
      have htop' : ∀ z ∈ f.val, tiltedTop N t z.val := by
        simpa only [tiltedWindowTopTopEdges,Finset.mem_filter,Finset.mem_univ,true_and] using htop
      have hall : ∀ z ∈ b.val.val.toSym2, tiltedTop N t z := by
        intro z hz
        rw [← hpair] at hz
        obtain ⟨w,hw,hwz⟩ := Sym2.mem_map.mp hz
        exact hwz ▸ htop' w hw
      exact b.property ⟨hall _ (by simp [LatticeBond.toSym2]),hall _ (by simp [LatticeBond.toSym2])⟩
    let e := (edgeRestrictionEdgeEquiv _ (tiltedWindowTopTopEdges N M t)).symm ⟨f,hnot⟩
    have hemb : subgraphEdgeEmbedding h e = f := rfl
    have heC : e ∈ subgraphConfigurationRestriction h C := by
      rw [mem_subgraphConfigurationRestriction,hemb]
      exact hf
    have hfC : f ∈ subgraphConfigurationEmbedding h (subgraphConfigurationRestriction h C) :=
      Finset.mem_map.mpr ⟨e,heC,hemb⟩
    exact Finset.mem_map.mpr ⟨f,hfC,hfe⟩

/-- The reduced closed extension preserves increasing states. -/
theorem tiltedReducedWindowRead_monotone (N M : ℕ) (t : ℝ) :
    Monotone (tiltedReducedWindowRead N M t) := by
  intro A B hAB b
  exact tiltedWindowPlaneConfiguration_mono N M t
    (Finset.map_subset_map.mpr hAB) _

/-- Clopen events of the reduced original bonds have the canonical strip limit. -/
theorem selfDual_tiltedReducedWindowRead_tendsto
    (q : Set.Ici (1 : ℝ)) (N : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (ξ : ∀ M : ℕ, BoundaryCondition (tiltedWindow N M t : Set LatticeVertex))
    (htop : ∀ M, (tiltedWindowBoundary N M t 0).partition ≤ (ξ M).partition)
    (hlateral : ∀ M, (ξ M).boundary ⊆ tiltedWindowWiredVertices N M t 1)
    (E : Set (tiltedStripReducedCarrier N t → Bool)) (hE : IsClopen E) :
    Tendsto (fun M => (measure (tiltedWindowReducedGraph N M t) (selfDualParameters q) (ξ M)
      {C | tiltedReducedWindowRead N M t C ∈ E}).toReal) atTop
      (𝓝 ((selfDualTiltedStripMeasure q N t).real
        ((tiltedStripReducedRestriction N t) ⁻¹' E))) := by
  have hconv := selfDual_tiltedStrip_clopen_tendsto q N t ht ξ htop hlateral
    ((tiltedStripReducedRestriction N t) ⁻¹' E)
    (hE.preimage (tiltedStripReducedRestriction_continuous N t))
  have hmass (M : ℕ) :
      measure (tiltedWindowReducedGraph N M t) (selfDualParameters q) (ξ M)
        {C | tiltedReducedWindowRead N M t C ∈ E} =
      measure (squareLattice.induce (tiltedWindow N M t : Set LatticeVertex))
        (selfDualParameters q) (ξ M)
        {C | tiltedStripReducedRestriction N t (tiltedStripWindowOriginalRead N t M C) ∈ E} := by
    have h := congrArg (fun p => p.toMeasure {C | tiltedReducedWindowRead N M t C ∈ E})
      (tiltedWindowReducedGraph_law N M t (selfDualParameters q) (ξ M) (htop M))
    rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at h
    have hpre : (subgraphConfigurationRestriction
        (edgeRestriction_le _ (tiltedWindowTopTopEdges N M t))) ⁻¹'
        {C | tiltedReducedWindowRead N M t C ∈ E} =
        {C | tiltedStripReducedRestriction N t (tiltedStripWindowOriginalRead N t M C) ∈ E} := by
      ext C
      change tiltedReducedWindowRead N M t (subgraphConfigurationRestriction _ C) ∈ E ↔ _
      rw [tiltedReducedWindowRead_restriction]
      rfl
    rw [hpre] at h
    exact h.symm
  simpa only [hmass,Set.mem_preimage] using hconv

/-- Every retained infinite bond eventually has a literal native reduced lift. -/
theorem eventually_tiltedReducedWindow_edge_lift (N : ℕ) (t : ℝ)
    (b : tiltedStripReducedCarrier N t) :
    ∀ᶠ M : ℕ in atTop, ∃ e : (tiltedWindowReducedGraph N M t).edgeSet,
      Sym2.map Subtype.val e.val = b.val.val.toSym2 := by
  classical
  filter_upwards [eventually_tiltedWindow_edge_lift N t (tiltedBondEdge N t b.val)] with M hM
  obtain ⟨f,hf⟩ := hM
  have hpair : Sym2.map Subtype.val f.val = b.val.val.toSym2 := hf
  have hnot : f ∉ tiltedWindowTopTopEdges N M t := by
    intro htop
    have htop' : ∀ z ∈ f.val, tiltedTop N t z.val := by
      simpa only [tiltedWindowTopTopEdges,Finset.mem_filter,Finset.mem_univ,true_and] using htop
    have hall : ∀ z ∈ b.val.val.toSym2, tiltedTop N t z := by
      intro z hz
      rw [← hpair] at hz
      obtain ⟨w,hw,hwz⟩ := Sym2.mem_map.mp hz
      exact hwz ▸ htop' w hw
    exact b.property ⟨hall _ (by simp [LatticeBond.toSym2]),hall _ (by simp [LatticeBond.toSym2])⟩
  exact ⟨(edgeRestrictionEdgeEquiv _ (tiltedWindowTopTopEdges N M t)).symm ⟨f,hnot⟩,hpair⟩

end
end PottsContinuity.RSW
