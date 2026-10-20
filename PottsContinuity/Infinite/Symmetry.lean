module

public import PottsContinuity.Infinite.Bridge
public import PottsContinuity.Infinite.Parameters
public import PottsContinuity.PD.FK.LimitTranslation
public import PottsContinuity.PD.FK.WiredBoxLimits
public import PottsContinuity.PD.FK.WiredBoxLaw
public import PottsContinuity.PD.FK.Isomorphism
public import PottsContinuity.PD.Duality.FreeAssociation

/-! Lattice symmetry invariance for free and wired infinite-volume limits. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Infinite

open PottsContinuity.PD.FK
open PottsContinuity.PD
open PottsContinuity.PD.Duality

noncomputable section

private theorem boundaryConditionIso_wired_box
    (e : PottsContinuity.PD.squareLattice ≃g
      PottsContinuity.PD.squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (c : LatticeVertex) (r : ℕ) :
    (boundaryConditionIso (boxGraphIsoOfLatticeIso e hbox c r)
      (BoundaryCondition.wired (boxVertexBoundary c r))).partition =
        (BoundaryCondition.wired (boxVertexBoundary (e c) r)).partition := by
  let f := boxGraphIsoOfLatticeIso e hbox c r
  have hmem (v : BoxVertex (e c) r) :
      f.symm v ∈ boxVertexBoundary c r ↔ v ∈ boxVertexBoundary (e c) r := by
    change (f.symm v).val ∈ PottsContinuity.PD.vertexBoundary
        (latticeBox c r) ↔
      v.val ∈ PottsContinuity.PD.vertexBoundary (latticeBox (e c) r)
    have hv : (f.symm v).val = e.symm v.val := rfl
    rw [hv]
    simp only [PottsContinuity.PD.vertexBoundary, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hv, w, hadj, hw⟩
      refine ⟨(by simp), e w, ?_, ?_⟩
      · simpa using e.map_rel_iff'.mpr hadj
      · intro hwe
        exact hw ((hbox c w r).mp hwe)
    · rintro ⟨hv, w, hadj, hw⟩
      refine ⟨(hbox c (e.symm v.val) r).mp (by simp), e.symm w, ?_, ?_⟩
      · have hadj' : PottsContinuity.PD.squareLattice.Adj
            (e (e.symm v.val)) (e (e.symm w)) := by simpa using hadj
        exact e.map_rel_iff'.mp hadj'
      · intro hwe
        exact hw (by simpa using (hbox c (e.symm w) r).mpr hwe)
  apply Setoid.ext
  intro u v
  change (f.symm u = f.symm v ∨
      f.symm u ∈ boxVertexBoundary c r ∧ f.symm v ∈ boxVertexBoundary c r) ↔
    (u = v ∨ u ∈ boxVertexBoundary (e c) r ∧ v ∈ boxVertexBoundary (e c) r)
  constructor
  · rintro (hEq | ⟨hu, hv⟩)
    · exact Or.inl (by simpa using congrArg f hEq)
    · exact Or.inr ⟨(hmem u).mp hu, (hmem v).mp hv⟩
  · rintro (hEq | ⟨hu, hv⟩)
    · exact Or.inl (by simpa using congrArg f.symm hEq)
    · exact Or.inr ⟨(hmem u).mpr hu, (hmem v).mpr hv⟩

private theorem wiredBoxConfiguration_iso_commute
    (e : PottsContinuity.PD.squareLattice ≃g
      PottsContinuity.PD.squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (c : LatticeVertex) (r : ℕ) (A : Configuration (boxGraph c r)) :
    wiredBoxConfiguration (e c) r (configurationIso (boxGraphIsoOfLatticeIso e hbox c r) A) =
      latticeConfigurationIsoHomeomorph e (wiredBoxConfiguration c r A) := by
  classical
  let f := boxGraphIsoOfLatticeIso e hbox c r
  let I := SimpleGraph.Iso.mapEdgeSet f
  let E := SimpleGraph.Iso.mapEdgeSet e
  funext b
  rw [latticeConfigurationIsoHomeomorph_apply]
  have hmap (g : (boxGraph c r).edgeSet) :
      boxEdgeEmbedding (e c) r (I g) = E (boxEdgeEmbedding c r g) :=
    boxEdgeEmbedding_iso_commute e hbox c r g
  have hmem (g : (boxGraph c r).edgeSet) : I g ∈ configurationIso f A ↔ g ∈ A := by
    change I g ∈ A.map I.toEmbedding ↔ g ∈ A
    rw [Finset.mem_map_equiv]
    simp
  apply Bool.eq_iff_iff.mpr
  rw [wiredBoxConfiguration_open_iff, wiredBoxConfiguration_open_iff]
  constructor
  · intro h g hg
    have htarget : boxEdgeEmbedding (e c) r (I g) = b := by
      calc
        boxEdgeEmbedding (e c) r (I g) = E (boxEdgeEmbedding c r g) := hmap g
        _ = E (E.symm b) := congrArg E hg
        _ = b := E.apply_symm_apply b
    have hopen := h (I g) htarget
    exact (hmem g).mp hopen
  · intro h g hg
    obtain ⟨g', hI⟩ := I.surjective g
    have hsource : boxEdgeEmbedding c r g' = E.symm b := by
      apply E.injective
      calc
        E (boxEdgeEmbedding c r g') = boxEdgeEmbedding (e c) r (I g') := (hmap g').symm
        _ = boxEdgeEmbedding (e c) r g := congrArg (boxEdgeEmbedding (e c) r) hI
        _ = b := hg
        _ = E (E.symm b) := (E.apply_symm_apply b).symm
    have hopen : I g' ∈ configurationIso f A := (hmem g').mpr (h g' hsource)
    simpa only [hI] using hopen

private theorem pmf_map_commute {α β γ δ : Type*}
    (μ : PMF α) (ν : PMF β) (f : α → γ) (g : β → δ)
    (e : α → β) (T : γ → δ) (he : μ.map e = ν)
    (hcomm : ∀ x, g (e x) = T (f x)) :
    (μ.map f).map T = ν.map g := by
  rw [← he, PMF.map_comp, PMF.map_comp]
  apply congrArg (fun k => μ.map k)
  exact funext fun x => (hcomm x).symm

private theorem wiredBoxLaw_iso_map
    (θ : Parameters) (e : PottsContinuity.PD.squareLattice ≃g
      PottsContinuity.PD.squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (c : LatticeVertex) (r : ℕ) :
    PMF.map (latticeConfigurationIsoHomeomorph e).toEquiv (wiredBoxLaw θ c r) =
      wiredBoxLaw θ (e c) r := by
  apply pmf_map_commute
    (law (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r)))
    (law (boxGraph (e c) r) θ (BoundaryCondition.wired (boxVertexBoundary (e c) r)))
    (wiredBoxConfiguration c r) (wiredBoxConfiguration (e c) r)
    (configurationIso (boxGraphIsoOfLatticeIso e hbox c r))
    (latticeConfigurationIsoHomeomorph e)
    ((law_configurationIso_map θ (boxGraphIsoOfLatticeIso e hbox c r)
      (BoundaryCondition.wired (boxVertexBoundary c r))).trans
      (law_eq_of_boundary_partition_eq θ _ _
        (boundaryConditionIso_wired_box e hbox c r)))
    (wiredBoxConfiguration_iso_commute e hbox c r)

private theorem wiredBoxProbabilityMeasure_iso_map
    (θ : Parameters) (e : PottsContinuity.PD.squareLattice ≃g
      PottsContinuity.PD.squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (c : LatticeVertex) (r : ℕ) :
    ProbabilityMeasure.map (wiredBoxProbabilityMeasure θ c r)
      (latticeConfigurationIsoHomeomorph e) =
        wiredBoxProbabilityMeasure θ (e c) r := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (latticeConfigurationIsoHomeomorph e) (wiredBoxLaw θ c r).toMeasure =
    (wiredBoxLaw θ (e c) r).toMeasure
  rw [PMF.toMeasure_map _ _ (latticeConfigurationIsoHomeomorph_measurable e)]
  exact congrArg PMF.toMeasure (wiredBoxLaw_iso_map θ e hbox c r)

/-- Every wired-box weak limit is invariant under a lattice graph isomorphism
that preserves the boxes. -/
theorem wiredBoxLimit_latticeIso_invariant
    (θ : Parameters) (e : PottsContinuity.PD.squareLattice ≃g
      PottsContinuity.PD.squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r) :
    ProbabilityMeasure.map
        (Classical.choose (wiredBoxLimit_existsUnique θ))
        (latticeConfigurationIsoHomeomorph e) =
      Classical.choose (wiredBoxLimit_existsUnique θ) := by
  let μ : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (wiredBoxLimit_existsUnique θ)
  let ν : ProbabilityMeasure LatticeConfiguration :=
    ProbabilityMeasure.map μ (latticeConfigurationIsoHomeomorph e)
  have hproperty := (Classical.choose_spec (wiredBoxLimit_existsUnique θ)).1
  have hboxInvCenter (c v : LatticeVertex) (r : ℕ) :
      e v ∈ latticeBox c r ↔ v ∈ latticeBox (e.symm c) r := by
    have hh := hbox (e.symm c) v r
    simpa using hh
  have hνproperty :
      ∀ (c : ℕ → LatticeVertex) (r : ℕ → ℕ),
        (∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1))) →
        (∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n)) →
        Tendsto (fun n => wiredBoxProbabilityMeasure θ (c n) (r n)) atTop (𝓝 ν) := by
    intro c r hnest hexhaust
    have htransformed : ∀ n,
        latticeBox (e.symm (c n)) (r n) ⊆
          latticeBox (e.symm (c (n + 1))) (r (n + 1)) := by
      intro n v hv
      exact (hboxInvCenter (c (n + 1)) v (r (n + 1))).mp (hnest n
        ((hboxInvCenter (c n) v (r n)).mpr hv))
    have hexhaustTransformed : ∀ v : LatticeVertex,
        ∃ n, v ∈ latticeBox (e.symm (c n)) (r n) := by
      intro v
      obtain ⟨n, hn⟩ := hexhaust (e v)
      refine ⟨n, ?_⟩
      exact (hboxInvCenter (c n) v (r n)).mp hn
    have hμ : Tendsto
        (fun n => wiredBoxProbabilityMeasure θ (e.symm (c n)) (r n)) atTop (𝓝 μ) :=
      hproperty (fun n => e.symm (c n)) r htransformed hexhaustTransformed
    have hmap : Tendsto
        (fun n => ProbabilityMeasure.map
          (wiredBoxProbabilityMeasure θ (e.symm (c n)) (r n))
          (latticeConfigurationIsoHomeomorph e)) atTop (𝓝 ν) :=
      ((ProbabilityMeasure.continuous_map
        (latticeConfigurationIsoHomeomorph e).continuous_toFun).continuousAt.tendsto).comp hμ
    have hterms :
        (fun n => ProbabilityMeasure.map
          (wiredBoxProbabilityMeasure θ (e.symm (c n)) (r n))
          (latticeConfigurationIsoHomeomorph e)) =
        (fun n => wiredBoxProbabilityMeasure θ (c n) (r n)) := by
      funext n
      simpa using wiredBoxProbabilityMeasure_iso_map θ e hbox (e.symm (c n)) (r n)
    rw [hterms] at hmap
    exact hmap
  have huniq := (Classical.choose_spec (wiredBoxLimit_existsUnique θ)).2 ν hνproperty
  simpa [μ, ν] using huniq

/-- Every frozen wired limit is invariant under a box-preserving lattice graph
isomorphism. -/
theorem wired_limit_map_latticeIso
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : PottsContinuity.PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (e : PottsContinuity.PD.squareLattice ≃g
      PottsContinuity.PD.squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r) :
    μ.map (latticeConfigurationIsoHomeomorph e) = μ := by
  let ν : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (wiredBoxLimit_existsUnique θ)
  have hν := (Classical.choose_spec (wiredBoxLimit_existsUnique θ)).1
    (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive
  have heq : μ = ν.toMeasure := PottsContinuity.PD.rc_limit_unique
    θ.toP θ.toQ 1 μ ν.toMeasure hμ
    (isRCInfiniteVolumeLimit_of_wiredBox_tendsto θ ν hν)
  rw [heq]
  exact congrArg ProbabilityMeasure.toMeasure (wiredBoxLimit_latticeIso_invariant θ e hbox)

private theorem frozen_limit_to_pd
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure (PottsContinuity.PD.squareLattice.edgeSet → Bool))
    (hμ : PottsContinuity.IsRCInfiniteVolumeLimit p q i μ) :
    PottsContinuity.PD.IsRCInfiniteVolumeLimit
      (pdParameters p q hp0 hp1 hq).toP (pdParameters p q hp0 hp1 hq).toQ i μ := by
  simpa only [pdParameters_toP, pdParameters_toQ] using
    isRCInfiniteVolumeLimit_to_PD_box p q i μ hμ

/-- Both frozen infinite-volume limits are invariant under any lattice graph
isomorphism preserving the centered box family. -/
theorem infinite_volume_latticeIso_invariant
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure (PottsContinuity.PD.squareLattice.edgeSet → Bool))
    (hμ : PottsContinuity.IsRCInfiniteVolumeLimit p q i μ)
    (e : PottsContinuity.PD.squareLattice ≃g
      PottsContinuity.PD.squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r) :
    μ.map (latticeConfigurationIsoHomeomorph e) = μ := by
  let θ := pdParameters p q hp0 hp1 hq
  have hPD := frozen_limit_to_pd p q hp0 hp1 hq i μ hμ
  fin_cases i
  · exact PottsContinuity.PD.Duality.free_limit_map_latticeIso
      θ μ hPD e hbox
  · exact wired_limit_map_latticeIso θ μ hPD e hbox

def latticeReflection : LatticeVertex → LatticeVertex := fun v => (-v.1, v.2)

lemma squareLattice_adj_reflection_iff (u v : LatticeVertex) :
    PottsContinuity.PD.FK.squareLattice.Adj (latticeReflection u)
      (latticeReflection v) ↔
      PottsContinuity.PD.FK.squareLattice.Adj u v := by
  simp only [PottsContinuity.PD.FK.squareLattice_adj_iff, latticeReflection]
  omega

def latticeReflectionIso : PottsContinuity.PD.FK.squareLattice ≃g
    PottsContinuity.PD.FK.squareLattice where
  toFun := latticeReflection
  invFun := latticeReflection
  left_inv := by intro v; ext <;> simp [latticeReflection]
  right_inv := by intro v; ext <;> simp [latticeReflection]
  map_rel_iff' := by intro u v; exact squareLattice_adj_reflection_iff u v

lemma mem_latticeBox_reflection_iff (c v : LatticeVertex) (r : ℕ) :
    latticeReflectionIso v ∈ latticeBox (latticeReflectionIso c) r ↔
      v ∈ latticeBox c r := by
  change latticeReflection v ∈ latticeBox (latticeReflection c) r ↔
    v ∈ latticeBox c r
  rw [mem_latticeBox, mem_latticeBox]
  simp only [latticeReflection]
  omega

end
end PottsContinuity.Infinite

