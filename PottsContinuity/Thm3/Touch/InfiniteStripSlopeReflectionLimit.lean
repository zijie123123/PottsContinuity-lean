module

public import PottsContinuity.Thm3.Touch.InfiniteSlopeReflectionLimit
public import PottsContinuity.Thm3.RSW.FiniteIso

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.Thm3.Prop4
open MeasureTheory

noncomputable section

attribute [local instance] configurationMeasurableSpace

 def reflectX (z : ℤ × ℤ) : ℤ × ℤ := (-z.1,z.2)

private theorem reflectX_sym2_involutive (e : Sym2 (ℤ × ℤ)) :
    Sym2.map reflectX (Sym2.map reflectX e) = e := by
  induction e using Sym2.inductionOn with
  | _ x y => simp [reflectX]

private theorem tiltedWindowEdge_reflect_ambient (n m : ℕ) (t : ℝ)
    (f : (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))).edgeSet) :
    Sym2.map Subtype.val
        ((tiltedWindowHorizontalReflectionIso n m t).mapEdgeSet f).1 =
      Sym2.map reflectX (Sym2.map Subtype.val f.1) := by
  change Sym2.map Subtype.val
      (Sym2.map (fun z => tiltedWindowHorizontalReflectionIso n m t z) f.1) =
    Sym2.map reflectX (Sym2.map Subtype.val f.1)
  rw [Sym2.map_map, Sym2.map_map]
  congr 1

private theorem tiltedWindowEdge_reflect_ambient_symm (n m : ℕ) (t : ℝ)
    (f : (squareLattice.induce (tiltedWindow n m (-t) : Set (ℤ × ℤ))).edgeSet) :
    Sym2.map Subtype.val
        ((tiltedWindowHorizontalReflectionIso n m t).symm.mapEdgeSet f).1 =
      Sym2.map reflectX (Sym2.map Subtype.val f.1) := by
  change Sym2.map Subtype.val
      (Sym2.map (fun z => (tiltedWindowHorizontalReflectionIso n m t).symm z) f.1) =
    Sym2.map reflectX (Sym2.map Subtype.val f.1)
  rw [Sym2.map_map, Sym2.map_map]
  congr 1

private theorem tiltedStripEdge_reflect_ambient (N : ℕ) (t : ℝ)
    (e : (tiltedStripGraph N t).edgeSet) :
    Sym2.map Subtype.val ((tiltedStripSlopeReflectionIso N t).mapEdgeSet e).1 =
      Sym2.map reflectX (Sym2.map Subtype.val e.1) := by
  change Sym2.map Subtype.val
      (Sym2.map (fun z => tiltedStripSlopeReflectionIso N t z) e.1) =
    Sym2.map reflectX (Sym2.map Subtype.val e.1)
  rw [Sym2.map_map, Sym2.map_map]
  congr 1

private theorem tiltedStripEdge_reflect_ambient_symm (N : ℕ) (t : ℝ)
    (e : (tiltedStripGraph N (-t)).edgeSet) :
    Sym2.map Subtype.val ((tiltedStripSlopeReflectionIso N t).symm.mapEdgeSet e).1 =
      Sym2.map reflectX (Sym2.map Subtype.val e.1) := by
  change Sym2.map Subtype.val
      (Sym2.map (fun z => (tiltedStripSlopeReflectionIso N t).symm z) e.1) =
    Sym2.map reflectX (Sym2.map Subtype.val e.1)
  rw [Sym2.map_map, Sym2.map_map]
  congr 1

private theorem finiteBoolIso_state (n m : ℕ) (t : ℝ)
    (ω : (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))).edgeSet → Bool)
    (f : (squareLattice.induce (tiltedWindow n m (-t) : Set (ℤ × ℤ))).edgeSet) :
    finiteBoolIso (tiltedWindow n m t) (tiltedWindow n m (-t))
        (tiltedWindowHorizontalReflectionIso n m t) ω f =
      ω ((configurationIsoEdgeEquiv (tiltedWindowHorizontalReflectionIso n m t)).symm f) := by
  simp [finiteBoolIso, Equiv.trans_apply, boolConfigurationEquiv,
    configurationIso, configurationIsoEdgeEquiv]

private theorem tiltedWindowCylinder_reflection_iff (N m : ℕ) (t : ℝ)
    (A : Finset (tiltedStripGraph N (-t)).edgeSet)
    (σ : TiltedConfiguration N (-t))
    (ω : (squareLattice.induce (tiltedWindow N m t : Set (ℤ × ℤ))).edgeSet → Bool) :
    tiltedWindowCylinder N m (-t) A σ
        (finiteBoolIso (tiltedWindow N m t) (tiltedWindow N m (-t))
          (tiltedWindowHorizontalReflectionIso N m t) ω) ↔
      tiltedWindowCylinder N m t
        (A.map (configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)).symm.toEmbedding)
        ((tiltedStripSlopeReflectionHomeomorph N t).symm σ) ω := by
  classical
  constructor
  · intro h es hes
    obtain ⟨et,het,hesEq⟩ := Finset.mem_map.mp hes
    obtain ⟨ft,hcoord,hstate⟩ := h et het
    let fs := (tiltedWindowHorizontalReflectionIso N m t).symm.mapEdgeSet ft
    have hesEq' :
        (configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)).symm et = es := by
      simpa [configurationIsoEdgeEquiv] using hesEq
    have hEt : (tiltedStripSlopeReflectionIso N t).mapEdgeSet es = et := by
      calc
        configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t) es =
            configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)
              ((configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)).symm et) := by rw [← hesEq']
        _ = et := Equiv.apply_symm_apply _ _
    have hcoordS : Sym2.map Subtype.val fs.1 = Sym2.map Subtype.val es.1 := by
      have hcoordReflect := congrArg (Sym2.map reflectX) hcoord
      have hstrip : Sym2.map Subtype.val et.1 =
          Sym2.map reflectX (Sym2.map Subtype.val es.1) := by
        rw [← hEt]
        exact tiltedStripEdge_reflect_ambient N t es
      calc
        Sym2.map Subtype.val fs.1 =
            Sym2.map reflectX (Sym2.map Subtype.val ft.1) :=
          tiltedWindowEdge_reflect_ambient_symm N m t ft
        _ = Sym2.map reflectX (Sym2.map Subtype.val et.1) := hcoordReflect
        _ = Sym2.map reflectX (Sym2.map reflectX (Sym2.map Subtype.val es.1)) := by rw [hstrip]
        _ = Sym2.map Subtype.val es.1 := reflectX_sym2_involutive _
    have hstate' : ω fs = σ et := by
      simpa [finiteBoolIso, Equiv.trans_apply, boolConfigurationEquiv,
        configurationIso, configurationIsoEdgeEquiv, fs] using hstate
    have hsig : (tiltedStripSlopeReflectionHomeomorph N t).symm σ es =
        σ ((tiltedStripSlopeReflectionIso N t).mapEdgeSet es) := by
      have hh := tiltedStripSlopeReflectionHomeomorph_edge N t
        ((tiltedStripSlopeReflectionHomeomorph N t).symm σ) es
      simpa using hh.symm
    have hstateS : ω fs = (tiltedStripSlopeReflectionHomeomorph N t).symm σ es := by
      rw [hsig, hEt]
      exact hstate'
    exact ⟨fs,hcoordS,hstateS⟩
  · intro h et het
    let es := (tiltedStripSlopeReflectionIso N t).symm.mapEdgeSet et
    have hes : es ∈ A.map
        (configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)).symm.toEmbedding := by
      exact Finset.mem_map.mpr ⟨et, het, by simp [es, configurationIsoEdgeEquiv]⟩
    obtain ⟨fs,hcoordS,hstateS⟩ := h es hes
    let ft := (tiltedWindowHorizontalReflectionIso N m t).mapEdgeSet fs
    have hEt : (tiltedStripSlopeReflectionIso N t).mapEdgeSet es = et := by
      change configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)
        ((configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)).symm et) = et
      exact Equiv.apply_symm_apply _ _
    have hcoordT : Sym2.map Subtype.val ft.1 = Sym2.map Subtype.val et.1 := by
      have hstrip : Sym2.map Subtype.val es.1 =
          Sym2.map reflectX (Sym2.map Subtype.val et.1) := by
        simpa [es, configurationIsoEdgeEquiv] using tiltedStripEdge_reflect_ambient_symm N t et
      calc
        Sym2.map Subtype.val ft.1 =
            Sym2.map reflectX (Sym2.map Subtype.val fs.1) :=
          tiltedWindowEdge_reflect_ambient N m t fs
        _ = Sym2.map reflectX (Sym2.map Subtype.val es.1) :=
          congrArg (Sym2.map reflectX) hcoordS
        _ = Sym2.map reflectX (Sym2.map reflectX (Sym2.map Subtype.val et.1)) := by rw [hstrip]
        _ = Sym2.map Subtype.val et.1 := reflectX_sym2_involutive _
    have hsig : (tiltedStripSlopeReflectionHomeomorph N t).symm σ es = σ et := by
      have hh := tiltedStripSlopeReflectionHomeomorph_edge N t
        ((tiltedStripSlopeReflectionHomeomorph N t).symm σ) es
      simpa [hEt] using hh.symm
    have hstate' : ω fs = σ et := by
      rw [hsig] at hstateS
      exact hstateS
    have hfin : (configurationIsoEdgeEquiv (tiltedWindowHorizontalReflectionIso N m t)).symm ft = fs := by
      simpa [ft, configurationIsoEdgeEquiv] using
        (Equiv.symm_apply_apply
          (SimpleGraph.Iso.mapEdgeSet (tiltedWindowHorizontalReflectionIso N m t)) fs)
    have hstateT : (finiteBoolIso (tiltedWindow N m t) (tiltedWindow N m (-t))
        (tiltedWindowHorizontalReflectionIso N m t) ω) ft = σ et := by
      rw [finiteBoolIso_state, hfin]
      exact hstate'
    exact ⟨ft,hcoordT,hstateT⟩

private theorem finite_measure_event_map {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (θ : Parameters)
    (ξ : BoundaryCondition V) (η : BoundaryCondition W)
    (e : Configuration G ≃ Configuration H)
    (hLaw : (law G θ ξ).map e = law H θ η)
    (T : Set (Configuration H)) :
    (measure H θ η T).toReal =
      (measure G θ ξ {A | e A ∈ T}).toReal := by
  unfold PD.FK.measure
  rw [← hLaw, PMF.toMeasure_map_apply _ _ _ measurable_from_top
    MeasurableSpace.measurableSet_top]
  rfl

private theorem finiteBoundaryEventProbability_graphIso
    (V W : Finset (ℤ × ℤ)) (θ : Parameters)
    (ξ : BoundaryCondition (V : Set (ℤ × ℤ)))
    (η : BoundaryCondition (W : Set (ℤ × ℤ)))
    (e : (squareLattice.induce (V : Set (ℤ × ℤ))) ≃g
      (squareLattice.induce (W : Set (ℤ × ℤ))))
    (hLaw : (law (squareLattice.induce (V : Set (ℤ × ℤ))) θ ξ).map
        (configurationIso e) =
      law (squareLattice.induce (W : Set (ℤ × ℤ))) θ η)
    (E : ((squareLattice.induce (W : Set (ℤ × ℤ))).edgeSet → Bool) → Prop) :
    finiteBoundaryEventProbability W θ η E =
      finiteBoundaryEventProbability V θ ξ (fun ω => E (finiteBoolIso V W e ω)) := by
  unfold finiteBoundaryEventProbability
  have hset : finiteBoolEvent V (fun ω => E (finiteBoolIso V W e ω)) =
      {A | configurationIso e A ∈ finiteBoolEvent W E} := by
    ext A
    simp [finiteBoolEvent, finiteBoolIso, Equiv.trans_apply]
  rw [hset]
  exact finite_measure_event_map θ ξ η (configurationIso e) hLaw (finiteBoolEvent W E)

private theorem tiltedWindowCylinderProbability_reflection
    (θ : Parameters) (N m : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (A : Finset (tiltedStripGraph N (-t)).edgeSet)
    (σ : TiltedConfiguration N (-t)) :
    tiltedWindowCylinderProbability θ N (-t) 0 m A σ =
      tiltedWindowCylinderProbability θ N t 0 m
        (A.map (configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)).symm.toEmbedding)
        ((tiltedStripSlopeReflectionHomeomorph N t).symm σ) := by
  have hLaw := tiltedWindowTopLaw_map_horizontalReflection θ N m t ht
  have hprob := finiteBoundaryEventProbability_graphIso
    (tiltedWindow N m t) (tiltedWindow N m (-t)) θ
    (tiltedWindowBoundary N m t 0) (tiltedWindowBoundary N m (-t) 0)
    (tiltedWindowHorizontalReflectionIso N m t) hLaw
    (tiltedWindowCylinder N m (-t) A σ)
  unfold tiltedWindowCylinderProbability at *
  rw [hprob]
  congr 1
  funext ω
  exact propext (tiltedWindowCylinder_reflection_iff N m t A σ ω)


private theorem configurationCylinder_isClopen {ι : Type*}
    (A : Finset ι) (ξ : ι → Bool) :
    IsClopen {ω : ι → Bool | ∀ e ∈ A, ω e = ξ e} := by
  have heq : {ω : ι → Bool | ∀ e ∈ A, ω e = ξ e} =
      ⋂ e ∈ A, {ω | ω e = ξ e} := by
    ext ω
    simp
  rw [heq]
  exact isClopen_biInter_finset fun e _ =>
    (isClopen_discrete ({ξ e} : Set Bool)).preimage (continuous_apply e)

private theorem tiltedStripCylinder_reflection_iff (N : ℕ) (t : ℝ)
    (A : Finset (tiltedStripGraph N (-t)).edgeSet)
    (σ : TiltedConfiguration N (-t))
    (ω : TiltedConfiguration N t) :
    (∀ e ∈ A,
      tiltedStripSlopeReflectionHomeomorph N t ω e = σ e) ↔
    ∀ e ∈ A.map
        (configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)).symm.toEmbedding,
      ω e = (tiltedStripSlopeReflectionHomeomorph N t).symm σ e := by
  classical
  constructor
  · intro h es hes
    obtain ⟨et,het,hesEq⟩ := Finset.mem_map.mp hes
    have hEt : (tiltedStripSlopeReflectionIso N t).mapEdgeSet es = et := by
      have hesEq' :
          (configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)).symm et = es := by
        simpa [configurationIsoEdgeEquiv] using hesEq
      calc
        configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t) es =
            configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)
              ((configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)).symm et) := by rw [← hesEq']
        _ = et := Equiv.apply_symm_apply _ _
    have hsig : (tiltedStripSlopeReflectionHomeomorph N t).symm σ es =
        σ ((tiltedStripSlopeReflectionIso N t).mapEdgeSet es) := by
      have hh := tiltedStripSlopeReflectionHomeomorph_edge N t
        ((tiltedStripSlopeReflectionHomeomorph N t).symm σ) es
      simpa using hh.symm
    have hmap := tiltedStripSlopeReflectionHomeomorph_edge N t ω es
    rw [hEt] at hmap
    have hsig' : (tiltedStripSlopeReflectionHomeomorph N t).symm σ es = σ et := by
      simpa [hEt] using hsig
    calc
      ω es = tiltedStripSlopeReflectionHomeomorph N t ω et := hmap.symm
      _ = σ et := h et het
      _ = (tiltedStripSlopeReflectionHomeomorph N t).symm σ es := hsig'.symm
  · intro h et het
    let es := (tiltedStripSlopeReflectionIso N t).symm.mapEdgeSet et
    have hes : es ∈ A.map
        (configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)).symm.toEmbedding := by
      exact Finset.mem_map.mpr ⟨et, het, by simp [es, configurationIsoEdgeEquiv]⟩
    have hEt : (tiltedStripSlopeReflectionIso N t).mapEdgeSet es = et := by
      change configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)
        ((configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)).symm et) = et
      exact Equiv.apply_symm_apply _ _
    have hsig : (tiltedStripSlopeReflectionHomeomorph N t).symm σ es = σ et := by
      have hh := tiltedStripSlopeReflectionHomeomorph_edge N t
        ((tiltedStripSlopeReflectionHomeomorph N t).symm σ) es
      simpa [hEt] using hh.symm
    have hmap := tiltedStripSlopeReflectionHomeomorph_edge N t ω es
    rw [hEt] at hmap
    have hsig' : (tiltedStripSlopeReflectionHomeomorph N t).symm σ es = σ et := by
      simpa [hEt] using hsig
    calc
      tiltedStripSlopeReflectionHomeomorph N t ω et = ω es := hmap
      _ = (tiltedStripSlopeReflectionHomeomorph N t).symm σ es := h es hes
      _ = σ et := hsig'

/-- The unique top-wired cylinder limit is invariant under horizontal
reflection, which changes the sign of the tilt. -/
theorem selfDualTiltedStripMeasure_horizontalReflection
    (q : Set.Ici (1 : ℝ)) (N : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (selfDualTiltedStripMeasure q N t).map
        (tiltedStripSlopeReflectionHomeomorph N t) =
      selfDualTiltedStripMeasure q N (-t) := by
  let μ := selfDualTiltedStripMeasure q N t
  let μlim := selfDualTiltedStripMeasure q N (-t)
  let F := tiltedStripSlopeReflectionHomeomorph N t
  let ν : ProbabilityMeasure (TiltedConfiguration N (-t)) :=
    ProbabilityMeasure.map
      (⟨μ, (selfDualTiltedStripMeasure_isLimit q N t).1⟩ : ProbabilityMeasure
        (TiltedConfiguration N t)) (fun ω => F ω)
  have hν : IsTiltedStripLimit (selfDualParameters q) N (-t) 0 ν.toMeasure := by
    refine ⟨ν.prop, ?_⟩
    intro A σ
    let A' := A.map
      (configurationIsoEdgeEquiv (tiltedStripSlopeReflectionIso N t)).symm.toEmbedding
    let σ' := F.symm σ
    let E : Set (TiltedConfiguration N (-t)) := {ω | ∀ e ∈ A, ω e = σ e}
    let E' : Set (TiltedConfiguration N t) := {ω | ∀ e ∈ A', ω e = σ' e}
    have hpre : F ⁻¹' E = E' := by
      ext ω
      simp only [E, E', Set.mem_preimage, Set.mem_ofPred_eq]
      exact tiltedStripCylinder_reflection_iff N t A σ ω
    have hclopen : IsClopen E := configurationCylinder_isClopen A σ
    have hreal : ν.toMeasure.real E = μ.real E' := by
      change ((μ.map F) E).toReal = (μ E').toReal
      rw [Measure.map_apply F.measurable hclopen.isOpen.measurableSet, hpre]

    have hlimit :=
      (selfDualTiltedStripMeasure_isLimit q N t).2 A' σ'
    have hterm : ∀ m,
        tiltedWindowCylinderProbability (selfDualParameters q) N (-t) 0 m A σ =
          tiltedWindowCylinderProbability (selfDualParameters q) N t 0 m A' σ' := by
      intro m
      exact tiltedWindowCylinderProbability_reflection (selfDualParameters q) N m t ht A σ
    have htarget := hlimit.congr' (Filter.Eventually.of_forall fun m => (hterm m).symm)
    have htarget' : Filter.Tendsto
        (fun m => tiltedWindowCylinderProbability (selfDualParameters q) N (-t) 0 m A σ)
        Filter.atTop (nhds (ν.toMeasure.real E)) := by
      simpa only [hreal, E, E', μ, σ'] using htarget
    exact htarget'
  have huniq := isTiltedStripLimit_unique (selfDualParameters q) N (-t) 0
    ν.toMeasure μlim hν (selfDualTiltedStripMeasure_isLimit q N (-t))
  change (μ.map F) = μlim at huniq
  simpa [μ, μlim, ν] using huniq

end

end PottsContinuity.Thm3.Touch
