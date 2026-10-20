module

public import PottsContinuity.Thm4Plane.ScreenBoundaryClusterFiber
public import PottsContinuity.Thm4Plane.ScreenCapDomainPlaneEvent
public import PottsContinuity.Thm4Plane.ScreenTargetCapInducedPath
public import PottsContinuity.Thm4Plane.ScreenCapFreeLaw
public import PottsContinuity.Thm4Plane.PlaneFiniteComparison
public import PottsContinuity.Thm4Plane.ScreenFactorAssembly
public import PottsContinuity.Thm4Plane.PlaneTranslation
public import PottsContinuity.Thm4Plane.ScreenBoundaryClusterCap
public import PottsContinuity.Exploration.BoundaryClusterStatisticDMP
public import PottsContinuity.FKC.FiniteFK.FiniteConditionalGoodFiberBound

@[expose] public section

namespace PottsContinuity.Thm4Plane

open MeasureTheory
open PottsContinuity.Exploration
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.Infinite

noncomputable section

local instance screenBoundaryClusterConditionalEdgeFintype (m : ℕ) :
    Fintype (slitBoxGraph (16 * m)).edgeSet := Fintype.ofFinite _
local instance screenBoundaryClusterConditionalEdgeDecidableEq (m : ℕ) :
    DecidableEq (slitBoxGraph (16 * m)).edgeSet := Classical.decEq _
local instance screenBoundaryClusterConditionalConfigFintype (m : ℕ) :
    Fintype (PottsContinuity.FKC.FiniteFK.Configuration
      (slitBoxGraph (16 * m))) := Fintype.ofFinite _
local instance screenBoundaryClusterConditionalConfigNonempty (m : ℕ) :
    Nonempty (PottsContinuity.FKC.FiniteFK.Configuration
      (slitBoxGraph (16 * m))) := ⟨∅⟩
local instance screenBoundaryClusterConditionalConfigMeasurable (m : ℕ) :
    MeasurableSpace (PottsContinuity.FKC.FiniteFK.Configuration
      (slitBoxGraph (16 * m))) := ⊤
local instance screenBoundaryClusterConditionalConfigSingleton (m : ℕ) :
    MeasurableSingletonClass (PottsContinuity.FKC.FiniteFK.Configuration
      (slitBoxGraph (16 * m))) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

private theorem screenCapEmptyRestriction_eq_induce (m : ℕ)
    (U : Set (SlitBoxVertex (16 * m))) :
    screenCapEdgeDeletedDomainGraph m
      (∅ : PottsContinuity.FKC.FiniteFK.Configuration
        (slitBoxGraph (16 * m))) U =
      (slitBoxGraph (16 * m)).induce U := by
  ext x y
  simp [screenCapEdgeDeletedDomainGraph,
    PottsContinuity.FKC.FiniteFK.edgeRestriction,
    PottsContinuity.FKC.FiniteFK.openEdges]

def screenBoundaryClusterCapConnectionEvent (m : ℕ)
    (U : Set (SlitBoxVertex (16 * m)))
    (hcap : screenTargetCap m ⊆ U) :
    Set (PottsContinuity.FKC.FiniteFK.Configuration
      ((slitBoxGraph (16 * m)).induce U)) :=
  {B | ∃ v : {x : SlitBoxVertex (16 * m) // x ∈ U},
      v.val ∈ screenTargetCap m ∧
      (|v.val.val.1| = (m : ℤ) ∨ v.val.val.2 = -(15 * (m : ℤ))) ∧
      (openGraph ((slitBoxGraph (16 * m)).induce U) B).Reachable
        ⟨slitBoxBottomCenterVertex (16 * m), hcap
          (screenTargetCap_bottomCenter_mem m)⟩ v}

private theorem screenBoundaryClusterCapConnectionEvent_isUpperSet
    (m : ℕ) (U : Set (SlitBoxVertex (16 * m)))
    (hcap : screenTargetCap m ⊆ U) :
    IsUpperSet (screenBoundaryClusterCapConnectionEvent m U hcap) := by
  intro A B hAB hA
  rcases hA with ⟨v, hv, hb, hconn⟩
  exact ⟨v, hv, hb, actualConnected_mono hAB hconn⟩

private theorem screenBoundaryClusterRestriction_openAdj
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V ↪ W) (hGH : G.map f ≤ H)
    (A : PottsContinuity.PD.FK.Configuration H)
    {x y : V} (hxy : G.Adj x y)
    (hopen : (openGraph H A).Adj (f x) (f y)) :
    (openGraph G
      (PottsContinuity.PD.FK.embeddedConfigurationRestriction G H f hGH A)).Adj x y := by
  rw [openGraph_adj] at hopen ⊢
  rcases hopen with ⟨eH, heH, heval⟩
  let eG : G.edgeSet := ⟨s(x, y), G.mem_edgeSet.mpr hxy⟩
  have hval :
      (PottsContinuity.PD.FK.embeddedEdgeEmbedding G H f hGH eG).val = eH.val := by
    rw [PottsContinuity.PD.FK.embeddedEdgeEmbedding_coe]
    change Sym2.map f s(x, y) = eH.val
    rw [Sym2.map_mk]
    exact heval.symm
  have he : PottsContinuity.PD.FK.embeddedEdgeEmbedding G H f hGH eG = eH :=
    Subtype.ext hval
  exact ⟨eG,
    (PottsContinuity.PD.FK.mem_embeddedConfigurationRestriction
      G H f hGH A eG).mpr (he ▸ heH), rfl⟩

private theorem screenBoundaryClusterConditionedCapEvent_le_freePlane
    (q : Set.Icc (1 : ℝ) 4) (m : ℕ)
    (p : Set.Icc (0 : ℝ) 1)
    (hp : (p : ℝ) = Real.sqrt q / (1 + Real.sqrt q))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : PottsContinuity.IsRCInfiniteVolumeLimit p
      ⟨(q : ℝ), lt_of_lt_of_le one_pos q.2.1⟩ 0 μ)
    (C : PottsContinuity.FKC.FiniteFK.Configuration
      (slitBoxGraph (16 * m)))
    (hgood : screenBoundaryClusterGood m C) :
    ((finiteStatisticConditionalPMF
      (PottsContinuity.PD.FK.law (slitBoxGraph (16 * m))
        (PottsContinuity.PD.FK.criticalParameters
          (⟨(q : ℝ), q.2.1⟩ : Set.Ici (1 : ℝ)))
        (PottsContinuity.Thm4.fkcBoundaryToPD
          (slitBoxBoundary (16 * m))))
      (fun A => (PottsContinuity.PD.FK.law_pos
        (slitBoxGraph (16 * m))
        (PottsContinuity.PD.FK.criticalParameters
          (⟨(q : ℝ), q.2.1⟩ : Set.Ici (1 : ℝ)))
        (PottsContinuity.Thm4.fkcBoundaryToPD
          (slitBoxBoundary (16 * m))) A).ne')
      (boundaryClusterStatistic
        (slitBoxWiredArc (16 * m) : Set (SlitBoxVertex (16 * m))))
      ⟨boundaryClusterStatistic
        (slitBoxWiredArc (16 * m) : Set (SlitBoxVertex (16 * m))) C, ⟨C, rfl⟩⟩).toMeasure
      (generalEScreenEvent (16 * m))).toReal ≤
      μ.real (centeredBoxBoundaryConnectionEvent m) := by
  let G := slitBoxGraph (16 * m)
  let S := (slitBoxWiredArc (16 * m) : Set (SlitBoxVertex (16 * m)))
  let U := boundaryClusterInterior S C
  let H := G.induce U
  let f := boundaryClusterEmbedding S C
  let hGH : H.map f ≤ G := by
    intro x z hAdj
    obtain ⟨x', z', hadj, hx, hz⟩ :=
      (SimpleGraph.map_adj (f := f) (G := H) x z).mp hAdj
    have hxval : (x' : SlitBoxVertex (16 * m)) = x := by
      simpa [f, boundaryClusterEmbedding] using hx
    have hzval : (z' : SlitBoxVertex (16 * m)) = z := by
      simpa [f, boundaryClusterEmbedding] using hz
    have h := (SimpleGraph.induce_adj (G := G)).mp hadj
    rw [hxval, hzval] at h
    exact h
  have hcap : screenTargetCap m ⊆ U := by
    simpa [screenBoundaryClusterGood, U, S] using hgood
  let E : Set (Configuration H) := screenBoundaryClusterCapConnectionEvent m U hcap
  have hEUpper : IsUpperSet E := screenBoundaryClusterCapConnectionEvent_isUpperSet m U hcap
  have hsource :
      generalEScreenEvent (16 * m) ⊆
        (PottsContinuity.PD.FK.embeddedConfigurationRestriction H G f hGH) ⁻¹' E := by
    intro A hA
    obtain ⟨v, hv, hb, ⟨walk⟩⟩ :=
      generalEScreenEvent_has_path_in_any_induced_cap_domain m A hA U hcap
    have hsub : (openGraph G A).induce U ≤
        openGraph H
          (PottsContinuity.PD.FK.embeddedConfigurationRestriction H G f hGH A) := by
      intro x y hxy
      have hxyG : (openGraph G A).Adj x.val y.val :=
        SimpleGraph.induce_adj.mp hxy
      have hxyH : H.Adj x y :=
        SimpleGraph.induce_adj.mpr ((openGraph_le G A) hxyG)
      exact screenBoundaryClusterRestriction_openAdj f hGH A hxyH hxyG
    let φ : (openGraph G A).induce U →g
        openGraph H
          (PottsContinuity.PD.FK.embeddedConfigurationRestriction H G f hGH A) :=
      { toFun := id
        map_rel' := by
          intro x y hxy
          simpa using hsub hxy }
    have hconn := (walk.map φ).reachable
    change A ∈
      (PottsContinuity.PD.FK.embeddedConfigurationRestriction H G f hGH) ⁻¹' E
    change ∃ v : {x : SlitBoxVertex (16 * m) // x ∈ U},
      v.val ∈ screenTargetCap m ∧
      (|v.val.val.1| = (m : ℤ) ∨ v.val.val.2 = -(15 * (m : ℤ))) ∧
      (openGraph H
        (PottsContinuity.PD.FK.embeddedConfigurationRestriction H G f hGH A)).Reachable
        ⟨slitBoxBottomCenterVertex (16 * m), hcap
          (screenTargetCap_bottomCenter_mem m)⟩ v
    exact ⟨v, hv, hb, by simpa [φ] using hconn⟩
  let θ := PottsContinuity.PD.FK.criticalParameters
    (⟨(q : ℝ), q.2.1⟩ : Set.Ici (1 : ℝ))
  let ξ := PottsContinuity.Thm4.fkcBoundaryToPD
    (slitBoxBoundary (16 * m))
  let r := boundaryClusterStatistic (G := G) S
  let y : Set.range r := ⟨r C, ⟨C, rfl⟩⟩
  have hboundary : ξ.boundary ⊆ S := by
    simp [ξ, S, PottsContinuity.Thm4.fkcBoundaryToPD,
      slitBoxBoundary, BoundaryCondition.wired]
  let ζ : PottsContinuity.PD.FK.BoundaryCondition
      {x : SlitBoxVertex (16 * m) // x ∈ U} :=
    PottsContinuity.PD.FK.BoundaryCondition.free ∅
  have hJ : H.map (Function.Embedding.refl _) ≤ H := by
    intro x y hxy
    obtain ⟨x', y', hxy', rfl, rfl⟩ :=
      (SimpleGraph.map_adj (Function.Embedding.refl _) H x y).mp hxy
    exact hxy'
  let event : Set (Configuration H) := E
  have hcond := finiteStatisticConditionalPMF_boundaryCluster_embeddedIncreasingEvent_le_freeGraph
    θ ξ S hboundary C (Function.Embedding.refl _) hJ ζ event hEUpper
  let hGHstatement : H.map f ≤ G := by
    intro x z hAdj
    obtain ⟨x', z', hadj, hx, hz⟩ :=
      (SimpleGraph.map_adj
        (f := boundaryClusterEmbedding S C)
        (G := SimpleGraph.induce (boundaryClusterInterior S C) G) x z).mp hAdj
    have hxval : (x' : SlitBoxVertex (16 * m)) = x := by
      simpa [boundaryClusterEmbedding] using hx
    have hzval : (z' : SlitBoxVertex (16 * m)) = z := by
      simpa [boundaryClusterEmbedding] using hz
    have h := (SimpleGraph.induce_adj (G := G)).mp hadj
    rw [hxval, hzval] at h
    exact h
  have hsets :
      (PottsContinuity.PD.FK.embeddedConfigurationRestriction
        H G f hGHstatement) ⁻¹' event =
        (PottsContinuity.PD.FK.embeddedConfigurationRestriction
          H G f hGH) ⁻¹' event := by
    ext A
    simp only [Set.mem_preimage]
  let qI : Set.Ici (1 : ℝ) := ⟨(q : ℝ), q.2.1⟩
  have hparam : Infinite.pdParameters p
      ⟨(q : ℝ), PottsContinuity.PD.FK.clusterWeight_pos
        (PottsContinuity.PD.FK.criticalParameters qI)⟩ hp0 hp1 q.2.1 =
        PottsContinuity.PD.FK.criticalParameters qI := by
    exact pdParameters_eq_criticalParameters_of_selfDualValue qI p hp hp0 hp1
  have hrestrict (A : Configuration H) :
      PottsContinuity.PD.FK.embeddedConfigurationRestriction
        H H (Function.Embedding.refl _) hJ A = A := by
    have hedge (e : H.edgeSet) :
        PottsContinuity.PD.FK.embeddedEdgeEmbedding
          H H (Function.Embedding.refl _) hJ e = e := by
      apply Subtype.ext
      rw [PottsContinuity.PD.FK.embeddedEdgeEmbedding_coe]
      simp
    ext e
    rw [PottsContinuity.PD.FK.mem_embeddedConfigurationRestriction,
      hedge]
  have hpre :
      (PottsContinuity.PD.FK.embeddedConfigurationRestriction
        H H (Function.Embedding.refl _) hJ) ⁻¹' event = event := by
    ext A
    simp only [Set.mem_preimage]
    rw [hrestrict]
  have hconditional :
      ((finiteStatisticConditionalPMF
        (PottsContinuity.PD.FK.law G θ ξ)
        (fun A => (PottsContinuity.PD.FK.law_pos G θ ξ A).ne') r y).toMeasure
        ((PottsContinuity.PD.FK.embeddedConfigurationRestriction
          H G f hGH) ⁻¹' E)).toReal ≤
      (PottsContinuity.PD.FK.measure H (Infinite.pdParameters p
        ⟨(q : ℝ), lt_of_lt_of_le one_pos q.2.1⟩ hp0 hp1 q.2.1)
        (PottsContinuity.PD.FK.BoundaryCondition.free ∅) E).toReal := by
    have hmain := hcond
    dsimp [θ] at hmain
    conv at hmain =>
      rhs
      rw [← hparam]
    rw [hpre] at hmain
    rw [hsets] at hmain
    dsimp [θ, PottsContinuity.PD.FK.measure]
    exact hmain
  let fP := screenCapDomainVertexEmbedding m U
  have hGplane : H.map fP ≤ PottsContinuity.PD.FK.squareLattice := by
    change (SimpleGraph.induce U (slitBoxGraph (16 * m))).map fP ≤
      PottsContinuity.PD.FK.squareLattice
    rw [← screenCapEmptyRestriction_eq_induce m U]
    exact screenCapEdgeDeletedDomainGraph_map_to_PD m (∅ : Configuration G) U
  have hfinite :=
    finite_free_embedded_event_le_centered_box_boundary_probability_of_event_inclusion
      p ⟨(q : ℝ), lt_of_lt_of_le one_pos q.2.1⟩ hp0 hp1 q.2.1 H fP hGplane
      E hEUpper μ hμ (0, -(16 * (m : ℤ))) m
      (by
        intro ω hω
        change latticeGraphRestriction H fP hGplane ω ∈ E at hω
        rcases hω with ⟨v, hv, hb, hconn⟩
        let cfg := latticeGraphRestriction H fP hGplane ω
        obtain ⟨path⟩ := hconn
        have hOpen : ∀ {u w : {x : SlitBoxVertex (16 * m) // x ∈ U}},
            (PottsContinuity.FKC.FiniteFK.openGraph H cfg).Adj u w →
              (PottsContinuity.PD.rcInfiniteOpenGraph ω).Adj
                (fP u) (fP w) := by
          intro u w huw
          obtain ⟨e, heOpen, heuw⟩ :=
            (PottsContinuity.FKC.FiniteFK.openGraph_adj H cfg u w).mp huw
          have hstate : ω
              (PottsContinuity.PD.FK.embeddedEdgeEmbedding
                H PottsContinuity.PD.FK.squareLattice fP hGplane e) = true := by
            change e ∈ latticeGraphRestriction H fP hGplane ω at heOpen
            unfold latticeGraphRestriction at heOpen
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heOpen
            exact heOpen
          have hEdgeUV : s(u, w) ∈ H.edgeSet := heuw.symm ▸ e.property
          have hAdj : PottsContinuity.PD.FK.squareLattice.Adj
              (fP u) (fP w) := hGplane
            ((SimpleGraph.map_adj fP H (fP u) (fP w)).mpr
              ⟨u, w, H.mem_edgeSet.mp hEdgeUV, rfl, rfl⟩)
          have hval :
              (PottsContinuity.PD.FK.embeddedEdgeEmbedding
                H PottsContinuity.PD.FK.squareLattice fP hGplane e).val =
                s(fP u, fP w) := by
            rw [PottsContinuity.PD.FK.embeddedEdgeEmbedding_coe]
            change Sym2.map fP e.val = s(fP u, fP w)
            rw [heuw]
            rfl
          apply (PottsContinuity.PD.RCInfinite.rcInfiniteOpenGraph_adj
            ω (fP u) (fP w)).mpr
          refine ⟨PottsContinuity.PD.FK.squareLattice.mem_edgeSet.mpr hAdj, ?_⟩
          have heq :
              PottsContinuity.PD.FK.embeddedEdgeEmbedding
                  H PottsContinuity.PD.FK.squareLattice fP hGplane e =
                ⟨s(fP u, fP w),
                  PottsContinuity.PD.FK.squareLattice.mem_edgeSet.mpr hAdj⟩ :=
            Subtype.ext hval
          rw [heq] at hstate
          exact hstate
        let hom : PottsContinuity.FKC.FiniteFK.openGraph H cfg →g
            PottsContinuity.PD.rcInfiniteOpenGraph ω :=
          { toFun := fP
            map_rel' := by
              intro u w huw
              exact hOpen huw }
        have hreach := (path.map hom).reachable
        have hstart : fP ⟨slitBoxBottomCenterVertex (16 * m),
            hcap (screenTargetCap_bottomCenter_mem m)⟩ =
              (0, -(16 * (m : ℤ))) := rfl
        let z : PottsContinuity.PD.FK.LatticeVertex :=
          (v.val.val.1, v.val.val.2 + 16 * (m : ℤ))
        have hvCoords := hv
        change -(m : ℤ) ≤ v.val.val.1 ∧ v.val.val.1 ≤ (m : ℤ) ∧
          -(16 * (m : ℤ)) ≤ v.val.val.2 ∧
            v.val.val.2 ≤ -(15 * (m : ℤ)) at hvCoords
        have hzx : |z.1| ≤ (m : ℤ) :=
          abs_le.mpr ⟨hvCoords.1, hvCoords.2.1⟩
        have hzy0 : 0 ≤ z.2 := by dsimp [z]; omega
        have hzym : z.2 ≤ (m : ℤ) := by dsimp [z]; omega
        have hmax : max |z.1| |z.2| = (m : ℤ) := by
          rcases hb with hside | htop
          · have hzx' : |z.1| = (m : ℤ) := by simpa [z] using hside
            rw [hzx']
            exact max_eq_left (abs_le.mpr (by omega))
          · have hzy' : |z.2| = (m : ℤ) := by
              rw [abs_of_nonneg hzy0]
              dsimp [z]
              omega
            rw [hzy']
            exact max_eq_right hzx
        have hzBoundary : z ∈
            PottsContinuity.vertexBoundary
              (PottsContinuity.box m) := by
          rw [PottsContinuity.Foundations.vertexBoundary_box_eq]
          exact hmax
        have hboundary : v.val.val ∈
            PottsContinuity.PD.FK.latticeTranslate
              (0, -(16 * (m : ℤ))) ''
              PottsContinuity.vertexBoundary
                (PottsContinuity.box m) := by
          have htranslate :
              PottsContinuity.PD.FK.latticeTranslate
                (0, -(16 * (m : ℤ))) z = v.val.val := by
            simp [PottsContinuity.PD.FK.latticeTranslate, z]
          exact ⟨z, hzBoundary, htranslate⟩
        change ∃ y ∈ PottsContinuity.PD.FK.latticeTranslate
            (0, -(16 * (m : ℤ))) ''
              PottsContinuity.vertexBoundary
                (PottsContinuity.box m),
          (PottsContinuity.PD.rcInfiniteOpenGraph ω).Reachable
            (0, -(16 * (m : ℤ))) y
        have hreach' :
            (PottsContinuity.PD.rcInfiniteOpenGraph ω).Reachable
              (0, -(16 * (m : ℤ))) (fP v) := by
          simpa [hom, hstart] using hreach
        exact ⟨fP v, hboundary, hreach'⟩)
  have hsourceMeasure :
      (finiteStatisticConditionalPMF
        (PottsContinuity.PD.FK.law G θ ξ)
        (fun A => (PottsContinuity.PD.FK.law_pos G θ ξ A).ne')
        r y).toMeasure (generalEScreenEvent (16 * m)) ≤
      (finiteStatisticConditionalPMF
        (PottsContinuity.PD.FK.law G θ ξ)
        (fun A => (PottsContinuity.PD.FK.law_pos G θ ξ A).ne')
        r y).toMeasure
          ((PottsContinuity.PD.FK.embeddedConfigurationRestriction
            H G f hGH) ⁻¹' E) :=
    measure_mono hsource
  have hsourceReal := ENNReal.toReal_mono
    (measure_ne_top ((finiteStatisticConditionalPMF
      (PottsContinuity.PD.FK.law G θ ξ)
      (fun A => (PottsContinuity.PD.FK.law_pos G θ ξ A).ne') r y).toMeasure) _)
    hsourceMeasure
  exact hsourceReal.trans (hconditional.trans hfinite)

/-- The joint slit-screen event with both side crossings and the connector is
bounded by the translated free-plane box event. -/
theorem slitScreen_joint_connector_probability_le_free_plane
    (q : Set.Icc (1 : ℝ) 4) (m : ℕ) (hm : 1 ≤ m)
    (p : Set.Icc (0 : ℝ) 1)
    (hp : (p : ℝ) = Real.sqrt q / (1 + Real.sqrt q))
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : PottsContinuity.IsRCInfiniteVolumeLimit p
      ⟨(q : ℝ), lt_of_lt_of_le one_pos q.2.1⟩ 0 μ) :
    (slitScreenFiniteMeasure q m).real
      (slitScreenEvent m ∩
        (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m) ∩
          slitScreenConnectorEvent m) ≤
      μ.real (translatedBoxBoundaryConnectionEvent (0, -(16 * (m : ℤ))) m) := by
  classical
  let qI : Set.Ici (1 : ℝ) := ⟨q, q.2.1⟩
  let G := slitBoxGraph (16 * m)
  let θ := PottsContinuity.PD.FK.criticalParameters qI
  let ξ := PottsContinuity.Thm4.fkcBoundaryToPD (slitBoxBoundary (16 * m))
  let law := PottsContinuity.PD.FK.law G θ ξ
  let S : Set (Configuration G) := {A | screenBoundaryClusterGood m A}
  let E := generalEScreenEvent (16 * m)
  let r := boundaryClusterStatistic (G := G)
    (slitBoxWiredArc (16 * m) : Set (SlitBoxVertex (16 * m)))
  let c := μ.real (centeredBoxBoundaryConnectionEvent m)
  have hp0 : 0 < (p : ℝ) := by
    rw [hp]
    exact div_pos (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one q.2.1)) (by positivity)
  have hp1 : (p : ℝ) < 1 := by
    rw [hp]
    have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by linarith [q.2.1])
    have hd : 0 < 1 + Real.sqrt (q : ℝ) := by linarith
    exact (div_lt_one hd).2 (by linarith)
  have hpmf : ∀ A, law A ≠ 0 := fun A =>
    (PottsContinuity.PD.FK.law_pos G θ ξ A).ne'
  have hstable : ∀ A B, r A = r B → (A ∈ S ↔ B ∈ S) := by
    intro A B hrecord
    exact screenBoundaryClusterGood_stable_on_statistic_fiber m A B hrecord.symm
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hc1 : c ≤ 1 := by
    have hmass : μ (centeredBoxBoundaryConnectionEvent m) ≤ 1 := by
      calc
        μ (centeredBoxBoundaryConnectionEvent m) ≤ μ Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := hμ.1.measure_univ
    simpa [c, Measure.real_def] using
      ENNReal.toReal_mono ENNReal.one_ne_top hmass
  have hcond : ∀ y : Set.range r,
      (∃ A, r A = y.1 ∧ A ∈ S) →
        1 - c ≤
          ((finiteStatisticConditionalPMF law hpmf r y).toMeasure Eᶜ).toReal := by
    intro y hy
    obtain ⟨A, hAy, hAS⟩ := hy
    have hcap := screenBoundaryClusterConditionedCapEvent_le_freePlane
      q m p hp hp0 hp1 μ hμ A hAS
    let yA : Set.range r := ⟨r A, ⟨A, rfl⟩⟩
    have hrecord : y = yA := Subtype.ext hAy.symm
    have hcap' :
        ((finiteStatisticConditionalPMF law hpmf r y).toMeasure E).toReal ≤ c := by
      rw [hrecord]
      simpa [law, θ, ξ, G, r, E, c, qI] using hcap
    let ν := (finiteStatisticConditionalPMF law hpmf r y).toMeasure
    have hsum : (ν E).toReal + (ν Eᶜ).toReal = 1 := by
      simpa [ν, Measure.real] using
        (MeasureTheory.probReal_add_probReal_compl (μ := ν) (s := E)
          (MeasurableSet.of_discrete (s := E)))
    linarith [hcap']
  have hlow := PottsContinuity.FKC.FiniteFK.finiteConditional_event_lower_bound_on_good_fibers
    law hpmf r S Eᶜ (1 - c) hstable (by linarith) (by linarith) hcond
  have hdiff : S \ E = S ∩ Eᶜ := by
    ext A
    simp
  have hlow' : (1 - c) * (law.toMeasure S).toReal ≤
      (law.toMeasure (S \ E)).toReal := by
    rw [hdiff]
    exact hlow
  have hparts : (law.toMeasure (S ∩ E)).toReal +
      (law.toMeasure (S \ E)).toReal = (law.toMeasure S).toReal := by
    have hmeasureParts : law.toMeasure (S ∩ E) + law.toMeasure (S \ E) =
        law.toMeasure S :=
      MeasureTheory.measure_inter_add_sdiff S
        (MeasurableSet.of_discrete (s := E)) (μ := law.toMeasure)
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hmeasureParts]
  have hupper' : (law.toMeasure (S ∩ E)).toReal ≤
      c * (law.toMeasure S).toReal := by
    linarith [hlow', hparts]
  have hSprob : (law.toMeasure S).toReal ≤ 1 := MeasureTheory.measureReal_le_one
  have hgood_event :
      slitScreenEvent m ∩
          (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m) ∩
            slitScreenConnectorEvent m ⊆ S ∩ E := by
    intro A hA
    rcases hA with ⟨⟨hscreen, _hcrossings⟩, hconnector⟩
    have hE : A ∈ E := by
      dsimp [E]
      rw [generalEScreenEvent_sixteen_eq]
      exact hscreen
    have hGood : A ∈ S := by
      apply screenTargetCap_subset_boundaryClusterInterior_of_sourceScreen_and_connector
        m hm A hE hconnector
    exact ⟨hGood, hE⟩
  have hsubsetProb :
      (law.toMeasure
        (slitScreenEvent m ∩
          (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m) ∩
            slitScreenConnectorEvent m)).toReal ≤
        (law.toMeasure (S ∩ E)).toReal := by
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono hgood_event)
  have hparam :
      PottsContinuity.Thm4.selfDualParameters qI = θ := by
    rfl
  have hmeasure : slitScreenFiniteMeasure q m = law.toMeasure := by
    simp [slitScreenFiniteMeasure, law, θ, ξ, G, qI, hparam,
      PottsContinuity.PD.FK.measure]
  have hbound : (slitScreenFiniteMeasure q m).real
      (slitScreenEvent m ∩
        (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m) ∩
          slitScreenConnectorEvent m) ≤ c := by
    rw [hmeasure, Measure.real_def]
    exact hsubsetProb.trans (hupper'.trans
      (by simpa using mul_le_mul_of_nonneg_left hSprob hc0))
  have htranslate := translatedBoxBoundaryConnection_probability_eq
    p ⟨q, lt_of_lt_of_le one_pos q.2.1⟩ q.2.1 μ hμ
      (0, -(16 * (m : ℤ))) m
  exact hbound.trans_eq htranslate.symm

end
end PottsContinuity.Thm4Plane
