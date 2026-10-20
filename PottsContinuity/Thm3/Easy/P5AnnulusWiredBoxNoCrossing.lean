module

public import PottsContinuity.DualityExt.AnnulusWiredBoxDMP
public import PottsContinuity.Infinite.FiniteGraphDMP
public import PottsContinuity.PD.RCInfinite.FiniteConditioning

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open MeasureTheory
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.Infinite
open PottsContinuity.DualityExt

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance p5BoxConfigFintype {V : Type*} [Finite V] (G : SimpleGraph V) :
    Fintype (Configuration G) := Fintype.ofFinite _

local instance p5BoxConfigDecidableEq {V : Type*} [Finite V]
    (G : SimpleGraph V) : DecidableEq (Configuration G) := Classical.decEq _

private theorem inducedPullbackBoundary_le_wired_noGap
    (S U : Finset LatticeVertex) (hSU : S ⊆ U)
    (K : RemovedConfiguration (finiteLatticeGraph U)
      (subgraphRemovedEdges
        ((finiteLatticeGraph S).map (finiteLatticeVertexEmbedding hSU))
        (finiteLatticeGraph U))) :
    (isolatedExtensionPullbackBoundary (finiteLatticeVertexEmbedding hSU)
      (frozenBoundary (frozenBoundaryCondition U 1) K.val)).partition ≤
      (frozenBoundaryCondition S 1).partition := by
  classical
  let G := finiteLatticeGraph S
  let H := finiteLatticeGraph U
  let f := finiteLatticeVertexEmbedding hSU
  let R := subgraphRemovedEdges (G.map f) H
  let external : Set (U : Set LatticeVertex) :=
    {x | x.val ∈ PottsContinuity.PD.vertexBoundary S ∨
      x.val ∉ (S : Set LatticeVertex)}
  let rel : Setoid (U : Set LatticeVertex) := {
    r := fun x y => x = y ∨ (x ∈ external ∧ y ∈ external)
    iseqv := {
      refl := fun x => Or.inl rfl
      symm := by
        intro x y h
        rcases h with h | ⟨hx, hy⟩
        · exact Or.inl h.symm
        · exact Or.inr ⟨hy, hx⟩
      trans := by
        intro x y z hxy hyz
        rcases hxy with rfl | ⟨hx, hy⟩
        · exact hyz
        · rcases hyz with rfl | ⟨_, hz⟩
          · exact Or.inr ⟨hx, hy⟩
          · exact Or.inr ⟨hx, hz⟩
    }
  }
  have hboundaryOuter : (frozenBoundaryCondition U 1).partition ≤ rel := by
    intro x y hxy
    have hwire : (BoundaryCondition.wired (frozenVertexBoundary U)).partition x y := by
      exact hxy
    have hxy' := (BoundaryCondition.wired_rel (frozenVertexBoundary U) x y).mp hwire
    rcases hxy' with hxy' | ⟨hx, hy⟩
    · exact Or.inl hxy'
    · right
      constructor
      · by_cases hxS : x.val ∈ S
        · left
          change x.val ∈ PottsContinuity.PD.vertexBoundary U at hx
          change x.val ∈ PottsContinuity.PD.vertexBoundary S
          rcases hx with ⟨_, z, hAdj, hz⟩
          exact ⟨hxS, z, hAdj, fun hzS => hz (hSU hzS)⟩
        · exact Or.inr (by simpa [external] using hxS)
      · by_cases hyS : y.val ∈ S
        · left
          change y.val ∈ PottsContinuity.PD.vertexBoundary U at hy
          change y.val ∈ PottsContinuity.PD.vertexBoundary S
          rcases hy with ⟨_, z, hAdj, hz⟩
          exact ⟨hyS, z, hAdj, fun hzS => hz (hSU hzS)⟩
        · exact Or.inr (by simpa [external] using hyS)
  have hopen : ∀ {x y : (U : Set LatticeVertex)},
      ActualConnected H K.val x y → rel.r x y := by
    intro x y hxy
    have hreach : (openGraph H K.val).reachableSetoid ≤ rel := by
      apply reachableSetoid_le_of_adj
      intro a b hab
      have hadj : H.Adj a b := openGraph_le H K.val hab
      have hopen' := (openGraph_adj H K.val a b).mp hab
      obtain ⟨e, heK, heval⟩ := hopen'
      have heR : e ∈ R := K.property heK
      have heOutside : e.val ∉ (G.map f).edgeSet :=
        (mem_subgraphRemovedEdges e).mp heR
      have hAdjLattice : squareLattice.Adj a.val b.val := hadj
      have haExt : a ∈ external := by
        by_cases haS : a.val ∈ S
        · by_cases haB : a.val ∈ PottsContinuity.PD.vertexBoundary S
          · exact Or.inl haB
          · exfalso
            have hbS : b.val ∈ S := by
              by_contra hbS
              apply haB
              exact ⟨haS, b.val, hAdjLattice, hbS⟩
            let xS : (S : Set LatticeVertex) := ⟨a.val, haS⟩
            let yS : (S : Set LatticeVertex) := ⟨b.val, hbS⟩
            have hfx : f xS = a := by
              apply Subtype.ext
              rfl
            have hfy : f yS = b := by
              apply Subtype.ext
              rfl
            have hGxy : G.Adj xS yS := hAdjLattice
            have hy : (G.map f).Adj a b := by
              have hmap : (G.map f).Adj (f xS) (f yS) :=
                (SimpleGraph.map_adj f G (f xS) (f yS)).mpr
                  ⟨xS, yS, hGxy, rfl, rfl⟩
              simpa only [hfx, hfy] using hmap
            apply heOutside
            rw [heval]
            exact (G.map f).mem_edgeSet.mpr hy
        · exact Or.inr haS
      have hbExt : b ∈ external := by
        by_cases hbS : b.val ∈ S
        · by_cases hbB : b.val ∈ PottsContinuity.PD.vertexBoundary S
          · exact Or.inl hbB
          · exfalso
            have haS : a.val ∈ S := by
              by_contra haS
              apply hbB
              exact ⟨hbS, a.val, hAdjLattice.symm, haS⟩
            let xS : (S : Set LatticeVertex) := ⟨a.val, haS⟩
            let yS : (S : Set LatticeVertex) := ⟨b.val, hbS⟩
            have hfx : f xS = a := by
              apply Subtype.ext
              rfl
            have hfy : f yS = b := by
              apply Subtype.ext
              rfl
            have hGxy : G.Adj xS yS := hAdjLattice
            have hy : (G.map f).Adj a b := by
              have hmap : (G.map f).Adj (f xS) (f yS) :=
                (SimpleGraph.map_adj f G (f xS) (f yS)).mpr
                  ⟨xS, yS, hGxy, rfl, rfl⟩
              simpa only [hfx, hfy] using hmap
            apply heOutside
            rw [heval]
            exact (G.map f).mem_edgeSet.mpr hy
        · exact Or.inr hbS
      exact Or.inr ⟨haExt, hbExt⟩
    exact hreach hxy
  have hboundary : (frozenBoundary (frozenBoundaryCondition U 1) K.val).partition ≤ rel := by
    change componentSetoid H (frozenBoundaryCondition U 1) K.val ≤ rel
    exact componentSetoid_le H (frozenBoundaryCondition U 1) K.val rel hopen hboundaryOuter
  intro x y hxy
  have hxy' : rel.r (f x) (f y) := by
    exact hboundary ((Setoid.comap_rel f
      (frozenBoundary (frozenBoundaryCondition U 1) K.val).partition x y).mp hxy)
  rcases hxy' with hxy' | ⟨hx, hy⟩
  · exact Or.inl (f.injective hxy')
  · have hxB : x.val ∈ PottsContinuity.PD.vertexBoundary S := by
      rcases hx with hx | hx
      · exact hx
      · exact (hx x.property).elim
    have hyB : y.val ∈ PottsContinuity.PD.vertexBoundary S := by
      rcases hy with hy | hy
      · exact hy
      · exact (hy y.property).elim
    have hxB' : x ∈ frozenVertexBoundary S := by
      simpa [frozenVertexBoundary] using hxB
    have hyB' : y ∈ frozenVertexBoundary S := by
      simpa [frozenVertexBoundary] using hyB
    exact (BoundaryCondition.wired_rel (frozenVertexBoundary S) x y).mpr
      (Or.inr ⟨hxB', hyB'⟩)

theorem annulus_wired_noCrossing_le_wiredBox_noCrossing_at_touchingBoundary
    (θ : Parameters) (N M : ℕ) (hN : 1 ≤ N) (hNM : 2 * N ≤ M) :
    (measure (annulusSourceGraph N) θ
      (BoundaryCondition.wired {x | x.1 ∈ PottsContinuity.PD.vertexBoundary
        (annulusVertexSet N)})
      (annulusSourceFullBoxCrossingEvent N)ᶜ).toReal ≤
    (boxMeasure θ 1 (0, 0) M : Measure LatticeConfiguration).real
      ({ω | annulusOpenCrossing N ω}ᶜ) := by
  let S := annulusVertexSet N
  let U := latticeBox (0, 0) M
  have hSbox : S ⊆ latticeBox (0, 0) (2 * N) := by
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1
  have hSU : S ⊆ U := Finset.Subset.trans hSbox
    (latticeBox_mono (0, 0) hNM)
  let f := finiteLatticeVertexEmbedding hSU
  have hGH : (finiteLatticeGraph S).map f ≤ finiteLatticeGraph U :=
    finiteLatticeGraph_map_le hSU
  let A : Set (Configuration (finiteLatticeGraph S)) := annulusSourceFullBoxCrossingEvent N
  have hA : IsUpperSet A := by
    change IsUpperSet (annulusSourceFullBoxCrossingEvent N)
    intro C D hCD hC
    rcases hC with ⟨u, v, hu, hv, hconn⟩
    exact ⟨u, v, hu, hv, actualConnected_mono (by simpa using hCD) hconn⟩
  have hcmp := embedded_joint_le_boundary_order
    (finiteLatticeGraph S) (finiteLatticeGraph U) f hGH θ
    (frozenBoundaryCondition U 1) (frozenBoundaryCondition S 1) A hA
    (fun K => inducedPullbackBoundary_le_wired_noGap S U hSU K) Set.univ
  have hcmp' :
      (measure (finiteLatticeGraph U) θ (frozenBoundaryCondition U 1)
        (embeddedConfigurationRestriction (finiteLatticeGraph S)
          (finiteLatticeGraph U) f hGH ⁻¹' A)).toReal ≤
      (measure (finiteLatticeGraph S) θ (frozenBoundaryCondition S 1) A).toReal := by
    simpa [embeddedOutsideState] using hcmp
  have hbcS : (frozenBoundaryCondition S 1).partition =
      (BoundaryCondition.wired {x | x.1 ∈ PottsContinuity.PD.vertexBoundary S}).partition := by
    simp [S, frozenBoundaryCondition, frozenVertexBoundary]
  have hbcU : (frozenBoundaryCondition U 1).partition =
      (boxBoundary 1 (0, 0) M).partition := by
    dsimp [U, frozenBoundaryCondition, frozenVertexBoundary, boxBoundary, boxVertexBoundary]
  have hf : finiteLatticeVertexEmbedding hSU = annulusToBoxVertex N M (by omega) := by
    rfl
  have hRestriction : embeddedConfigurationRestriction (finiteLatticeGraph S)
      (finiteLatticeGraph U) f hGH =
      embeddedConfigurationRestriction (annulusSourceGraph N) (boxGraph (0, 0) M)
        (annulusToBoxVertex N M (by omega))
        (annulusSourceGraph_map_le_boxGraph N M (by omega)) := by
    rfl
  have hEvDmp :
      (boxExtension 1 (0, 0) M) ⁻¹' {ω | annulusOpenCrossing N ω} =
      (embeddedConfigurationRestriction (finiteLatticeGraph S)
        (finiteLatticeGraph U) f hGH ⁻¹' A) := by
    ext C
    change annulusOpenCrossing N (boxExtension 1 (0, 0) M C) ↔
      annulusSourceFullBoxCrossingEvent N
        (embeddedConfigurationRestriction (finiteLatticeGraph S)
          (finiteLatticeGraph U) f hGH C)
    rw [annulusOpenCrossing_iff_sourcePlaneRestriction N hN]
    change annulusSourceFullBoxCrossingEvent N
      (annulusSourcePlaneConfiguration N (boxExtension 1 (0, 0) M C)) ↔ _
    rw [annulusSourcePlaneRestriction_eq_boxRestriction N M (by omega) C]
    rw [← hRestriction]
  have hL : law (finiteLatticeGraph U) θ (frozenBoundaryCondition U 1) =
      law (boxGraph (0, 0) M) θ (boxBoundary 1 (0, 0) M) := by
    dsimp [U, frozenBoundaryCondition, finiteLatticeGraph, boxGraph]
    apply law_eq_of_boundary_partition_eq
    exact hbcU
  have hmeasure :
      (measure (finiteLatticeGraph U) θ (frozenBoundaryCondition U 1)
        (embeddedConfigurationRestriction (finiteLatticeGraph S)
          (finiteLatticeGraph U) f hGH ⁻¹' A)).toReal =
      (boxMeasure θ 1 (0, 0) M : Measure LatticeConfiguration).real
        {ω | annulusOpenCrossing N ω} := by
    rw [Measure.real_def]
    rw [boxMeasure_apply θ 1 (0, 0) M
      (annulusOpenCrossing_isCylinder N hN).measurableSet]
    change ((law (finiteLatticeGraph U) θ (frozenBoundaryCondition U 1)).toMeasure
        (embeddedConfigurationRestriction (finiteLatticeGraph S)
          (finiteLatticeGraph U) f hGH ⁻¹' A)).toReal =
      ((law (boxGraph (0, 0) M) θ (boxBoundary 1 (0, 0) M)).toMeasure
        ((boxExtension 1 (0, 0) M) ⁻¹' {ω | annulusOpenCrossing N ω})).toReal
    rw [← hL, hEvDmp]
    rfl
  have hLS : law (finiteLatticeGraph S) θ (frozenBoundaryCondition S 1) =
      law (annulusSourceGraph N) θ
        (BoundaryCondition.wired {x | x.1 ∈ PottsContinuity.PD.vertexBoundary S}) := by
    dsimp [S, finiteLatticeGraph, annulusSourceGraph]
    apply law_eq_of_boundary_partition_eq
    simp [frozenBoundaryCondition, frozenVertexBoundary]
  have hcross :
      (boxMeasure θ 1 (0, 0) M : Measure LatticeConfiguration).real
        {ω | annulusOpenCrossing N ω} ≤
      (measure (annulusSourceGraph N) θ
        (BoundaryCondition.wired {x | x.1 ∈ PottsContinuity.PD.vertexBoundary
          (annulusVertexSet N)}) (annulusSourceFullBoxCrossingEvent N)).toReal := by
    calc
      _ = (measure (finiteLatticeGraph U) θ (frozenBoundaryCondition U 1)
          (embeddedConfigurationRestriction (finiteLatticeGraph S)
            (finiteLatticeGraph U) f hGH ⁻¹' A)).toReal := hmeasure.symm
      _ ≤ (measure (finiteLatticeGraph S) θ (frozenBoundaryCondition S 1) A).toReal := hcmp'
      _ = (measure (annulusSourceGraph N) θ
          (BoundaryCondition.wired {x | x.1 ∈ PottsContinuity.PD.vertexBoundary
            (annulusVertexSet N)}) (annulusSourceFullBoxCrossingEvent N)).toReal := by
          change ((law (finiteLatticeGraph S) θ (frozenBoundaryCondition S 1)).toMeasure A).toReal = _
          rw [hLS]
          rfl
  have hsumS :
      (measure (annulusSourceGraph N) θ
        (BoundaryCondition.wired {x | x.1 ∈ PottsContinuity.PD.vertexBoundary
          (annulusVertexSet N)}) (annulusSourceFullBoxCrossingEvent N)).toReal +
      (measure (annulusSourceGraph N) θ
        (BoundaryCondition.wired {x | x.1 ∈ PottsContinuity.PD.vertexBoundary
          (annulusVertexSet N)}) (annulusSourceFullBoxCrossingEvent N)ᶜ).toReal = 1 := by
    simpa [Measure.real_def] using measureReal_add_measureReal_compl
      (μ := measure (annulusSourceGraph N) θ
        (BoundaryCondition.wired {x | x.1 ∈ PottsContinuity.PD.vertexBoundary
          (annulusVertexSet N)}))
      (Set.toFinite _).measurableSet
  have hsumBox :
      (boxMeasure θ 1 (0, 0) M : Measure LatticeConfiguration).real
        {ω | annulusOpenCrossing N ω} +
      (boxMeasure θ 1 (0, 0) M : Measure LatticeConfiguration).real
        ({ω | annulusOpenCrossing N ω}ᶜ) = 1 := by
    simpa [Measure.real_def] using measureReal_add_measureReal_compl
      (μ := (boxMeasure θ 1 (0, 0) M : Measure LatticeConfiguration))
      (annulusOpenCrossing_isCylinder N hN).measurableSet
  linarith

end

end PottsContinuity.Thm3.Easy
