module

public import PottsContinuity.Infinite.FiniteGraphDMP
public import PottsContinuity.PD.RCInfinite.SubgraphExhaustion

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped symmDiff

namespace PottsContinuity.Infinite

open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

local instance inducedDMPEdgeFintype {V : Type*} [Finite V] (G : SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite _
local instance inducedDMPEdgeDecidableEq {V : Type*} [Finite V]
    (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

private theorem inducedDMP_inter_symmDiff_subset_right
    (A B C : Set LatticeConfiguration) :
    (A ∩ B) ∆ (A ∩ C) ⊆ B ∆ C := by
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_inter_iff] at hx ⊢
  tauto

private theorem inducedDMP_measureReal_symmDiff_lt_of_ennreal
    (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ]
    {A B : Set LatticeConfiguration} (δ : ℝ) (hδ : 0 < δ)
    (hAB : μ (A ∆ B) < ENNReal.ofReal δ) : μ.real (A ∆ B) < δ := by
  have h := (ENNReal.toReal_lt_toReal (by finiteness) ENNReal.ofReal_ne_top).2 hAB
  simpa [Measure.real_def, ENNReal.toReal_ofReal (le_of_lt hδ)] using h

private theorem inducedDMP_abs_measureReal_inter_sub_le
    (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ]
    {A B C : Set LatticeConfiguration} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    |μ.real (A ∩ B) - μ.real (A ∩ C)| ≤ μ.real (B ∆ C) := by
  calc
    |μ.real (A ∩ B) - μ.real (A ∩ C)| ≤
        μ.real ((A ∩ B) ∆ (A ∩ C)) :=
      abs_measureReal_sub_le_measureReal_symmDiff
        (hA.inter hB).nullMeasurableSet (hA.inter hC).nullMeasurableSet
    _ ≤ μ.real (B ∆ C) :=
      measureReal_mono (inducedDMP_inter_symmDiff_subset_right A B C)

private theorem mappedEdgeEmbedding_factor {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
    (hGH : G.map f ≤ H) (e : (G.map f).edgeSet) :
    ∃ e₀ : G.edgeSet,
      embeddedEdgeEmbedding G H f hGH e₀ = subgraphEdgeEmbedding hGH e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab : (G.map f).Adj a b := (G.map f).mem_edgeSet.mp he
      obtain ⟨x, y, hxy, rfl, rfl⟩ := (SimpleGraph.map_adj f G a b).mp hab
      refine ⟨⟨s(x, y), G.mem_edgeSet.mpr hxy⟩, ?_⟩
      apply Subtype.ext
      rfl

theorem latticeBox_adj_mem_succ {r : ℕ} {x y : LatticeVertex}
    (hx : x ∈ latticeBox (0, 0) r) (hxy : squareLattice.Adj x y) :
    y ∈ latticeBox (0, 0) (r + 1) := by
  have hx' := (mem_latticeBox (0, 0) x r).mp hx
  simp only [zero_sub, zero_add] at hx'
  rw [mem_latticeBox]
  simp only [zero_sub, zero_add]
  have hxy' := (squareLattice_adj_iff x y).mp hxy
  omega

theorem finite_set_misses_outer_box_boundary
    (S : Finset LatticeVertex) (r n : ℕ)
    (hS : S ⊆ latticeBox (0, 0) r) (hr : r + 1 ≤ n) :
    Disjoint (S : Set LatticeVertex)
      (PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) n)) := by
  apply Set.disjoint_left.mpr
  intro x hx hxbd
  rcases hxbd with ⟨_, y, hxy, hyout⟩
  have hxbox : x ∈ latticeBox (0, 0) r := hS hx
  have hybox := latticeBox_adj_mem_succ hxbox hxy
  exact hyout (latticeBox_mono (0, 0) hr hybox)

private theorem outerBoxEdge_not_mapped_inner
    (S : Finset LatticeVertex) (n : ℕ) (hSU : S ⊆ latticeBox (0, 0) n)
    (e : (boxGraph (0, 0) n).edgeSet)
    (he : boxEdgeEmbedding (0, 0) n e ∉ Set.range (frozenEdgeEmbedding S)) :
    e ∈ subgraphRemovedEdges
      ((finiteLatticeGraph S).map (finiteLatticeVertexEmbedding hSU))
      (boxGraph (0, 0) n) := by
  rw [mem_subgraphRemovedEdges]
  intro hemap
  let G := finiteLatticeGraph S
  let H := boxGraph (0, 0) n
  let f := finiteLatticeVertexEmbedding hSU
  let hGH : G.map f ≤ H := finiteLatticeGraph_map_le hSU
  obtain ⟨e₀, he₀⟩ := mappedEdgeEmbedding_factor G H f hGH ⟨e.val, hemap⟩
  let fGlobal : (S : Set LatticeVertex) ↪ LatticeVertex := ⟨Subtype.val, Subtype.val_injective⟩
  have hG : G.map fGlobal ≤ squareLattice := by
    intro x y hxy
    rw [SimpleGraph.map_adj] at hxy
    rcases hxy with ⟨a, b, hab, rfl, rfl⟩
    exact hab
  have hV : ∀ v : (S : Set LatticeVertex), fGlobal v ∈ latticeBox (0, 0) n :=
    fun v => hSU v.property
  have hfb : ∀ v : (S : Set LatticeVertex), (f v).val = fGlobal v := fun _ => rfl
  have hcompat := boxEdgeEmbedding_compatible_finiteGraph G fGlobal hG n hV f hfb hGH e₀
  have htarget : embeddedEdgeEmbedding G squareLattice fGlobal hG e₀ =
      frozenEdgeEmbedding S e₀ := by
    apply Subtype.ext
    rfl
  have heq : embeddedEdgeEmbedding G H f hGH e₀ = e := by
    apply Subtype.ext
    exact congrArg Subtype.val he₀
  have hrange : frozenEdgeEmbedding S e₀ = boxEdgeEmbedding (0, 0) n e :=
    htarget.symm.trans (hcompat.symm.trans (congrArg (boxEdgeEmbedding (0, 0) n) heq))
  exact he ⟨e₀, hrange⟩

private theorem boxExtension_agrees_at_removed_edge
    (i : Fin 2) (S : Finset LatticeVertex) (n : ℕ)
    (hSU : S ⊆ latticeBox (0, 0) n)
    (C : Configuration (boxGraph (0, 0) n))
    (e : (boxGraph (0, 0) n).edgeSet)
    (he : e ∈ subgraphRemovedEdges
      ((finiteLatticeGraph S).map (finiteLatticeVertexEmbedding hSU))
      (boxGraph (0, 0) n)) :
    boxExtension i (0, 0) n C (boxEdgeEmbedding (0, 0) n e) =
      boxExtension i (0, 0) n
        (embeddedOutsideState (finiteLatticeGraph S) (boxGraph (0, 0) n)
          (finiteLatticeVertexEmbedding hSU) (finiteLatticeGraph_map_le hSU) C).val
        (boxEdgeEmbedding (0, 0) n e) := by
  classical
  rw [boxExtension_at, boxExtension_at]
  have hmem : e ∈ C ↔ e ∈ C ∩
      subgraphRemovedEdges
        ((finiteLatticeGraph S).map (finiteLatticeVertexEmbedding hSU))
        (boxGraph (0, 0) n) := by
    simp [he]
  change decide (e ∈ C) = decide (e ∈ C ∩
    subgraphRemovedEdges
      ((finiteLatticeGraph S).map (finiteLatticeVertexEmbedding hSU))
      (boxGraph (0, 0) n))
  by_cases hC : e ∈ C
  · have hCR := hmem.mp hC
    simp [hC, hCR]
  · have hCR : e ∉ C ∩
        subgraphRemovedEdges
          ((finiteLatticeGraph S).map (finiteLatticeVertexEmbedding hSU))
          (boxGraph (0, 0) n) := fun hh => hC (Finset.mem_inter.mp hh).1
    simp [hC, hCR]

private theorem inducedDMP_edgeSigma_measurable_dependsOn (E : Set Edge)
    {B : Set LatticeConfiguration} (hB : MeasurableSet[edgeSigma E] B) :
    DependsOn E B := by
  refine MeasurableSpace.generateFrom_induction
    (C := {S | SupportedCylinder E S})
    (p := fun S _ => DependsOn E S) ?_ ?_ ?_ ?_ B hB
  · intro S hS hmeas
    exact hS.dependsOn
  · intro ω η hω
    exact Iff.rfl
  · intro S hS hdep ω η hω
    exact hdep.compl ω η hω
  · intro S hS hdep ω η hω
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨i, hx⟩ => ⟨i, (hdep i ω η hω).mp hx⟩,
      fun ⟨i, hx⟩ => ⟨i, (hdep i ω η hω).mpr hx⟩⟩

/-- Wired DMP for a finite induced domain and an exterior-supported cylinder.
The local event is carried by the finite induced graph itself. -/
theorem wired_infinite_DMP_induced_supportedCylinder
    (θ : PottsContinuity.PD.FK.Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : PottsContinuity.PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (S : Finset LatticeVertex)
    (A : Set (Configuration (finiteLatticeGraph S))) (hA : IsUpperSet A)
    (B : Set LatticeConfiguration)
    (hB : SupportedCylinder (Set.range (frozenEdgeEmbedding S))ᶜ B) :
    μ.real (latticeGraphEvent (finiteLatticeGraph S)
      ⟨Subtype.val, Subtype.val_injective⟩ (by
        intro x y hxy
        rw [SimpleGraph.map_adj] at hxy
        rcases hxy with ⟨a, b, hab, rfl, rfl⟩
        exact hab) A ∩ B) ≤
      (measure (finiteLatticeGraph S) θ (frozenBoundaryCondition S 1) A).toReal *
        μ.real B := by
  classical
  let G := finiteLatticeGraph S
  let fGlobal : (S : Set LatticeVertex) ↪ LatticeVertex :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hG : G.map fGlobal ≤ squareLattice := by
    intro x y hxy
    rw [SimpleGraph.map_adj] at hxy
    rcases hxy with ⟨a, b, hab, rfl, rfl⟩
    exact hab
  let Ainf := latticeGraphEvent G fGlobal hG A
  have hAcy : IsCylinder Ainf := latticeGraphEvent_isCylinder G fGlobal hG A
  have hBcy : IsCylinder B := hB.isCylinder
  have hABcy : IsCylinder (Ainf ∩ B) := hAcy.inter hBcy
  have hμAB := tendsto_cylinder_probability θ 1 μ hμ hABcy
  have hμB := tendsto_cylinder_probability θ 1 μ hμ hBcy
  let c : ℝ := (measure G θ (frozenBoundaryCondition S 1) A).toReal
  have hright : Tendsto
      (fun n => c * (boxMeasure θ 1 (0, 0) n : Measure LatticeConfiguration).real B)
      atTop (𝓝 (c * μ.real B)) := tendsto_const_nhds.mul hμB
  apply le_of_tendsto_of_tendsto hμAB hright
  obtain ⟨F, hFout, hFdep⟩ := hB
  obtain ⟨rF, hrF⟩ := exists_box_supporting_edge_finset F
  let rS := subgraphBoxRadius S
  have hSbox : S ⊆ latticeBox (0, 0) rS := by
    intro x hx
    exact subgraph_subset_boxRadius S hx
  filter_upwards [eventually_ge_atTop (max rF (rS + 1))] with n hn
  have hrFn : rF ≤ n := le_trans (le_max_left _ _) hn
  have hrSn : rS + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hSU : S ⊆ latticeBox (0, 0) n := by
    exact hSbox.trans (latticeBox_mono (0, 0) (by omega))
  have houter := finite_set_misses_outer_box_boundary S rS n hSbox hrSn
  let U := latticeBox (0, 0) n
  let H := boxGraph (0, 0) n
  let fb := finiteLatticeVertexEmbedding hSU
  have hGH : G.map fb ≤ H := finiteLatticeGraph_map_le hSU
  let R := subgraphRemovedEdges (G.map fb) H
  let out : Configuration H → RemovedConfiguration H R :=
    embeddedOutsideState G H fb hGH
  let T : Set (RemovedConfiguration H R) :=
    {K | boxExtension 1 (0, 0) n K.val ∈ B}
  have hAbox : (boxExtension 1 (0, 0) n) ⁻¹' Ainf =
      (embeddedConfigurationRestriction G H fb hGH) ⁻¹' A := by
    ext C
    change latticeGraphRestriction G fGlobal hG (boxExtension 1 (0, 0) n C) ∈ A ↔
      embeddedConfigurationRestriction G H fb hGH C ∈ A
    have hV : ∀ v : (S : Set LatticeVertex), fGlobal v ∈ U :=
      fun v => hSU v.property
    have hfb : ∀ v : (S : Set LatticeVertex), (fb v).val = fGlobal v := fun _ => rfl
    rw [latticeGraphRestriction_boxExtension G fGlobal hG 1 n hV fb hfb hGH]
  have hBbox : (boxExtension 1 (0, 0) n) ⁻¹' B = out ⁻¹' T := by
    ext C
    change boxExtension 1 (0, 0) n C ∈ B ↔
      boxExtension 1 (0, 0) n (out C).val ∈ B
    apply hFdep
    intro e heF
    have heSmall : e ∈ boxEdges (0, 0) rF := hrF e heF
    have heRangeSmall : e ∈ Set.range (frozenEdgeEmbedding (latticeBox (0, 0) rF)) :=
      boxEdges_subset_frozenEdgeEmbedding_range rF heSmall
    have heRangeOuter : e ∈ Set.range (frozenEdgeEmbedding U) :=
      frozenEdgeEmbedding_range_mono (latticeBox_mono (0, 0) hrFn) heRangeSmall
    have hEmbed : frozenEdgeEmbedding U = boxEdgeEmbedding (0, 0) n := rfl
    rw [hEmbed] at heRangeOuter
    obtain ⟨eH, rfl⟩ := heRangeOuter
    have heNotInner : boxEdgeEmbedding (0, 0) n eH ∉ Set.range (frozenEdgeEmbedding S) :=
      fun hin => hFout heF hin
    have heRemoved := outerBoxEdge_not_mapped_inner S n hSU eH heNotInner
    exact boxExtension_agrees_at_removed_edge 1 S n hSU C eH heRemoved
  have hBoundary : boxBoundary 1 (0, 0) n = frozenBoundaryCondition U 1 := by
    rfl
  have hboxAB :
      (boxMeasure θ 1 (0, 0) n : Measure LatticeConfiguration).real (Ainf ∩ B) =
        (measure H θ (frozenBoundaryCondition U 1)
          (((embeddedConfigurationRestriction G H fb hGH) ⁻¹' A) ∩ out ⁻¹' T)).toReal := by
    have hboxEvent : (boxExtension 1 (0, 0) n) ⁻¹' (Ainf ∩ B) =
        ((embeddedConfigurationRestriction G H fb hGH) ⁻¹' A) ∩ out ⁻¹' T := by
      rw [preimage_inter, hAbox, hBbox]
    rw [Measure.real_def,
      boxMeasure_apply θ 1 (0, 0) n hABcy.measurableSet,
      hboxEvent, hBoundary]
  have hboxB :
      (boxMeasure θ 1 (0, 0) n : Measure LatticeConfiguration).real B =
        (measure H θ (frozenBoundaryCondition U 1) (out ⁻¹' T)).toReal := by
    rw [Measure.real_def, boxMeasure_apply θ 1 (0, 0) n hBcy.measurableSet,
      hBbox, hBoundary]
  have hpart : ∀ K : RemovedConfiguration H R,
      (isolatedExtensionPullbackBoundary fb
        (frozenBoundary (boxBoundary 1 (0, 0) n) K.val)).partition ≤
        (frozenBoundaryCondition S 1).partition := by
    intro K
    rw [hBoundary]
    exact finite_induced_pullback_boundary_le_wired S U hSU houter K
  have hfinite := embedded_joint_le_boundary_order G H fb hGH θ
    (boxBoundary 1 (0, 0) n) (frozenBoundaryCondition S 1) A hA hpart T
  have hfinite' :
      (measure H θ (frozenBoundaryCondition U 1)
        (((embeddedConfigurationRestriction G H fb hGH) ⁻¹' A) ∩ out ⁻¹' T)).toReal ≤
        c * (measure H θ (frozenBoundaryCondition U 1) (out ⁻¹' T)).toReal := by
    simpa [c, U, H, R, out, embeddedOutsideState, hBoundary] using hfinite
  rw [hboxAB]
  calc
    (measure H θ (frozenBoundaryCondition U 1)
      (((embeddedConfigurationRestriction G H fb hGH) ⁻¹' A) ∩ out ⁻¹' T)).toReal ≤
      c * (measure H θ (frozenBoundaryCondition U 1) (out ⁻¹' T)).toReal := hfinite'
    _ = c * (boxMeasure θ 1 (0, 0) n : Measure LatticeConfiguration).real B := by
      rw [hboxB]

/-- Wired DMP for arbitrary finite induced domains and all measurable events
of the exterior edge sigma-field. -/
theorem wired_infinite_DMP_induced_measurable
    (θ : PottsContinuity.PD.FK.Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : PottsContinuity.PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (S : Finset LatticeVertex)
    (A : Set (Configuration (finiteLatticeGraph S))) (hA : IsUpperSet A)
    (B : Set LatticeConfiguration)
    (hB : MeasurableSet[edgeSigma (Set.range (frozenEdgeEmbedding S))ᶜ] B) :
    μ.real (latticeGraphEvent (finiteLatticeGraph S)
      ⟨Subtype.val, Subtype.val_injective⟩ (by
        intro x y hxy
        rw [SimpleGraph.map_adj] at hxy
        rcases hxy with ⟨a, b, hab, rfl, rfl⟩
        exact hab) A ∩ B) ≤
      (measure (finiteLatticeGraph S) θ (frozenBoundaryCondition S 1) A).toReal *
        μ.real B := by
  classical
  have : IsProbabilityMeasure μ := hμ.1
  let G := finiteLatticeGraph S
  let fGlobal : (S : Set LatticeVertex) ↪ LatticeVertex :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hG : G.map fGlobal ≤ squareLattice := by
    intro x y hxy
    rw [SimpleGraph.map_adj] at hxy
    rcases hxy with ⟨a, b, hab, rfl, rfl⟩
    exact hab
  let Ainf := latticeGraphEvent G fGlobal hG A
  have hAcy : IsCylinder Ainf := latticeGraphEvent_isCylinder G fGlobal hG A
  have hBdep : DependsOn (Set.range (frozenEdgeEmbedding S))ᶜ B :=
    inducedDMP_edgeSigma_measurable_dependsOn _ hB
  have hBambient : MeasurableSet B := (edgeSigma_le _ B) hB
  by_contra hnot
  let w : ℝ := (measure G θ (frozenBoundaryCondition S 1) A).toReal
  let j : ℝ := μ.real (Ainf ∩ B)
  let b : ℝ := μ.real B
  have hgap : w * b < j := by
    dsimp [w, j, b] at hnot ⊢
    exact lt_of_not_ge hnot
  let δ : ℝ := (j - w * b) / 3
  have hδ : 0 < δ := div_pos (sub_pos.mpr hgap) (by norm_num)
  have hgapEq : j - w * b = 3 * δ := by dsimp [δ]; ring
  obtain ⟨C, hCsupport, hCB⟩ := exists_supportedCylinder_approx μ
    (Set.range (frozenEdgeEmbedding S))ᶜ hBambient hBdep
    (ENNReal.ofReal_pos.mpr hδ)
  have hCdep := hCsupport.dependsOn
  have hCcy : IsCylinder C := hCsupport.isCylinder
  have hCambient : MeasurableSet C := hCcy.measurableSet
  have herr : μ.real (B ∆ C) < δ := by
    apply inducedDMP_measureReal_symmDiff_lt_of_ennreal μ δ hδ
    simpa [symmDiff_comm] using hCB
  have hBabs : |μ.real B - μ.real C| ≤ μ.real (B ∆ C) :=
    abs_measureReal_sub_le_measureReal_symmDiff
      hBambient.nullMeasurableSet hCambient.nullMeasurableSet
  have hCupper : μ.real C ≤ μ.real B + μ.real (B ∆ C) := by
    have h := le_abs_self (μ.real C - μ.real B)
    have habs : |μ.real C - μ.real B| = |μ.real B - μ.real C| := abs_sub_comm _ _
    linarith
  have hjointAbs := inducedDMP_abs_measureReal_inter_sub_le μ
    hAcy.measurableSet hBambient hCambient
  have hjointUpper : μ.real (Ainf ∩ B) ≤ μ.real (Ainf ∩ C) + μ.real (B ∆ C) := by
    have h := le_abs_self (μ.real (Ainf ∩ B) - μ.real (Ainf ∩ C))
    linarith
  have hDMP := wired_infinite_DMP_induced_supportedCylinder θ μ hμ S A hA C hCsupport
  have hDMP' : μ.real (Ainf ∩ C) ≤ w * μ.real C := by
    simpa [Ainf, w] using hDMP
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hw1 : w ≤ 1 := by dsimp [w]; exact measureReal_le_one
  have hbound : j ≤ w * b + 2 * μ.real (B ∆ C) := by
    calc
      j ≤ μ.real (Ainf ∩ C) + μ.real (B ∆ C) := by
        simpa [j] using hjointUpper
      _ ≤ w * μ.real C + μ.real (B ∆ C) := add_le_add hDMP' le_rfl
      _ ≤ w * (μ.real B + μ.real (B ∆ C)) + μ.real (B ∆ C) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hCupper hw0) le_rfl
      _ = w * μ.real B + w * μ.real (B ∆ C) + μ.real (B ∆ C) := by ring
      _ ≤ w * b + 2 * μ.real (B ∆ C) := by
        have he0 : 0 ≤ μ.real (B ∆ C) :=
          measureReal_nonneg (μ := μ) (s := B ∆ C)
        have hmul : w * μ.real (B ∆ C) ≤ μ.real (B ∆ C) := by
          calc
            w * μ.real (B ∆ C) ≤ 1 * μ.real (B ∆ C) :=
              mul_le_mul_of_nonneg_right hw1 he0
            _ = μ.real (B ∆ C) := one_mul _
        dsimp [b]
        nlinarith [hmul]
  nlinarith [hgapEq, herr]

end
end PottsContinuity.Infinite
