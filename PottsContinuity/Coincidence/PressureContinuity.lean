module

public import PottsContinuity.BD12.InfiniteBoxPressureSandwich
public import PottsContinuity.BD12.OrderedEdgeMarginalUniqueness
public import PottsContinuity.Foundations.EveryExhaustion
public import PottsContinuity.Infinite.Symmetry
public import PottsContinuity.Infinite.Translation
public import PottsContinuity.Coincidence.FreeMonotonicity
public import Mathlib.Topology.Order.Monotone

@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators

namespace PottsContinuity.Coincidence

open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.Infinite
open PottsContinuity.BD12

noncomputable section

local instance pressureBoxEdgeFintype (n : ℕ) : Fintype (boxGraph (0, 0) n).edgeSet :=
  Fintype.ofFinite _

abbrev PressureSquareLattice := PottsContinuity.PD.FK.squareLattice

/-- A fixed horizontal unit edge used to represent every edge intensity. -/
def horizontalUnitEdge : PressureSquareLattice.edgeSet :=
  ⟨s((0, 0), (1, 0)), by
    apply PressureSquareLattice.mem_edgeSet.mpr
    exact (PottsContinuity.PD.FK.squareLattice_adj_iff (0, 0) (1, 0)).mpr
      (Or.inl ⟨Or.inl rfl, rfl⟩)⟩

theorem allOpen_singleton_eq_edgeOpen (b : PressureSquareLattice.edgeSet) :
    LatticeConfiguration.allOpen {b} = {ω | ω b = true} := by
  ext ω
  rw [LatticeConfiguration.allOpen]
  simp only [Finset.mem_singleton]
  exact ⟨fun h => h b rfl, fun h e he => he ▸ h⟩

private theorem edgeProbability_eq_of_map_preimage
    (μ : Measure LatticeConfiguration) (f : LatticeConfiguration → LatticeConfiguration)
    (hf : Measurable f) (hmap : μ.map f = μ)
    (E F : Set LatticeConfiguration) (hE : MeasurableSet E)
    (hpre : f ⁻¹' E = F) : μ.real E = μ.real F := by
  have h := congrArg (fun ν : Measure LatticeConfiguration => ν E) hmap
  rw [Measure.map_apply hf hE, hpre] at h
  exact (congrArg ENNReal.toReal h).symm

private theorem iso_edge_preimage (e : PressureSquareLattice ≃g PressureSquareLattice)
    (b : PressureSquareLattice.edgeSet) :
    (latticeConfigurationIsoHomeomorph e) ⁻¹'
      LatticeConfiguration.allOpen {(e.mapEdgeSet b)} =
        LatticeConfiguration.allOpen {b} := by
  rw [allOpen_singleton_eq_edgeOpen (e.mapEdgeSet b), allOpen_singleton_eq_edgeOpen b]
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [latticeConfigurationIsoHomeomorph_apply]
  have hcancel : e.symm.mapEdgeSet (e.mapEdgeSet b) = b := by
    exact e.mapEdgeSet.left_inv b
  rw [hcancel]

private theorem iso_edge_probability_eq
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit p q i μ)
    (e : PressureSquareLattice ≃g PressureSquareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (b : PressureSquareLattice.edgeSet) :
    μ.real (LatticeConfiguration.allOpen {e.mapEdgeSet b}) =
      μ.real (LatticeConfiguration.allOpen {b}) := by
  have hmap := infinite_volume_latticeIso_invariant p q hp0 hp1 hq i μ hμ e hbox
  exact edgeProbability_eq_of_map_preimage μ (latticeConfigurationIsoHomeomorph e)
    (latticeConfigurationIsoHomeomorph_measurable e) hmap _ _
    (LatticeConfiguration.allOpen_isClopen _).isOpen.measurableSet
    (iso_edge_preimage e b)

private theorem translation_edge_preimage (a : LatticeVertex)
    (b : PressureSquareLattice.edgeSet) :
    (latticeConfigurationTranslate a) ⁻¹'
      LatticeConfiguration.allOpen
        {(latticeTranslationIso a).mapEdgeSet b} = LatticeConfiguration.allOpen {b} := by
  rw [allOpen_singleton_eq_edgeOpen ((latticeTranslationIso a).mapEdgeSet b),
    allOpen_singleton_eq_edgeOpen b]
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [latticeConfigurationTranslate_apply]
  have hcancel : (latticeTranslationIso (-a)).mapEdgeSet
      ((latticeTranslationIso a).mapEdgeSet b) = b := by
    apply Subtype.ext
    change Sym2.map (latticeTranslate (-a))
      (Sym2.map (latticeTranslate a) b.val) = b.val
    rw [Sym2.map_map]
    have hfun : latticeTranslate (-a) ∘ latticeTranslate a = id := by
      funext v
      exact latticeTranslate_neg_cancel a v
    change Sym2.map (latticeTranslate (-a) ∘ latticeTranslate a) b.val = b.val
    rw [hfun]
    simp
  rw [hcancel]

private theorem translation_edge_probability_eq
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit p q i μ)
    (a : LatticeVertex) (b : PressureSquareLattice.edgeSet) :
    μ.real (LatticeConfiguration.allOpen
      {(latticeTranslationIso a).mapEdgeSet b}) =
      μ.real (LatticeConfiguration.allOpen {b}) := by
  have hmap := infinite_volume_translation_invariant p q hq i μ hμ a
  exact edgeProbability_eq_of_map_preimage μ (latticeConfigurationTranslate a)
    (latticeConfigurationTranslate_measurable a) hmap _ _
    (LatticeConfiguration.allOpen_isClopen _).isOpen.measurableSet
    (translation_edge_preimage a b)

private theorem every_edge_is_a_translated_axis_edge
    (b : PressureSquareLattice.edgeSet) :
    ∃ a : LatticeVertex,
      b = (latticeTranslationIso a).mapEdgeSet horizontalUnitEdge ∨
      b = (latticeTranslationIso a).mapEdgeSet
        (latticeQuarterTurnIso.mapEdgeSet horizontalUnitEdge) := by
  obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective b.val
  have hadj : PressureSquareLattice.Adj u v := by
    change s(u, v) = b.val at huv
    have hmem := congrArg (fun e : Sym2 LatticeVertex =>
      e ∈ PressureSquareLattice.edgeSet) huv
    exact PressureSquareLattice.mem_edgeSet.mp (hmem.symm ▸ b.property)
  rcases (PottsContinuity.PD.FK.squareLattice_adj_iff u v).mp hadj with
      ⟨horiz, hy⟩ | ⟨hx, vert⟩
  · rcases horiz with h | h
    · refine ⟨(u.1, u.2), Or.inl ?_⟩
      apply Subtype.ext
      rw [← huv]
      simp only [SimpleGraph.Iso.mapEdgeSet_apply, SimpleGraph.Hom.mapEdgeSet_coe,
        RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding, latticeTranslationIso,
        horizontalUnitEdge]
      apply Sym2.eq_iff.mpr
      exact Or.inl ⟨by simp [latticeTranslate], by
        apply Prod.ext <;> dsimp [latticeTranslate] <;> omega⟩
    · refine ⟨(v.1, v.2), Or.inl ?_⟩
      apply Subtype.ext
      rw [← huv]
      simp only [SimpleGraph.Iso.mapEdgeSet_apply, SimpleGraph.Hom.mapEdgeSet_coe,
        RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding, latticeTranslationIso,
        horizontalUnitEdge]
      apply Sym2.eq_iff.mpr
      exact Or.inr ⟨by
        apply Prod.ext <;> dsimp [latticeTranslate] <;> omega,
        by simp [latticeTranslate]⟩
  · rcases vert with h | h
    · refine ⟨(u.1, u.2), Or.inr ?_⟩
      apply Subtype.ext
      rw [← huv]
      simp only [SimpleGraph.Iso.mapEdgeSet_apply, SimpleGraph.Hom.mapEdgeSet_coe,
        RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding, latticeTranslationIso,
        horizontalUnitEdge, SimpleGraph.Iso.mapEdgeSet_apply,
        SimpleGraph.Hom.mapEdgeSet_coe, RelEmbedding.coe_toRelHom,
        RelIso.coe_toRelEmbedding, latticeQuarterTurnIso]
      apply Sym2.eq_iff.mpr
      exact Or.inl ⟨by simp [latticeQuarterTurn, latticeTranslate], by
        apply Prod.ext <;> dsimp [latticeQuarterTurn, latticeTranslate] <;> omega⟩
    · refine ⟨(v.1, v.2), Or.inr ?_⟩
      apply Subtype.ext
      rw [← huv]
      simp only [SimpleGraph.Iso.mapEdgeSet_apply, SimpleGraph.Hom.mapEdgeSet_coe,
        RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding, latticeTranslationIso,
        horizontalUnitEdge, SimpleGraph.Iso.mapEdgeSet_apply,
        SimpleGraph.Hom.mapEdgeSet_coe, RelEmbedding.coe_toRelHom,
        RelIso.coe_toRelEmbedding, latticeQuarterTurnIso]
      apply Sym2.eq_iff.mpr
      exact Or.inr ⟨by
        apply Prod.ext <;> dsimp [latticeQuarterTurn, latticeTranslate] <;> omega,
        by simp [latticeQuarterTurn, latticeTranslate]⟩

theorem frozen_limit_edge_probabilities_eq_horizontal
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit p q i μ) :
    ∀ b : PressureSquareLattice.edgeSet,
      μ.real (LatticeConfiguration.allOpen {b}) =
        μ.real (LatticeConfiguration.allOpen {horizontalUnitEdge}) := by
  intro b
  obtain ⟨a, hor | vert⟩ := every_edge_is_a_translated_axis_edge b
  · rw [hor]
    exact translation_edge_probability_eq p q hq i μ hμ a horizontalUnitEdge
  · rw [vert]
    exact (translation_edge_probability_eq p q hq i μ hμ a
      (latticeQuarterTurnIso.mapEdgeSet horizontalUnitEdge)).trans
      (iso_edge_probability_eq p q hp0 hp1 hq i μ hμ latticeQuarterTurnIso
        (fun c v r => mem_latticeBox_quarterTurn_iff c v r) horizontalUnitEdge)

def pressureBoxPerimeter (n : ℕ) : Finset LatticeVertex :=
  (({-(n : ℤ)} : Finset ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)) ∪
  (({(n : ℤ)} : Finset ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)) ∪
  (Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ {-(n : ℤ)}) ∪
  (Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ {(n : ℤ)})

private theorem pressureBoxPerimeter_card_bound (n : ℕ) :
    (pressureBoxPerimeter n).card ≤ 4 * (2 * n + 1) := by
  let I := Finset.Icc (-(n : ℤ)) (n : ℤ)
  let leftSide := ({-(n : ℤ)} : Finset ℤ) ×ˢ I
  let rightSide := ({(n : ℤ)} : Finset ℤ) ×ˢ I
  let bottomSide := I ×ˢ {-(n : ℤ)}
  let topSide := I ×ˢ {(n : ℤ)}
  have hI : I.card = 2 * n + 1 := by
    simp only [I, Int.card_Icc]
    omega
  have hleft : leftSide.card = 2 * n + 1 := by simp [leftSide, hI]
  have hright : rightSide.card = 2 * n + 1 := by simp [rightSide, hI]
  have hbottom : bottomSide.card = 2 * n + 1 := by simp [bottomSide, hI]
  have htop : topSide.card = 2 * n + 1 := by simp [topSide, hI]
  have h1 := Finset.card_union_le leftSide rightSide
  have h2 := Finset.card_union_le (leftSide ∪ rightSide) bottomSide
  have h3 := Finset.card_union_le (leftSide ∪ rightSide ∪ bottomSide) topSide
  change (leftSide ∪ rightSide ∪ bottomSide ∪ topSide).card ≤ _
  omega

private theorem boxVertexBoundary_on_perimeter (n : ℕ)
    (x : BoxVertex (0, 0) n) (hx : x ∈ boxVertexBoundary (0, 0) n) :
    x.val ∈ pressureBoxPerimeter n := by
  have hboundary : x.val ∈ PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) n) := hx
  rcases hboundary with ⟨hxin, y, hadj, hyout⟩
  have hbox := (mem_latticeBox (0, 0) x.val n).mp hxin
  have hface : x.val.1 = -(n : ℤ) ∨ x.val.1 = n ∨
      x.val.2 = -(n : ℤ) ∨ x.val.2 = n := by
    by_contra hface
    push Not at hface
    have hAdj := (squareLattice_adj_iff x.val y).mp hadj
    have hyin : y ∈ latticeBox (0, 0) n := by
      rw [mem_latticeBox]
      rcases hAdj with ⟨⟨hstep | hstep, hy⟩⟩ | ⟨hx, hstep | hstep⟩ <;> omega
    exact (hyout hyin).elim
  have hbox' := (mem_latticeBox (0, 0) x.val n).mp x.property
  simp only [pressureBoxPerimeter, Finset.mem_union, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_Icc]
  omega

private theorem boxVertexBoundary_card_bound (n : ℕ) :
    Nat.card (boxVertexBoundary (0, 0) n) ≤ 4 * (2 * n + 1) := by
  let : Fintype (boxVertexBoundary (0, 0) n) := Fintype.ofFinite _
  let f : boxVertexBoundary (0, 0) n → {v : LatticeVertex // v ∈ pressureBoxPerimeter n} :=
    fun x => ⟨x.val.val, boxVertexBoundary_on_perimeter n x.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {v : LatticeVertex // v ∈ pressureBoxPerimeter n} => z.val) h
  calc
    Nat.card (boxVertexBoundary (0, 0) n) = Fintype.card (boxVertexBoundary (0, 0) n) := by simp
    _ ≤ Fintype.card {v : LatticeVertex // v ∈ pressureBoxPerimeter n} :=
      Fintype.card_le_of_injective f hf
    _ = (pressureBoxPerimeter n).card := by simp
    _ ≤ 4 * (2 * n + 1) := pressureBoxPerimeter_card_bound n

def pressureGridVertex (n : ℕ) (i j : Fin (n + 1)) : BoxVertex (0, 0) n := by
  refine ⟨((i.val : ℤ), (j.val : ℤ)), ?_⟩
  rw [mem_latticeBox]
  constructor <;> constructor <;> omega

def pressureGridHorizontalEdge (n : ℕ) (i j : Fin n) :
    (boxGraph (0, 0) n).edgeSet := by
  let u := pressureGridVertex n i.castSucc j.castSucc
  let v := pressureGridVertex n i.succ j.castSucc
  refine ⟨s(u, v), ?_⟩
  apply (boxGraph (0, 0) n).mem_edgeSet.mpr
  apply (boxGraph_adj_iff (0, 0) n u v).2
  apply (squareLattice_adj_iff u.val v.val).2
  left
  refine ⟨Or.inl ?_, ?_⟩
  · simp [u, v, pressureGridVertex]
  · rfl

private theorem pressureGridHorizontalEdge_injective (n : ℕ) :
    Function.Injective (fun ij : Fin n × Fin n =>
      pressureGridHorizontalEdge n ij.1 ij.2) := by
  intro ij kl h
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨i', j'⟩
  have he := congrArg (fun e : (boxGraph (0, 0) n).edgeSet => e.val) h
  change s(pressureGridVertex n i.castSucc j.castSucc,
      pressureGridVertex n i.succ j.castSucc) =
    s(pressureGridVertex n i'.castSucc j'.castSucc,
      pressureGridVertex n i'.succ j'.castSucc) at he
  rcases Sym2.eq_iff.mp he with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · apply Prod.ext
    · apply Fin.ext
      have hx := congrArg (fun z : BoxVertex (0, 0) n => z.val.1) hleft
      simpa [pressureGridVertex] using hx
    · apply Fin.ext
      have hy := congrArg (fun z : BoxVertex (0, 0) n => z.val.2) hleft
      simpa [pressureGridVertex] using hy
  · have hx₁ := congrArg (fun z : BoxVertex (0, 0) n => z.val.1) hleft
    have hx₂ := congrArg (fun z : BoxVertex (0, 0) n => z.val.1) hright
    simp [pressureGridVertex] at hx₁ hx₂
    omega

private theorem pressureBoxEdge_card_lower (n : ℕ) :
    n ^ 2 ≤ Nat.card (boxGraph (0, 0) n).edgeSet := by
  have hcard := Fintype.card_le_of_injective
    (fun ij : Fin n × Fin n => pressureGridHorizontalEdge n ij.1 ij.2)
    (pressureGridHorizontalEdge_injective n)
  calc
    n ^ 2 = Fintype.card (Fin n × Fin n) := by simp [pow_two]
    _ ≤ Fintype.card (boxGraph (0, 0) n).edgeSet := hcard
    _ = Nat.card (boxGraph (0, 0) n).edgeSet := by simp [Nat.card_eq_fintype_card]

private theorem box_edge_sum_eq_card_mul_horizontal
    (μ : Measure LatticeConfiguration)
    (hcommon : ∀ b : PressureSquareLattice.edgeSet,
      μ.real (LatticeConfiguration.allOpen {b}) =
        μ.real (LatticeConfiguration.allOpen {horizontalUnitEdge})) (n : ℕ) :
    (∑ e : (boxGraph (0, 0) n).edgeSet,
      μ.real (LatticeConfiguration.allOpen {boxEdgeEmbedding (0, 0) n e})) =
    (Nat.card (boxGraph (0, 0) n).edgeSet : ℝ) *
      μ.real (LatticeConfiguration.allOpen {horizontalUnitEdge}) := by
  calc
    (∑ e : (boxGraph (0, 0) n).edgeSet,
        μ.real (LatticeConfiguration.allOpen {boxEdgeEmbedding (0, 0) n e})) =
      ∑ _e : (boxGraph (0, 0) n).edgeSet,
        μ.real (LatticeConfiguration.allOpen {horizontalUnitEdge}) := by
          apply Finset.sum_congr rfl
          intro e he
          exact hcommon (boxEdgeEmbedding (0, 0) n e)
    _ = (Nat.card (boxGraph (0, 0) n).edgeSet : ℝ) *
        μ.real (LatticeConfiguration.allOpen {horizontalUnitEdge}) := by
          calc
            (∑ _e : (boxGraph (0, 0) n).edgeSet,
                μ.real (LatticeConfiguration.allOpen {horizontalUnitEdge})) =
              (Fintype.card (boxGraph (0, 0) n).edgeSet : ℝ) *
                μ.real (LatticeConfiguration.allOpen {horizontalUnitEdge}) := by
                  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            _ = (Nat.card (boxGraph (0, 0) n).edgeSet : ℝ) *
                μ.real (LatticeConfiguration.allOpen {horizontalUnitEdge}) := by
                  rw [Nat.card_eq_fintype_card]

private theorem wired_pressure_sums
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (s t : ℝ) (hst : s < t)
    (μ₁ μ₀ : Measure LatticeConfiguration)
    (hμ₁ : IsRCInfiniteVolumeLimit
      (drtHomogeneousParameters q hq (drtLogActivityTemperature s)).toP
      (drtHomogeneousParameters q hq (drtLogActivityTemperature s)).toQ 1 μ₁)
    (hμ₀ : IsRCInfiniteVolumeLimit
      (drtHomogeneousParameters q hq (drtLogActivityTemperature t)).toP
      (drtHomogeneousParameters q hq (drtLogActivityTemperature t)).toQ 0 μ₀)
    (n : ℕ) :
    (∑ e : (boxGraph (0, 0) n).edgeSet,
      μ₁.real (LatticeConfiguration.allOpen {boxEdgeEmbedding (0, 0) n e})) ≤
    (∑ e : (boxGraph (0, 0) n).edgeSet,
      μ₀.real (LatticeConfiguration.allOpen {boxEdgeEmbedding (0, 0) n e})) +
      (Nat.card (boxVertexBoundary (0, 0) n) : ℝ) * Real.log q / (t - s) := by
  exact wired_infinite_box_edge_sum_le_free_larger_activity
    q hq s t hst μ₁ μ₀ hμ₁ hμ₀ n

private theorem homogeneous_box_edge_sums_eq_card_mul_horizontal
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (s t : ℝ)
    (μ₁ μ₀ : Measure LatticeConfiguration)
    (hμ₁ : IsRCInfiniteVolumeLimit
      (drtHomogeneousParameters q hq (drtLogActivityTemperature s)).toP
      (drtHomogeneousParameters q hq (drtLogActivityTemperature s)).toQ 1 μ₁)
    (hμ₀ : IsRCInfiniteVolumeLimit
      (drtHomogeneousParameters q hq (drtLogActivityTemperature t)).toP
      (drtHomogeneousParameters q hq (drtLogActivityTemperature t)).toQ 0 μ₀)
    (n : ℕ) :
    (∑ e : (boxGraph (0, 0) n).edgeSet,
      μ₁.real (LatticeConfiguration.allOpen {boxEdgeEmbedding (0, 0) n e})) =
        (Nat.card (boxGraph (0, 0) n).edgeSet : ℝ) *
          μ₁.real (LatticeConfiguration.allOpen {horizontalUnitEdge}) ∧
    (∑ e : (boxGraph (0, 0) n).edgeSet,
      μ₀.real (LatticeConfiguration.allOpen {boxEdgeEmbedding (0, 0) n e})) =
        (Nat.card (boxGraph (0, 0) n).edgeSet : ℝ) *
          μ₀.real (LatticeConfiguration.allOpen {horizontalUnitEdge}) := by
  let θ₁ := drtHomogeneousParameters q hq (drtLogActivityTemperature s)
  let θ₀ := drtHomogeneousParameters q hq (drtLogActivityTemperature t)
  have hμ₁' : IsRCInfiniteVolumeLimit θ₁.toP θ₁.toQ 1 μ₁ := by
    dsimp only [θ₁]
    exact hμ₁
  have hμ₀' : IsRCInfiniteVolumeLimit θ₀.toP θ₀.toQ 0 μ₀ := by
    dsimp only [θ₀]
    exact hμ₀
  have hcommon₁ := frozen_limit_edge_probabilities_eq_horizontal θ₁.toP θ₁.toQ
    (edgeParameter_pos θ₁) (edgeParameter_lt_one θ₁) θ₁.property 1 μ₁ hμ₁'
  have hcommon₀ := frozen_limit_edge_probabilities_eq_horizontal θ₀.toP θ₀.toQ
    (edgeParameter_pos θ₀) (edgeParameter_lt_one θ₀) θ₀.property 0 μ₀ hμ₀'
  constructor
  · exact box_edge_sum_eq_card_mul_horizontal μ₁ hcommon₁ n
  · exact box_edge_sum_eq_card_mul_horizontal μ₀ hcommon₀ n

theorem wired_activity_edge_probability_le_free_larger_activity
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (s t : ℝ) (hst : s < t)
    (μ₁ μ₀ : Measure LatticeConfiguration)
    (hμ₁ : IsRCInfiniteVolumeLimit
      (drtHomogeneousParameters q hq (drtLogActivityTemperature s)).toP
      (drtHomogeneousParameters q hq (drtLogActivityTemperature s)).toQ 1 μ₁)
    (hμ₀ : IsRCInfiniteVolumeLimit
      (drtHomogeneousParameters q hq (drtLogActivityTemperature t)).toP
      (drtHomogeneousParameters q hq (drtLogActivityTemperature t)).toQ 0 μ₀) :
    μ₁.real (LatticeConfiguration.allOpen {horizontalUnitEdge}) ≤
      μ₀.real (LatticeConfiguration.allOpen {horizontalUnitEdge}) := by
  let m₁ := μ₁.real (LatticeConfiguration.allOpen {horizontalUnitEdge})
  let m₀ := μ₀.real (LatticeConfiguration.allOpen {horizontalUnitEdge})
  let L := Real.log (q : ℝ)
  let d := t - s
  have hL : 0 ≤ L := Real.log_nonneg hq
  have hd : 0 < d := sub_pos.mpr hst
  have hpoint (n : ℕ) (hn : 0 < n) : m₁ ≤ m₀ + (12 * L / d) / n := by
    let N := (Nat.card (boxGraph (0, 0) n).edgeSet : ℝ)
    let B := (Nat.card (boxVertexBoundary (0, 0) n) : ℝ)
    have hpressure := wired_pressure_sums
      q hq s t hst μ₁ μ₀ hμ₁ hμ₀ n
    have hsum := homogeneous_box_edge_sums_eq_card_mul_horizontal
      q hq s t μ₁ μ₀ hμ₁ hμ₀ n
    rw [hsum.1, hsum.2] at hpressure
    have hpressure' : N * m₁ ≤ N * m₀ + B * L / d := by
      simpa [N, B, m₁, m₀, L, d] using hpressure
    have hNcast : ((n ^ 2 : ℕ) : ℝ) ≤
        (Nat.card (boxGraph (0, 0) n).edgeSet : ℝ) := by
      exact_mod_cast pressureBoxEdge_card_lower n
    have hN : (n : ℝ) ^ 2 ≤ N := by
      simpa only [Nat.cast_pow] using hNcast
    have hBcast : (Nat.card (boxVertexBoundary (0, 0) n) : ℝ) ≤
        (4 * (2 * n + 1) : ℕ) := by
      exact_mod_cast boxVertexBoundary_card_bound n
    have hB : B ≤ 4 * (2 * (n : ℝ) + 1) := by
      norm_num [B, Nat.cast_mul, Nat.cast_add] at hBcast ⊢
      exact hBcast
    have hnReal : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
    have hnRealPos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
    have hBsmall : B ≤ 12 * (n : ℝ) := by nlinarith
    have hratio : B / N ≤ 12 / (n : ℝ) := by
      rw [div_le_div_iff₀ hNpos hnRealPos]
      nlinarith [hN, hBsmall]
    have hdivide := (div_le_div_iff_of_pos_right hNpos).2 hpressure'
    have hcancelL : N * m₁ / N = m₁ := by field_simp [ne_of_gt hNpos]
    have hcancelR : N * m₀ / N = m₀ := by field_simp [ne_of_gt hNpos]
    have hterm : (B * L / d) / N = (B / N) * (L / d) := by
      field_simp [ne_of_gt hNpos, ne_of_gt hd]
    rw [add_div, hcancelL, hcancelR, hterm] at hdivide
    have hratio' := mul_le_mul_of_nonneg_right hratio (div_nonneg hL hd.le)
    have hconstant : (12 / (n : ℝ)) * (L / d) = (12 * L / d) / n := by
      ring
    rw [hconstant] at hratio'
    exact le_trans hdivide (add_le_add_right hratio' m₀)
  by_contra hnot
  have hstrict : m₀ < m₁ := lt_of_not_ge hnot
  have hgap : 0 < m₁ - m₀ := sub_pos.mpr hstrict
  let K := 12 * L / d
  have hK : 0 ≤ K := div_nonneg (mul_nonneg (by norm_num) hL) hd.le
  obtain ⟨n, hn⟩ := exists_nat_gt (K / (m₁ - m₀))
  have hnpos : 0 < n := by
    exact_mod_cast (lt_of_le_of_lt (div_nonneg hK hgap.le) hn)
  have hnK : K / (n : ℝ) < m₁ - m₀ := by
    rw [div_lt_iff₀ (by exact_mod_cast hnpos)]
    have hmul := (div_lt_iff₀ hgap).mp hn
    nlinarith
  have hlarge := hpoint n hnpos
  dsimp [K, L, d] at hlarge hnK
  linarith

end

end PottsContinuity.Coincidence
