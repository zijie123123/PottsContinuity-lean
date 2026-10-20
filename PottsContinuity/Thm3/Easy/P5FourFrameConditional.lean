module

public import Mathlib
public import PottsContinuity.Foundations.BoxBoundary
public import PottsContinuity.PlanarTopology.RectanglePolygonDomain
public import PottsContinuity.Thm3.RSW.AnnulusCircuit
public import PottsContinuity.Thm3.RSW.AnnulusPositivity
public import PottsContinuity.Thm3.RSW.FiniteBoundary

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open PottsContinuity
open PottsContinuity.PD.FK

/-- The source P5a finite annulus, with its corrected inner exclusion. -/
def p5aAnnulusVertexSet (n : ℕ) : Finset (ℤ × ℤ) :=
  PottsContinuity.box (2 * n) \
    PottsContinuity.box (n + 1)

/-- A vertical crossing of a coordinate rectangle by an actual open walk in
the induced graph on `V`. -/
def p5VerticalCrossing (V : Finset (ℤ × ℤ)) (a b c d : ℤ)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : Prop :=
  ∃ (x y : (V : Set (ℤ × ℤ))) (w : (PottsContinuity.rcOpenGraph V ω).Walk x y),
    x.1.2 = a ∧ y.1.2 = b ∧ x.1.1 ∈ Set.Icc c d ∧ y.1.1 ∈ Set.Icc c d ∧
      ∀ v ∈ w.support, v.1.1 ∈ Set.Icc c d ∧ v.1.2 ∈ Set.Icc a b

/-- The four actual side crossings used for the P5a annulus circuit. The
annulus carrier already removes `box (n+1)`, so every sampled vertex of these
walks lies outside the deleted inner box. -/
def p5FrameCrossing (n m : ℕ) (i : Fin 4)
    (ω : (squareLattice.induce
      (p5aAnnulusVertexSet n : Set (ℤ × ℤ))).edgeSet → Bool) : Prop :=
  let V := p5aAnnulusVertexSet n
  match i.val with
  | 0 => PottsContinuity.horizontalCrossing V
      (-(8 * (m : ℤ))) (8 * (m : ℤ))
      ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m) ω
  | 1 => PottsContinuity.horizontalCrossing V
      (-(8 * (m : ℤ))) (8 * (m : ℤ))
      (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m) ω
  | 2 => p5VerticalCrossing V (-(8 * (m : ℤ))) (8 * (m : ℤ))
      ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m) ω
  | _ => p5VerticalCrossing V (-(8 * (m : ℤ))) (8 * (m : ℤ))
      (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m) ω

/-- The corrected P5a open circuit event on the finite free annulus. -/
def p5aAnnulusCircuitEvent (n : ℕ)
    (ω : (squareLattice.induce
      (p5aAnnulusVertexSet n : Set (ℤ × ℤ))).edgeSet → Bool) : Prop :=
  ω ∈ PottsContinuity.RSW.annulusCircuitEvent
    (p5aAnnulusVertexSet n) (0, 0) n

/-- The corrected P5a annulus probability, in the source's free boundary
convention on `Λ_(2n) \ Λ_(n+1)`. -/
noncomputable def p5aAnnulusProbability (θ : Parameters) (n : ℕ) : ℝ :=
  PottsContinuity.RSW.finiteBoundaryEventProbability
    (p5aAnnulusVertexSet n) θ
    (frozenBoundaryCondition (p5aAnnulusVertexSet n) 0)
    (p5aAnnulusCircuitEvent n)

private theorem p5a_allTrue_mem_annulusCircuitEvent (n : ℕ) (hn : 2 ≤ n) :
    p5aAnnulusCircuitEvent n (fun _ => true) := by
  let a : LatticeVertex := (-(n : ℤ) - 2, -(n : ℤ) - 2)
  let w := 2 * n + 4
  let P := PlanarTopology.rectangleLatticePolygon a w w
    (by dsimp [w]; omega) (by dsimp [w]; omega)
  have hboundary (i : ZMod ((2 * w + 2 * w - 3) + 3)) :=
    (PlanarTopology.mem_rectanglePolygon_vertices_iff a w w
      (by dsimp [w]; omega) (by dsimp [w]; omega) (P.vertex i)).mp ⟨i, rfl⟩
  have hmax (i : ZMod ((2 * w + 2 * w - 3) + 3)) :
      max |(P.vertex i).1| |(P.vertex i).2| = (n : ℤ) + 2 := by
    have hi := hboundary i
    dsimp only [a, w] at hi
    simp only [abs_eq_max_neg]
    omega
  have hgeom (i : ZMod ((2 * w + 2 * w - 3) + 3)) :
      (n : ℤ) < max |(P.vertex i).1| |(P.vertex i).2| ∧
        max |(P.vertex i).1| |(P.vertex i).2| ≤ 2 * (n : ℤ) := by
    rw [hmax i]
    constructor <;> omega
  have hV (i : ZMod ((2 * w + 2 * w - 3) + 3)) :
      P.vertex i ∈ p5aAnnulusVertexSet n := by
    rw [p5aAnnulusVertexSet, Finset.mem_sdiff]
    constructor
    · apply (PottsContinuity.Foundations.mem_box_iff_abs_le
        (2 * n) (P.vertex i)).2
      have h := hmax i
      constructor
      · exact le_trans (le_max_left _ _) (by rw [h]; omega)
      · exact le_trans (le_max_right _ _) (by rw [h]; omega)
    · intro hi
      have hi' := (PottsContinuity.Foundations.mem_box_iff_abs_le
        (n + 1) (P.vertex i)).mp hi
      have hsmall : max |(P.vertex i).1| |(P.vertex i).2| ≤ (n : ℤ) + 1 :=
        max_le_iff.mpr hi'
      rw [hmax i] at hsmall
      omega
  have hcenter :
      FKC.latticeEmbed ⟨1, zero_lt_one⟩ (0, 0) ∈ P.domain ⟨1, zero_lt_one⟩ := by
    rw [PlanarTopology.rectangleLatticePolygon_domain a w w
      (by dsimp [w]; omega) (by dsimp [w]; omega) ⟨1, zero_lt_one⟩]
    dsimp [FKC.latticeEmbed, PlanarTopology.complexOpenRectangle, a, w]
    push_cast
    norm_num only [mul_zero, one_mul, Int.cast_zero]
    constructor <;> constructor <;> linarith only [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨2 * w + 2 * w - 3, P, hcenter, ?_, ?_⟩
  · intro i
    simpa only [Prod.fst_zero, Prod.snd_zero, sub_zero] using hgeom i
  · intro i
    refine ⟨hV i, hV (i + 1), ?_⟩
    rw [PottsContinuity.RSW.rcOpenGraph_all_true]
    apply (PottsContinuity.PD.FK.squareLattice_adj_iff _ _).mpr
    exact P.adjacent i

/-- The corrected P5a annulus has positive free probability at every source
scale `n ≥ 2`; the all-open square circuit at radius `n+2` witnesses it. -/
theorem p5aAnnulusProbability_pos (θ : Parameters) (n : ℕ) (hn : 2 ≤ n) :
    0 < p5aAnnulusProbability θ n := by
  unfold p5aAnnulusProbability
  apply (PottsContinuity.RSW.finiteBoundaryEventProbability_pos_iff
    (p5aAnnulusVertexSet n) θ
    (frozenBoundaryCondition (p5aAnnulusVertexSet n) 0)
    (p5aAnnulusCircuitEvent n)).mpr
  exact ⟨fun _ => true, p5a_allTrue_mem_annulusCircuitEvent n hn⟩

private theorem p5a_small_scales_uniform_lower_bound
    (θ : Parameters) (N : ℕ) (hN : 2 ≤ N) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → n < N →
      c ≤ p5aAnnulusProbability θ n := by
  by_cases hN3 : 3 ≤ N
  · let S := (Finset.Icc 2 (N - 1)).image (p5aAnnulusProbability θ)
    have hSne : S.Nonempty := by
      refine ⟨p5aAnnulusProbability θ 2, Finset.mem_image.mpr ?_⟩
      exact ⟨2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
    let c := S.min' hSne
    have hcpos : 0 < c := by
      have hcMem : c ∈ S := Finset.min'_mem S hSne
      rcases Finset.mem_image.mp hcMem with ⟨k, hk, hkc⟩
      rw [← hkc]
      exact p5aAnnulusProbability_pos θ k (Finset.mem_Icc.mp hk).1
    refine ⟨c, hcpos, ?_⟩
    intro n hn hnN
    have hnUpper : n ≤ N - 1 := by omega
    have hmem : p5aAnnulusProbability θ n ∈ S :=
      Finset.mem_image.mpr ⟨n, Finset.mem_Icc.mpr ⟨hn, hnUpper⟩, rfl⟩
    exact Finset.min'_le S _ hmem
  · have hNeq : N = 2 := by omega
    subst N
    refine ⟨1, by norm_num, ?_⟩
    intro n hn hnN
    omega

private theorem p5VerticalCrossing_isUpperSet (V : Finset (ℤ × ℤ))
    (a b c d : ℤ) :
    IsUpperSet {ω | p5VerticalCrossing V a b c d ω} := by
  intro ω η hωη hcross
  rcases hcross with ⟨x, y, w, hx, hy, hxc, hyc, hsupport⟩
  refine ⟨x, y, w.mapLe
    (PottsContinuity.RSW.rcOpenGraph_mono V hωη),
    hx, hy, hxc, hyc, ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
  exact hsupport v hv

private theorem p5FrameCrossing_isUpperSet (n m : ℕ) (i : Fin 4) :
    IsUpperSet {ω | p5FrameCrossing n m i ω} := by
  fin_cases i <;> simp [p5FrameCrossing] <;>
    first
    | exact PottsContinuity.RSW.horizontalCrossing_isUpperSet
        (p5aAnnulusVertexSet n) _ _ _ _
    | exact p5VerticalCrossing_isUpperSet
        (p5aAnnulusVertexSet n) _ _ _ _

/-- If four increasing frame events each have probability at least `c` under
the free annulus law, and their intersection forces the source annulus circuit,
FKG gives the product lower bound `c^4`. The missing crossing comparison and
planar circuit extraction remain explicit premises. -/
theorem p5a_probability_lower_of_fourFrameCrossings
    (θ : Parameters) (n m : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hframe : ∀ i : Fin 4,
      c ≤ PottsContinuity.RSW.finiteBoundaryEventProbability
        (p5aAnnulusVertexSet n) θ
        (frozenBoundaryCondition (p5aAnnulusVertexSet n) 0)
        (p5FrameCrossing n m i))
    (hgeometry : ∀ ω, p5FrameCrossing n m 0 ω ∧ p5FrameCrossing n m 1 ω ∧
          p5FrameCrossing n m 2 ω ∧ p5FrameCrossing n m 3 ω →
          p5aAnnulusCircuitEvent n ω) :
    c ^ 4 ≤ p5aAnnulusProbability θ n := by
  let V := p5aAnnulusVertexSet n
  let ξ := frozenBoundaryCondition V 0
  let E (i : Fin 4) : ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) → Prop :=
    p5FrameCrossing n m i
  let P (i : Fin 4) : ℝ :=
    PottsContinuity.RSW.finiteBoundaryEventProbability V θ ξ (E i)
  have hP01 := PottsContinuity.RSW.finiteBoundaryEventProbability_fkg
    V θ ξ (E 0) (E 1)
    (by simpa [E] using p5FrameCrossing_isUpperSet n m 0)
    (by simpa [E] using p5FrameCrossing_isUpperSet n m 1)
  have hP23 := PottsContinuity.RSW.finiteBoundaryEventProbability_fkg
    V θ ξ (E 2) (E 3)
    (by simpa [E] using p5FrameCrossing_isUpperSet n m 2)
    (by simpa [E] using p5FrameCrossing_isUpperSet n m 3)
  let E01 : ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) → Prop :=
    fun ω => E 0 ω ∧ E 1 ω
  let E23 : ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) → Prop :=
    fun ω => E 2 ω ∧ E 3 ω
  have hE01 : IsUpperSet {ω | E01 ω} := by
    intro ω η h hω
    exact ⟨(p5FrameCrossing_isUpperSet n m 0) h (hω.1),
      (p5FrameCrossing_isUpperSet n m 1) h (hω.2)⟩
  have hE23 : IsUpperSet {ω | E23 ω} := by
    intro ω η h hω
    exact ⟨(p5FrameCrossing_isUpperSet n m 2) h (hω.1),
      (p5FrameCrossing_isUpperSet n m 3) h (hω.2)⟩
  have hP0123 := PottsContinuity.RSW.finiteBoundaryEventProbability_fkg
    V θ ξ E01 E23 hE01 hE23
  let Eall : ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) → Prop :=
    fun ω => (E 0 ω ∧ E 1 ω) ∧ (E 2 ω ∧ E 3 ω)
  have hP01Lower : c ^ 2 ≤
      PottsContinuity.RSW.finiteBoundaryEventProbability V θ ξ E01 := by
    have hmul : c * c ≤ P 0 * P 1 := by
      exact mul_le_mul (hframe 0) (hframe 1) hc (le_trans hc (hframe 0))
    have hfirst : c * c ≤
        PottsContinuity.RSW.finiteBoundaryEventProbability V θ ξ E01 :=
      hmul.trans (by simpa [P, E01, E] using hP01)
    simpa [pow_two] using hfirst
  have hP23Lower : c ^ 2 ≤
      PottsContinuity.RSW.finiteBoundaryEventProbability V θ ξ E23 := by
    have hmul : c * c ≤ P 2 * P 3 := by
      exact mul_le_mul (hframe 2) (hframe 3) hc (le_trans hc (hframe 2))
    have hfirst : c * c ≤
        PottsContinuity.RSW.finiteBoundaryEventProbability V θ ξ E23 :=
      hmul.trans (by simpa [P, E23, E] using hP23)
    simpa [pow_two] using hfirst
  have hP01nonneg : 0 ≤
      PottsContinuity.RSW.finiteBoundaryEventProbability V θ ξ E01 :=
    le_trans (sq_nonneg c) hP01Lower
  have hPallLower : c ^ 4 ≤
      PottsContinuity.RSW.finiteBoundaryEventProbability V θ ξ Eall := by
    have hmul : c ^ 2 * c ^ 2 ≤
        PottsContinuity.RSW.finiteBoundaryEventProbability V θ ξ E01 *
          PottsContinuity.RSW.finiteBoundaryEventProbability V θ ξ E23 :=
      mul_le_mul hP01Lower hP23Lower (sq_nonneg c) hP01nonneg
    have hprod := hmul.trans (by simpa [Eall, E01, E23] using hP0123)
    calc
      c ^ 4 = c ^ 2 * c ^ 2 := by ring
      _ ≤ PottsContinuity.RSW.finiteBoundaryEventProbability V θ ξ Eall := hprod
  have hset :
      PottsContinuity.RSW.finiteBoolEvent V Eall ⊆
        PottsContinuity.RSW.finiteBoolEvent V (p5aAnnulusCircuitEvent n) := by
    intro A hA
    change Eall ((boolConfigurationEquiv
      (squareLattice.induce (V : Set (ℤ × ℤ)))).symm A) at hA
    change p5aAnnulusCircuitEvent n ((boolConfigurationEquiv
      (squareLattice.induce (V : Set (ℤ × ℤ)))).symm A)
    exact hgeometry _ ⟨hA.1.1, hA.1.2, hA.2.1, hA.2.2⟩
  have hmono :
      PottsContinuity.RSW.finiteBoundaryEventProbability V θ ξ Eall ≤
        PottsContinuity.RSW.finiteBoundaryEventProbability V θ ξ
          (p5aAnnulusCircuitEvent n) := by
    unfold PottsContinuity.RSW.finiteBoundaryEventProbability
    exact MeasureTheory.measureReal_mono hset
  unfold p5aAnnulusProbability
  have hfinal := hPallLower.trans hmono
  simpa [V, ξ, E, Eall] using hfinal

/-- The four-frame FKG estimate and strict finite-scale positivity combine to
give a uniform corrected P5a bound once the large-scale frame probability
bounds and the deterministic four-frame circuit geometry `hgeometry` are supplied. -/
theorem exists_p5a_uniform_lower_bound_of_largeFrameCrossings
    (θ : Parameters) (N : ℕ) (hN : 2 ≤ N) (c : ℝ) (hc : 0 < c)
    (hframe : ∀ n : ℕ, N ≤ n → ∃ m : ℕ, 1 ≤ m ∧
      n + 2 ≤ 6 * m ∧ n + 2 + 3 * m ≤ 2 * n ∧ 9 * m ≤ 2 * n ∧
      ∀ i : Fin 4,
        c ≤ PottsContinuity.RSW.finiteBoundaryEventProbability
          (p5aAnnulusVertexSet n) θ
          (frozenBoundaryCondition (p5aAnnulusVertexSet n) 0)
          (p5FrameCrossing n m i))
    (hgeometry : ∀ (n m : ℕ), 2 ≤ n → 1 ≤ m → n + 2 ≤ 6 * m →
      n + 2 + 3 * m ≤ 2 * n → 9 * m ≤ 2 * n →
      ∀ ω, p5FrameCrossing n m 0 ω ∧ p5FrameCrossing n m 1 ω ∧
        p5FrameCrossing n m 2 ω ∧ p5FrameCrossing n m 3 ω →
        p5aAnnulusCircuitEvent n ω) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ n : ℕ, 2 ≤ n →
      c₂ ≤ p5aAnnulusProbability θ n := by
  obtain ⟨csmall, hcsmall, hsmall⟩ :=
    p5a_small_scales_uniform_lower_bound θ N hN
  let c₂ := min csmall (c ^ 4)
  have hc₂ : 0 < c₂ := by
    dsimp [c₂]
    exact lt_min hcsmall (pow_pos hc 4)
  refine ⟨c₂, hc₂, ?_⟩
  intro n hn
  by_cases hnN : n < N
  · exact (min_le_left _ _).trans (hsmall n hn hnN)
  · obtain ⟨m, hm, hcorner, hradial, htangent, hframeN⟩ := hframe n (by omega)
    have hlarge := p5a_probability_lower_of_fourFrameCrossings θ n m c hc.le
      hframeN (hgeometry n m hn hm hcorner hradial htangent)
    exact (min_le_right _ _).trans hlarge

end PottsContinuity.Thm3.Easy
