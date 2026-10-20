module

public import PottsContinuity.Thm3.RSW.AnnulusCircuit
public import PottsContinuity.PlanarTopology.RectanglePolygonDomain
public import PottsContinuity.Foundations.BoxBoundary

/-!
# Nondegeneracy of the genuine finite annulus event

The all-open witness is the literal boundary of the square of radius n+1.
`PlanarTopology.RectanglePolygonDomain` identifies its Jordan interior with the actual
open rectangle. The
all-closed configuration is outside the event. Finite FK full support then
gives 0 < P[A_n] < 1 at each positive scale, independently of q's upper range.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory

/-- Opening every sampled edge gives precisely the induced lattice graph. -/
theorem rcOpenGraph_all_true (V : Finset (ℤ × ℤ)) :
    rcOpenGraph V (fun _ => true) = squareLattice.induce (V : Set (ℤ × ℤ)) := by
  unfold rcOpenGraph
  have heq : {e | ∃ h : e ∈ (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet,
      (fun _ : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet => true) ⟨e, h⟩ = true} =
      (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet := by
    ext e
    simp
  rw [heq, SimpleGraph.fromEdgeSet_edgeSet]

/-- Closing every sampled edge gives the edgeless graph. -/
theorem rcOpenGraph_all_false (V : Finset (ℤ × ℤ)) :
    rcOpenGraph V (fun _ => false) = ⊥ := by
  simp [rcOpenGraph]

/-- The all-closed configuration never contains an actual open circuit. -/
theorem all_false_not_annulusCircuitEvent (V : Finset (ℤ × ℤ)) (z : ℤ × ℤ) (n : ℕ) :
    (fun _ => false) ∉ annulusCircuitEvent V z n := by
  rintro ⟨m, P, _, _, hP⟩
  obtain ⟨_, _, hadj⟩ := hP 0
  rw [rcOpenGraph_all_false] at hadj
  exact hadj

/-- The literal square of radius n+1 supplies an actual annulus circuit in an
all-open sample whenever the finite domain contains box(2n). -/
theorem all_true_mem_annulusCircuitEvent (R n : ℕ) (hR : 2 ≤ R) (hn : 1 ≤ n) :
    (fun _ => true) ∈ annulusCircuitEvent (box (R*n)) (0, 0) n := by
  let a : FKC.LatticeVertex := (-(n:ℤ)-1, -(n:ℤ)-1)
  let w := 2*n+2
  let P := PlanarTopology.rectangleLatticePolygon a w w (by dsimp [w]; omega) (by dsimp [w]; omega)
  have hboundary (i : ZMod ((2*w+2*w-3)+3)) :=
    (PlanarTopology.mem_rectanglePolygon_vertices_iff a w w
      (by dsimp [w]; omega) (by dsimp [w]; omega) (P.vertex i)).mp ⟨i, rfl⟩
  have hgeom (i : ZMod ((2*w+2*w-3)+3)) :
      (n : ℤ) < max |(P.vertex i).1| |(P.vertex i).2| ∧
      max |(P.vertex i).1| |(P.vertex i).2| ≤ 2*(n:ℤ) := by
    have hi := hboundary i
    dsimp only [a, w] at hi
    simp only [abs_eq_max_neg]
    omega
  have hV (i : ZMod ((2*w+2*w-3)+3)) : P.vertex i ∈ box (R*n) := by
    have hi := (hgeom i).2
    have hmul := Nat.mul_le_mul_right n hR
    rw [Foundations.mem_box_iff_interval]
    have hx := le_trans (le_max_left _ _) hi
    have hy := le_trans (le_max_right _ _) hi
    rw [abs_le] at hx hy
    constructor <;> constructor <;> omega
  have hcenter : FKC.latticeEmbed ⟨1, zero_lt_one⟩ (0, 0) ∈ P.domain ⟨1, zero_lt_one⟩ := by
    rw [PlanarTopology.rectangleLatticePolygon_domain a w w
      (by dsimp [w]; omega) (by dsimp [w]; omega)]
    dsimp [FKC.latticeEmbed, PlanarTopology.complexOpenRectangle, a, w]
    push_cast
    norm_num only [mul_zero, one_mul, Int.cast_zero]
    constructor <;> constructor <;> linarith only [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨2*w+2*w-3, P, hcenter, ?_, ?_⟩
  · intro i
    simpa only [Prod.fst_zero, Prod.snd_zero, sub_zero] using hgeom i
  · intro i
    refine ⟨hV i, hV (i+1), ?_⟩
    rw [rcOpenGraph_all_true]
    apply (PD.FK.squareLattice_adj_iff _ _).mpr
    exact P.adjacent i

/-- The annulus circuit event has probability strictly below one, on every
finite domain and at every scale, by the positive all-closed configuration. -/
theorem finite_annulusCircuit_probability_lt_one (θ : PD.FK.Parameters)
    (V : Finset (ℤ × ℤ)) (ξ : PD.FK.BoundaryCondition (V : Set (ℤ × ℤ)))
    (z : ℤ × ℤ) (n : ℕ) :
    finiteBoundaryEventProbability V θ ξ (fun ω => ω ∈ annulusCircuitEvent V z n) < 1 := by
  classical
  let S := finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n)
  let ρ := PD.FK.measure (squareLattice.induce (V : Set (ℤ × ℤ))) θ ξ
  have hcomp : 0 < (ρ Sᶜ).toReal := by
    have h := (finiteBoundaryEventProbability_pos_iff V θ ξ
      (fun ω => ω ∉ annulusCircuitEvent V z n)).mpr
      ⟨fun _ => false, all_false_not_annulusCircuitEvent V z n⟩
    exact h
  have hsum := measureReal_add_measureReal_compl (μ := ρ)
    (s := S) MeasurableSpace.measurableSet_top
  have huniv : ρ.real Set.univ = 1 := probReal_univ
  rw [huniv] at hsum
  change (ρ S).toReal < 1
  change (ρ S).toReal + (ρ Sᶜ).toReal = 1 at hsum
  linarith only [hcomp, hsum]

/-- The source annulus probability is strictly below one on its full carrier. -/
theorem annulusProbability_lt_one (θ : PD.FK.Parameters) (R n : ℕ) :
    annulusProbability θ R n < 1 :=
  finite_annulusCircuit_probability_lt_one θ _ _ _ _

end PottsContinuity.RSW
