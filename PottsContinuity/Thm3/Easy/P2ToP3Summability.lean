module

public import Mathlib
public import PottsContinuity.BD12.WiredSquare
public import PottsContinuity.Foundations.BoxBoundary
public import PottsContinuity.Foundations.Bridges
public import PottsContinuity.PD.Duality.ConnectionEvents
public import PottsContinuity.PD.RCInfinite.FiniteBoxCounting
public import PottsContinuity.Thm3.Easy.P2ToP3WeakRSW

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open MeasureTheory
open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.CorrLength
open scoped ENNReal

def p2p3BoundaryShell (n : ℕ) :=
  {y : LatticeVertex // y ∈
    PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) (n + 1))}

private theorem p2p3Boundary_latticeBox_max (r : ℕ) (y : LatticeVertex)
    (hy : y ∈ PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) r)) :
    max |y.1| |y.2| = (r : ℤ) := by
  have hbox : PottsContinuity.box r = latticeBox (0, 0) r := by
    ext z
    simp [PottsContinuity.box, latticeBox, Finset.mem_product,
      Finset.mem_Icc]
  rw [← Foundations.vertexBoundary_eq_PD (latticeBox (0, 0) r)] at hy
  rw [← hbox] at hy
  rw [Foundations.vertexBoundary_box_eq r] at hy
  exact hy

private theorem p2p3Boundary_finite (r : ℕ) :
    (PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) r)).Finite := by
  apply (latticeBox (0, 0) r).finite_toSet.subset
  intro y hy
  exact hy.1

private theorem p2p3BoundaryShell_injective :
    Function.Injective
      (fun i : Σ n : ℕ, p2p3BoundaryShell n => i.2.1) := by
  intro i j hij
  cases i with
  | mk n y =>
    cases j with
    | mk m z =>
      change y.1 = z.1 at hij
      have hi := p2p3Boundary_latticeBox_max (n + 1) y.1 y.2
      have hj := p2p3Boundary_latticeBox_max (m + 1) z.1 z.2
      have hrad := congrArg (fun v : LatticeVertex => max |v.1| |v.2|) hij
      rw [hi, hj] at hrad
      have hidx : n = m := by omega
      subst m
      have hyz : y = z := Subtype.ext hij
      subst z
      rfl

private theorem p2p3_boundary_shell_lower
    (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure (squareLattice.edgeSet → Bool))
    (hμ₀ : IsRCInfiniteVolumeLimit
      (PottsContinuity.PD.FK.criticalParameters q).toP
      (PottsContinuity.PD.FK.criticalParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit
      (PottsContinuity.PD.FK.criticalParameters q).toP
      (PottsContinuity.PD.FK.criticalParameters q).toQ 1 μ₁)
    (hP2 : μ₀ = μ₁)
    (hWeakRSW : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ μ₁.real (PottsContinuity.BD12.verticalRectangle
        (-(n : ℤ), 0) (2 * n) n))
    (n : ℕ) :
    ENNReal.ofReal (hWeakRSW.choose / (2 * ((n + 1 : ℕ) : ℝ) + 1)) ≤
      ∑' y : p2p3BoundaryShell n,
        μ₀ (connectionEvent (0, 0) y.1) := by
  classical
  let : IsProbabilityMeasure μ₀ := hμ₀.1
  have hArm₁ := wired_weakRSW_oneArm_lower_bound q μ₁ hμ₁ hWeakRSW
    (n + 1) (by omega)
  have hArm : hWeakRSW.choose / (2 * ((n + 1 : ℕ) : ℝ) + 1) ≤
      μ₀.real (oneArmBoundaryEvent (0, 0) (n + 1)) := by
    rw [hP2]
    exact hArm₁
  have hfinite := p2p3Boundary_finite (n + 1)
  let : Fintype (p2p3BoundaryShell n) := hfinite.fintype
  have hsubset : oneArmBoundaryEvent (0, 0) (n + 1) ⊆
      ⋃ y : p2p3BoundaryShell n, connectionEvent (0, 0) y.1 := by
    intro ω hω
    rcases hω with ⟨y, hy, hconn⟩
    exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, hconn⟩
  have hrealShell :
      μ₀.real (oneArmBoundaryEvent (0, 0) (n + 1)) ≤
        ∑ y : p2p3BoundaryShell n, μ₀.real (connectionEvent (0, 0) y.1) := by
    calc
      μ₀.real (oneArmBoundaryEvent (0, 0) (n + 1)) ≤
          μ₀.real (⋃ y : p2p3BoundaryShell n, connectionEvent (0, 0) y.1) :=
            measureReal_mono hsubset
      _ ≤ ∑ y : p2p3BoundaryShell n, μ₀.real (connectionEvent (0, 0) y.1) :=
        measureReal_iUnion_fintype_le (μ := μ₀) _
  have hsumTop :
      (∑ y : p2p3BoundaryShell n, μ₀ (connectionEvent (0, 0) y.1)) ≠ ∞ := by
    exact ENNReal.sum_ne_top
      (s := (Finset.univ : Finset (p2p3BoundaryShell n)))
      (f := fun y : p2p3BoundaryShell n => μ₀ (connectionEvent (0, 0) y.1)) |>.2
        (by
          intro y hy
          exact measure_ne_top μ₀ _)
  have hsumReal :
      ENNReal.toReal
          (∑ y : p2p3BoundaryShell n, μ₀ (connectionEvent (0, 0) y.1)) =
        ∑ y : p2p3BoundaryShell n, μ₀.real (connectionEvent (0, 0) y.1) := by
    rw [ENNReal.toReal_sum (s := (Finset.univ : Finset (p2p3BoundaryShell n)))
        (f := fun y : p2p3BoundaryShell n => μ₀ (connectionEvent (0, 0) y.1))
        (by
          intro y hy
          exact measure_ne_top μ₀ _)]
    rfl
  have hENN : ENNReal.ofReal
      (hWeakRSW.choose / (2 * ((n + 1 : ℕ) : ℝ) + 1)) ≤
        ∑ y : p2p3BoundaryShell n, μ₀ (connectionEvent (0, 0) y.1) := by
    apply (ENNReal.ofReal_le_iff_le_toReal hsumTop).2
    calc
      hWeakRSW.choose / (2 * ((n + 1 : ℕ) : ℝ) + 1) ≤
          μ₀.real (oneArmBoundaryEvent (0, 0) (n + 1)) := hArm
      _ ≤ ∑ y : p2p3BoundaryShell n, μ₀.real (connectionEvent (0, 0) y.1) :=
        hrealShell
      _ = ENNReal.toReal
          (∑ y : p2p3BoundaryShell n, μ₀ (connectionEvent (0, 0) y.1)) :=
        hsumReal.symm
  simpa using hENN

private theorem p2p3_harmonic_lower_diverges (c : ℝ) (hc : 0 < c) :
    ∑' n : ℕ, ENNReal.ofReal (c / (2 * ((n + 1 : ℕ) : ℝ) + 1)) = ∞ := by
  by_contra hsum
  have hrealSummable := ENNReal.summable_toReal hsum
  have hD : Summable (fun n : ℕ => c / (2 * ((n + 1 : ℕ) : ℝ) + 1)) := by
    convert hrealSummable using 1
    ext n
    exact (ENNReal.toReal_ofReal (by positivity)).symm
  let k := c / 3
  have hk : 0 < k := by dsimp [k]; positivity
  have hscaled : Summable (fun n : ℕ => k / ((n + 1 : ℕ) : ℝ)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => by
      have hden :
          (2 * ((n + 1 : ℕ) : ℝ) + 1) ≤ 3 * ((n + 1 : ℕ) : ℝ) := by
        have hn1 : 1 ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        nlinarith
      have hdenpos : 0 < 2 * ((n + 1 : ℕ) : ℝ) + 1 := by positivity
      have hnpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      apply (div_le_div_iff₀ hnpos hdenpos).2
      have hkden : k * (2 * ((n + 1 : ℕ) : ℝ) + 1) ≤
          c * ((n + 1 : ℕ) : ℝ) := by
        dsimp [k]
        calc
          (c / 3) * (2 * ((n + 1 : ℕ) : ℝ) + 1) ≤
              (c / 3) * (3 * ((n + 1 : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_left hden (by positivity)
          _ = c * ((n + 1 : ℕ) : ℝ) := by ring
      simpa [k, mul_comm] using hkden) hD
  have hscaled' : Summable
      (fun n : ℕ => k * (1 / ((n + 1 : ℕ) : ℝ))) := by
    simpa [div_eq_mul_inv, one_div, mul_comm] using hscaled
  have hshift : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) :=
    (summable_mul_left_iff hk.ne').1 hscaled'
  have hunshift : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    apply (summable_nat_add_iff 1).1
    simpa [Nat.cast_add] using hshift
  exact Real.not_summable_one_div_natCast hunshift

private theorem p2p3_corrConnectionEvent_eq_dualityConnectionEvent (u v : ℤ × ℤ) :
    PottsContinuity.PD.CorrLength.connectionEvent u v =
      PottsContinuity.PD.Duality.connectionEvent u v := by
  ext ω
  simp only [PottsContinuity.PD.Duality.connectionEvent,
    PottsContinuity.PD.Duality.cluster, Set.mem_ofPred_eq]
  exact PottsContinuity.PD.CorrLength.connectionEvent_iff_rcInfiniteReachable u v ω

private theorem p2p3_pairZero_eq_pair :
    (0 : ℤ × ℤ) = ((0 : ℤ), (0 : ℤ)) := by
  ext <;> rfl

private theorem p2p3_frozenConnectionEvent_eq_dualityConnectionEvent (x : ℤ × ℤ) :
    {ω | (PottsContinuity.rcInfiniteOpenGraph ω).Reachable (0, 0) x} =
      PottsContinuity.PD.Duality.connectionEvent 0 x := by
  ext ω
  change (PottsContinuity.rcInfiniteOpenGraph ω).Reachable (0, 0) x ↔
    (PottsContinuity.PD.rcInfiniteOpenGraph ω).Reachable 0 x
  rw [p2p3_pairZero_eq_pair]
  rw [Foundations.rcInfiniteOpenGraph_eq_PD]

/-- P2 implies infinite susceptibility at the explicit self-dual parameter,
conditional only on the wired aspect-two RSW statement given as its
hypothesis. -/
theorem p2_implies_p3_of_weakRSW
    (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure (squareLattice.edgeSet → Bool))
    (hμ₀ : IsRCInfiniteVolumeLimit
      (PottsContinuity.PD.FK.criticalParameters q).toP
      (PottsContinuity.PD.FK.criticalParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit
      (PottsContinuity.PD.FK.criticalParameters q).toP
      (PottsContinuity.PD.FK.criticalParameters q).toQ 1 μ₁)
    (hP2 : μ₀ = μ₁)
    (hWeakRSW : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ μ₁.real (PottsContinuity.BD12.verticalRectangle
        (-(n : ℤ), 0) (2 * n) n)) :
    ∑' x : ℤ × ℤ,
      μ₀ {ω | (PottsContinuity.rcInfiniteOpenGraph ω).Reachable (0, 0) x} = ∞ := by
  let f : LatticeVertex → ℝ≥0∞ := fun x =>
    μ₀ (connectionEvent (0, 0) x)
  have hinj := p2p3BoundaryShell_injective
  have hsubsum :
      (∑' i : Σ n : ℕ, p2p3BoundaryShell n, f i.2.1) ≤ ∑' x : LatticeVertex, f x := by
    exact ENNReal.tsum_comp_le_tsum_of_injective hinj f
  have hshell : ∀ n : ℕ,
      ENNReal.ofReal (hWeakRSW.choose / (2 * ((n + 1 : ℕ) : ℝ) + 1)) ≤
        ∑' y : p2p3BoundaryShell n, f y.1 := by
    intro n
    exact p2p3_boundary_shell_lower q μ₀ μ₁ hμ₀ hμ₁ hP2 hWeakRSW n
  have hseries :
      (∑' n : ℕ,
        ENNReal.ofReal (hWeakRSW.choose / (2 * ((n + 1 : ℕ) : ℝ) + 1))) ≤
        ∑' x : LatticeVertex, f x := by
    calc
      _ ≤ ∑' n : ℕ, ∑' y : p2p3BoundaryShell n, f y.1 :=
        ENNReal.tsum_le_tsum hshell
      _ = ∑' i : Σ n : ℕ, p2p3BoundaryShell n, f i.2.1 := by
        symm
        exact ENNReal.tsum_sigma' _
      _ ≤ _ := hsubsum
  cases Foundations.squareLattice_eq_PD
  have hdiv := p2p3_harmonic_lower_diverges hWeakRSW.choose hWeakRSW.choose_spec.1
  have htotal : ∑' x : LatticeVertex, f x = ∞ := by
    apply top_unique
    calc
      ∞ = ∑' n : ℕ,
          ENNReal.ofReal (hWeakRSW.choose / (2 * ((n + 1 : ℕ) : ℝ) + 1)) := hdiv.symm
      _ ≤ ∑' x : LatticeVertex, f x := hseries
  have htotalPD : ∑' x : ℤ × ℤ,
      μ₀ (PottsContinuity.PD.Duality.connectionEvent 0 x) = ∞ := by
    simpa only [f, PottsContinuity.PD.FK.LatticeVertex,
      p2p3_corrConnectionEvent_eq_dualityConnectionEvent,
      p2p3_pairZero_eq_pair] using htotal
  simpa only [p2p3_frozenConnectionEvent_eq_dualityConnectionEvent] using htotalPD

end PottsContinuity.Thm3.Easy
