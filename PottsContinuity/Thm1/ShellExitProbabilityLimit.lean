module

public import PottsContinuity.Thm1.ShellExitInnerComparison
public import PottsContinuity.Thm1.ShellExitLimit
public import PottsContinuity.PD.RCInfinite.Cylinders

@[expose] public section

namespace PottsContinuity.Thm1

open MeasureTheory Filter Topology
open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance pottsESExitLimitVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESExitLimitEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESExitLimitEdgeDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

private theorem pottsESBoxEdges_mono {m n : ℕ} (hmn : m ≤ n) :
    boxEdges (0, 0) m ⊆ boxEdges (0, 0) n := by
  intro e he
  rw [mem_boxEdges_iff] at he ⊢
  intro x hx
  exact latticeBox_mono (0, 0) hmn (he x hx)

theorem pottsESShellExitProbability_eq_finiteConnection
    (θ : Parameters) (V : Finset (ℤ × ℤ)) (h0 : (0, 0) ∈ V) :
    (pottsESShellBondProbabilityMeasure θ V : Measure LatticeConfiguration).real
        (pottsESLatticeExitEvent V) =
      (measure (pottsESGraph V) θ (pottsESBoundaryCondition V)
        {A | pottsESOriginExteriorConnected V h0 A}).toReal := by
  classical
  have hMeas : MeasurableSet (pottsESLatticeExitEvent V) :=
    (pottsESLatticeExitEvent_isCylinder V h0).measurableSet
  have hEvent :
      {A | pottsESShellBondExtension V A ∈ pottsESLatticeExitEvent V} =
        {A | pottsESOriginExteriorConnected V h0 A} := by
    ext A
    change pottsESLatticeExitEvent V (pottsESShellBondExtension V A) ↔
      pottsESOriginExteriorConnected V h0 A
    exact (pottsESOriginExteriorConnected_iff_latticeExit V h0 A).symm
  rw [Measure.real,
    pottsESShellBondProbabilityMeasure_apply θ V hMeas,
    hEvent]

/-- The finite ghost-connection probability converges along every nested
exhaustion to the wired infinite-cluster probability. -/
theorem pottsESShellExitProbability_tendsto_infiniteAt
    (θ : Parameters) (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (μ : Measure LatticeConfiguration)
    (hμ : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 1 μ) :
    Tendsto
      (fun n =>
        (pottsESShellBondProbabilityMeasure θ (V n) :
          Measure LatticeConfiguration).real
          (pottsESLatticeExitEvent (V n)))
      atTop (𝓝 (μ.real (infiniteAt (0, 0)))) := by
  let := hμ.1
  have hExit := pottsESLatticeExitProbability_tendsto_infiniteAt
    V hNest hExhaust μ
  have hOrigin : ∀ᶠ n : ℕ in atTop, (0, 0) ∈ V n := by
    obtain ⟨N, hN⟩ := hExhaust (0, 0)
    filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    have hSN : V N ⊆ V n := by
      induction hn with
      | refl => exact Finset.Subset.rfl
      | @step k hkn ih => exact ih.trans (hNest k)
    exact hSN hN
  have hLower : ∀ᶠ n : ℕ in atTop,
      μ.real (pottsESLatticeExitEvent (V n)) ≤
        (pottsESShellBondProbabilityMeasure θ (V n) :
          Measure LatticeConfiguration).real
          (pottsESLatticeExitEvent (V n)) := by
    filter_upwards [hOrigin] with n h0n
    rw [pottsESShellExitProbability_eq_finiteConnection θ (V n) h0n]
    exact pottsESLatticeExitProbability_le_pottsESShell θ μ hμ (V n) h0n
  have hBoxExit : Tendsto
      (fun k => μ.real (pottsESLatticeExitEvent (latticeBox (0, 0) k)))
      atTop (𝓝 (μ.real (infiniteAt (0, 0)))) := by
    simpa using pottsESLatticeExitProbability_tendsto_infiniteAt
      (fun k => latticeBox (0, 0) k) origin_latticeBox_nested
      origin_latticeBox_exhaustive μ
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [((tendsto_order.1 hExit).1 a ha).and hLower]
      with n ⟨hnμ, hμn⟩
    exact lt_of_lt_of_le hnμ hμn
  · intro a ha
    obtain ⟨k, hk⟩ := ((tendsto_order.1 hBoxExit).2 a ha).exists
    let W := latticeBox (0, 0) k
    have h0W : (0, 0) ∈ W := by simp [W, latticeBox]
    have hWcyl := pottsESLatticeExitEvent_isCylinder W h0W
    have hWprob : Tendsto
        (fun r => (boxMeasure θ 1 (0, 0) r : Measure LatticeConfiguration).real
          (pottsESLatticeExitEvent W)) atTop
        (𝓝 (μ.real (pottsESLatticeExitEvent W))) :=
      tendsto_cylinder_probability θ 1 μ hμ hWcyl
    let rMin := max (pottsESShellComparisonRadius W) k
    let b := (μ.real (pottsESLatticeExitEvent W) + a) / 2
    have hWb : μ.real (pottsESLatticeExitEvent W) < b := by
      dsimp [b]
      linarith
    have hba : b < a := by
      dsimp [b]
      linarith
    obtain ⟨r, hrProb, hrMin⟩ :=
      (((tendsto_order.1 hWprob).2 b hWb).and
        (Filter.eventually_atTop.2 ⟨rMin, fun r hr => hr⟩)).exists
    have hWedges : (pottsESLatticeEdgeSet W : Set
        PottsContinuity.PD.FK.squareLattice.edgeSet) ⊆ boxEdges (0, 0) r :=
      (pottsESLatticeEdgeSet_subset_shellComparisonBox W).trans
        (pottsESBoxEdges_mono (le_trans (le_max_left _ _) hrMin))
    have hWbox : W ⊆ latticeBox (0, 0) r := by
      dsimp [W]
      exact latticeBox_mono (0, 0) (le_trans (le_max_right _ _) hrMin)
    have hInclude := eventually_latticeBox_subset_of_exhaustion
      V hNest hExhaust r
    filter_upwards [hInclude, hOrigin] with n hInc h0n
    have hWV : W ⊆ V n := hWbox.trans hInc
    have hShell := pottsESOriginExteriorConnectionProbability_le_wiredBoxExit
      θ (V n) h0n r hInc W h0W hWV hWedges
    rw [pottsESShellExitProbability_eq_finiteConnection θ (V n) h0n]
    calc
      (measure (pottsESGraph (V n)) θ (pottsESBoundaryCondition (V n))
        {A | pottsESOriginExteriorConnected (V n) h0n A}).toReal
          ≤ (boxMeasure θ 1 (0, 0) r : Measure LatticeConfiguration).real
            (pottsESLatticeExitEvent W) := hShell
      _ < b := hrProb
      _ < a := hba

end

end PottsContinuity.Thm1
