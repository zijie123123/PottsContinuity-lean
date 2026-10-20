module

public import PottsContinuity.PlanarTopology.RectangleConnectionTransport
public import PottsContinuity.PlanarTopology.BalancedSeedCell
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK
noncomputable section

theorem transposeLaw_rectangleSeedConnectionEvent (μ : Measure LatticeConfiguration)
    (W H s : ℕ) (v : Fin (W+1) × Fin (H+1)) (T : Set LatticeVertex) :
    (μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso)).real
      (rectangleSeedConnectionEvent H W s v.swap T) =
    μ.real (rectangleSeedConnectionEvent W H s v (Prod.swap ⁻¹' T)) := by
  have hh := transposeLaw_rectangleConnectionEvent μ (0,0) (W+s) (H+s)
    (latticeRectangle ((v.2.val:ℤ),(v.1.val:ℤ)) s s : Set LatticeVertex) T
  have hs : Prod.swap ⁻¹'
      (latticeRectangle ((v.2.val:ℤ),(v.1.val:ℤ)) s s : Set LatticeVertex) =
      (latticeRectangle ((v.1.val:ℤ),(v.2.val:ℤ)) s s : Set LatticeVertex) := by
    ext z
    simp only [Set.mem_preimage,Finset.mem_coe,mem_latticeRectangle,Prod.swap]
    tauto
  rw [hs] at hh
  exact congrArg ENNReal.toReal hh

theorem transposeLaw_rectangleSeedLeftProbability (μ : Measure LatticeConfiguration)
    (W H s : ℕ) (v : Fin (W+1) × Fin (H+1)) :
    rectangleSeedLeftProbability (μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso)) H W s v.swap =
    rectangleSeedBottomProbability μ W H s v :=
  transposeLaw_rectangleSeedConnectionEvent μ W H s v {z | z.1 = 0}

theorem transposeLaw_rectangleSeedRightProbability (μ : Measure LatticeConfiguration)
    (W H s : ℕ) (v : Fin (W+1) × Fin (H+1)) :
    rectangleSeedRightProbability (μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso)) H W s v.swap =
    rectangleSeedTopProbability μ W H s v :=
  transposeLaw_rectangleSeedConnectionEvent μ W H s v {z | z.1 = ((H+s:ℕ):ℤ)}

theorem transposeLaw_rectangleSeedBottomProbability (μ : Measure LatticeConfiguration)
    (W H s : ℕ) (v : Fin (W+1) × Fin (H+1)) :
    rectangleSeedBottomProbability (μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso)) H W s v.swap =
    rectangleSeedLeftProbability μ W H s v :=
  transposeLaw_rectangleSeedConnectionEvent μ W H s v {z | z.2 = 0}

theorem transposeLaw_rectangleSeedTopProbability (μ : Measure LatticeConfiguration)
    (W H s : ℕ) (v : Fin (W+1) × Fin (H+1)) :
    rectangleSeedTopProbability (μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso)) H W s v.swap =
    rectangleSeedRightProbability μ W H s v :=
  transposeLaw_rectangleSeedConnectionEvent μ W H s v {z | z.2 = ((W+s:ℕ):ℤ)}

/-- Transposition exchanges the two reverse witnesses as well as the two
coordinate comparisons. The measure is transported, with no symmetry premise. -/
theorem RectangleSeedBalancedCell.transpose {μ : Measure LatticeConfiguration}
    {W H s : ℕ} {v x y : Fin (W+1) × Fin (H+1)}
    (hc : RectangleSeedBalancedCell μ W H s v x y) :
    RectangleSeedBalancedCell (μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso))
      H W s v.swap y.swap x.swap := by
  constructor
  · simpa only [transposeLaw_rectangleSeedRightProbability,transposeLaw_rectangleSeedLeftProbability]
      using hc.bottom_ge_top
  · simpa only [transposeLaw_rectangleSeedTopProbability,transposeLaw_rectangleSeedBottomProbability]
      using hc.left_ge_right
  · simpa only [transposeLaw_rectangleSeedLeftProbability,transposeLaw_rectangleSeedRightProbability]
      using hc.top_ge_bottom
  · simpa only [transposeLaw_rectangleSeedBottomProbability,transposeLaw_rectangleSeedTopProbability]
      using hc.right_ge_left
  · exact hc.top_close_snd
  · exact hc.top_close_fst
  · exact hc.right_close_snd
  · exact hc.right_close_fst

end
end PottsContinuity.PlanarTopology
