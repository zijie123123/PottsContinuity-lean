module

public import PottsContinuity.PlanarTopology.BalancedBottomEnlargement
public import PottsContinuity.PlanarTopology.BalancedSeedDominantLimit
public import PottsContinuity.PlanarTopology.BalancedCellTranspose

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite BD12 Filter Topology
noncomputable section

/-- The DRT maximum estimate with arbitrary fixed integral horizontal and
vertical enlargements. It applies to actual crossings and needs no symmetry. -/
theorem drt_fixed_enlargement_crossing_max_eventually_gt
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hdualUnique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hdualInfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω)
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent)
    (dx dy : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n k : ℕ, N < n → N < k →
      1-ε < max (μ.real (horizontalRectangle (0,0) (n+dx) k))
        (μ.real (verticalRectangle (0,0) n (k+dy))) := by
  let δ := ε/5
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨RV,hV⟩ := balanced_bottom_connection_enlarges_to_vertical μ htranslation hFKG
    hdualUnique hdualInfinite hunique hinfinite dy δ hδ
  let ν := μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso)
  obtain ⟨RH,hH⟩ := balanced_bottom_connection_enlarges_to_vertical ν
    (transposeLaw_translation_invariant μ htranslation) (transposeLaw_FKG μ hFKG)
    (transposeLaw_dual_unique μ hdualUnique) (transposeLaw_dual_infinite μ hdualInfinite)
    (configurationIsoLaw_unique latticeTransposeIso μ hunique)
    (configurationIsoLaw_infinite latticeTransposeIso μ hinfinite) dx δ hδ
  obtain ⟨RD,hD⟩ := balanced_seed_dominant_probability_eventually_gt μ htranslation hFKG hinfinite δ hδ
  let r := max RV (max RH RD)
  have hrV : RV ≤ r := le_max_left _ _
  have hrH : RH ≤ r := le_trans (le_max_left _ _) (le_max_right _ _)
  have hrD : RD ≤ r := le_trans (le_max_right _ _) (le_max_right _ _)
  let s := 2*r+2
  obtain ⟨NV,hNV⟩ := hV r hrV
  obtain ⟨NH,hNH⟩ := hH r hrH
  refine ⟨NV+NH+s+1,?_⟩
  intro n k hn hk
  let W := n-s
  let H := k-s
  have hw : W+s = n := by dsimp [W]; omega
  have hh : H+s = k := by dsimp [H]; omega
  have hWV : NV < W := by dsimp [W]; omega
  have hHV : NV < H := by dsimp [H]; omega
  have hWH : NH < W := by dsimp [W]; omega
  have hHH : NH < H := by dsimp [H]; omega
  obtain ⟨v,x,y,hc⟩ := exists_rectangleSeedBalancedCell μ W H s (by omega) (by omega)
  have hdom := hD r hrD W H v x y hc
  rcases lt_max_iff.mp hdom with hleft | hbottom
  · have hb : 1-δ < rectangleSeedBottomProbability ν H W s v.swap := by
      simpa only [ν,transposeLaw_rectangleSeedBottomProbability] using hleft
    have hc' := hNH H W hHH hWH v.swap y.swap x.swap hc.transpose hb
    have heq : ν.real (verticalRectangle (0,0) (H+s) (W+s+dx)) =
        μ.real (horizontalRectangle (0,0) (W+s+dx) (H+s)) := by
      have ht := congrArg ENNReal.toReal (transposeLaw_verticalRectangle μ (0,0) (W+s+dx) (H+s))
      simpa only [ν,Measure.real_def,Prod.swap,Prod.fst,Prod.snd] using ht
    change 1-5*δ < ν.real (verticalRectangle (0,0) (H+s) (W+s+dx)) at hc'
    rw [heq,hw,hh] at hc'
    have hle := le_max_left (μ.real (horizontalRectangle (0,0) (n+dx) k))
      (μ.real (verticalRectangle (0,0) n (k+dy)))
    dsimp [δ] at hc'
    linarith
  · have hc' := hNV W H hWV hHV v x y hc hbottom
    change 1-5*δ < μ.real (verticalRectangle (0,0) (W+s) (H+s+dy)) at hc'
    rw [hw,hh] at hc'
    have hle := le_max_right (μ.real (horizontalRectangle (0,0) (n+dx) k))
      (μ.real (verticalRectangle (0,0) n (k+dy)))
    dsimp [δ] at hc'
    linarith

/-- Along every pair of diverging integral side lengths, the enlarged maximum
of the actual horizontal and vertical crossing probabilities tends to one. -/
theorem drt_fixed_enlargement_crossing_max_tendsto_one
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hdualUnique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hdualInfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω)
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent)
    (dx dy : ℕ) (n k : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hk : Tendsto k atTop atTop) :
    Tendsto (fun j => max (μ.real (horizontalRectangle (0,0) (n j+dx) (k j)))
      (μ.real (verticalRectangle (0,0) (n j) (k j+dy)))) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨N,hN⟩ := drt_fixed_enlargement_crossing_max_eventually_gt μ htranslation hFKG
      hdualUnique hdualInfinite hunique hinfinite dx dy (1-b) (by linarith)
    filter_upwards [hn.eventually_gt_atTop N,hk.eventually_gt_atTop N] with j hjn hjk
    have hh := hN (n j) (k j) hjn hjk
    linarith
  · intro b hb
    exact Filter.Eventually.of_forall (fun _ => lt_of_le_of_lt
      (max_le measureReal_le_one measureReal_le_one) hb)

end
end PottsContinuity.PlanarTopology
