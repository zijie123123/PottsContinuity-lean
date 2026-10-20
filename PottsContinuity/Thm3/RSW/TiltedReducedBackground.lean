module

public import PottsContinuity.Thm3.RSW.TiltedStripReducedReads

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial Thm3.Prop4 MeasureTheory
noncomputable section

/-- The upper open frozen background, on actual whole-plane bond labels. -/
def tiltedReducedUpperBond (N : ℕ) (t : ℝ) (b : LatticeBond) : Prop :=
  (N : ℝ) < tiltedHeight t b.source+1 ∧ (N : ℝ) < tiltedHeight t b.target+1

/-- At positive height, every bond outside the reduced carrier has its
fixed background state complemented by the genuine crossed involution. -/
theorem tiltedReducedUpperBond_crossed_complement
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (b : LatticeBond)
    (hout : ¬ (b.source ∈ tiltedStripVertices N t ∧ b.target ∈ tiltedStripVertices N t ∧
      ¬ (tiltedTop N t b.source ∧ tiltedTop N t b.target))) :
    tiltedReducedUpperBond N t b ↔
      ¬ tiltedReducedUpperBond N t (tiltedStripReducedCrossedBond N t b) := by
  rw [tiltedStripReducedCarrier_iff N t ht] at hout
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> by_cases hp : 0 < t
  all_goals
    simp only [tiltedReducedUpperBond,tiltedStripReducedCrossedBond,hp,ite_true,ite_false,
      LatticeBond.source,LatticeBond.target,tiltedHeight] at hout ⊢
    push_cast at hout ⊢
    constructor
    · rintro ⟨ha,hb⟩ ⟨hc,hd⟩
      linarith
    · intro hdual
      by_contra hsource
      simp only [not_and_or,not_lt] at hsource hdual
      apply hout
      rcases hsource with ha | ha
      all_goals rcases hdual with hb | hb
      all_goals constructor <;> linarith

/-- At height zero the prescribed reduced carrier is empty, including the
fractional-slope cases where the original strip itself can be sparse. -/
theorem tiltedStripReducedCarrier_zero_isEmpty (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    IsEmpty (tiltedStripReducedCarrier 0 t) := by
  refine ⟨?_⟩
  intro b
  have hb := (tiltedStripReducedCarrier_iff 0 t ht b.val.val).mp
    ⟨b.val.property.1,b.val.property.2,b.property⟩
  rcases b with ⟨⟨⟨⟨x,y⟩,ax⟩,hstrip⟩,htop⟩
  cases ax <;> by_cases hp : 0 < t
  all_goals simp only [hp,ite_true,ite_false,Nat.cast_zero] at hb
  all_goals linarith [hb.1,hb.2]

/-- The requested reduced marginal identity at height zero, with no
probability or finite-duality premise. -/
theorem selfDual_tiltedStrip_reflected_marginal_zero_height
    (q : Set.Ici (1 : ℝ)) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    Measure.map (tiltedStripReducedDualTransport 0 t ht)
      (Measure.map (tiltedStripReducedRestriction 0 t) (selfDualTiltedStripMeasure q 0 t)) =
      Measure.map (tiltedStripReducedRestriction 0 t) (selfDualTiltedStripMeasure q 0 t) := by
  have hempty := tiltedStripReducedCarrier_zero_isEmpty t ht
  have hid : tiltedStripReducedDualTransport 0 t ht = id := by
    funext ω b
    exact (hempty.false b).elim
  rw [hid,Measure.map_id]

end
end PottsContinuity.RSW
