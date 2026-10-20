module

public import PottsContinuity.Thm3.RSW.TiltedReducedActiveGeometry

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt Thm3.Prop4
noncomputable section

/-- A bounded core uses the full rectangular dual vertex carrier, including
isolated top vertices, through the inverse genuine crossed half-turn. -/
def tiltedReducedCoreDualEmbedding (N L M : ℕ) (t : ℝ) (hM : L+N+3 ≤ M) :
    (tiltedWindow N L t : Set (ℤ × ℤ)) ↪
      RectangleDualVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) where
  toFun z := ⟨tiltedStripReducedDualVertex N t z.val,by
    have hb := (Foundations.mem_box_iff_abs_le L z.val).mp
      ((mem_tiltedWindow N L t z.val).mp z.property).1
    have hx := abs_le.mp hb.1
    have hy := abs_le.mp hb.2
    unfold rectangleDualExpanded
    rw [mem_latticeRectangle]
    dsimp [tiltedStripReducedDualVertex]
    split_ifs <;> constructor <;> constructor <;> omega⟩
  inj' := by
    intro x y heq
    apply Subtype.ext
    have hv := congrArg (fun z : RectangleDualVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ))
      (2*M) (2*(M+N+2)) => z.val) heq
    apply Prod.ext
    · have hx := congrArg Prod.fst hv
      dsimp [tiltedStripReducedDualVertex] at hx
      omega
    · have hy := congrArg Prod.snd hv
      dsimp [tiltedStripReducedDualVertex] at hy
      omega

/-- Transporting the embedded core back gives its unchanged physical vertex. -/
theorem tiltedReducedCoreDualEmbedding_replay (N L M : ℕ) (t : ℝ) (hM : L+N+3 ≤ M)
    (z : (tiltedWindow N L t : Set (ℤ × ℤ))) :
    tiltedStripReducedDualVertex N t (tiltedReducedCoreDualEmbedding N L M t hM z).val = z.val := by
  change tiltedStripReducedDualVertex N t (tiltedStripReducedDualVertex N t z.val) = z.val
  apply Prod.ext <;> dsimp [tiltedStripReducedDualVertex] <;> omega

/-- The core stays away from all four host dual boundary sides. -/
theorem tiltedReducedCoreDualEmbedding_interior (N L M : ℕ) (t : ℝ) (hM : L+N+3 ≤ M)
    (z : (tiltedWindow N L t : Set (ℤ × ℤ))) :
    (tiltedReducedCoreDualEmbedding N L M t hM z).val ∈
      rectangleDualInterior (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) := by
  classical
  have hb := (Foundations.mem_box_iff_abs_le L z.val).mp
    ((mem_tiltedWindow N L t z.val).mp z.property).1
  have hx := abs_le.mp hb.1
  have hy := abs_le.mp hb.2
  rw [rectangleDualInterior,Finset.mem_filter]
  refine ⟨(tiltedReducedCoreDualEmbedding N L M t hM z).property,?_⟩
  change -(M:ℤ) ≤ (tiltedStripReducedDualVertex N t z.val).1 ∧
    (tiltedStripReducedDualVertex N t z.val).1 < -(M:ℤ)+(2*M:ℕ) ∧
    -((M+N+2:ℕ):ℤ) ≤ (tiltedStripReducedDualVertex N t z.val).2 ∧
    (tiltedStripReducedDualVertex N t z.val).2 < -((M+N+2:ℕ):ℤ)+(2*(M+N+2):ℕ)
  dsimp [tiltedStripReducedDualVertex]
  split_ifs <;> omega

end
end PottsContinuity.RSW
