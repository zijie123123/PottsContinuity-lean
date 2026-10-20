module

public import PottsContinuity.PlanarTopology.RectangleDualGraphBridge
public import PottsContinuity.PlanarTopology.AlphaTargetGraphBridge
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- Alpha-target four-arc dual existence in PD's EXACT original rectangle
and true complementary dual configuration. The integer face-base sets are
the half-cell-correct complementary ports for the arm event. -/
theorem alpha_target_dual_exists (k : ℕ) (hk : 1 ≤ k)
    (A : PD.FK.Configuration
      (PD.FK.rectangleGraph (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k)))
    (hno : ¬∃ u : PD.FK.RectangleVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k),
      (u.val.2 = 64*(k : ℤ) ∧ -(k : ℤ) ≤ u.val.1 ∧ u.val.1 ≤ (k : ℤ)) ∧
      ∃ v : PD.FK.RectangleVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k),
        (v.val.2 = -64*(k : ℤ) ∧ -(k : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (k : ℤ)) ∧
        PD.FK.ActualConnected _ A u v) :
    ∃ b : PD.FK.RectangleDualVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k),
      b.val ∈ alphaLeftDualPorts k ∧
      ∃ d : PD.FK.RectangleDualVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k),
        d.val ∈ alphaRightDualPorts k ∧
        (PD.FK.openGraph
          (PD.FK.rectangleDualGraph (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k))
          (PD.FK.rectangleDualConfiguration (-65*(k : ℤ),-64*(k : ℤ))
            (130*k) (128*k) A)).Reachable b d := by
  let δ : FKC.PositiveMesh := ⟨1,by norm_num⟩
  let e := alphaTargetRectangleGraphIso k hk δ
  obtain ⟨x,hx,y,hy,hxy⟩ := alphaTargetRectangle_transported_dual_exists k hk δ A hno
  have hxexpanded : x ∈ PD.FK.rectangleDualExpanded
      (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k) := by
    rw [PD.FK.rectangleDualExpanded,PD.FK.mem_latticeRectangle]
    change (-65*(k : ℤ)-1 ≤ x.1 ∧ x.1 ≤ -65*(k : ℤ)-1+((130*k+1 : ℕ) : ℤ)) ∧
      (-64*(k : ℤ)-1 ≤ x.2 ∧ x.2 ≤ -64*(k : ℤ)-1+((128*k+1 : ℕ) : ℤ))
    change (x.1 = -65*(k : ℤ)-1 ∧ -64*(k : ℤ) ≤ x.2 ∧ x.2 < 64*(k : ℤ)) ∨
      ((x.2 = -64*(k : ℤ)-1 ∨ x.2 = 64*(k : ℤ)) ∧
        -65*(k : ℤ) ≤ x.1 ∧ x.1 < -(k : ℤ)) at hx
    omega
  let b : PD.FK.RectangleDualVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k) :=
    ⟨x,hxexpanded⟩
  obtain ⟨d,hd,hbd⟩ := domain_closed_dual_reachable_to_pd
    (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k) e
    (alphaTargetRectangleGraphIso_val k hk δ) A hxy b rfl
  refine ⟨b,hx,d,?_,hbd⟩
  rwa [hd]

end PottsContinuity.PlanarTopology
