module

public import PottsContinuity.PlanarTopology.RectangleDualGraphBridge
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- Central-target four-arc dual existence in PD's EXACT original rectangle
and true complementary dual configuration. The integer face-base sets are
precisely the left and right dual ports `centralLeftDualPorts` and
`centralRightDualPorts`. -/
theorem central_target_dual_exists (k : ℕ) (hk : 1 ≤ k)
    (A : PD.FK.Configuration
      (PD.FK.rectangleGraph (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k)))
    (hno : ¬∃ u : PD.FK.RectangleVertex (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k),
      (u.val.2 = 12*(k : ℤ) ∧ -(k : ℤ) ≤ u.val.1 ∧ u.val.1 ≤ (k : ℤ)) ∧
      ∃ v : PD.FK.RectangleVertex (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k),
        (v.val.2 = -12*(k : ℤ) ∧ -(k : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (k : ℤ)) ∧
        PD.FK.ActualConnected _ A u v) :
    ∃ b : PD.FK.RectangleDualVertex (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k),
      b.val ∈ centralLeftDualPorts k ∧
      ∃ d : PD.FK.RectangleDualVertex (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k),
        d.val ∈ centralRightDualPorts k ∧
        (PD.FK.openGraph
          (PD.FK.rectangleDualGraph (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k))
          (PD.FK.rectangleDualConfiguration (-13*(k : ℤ),-12*(k : ℤ))
            (26*k) (24*k) A)).Reachable b d := by
  let δ : FKC.PositiveMesh := ⟨1,by norm_num⟩
  let e := centralTargetRectangleGraphIso k hk δ
  obtain ⟨x,hx,y,hy,hxy⟩ := centralTargetRectangle_transported_dual_exists k hk δ A hno
  have hxexpanded : x ∈ PD.FK.rectangleDualExpanded
      (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k) := by
    rw [PD.FK.rectangleDualExpanded,PD.FK.mem_latticeRectangle]
    change (-13*(k : ℤ)-1 ≤ x.1 ∧ x.1 ≤ -13*(k : ℤ)-1+((26*k+1 : ℕ) : ℤ)) ∧
      (-12*(k : ℤ)-1 ≤ x.2 ∧ x.2 ≤ -12*(k : ℤ)-1+((24*k+1 : ℕ) : ℤ))
    change (x.1 = -13*(k : ℤ)-1 ∧ -12*(k : ℤ) ≤ x.2 ∧ x.2 < 12*(k : ℤ)) ∨
      ((x.2 = -12*(k : ℤ)-1 ∨ x.2 = 12*(k : ℤ)) ∧
        -13*(k : ℤ) ≤ x.1 ∧ x.1 < -(k : ℤ)) at hx
    omega
  let b : PD.FK.RectangleDualVertex (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k) :=
    ⟨x,hxexpanded⟩
  obtain ⟨d,hd,hbd⟩ := domain_closed_dual_reachable_to_pd
    (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k) e
    (centralTargetRectangleGraphIso_val k hk δ) A hxy b rfl
  refine ⟨b,hx,d,?_,hbd⟩
  rwa [hd]

end PottsContinuity.PlanarTopology
