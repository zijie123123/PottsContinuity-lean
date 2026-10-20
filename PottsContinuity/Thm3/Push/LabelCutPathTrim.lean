module

public import PottsContinuity.Thm3.Push.LabelCutPathBounds
public import PottsContinuity.Thm3.Push.FirstArrivalDown
public import PottsContinuity.PlanarTopology.BoundaryWalkClipping
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PlanarTopology
noncomputable section

/-- Trim the two exterior rows from a dual label-cut crossing. Its start is
still adjacent to an actual bottom port, so the source interval can be read
from that original boundary step rather than from an arbitrary later visit. -/
theorem labelCutDual_inner_walk (N : ℕ) (hN : 1 ≤ N)
    (σ : RectangleVertex (-1,-1) (N+1) (N+1) → Bool)
    (hleft : ∀ v, v.val.1 = -1 → σ v = true)
    (hright : ∀ v, v.val.1 = (N : ℤ) → σ v = false) :
    ∃ (i : ℕ) (_hi : i < N+1) (z : RectangleDualVertex (-1,-1) (N+1) (N+1))
      (p : (rectangleLabelCutDualGraph (-1,-1) (N+1) (N+1) σ).Walk
        (rectangleDualBottomUpVertex (-1,-1) (N+1) (N+1) i) z),
      (rectangleLabelCutDualGraph (-1,-1) (N+1) (N+1) σ).Adj
        (rectangleDualBottomPortVertex (-1,-1) (N+1) (N+1) i)
        (rectangleDualBottomUpVertex (-1,-1) (N+1) (N+1) i) ∧
      z.val.2 = (N : ℤ)-1 ∧
      ∀ v ∈ p.support, -1 ≤ v.val.1 ∧ v.val.1 ≤ (N : ℤ)-1 ∧
        -1 ≤ v.val.2 ∧ v.val.2 ≤ (N : ℤ)-1 := by
  classical
  have hright' : ∀ v : RectangleVertex (-1,-1) (N+1) (N+1),
      v.val.1 = (-1 : ℤ)+(N+1 : ℕ) → σ v = false := by
    intro v hv
    apply hright v
    omega
  obtain ⟨b,hb,d,hd,⟨q⟩⟩ := rectangleLabelCutDual_bottom_top_reachable
    (-1,-1) (N+1) (N+1) σ hleft hright'
  obtain ⟨b,hb,d,hd,q,_,hB,_⟩ := walk_subwalk_between_sets q
    (rectangleDualBottomPorts (-1,-1) (N+1) (N+1) : Set _)
    (rectangleDualTopPorts (-1,-1) (N+1) (N+1) : Set _) hb hd
  let P := q.toPath.val
  have hPath : P.IsPath := q.toPath.property
  have hPsub : ∀ v ∈ P.support, v ∈ q.support := q.support_toPath_subset_support
  have hbottomOnly : ∀ v ∈ P.support,
      v ∈ rectangleDualBottomPorts (-1,-1) (N+1) (N+1) → v = b := by
    intro v hv hport
    exact hB v (hPsub v hv) hport
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
  have hi' : i < N+1 := Finset.mem_range.mp hi
  have hbY := congrArg Prod.snd (rectangleDualBottomPort_val_of_lt (-1,-1) (N+1) (N+1) i hi')
  have hdY : d.val.2 = (N : ℤ) := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    simp only [rectangleDualTopPortVertex,Nat.cast_add,Nat.cast_one]
    omega
  have hnonil : ¬ P.Nil := by
    intro hn
    have he := congrArg (fun v : RectangleDualVertex (-1,-1) (N+1) (N+1) => v.val.2) hn.eq
    omega
  have hX : ∀ v ∈ P.support, -1 ≤ v.val.1 ∧ v.val.1 ≤ (N : ℤ)-1 := by
    intro v hv
    have hx := labelCutDualWalk_support_x_bounds (-1,-1) (N+1) (N+1) σ hleft hright' P hnonil v hv
    constructor <;> omega
  cases hP : P with
  | nil => exact (hnonil (by rw [hP]; exact .nil)).elim
  | @cons b c d hadj tail =>
    have hPath' := hPath
    rw [hP] at hPath'
    have hnoB := ((SimpleGraph.Walk.cons_isPath_iff hadj tail).mp hPath').2
    have htailSub : ∀ v ∈ tail.support, v ∈ P.support := by
      intro v hv
      rw [hP]
      exact List.mem_cons_of_mem _ hv
    have hlow : ∀ v ∈ tail.support, -1 ≤ v.val.2 := by
      intro v hv
      have hbounds := v.property
      change v.val ∈ latticeRectangle (-2,-2) (N+2) (N+2) at hbounds
      rw [mem_latticeRectangle] at hbounds
      have hx := hX v (htailSub v hv)
      by_contra hnot
      have hy : v.val.2 = -2 := by omega
      have hport := rectangleDualBottomPorts_of_coords (-1,-1) (N+1) (N+1) v
        hx.1 (by omega) (by simpa using hy)
      have heq := hbottomOnly v (htailSub v hv) hport
      exact hnoB (heq ▸ hv)
    have hcEq := rectangleDualBottomAdj_implies_up (-1,-1) (N+1) (N+1) σ i hi' c hadj
    subst c
    have hcY := congrArg Prod.snd (rectangleDualBottomUpVertex_val_of_lt (-1,-1) (N+1) (N+1) i hi')
    obtain ⟨z,p,s,hz,hdecomp,hfirst⟩ := walk_first_arrival_down
      (fun v : RectangleDualVertex (-1,-1) (N+1) (N+1) => -v.val.2)
      (fun x y hxy => by
        simpa only [neg_sub_neg,abs_sub_comm] using
          labelCutDual_adj_vertical_step (-1,-1) (N+1) (N+1) σ x y hxy)
      tail (-(N-1 : ℤ)) (by omega) (by omega)
    refine ⟨i,hi',z,p,hadj,by omega,?_⟩
    intro v hv
    have hvtail : v ∈ tail.support := by
      rw [hdecomp,SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl hv
    have hx := hX v (htailSub v hvtail)
    refine ⟨hx.1,hx.2,hlow v hvtail,?_⟩
    by_contra hnot
    have heq := hfirst v hv (by omega)
    subst v
    omega

end
end PottsContinuity.Push
