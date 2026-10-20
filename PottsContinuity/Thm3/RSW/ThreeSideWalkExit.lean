module

public import PottsContinuity.Thm3.RSW.WalkClipping

@[expose] public section

namespace PottsContinuity.RSW

/-- A walk starting inside a rectangle and staying above its bottom reaches
its left, right or top side before reaching the top height outside it. -/
theorem walk_reach_three_sides {V : Type*} (G : SimpleGraph V) (f g : V → ℤ)
    (hx : ∀ {u v}, G.Adj u v → |f v-f u| ≤ 1)
    (hy : ∀ {u v}, G.Adj u v → |g v-g u| ≤ 1)
    (a b H : ℤ) {u v : V} (p : G.Walk u v)
    (hu : a ≤ f u ∧ f u ≤ b ∧ 0 ≤ g u ∧ g u ≤ H)
    (hv : H ≤ g v) (hp : ∀ z ∈ p.support, 0 ≤ g z) :
    ∃ t : V, ∃ q : G.Walk u t,
      (f t = a ∨ f t = b ∨ g t = H) ∧
      (∀ z ∈ q.support, a ≤ f z ∧ f z ≤ b ∧ 0 ≤ g z ∧ g z ≤ H) ∧
      (∀ z ∈ q.support, z ∈ p.support) := by
  classical
  revert hu hv hp
  induction p with
  | nil =>
    intro hu hv hp
    refine ⟨_,.nil,Or.inr (Or.inr (by omega)),?_,?_⟩
    · intro z hz
      have hz' : z = _ := List.mem_singleton.mp hz
      exact hz' ▸ hu
    · intro z hz
      exact hz
  | @cons u v w huv p ih =>
    intro hu hw hp
    by_cases hb : f u = a ∨ f u = b ∨ g u = H
    · refine ⟨u,.nil,hb,?_,?_⟩
      · intro z hz
        have hz' : z = u := List.mem_singleton.mp hz
        exact hz' ▸ hu
      · intro z hz
        have hz' : z = u := List.mem_singleton.mp hz
        subst z
        exact List.mem_cons_self
    · have hxu : a < f u ∧ f u < b := by omega
      have hyu : g u < H := by omega
      have hstepx := abs_le.mp (hx huv)
      have hstepy := abs_le.mp (hy huv)
      have hv0 : 0 ≤ g v := hp v (List.mem_cons.mpr (Or.inr p.start_mem_support))
      have hvbox : a ≤ f v ∧ f v ≤ b ∧ 0 ≤ g v ∧ g v ≤ H := by omega
      obtain ⟨t,q,ht,hq,hsub⟩ := ih hvbox hw (fun z hz => hp z (List.mem_cons.mpr (Or.inr hz)))
      refine ⟨t,q.cons huv,ht,?_,?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hu
        · exact hq z hz
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact List.mem_cons_self
        · exact List.mem_cons.mpr (Or.inr (hsub z hz))

end PottsContinuity.RSW
