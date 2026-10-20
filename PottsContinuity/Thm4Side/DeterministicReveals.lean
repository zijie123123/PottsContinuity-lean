module

public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import PottsContinuity.FKC.FiniteFK.ActualConnectionFirstHitPath
public import PottsContinuity.FKC.FiniteFK.SlitBoxDomain
public import PottsContinuity.Thm4Plane.SlitScreenEvent

@[expose] public section

namespace PottsContinuity.Thm4Side

noncomputable section

open PottsContinuity.Exploration
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.Thm4Plane

local instance slitRightHalfRevealEdgeFintype (m : ℕ) :
    Fintype (slitBoxGraph (16 * m)).edgeSet := Fintype.ofFinite _

local instance slitRightHalfRevealEdgeDecidableEq (m : ℕ) :
    DecidableEq (slitBoxGraph (16 * m)).edgeSet := Classical.decEq _

/-- The source's max-norm radius around the screen root. -/
def slitScreenRadius (m : ℕ) (v : SlitBoxVertex (16 * m)) : ℤ :=
  max |v.val.1| |v.val.2 + (16 * m : ℤ)|

private theorem int_abs_succ_bounds (z : ℤ) :
    |z| ≤ |z + 1| + 1 ∧ |z + 1| ≤ |z| + 1 := by
  by_cases hz : 0 ≤ z
  · have hz' : 0 ≤ z + 1 := by omega
    rw [abs_of_nonneg hz, abs_of_nonneg hz']
    omega
  · have hz0 : z ≤ 0 := le_of_not_ge hz
    have hz' : z + 1 ≤ 0 := by omega
    rw [abs_of_nonpos hz0, abs_of_nonpos hz']
    omega

private theorem int_abs_adj_bounds {a b : ℤ}
    (h : a + 1 = b ∨ b + 1 = a) :
    |a| ≤ |b| + 1 ∧ |b| ≤ |a| + 1 := by
  rcases h with h | h
  · rw [← h]
    exact int_abs_succ_bounds a
  · rw [← h]
    exact ⟨(int_abs_succ_bounds b).2, (int_abs_succ_bounds b).1⟩

private theorem slitScreenRadius_adj_step (m : ℕ)
    {u v : SlitBoxVertex (16 * m)}
    (h : (slitBoxGraph (16 * m)).Adj u v) :
    slitScreenRadius m u ≤ slitScreenRadius m v + 1 ∧
      slitScreenRadius m v ≤ slitScreenRadius m u + 1 := by
  have hsq : PottsContinuity.FKC.squareLattice.Adj u.val v.val :=
    ((slitBoxGraph_adj_iff (16 * m) u v).mp h).1
  rcases (PottsContinuity.FKC.squareLattice_adj_iff u.val v.val).mp hsq with
    ⟨horiz | horiz, hy⟩ | ⟨hx, vert | vert⟩
  · have hx' := int_abs_adj_bounds (Or.inl horiz)
    have hy' : |u.val.2 + (16 * m : ℤ)| = |v.val.2 + (16 * m : ℤ)| := by rw [hy]
    simp only [slitScreenRadius]
    constructor <;> apply max_le
    · calc
        |u.val.1| ≤ |v.val.1| + 1 := hx'.1
        _ ≤ max |v.val.1| |v.val.2 + (16 * m : ℤ)| + 1 := by
          have hle : |v.val.1| ≤ max |v.val.1| |v.val.2 + (16 * m : ℤ)| :=
            le_max_left _ _
          simpa [add_comm] using add_le_add_right hle (1 : ℤ)
    · calc
        |u.val.2 + (16 * m : ℤ)| = |v.val.2 + (16 * m : ℤ)| := hy'
        _ ≤ max |v.val.1| |v.val.2 + (16 * m : ℤ)| := le_max_right _ _
        _ ≤ max |v.val.1| |v.val.2 + (16 * m : ℤ)| + 1 :=
          le_add_of_nonneg_right (by norm_num : 0 ≤ (1 : ℤ))
    · calc
        |v.val.1| ≤ |u.val.1| + 1 := hx'.2
        _ ≤ max |u.val.1| |u.val.2 + (16 * m : ℤ)| + 1 := by
          have hle : |u.val.1| ≤ max |u.val.1| |u.val.2 + (16 * m : ℤ)| :=
            le_max_left _ _
          simpa [add_comm] using add_le_add_right hle (1 : ℤ)
    · calc
        |v.val.2 + (16 * m : ℤ)| = |u.val.2 + (16 * m : ℤ)| := hy'.symm
        _ ≤ max |u.val.1| |u.val.2 + (16 * m : ℤ)| := le_max_right _ _
        _ ≤ max |u.val.1| |u.val.2 + (16 * m : ℤ)| + 1 :=
          le_add_of_nonneg_right (by norm_num : 0 ≤ (1 : ℤ))
  · have hx' := int_abs_adj_bounds (Or.inr horiz)
    have hy' : |u.val.2 + (16 * m : ℤ)| = |v.val.2 + (16 * m : ℤ)| := by rw [hy]
    simp only [slitScreenRadius]
    constructor <;> apply max_le
    · calc
        |u.val.1| ≤ |v.val.1| + 1 := hx'.1
        _ ≤ max |v.val.1| |v.val.2 + (16 * m : ℤ)| + 1 := by
          have hle : |v.val.1| ≤ max |v.val.1| |v.val.2 + (16 * m : ℤ)| :=
            le_max_left _ _
          simpa [add_comm] using add_le_add_right hle (1 : ℤ)
    · calc
        |u.val.2 + (16 * m : ℤ)| = |v.val.2 + (16 * m : ℤ)| := hy'
        _ ≤ max |v.val.1| |v.val.2 + (16 * m : ℤ)| := le_max_right _ _
        _ ≤ max |v.val.1| |v.val.2 + (16 * m : ℤ)| + 1 :=
          le_add_of_nonneg_right (by norm_num : 0 ≤ (1 : ℤ))
    · calc
        |v.val.1| ≤ |u.val.1| + 1 := hx'.2
        _ ≤ max |u.val.1| |u.val.2 + (16 * m : ℤ)| + 1 := by
          have hle : |u.val.1| ≤ max |u.val.1| |u.val.2 + (16 * m : ℤ)| :=
            le_max_left _ _
          simpa [add_comm] using add_le_add_right hle (1 : ℤ)
    · calc
        |v.val.2 + (16 * m : ℤ)| = |u.val.2 + (16 * m : ℤ)| := hy'.symm
        _ ≤ max |u.val.1| |u.val.2 + (16 * m : ℤ)| := le_max_right _ _
        _ ≤ max |u.val.1| |u.val.2 + (16 * m : ℤ)| + 1 :=
          le_add_of_nonneg_right (by norm_num : 0 ≤ (1 : ℤ))
  · have hx' : |u.val.1| = |v.val.1| := by rw [hx]
    have hshift : u.val.2 + (16 * m : ℤ) + 1 = v.val.2 + (16 * m : ℤ) := by
      calc
        u.val.2 + (16 * m : ℤ) + 1 = (u.val.2 + 1) + (16 * m : ℤ) := by ring
        _ = v.val.2 + (16 * m : ℤ) := by rw [vert]
    have hy' := int_abs_adj_bounds (Or.inl hshift)
    simp only [slitScreenRadius]
    constructor <;> apply max_le
    · calc
        |u.val.1| = |v.val.1| := hx'
        _ ≤ max |v.val.1| |v.val.2 + (16 * m : ℤ)| := le_max_left _ _
        _ ≤ max |v.val.1| |v.val.2 + (16 * m : ℤ)| + 1 :=
          le_add_of_nonneg_right (by norm_num : 0 ≤ (1 : ℤ))
    · calc
        |u.val.2 + (16 * m : ℤ)| ≤ |v.val.2 + (16 * m : ℤ)| + 1 := hy'.1
        _ ≤ max |v.val.1| |v.val.2 + (16 * m : ℤ)| + 1 := by
          have hle : |v.val.2 + (16 * m : ℤ)| ≤
              max |v.val.1| |v.val.2 + (16 * m : ℤ)| := le_max_right _ _
          simp [add_comm]
    · calc
        |v.val.1| = |u.val.1| := hx'.symm
        _ ≤ max |u.val.1| |u.val.2 + (16 * m : ℤ)| := le_max_left _ _
        _ ≤ max |u.val.1| |u.val.2 + (16 * m : ℤ)| + 1 :=
          le_add_of_nonneg_right (by norm_num : 0 ≤ (1 : ℤ))
    · calc
        |v.val.2 + (16 * m : ℤ)| ≤ |u.val.2 + (16 * m : ℤ)| + 1 := hy'.2
        _ ≤ max |u.val.1| |u.val.2 + (16 * m : ℤ)| + 1 := by
          have hle : |u.val.2 + (16 * m : ℤ)| ≤
              max |u.val.1| |u.val.2 + (16 * m : ℤ)| := le_max_right _ _
          simp [add_comm]
  · have hx' : |u.val.1| = |v.val.1| := by rw [hx]
    have hshift : v.val.2 + (16 * m : ℤ) + 1 = u.val.2 + (16 * m : ℤ) := by
      calc
        v.val.2 + (16 * m : ℤ) + 1 = (v.val.2 + 1) + (16 * m : ℤ) := by ring
        _ = u.val.2 + (16 * m : ℤ) := by rw [vert]
    have hy' := int_abs_adj_bounds (Or.inr hshift)
    simp only [slitScreenRadius]
    constructor <;> apply max_le
    · calc
        |u.val.1| = |v.val.1| := hx'
        _ ≤ max |v.val.1| |v.val.2 + (16 * m : ℤ)| := le_max_left _ _
        _ ≤ max |v.val.1| |v.val.2 + (16 * m : ℤ)| + 1 :=
          le_add_of_nonneg_right (by norm_num : 0 ≤ (1 : ℤ))
    · calc
        |u.val.2 + (16 * m : ℤ)| ≤ |v.val.2 + (16 * m : ℤ)| + 1 := hy'.1
        _ ≤ max |v.val.1| |v.val.2 + (16 * m : ℤ)| + 1 := by
          have hle : |v.val.2 + (16 * m : ℤ)| ≤
              max |v.val.1| |v.val.2 + (16 * m : ℤ)| := le_max_right _ _
          simp [add_comm]
    · calc
        |v.val.1| = |u.val.1| := hx'.symm
        _ ≤ max |u.val.1| |u.val.2 + (16 * m : ℤ)| := le_max_left _ _
        _ ≤ max |u.val.1| |u.val.2 + (16 * m : ℤ)| + 1 :=
          le_add_of_nonneg_right (by norm_num : 0 ≤ (1 : ℤ))
    · calc
        |v.val.2 + (16 * m : ℤ)| ≤ |u.val.2 + (16 * m : ℤ)| + 1 := hy'.2
        _ ≤ max |u.val.1| |u.val.2 + (16 * m : ℤ)| + 1 := by
          have hle : |u.val.2 + (16 * m : ℤ)| ≤
              max |u.val.1| |u.val.2 + (16 * m : ℤ)| := le_max_right _ _
          simp [add_comm]

private theorem walk_support_radius_le
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x z : V}
    (m : ℤ) (radius : V → ℤ) (p : G.Walk x z)
    (hpath : p.IsPath) (hstart : radius x ≤ m) (hend : radius z = m)
    (hfirst : ∀ v ∈ p.support, radius v = m → v = z)
    (hstep : ∀ {u v}, G.Adj u v →
      radius u ≤ radius v + 1 ∧ radius v ≤ radius u + 1) :
    ∀ v ∈ p.support, radius v ≤ m := by
  revert m radius hpath hstart hend hfirst hstep
  induction p with
  | nil =>
      intro m radius hpath hstart hend hfirst hstep v hv
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      subst v
      exact hstart
  | @cons x y z hadj tail ih =>
      intro m radius hpath hstart hend hfirst hstep
      have hnodup := hpath.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnodup
      have hxNotEnd : x ≠ z := by
        intro hxz
        apply hnodup.1
        rw [hxz]
        exact SimpleGraph.Walk.end_mem_support tail
      have hxm : radius x < m := by
        have hxEq : radius x ≠ m := by
          intro hxEq
          exact hxNotEnd (hfirst x (by simp) hxEq)
        omega
      have hym : radius y ≤ m := by
        have := (hstep hadj).2
        omega
      have htailFirst : ∀ v ∈ tail.support, radius v = m → v = z := by
        intro v hv hvEq
        exact hfirst v (by simp [hv]) hvEq
      have htailPath : tail.IsPath := by simpa using hpath.tail
      have htail := ih m radius htailPath hym hend htailFirst hstep
      intro v hv
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact le_of_lt hxm
      · exact htail v hv

/-- The source screen event has a first-hit path contained in the centered
max-norm box of radius `m`. -/
theorem slitScreenEvent_firstHit_path_local
    (m : ℕ) (A : Configuration (slitBoxGraph (16 * m)))
    (hA : A ∈ slitScreenEvent m) :
    ∃ z : SlitBoxVertex (16 * m),
      slitScreenRadius m z = (m : ℤ) ∧
      ∃ p : (openGraph (slitBoxGraph (16 * m)) A).Walk
        (slitBoxBottomCenterVertex (16 * m)) z,
        p.IsPath ∧
        (∀ v ∈ p.support, slitScreenRadius m v = (m : ℤ) → v = z) ∧
        ∀ v ∈ p.support, slitScreenRadius m v ≤ (m : ℤ) := by
  classical
  rcases hA with ⟨z, hz, hconn⟩
  have hzRadius : slitScreenRadius m z = (m : ℤ) := by
    simpa [slitScreenRadius] using hz
  let B : Set (SlitBoxVertex (16 * m)) := {v | slitScreenRadius m v = (m : ℤ)}
  obtain ⟨z', hz', p, hp, hfirst⟩ :=
    actualConnected_exists_first_hit_path (B := B) A
      ⟨z, by simpa [B] using hzRadius, hconn⟩
  have hstart : slitScreenRadius m (slitBoxBottomCenterVertex (16 * m)) ≤ (m : ℤ) := by
    simp [slitScreenRadius, slitBoxBottomCenterVertex_val]
  have hfirst' : ∀ v ∈ p.support, slitScreenRadius m v = (m : ℤ) → v = z' := by
    intro v hv hvm
    exact hfirst v hv (by simpa [B] using hvm)
  have hstep' : ∀ {u v}, (openGraph (slitBoxGraph (16 * m)) A).Adj u v →
      slitScreenRadius m u ≤ slitScreenRadius m v + 1 ∧
        slitScreenRadius m v ≤ slitScreenRadius m u + 1 := by
    intro u v huv
    exact slitScreenRadius_adj_step m
      (openGraph_le (slitBoxGraph (16 * m)) A huv)
  have hbound := walk_support_radius_le (m : ℤ) (slitScreenRadius m) p hp
    hstart hz' hfirst' hstep'
  exact ⟨z', by simpa [B] using hz', p, hp, hfirst', hbound⟩

/-- The deterministic reveal of the slit-box edges on or to the left of the
screen line `x = m`, with bonds lying along the cut retained in the residual
domain. Horizontal bonds crossing from `m` to `m+1` also remain residual. -/
noncomputable def slitRightHalfRevealEdges (m : ℕ) :
    Configuration (slitBoxGraph (16 * m)) :=
  Finset.univ.filter fun e =>
    (∀ v ∈ e.1, v.val.1 ≤ (m : ℤ)) ∧
      ¬ (∀ v ∈ e.1, v.val.1 = (m : ℤ))

/-- The reflected reveal of slit-box edges on or to the right of `x = -m`,
with bonds lying along the cut retained in the residual domain. Horizontal
bonds crossing from `-m-1` to `-m` also remain residual. -/
noncomputable def slitLeftHalfRevealEdges (m : ℕ) :
    Configuration (slitBoxGraph (16 * m)) :=
  Finset.univ.filter fun e =>
    (∀ v ∈ e.1, -(m : ℤ) ≤ v.val.1) ∧
      ¬ (∀ v ∈ e.1, v.val.1 = -(m : ℤ))

end

end PottsContinuity.Thm4Side
