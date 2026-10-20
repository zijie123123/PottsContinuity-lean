module

public import PottsContinuity.Thm4Side.DeterministicReveals
public import PottsContinuity.FKC.FiniteFK.SlitScreenCrossingEvents
public import PottsContinuity.FKC.FiniteFK.SlitScreenSupportSeparation
public import PottsContinuity.Thm3.RSW.StoppingAverage

@[expose] public section

namespace PottsContinuity.Thm4Side

noncomputable section

open PottsContinuity.Exploration
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.RSW
open PottsContinuity.Thm4Plane

local instance screenSelectionEdgeFintype (m : ℕ) :
    Fintype (slitBoxGraph (16 * m)).edgeSet := Fintype.ofFinite _

local instance screenSelectionEdgeDecidableEq (m : ℕ) :
    DecidableEq (slitBoxGraph (16 * m)).edgeSet := Classical.decEq _

private theorem rightHalf_reveal_adj_of_radius_lt (m : ℕ)
    {u v : SlitBoxVertex (16 * m)}
    (hG : (slitBoxGraph (16 * m)).Adj u v)
    (hu : slitScreenRadius m u < (m : ℤ)) :
    (⟨s(u, v), (slitBoxGraph (16 * m)).mem_edgeSet.mpr hG⟩ :
      (slitBoxGraph (16 * m)).edgeSet) ∈ slitRightHalfRevealEdges m := by
  have habs : |u.val.1| < (m : ℤ) :=
    lt_of_le_of_lt (le_max_left _ _) hu
  have hucoord := (abs_lt.mp habs).2
  have hsq : PottsContinuity.FKC.squareLattice.Adj u.val v.val :=
    ((slitBoxGraph_adj_iff (16 * m) u v).mp hG).1
  have hvcoord : v.val.1 ≤ (m : ℤ) := by
    rcases (PottsContinuity.FKC.squareLattice_adj_iff u.val v.val).mp hsq with
      ⟨horiz | horiz, hy⟩ | ⟨hx, vert | vert⟩ <;> omega
  simp only [slitRightHalfRevealEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases (Sym2.mem_iff').mp hz with hzu | hzv
    · rw [hzu]
      omega
    · rw [hzv]
      exact hvcoord
  · intro hall
    have huMem : u ∈ s(u, v) := (Sym2.mem_iff').mpr (Or.inl rfl)
    have huEq := hall u huMem
    omega

private theorem leftHalf_reveal_adj_of_radius_lt (m : ℕ)
    {u v : SlitBoxVertex (16 * m)}
    (hG : (slitBoxGraph (16 * m)).Adj u v)
    (hu : slitScreenRadius m u < (m : ℤ)) :
    (⟨s(u, v), (slitBoxGraph (16 * m)).mem_edgeSet.mpr hG⟩ :
      (slitBoxGraph (16 * m)).edgeSet) ∈ slitLeftHalfRevealEdges m := by
  have habs : |u.val.1| < (m : ℤ) :=
    lt_of_le_of_lt (le_max_left _ _) hu
  have hucoord := (abs_lt.mp habs).1
  have hsq : PottsContinuity.FKC.squareLattice.Adj u.val v.val :=
    ((slitBoxGraph_adj_iff (16 * m) u v).mp hG).1
  have hvcoord : -(m : ℤ) ≤ v.val.1 := by
    rcases (PottsContinuity.FKC.squareLattice_adj_iff u.val v.val).mp hsq with
      ⟨horiz | horiz, hy⟩ | ⟨hx, vert | vert⟩ <;> omega
  simp only [slitLeftHalfRevealEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases (Sym2.mem_iff').mp hz with hzu | hzv
    · rw [hzu]
      omega
    · rw [hzv]
      exact hvcoord
  · intro hall
    have huMem : u ∈ s(u, v) := (Sym2.mem_iff').mpr (Or.inl rfl)
    have huEq := hall u huMem
    omega

private theorem transfer_walk_of_fixed_reveal
    {m : ℕ} (R : Configuration (slitBoxGraph (16 * m)))
    (radius : SlitBoxVertex (16 * m) → ℤ)
    (hreveal : ∀ {u v} (hG : (slitBoxGraph (16 * m)).Adj u v),
      radius u < (m : ℤ) →
      (⟨s(u, v), (slitBoxGraph (16 * m)).mem_edgeSet.mpr hG⟩ :
        (slitBoxGraph (16 * m)).edgeSet) ∈ R)
    {A B : Configuration (slitBoxGraph (16 * m))}
    {u z : SlitBoxVertex (16 * m)}
    (p : (openGraph (slitBoxGraph (16 * m)) A).Walk u z)
    (hp : p.IsPath)
    (hfirst : ∀ v ∈ p.support, radius v = (m : ℤ) → v = z)
    (hbound : ∀ v ∈ p.support, radius v ≤ (m : ℤ))
    (hagree : B ∩ R = A ∩ R) :
    Nonempty ((openGraph (slitBoxGraph (16 * m)) B).Walk u z) := by
  revert hp hfirst hbound
  induction p with
  | nil =>
      intro _ _ _
      exact ⟨SimpleGraph.Walk.nil⟩
  | @cons x y z hadj tail ih =>
      intro hp hfirst hbound
      have hnodup := hp.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnodup
      have hxNotEnd : x ≠ z := by
        intro hxz
        apply hnodup.1
        rw [hxz]
        exact SimpleGraph.Walk.end_mem_support tail
      have hxEq : radius x ≠ (m : ℤ) := by
        intro hx
        exact hxNotEnd (hfirst x (by simp) hx)
      have hxlt : radius x < (m : ℤ) := by
        have hle := hbound x (by simp)
        omega
      have hG : (slitBoxGraph (16 * m)).Adj x y :=
        (openGraph_le (slitBoxGraph (16 * m)) A) hadj
      let e : (slitBoxGraph (16 * m)).edgeSet :=
        ⟨s(x, y), (slitBoxGraph (16 * m)).mem_edgeSet.mpr hG⟩
      have heA : e ∈ A := by
        have hmem := (openGraph_adj (slitBoxGraph (16 * m)) A x y).mp hadj
        rcases hmem with ⟨f, hf, hval⟩
        have hfe : f = e := Subtype.ext hval
        simpa [e, hfe] using hf
      have heR : e ∈ R := by
        simpa [e] using hreveal hG hxlt
      have heq := Finset.ext_iff.mp hagree e
      simp only [Finset.mem_inter] at heq
      have heB : e ∈ B := (heq.mpr ⟨heA, heR⟩).1
      have hadj' : (openGraph (slitBoxGraph (16 * m)) B).Adj x y := by
        rw [openGraph_adj]
        exact ⟨e, heB, rfl⟩
      have htailPath : tail.IsPath := by simpa using hp.tail
      have htailFirst : ∀ v ∈ tail.support, radius v = (m : ℤ) → v = z := by
        intro v hv hvEq
        exact hfirst v (by simp [hv]) hvEq
      have htailBound : ∀ v ∈ tail.support, radius v ≤ (m : ℤ) := by
        intro v hv
        exact hbound v (by simp [hv])
      have htail := ih htailPath htailFirst htailBound
      exact ⟨SimpleGraph.Walk.cons hadj' htail.some⟩

private theorem slitScreenEvent_iff_of_agree_rightHalfReveal
    (m : ℕ) (A B : Configuration (slitBoxGraph (16 * m)))
    (hagree : B ∩ slitRightHalfRevealEdges m = A ∩ slitRightHalfRevealEdges m) :
    (A ∈ slitScreenEvent m ↔ B ∈ slitScreenEvent m) := by
  constructor
  · intro hA
    obtain ⟨z, hz, p, hp, hfirst, hbound⟩ :=
      slitScreenEvent_firstHit_path_local m A hA
    have hwalk := transfer_walk_of_fixed_reveal (m := m)
      (slitRightHalfRevealEdges m) (slitScreenRadius m)
      (fun hG hu => rightHalf_reveal_adj_of_radius_lt m hG hu)
      p hp hfirst hbound hagree
    refine ⟨z, hz, ?_⟩
    exact (actualConnected_iff_walk (slitBoxGraph (16 * m)) B
      (slitBoxBottomCenterVertex (16 * m)) z).2 hwalk
  · intro hB
    obtain ⟨z, hz, p, hp, hfirst, hbound⟩ :=
      slitScreenEvent_firstHit_path_local m B hB
    have hwalk := transfer_walk_of_fixed_reveal (m := m)
      (slitRightHalfRevealEdges m) (slitScreenRadius m)
      (fun hG hu => rightHalf_reveal_adj_of_radius_lt m hG hu)
      p hp hfirst hbound hagree.symm
    refine ⟨z, hz, ?_⟩
    exact (actualConnected_iff_walk (slitBoxGraph (16 * m)) A
      (slitBoxBottomCenterVertex (16 * m)) z).2 hwalk

private theorem slitScreenEvent_iff_of_agree_leftHalfReveal
    (m : ℕ) (A B : Configuration (slitBoxGraph (16 * m)))
    (hagree : B ∩ slitLeftHalfRevealEdges m = A ∩ slitLeftHalfRevealEdges m) :
    (A ∈ slitScreenEvent m ↔ B ∈ slitScreenEvent m) := by
  constructor
  · intro hA
    obtain ⟨z, hz, p, hp, hfirst, hbound⟩ :=
      slitScreenEvent_firstHit_path_local m A hA
    have hwalk := transfer_walk_of_fixed_reveal (m := m)
      (slitLeftHalfRevealEdges m) (slitScreenRadius m)
      (fun hG hu => leftHalf_reveal_adj_of_radius_lt m hG hu)
      p hp hfirst hbound hagree
    refine ⟨z, hz, ?_⟩
    exact (actualConnected_iff_walk (slitBoxGraph (16 * m)) B
      (slitBoxBottomCenterVertex (16 * m)) z).2 hwalk
  · intro hB
    obtain ⟨z, hz, p, hp, hfirst, hbound⟩ :=
      slitScreenEvent_firstHit_path_local m B hB
    have hwalk := transfer_walk_of_fixed_reveal (m := m)
      (slitLeftHalfRevealEdges m) (slitScreenRadius m)
      (fun hG hu => leftHalf_reveal_adj_of_radius_lt m hG hu)
      p hp hfirst hbound hagree.symm
    refine ⟨z, hz, ?_⟩
    exact (actualConnected_iff_walk (slitBoxGraph (16 * m)) A
      (slitBoxBottomCenterVertex (16 * m)) z).2 hwalk

private theorem slitScreenRightCrossingEvent_iff_of_agree_leftHalfReveal
    (m : ℕ) (hm : 1 ≤ m) (A B : Configuration (slitBoxGraph (16 * m)))
    (hagree : B ∩ slitLeftHalfRevealEdges m = A ∩ slitLeftHalfRevealEdges m) :
    (A ∈ slitScreenRightCrossingEvent m ↔ B ∈ slitScreenRightCrossingEvent m) := by
  apply slitScreenRightCrossingEvent_iff_of_agree_on_support m hm A B
  intro e he
  have heR : e ∈ slitLeftHalfRevealEdges m := by
    simp only [slitLeftHalfRevealEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    let u : SlitBoxVertex (16 * m) := (Quot.out e.val).1
    let v : SlitBoxVertex (16 * m) := (Quot.out e.val).2
    have hrepr : s(u, v) = e.val := by
      change Quot.mk _ (u, v) = e.val
      exact Quot.out_eq e.val
    have hcoords := slitScreenRight_support_edge_coordinates m e he u v hrepr
    refine ⟨?_, ?_⟩
    · intro z hz
      have hz' : z = u ∨ z = v := by
        have hz'' : z ∈ s(u, v) := by
          have hzval : z ∈ e.val := hz
          rw [← hrepr] at hzval
          exact hzval
        exact (Sym2.mem_iff').mp hz''
      rcases hz' with hzu | hzv
      · rw [hzu]
        rcases hcoords with ⟨hu, _, _⟩
        omega
      · rw [hzv]
        rcases hcoords with ⟨_, hv, _⟩
        omega
    · intro hall
      have huMem : u ∈ e.val := by
        rw [← hrepr]
        exact (Sym2.mem_iff').mpr (Or.inl rfl)
      have huEq := hall u huMem
      rcases hcoords with ⟨hu, _, _⟩
      omega
  have heq := Finset.ext_iff.mp hagree e
  simp only [Finset.mem_inter] at heq
  constructor
  · intro hA
    exact (heq.mpr ⟨hA, heR⟩).1
  · intro hB
    exact (heq.mp ⟨hB, heR⟩).1

/-- The screen event is determined by the fixed reveal on the left of `x=m`.
The first-hit path stops at radius `m`, so every edge on it has a revealed
endpoint strictly to the left of the cut. -/
theorem slitScreenEvent_rightReveal_invariant (m : ℕ)
    (A B : Configuration (slitBoxGraph (16 * m)))
    (hagree : B ∩ slitRightHalfRevealEdges m = A ∩ slitRightHalfRevealEdges m) :
    (A ∈ slitScreenEvent m ↔ B ∈ slitScreenEvent m) :=
  slitScreenEvent_iff_of_agree_rightHalfReveal m A B hagree

/-- The reflected fixed reveal determines the screen event and, for positive
`m`, the entire right closed-dual crossing event. -/
theorem slitScreenEvent_leftReveal_invariant (m : ℕ)
    (A B : Configuration (slitBoxGraph (16 * m)))
    (hagree : B ∩ slitLeftHalfRevealEdges m = A ∩ slitLeftHalfRevealEdges m) :
    (A ∈ slitScreenEvent m ↔ B ∈ slitScreenEvent m) :=
  slitScreenEvent_iff_of_agree_leftHalfReveal m A B hagree

theorem slitScreenRightCrossingEvent_leftReveal_invariant
    (m : ℕ) (hm : 1 ≤ m) (A B : Configuration (slitBoxGraph (16 * m)))
    (hagree : B ∩ slitLeftHalfRevealEdges m = A ∩ slitLeftHalfRevealEdges m) :
    (A ∈ slitScreenRightCrossingEvent m ↔ B ∈ slitScreenRightCrossingEvent m) :=
  slitScreenRightCrossingEvent_iff_of_agree_leftHalfReveal m hm A B hagree

end

end PottsContinuity.Thm4Side
