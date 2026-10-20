module

public import PottsContinuity.Thm3.RSW.TiltedStripWindowReads

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial Thm3.Prop4
noncomputable section

/-- All original bonds except those joining two intrinsically wired top vertices. -/
def tiltedStripReducedCarrier (N : ℕ) (t : ℝ) :=
  {b : TiltedBond N t // ¬ (tiltedTop N t b.val.source ∧ tiltedTop N t b.val.target)}

/-- Crossed half-turn with the digital staircase phase retained. -/
def tiltedStripReducedCrossedBond (N : ℕ) (t : ℝ) (b : LatticeBond) : LatticeBond :=
  ⟨(-b.base.1-(if 0 < t then 1 else 0),(N : ℤ)-1-b.base.2),
    match b.axis with | .horizontal => .vertical | .vertical => .horizontal⟩

theorem tiltedStripReducedCrossedBond_involutive (N : ℕ) (t : ℝ) :
    Function.Involutive (tiltedStripReducedCrossedBond N t) := by
  rintro ⟨⟨x,y⟩,ax⟩
  cases ax <;> simp [tiltedStripReducedCrossedBond]

/-- Exact reduced-carrier inequalities, including the staircase boundary. -/
theorem tiltedStripReducedCarrier_iff (N : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (b : LatticeBond) :
    (b.source ∈ tiltedStripVertices N t ∧ b.target ∈ tiltedStripVertices N t ∧
      ¬ (tiltedTop N t b.source ∧ tiltedTop N t b.target)) ↔
    match b.axis with
    | .horizontal =>
        if 0 < t then t ≤ tiltedHeight t b.source ∧ tiltedHeight t b.source ≤ (N : ℝ)-1+t
        else 0 ≤ tiltedHeight t b.source ∧ tiltedHeight t b.source ≤ (N : ℝ)-1
    | .vertical => 0 ≤ tiltedHeight t b.source ∧ tiltedHeight t b.source ≤ (N : ℝ)-1 := by
  rw [tiltedTop_iff_height N ht,tiltedTop_iff_height N ht]
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;>
    simp only [tiltedStripVertices,Set.mem_ofPred_eq,LatticeBond.source,LatticeBond.target,tiltedHeight]
  all_goals
    push_cast
    by_cases hp : 0 < t
    all_goals try simp only [hp,ite_true,ite_false]
    all_goals constructor
    all_goals
      first
      | (rintro ⟨⟨ha,hb⟩,⟨hc,hd⟩,he⟩
         constructor
         · linarith
         · by_contra hf
           apply he
           constructor <;> linarith)
      | (rintro ⟨ha,hb⟩
         refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,?_⟩
         · linarith [ht.1,ht.2]
         · linarith [ht.1,ht.2]
         · linarith [ht.1,ht.2]
         · linarith [ht.1,ht.2]
         · rintro ⟨hc,hd⟩; linarith)

/-- The crossed image is again exactly a reduced original strip bond. -/
theorem tiltedStripReducedCrossedBond_mem (N : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (b : tiltedStripReducedCarrier N t) :
    (tiltedStripReducedCrossedBond N t b.val.val).source ∈ tiltedStripVertices N t ∧
    (tiltedStripReducedCrossedBond N t b.val.val).target ∈ tiltedStripVertices N t ∧
    ¬ (tiltedTop N t (tiltedStripReducedCrossedBond N t b.val.val).source ∧
       tiltedTop N t (tiltedStripReducedCrossedBond N t b.val.val).target) := by
  have hb := (tiltedStripReducedCarrier_iff N t ht b.val.val).mp
    ⟨b.val.property.1,b.val.property.2,b.property⟩
  rw [tiltedStripReducedCarrier_iff N t ht]
  rcases b with ⟨⟨⟨⟨x,y⟩,ax⟩,hstrip⟩,htop⟩
  cases ax <;> by_cases hp : 0 < t
  all_goals
    simp only [tiltedStripReducedCrossedBond,hp,ite_true,ite_false,
      LatticeBond.source,tiltedHeight] at hb ⊢
    push_cast
    constructor <;> linarith

/-- Genuine crossed involution on precisely the reduced carrier. -/
def tiltedStripReducedBondEquiv (N : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    tiltedStripReducedCarrier N t ≃ tiltedStripReducedCarrier N t where
  toFun b := ⟨⟨tiltedStripReducedCrossedBond N t b.val.val,
    (tiltedStripReducedCrossedBond_mem N t ht b).1,
    (tiltedStripReducedCrossedBond_mem N t ht b).2.1⟩,
    (tiltedStripReducedCrossedBond_mem N t ht b).2.2⟩
  invFun b := ⟨⟨tiltedStripReducedCrossedBond N t b.val.val,
    (tiltedStripReducedCrossedBond_mem N t ht b).1,
    (tiltedStripReducedCrossedBond_mem N t ht b).2.1⟩,
    (tiltedStripReducedCrossedBond_mem N t ht b).2.2⟩
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    exact tiltedStripReducedCrossedBond_involutive N t b.val.val
  right_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    exact tiltedStripReducedCrossedBond_involutive N t b.val.val

end
end PottsContinuity.RSW
