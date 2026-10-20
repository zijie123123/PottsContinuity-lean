-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripBlockerLocality.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.OutsidePathLocalization
public import PottsContinuity.FKC.FiniteFK.HorizontalStripGoodEvent
public import PottsContinuity.FKC.FiniteFK.HorizontalStripCutRectangle
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

noncomputable section

/-- The public literal counterpart of the private blocker-failure set used by
`HorizontalStripGoodEventMeasurable`. -/
def horizontalStripBlockerFailureEvent
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) : Set LatticeConfiguration :=
  {ω | ∃ u : horizontalStripVertex n,
    ¬ horizontalStripClosedWindow n m k h u ∧
      ∃ p : (horizontalStripOpenGraph n ω).Walk u
        (horizontalStripVertexOfNat n k h (by omega)),
        ∀ z ∈ p.support, ¬ horizontalStripWiredSide n m k h z}

def horizontalStripBlockerCollarRadius (m : ℕ) (k : ℤ) : ℕ :=
  k.natAbs + m + 1

abbrev horizontalStripBlockerCollarGraph (M n : ℕ) (ω : LatticeConfiguration) :=
  horizontalStripRectangleOpenGraph M n ω

def horizontalStripBlockerRectangleToStrip (M n : ℕ)
    (v : RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)) : horizontalStripVertex n :=
  ⟨v.val, by
    have hv := (mem_latticeRectangle (-(M : ℤ), 0) v.1 (2 * M) (2 * n)).mp v.2
    constructor
    · exact_mod_cast hv.2.1
    · simpa using hv.2.2⟩

@[simp] theorem horizontalStripBlockerRectangleToStrip_val (M n : ℕ)
    (v : RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)) :
    (horizontalStripBlockerRectangleToStrip M n v).val = v.val := by
  change v.val = v.val
  rfl

def horizontalStripBlockerRectangleToStripHom (M n : ℕ) (ω : LatticeConfiguration) :
    horizontalStripBlockerCollarGraph M n ω →g horizontalStripOpenGraph n ω where
  toFun := horizontalStripBlockerRectangleToStrip M n
  map_rel' := by
    intro u v h
    change (wholePlaneOpenPrimalGraph ω).Adj u.1 v.1 at h
    change (wholePlaneOpenPrimalGraph ω).Adj u.val v.val at h
    change (wholePlaneOpenPrimalGraph ω).Adj
      (horizontalStripBlockerRectangleToStrip M n u).val
      (horizontalStripBlockerRectangleToStrip M n v).val
    rw [horizontalStripBlockerRectangleToStrip_val, horizontalStripBlockerRectangleToStrip_val]
    exact h

def horizontalStripBlockerCollarBound (n M : ℕ) (v : horizontalStripVertex n) : Prop :=
  -(M : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ M

abbrev horizontalStripBlockerCollarSet (M n : ℕ) :=
  {v : horizontalStripVertex n // horizontalStripBlockerCollarBound n M v}

def horizontalStripBlockerRectangleToCollar (M n : ℕ) :
    RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n) → horizontalStripBlockerCollarSet M n :=
  fun v => ⟨horizontalStripBlockerRectangleToStrip M n v, by
    have hv := (mem_latticeRectangle (-(M : ℤ), 0) v.val (2 * M) (2 * n)).mp v.property
    constructor
    · simpa only [horizontalStripBlockerRectangleToStrip_val] using hv.1.1
    · have hcast : ((2 * M : ℕ) : ℤ) = 2 * (M : ℤ) := by norm_cast
      rw [hcast] at hv
      have hupper : v.val.1 ≤ (M : ℤ) := by
        have := hv.1.2
        omega
      simpa only [horizontalStripBlockerRectangleToStrip_val] using hupper⟩

def horizontalStripBlockerCollarEquiv (M n : ℕ) :
    RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n) ≃ horizontalStripBlockerCollarSet M n where
  toFun := horizontalStripBlockerRectangleToCollar M n
  invFun v := ⟨v.val.val, by
    rw [mem_latticeRectangle]
    constructor
    · constructor
      · exact v.property.1
      · have hwidth : -(M : ℤ) + ((2 * M : ℕ) : ℤ) = (M : ℤ) := by
          push_cast
          ring
        rw [hwidth]
        exact v.property.2
    · constructor
      · exact_mod_cast v.val.property.1
      · simpa using (show (v.val.val).2 ≤ (2 * (n : ℤ)) by exact_mod_cast v.val.property.2)⟩
  left_inv := by intro v; apply Subtype.ext; rfl
  right_inv := by intro v; apply Subtype.ext; apply Subtype.ext; rfl

def horizontalStripBlockerCollarGraphOnStrip (M n : ℕ) (ω : LatticeConfiguration) :=
  (horizontalStripOpenGraph n ω).induce
    {v : horizontalStripVertex n | horizontalStripBlockerCollarBound n M v}

def horizontalStripBlockerCollarGraphIso (M n : ℕ) (ω : LatticeConfiguration) :
    horizontalStripBlockerCollarGraph M n ω ≃g horizontalStripBlockerCollarGraphOnStrip M n ω := by
  refine ⟨horizontalStripBlockerCollarEquiv M n, ?_⟩
  intro u v
  change (wholePlaneOpenPrimalGraph ω).Adj u.val v.val ↔
    (wholePlaneOpenPrimalGraph ω).Adj
      ((horizontalStripBlockerRectangleToCollar M n u).val).val
      ((horizontalStripBlockerRectangleToCollar M n v).val).val
  simp [horizontalStripBlockerRectangleToCollar, horizontalStripBlockerRectangleToStrip_val]

def horizontalStripBlockerCollarRoot (n m : ℕ) (k : ℤ) (h : ℕ)
    (hh : h ≤ n) : RectangleVertex
      (-(horizontalStripBlockerCollarRadius m k : ℤ), 0)
      (2 * horizontalStripBlockerCollarRadius m k) (2 * n) := by
  let M := horizontalStripBlockerCollarRadius m k
  refine ⟨(k, h), ?_⟩
  rw [mem_latticeRectangle]
  have hklo : -((k.natAbs : ℕ) : ℤ) ≤ k := by
    rw [Int.natCast_natAbs]
    exact neg_abs_le k
  have hkhi : k ≤ ((k.natAbs : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    exact le_abs_self k
  constructor
  · constructor
    · change -(M : ℤ) ≤ k
      dsimp [M, horizontalStripBlockerCollarRadius]
      omega
    · change k ≤ -(M : ℤ) + (2 * M : ℕ)
      dsimp [M, horizontalStripBlockerCollarRadius]
      omega
  · constructor
    · change 0 ≤ (h : ℤ)
      exact_mod_cast Nat.zero_le h
    · have hh' : (h : ℤ) ≤ (2 * (n : ℕ) : ℤ) := by exact_mod_cast (show h ≤ 2 * n by omega)
      simpa using hh'

private theorem horizontalStripBlockerWindow_abs_bound
    (n m : ℕ) (k : ℤ) (h : ℕ) (v : horizontalStripVertex n)
    (hv : horizontalStripClosedWindow n m k h v) :
    |v.val.1| ≤ (k.natAbs : ℤ) + m := by
  have hdist : |v.val.1 - k| ≤ (m : ℤ) := by
    have hc : ((v.val.1 - k).natAbs : ℤ) ≤ (m : ℤ) := by exact_mod_cast hv.1
    rw [Int.natCast_natAbs] at hc
    exact hc
  calc
    |v.val.1| = |(v.val.1 - k) + k| := by congr 1; ring
    _ ≤ |v.val.1 - k| + |k| := abs_add_le _ _
    _ ≤ (m : ℤ) + (k.natAbs : ℤ) := add_le_add hdist (by rw [Int.natCast_natAbs])
    _ = (k.natAbs : ℤ) + m := by ring

 theorem horizontalStripBlockerWindow_x_bound
    (n m : ℕ) (k : ℤ) (h : ℕ) (v : horizontalStripVertex n)
    (hv : horizontalStripClosedWindow n m k h v) :
    -(horizontalStripBlockerCollarRadius m k : ℤ) ≤ v.val.1 ∧
      v.val.1 ≤ horizontalStripBlockerCollarRadius m k := by
  have hxabs := horizontalStripBlockerWindow_abs_bound n m k h v hv
  have hxlo := (abs_le.mp hxabs).1
  have hxhi := (abs_le.mp hxabs).2
  constructor
  · dsimp [horizontalStripBlockerCollarRadius]
    omega
  · dsimp [horizontalStripBlockerCollarRadius]
    omega

private theorem horizontalStripBlockerNeighbor_x_bound
    (n m : ℕ) (k : ℤ) (h : ℕ) (ω : LatticeConfiguration)
    {z w : horizontalStripVertex n}
    (hw : horizontalStripClosedWindow n m k h w)
    (hzw : (horizontalStripOpenGraph n ω).Adj z w) :
    -(horizontalStripBlockerCollarRadius m k : ℤ) ≤ z.val.1 ∧
      z.val.1 ≤ horizontalStripBlockerCollarRadius m k := by
  have hwin := horizontalStripBlockerWindow_abs_bound n m k h w hw
  rcases hzw with ⟨hsq, _⟩
  have hadj := (squareLattice_adj_iff z.val w.val).mp hsq
  have hstep : |z.val.1 - w.val.1| ≤ 1 := by
    rcases hadj with ⟨horiz, hy⟩ | ⟨hx, vert⟩
    · rcases horiz with hh | hh
      · have hdiff : z.val.1 - w.val.1 = -1 := by omega
        rw [hdiff]
        norm_num
      · have hdiff : z.val.1 - w.val.1 = 1 := by omega
        rw [hdiff]
        norm_num
    · have hdiff : z.val.1 - w.val.1 = 0 := by omega
      rw [hdiff]
      norm_num
  have hzabs : |z.val.1| ≤ (horizontalStripBlockerCollarRadius m k : ℤ) := by
    calc
      |z.val.1| = |(z.val.1 - w.val.1) + w.val.1| := by congr 1; ring
      _ ≤ |z.val.1 - w.val.1| + |w.val.1| := abs_add_le _ _
      _ ≤ 1 + ((k.natAbs : ℤ) + m) := by omega
      _ = (horizontalStripBlockerCollarRadius m k : ℤ) := by
        dsimp [horizontalStripBlockerCollarRadius]
        norm_num [horizontalStripBlockerCollarRadius]
        ring
  exact abs_le.mp hzabs

/-- Negating the literal failure event is exactly the universal outside-walk
blocking clause in `horizontalStripSourceAEvent`. -/
theorem not_mem_horizontalStripBlockerFailureEvent_iff_blocking
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) (ω : LatticeConfiguration) :
    ω ∉ horizontalStripBlockerFailureEvent n m k h hh ↔
      ∀ u : horizontalStripVertex n,
        ¬ horizontalStripClosedWindow n m k h u →
        ∀ p : (horizontalStripOpenGraph n ω).Walk u
          (horizontalStripVertexOfNat n k h (by omega)),
          ∃ z, z ∈ p.support ∧ horizontalStripWiredSide n m k h z := by
  classical
  constructor
  · intro hnot u hu p
    by_contra hno
    apply hnot
    refine ⟨u, hu, p, ?_⟩
    intro z hz hside
    exact hno ⟨z, hz, hside⟩
  · intro hblock hfail
    rcases hfail with ⟨u, hu, p, hp⟩
    rcases hblock u hu p with ⟨z, hz, hs⟩
    exact hp z hz hs

/-- Finite-rectangle formulation of the blocker failure. The witness walk is
in the actual open graph restricted to the centered finite collar; the static
window and wired-side predicates are pulled back to its rectangle vertices. -/
def horizontalStripBlockerCollarFailureEvent
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) : Set LatticeConfiguration :=
  {ω | ∃ u : RectangleVertex
      (-(horizontalStripBlockerCollarRadius m k : ℤ), 0)
      (2 * horizontalStripBlockerCollarRadius m k) (2 * n),
    ¬ horizontalStripClosedWindow n m k h
      (horizontalStripBlockerRectangleToStrip (horizontalStripBlockerCollarRadius m k) n u) ∧
      ∃ p : (horizontalStripBlockerCollarGraph (horizontalStripBlockerCollarRadius m k) n ω).Walk u
        (horizontalStripBlockerCollarRoot n m k h hh),
        (∀ z ∈ p.support, ¬ horizontalStripWiredSide n m k h
          (horizontalStripBlockerRectangleToStrip (horizontalStripBlockerCollarRadius m k) n z)) ∧
        (∀ z ∈ p.support,
          horizontalStripClosedWindow n m k h
            (horizontalStripBlockerRectangleToStrip (horizontalStripBlockerCollarRadius m k) n z) ∨ z = u)}

def horizontalStripBlockerCollarRootOnStrip (n m : ℕ) (k : ℤ) (h : ℕ)
    (hh : h ≤ n) : horizontalStripBlockerCollarSet
      (horizontalStripBlockerCollarRadius m k) n := by
  let x := horizontalStripVertexOfNat n k h (by omega)
  have hxwin : horizontalStripClosedWindow n m k h x := by
    simp [horizontalStripClosedWindow, x, horizontalStripVertexOfNat]
  have hxbound := horizontalStripBlockerWindow_x_bound n m k h x hxwin
  exact ⟨x, hxbound⟩

def horizontalStripBlockerFiniteFailureEvent
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) : Set LatticeConfiguration :=
  {ω | ∃ u : horizontalStripBlockerCollarSet (horizontalStripBlockerCollarRadius m k) n,
    ¬ horizontalStripClosedWindow n m k h u.val ∧
      ∃ p : (horizontalStripBlockerCollarGraphOnStrip
          (horizontalStripBlockerCollarRadius m k) n ω).Walk u
        (horizontalStripBlockerCollarRootOnStrip n m k h hh),
        (∀ z ∈ p.support, ¬ horizontalStripWiredSide n m k h z.val) ∧
        (∀ z ∈ p.support, horizontalStripClosedWindow n m k h z.val ∨ z = u)}

private theorem support_induce_val_mem
    {V : Type*} {G : SimpleGraph V} {S : Set V} {u v : V}
    (p : G.Walk u v) (hs : ∀ z ∈ p.support, z ∈ S)
    {z : S} (hz : z ∈ (p.induce S hs).support) : z.val ∈ p.support := by
  have hmap : List.map Subtype.val (p.induce S hs).support = p.support := by
    rw [SimpleGraph.Walk.support_induce]
    simp
  have : z.val ∈ List.map Subtype.val (p.induce S hs).support :=
    List.mem_map.mpr ⟨z, hz, rfl⟩
  simpa [hmap] using this

@[simp] private theorem horizontalStripBlockerCollarEquiv_symm_val
    (M n : ℕ) (v : horizontalStripBlockerCollarSet M n) :
    ((horizontalStripBlockerCollarEquiv M n).symm v).val = v.val.val := rfl

/-- The original outside-to-fixed-point failure is exactly a finite-collar
open-walk event. The collar is a finite graph isomorphic to the centered
rectangle graph of radius `|k|+m+1`. -/
theorem horizontalStripBlockerFailureEvent_iff_finiteFailureEvent
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) (ω : LatticeConfiguration) :
    ω ∈ horizontalStripBlockerFailureEvent n m k h hh ↔
      ω ∈ horizontalStripBlockerFiniteFailureEvent n m k h hh := by
  classical
  let x := horizontalStripVertexOfNat n k h (by omega)
  have hxwin : horizontalStripClosedWindow n m k h x := by
    simp [horizontalStripClosedWindow, x, horizontalStripVertexOfNat]
  constructor
  · rintro ⟨u, hu, p, hpW⟩
    have hAvoid : ∀ z ∈ p.support, z ∉ {v | horizontalStripWiredSide n m k h v} := by
      simpa using hpW
    have hLocal := (exists_avoiding_walk_from_outside_neighbor_iff
      (horizontalStripOpenGraph n ω) {v | horizontalStripClosedWindow n m k h v}
      {v | horizontalStripWiredSide n m k h v} hxwin).mp
      ⟨u, hu, p, hAvoid⟩
    rcases hLocal with ⟨z, hz, ⟨w, hw, hzw⟩, r, hrW, hrLoc⟩
    let hzC : horizontalStripBlockerCollarSet (horizontalStripBlockerCollarRadius m k) n :=
      ⟨z, horizontalStripBlockerNeighbor_x_bound n m k h ω hw hzw⟩
    have hrC : ∀ v ∈ r.support,
        horizontalStripBlockerCollarBound n (horizontalStripBlockerCollarRadius m k) v := by
      intro v hv
      rcases hrLoc v hv with hvwin | rfl
      · exact horizontalStripBlockerWindow_x_bound n m k h v hvwin
      · exact hzC.property
    let rC := r.induce
      (fun v : horizontalStripVertex n =>
        horizontalStripBlockerCollarBound n (horizontalStripBlockerCollarRadius m k) v) hrC
    have hrCW : ∀ v ∈ rC.support, ¬ horizontalStripWiredSide n m k h v.val := by
      intro v hv
      exact hrW v.val (support_induce_val_mem r hrC hv)
    have hrCL : ∀ v ∈ rC.support,
        horizontalStripClosedWindow n m k h v.val ∨ v.val = z := by
      intro v hv
      have h := hrLoc v.val (support_induce_val_mem r hrC hv)
      exact h
    exact ⟨hzC, hz, rC, hrCW, by
      intro v hv
      rcases hrCL v hv with hw | heq
      · exact Or.inl hw
      · right
        apply Subtype.ext
        exact heq⟩
  · rintro ⟨u, hu, p, hpW, hpLoc⟩
    let f : horizontalStripBlockerCollarGraphOnStrip
        (horizontalStripBlockerCollarRadius m k) n ω →g horizontalStripOpenGraph n ω :=
      { toFun := Subtype.val
        map_rel' := by intro a b hab; exact hab }
    let q : (horizontalStripOpenGraph n ω).Walk u.val
        (horizontalStripBlockerCollarRootOnStrip n m k h hh).val := p.map f
    have hqW : ∀ z ∈ q.support, ¬ horizontalStripWiredSide n m k h z := by
      intro z hz
      rw [SimpleGraph.Walk.support_map] at hz
      rcases List.mem_map.mp hz with ⟨v, hv, rfl⟩
      exact hpW v hv
    have hqLoc : ∀ z ∈ q.support, horizontalStripClosedWindow n m k h z ∨ z = u.val := by
      intro z hz
      rw [SimpleGraph.Walk.support_map] at hz
      rcases List.mem_map.mp hz with ⟨v, hv, rfl⟩
      rcases hpLoc v hv with hw | heq
      · exact Or.inl hw
      · right
        exact congrArg Subtype.val heq
    exact ⟨u.val, hu, q, hqW⟩

@[simp] private theorem horizontalStripBlockerCollarIso_root
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) (ω : LatticeConfiguration) :
    horizontalStripBlockerCollarGraphIso (horizontalStripBlockerCollarRadius m k) n ω
      (horizontalStripBlockerCollarRoot n m k h hh) =
        horizontalStripBlockerCollarRootOnStrip n m k h hh := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The finite rectangle event and its graph-isomorphic induced-strip
formulation are exactly equivalent. -/
theorem horizontalStripBlockerCollarFailureEvent_iff_finiteFailureEvent
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) (ω : LatticeConfiguration) :
    ω ∈ horizontalStripBlockerCollarFailureEvent n m k h hh ↔
      ω ∈ horizontalStripBlockerFiniteFailureEvent n m k h hh := by
  classical
  let I := horizontalStripBlockerCollarGraphIso
    (horizontalStripBlockerCollarRadius m k) n ω
  have hroot : I (horizontalStripBlockerCollarRoot n m k h hh) =
      horizontalStripBlockerCollarRootOnStrip n m k h hh := by
    exact horizontalStripBlockerCollarIso_root n m k h hh ω
  have hrootInv : I.symm (horizontalStripBlockerCollarRootOnStrip n m k h hh) =
      horizontalStripBlockerCollarRoot n m k h hh := by
    apply I.injective
    simp [hroot]
  constructor
  · rintro ⟨u, hu, p, hpW, hpLoc⟩
    have hstart : I u = horizontalStripBlockerRectangleToCollar
        (horizontalStripBlockerCollarRadius m k) n u := rfl
    let q := p.map I.toHom
    let q' := q.copy hstart hroot
    have hsup : q'.support = p.support.map I := by
      simp [q', q, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map]
    have hu' : ¬ horizontalStripClosedWindow n m k h
        (horizontalStripBlockerRectangleToCollar
          (horizontalStripBlockerCollarRadius m k) n u).val := by
      simpa [horizontalStripBlockerRectangleToCollar] using hu
    refine ⟨horizontalStripBlockerRectangleToCollar
      (horizontalStripBlockerCollarRadius m k) n u, hu', q', ?_, ?_⟩
    · intro z hz
      rw [hsup] at hz
      rcases List.mem_map.mp hz with ⟨v, hv, rfl⟩
      exact hpW v hv
    · intro z hz
      rw [hsup] at hz
      rcases List.mem_map.mp hz with ⟨v, hv, rfl⟩
      rcases hpLoc v hv with hw | heq
      · exact Or.inl hw
      · right
        rw [← hstart]
        exact congrArg I heq
  · rintro ⟨u, hu, p, hpW, hpLoc⟩
    let e := I.symm
    let uRect := (horizontalStripBlockerCollarEquiv
      (horizontalStripBlockerCollarRadius m k) n).symm u
    have hval :
        horizontalStripBlockerRectangleToStrip (horizontalStripBlockerCollarRadius m k) n
          uRect = u.val := by
      apply Subtype.ext
      simp [uRect, horizontalStripBlockerCollarEquiv]
    have hstart : e u = uRect := rfl
    let q := p.map e.toHom
    let q' := q.copy hstart hrootInv
    have hsup : q'.support = p.support.map e := by
      simp [q', q, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map]
    have hu' : ¬ horizontalStripClosedWindow n m k h
        (horizontalStripBlockerRectangleToStrip
          (horizontalStripBlockerCollarRadius m k) n uRect) := by
      simpa only [hval] using hu
    refine ⟨uRect, hu', q', ?_, ?_⟩
    · intro z hz
      rw [hsup] at hz
      rcases List.mem_map.mp hz with ⟨v, hv, rfl⟩
      exact hpW v hv
    · intro z hz
      rw [hsup] at hz
      rcases List.mem_map.mp hz with ⟨v, hv, rfl⟩
      rcases hpLoc v hv with hw | heq
      · exact Or.inl hw
      · right
        exact (congrArg e heq).trans hstart

end
end PottsContinuity.FKC.Medial
