module

public import PottsContinuity.DualityExt.AnnulusCounterexample
public import PottsContinuity.FKC.FiniteFK.OutsidePathLocalization
public import PottsContinuity.PD.RCInfinite.TranslationSupport
public import PottsContinuity.PD.RCInfinite.Cylinders
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open MeasureTheory
open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial
open PottsContinuity.PD.RCInfinite
open PottsContinuity.DualityExt

private theorem annulusVertexSet_subset_outerBox (r : ℕ) {x : LatticeVertex}
    (hx : x ∈ annulusVertexSet r) : x ∈ latticeBox (0, 0) (2 * r) :=
  (Finset.mem_sdiff.mp hx).1

theorem annulusOuterBoundary_not_innerBox (r : ℕ) (hr : 1 ≤ r)
    {x : LatticeVertex} (hx : x ∈ annulusOuterBoundary (2 * r)) :
    x ∉ latticeBox (0, 0) r := by
  intro hxbox
  unfold annulusOuterBoundary at hx
  simp only [Finset.mem_filter] at hx
  rcases hx with ⟨_, hface⟩
  rw [mem_latticeBox] at hxbox
  rcases hface with h | h | h | h <;>
    simp only [zero_sub, zero_add] at hxbox <;>
    omega

 theorem annulusOpenGraph_adj_transfer
    (r : ℕ) (P : LatticeVertex → LatticeVertex → Prop)
    (ω η : LatticeConfiguration)
    (hstate : ∀ u v (h : squareLattice.Adj u v), P u v →
      ω ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true →
        η ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true)
    {u v : LatticeVertex} (hAdj : (annulusOpenGraph r ω).Adj u v)
    (hP : P u v) : (annulusOpenGraph r η).Adj u v := by
  change u ∈ annulusVertexSet r ∧ v ∈ annulusVertexSet r ∧
    (wholePlaneOpenPrimalGraph ω).Adj u v at hAdj
  rcases hAdj with ⟨hu, hv, hopen⟩
  rcases hopen with ⟨hadj, hopen⟩
  refine ⟨hu, hv, ⟨hadj, ?_⟩⟩
  exact hstate u v hadj hP hopen

noncomputable def annulusOpenWalk_transfer
    (r : ℕ) (P : LatticeVertex → LatticeVertex → Prop)
    (ω η : LatticeConfiguration)
    (hstate : ∀ u v (h : squareLattice.Adj u v), P u v →
      ω ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true →
        η ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true)
    {u v : LatticeVertex} (p : (annulusOpenGraph r ω).Walk u v)
    (hP : ∀ a b, (annulusOpenGraph r ω).Adj a b → P a b) :
    (annulusOpenGraph r η).Walk u v := by
  induction p with
  | nil => exact .nil
  | @cons u v w hadj p ih =>
      exact .cons (annulusOpenGraph_adj_transfer r P ω η hstate hadj
        (hP u v hadj)) ih

noncomputable def annulusOpenWalk_transfer_outside
    (r : ℕ) (ω η : LatticeConfiguration)
    (hstate : ∀ u v (h : squareLattice.Adj u v),
      (u ∉ latticeBox (0, 0) r ∨ v ∉ latticeBox (0, 0) r) →
      ω ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true →
        η ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true)
    {u y : LatticeVertex} (root : LatticeVertex)
    (p : (annulusOpenGraph r ω).Walk u y)
    (hsupport : ∀ v ∈ p.support,
      v ∈ (latticeBox (0, 0) r : Set LatticeVertex)ᶜ ∨ v = root) :
    (annulusOpenGraph r η).Walk u y := by
  induction p with
  | nil => exact .nil
  | @cons u v w hadj p ih =>
      have huSupport : u ∈ (SimpleGraph.Walk.cons hadj p).support :=
        SimpleGraph.Walk.start_mem_support _
      have hvSupport : v ∈ (SimpleGraph.Walk.cons hadj p).support :=
        (SimpleGraph.Walk.support_subset_support_cons p hadj) p.start_mem_support
      have hsep : u ∉ latticeBox (0, 0) r ∨ v ∉ latticeBox (0, 0) r := by
        by_contra hnot
        have huBox := (not_or.mp hnot).1
        have hvBox := (not_or.mp hnot).2
        obtain huH | huEq := hsupport u huSupport
        · exact huBox huH
        obtain hvH | hvEq := hsupport v hvSupport
        · exact hvBox hvH
        rw [huEq, hvEq] at hadj
        exact (annulusOpenGraph r ω).loopless.irrefl root hadj
      have htail : ∀ x ∈ p.support,
          x ∈ (latticeBox (0, 0) r : Set LatticeVertex)ᶜ ∨ x = root := by
        intro x hx
        exact hsupport x ((SimpleGraph.Walk.support_subset_support_cons p hadj) hx)
      exact .cons (annulusOpenGraph_adj_transfer r
        (fun a b => a ∉ latticeBox (0, 0) r ∨ b ∉ latticeBox (0, 0) r)
        ω η (fun a b h hP hopen => hstate a b h hP hopen) hadj hsep)
        (ih htail)

private theorem annulusOpenCrossing_of_outside_agreement
    (r : ℕ) (hr : 1 ≤ r) (ω η : LatticeConfiguration)
    (hAgree : ∀ e ∈ (boxEdges (0, 0) r)ᶜ, ω e = η e)
    (hCross : ω ∈ {ω | annulusOpenCrossing r ω}) :
    η ∈ {ω | annulusOpenCrossing r ω} := by
  classical
  rcases hCross with ⟨x, y, hx, hy, p⟩
  rcases p with ⟨p⟩
  let H : Set LatticeVertex := (latticeBox (0, 0) r : Set LatticeVertex)ᶜ
  have hxH : x ∉ H := by simpa [H] using hx
  have hyH : y ∈ H := by
    simpa [H] using annulusOuterBoundary_not_innerBox r hr hy
  have hleft : ∃ x', x' ∉ H ∧ ∃ p : (annulusOpenGraph r ω).Walk x' y,
      ∀ v ∈ p.support, v ∉ (∅ : Set LatticeVertex) :=
    ⟨x, hxH, p, by simp⟩
  obtain ⟨z, hzH, _hneighbor, p', _havoid, hsupport⟩ :=
    (PottsContinuity.FKC.Medial.exists_avoiding_walk_from_outside_neighbor_iff
      (annulusOpenGraph r ω) H (∅ : Set LatticeVertex) hyH).mp hleft
  have hzbox : z ∈ latticeBox (0, 0) r := by simpa [H] using hzH
  have hstate : ∀ u v (h : squareLattice.Adj u v),
      (u ∉ latticeBox (0, 0) r ∨ v ∉ latticeBox (0, 0) r) →
      ω ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true →
        η ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true := by
    intro u v hadj hsep hopen
    let e : squareLattice.edgeSet := ⟨s(u, v), squareLattice.mem_edgeSet.mpr hadj⟩
    have henot : e ∉ boxEdges (0, 0) r := by
      intro he
      rw [mem_boxEdges_iff] at he
      rcases hsep with hu | hv
      · exact hu (he u (by simp [e]))
      · exact hv (he v (by simp [e]))
    have hecomp : e ∈ (boxEdges (0, 0) r)ᶜ := by simpa using henot
    exact (hAgree e hecomp).symm.trans hopen
  have pη := annulusOpenWalk_transfer_outside r ω η hstate z p' hsupport
  exact ⟨z, y, hzbox, hy, ⟨pη⟩⟩

/-- The full-inner-box annulus crossing reads only edges strictly outside its
inner box. The last-exit walk localization removes any initial boundary walk
that could otherwise use edges internal to that box. -/
theorem annulusOpenCrossing_dependsOn_outside (r : ℕ) (hr : 1 ≤ r) :
    DependsOn (boxEdges (0, 0) r)ᶜ {ω | annulusOpenCrossing r ω} := by
  intro ω η hAgree
  constructor
  · exact annulusOpenCrossing_of_outside_agreement r hr ω η hAgree
  · exact annulusOpenCrossing_of_outside_agreement r hr η ω
      (fun e he => (hAgree e he).symm)

/-- The annulus crossing is a finite-coordinate event supported in its outer
box. -/
theorem annulusOpenCrossing_dependsOn_outerBox (r : ℕ) :
    DependsOn (boxEdges (0, 0) (2 * r)) {ω | annulusOpenCrossing r ω} := by
  intro ω η hAgree
  constructor
  · intro hCross
    rcases hCross with ⟨x, y, hx, hy, p⟩
    rcases p with ⟨p⟩
    have hstate : ∀ u v (h : squareLattice.Adj u v),
        (u ∈ latticeBox (0, 0) (2 * r) ∧ v ∈ latticeBox (0, 0) (2 * r)) →
        ω ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true →
          η ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true := by
      intro u v hadj hbox hopen
      let e : squareLattice.edgeSet := ⟨s(u, v), squareLattice.mem_edgeSet.mpr hadj⟩
      have he : e ∈ boxEdges (0, 0) (2 * r) := by
        rw [mem_boxEdges_iff]
        intro a ha
        have ha' : a = u ∨ a = v := by simpa [e] using ha
        rcases ha' with rfl | rfl
        · exact hbox.1
        · exact hbox.2
      exact (hAgree e he).symm.trans hopen
    have hP : ∀ u v, (annulusOpenGraph r ω).Adj u v →
        u ∈ latticeBox (0, 0) (2 * r) ∧ v ∈ latticeBox (0, 0) (2 * r) := by
      intro u v huv
      change u ∈ annulusVertexSet r ∧ v ∈ annulusVertexSet r ∧ _ at huv
      exact ⟨annulusVertexSet_subset_outerBox r huv.1,
        annulusVertexSet_subset_outerBox r huv.2.1⟩
    exact ⟨x, y, hx, hy, ⟨annulusOpenWalk_transfer r
      (fun u v => u ∈ latticeBox (0, 0) (2 * r) ∧
        v ∈ latticeBox (0, 0) (2 * r)) ω η hstate p hP⟩⟩
  · intro hCross
    rcases hCross with ⟨x, y, hx, hy, p⟩
    rcases p with ⟨p⟩
    have hstate : ∀ u v (h : squareLattice.Adj u v),
        (u ∈ latticeBox (0, 0) (2 * r) ∧ v ∈ latticeBox (0, 0) (2 * r)) →
        η ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true →
          ω ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true := by
      intro u v hadj hbox hopen
      let e : squareLattice.edgeSet := ⟨s(u, v), squareLattice.mem_edgeSet.mpr hadj⟩
      have he : e ∈ boxEdges (0, 0) (2 * r) := by
        rw [mem_boxEdges_iff]
        intro a ha
        have ha' : a = u ∨ a = v := by simpa [e] using ha
        rcases ha' with rfl | rfl
        · exact hbox.1
        · exact hbox.2
      exact (hAgree e he).trans hopen
    have hP : ∀ u v, (annulusOpenGraph r η).Adj u v →
        u ∈ latticeBox (0, 0) (2 * r) ∧ v ∈ latticeBox (0, 0) (2 * r) := by
      intro u v huv
      change u ∈ annulusVertexSet r ∧ v ∈ annulusVertexSet r ∧ _ at huv
      exact ⟨annulusVertexSet_subset_outerBox r huv.1,
        annulusVertexSet_subset_outerBox r huv.2.1⟩
    exact ⟨x, y, hx, hy, ⟨annulusOpenWalk_transfer r
      (fun u v => u ∈ latticeBox (0, 0) (2 * r) ∧
        v ∈ latticeBox (0, 0) (2 * r)) η ω hstate p hP⟩⟩

/-- The annulus crossing event is an increasing cylinder event. -/
theorem annulusOpenCrossing_isCylinder (r : ℕ) :
    IsCylinder {ω | annulusOpenCrossing r ω} := by
  classical
  have hfinite : (boxEdges (0, 0) (2 * r)).Finite := Set.finite_range _
  refine ⟨hfinite.toFinset, ?_⟩
  have hdep := annulusOpenCrossing_dependsOn_outerBox r
  rw [hfinite.coe_toFinset]
  exact hdep

theorem annulusOpenCrossing_isUpperSet (r : ℕ) :
    IsUpperSet {ω | annulusOpenCrossing r ω} := by
  intro ω η hωη hCross
  rcases hCross with ⟨x, y, hx, hy, p⟩
  rcases p with ⟨p⟩
  have hstate : ∀ u v (h : squareLattice.Adj u v),
      (u ∈ latticeBox (0, 0) (2 * r) ∧ v ∈ latticeBox (0, 0) (2 * r)) →
      ω ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true →
        η ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true := by
    intro u v hadj _ hopen
    let e : squareLattice.edgeSet := ⟨s(u, v), squareLattice.mem_edgeSet.mpr hadj⟩
    cases hη : η e with
    | false =>
        have hle : true ≤ false := by
          simpa [e, hopen, hη] using hωη e
        have hbad : ¬ (true ≤ false) := by decide
        exact (hbad hle).elim
    | true => rfl
  have hP : ∀ u v, (annulusOpenGraph r ω).Adj u v →
      u ∈ latticeBox (0, 0) (2 * r) ∧ v ∈ latticeBox (0, 0) (2 * r) := by
    intro u v huv
    change u ∈ annulusVertexSet r ∧ v ∈ annulusVertexSet r ∧ _ at huv
    exact ⟨annulusVertexSet_subset_outerBox r huv.1,
      annulusVertexSet_subset_outerBox r huv.2.1⟩
  exact ⟨x, y, hx, hy, ⟨annulusOpenWalk_transfer r
    (fun u v => u ∈ latticeBox (0, 0) (2 * r) ∧
      v ∈ latticeBox (0, 0) (2 * r)) ω η hstate p hP⟩⟩

end PottsContinuity.Thm3.Easy
