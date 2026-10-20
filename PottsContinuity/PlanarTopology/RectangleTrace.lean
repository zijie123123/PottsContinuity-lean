module

public import PottsContinuity.PlanarTopology.TraceChronology
public import PottsContinuity.PlanarTopology.CentralTargetDuality
public import PottsContinuity.BD12.KSTEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- Exactly the original rectangle edges occurring in the given lattice
walk; vertices outside the rectangle and chords are never inserted. -/
noncomputable def rectangleTraceConfiguration (a : PD.FK.LatticeVertex) (w h : ℕ)
    {u v : PD.FK.LatticeVertex} (p : PD.squareLattice.Walk u v) :
    PD.FK.Configuration (PD.FK.rectangleGraph a w h) := by
  classical
  exact Finset.univ.filter fun e => Sym2.map
    (fun z : PD.FK.RectangleVertex a w h => z.val) e.val ∈ p.edges

/-- The exact trace-membership test for each original rectangle bond. -/
theorem mem_rectangleTraceConfiguration (a : PD.FK.LatticeVertex) (w h : ℕ)
    {u v : PD.FK.LatticeVertex} (p : PD.squareLattice.Walk u v)
    (e : (PD.FK.rectangleGraph a w h).edgeSet) :
    e ∈ rectangleTraceConfiguration a w h p ↔
      Sym2.map (fun z : PD.FK.RectangleVertex a w h => z.val) e.val ∈ p.edges := by
  classical
  simp only [rectangleTraceConfiguration,Finset.mem_filter,Finset.mem_univ,true_and]

/-- The trace's actual open graph embeds into the original lattice by
forgetting only the rectangle subtype proof. -/
def rectangleTraceOpenHom (a : PD.FK.LatticeVertex) (w h : ℕ)
    {u v : PD.FK.LatticeVertex} (p : PD.squareLattice.Walk u v) :
    PD.FK.openGraph (PD.FK.rectangleGraph a w h) (rectangleTraceConfiguration a w h p) →g
      PD.squareLattice where
  toFun z := z.val
  map_rel' {x y} hxy := (PD.FK.rectangleGraph_adj_iff a w h x y).mp
    (PD.FK.openGraph_le _ _ hxy)

/-- Every edge of a trace-open walk really occurs in the original walk. -/
theorem rectangle_trace_walk_edges_subset (a : PD.FK.LatticeVertex) (w h : ℕ)
    {u v : PD.FK.LatticeVertex} (p : PD.squareLattice.Walk u v)
    {x y : PD.FK.RectangleVertex a w h}
    (q : (PD.FK.openGraph (PD.FK.rectangleGraph a w h)
      (rectangleTraceConfiguration a w h p)).Walk x y) :
    (q.map (rectangleTraceOpenHom a w h p)).edges ⊆ p.edges := by
  intro edge hedge
  rw [SimpleGraph.Walk.edges_map] at hedge
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hedge
  have hm := q.edges_subset_edgeSet he
  rw [PD.FK.openGraph_edgeSet] at hm
  obtain ⟨b,hb,hbe⟩ := hm
  have ht := (mem_rectangleTraceConfiguration a w h p b).mp hb
  rw [hbe] at ht
  exact ht

set_option backward.isDefEq.respectTransparency false in
/-- Every nontrivial actual connection in a simple path's restricted rectangle
trace is the corresponding CONTIGUOUS segment of that path, in one orientation. -/
theorem rectangle_trace_connection_subpath (a : PD.FK.LatticeVertex) (w h : ℕ)
    {u v : PD.FK.LatticeVertex} (p : PD.squareLattice.Walk u v) (hp : p.IsPath)
    (x y : PD.FK.RectangleVertex a w h) (hne : x.val ≠ y.val)
    (hxy : PD.FK.ActualConnected (PD.FK.rectangleGraph a w h)
      (rectangleTraceConfiguration a w h p) x y) :
    ∃ r : PD.squareLattice.Walk x.val y.val,
      (r.IsSubwalk p ∨ r.reverse.IsSubwalk p) ∧ r.IsPath ∧
      ∀ z ∈ r.support, z ∈ PD.FK.latticeRectangle a w h := by
  obtain ⟨q⟩ := hxy
  let q' : PD.squareLattice.Walk x.val y.val := q.map (rectangleTraceOpenHom a w h p)
  have hedge : q'.edges ⊆ p.edges := rectangle_trace_walk_edges_subset a w h p q
  have hnil : ¬q'.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  have hsupport : ∀ z ∈ q'.support, z ∈ p.support := by
    intro z hz
    obtain ⟨edge,he,hze⟩ :=
      (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnil).mp hz
    exact SimpleGraph.Walk.mem_support_of_mem_edges (hedge he) hze
  apply path_subpath_of_edges_subset p hp q' (hsupport _ q'.start_mem_support)
    (hsupport _ q'.end_mem_support) hedge (PD.FK.latticeRectangle a w h : Set _)
  intro z hz
  change z ∈ (q.map (rectangleTraceOpenHom a w h p)).support at hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨z',_,rfl⟩ := List.mem_map.mp hz
  exact z'.property

/-- Absence of an m-path as a CONTIGUOUS segment excludes central-target
primal connectivity in the restricted trace. Here m=12k is exact. -/
theorem rectangle_trace_no_central_connection_of_no_mpath (k : ℕ) (hk : 1 ≤ k)
    {u v : PD.FK.LatticeVertex} (p : PD.squareLattice.Walk u v) (hp : p.IsPath)
    (hno : ¬∃ (x y : PD.FK.LatticeVertex) (r : PD.squareLattice.Walk x y),
      BD12.kstMPath (12*k) r ∧ (r.IsSubwalk p ∨ r.reverse.IsSubwalk p)) :
    ¬∃ x : PD.FK.RectangleVertex (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k),
      (x.val.2 = 12*(k : ℤ) ∧ -(k : ℤ) ≤ x.val.1 ∧ x.val.1 ≤ (k : ℤ)) ∧
      ∃ y : PD.FK.RectangleVertex (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k),
        (y.val.2 = -12*(k : ℤ) ∧ -(k : ℤ) ≤ y.val.1 ∧ y.val.1 ≤ (k : ℤ)) ∧
        PD.FK.ActualConnected _
          (rectangleTraceConfiguration (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k) p) x y := by
  rintro ⟨x,hx,y,hy,hxy⟩
  have hne : x.val ≠ y.val := by
    intro he
    have hh := congrArg Prod.snd he
    omega
  obtain ⟨r,hr,hrp,hrH⟩ := rectangle_trace_connection_subpath
    (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k) p hp x y hne hxy
  apply hno
  refine ⟨x.val,y.val,r,?_,hr⟩
  have hxabs : |x.val.1| ≤ (k : ℤ) := abs_le.mpr ⟨hx.2.1,hx.2.2⟩
  have hyabs : |y.val.1| ≤ (k : ℤ) := abs_le.mpr ⟨hy.2.1,hy.2.2⟩
  refine ⟨hrp,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.cast_mul,Nat.cast_ofNat] using hx.1
  · simpa only [Nat.cast_mul,Nat.cast_ofNat,neg_mul] using hy.1
  · push_cast
    omega
  · push_cast
    omega
  · intro z hz
    have hbox := (PD.FK.mem_latticeRectangle _ z (26*k) (24*k)).mp (hrH z hz)
    have hzx : |z.1| ≤ 13*(k : ℤ) := by
      apply abs_le.mpr
      simp only [Nat.cast_mul,Nat.cast_ofNat] at hbox
      omega
    have hzy : |z.2| ≤ 12*(k : ℤ) := by
      apply abs_le.mpr
      simp only [Nat.cast_mul,Nat.cast_ofNat] at hbox
      omega
    push_cast
    constructor <;> omega

/-- The KST no-subpath case has an ACTUAL complementary-dual B/D crossing
avoiding every original edge of the restricted simple-path trace. This is the
input for the continuous avoidance connector, not the corridor lemma itself. -/
theorem kst_trace_dual_of_no_mpath (k : ℕ) (hk : 1 ≤ k)
    {u v : PD.FK.LatticeVertex} (p : PD.squareLattice.Walk u v) (hp : p.IsPath)
    (hno : ¬∃ (x y : PD.FK.LatticeVertex) (r : PD.squareLattice.Walk x y),
      BD12.kstMPath (12*k) r ∧ (r.IsSubwalk p ∨ r.reverse.IsSubwalk p)) :
    ∃ b : PD.FK.RectangleDualVertex (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k),
      b.val ∈ centralLeftDualPorts k ∧
      ∃ d : PD.FK.RectangleDualVertex (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k),
        d.val ∈ centralRightDualPorts k ∧
        (PD.FK.openGraph
          (PD.FK.rectangleDualGraph (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k))
          (PD.FK.rectangleDualConfiguration (-13*(k : ℤ),-12*(k : ℤ))
            (26*k) (24*k)
            (rectangleTraceConfiguration (-13*(k : ℤ),-12*(k : ℤ))
              (26*k) (24*k) p))).Reachable b d :=
  central_target_dual_exists k hk _
    (rectangle_trace_no_central_connection_of_no_mpath k hk p hp hno)

end PottsContinuity.PlanarTopology
