module

public import PottsContinuity.Thm3.Prop4.TiltedConnectionEvents
public import PottsContinuity.Thm3.Prop4.TiltedIncidentEvents

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open MeasureTheory Filter Topology
open PottsContinuity.Thm3.Prop4

noncomputable section

local instance finiteWindowEdgeFintype (n R : ℕ) (t : ℝ) :
    Fintype (squareLattice.induce (tiltedWindow n R t : Set (ℤ × ℤ))).edgeSet :=
  Fintype.ofFinite _

private theorem walk_support_x_bound {V : Type*} (G : SimpleGraph V)
    (x : V → ℤ) {u v : V} (p : G.Walk u v)
    (hstep : ∀ a b, G.Adj a b → |x a - x b| ≤ 1) :
    ∀ z ∈ p.support, |x z - x u| ≤ (p.length : ℤ) := by
  induction p with
  | nil =>
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst z
      simp
  | @cons a b c hab p ih =>
      intro z hz
      rw [SimpleGraph.Walk.support_cons] at hz
      rcases List.mem_cons.mp hz with hza | hzp
      · subst z
        have hlen : (0 : ℤ) ≤ (p.length : ℤ) := Int.natCast_nonneg _
        simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one,
          sub_self, abs_zero]
        omega
      · have htail := ih z hzp
        have htri : |x z - x a| ≤ |x z - x b| + |x b - x a| := by
          calc
            |x z - x a| = |(x z - x b) + (x b - x a)| := by
              congr 1
              ring
            _ ≤ |x z - x b| + |x b - x a| := abs_add_le _ _
        have hstep' : |x b - x a| ≤ 1 := by
          rw [abs_sub_comm]
          exact hstep a b hab
        calc
          |x z - x a| ≤ |x z - x b| + |x b - x a| := htri
          _ ≤ (p.length : ℤ) + 1 := add_le_add htail hstep'
          _ = ((SimpleGraph.Walk.cons hab p).length : ℤ) := by
            simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]

private theorem tilted_edge_mem_windowCoordinates {n R : ℕ} {t : ℝ}
    {u v : tiltedStripVertices n t} (hu : u.1 ∈ box R) (hv : v.1 ∈ box R)
    (hadj : (tiltedStripGraph n t).Adj u v) :
    (⟨s(u,v),hadj⟩ : (tiltedStripGraph n t).edgeSet) ∈
      tiltedWindowEdgeCoordinates n R t := by
  classical
  let hu' : u.1 ∈ tiltedWindow n R t :=
    (mem_tiltedWindow n R t u.1).mpr ⟨hu,u.2⟩
  let hv' : v.1 ∈ tiltedWindow n R t :=
    (mem_tiltedWindow n R t v.1).mpr ⟨hv,v.2⟩
  let f : (squareLattice.induce (tiltedWindow n R t : Set (ℤ × ℤ))).edgeSet :=
    ⟨s(⟨u.1,hu'⟩,⟨v.1,hv'⟩),hadj⟩
  have hmap : (tiltedWindowStripEmbedding n R t).mapEdgeSet f = ⟨s(u,v),hadj⟩ := rfl
  change ⟨s(u,v),hadj⟩ ∈ Finset.univ.map (tiltedWindowStripEmbedding n R t).mapEdgeSet
  exact Finset.mem_map.mpr ⟨f,Finset.mem_univ _,hmap⟩

private theorem walk_edge_open_transfers {n : ℕ} {t : ℝ}
    (ω η : TiltedConfiguration n t) (R : ℕ)
    (hstate : ∀ e ∈ tiltedWindowEdgeCoordinates n R t, ω e = η e)
    {u v : tiltedStripVertices n t} (p : (tiltedOpenGraph n t ω).Walk u v)
    (hbox : ∀ z ∈ p.support, z.1 ∈ box R) :
    ∃ q : (tiltedOpenGraph n t η).Walk u v, q.support = p.support := by
  induction p with
  | nil =>
      exact ⟨.nil,rfl⟩
  | @cons a b c hab p ih =>
      have ha : a.1 ∈ box R := hbox a (by simp)
      have hb : b.1 ∈ box R := hbox b (by simp)
      obtain ⟨hbase,hopen⟩ := (tiltedOpenGraph_adj_iff n t ω a b).mp hab
      have hedge := tilted_edge_mem_windowCoordinates (n := n) (R := R) (t := t)
        ha hb hbase
      have hsame := hstate ⟨s(a,b),hbase⟩ hedge
      have habη : (tiltedOpenGraph n t η).Adj a b :=
        (tiltedOpenGraph_adj_iff n t η a b).mpr ⟨hbase,by rw [← hsame]; exact hopen⟩
      have hboxTail : ∀ z ∈ p.support, z.1 ∈ box R := by
        intro z hz
        exact hbox z (by simp [hz])
      obtain ⟨q,hq⟩ := ih hboxTail
      exact ⟨.cons habη q,by simp [hq]⟩

private theorem strip_vertical_coordinate_bound (N R : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (z : tiltedStripVertices N t)
    (hx : |z.1.1| ≤ (R : ℤ)) : |(z.1.2 : ℝ)| ≤ (R : ℝ) + N := by
  have hheight : tiltedHeight t z.1 ∈ Set.Icc (0 : ℝ) N := z.2
  rcases hheight with ⟨hheight0,hheightN⟩
  have hheightAbs : |tiltedHeight t z.1| ≤ (N : ℝ) := by
    apply abs_le.mpr
    have hN : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
    exact ⟨le_trans (neg_nonpos.mpr hN) hheight0,hheightN⟩
  have hxR : |(z.1.1 : ℝ)| ≤ (R : ℝ) := by exact_mod_cast hx
  have htR : |t| ≤ 1 := abs_le.mpr ht
  have htx : |t| * |(z.1.1 : ℝ)| ≤ (R : ℝ) := by
    calc
      |t| * |(z.1.1 : ℝ)| ≤ 1 * |(z.1.1 : ℝ)| :=
        mul_le_mul_of_nonneg_right htR (abs_nonneg _)
      _ ≤ (R : ℝ) := by simpa using hxR
  calc
    |(z.1.2 : ℝ)| = |tiltedHeight t z.1 + t * (z.1.1 : ℝ)| := by
      congr 1
      dsimp [tiltedHeight]
      ring
    _ ≤ |tiltedHeight t z.1| + |t * (z.1.1 : ℝ)| := abs_add_le _ _
    _ = |tiltedHeight t z.1| + |t| * |(z.1.1 : ℝ)| := by rw [abs_mul]
    _ ≤ (N : ℝ) + (R : ℝ) := add_le_add hheightAbs htx
    _ = (R : ℝ) + N := by ring

private theorem walk_support_in_box {n : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) {ω : TiltedConfiguration (2*n) t}
    {u v : tiltedStripVertices (2*n) t}
    (p : (tiltedOpenGraph (2*n) t ω).Walk u v)
    (hu : u.1.1 = 0) :
    ∀ z ∈ p.support, z.1 ∈ box (p.length + 2*n) := by
  intro z hz
  have hx := walk_support_x_bound (tiltedOpenGraph (2*n) t ω)
    (fun a => a.1.1) p
    (by
      intro a b hab
      have hbase := (tiltedOpenGraph_adj_iff (2*n) t ω a b).mp hab |>.1
      have hsq := (tiltedStripGraph (2*n) t).mem_edgeSet.mp hbase
      change |a.1.1-b.1.1|+|a.1.2-b.1.2|=1 at hsq
      have hnonneg : 0 ≤ |a.1.2-b.1.2| := abs_nonneg _
      have hxle : |a.1.1-b.1.1| ≤ 1 := by nlinarith
      exact hxle)
    z hz
  have hxInt : |z.1.1| ≤ (p.length : ℤ) := by
    rw [hu] at hx
    simpa using hx
  have hR : (p.length : ℤ) ≤ ((p.length + 2*n : ℕ) : ℤ) := by omega
  have hxR : |z.1.1| ≤ ((p.length + 2*n : ℕ) : ℤ) := hxInt.trans hR
  have hyReal := strip_vertical_coordinate_bound (2*n) p.length ht z hxInt
  have hyR : |z.1.2| ≤ ((p.length + 2*n : ℕ) : ℤ) := by
    have : |(z.1.2 : ℝ)| ≤ ((p.length + 2*n : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using hyReal
    exact_mod_cast this
  exact (Foundations.mem_box_iff_abs_le (p.length + 2*n) z.1).2 ⟨hxR,hyR⟩

/-- A central lower-half vertex reaches the intrinsic top by an open walk kept
inside a finite square window. -/
def tiltedTopConnectionWithinBox (n R : ℕ) (t : ℝ) :
    Set (TiltedConfiguration (2*n) t) :=
  {ω | ∃ k : ℕ, k ≤ n ∧
    ∃ z : tiltedStripVertices (2*n) t, z.1 = (0,(k : ℤ)) ∧
    ∃ v : tiltedStripVertices (2*n) t, tiltedTop (2*n) t v.1 ∧
    ∃ p : (tiltedOpenGraph (2*n) t ω).Walk z v,
      ∀ w ∈ p.support, w.1 ∈ box R}

/-- The infinite-strip half-height event is the union of its finite path-cylinder
approximations. -/
theorem lowestTopConnectedHeight_half_sublevel_eq_iUnion (n : ℕ)
    (hn : 1 ≤ 2*n) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    {ω : TiltedConfiguration (2*n) t |
      lowestTopConnectedHeight (2*n) hn t ω 0 ≤ n} =
      ⋃ R : ℕ, tiltedTopConnectionWithinBox n R t := by
  ext ω
  constructor
  · intro hω
    obtain ⟨l,hlow,hle⟩ :=
      (lowestTopConnectedHeight_le_iff (2*n) hn t ω 0 n).mp hω
    obtain ⟨hz,v,hv,hconn⟩ := hlow
    have hl0 : 0 ≤ l := by
      have := hz.1
      dsimp [tiltedHeight] at this
      norm_num at this
      exact_mod_cast this
    have hlNat : ((Int.toNat l : ℕ) : ℤ) = l := Int.toNat_of_nonneg hl0
    have hk : Int.toNat l ≤ n := by
      have hle' : (l : ℝ) ≤ n := by simpa using hle
      have hleZ : l ≤ (n : ℤ) := by exact_mod_cast hle'
      omega
    obtain ⟨p⟩ := hconn
    let R := p.length + 2*n
    let z₀ : tiltedStripVertices (2*n) t := ⟨(0,l),hz⟩
    have hz₀ : z₀.1 = (0,(Int.toNat l : ℤ)) := by
      change (0,l) = (0,(Int.toNat l : ℤ))
      exact Prod.ext rfl hlNat.symm
    refine Set.mem_iUnion.mpr ⟨R,Int.toNat l,hk,z₀,hz₀,v,hv,p,?_⟩
    exact walk_support_in_box ht p rfl
  · intro hω
    obtain ⟨R,hR⟩ := Set.mem_iUnion.mp hω
    change ∃ k : ℕ, k ≤ n ∧ ∃ z : tiltedStripVertices (2*n) t,
      z.1 = (0,(k : ℤ)) ∧ ∃ v : tiltedStripVertices (2*n) t,
      tiltedTop (2*n) t v.1 ∧ ∃ p : (tiltedOpenGraph (2*n) t ω).Walk z v,
      ∀ w ∈ p.support, w.1 ∈ box R at hR
    obtain ⟨k,hk,z,hz,v,hv,p,_⟩ := hR
    apply (lowestTopConnectedHeight_le_iff (2*n) hn t ω 0 n).mpr
    refine ⟨k,?_,?_⟩
    · have hconn : tiltedConnectedToTop (2*n) t ω (0,(k : ℤ)) := by
        rw [← hz]
        exact ⟨z.2,v,hv,p.reachable⟩
      exact hconn
    · have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
      simpa [hz] using hkR

/-- Agreement on the finite window edges fixes the bounded path event. -/
theorem tiltedTopConnectionWithinBox_finiteSupport (n R : ℕ) (t : ℝ)
    (ω η : TiltedConfiguration (2*n) t)
    (hagree : ∀ e ∈ tiltedWindowEdgeCoordinates (2*n) R t, ω e = η e) :
    ω ∈ tiltedTopConnectionWithinBox n R t ↔
      η ∈ tiltedTopConnectionWithinBox n R t := by
  constructor
  · rintro ⟨k,hk,z,hz,v,hv,p,hbox⟩
    obtain ⟨q,hq⟩ := walk_edge_open_transfers ω η R hagree p hbox
    exact ⟨k,hk,z,hz,v,hv,q,by simpa [hq] using hbox⟩
  · rintro ⟨k,hk,z,hz,v,hv,p,hbox⟩
    obtain ⟨q,hq⟩ := walk_edge_open_transfers η ω R
      (fun e he => (hagree e he).symm) p hbox
    exact ⟨k,hk,z,hz,v,hv,q,by simpa [hq] using hbox⟩

/-- Each bounded path event is a clopen cylinder on original strip edges. -/
theorem isClopen_tiltedTopConnectionWithinBox (n R : ℕ) (t : ℝ) :
    IsClopen (tiltedTopConnectionWithinBox n R t) :=
  tilted_isClopen_of_finite_support (2*n) t
    (tiltedWindowEdgeCoordinates (2*n) R t) _
    (tiltedTopConnectionWithinBox_finiteSupport n R t)

end

end PottsContinuity.Thm3.Touch
