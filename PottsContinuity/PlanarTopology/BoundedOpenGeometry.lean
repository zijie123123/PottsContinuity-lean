module

public import PottsContinuity.FKC.Domains.JordanInside
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open Set

/-- A continuous open real coordinate cannot attain its maximum inside an
open set with compact closure. Thus a bound on its frontier bounds the closure. -/
theorem coordinate_le_on_closure_of_frontier {X : Type*} [TopologicalSpace X]
    (U : Set X) (hU : IsOpen U) (hc : IsCompact (closure U))
    (f : X → ℝ) (hf : Continuous f) (ho : IsOpenMap f) (b : ℝ)
    (hb : ∀ x ∈ frontier U, f x ≤ b) : ∀ x ∈ closure U, f x ≤ b := by
  intro x hx
  obtain ⟨p,hp,hm⟩ := hc.exists_isMaxOn ⟨x,hx⟩ hf.continuousOn
  have hpn : p ∉ U := by
    intro hpU
    have hop : IsOpen (f '' U) := ho U hU
    obtain ⟨a,c,⟨hap,hpc⟩,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      (hop.mem_nhds (mem_image_of_mem f hpU))
    obtain ⟨q,hq,hqe⟩ := hsub (show (f p+c)/2 ∈ Ioo a c by constructor <;> linarith)
    have hm' : f q ≤ f p := hm (subset_closure hq)
    rw [hqe] at hm'
    linarith
  have hpf : p ∈ frontier U := by
    rw [hU.frontier_eq]
    exact ⟨hp,hpn⟩
  exact (hm hx).trans (hb p hpf)

/-- A preconnected set missing an open set's frontier cannot enter and leave
that open set. This generic form is used for explicit Jordan interiors. -/
theorem subset_open_of_preconnected_frontier_disjoint {X : Type*} [TopologicalSpace X]
    {N U : Set X} (hN : IsPreconnected N) (hU : IsOpen U)
    (hd : Disjoint N (frontier U)) (hm : (N ∩ U).Nonempty) : N ⊆ U := by
  apply hN.subset_of_closure_inter_subset hU hm
  intro x hx
  by_contra hn
  exact Set.disjoint_left.mp hd hx.2 (by rw [hU.frontier_eq]; exact ⟨hx.1,hn⟩)

/-- The same frontier bound is strict at every point of the open set. -/
theorem coordinate_lt_on_open_of_frontier {X : Type*} [TopologicalSpace X]
    (U : Set X) (hU : IsOpen U) (hc : IsCompact (closure U))
    (f : X → ℝ) (hf : Continuous f) (ho : IsOpenMap f) (b : ℝ)
    (hb : ∀ x ∈ frontier U, f x ≤ b) : ∀ x ∈ U, f x < b := by
  intro x hx
  have hs : f '' U ⊆ Iic b := by
    rintro y ⟨z,hz,rfl⟩
    exact coordinate_le_on_closure_of_frontier U hU hc f hf ho b hb z (subset_closure hz)
  have hxi : f x ∈ interior (f '' U) := by
    rw [(ho U hU).interior_eq]
    exact mem_image_of_mem f hx
  have hi := interior_mono hs hxi
  simpa only [interior_Iic,mem_Iio] using hi

/-- An open coordinate rectangle in the complex plane. -/
def complexOpenRectangle (a b c d : ℝ) : Set ℂ :=
  Complex.re ⁻¹' Ioo a b ∩ Complex.im ⁻¹' Ioo c d

/-- The literal four closed sides of the coordinate rectangle. -/
def complexRectangleBoundary (a b c d : ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d ∧
    (z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d)}

/-- A nonempty bounded open plane set whose frontier lies on the four sides
is the entire open rectangle. In particular, no separate reverse coverage of
all four continuous sides is needed to identify a polygon's Jordan interior. -/
theorem open_eq_rectangle_of_frontier_subset (U : Set ℂ) (hU : IsOpen U)
    (hc : IsCompact (closure U)) (hne : U.Nonempty) (a b c d : ℝ)
    (hfr : frontier U ⊆ complexRectangleBoundary a b c d) :
    U = complexOpenRectangle a b c d := by
  have hxr : ∀ z ∈ U, z.re < b :=
    coordinate_lt_on_open_of_frontier U hU hc Complex.re Complex.continuous_re
      Complex.isOpenMap_re b (fun z hz => (hfr hz).2.1)
  have hxl : ∀ z ∈ U, a < z.re := by
    intro z hz
    have h := coordinate_lt_on_open_of_frontier U hU hc (fun z : ℂ => -z.re)
      Complex.continuous_re.neg ((Homeomorph.neg ℝ).isOpenMap.comp Complex.isOpenMap_re)
      (-a) (fun z hz => by have h := (hfr hz).1; linarith) z hz
    linarith
  have hyr : ∀ z ∈ U, z.im < d :=
    coordinate_lt_on_open_of_frontier U hU hc Complex.im Complex.continuous_im
      Complex.isOpenMap_im d (fun z hz => (hfr hz).2.2.2.1)
  have hyl : ∀ z ∈ U, c < z.im := by
    intro z hz
    have h := coordinate_lt_on_open_of_frontier U hU hc (fun z : ℂ => -z.im)
      Complex.continuous_im.neg ((Homeomorph.neg ℝ).isOpenMap.comp Complex.isOpenMap_im)
      (-c) (fun z hz => by have h := (hfr hz).2.2.1; linarith) z hz
    linarith
  have hsub : U ⊆ complexOpenRectangle a b c d := by
    intro z hz
    exact ⟨⟨hxl z hz,hxr z hz⟩,⟨hyl z hz,hyr z hz⟩⟩
  apply subset_antisymm hsub
  apply subset_open_of_preconnected_frontier_disjoint
    ((((convex_Ioo a b).linear_preimage Complex.reLm).inter
      ((convex_Ioo c d).linear_preimage Complex.imLm)).isPreconnected) hU
  · apply Set.disjoint_left.mpr
    intro z hz hzfr
    rcases (hfr hzfr).2.2.2.2 with h | h | h | h
    all_goals change (a < z.re ∧ z.re < b) ∧ (c < z.im ∧ z.im < d) at hz
    all_goals linarith [hz.1.1,hz.1.2,hz.2.1,hz.2.2]
  · obtain ⟨z,hz⟩ := hne
    exact ⟨z,hsub hz,hz⟩

end PottsContinuity.PlanarTopology
