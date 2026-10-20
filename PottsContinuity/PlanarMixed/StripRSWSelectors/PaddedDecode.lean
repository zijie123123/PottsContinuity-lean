module

public import PottsContinuity.PlanarMixed.StripRSWSelectors.PaddedArm
public import PottsContinuity.Thm3.Push.ConfinedPrefixCrosscutGeometry

@[expose] public section

namespace PottsContinuity.PlanarMixed.StripRSWSelectors
open PD.FK Push BD12 Exploration
noncomputable section

/-- Clamping the two extra coordinates is a retraction onto the source. -/
def prefixPaddingRetraction (n : ℕ) (v : PrefixAuxVertex n) : PrefixSourceVertex n :=
  ⟨(min v.val.1 (2*(n:ℤ)),min v.val.2 (2*(n:ℤ))),by
    have hv :=  (PD.FK.mem_latticeRectangle _ _ _ _).mp v.property
    rw [PD.FK.mem_latticeRectangle]
    dsimp at hv ⊢
    constructor <;> constructor <;> omega⟩

@[simp] theorem prefixPaddingRetraction_embedding (n : ℕ) (v : PrefixSourceVertex n) :
    prefixPaddingRetraction n (prefixPaddingEmbedding n v) = v :=  by
  apply Subtype.ext
  have hv :=  (PD.FK.mem_latticeRectangle _ _ _ _).mp v.property
  change (min v.val.1 (2*(n:ℤ)),min v.val.2 (2*(n:ℤ))) = v.val
  dsimp at hv
  exact Prod.ext (min_eq_left (by omega)) (min_eq_left (by omega))

/-- Target membership is preserved even on the added vertices. -/
theorem prefixPaddingRetraction_mem_target_iff (n s : ℕ) (_hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) (v : PrefixAuxVertex n) :
    ((prefixPaddingRetraction n v).val.1 = 4*(s:ℤ)-1 ∧
      b.2.val.2 ≤ (prefixPaddingRetraction n v).val.2) ↔ v ∈ prefixAuxRay n s b :=  by
  have hb :=  (PD.FK.mem_latticeRectangle _ _ _ _).mp b.2.property
  change (min v.val.1 (2*(n:ℤ)) = 4*(s:ℤ)-1 ∧ b.2.val.2 ≤ min v.val.2 (2*(n:ℤ))) ↔
    v.val.1 = 4*(s:ℤ)-1 ∧ b.2.val.2 ≤ v.val.2
  dsimp at hb
  constructor <;> intro h <;> constructor <;> omega

/-- A first-contact walk has no edge with both endpoints in its target. -/
theorem first_contact_no_target_edge {V : Type*} {G : SimpleGraph V} {a t : V}
    (p : G.Walk a t) (T : Set V) (ht : t ∈ T)
    (hfirst : firstContactTrace T p.support = some p.support)
    {u v : V} (he : s(u,v) ∈ p.edges) : ¬(u ∈ T ∧ v ∈ T) :=  by
  have hc :=  (firstContactTrace_fixed_iff_firstContact_at_length p T ht).mp hfirst
  have htake : (p.take p.length).support = p.support :=  by
    rw [SimpleGraph.Walk.support_take,←p.length_support,List.take_length]
  intro h
  have hu :=  firstContact_prefix_target_unique p T p.length hc u
    (htake.symm ▸ p.fst_mem_support_of_mem_edges he) h.1
  have hv :=  firstContact_prefix_target_unique p T p.length hc v
    (htake.symm ▸ p.snd_mem_support_of_mem_edges he) h.2
  exact (p.adj_of_mem_edges he).ne (hu.trans hv.symm)

/-- Before its first ray contact an auxiliary open walk uses only sampled
confined bonds; none of the fixed ray bonds survives the crop. -/
theorem prefixAux_first_contact_edges_decode (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    {a t : PrefixAuxVertex n}
    (p : (openGraph (prefixAuxGraph n) (prefixAuxCompletion n s hfit b C)).Walk a t)
    (ht : t ∈ prefixAuxRay n s b)
    (hfirst : firstContactTrace (prefixAuxRay n s b) p.support = some p.support)
    {u v : PrefixAuxVertex n} (he : s(u,v) ∈ p.edges) :
    (openGraph (caseTwoConfinedPrefixGraph n s hfit b)
      (caseTwoConfinedPrefixConfiguration n s hfit b C)).Adj
      (prefixPaddingRetraction n u) (prefixPaddingRetraction n v) :=  by
  classical
  obtain ⟨e,heo,heq⟩ :=  (openGraph_adj _ _ u v).mp (p.adj_of_mem_edges he)
  rcases prefixAuxCompletion_open_edge_cases n s hfit b C e heo with ⟨f,hf,hfe⟩ | hray
  · apply (openGraph_adj _ _ _ _).mpr
    refine ⟨f,hf,?_⟩
    have hm :=  congrArg (Sym2.map (prefixPaddingRetraction n))
      ((congrArg Subtype.val hfe).trans heq)
    change Sym2.map (prefixPaddingRetraction n)
      (Sym2.map (prefixPaddingEmbedding n) f.val) = _ at hm
    rw [Sym2.map_map] at hm
    have hid : (prefixPaddingRetraction n) ∘ (prefixPaddingEmbedding n) = id :=  by
      funext z
      exact prefixPaddingRetraction_embedding n z
    rw [hid,Sym2.map_id] at hm
    exact hm
  · exact (first_contact_no_target_edge p _ ht hfirst he
      ⟨hray u (by rw [heq]; exact Sym2.mem_mk_left _ _),
        hray v (by rw [heq]; exact Sym2.mem_mk_right _ _)⟩).elim

/-- Mapping a trace commutes with first contact when target membership agrees. -/
theorem firstContactTrace_map_of_target_iff {V W : Type*} (f : V → W)
    (S : Set V) (T : Set W) (h : ∀ v, f v ∈ T ↔ v ∈ S) (trace : List V) :
    firstContactTrace T (trace.map f) = (firstContactTrace S trace).map (List.map f) := by
  classical
  have he : (fun v => decide (f v ∈ T)) = (fun v => decide (v ∈ S)) := by
    funext v
    exact decide_eq_decide.mpr (h v)
  simp only [firstContactTrace,List.findIdx?_map,Function.comp_def,he]
  cases trace.findIdx? (fun v => decide (v ∈ S)) <;>
    simp only [Option.map_none,Option.map_some,List.map_take]

/-- The cropped auxiliary walk decodes to a physical confined walk with
exactly the mapped first-contact support. -/
theorem prefixAux_first_contact_decodes (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    {a t : PrefixAuxVertex n}
    (p : (openGraph (prefixAuxGraph n) (prefixAuxCompletion n s hfit b C)).Walk a t)
    (ha : a ∈ intervalArmBottomArc (2*n+1) (4*(s:ℤ)) (5*(s:ℤ)))
    (ht : t ∈ prefixAuxRay n s b)
    (hfirst : firstContactTrace (prefixAuxRay n s b) p.support = some p.support) :
    ConfinedPrefixFirstContact n s hfit C b (p.support.map (prefixPaddingRetraction n)) := by
  let T : Set (PrefixSourceVertex n) := {z | z.val.1 = 4*(s:ℤ)-1 ∧ b.2.val.2 ≤ z.val.2}
  let q := retainedWalk (openGraph (caseTwoConfinedPrefixGraph n s hfit b)
    (caseTwoConfinedPrefixConfiguration n s hfit b C)) (prefixPaddingRetraction n) p
    (prefixAux_first_contact_edges_decode n s hfit b C p ht hfirst)
  refine ⟨prefixPaddingRetraction n a,?_,prefixPaddingRetraction n t,
    ((prefixPaddingRetraction_mem_target_iff n s hs hfit b t).mpr ht).1,
    ((prefixPaddingRetraction_mem_target_iff n s hs hfit b t).mpr ht).2,q,
    retainedWalk_support _ _ _ _,?_⟩
  · change min a.val.2 (2*(n:ℤ)) = 0 ∧
      4*(s:ℤ) ≤ min a.val.1 (2*(n:ℤ)) ∧ min a.val.1 (2*(n:ℤ)) ≤ 5*(s:ℤ)
    have ha0 := ha.1
    have hal := ha.2.1
    have har := ha.2.2
    constructor <;> omega
  · rw [firstContactTrace_map_of_target_iff (prefixPaddingRetraction n)
      (prefixAuxRay n s b) T (prefixPaddingRetraction_mem_target_iff n s hs hfit b),hfirst]
    rfl

end
end PottsContinuity.PlanarMixed.StripRSWSelectors
