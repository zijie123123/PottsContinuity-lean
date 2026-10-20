module

public import Mathlib

/-!
# The definitions used by the main theorems

The 22 definitions on which the statements of `PottsContinuity/Frozen/` depend, transcribed from
H. Duminil-Copin, V. Sidoravicius and V. Tassion, arXiv:1505.04159v1. Their text was reviewed
against the paper and approved by the author before any proof was written. They form one module,
in the same order as in `Challenge.lean`, so that the definitions here and there elaborate to the
same terms (including the auxiliary proofs Lean creates inside definition bodies); Comparator
checks that they agree.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal


namespace PottsContinuity

/-- The box `Λₙ = [-n, n]² ∩ ℤ²` (p. 7 and p. 15). -/
def box (n : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n

end PottsContinuity

namespace PottsContinuity

/-- The square lattice `ℤ²`: vertex set `ℤ²`, edges between nearest neighbours (p. 14, §2.1). -/
def squareLattice : SimpleGraph (ℤ × ℤ) where
  Adj x y := |x.1 - y.1| + |x.2 - y.2| = 1
  symm := ⟨fun x y h => by rwa [abs_sub_comm y.1, abs_sub_comm y.2]⟩
  loopless := ⟨fun x h => by simp at h⟩

end PottsContinuity

namespace PottsContinuity

/-- The open subgraph of a configuration `ω ∈ {0,1}^{E_G}` on the subgraph `G = (V, E_G)` of `ℤ²`
induced by `V`: vertex set `V`, edge set `{e ∈ E_G : ω(e) = 1}` (p. 5 and p. 15). -/
def rcOpenGraph (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    SimpleGraph (V : Set (ℤ × ℤ)) :=
  SimpleGraph.fromEdgeSet
    {e | ∃ h : e ∈ (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet, ω ⟨e, h⟩ = true}

end PottsContinuity

namespace PottsContinuity

/-- `C_h([a,b] × [c,d])` for a configuration `ω` on the subgraph induced by `V`: there is an open
path, all of whose vertices lie in `[a,b] × [c,d]`, from `{a} × [c,d]` to `{b} × [c,d]`
(pp. 7 and 17).  An open path is a walk along open edges of `ω`; as on p. 15, paths need not be
self-avoiding.  The event is meant for rectangles `[a,b] × [c,d]` contained in `V`. -/
def horizontalCrossing (V : Finset (ℤ × ℤ)) (a b c d : ℤ)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : Prop :=
  ∃ (x y : (V : Set (ℤ × ℤ))) (w : (rcOpenGraph V ω).Walk x y),
    x.1 ∈ ({a} : Set ℤ) ×ˢ Set.Icc c d ∧ y.1 ∈ ({b} : Set ℤ) ×ˢ Set.Icc c d ∧
      ∀ v ∈ w.support, v.1 ∈ Set.Icc a b ×ˢ Set.Icc c d

end PottsContinuity

namespace PottsContinuity

open Classical in
/-- The nearest-neighbour edges `{x, y}` of `ℤ²` with `{x, y} ∩ V ≠ ∅` (the edges of the Hamiltonian
`H^τ_G`, p. 4), as unordered pairs. -/
noncomputable def pottsEdges (V : Finset (ℤ × ℤ)) : Finset (Sym2 (ℤ × ℤ)) :=
  V.biUnion fun x =>
    (({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ))).image fun d => s(x, x + d)

end PottsContinuity

namespace PottsContinuity

open Classical in
/-- `-H^τ_G(σ) = Σ_{x∼y, {x,y}∩V_G≠∅} δ_{σ_x,σ_y}`: the number of edges of `pottsEdges V` whose two
endpoints carry the same spin (p. 4). -/
noncomputable def pottsAgreeCount {q : ℕ} (V : Finset (ℤ × ℤ)) (σ : ℤ × ℤ → Fin q) : ℕ :=
  ((pottsEdges V).filter fun e => ∀ x ∈ e, ∀ y ∈ e, σ x = σ y).card

end PottsContinuity

namespace PottsContinuity

/-- The spin configuration on `ℤ²` equal to `σ` on the finite vertex set `V` and to the constant
colour `i` outside `V` (monochromatic boundary condition `(i)`, p. 4). -/
def pottsExtend {q : ℕ} (V : Finset (ℤ × ℤ)) (i : Fin q) (σ : V → Fin q) : ℤ × ℤ → Fin q :=
  fun x => if h : x ∈ V then σ ⟨x, h⟩ else i

end PottsContinuity

namespace PottsContinuity

/-- The Boltzmann weight `e^{-β H^{(i)}_G(σ)}` of a configuration agreeing with `(i)` off `V` (p. 4). -/
noncomputable def pottsWeight {q : ℕ} (V : Finset (ℤ × ℤ)) (β : ℝ) (i : Fin q) (σ : V → Fin q) : ℝ :=
  Real.exp (β * (pottsAgreeCount V (pottsExtend V i σ) : ℝ))

end PottsContinuity

namespace PottsContinuity

/-- The finite-volume Gibbs measure `μ^{(i)}_{G,β}[σ] = e^{-βH}/Z^{(i)}_{G,β}` (p. 4). -/
noncomputable def pottsProb {q : ℕ} (V : Finset (ℤ × ℤ)) (β : ℝ) (i : Fin q) (σ : V → Fin q) : ℝ :=
  pottsWeight V β i σ / ∑ σ', pottsWeight V β i σ'

end PottsContinuity

namespace PottsContinuity

open Classical in
/-- `μ^{(i)}_{G,β}[E]` for an event `E ⊆ {1,…,q}^{ℤ²}`; configurations not equal to `(i)` off `V`
have probability `0` (p. 4). -/
noncomputable def pottsEventProb {q : ℕ} (V : Finset (ℤ × ℤ)) (β : ℝ) (i : Fin q)
    (E : (ℤ × ℤ → Fin q) → Prop) : ℝ :=
  ∑ σ, if E (pottsExtend V i σ) then pottsProb V β i σ else 0

end PottsContinuity

namespace PottsContinuity

/-- `μ` is the infinite-volume Gibbs measure `μ^{(i)}_{ℤ²,β}` with monochromatic boundary
conditions `i`: the limit of `μ^{(i)}_{G,β}` as `G ↗ ℤ²` (p. 4), along every increasing sequence of
finite vertex sets exhausting `ℤ²`, tested on every finite-dimensional cylinder event. -/
def IsPottsInfiniteVolumeLimit (q : ℕ) (β : ℝ) (i : Fin q) (μ : Measure (ℤ × ℤ → Fin q)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ G : ℕ → Finset (ℤ × ℤ), Monotone G → (∀ x : ℤ × ℤ, ∃ n, x ∈ G n) →
      ∀ (A : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q),
        Tendsto (fun n : ℕ => pottsEventProb (G n) β i fun σ => ∀ x ∈ A, σ x = ξ x)
          atTop (𝓝 (μ.real {σ | ∀ x ∈ A, σ x = ξ x}))

end PottsContinuity

namespace PottsContinuity

/-- `βc` is the critical inverse temperature `β_c(q) ∈ (0, ∞)` of the `q`-state Potts model (p. 4):
for every `β ≥ 0` and every colour `i`, `μ^{(i)}_{ℤ²,β}` exists and
`μ^{(i)}_{ℤ²,β}[σ₀ = i] = 1/q` if `β < βc`, `μ^{(i)}_{ℤ²,β}[σ₀ = i] > 1/q` if `β > βc`. -/
def IsPottsCriticalPoint (q : ℕ) (βc : ℝ) : Prop :=
  0 < βc ∧
    ∀ (β : Set.Ici (0 : ℝ)) (i : Fin q), ∃ μ : Measure (ℤ × ℤ → Fin q),
      IsPottsInfiniteVolumeLimit q β i μ ∧
      ((β : ℝ) < βc → μ.real {σ | σ (0, 0) = i} = 1 / (q : ℝ)) ∧
      (βc < β → 1 / (q : ℝ) < μ.real {σ | σ (0, 0) = i})

end PottsContinuity

namespace PottsContinuity

/-- `k₀(ω)`: the number of connected components of the graph `ω` (isolated vertices included). -/
noncomputable def rcFreeClusterCount (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℕ :=
  Nat.card (rcOpenGraph V ω).ConnectedComponent

end PottsContinuity

namespace PottsContinuity

/-- The vertex boundary `∂G` of the subgraph `G` of `ℤ²` induced by the finite vertex set `V`:
the vertices of `G` with strictly fewer than four neighbours in `G` (p. 6 and p. 15). -/
def vertexBoundary (V : Finset (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  {x | x ∈ V ∧ {y | y ∈ V ∧ squareLattice.Adj x y}.ncard < 4}

end PottsContinuity

namespace PottsContinuity

open Classical in
/-- `k₁(ω)`: the number of connected components of `ω`, except that all the connected components
of vertices in `∂G` are counted as one component (p. 6). -/
noncomputable def rcWiredClusterCount (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℕ :=
  Nat.card {c : (rcOpenGraph V ω).ConnectedComponent //
      ∀ x : (V : Set (ℤ × ℤ)), (rcOpenGraph V ω).connectedComponentMk x = c →
        x.1 ∉ vertexBoundary V} +
    if ∃ c : (rcOpenGraph V ω).ConnectedComponent,
        ∃ x : (V : Set (ℤ × ℤ)), (rcOpenGraph V ω).connectedComponentMk x = c ∧
          x.1 ∈ vertexBoundary V then 1 else 0

end PottsContinuity

namespace PottsContinuity

/-- The unnormalised weight `p^{o(ω)} (1-p)^{c(ω)} q^{kᵢ(ω)}`, with `i = 0` free and `i = 1`
wired (p. 6). -/
noncomputable def rcWeight (V : Finset (ℤ × ℤ)) (p q : ℝ) (i : Fin 2)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℝ :=
  p ^ Nat.card {e // ω e = true} * (1 - p) ^ Nat.card {e // ω e = false} *
    q ^ (if i = 0 then rcFreeClusterCount V ω else rcWiredClusterCount V ω)

end PottsContinuity

namespace PottsContinuity

open Classical in
/-- The finite-volume random-cluster measure `φⁱ_{G,p,q}[ω] = weight / Zⁱ_{G,p,q}` on the subgraph
`G` of `ℤ²` induced by `V`, for the source range `p ∈ [0, 1]`, `q > 0` (pp. 5–6). -/
noncomputable def rcProb (V : Finset (ℤ × ℤ)) (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (i : Fin 2) (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℝ :=
  rcWeight V p q i ω / ∑ ω', rcWeight V p q i ω'

end PottsContinuity

namespace PottsContinuity

open Classical in
/-- `φⁱ_{G,p,q}[E]`: the finite-volume probability of an event `E ⊆ {0,1}^{E_G}`. -/
noncomputable def rcEventProb (V : Finset (ℤ × ℤ)) (p : Set.Icc (0 : ℝ) 1)
    (q : Set.Ioi (0 : ℝ)) (i : Fin 2)
    (E : ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) → Prop) : ℝ :=
  ∑ ω, if E ω then rcProb V p q i ω else 0

end PottsContinuity

namespace PottsContinuity

/-- `μ` is the infinite-volume random-cluster measure `φⁱ_{ℤ²,p,q}`: the probability measure on
`{0,1}^{E(ℤ²)}` that is the limit of `φⁱ_{G,p,q}` for `G ↗ ℤ²` (p. 6).  Here `G` runs along every
increasing sequence of finite induced subgraphs exhausting `ℤ²` (this implies the box statement
`φⁱ_{Λₙ,p,q} → φⁱ_{ℤ²,p,q}` of p. 16), and convergence of measures is tested on every
finite-dimensional cylinder event. -/
def IsRCInfiniteVolumeLimit (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (i : Fin 2)
    (μ : Measure (squareLattice.edgeSet → Bool)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ G : ℕ → Finset (ℤ × ℤ), Monotone G → (∀ x : ℤ × ℤ, ∃ n, x ∈ G n) →
      ∀ (A : Finset squareLattice.edgeSet) (ξ : squareLattice.edgeSet → Bool),
        Tendsto
          (fun n : ℕ => rcEventProb (G n) p q i fun ω =>
            ∀ e ∈ A, ∃ f : (squareLattice.induce (G n : Set (ℤ × ℤ))).edgeSet,
              Sym2.map Subtype.val f.1 = e.1 ∧ ω f = ξ e)
          atTop (𝓝 (μ.real {ω | ∀ e ∈ A, ω e = ξ e}))

end PottsContinuity

namespace PottsContinuity

/-- The open subgraph of `ℤ²` of an infinite-volume configuration `ω ∈ {0,1}^{E(ℤ²)}`. -/
def rcInfiniteOpenGraph (ω : squareLattice.edgeSet → Bool) : SimpleGraph (ℤ × ℤ) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ squareLattice.edgeSet, ω ⟨e, h⟩ = true}

end PottsContinuity

namespace PottsContinuity

/-- `pc` is the critical parameter `p_c(q)` of the random-cluster model with `q ≥ 1` (p. 6):
`pc ∈ (0, 1)` and, for every `p ∈ [0, 1]`, the wired infinite-volume measure `φ¹_{ℤ²,p,q}` exists
and satisfies `φ¹_{ℤ²,p,q}[0 ⟷ ∞] = 0` if `p < pc` and `φ¹_{ℤ²,p,q}[0 ⟷ ∞] > 0` if `p > pc`. -/
def IsRCCriticalPoint (q : Set.Ici (1 : ℝ)) (pc : ℝ) : Prop :=
  pc ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∀ p : Set.Icc (0 : ℝ) 1, ∃ μ : Measure (squareLattice.edgeSet → Bool),
      IsRCInfiniteVolumeLimit p ⟨q, Set.mem_Ioi.2 (lt_of_lt_of_le one_pos q.2)⟩ 1 μ ∧
      ((p : ℝ) < pc →
        μ {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} = 0) ∧
      (pc < p →
        0 < μ {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite})

end PottsContinuity

namespace PottsContinuity

/-- The lattice rectangle `[a, b] × [c, d] ∩ ℤ²` (integer corners). -/
def latticeRectangle (a b c d : ℤ) : Finset (ℤ × ℤ) :=
  Finset.Icc a b ×ˢ Finset.Icc c d

end PottsContinuity
