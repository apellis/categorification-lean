/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Weighted graphs, loadings and chambers

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.1.

A *weighted graph* has a set of colours `I`, a finite set of oriented edges `e : t(e) → h(e)`,
a weight `ϑ_e` for each edge and a polynomial `Q_e(u, v)`, with `u` the dot on the strand
coloured `h(e)` and `v` the dot on the strand coloured `t(e)`. A loop of weight `0` at `i`
(at most one, in the paper) is recorded separately by its polynomial `P_i`, with
`Q = (u - v) P_i`; edges themselves are never loops of weight `0` (`WeightedGraph.NoZeroLoops`).

A *loading* places strands at points of a line, the ghost of a strand coloured `h(e)` sitting
`ϑ_e` to its right. A strand coloured `t(e)` *interacts* with the ghosts for `e`. Positions and
weights take values in a linearly ordered field `𝕜` (the paper uses `ℝ`); only the relative
order of finitely many points matters.

## Encoding

Strands are indexed by their colour and their rank among the strands of that colour
(`Strand ν`), so a configuration is a map `Strand ν → 𝕜`, increasing on each colour.
For an edge `e`, a strand `a` coloured `h(e)` and a strand `b ≠ a` coloured `t(e)` there is a
*wall* `x_b - x_a = ϑ_e`: strand `b` meets the ghost of `a`. A configuration is generic when it
lies on no wall (the genericity of the paper's Definition of a loading, for interacting pairs).
Its *chamber* records on which side of each wall it lies. Two loadings lie in the same chamber
exactly when they are equivalent in the sense of the paper's Definition `def:equivalent`; these
chambers are the objects of the weighted KLR algebra in this library.

## Main definitions

* `WeightedGraph`, `WeightedGraph.NoZeroLoops`, `WeightedGraph.Dagger` (assumption (†)).
* `Strand`, `Wall`, `Wall.val`, `IsAdmissible`, `Loading`.
* `Chamber`, `Loading.chamber`, `Chamber.Adjacent` (adjacent across one wall),
  `Chamber.DiagAdj` (the two strands of a colour and consecutive ranks can be brought
  together without crossing a wall).
-/

namespace Categorification.WeightedKLR

open Finsupp

/-- A weighted graph: colours `I`, edges `e : tail e → head e` with weight `ϑ_e ∈ 𝕜` and
polynomial `Q_e(u, v)` (`u` the dot on the `head e` strand, `v` on the `tail e` strand), and
for each colour `i` the polynomial `P_i` of a loop of weight `0` at `i`, if there is one. -/
structure WeightedGraph (I : Type*) (𝕜 : Type*) (k : Type*) [CommRing k] where
  /-- The edges. -/
  E : Type
  [fintypeE : Fintype E]
  [decEqE : DecidableEq E]
  /-- The tail of an edge. -/
  tail : E → I
  /-- The head of an edge. -/
  head : E → I
  /-- The weight `ϑ_e`. -/
  weight : E → 𝕜
  /-- The polynomial `Q_e(u, v)`. -/
  Q : E → MvPolynomial (Fin 2) k
  /-- The polynomial `P_i` of the loop of weight `0` at `i` (`Q = (u - v) P_i`), or `none` if
  there is no such loop. -/
  loop : I → Option (MvPolynomial (Fin 2) k)

attribute [instance] WeightedGraph.fintypeE WeightedGraph.decEqE

namespace WeightedGraph

variable {I 𝕜 k : Type*} [CommRing k] (Γ : WeightedGraph I 𝕜 k)

/-- No edge is a loop of weight `0` (those are recorded by `P`). -/
def NoZeroLoops [Zero 𝕜] : Prop :=
  ∀ e, Γ.head e = Γ.tail e → Γ.weight e ≠ 0

/-- Assumption (†) of the paper: no two edges with the same tail, head and weight, and no
cyclically oriented bigon whose two weights are opposite. Under (†) distinct walls are distinct
hyperplanes. -/
def Dagger [Neg 𝕜] : Prop :=
  (∀ e e', Γ.tail e = Γ.tail e' → Γ.head e = Γ.head e' → Γ.weight e = Γ.weight e' → e = e') ∧
    ∀ e e', Γ.tail e = Γ.head e' → Γ.head e = Γ.tail e' → Γ.weight e' ≠ -Γ.weight e

/-- Each loop polynomial `P_i` is symmetric. -/
def PSymm : Prop :=
  ∀ i P, Γ.loop i = some P → MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P = P

end WeightedGraph

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {k : Type*} [CommRing k]

/-- The strands of a loading of weight `ν`: a colour `i` and a rank `m < ν i`. -/
abbrev Strand (ν : I →₀ ℕ) : Type _ := (i : ν.support) × Fin (ν i)

namespace Strand

variable {ν : I →₀ ℕ}

/-- The colour of a strand. -/
def label (s : Strand ν) : I := s.1

end Strand

variable (Γ : WeightedGraph I 𝕜 k) (ν : I →₀ ℕ)

/-- A wall: an edge `e`, a strand `a` coloured `head e` and a strand `b ≠ a` coloured `tail e`.
It is the hyperplane `x_b - x_a = ϑ_e` where `b` meets the ghost of `a`. -/
def Wall : Type _ :=
  {w : Γ.E × Strand ν × Strand ν //
    w.2.1.label = Γ.head w.1 ∧ w.2.2.label = Γ.tail w.1 ∧ w.2.1 ≠ w.2.2}

instance : Fintype (Wall Γ ν) := by unfold Wall; infer_instance
instance : DecidableEq (Wall Γ ν) := by unfold Wall; infer_instance

variable {Γ ν}

namespace Wall

/-- The edge of a wall. -/
def edge (w : Wall Γ ν) : Γ.E := w.1.1
/-- The strand whose ghost is met (coloured `head`). -/
def src (w : Wall Γ ν) : Strand ν := w.1.2.1
/-- The strand meeting the ghost (coloured `tail`). -/
def tgt (w : Wall Γ ν) : Strand ν := w.1.2.2

/-- The value of the wall equation at a configuration: `x_b - x_a - ϑ_e`. It is negative when
strand `b` is to the left of the ghost of `a`. -/
def val (w : Wall Γ ν) (p : Strand ν → 𝕜) : 𝕜 := p w.tgt - p w.src - Γ.weight w.edge

end Wall

variable (Γ) in
/-- An admissible configuration: injective, increasing on the strands of each colour, and
generic (on no wall). -/
def IsAdmissible (p : Strand ν → 𝕜) : Prop :=
  Function.Injective p ∧ (∀ s t : Strand ν, s.1 = t.1 → s.2.val < t.2.val → p s < p t) ∧
    ∀ w : Wall Γ ν, w.val p ≠ 0

variable (Γ ν) in
/-- A generic loading of weight `ν`. -/
structure Loading where
  /-- The positions of the strands. -/
  pos : Strand ν → 𝕜
  admissible : IsAdmissible Γ pos

/-- The side of each wall on which a configuration lies (`true`: strand `b` to the right of
the ghost of `a`). -/
def signs (p : Strand ν → 𝕜) : Wall Γ ν → Bool := fun w => decide (0 < w.val p)

variable (Γ ν) in
/-- A chamber: the sign vector of some admissible configuration. -/
def Chamber : Type _ :=
  {σ : Wall Γ ν → Bool // ∃ p, IsAdmissible Γ p ∧ signs p = σ}

instance : DecidableEq (Chamber Γ ν) := by unfold Chamber; infer_instance
instance : Finite (Chamber Γ ν) := by unfold Chamber; infer_instance
noncomputable instance : Fintype (Chamber Γ ν) := Fintype.ofFinite _

/-- The chamber of a loading. -/
def Loading.chamber (B : Loading Γ ν) : Chamber Γ ν := ⟨signs B.pos, B.pos, B.admissible, rfl⟩

/-- Two loadings are equivalent (the paper's Definition `def:equivalent`) when every strand
lies on the same side of every interacting ghost in both. -/
def Loading.Equiv (B B' : Loading Γ ν) : Prop := ∀ w : Wall Γ ν, (0 < w.val B.pos ↔ 0 < w.val B'.pos)

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Loading.chamber_eq_iff (B B' : Loading Γ ν) : B.chamber = B'.chamber ↔ B.Equiv B' := by
  constructor
  · intro h w
    have := congrArg (fun c : Chamber Γ ν => c.1 w) h
    simpa [Loading.chamber, signs] using this
  · intro h
    apply Subtype.ext
    funext w
    simp [Loading.chamber, signs, h w]

namespace Chamber

/-- `c'` is obtained from `c` by crossing the single wall `w`. -/
def Adjacent (c c' : Chamber Γ ν) (w : Wall Γ ν) : Prop :=
  c.1 w ≠ c'.1 w ∧ ∀ w', w' ≠ w → c.1 w' = c'.1 w'

/-- The configuration obtained by moving strands `s` and `s'` to their midpoint. -/
def mid (p : Strand ν → 𝕜) (s s' : Strand ν) : Strand ν → 𝕜 :=
  fun t => if t = s ∨ t = s' then (p s + p s') / 2 else p t

/-- The strands `s` and `s'` (same colour, consecutive ranks) can cross in chamber `c`: some
configuration of `c` can be moved to the configuration where they meet without crossing a
wall (every wall keeps its strict sign at the meeting point). -/
def DiagAdj (c : Chamber Γ ν) (s s' : Strand ν) : Prop :=
  s.1 = s'.1 ∧ s'.2.val = s.2.val + 1 ∧
    ∃ p, IsAdmissible Γ p ∧ signs p = c.1 ∧
      ∀ w : Wall Γ ν, (0 < w.val p ↔ 0 < w.val (mid p s s')) ∧ w.val (mid p s s') ≠ 0

end Chamber

end Categorification.WeightedKLR
