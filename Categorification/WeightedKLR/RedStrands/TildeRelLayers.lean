/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TildePhiLayers

/-!
# Layers of `T̃^λ e(s)` along a refinement of Webster's order

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Corollary 5.23, in the form used for the stratum peeling: the filtration of `P̃ = T̃^λ e(s)` may
be taken along any relation `≺` on the block assignments of `s` that contains Webster's order
`PhiLT` (for example a linear extension of it). Put `P̃_{≻φ} = Σ_{φ ≺ φ'} T̃^λ x̃_{φ'}` and
`P̃_{⪰φ} = T̃^λ x̃_φ + P̃_{≻φ}`. Since `P̃_{>φ} ⊆ P̃_{≻φ}`, the class `[x̃_φ]` is still killed by
`e(t) T̃^λ` for `t` above `φ • s`, and `S̃_{φ • s} → P̃_{⪰φ}/P̃_{≻φ}` is a surjection
(`tildeRelLayerMap_surjective`).

## Main definitions

* `tildeRelAbove`, `tildeRelAtLeast`, `tildeRelLayer`, `tildeRelLayerGen`, `tildeRelLayerMap`.

## Main results

* `tildeRelLayerGen_annihilated`, `tildeRelLayerMap_surjective`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR TypeA Equiv

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "B" => StendhalAlgebra k Q Λ ν

/-- A shortcut: instance search does not unfold `StendhalAlgebra` to find the additive group of
a submodule of a left ideal. -/
private abbrev addCommGroupSubmoduleLIdeal' (x : B) (M : Submodule B (lIdeal x)) :
    AddCommGroup M :=
  Submodule.addCommGroup (R := B) M

attribute [local instance] addCommGroupSubmoduleLIdeal'

/-- `P̃_{≻φ}`: the sum of the `T̃^λ x̃_{φ'}` with `φ ≺ φ'`. -/
abbrev tildeRelAbove (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (rel : PhiIndex s → PhiIndex s → Prop) (g : PhiIndex s) :
    Submodule B (lIdeal (StendhalAlgebra.e s hs : B)) :=
  Submodule.above rel (tildePhiSub Q Λ ρ hs) g

/-- `P̃_{⪰φ} = T̃^λ x̃_φ + P̃_{≻φ}`. -/
abbrev tildeRelAtLeast (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (rel : PhiIndex s → PhiIndex s → Prop) (g : PhiIndex s) :
    Submodule B (lIdeal (StendhalAlgebra.e s hs : B)) :=
  tildePhiSub Q Λ ρ hs g ⊔ tildeRelAbove Q Λ ρ hs rel g

/-- The layer `P̃_{⪰φ}/P̃_{≻φ}`. -/
abbrev tildeRelLayer (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (rel : PhiIndex s → PhiIndex s → Prop) (g : PhiIndex s) : Type :=
  tildeRelAtLeast Q Λ ρ hs rel g ⧸
    (tildeRelAbove Q Λ ρ hs rel g).comap (tildeRelAtLeast Q Λ ρ hs rel g).subtype

/-- The class `[x̃_φ]` in the layer. -/
def tildeRelLayerGen (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (rel : PhiIndex s → PhiIndex s → Prop) (g : PhiIndex s) : tildeRelLayer Q Λ ρ hs rel g :=
  Submodule.Quotient.mk
    ⟨tildePhiVec Q Λ ρ hs g, Submodule.mem_sup_left (Submodule.subset_span rfl)⟩

variable {Q Λ}

private theorem stendhalLT_of_lt_of_le'' {a b c : Seq μ} (hab : StendhalLT a b)
    (hbc : StendhalLE b c) : StendhalLT a c :=
  ⟨fun r i => (hab.1 r i).trans (hbc r i), fun hca => hab.2 fun r i => (hbc r i).trans (hca r i)⟩

/-- `[x̃_φ]` is killed by `e(t) T̃^λ` for `t` strictly above `φ • s`, along any `≺` containing
Webster's order. -/
theorem tildeRelLayerGen_annihilated (ρ : Perm (Fin m) → List ℕ) {s : Seq μ}
    (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    {rel : PhiIndex s → PhiIndex s → Prop} (hrel : ∀ a b, PhiLT a b → rel a b) (g : PhiIndex s)
    (t : Seq μ) (ht : IsRedOrdered t) (a : B) (hlt : StendhalLT (phiBottom s g.1) t) :
    (StendhalAlgebra.e t ht * a) • tildeRelLayerGen Q Λ ρ hs rel g = 0 := by
  rw [tildeRelLayerGen, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  change (StendhalAlgebra.e t ht * a) • tildePhiVec Q Λ ρ hs g ∈ tildeRelAbove Q Λ ρ hs rel g
  have h := mem_iSup_tildePhiSub_of_e ρ hs hρ ht
    ((StendhalAlgebra.e t ht * a) • tildePhiVec Q Λ ρ hs g) (by
      change StendhalAlgebra.e t ht * (StendhalAlgebra.e t ht * a * tildePhiElt Q Λ ρ hs g.mem) =
        StendhalAlgebra.e t ht * a * tildePhiElt Q Λ ρ hs g.mem
      rw [← mul_assoc, ← mul_assoc, stendhalAlgebra_e_mul_e_self])
  refine (iSup₂_le (fun g' hle => ?_) : _ ≤ tildeRelAbove Q Λ ρ hs rel g) h
  exact le_iSup₂_of_le (f := fun g' (_ : rel g g') => tildePhiSub Q Λ ρ hs g') g'
    (hrel _ _ (stendhalLT_of_lt_of_le'' hlt hle)) le_rfl

variable (Q Λ) in
/-- **The map `S̃_{φ • s} → P̃_{⪰φ}/P̃_{≻φ}`**, `[y] ↦ y [x̃_φ]`. -/
def tildeRelLayerMap (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    {rel : PhiIndex s → PhiIndex s → Prop} (hrel : ∀ a b, PhiLT a b → rel a b)
    (g : PhiIndex s) :
    tildeStandard Q Λ (phiBottom s g.1) (g.isRedOrdered hs) →ₗ[B]
      tildeRelLayer Q Λ ρ hs rel g :=
  ((tildeLeftUpper Q Λ ν (phiBottom s g.1) (g.isRedOrdered hs)).comap
    (lIdeal (StendhalAlgebra.e (phiBottom s g.1) (g.isRedOrdered hs) : B)).subtype).liftQ
    ((LinearMap.toSpanSingleton B _ (tildeRelLayerGen Q Λ ρ hs rel g)).comp
      (lIdeal (StendhalAlgebra.e (phiBottom s g.1) (g.isRedOrdered hs) : B)).subtype)
    fun _ hy => tildeLeftUpper_smul_eq_zero _ _ _
      (fun t ht a hlt => tildeRelLayerGen_annihilated ρ hs hρ hrel g t ht a hlt) hy

theorem tildeRelLayerMap_mk (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    {rel : PhiIndex s → PhiIndex s → Prop} (hrel : ∀ a b, PhiLT a b → rel a b)
    (g : PhiIndex s)
    (y : lIdeal (StendhalAlgebra.e (phiBottom s g.1) (g.isRedOrdered hs) : B)) :
    tildeRelLayerMap Q Λ ρ hs hρ hrel g (Submodule.Quotient.mk y) =
      (y : B) • tildeRelLayerGen Q Λ ρ hs rel g :=
  rfl

/-- `S̃_{φ • s} → P̃_{⪰φ}/P̃_{≻φ}` is surjective. -/
theorem tildeRelLayerMap_surjective (ρ : Perm (Fin m) → List ℕ) {s : Seq μ}
    (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    {rel : PhiIndex s → PhiIndex s → Prop} (hrel : ∀ a b, PhiLT a b → rel a b)
    (g : PhiIndex s) :
    Function.Surjective (tildeRelLayerMap Q Λ ρ hs hρ hrel g) := by
  intro v
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨n, hn, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hn
  set eb : B := StendhalAlgebra.e (phiBottom s g.1) (g.isRedOrdered hs)
  refine ⟨Submodule.Quotient.mk ⟨c * eb, by
    change c * eb * eb = c * eb
    rw [mul_assoc, stendhalAlgebra_e_mul_e_self]⟩, ?_⟩
  rw [tildeRelLayerMap_mk, tildeRelLayerGen, ← Submodule.Quotient.mk_smul, eq_comm,
    Submodule.Quotient.eq]
  have hev : (c * eb) • tildePhiVec Q Λ ρ hs g = c • tildePhiVec Q Λ ρ hs g := by
    apply Subtype.ext
    change c * eb * tildePhiElt Q Λ ρ hs g.mem = c * tildePhiElt Q Λ ρ hs g.mem
    rw [mul_assoc, e_mul_tildePhiElt]
  change (⟨c • tildePhiVec Q Λ ρ hs g + b, hy⟩ - (c * eb) • ⟨tildePhiVec Q Λ ρ hs g, _⟩ :
    tildeRelAtLeast Q Λ ρ hs rel g) ∈ _
  rw [Submodule.mem_comap]
  convert hb using 1
  change c • tildePhiVec Q Λ ρ hs g + b - (c * eb) • tildePhiVec Q Λ ρ hs g = b
  rw [hev]
  abel

end Categorification.Stendhal
