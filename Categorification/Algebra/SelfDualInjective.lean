/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.IdempotentEquiv
import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option backward.isDefEq.respectTransparency false

/-!
# Self-dual projectives are injective

Background for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v2, Theorem 5.27, implication (3) ⇒ (1): the projective `P⁰` is self-dual
through the pairing `(a, b) ↦ τ(a b)` for a nondegenerate trace `τ`, hence injective.

Let `A` be a `k`-algebra, `e ∈ A` idempotent and `τ : A → k` a `k`-linear functional. Suppose
that the pairing `e A × A e → k`, `(a, b) ↦ τ(a b)`, is nondegenerate on the left
(`∀ a ∈ e A, a ≠ 0 → ∃ b ∈ A e, τ(a b) ≠ 0`) and that `e A` and `A e` have the same finite
dimension. Then the pairing is perfect, and the left `A`-module `A e` satisfies Baer's
criterion, so it is injective (`Module.Baer.injective_lIdeal_of_pairing`).

The proof: a map `g : J → A e` on a left ideal `J` gives the functional `x ↦ τ(g x)` on
`J ∩ e A`; extend it to `e A` and represent it as `τ(· b₀)` with `b₀ ∈ A e`. For `j ∈ J` and
`a ∈ e A`, `τ(a j b₀) = τ(g(a j)) = τ(a g(j))`, so `j b₀ = g(j)` by nondegeneracy.
-/

noncomputable section

namespace Categorification

open Module

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- `e A = {a | e a = a}` as a `k`-subspace of `A`. -/
def leftCorner (e : A) : Submodule k A where
  carrier := {a | e * a = a}
  add_mem' {x y} hx hy := by simp only [Set.mem_ofPred_eq, mul_add] at *; rw [hx, hy]
  zero_mem' := mul_zero e
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Algebra.mul_smul_comm, hx]

/-- `A e = {b | b e = b}` as a `k`-subspace of `A`. -/
def rightCorner (e : A) : Submodule k A where
  carrier := {b | b * e = b}
  add_mem' {x y} hx hy := by simp only [Set.mem_ofPred_eq, add_mul] at *; rw [hx, hy]
  zero_mem' := zero_mul e
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Algebra.smul_mul_assoc, hx]

theorem mem_leftCorner {e a : A} : a ∈ leftCorner (k := k) e ↔ e * a = a := Iff.rfl

theorem mem_rightCorner {e b : A} : b ∈ rightCorner (k := k) e ↔ b * e = b := Iff.rfl

variable (τ : A →ₗ[k] k) (e : A)

/-- The pairing `e A → (A e)^*`, `a ↦ τ(a ·)`. -/
def cornerPairing : leftCorner (k := k) e →ₗ[k] Dual k (rightCorner (k := k) e) where
  toFun a :=
    { toFun := fun b => τ (a.1 * b.1)
      map_add' := fun b b' => by simp [mul_add]
      map_smul' := fun c b => by simp [Algebra.mul_smul_comm] }
  map_add' a a' := by ext b; simp [add_mul]
  map_smul' c a := by ext b; simp [Algebra.smul_mul_assoc]

variable {τ e}

/-- If the pairing is nondegenerate on the left and the two corners have the same finite
dimension, every functional on `e A` is `τ(· b)` for some `b ∈ A e`, and `b` is unique. -/
theorem bijective_cornerPairing_dual [FiniteDimensional k A]
    (hnd : ∀ a, e * a = a → a ≠ 0 → ∃ b, b * e = b ∧ τ (a * b) ≠ 0)
    (hdim : finrank k (leftCorner (k := k) e) = finrank k (rightCorner (k := k) e)) :
    Function.Bijective
      ((cornerPairing τ e).dualMap ∘ₗ (evalEquiv k (rightCorner (k := k) e)).toLinearMap) := by
  have hinj : Function.Injective (cornerPairing τ e) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    by_contra h0
    obtain ⟨b, hb, hτ⟩ := hnd a.1 a.2 (fun h => h0 (Subtype.ext h))
    exact hτ (LinearMap.congr_fun (LinearMap.mem_ker.mp ha) ⟨b, hb⟩)
  have hbij : Function.Bijective (cornerPairing τ e) := by
    refine ⟨hinj, ?_⟩
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hinj, Subspace.dual_finrank_eq, hdim]
  let E := LinearEquiv.ofBijective (cornerPairing τ e) hbij
  have : (cornerPairing τ e).dualMap = E.dualMap.toLinearMap := rfl
  rw [this]
  exact (E.dualMap.toEquiv.bijective).comp (evalEquiv k _).bijective

theorem cornerPairing_dual_apply [FiniteDimensional k A] (b : rightCorner (k := k) e) (a : leftCorner (k := k) e) :
    ((cornerPairing τ e).dualMap ∘ₗ (evalEquiv k (rightCorner (k := k) e)).toLinearMap) b a =
      τ (a.1 * b.1) := rfl

/-- An anti-involution fixing `e` exchanges the two corners `e A` and `A e`, so they have the same
dimension. -/
theorem finrank_leftCorner_eq_rightCorner (σ : A ≃ₗ[k] A)
    (hmul : ∀ x y, σ (x * y) = σ y * σ x) (hinv : ∀ x, σ (σ x) = x) (he : σ e = e) :
    finrank k (leftCorner (k := k) e) = finrank k (rightCorner (k := k) e) := by
  have hmap : (leftCorner (k := k) e).map σ.toLinearMap = rightCorner (k := k) e := by
    ext b
    simp only [Submodule.mem_map, LinearEquiv.coe_coe, mem_leftCorner, mem_rightCorner]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [← he, ← hmul, ha]
    · intro hb
      refine ⟨σ b, ?_, hinv b⟩
      rw [← he, ← hmul, hb]
  rw [← hmap, LinearEquiv.finrank_map_eq]

/-- **Baer's criterion for a self-dual projective**: if `τ` pairs `e A` and `A e`
nondegenerately on the left and both have the same finite dimension, then `A e` is a Baer
`A`-module. -/
theorem Module.Baer.lIdeal_of_pairing [FiniteDimensional k A]
    (hnd : ∀ a, e * a = a → a ≠ 0 → ∃ b, b * e = b ∧ τ (a * b) ≠ 0)
    (hdim : finrank k (leftCorner (k := k) e) = finrank k (rightCorner (k := k) e)) :
    Module.Baer A (lIdeal e) := by
  have hbij := bijective_cornerPairing_dual hnd hdim
  -- uniqueness of the representing vector
  have huniq : ∀ c, c * e = c → (∀ a, e * a = a → τ (a * c) = 0) → c = 0 := by
    intro c hc h
    have : ((cornerPairing τ e).dualMap ∘ₗ (evalEquiv k (rightCorner (k := k) e)).toLinearMap)
        ⟨c, hc⟩ = 0 := by
      ext a; exact h a.1 a.2
    have h0 := hbij.1 (this.trans (map_zero _).symm)
    exact congrArg Subtype.val h0
  intro J g
  -- the subspace `J ∩ e A` of `e A` and the functional `x ↦ τ(g x)` on it
  let W : Submodule k (leftCorner (k := k) e) :=
    (J.restrictScalars k).comap (leftCorner (k := k) e).subtype
  let lam : W →ₗ[k] k :=
    { toFun := fun x => τ (g ⟨x.1.1, x.2⟩ : A)
      map_add' := fun x y => by
        rw [← map_add]; congr 2
        rw [show (⟨(x + y).1.1, (x + y).2⟩ : J) = ⟨x.1.1, x.2⟩ + ⟨y.1.1, y.2⟩ from rfl,
          map_add, Submodule.coe_add]
      map_smul' := fun c x => by
        have hx : (⟨(c • x).1.1, (c • x).2⟩ : J) = algebraMap k A c • ⟨x.1.1, x.2⟩ := by
          ext; simp [Algebra.smul_def]
        rw [hx, map_smul, Submodule.coe_smul, smul_eq_mul, ← Algebra.smul_def, map_smul]
        rfl }
  obtain ⟨Lam, hLam⟩ := LinearMap.exists_extend lam
  obtain ⟨⟨b₀, hb₀⟩, hrep⟩ := hbij.2 Lam
  refine ⟨LinearMap.toSpanSingleton A (lIdeal e) ⟨b₀, hb₀⟩, fun x hx => ?_⟩
  apply Subtype.ext
  simp only [LinearMap.toSpanSingleton_apply, Submodule.coe_smul, smul_eq_mul]
  have hgx : (g ⟨x, hx⟩ : A) * e = g ⟨x, hx⟩ := (g ⟨x, hx⟩).2
  rw [← sub_eq_zero]
  refine huniq _ (by rw [sub_mul, mul_assoc, hb₀, hgx]) fun a ha => ?_
  have hax : a * x ∈ J := J.smul_mem a hx
  have h1 : τ (a * x * b₀) = τ (g ⟨a * x, hax⟩ : A) := by
    have := LinearMap.congr_fun hrep ⟨a * x, by rw [mem_leftCorner, ← mul_assoc, ha]⟩
    rw [cornerPairing_dual_apply] at this
    rw [this]
    exact LinearMap.congr_fun hLam ⟨⟨a * x, by rw [mem_leftCorner, ← mul_assoc, ha]⟩, hax⟩
  have h2 : (g ⟨a * x, hax⟩ : A) = a * g ⟨x, hx⟩ := by
    rw [show (⟨a * x, hax⟩ : J) = a • ⟨x, hx⟩ from rfl, map_smul]; rfl
  rw [mul_sub, map_sub, ← mul_assoc, h1, h2, sub_self]

/-- **A self-dual projective is injective**: under the hypotheses of
`Module.Baer.lIdeal_of_pairing`, `A e` is an injective `A`-module. -/
theorem injective_lIdeal_of_pairing [FiniteDimensional k A]
    (hnd : ∀ a, e * a = a → a ≠ 0 → ∃ b, b * e = b ∧ τ (a * b) ≠ 0)
    (hdim : finrank k (leftCorner (k := k) e) = finrank k (rightCorner (k := k) e)) :
    Module.Injective A (lIdeal e) :=
  (Module.Baer.lIdeal_of_pairing hnd hdim).injective

end Categorification
