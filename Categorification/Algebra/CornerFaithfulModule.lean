/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.SelfDualDoubleCentralizer
import Categorification.WeightedKLR.Induction.Generation

set_option backward.isDefEq.respectTransparency false

/-!
# Modules without nonzero submodules killed by a corner

Background for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Theorem 5.30, (2) ⇒ (3), and Corollary 5.32 (v2: Theorem 5.27 and
Corollary 5.29): no nonzero submodule of a standard module is killed by `e⁰`.

A left `A`-module `M` is *faithful on the corner* `e` (`IsCornerFaithfulModule e M`) when
`(e a) • m = 0` for every `a` forces `m = 0`, i.e. no nonzero submodule of `M` is killed by `e`.

* `IsCornerFaithfulModule.of_injective`: the property passes to submodules, also along a ring
  isomorphism (`IsCornerFaithfulModule.of_injective_ringEquiv`).
* `exists_injective_pi_lIdeal_of_isCornerFaithfulModule`: if `A` is finite-dimensional and a
  functional `τ` pairs `e A` and `A e` perfectly, a finite-dimensional module faithful on `e`
  embeds into a free module `Aᵈ` (in fact into a sum of copies of `A e`, the dual of `e A`).
* `IsCornerFaithfulModule.ind`: induction along `φ : A → B` carries such an embedding to `B`; if
  it preserves injections and `B` acts faithfully on the corner `e' B`, the induced module is
  faithful on `e'`.
-/

noncomputable section

namespace Categorification

open _root_.Module InductionAlong

/-- No nonzero submodule of the left `A`-module `M` is killed by `e`: `(e a) • m = 0` for every
`a` forces `m = 0`. -/
def IsCornerFaithfulModule {A : Type*} [Ring A] (e : A) (M : Type*) [AddCommGroup M]
    [Module A M] : Prop :=
  ∀ m : M, (∀ a : A, (e * a) • m = 0) → m = 0

theorem IsCornerFaithfulModule.of_injective {A : Type*} [Ring A] {e : A} {M M' : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] (f : M →ₗ[A] M')
    (hf : Function.Injective f) (h : IsCornerFaithfulModule e M') :
    IsCornerFaithfulModule e M := fun m hm =>
  hf (by rw [map_zero]; exact h _ fun a => by rw [← map_smul, hm a, map_zero])

/-- The property passes along an injective map that is semilinear for a ring isomorphism taking
`e` to `e'`. -/
theorem IsCornerFaithfulModule.of_injective_ringEquiv {A A' : Type*} [Ring A] [Ring A']
    (σ : A ≃+* A') {e : A} {e' : A'} (he : σ e = e') {M M' : Type*} [AddCommGroup M]
    [Module A M] [AddCommGroup M'] [Module A' M'] (f : M →+ M') (hf : Function.Injective f)
    (hσ : ∀ (a : A) (m : M), f (a • m) = σ a • f m) (h : IsCornerFaithfulModule e' M') :
    IsCornerFaithfulModule e M := fun m hm =>
  hf (by
    rw [map_zero]
    refine h _ fun a => ?_
    rw [← σ.apply_symm_apply a, ← he, ← map_mul, ← hσ, hm, map_zero])

section Embedding

variable {k A : Type*} [Field k] [Ring A] [Algebra k A] {τ : A →ₗ[k] k} {e : A}

/-- The element of `A e` representing a functional on `e A`. -/
private def repOf [FiniteDimensional k A]
    (hnd : ∀ a, e * a = a → a ≠ 0 → ∃ b, b * e = b ∧ τ (a * b) ≠ 0)
    (hdim : finrank k (leftCorner (k := k) e) = finrank k (rightCorner (k := k) e))
    (l : leftCorner (k := k) e →ₗ[k] k) : A :=
  (exists_rightCorner_rep hnd hdim l).choose

private theorem repOf_mul [FiniteDimensional k A]
    (hnd : ∀ a, e * a = a → a ≠ 0 → ∃ b, b * e = b ∧ τ (a * b) ≠ 0)
    (hdim : finrank k (leftCorner (k := k) e) = finrank k (rightCorner (k := k) e))
    (l : leftCorner (k := k) e →ₗ[k] k) : repOf hnd hdim l * e = repOf hnd hdim l :=
  (exists_rightCorner_rep hnd hdim l).choose_spec.1

private theorem repOf_spec [FiniteDimensional k A]
    (hnd : ∀ a, e * a = a → a ≠ 0 → ∃ b, b * e = b ∧ τ (a * b) ≠ 0)
    (hdim : finrank k (leftCorner (k := k) e) = finrank k (rightCorner (k := k) e))
    (l : leftCorner (k := k) e →ₗ[k] k) (a : A) (ha : e * a = a) :
    τ (a * repOf hnd hdim l) = l ⟨a, ha⟩ :=
  (exists_rightCorner_rep hnd hdim l).choose_spec.2 a ha

/-- Uniqueness of the representing element. -/
private theorem eq_repOf [FiniteDimensional k A]
    (hnd : ∀ a, e * a = a → a ≠ 0 → ∃ b, b * e = b ∧ τ (a * b) ≠ 0)
    (hdim : finrank k (leftCorner (k := k) e) = finrank k (rightCorner (k := k) e))
    (l : leftCorner (k := k) e →ₗ[k] k) {g : A} (hg : g * e = g)
    (hrep : ∀ a (ha : e * a = a), τ (a * g) = l ⟨a, ha⟩) : g = repOf hnd hdim l := by
  rw [← sub_eq_zero]
  refine eq_zero_of_rightCorner_pairing hnd hdim
    (by rw [sub_mul, hg, repOf_mul]) fun a ha => ?_
  rw [mul_sub, map_sub, hrep a ha, repOf_spec hnd hdim l a ha, sub_self]

variable {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

/-- The functional `a ↦ λ(a • m)` on `e A`. -/
private def evalCorner (lam : Dual k M) (m : M) : leftCorner (k := k) e →ₗ[k] k where
  toFun a := lam (a.1 • m)
  map_add' a a' := by simp [add_smul]
  map_smul' c a := by simp [smul_assoc]

/-- **Embedding into a free module.** If `A` is finite-dimensional, `τ` pairs `e A` and `A e`
perfectly and the finite-dimensional module `M` has no nonzero submodule killed by `e`, then `M`
embeds into `Aᵈ`. -/
theorem exists_injective_pi_lIdeal_of_isCornerFaithfulModule [FiniteDimensional k A]
    (hnd : ∀ a, e * a = a → a ≠ 0 → ∃ b, b * e = b ∧ τ (a * b) ≠ 0)
    (hdim : finrank k (leftCorner (k := k) e) = finrank k (rightCorner (k := k) e))
    (he : e * e = e) [FiniteDimensional k M] (h : IsCornerFaithfulModule e M) :
    ∃ (d : ℕ) (ι : M →ₗ[A] (Fin d → lIdeal (1 : A))), Function.Injective ι := by
  let b := Module.finBasis k M
  let ψ : Fin (finrank k M) → M →ₗ[A] lIdeal (1 : A) := fun j =>
    { toFun := fun m => ⟨repOf hnd hdim (evalCorner (b.coord j) m), by rw [mem_lIdeal, mul_one]⟩
      map_add' := fun m m' => Subtype.ext (by
        change repOf hnd hdim _ = repOf hnd hdim _ + repOf hnd hdim _
        refine (eq_repOf hnd hdim _ (by rw [add_mul, repOf_mul, repOf_mul]) fun a ha => ?_).symm
        rw [mul_add, map_add, repOf_spec hnd hdim _ a ha, repOf_spec hnd hdim _ a ha]
        simp [evalCorner, smul_add])
      map_smul' := fun c m => Subtype.ext (by
        change repOf hnd hdim _ = c * repOf hnd hdim _
        refine (eq_repOf hnd hdim _ (by rw [mul_assoc, repOf_mul]) fun a ha => ?_).symm
        rw [← mul_assoc, repOf_spec hnd hdim _ (a * c) (by rw [← mul_assoc, ha])]
        simp [evalCorner, mul_smul]) }
  refine ⟨finrank k M, LinearMap.pi ψ, fun m m' hmm => ?_⟩
  rw [← sub_eq_zero]
  refine h _ fun a => ?_
  have hx : e * (e * a) = e * a := by rw [← mul_assoc, he]
  refine b.ext_elem fun j => ?_
  have hj : repOf hnd hdim (evalCorner (b.coord j) (m - m')) = 0 := by
    have h1 := congrArg Subtype.val (congrFun hmm j)
    have h2 := congrArg Subtype.val (map_sub (ψ j) m m')
    change repOf hnd hdim _ = repOf hnd hdim _ at h1
    change repOf hnd hdim _ = repOf hnd hdim _ - repOf hnd hdim _ at h2
    rw [h2, h1, sub_self]
  have := repOf_spec hnd hdim (evalCorner (b.coord j) (m - m')) (e * a) hx
  rw [hj, mul_zero, map_zero] at this
  simpa [evalCorner] using this.symm

end Embedding

section Induction

universe u

variable {A : Type u} [Ring A] {B : Type u} [Ring B] (φ : A →ₙ+* B)

/-- An element of the induction of a finite product vanishes when all its components do. -/
private theorem ind_eq_zero_of_map_proj {N : Type u} [AddCommGroup N] [Module A N] {n : ℕ}
    (y : Ind (Fin n → N) φ)
    (h : ∀ j, Ind.map (LinearMap.proj (R := A) (φ := fun _ : Fin n => N) j) y = 0) : y = 0 := by
  have hid : ∀ x : Fin n → N,
      x = ∑ j, (LinearMap.single A (fun _ : Fin n => N) j).comp (LinearMap.proj j) x := by
    intro x
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hy : y = ∑ j, Ind.map (φ := φ)
      ((LinearMap.single A (fun _ : Fin n => N) j).comp (LinearMap.proj j)) y := by
    clear h
    induction y using Ind.induction_on with
    | zero => simp
    | tmul z x =>
      simp only [Ind.map_tmul]
      conv_lhs => rw [hid x]
      exact map_sum (AddMonoidHom.mk' (Ind.tmul (N := Fin n → N) (φ := φ) z)
        (Ind.tmul_add z)) _ _
    | add s t hs ht =>
      rw [Finset.sum_congr rfl fun j _ => map_add (Ind.map (φ := φ)
        ((LinearMap.single A (fun _ : Fin n => N) j).comp (LinearMap.proj j))) s t,
        Finset.sum_add_distrib, ← hs, ← ht]
  rw [hy]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Ind.map_comp, LinearMap.comp_apply, h j, map_zero]

/-- **Induction preserves faithfulness on corners**: if `M` embeds into `Aᵈ` by `ι`, induction
along `φ` keeps `ι` injective, and `B` acts faithfully on the corner `e' B` from the right, then
no nonzero submodule of `Ind M φ` is killed by `e'`. -/
theorem IsCornerFaithfulModule.ind {e' : B} (hfaith : ∀ y : B, (∀ b, e' * b * y = 0) → y = 0)
    {M : Type u} [AddCommGroup M] [Module A M] {d : ℕ} (ι : M →ₗ[A] (Fin d → lIdeal (1 : A)))
    (hι : Function.Injective (Ind.map (φ := φ) ι)) : IsCornerFaithfulModule e' (Ind M φ) := by
  intro y hy
  apply hι
  rw [map_zero]
  refine ind_eq_zero_of_map_proj φ _ fun j => ?_
  apply (indLIdealEquiv φ IsIdempotentElem.one).injective
  rw [map_zero]
  apply Subtype.ext
  refine hfaith _ fun b => ?_
  have h1 : (e' * b) • (indLIdealEquiv φ IsIdempotentElem.one
      (Ind.map (LinearMap.proj j) (Ind.map ι y))) = 0 := by
    rw [← map_smul, ← map_smul, ← map_smul, hy b, map_zero, map_zero, map_zero]
  have h2 := congrArg Subtype.val h1
  rw [Submodule.coe_smul, smul_eq_mul] at h2
  rw [mul_assoc] at h2 ⊢
  simpa [mul_assoc] using h2

end Induction

end Categorification
