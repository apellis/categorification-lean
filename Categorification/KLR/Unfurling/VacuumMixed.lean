/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.VacuumBubbles
import Categorification.KLR.Unfurling.VacuumPartialFractions

/-!
# Clockwise bubbles on the generating object with labels of both signs

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`: on the generating object `𝕍` the bubbles of the colour `i`
act by the coefficients of `∏_{π a = i} (1 - z_a t)^{-Λ_a}`, the product running over the labels
of both signs (with `Λ_a < 0` for the labels on which `𝕍` is highest weight).

`VacuumBubbles` treats an object on which all labels over `i` are lowest weight. This file allows
in addition labels `b` on which the object is highest weight. Let `V` have weight `h = -n < 0`
for `i`. Rouquier's inverse (Brundan (1.9)) gives cups `ν ≫ Dᵗ : V → F E V` and a cap
`d : F E V → V` with `ν ≫ Dᵗ ≫ d = δ_{t, n-1}` for `t < n` and `σ ≫ d = 0`, `σ : E F V → F E V` the
rightward crossing. Over the lowest weight labels `a`, `F E V = ⊕ₐ Wₐ` as in `VacuumBubbles`,
now with `∑ₐ hₐ = n + ∑_b Λ_b`. For each highest weight label `b`, `D - z_b` is invertible on
`F E V`, with inverse `w_b`, and `E F V` contains a Jordan chain `u_{b,1}, …, u_{b,Λ_b}` for the
dot `D' - z_b` whose first vector has cap `1` (`u_{b,m} ≫ κ = δ_{m,1}`).

Then, through an `L`-algebra map `ev` from `End V` to a commutative ring,

  `ev (ν ≫ Dᵏ ≫ d) = [t^{k+1-n}] ∏ₐ (1 - zₐ t)^{-hₐ} ∏_b (1 - z_b t)^{Λ_b}`

(`ev_comp_eq_lwSeq`). The proof:

* the dot slide `σ ≫ D - D' ≫ σ = κ ≫ ν` turns the Jordan chain into `ν ≫ w_bᵐ = u_{b,m} ≫ σ`
  (`chain_comp_sigma`), so `ν ≫ w_bᵐ ≫ d = 0`;
* partial fractions (`map_pow_mul_prod_pow_eq`) then give the dual-basis values of the cap
  `W ≫ d`, `W = ∏_b w_b^{Λ_b}`, in degrees below `∑ₐ hₐ`;
* `ev_comp_eq_coeff` computes all values of `W ≫ d`;
* multiplying back by the factors `D - z_b` multiplies the generating series by
  `1 - z_b t` (`lwSeq_succ_sub`, `map_pow_mul_eq_lwSeq_of_prod`).

## Main definitions

* `lwSeq D F n = [t^{n+1-D}] F`, zero if `n + 1 < D`.

## Main results

* `chain_comp_sigma`: the Jordan chain and the inverted dot.
* `map_pow_mul_eq_lwSeq_of_prod`: removing the inverted dots.
* `ev_comp_eq_lwSeq`: the values of the bubbles.
-/

open CategoryTheory CategoryTheory.Limits PowerSeries

namespace Categorification.KLR.Unfurling

/-! ## Shifted coefficient sequences -/

section Seq

variable {L : Type*} [Field L]

/-- `lwSeq D F n = [t^{n+1-D}] F`, and `0` if `n + 1 < D`. -/
noncomputable def lwSeq (D : ℕ) (F : PowerSeries L) (n : ℕ) : L :=
  if D ≤ n + 1 then coeff (n + 1 - D) F else 0

theorem lwSeq_succ_sub {D : ℕ} (hD : 1 ≤ D) (F : PowerSeries L) (u : L) (n : ℕ) :
    lwSeq D F (n + 1) - u * lwSeq D F n = lwSeq (D - 1) ((1 - C u * X) * F) n := by
  have hcoeff : ∀ m, coeff (m + 1) ((1 - C u * X) * F) = coeff (m + 1) F - u * coeff m F := by
    intro m; rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_succ_X_mul]
  have hcoeff0 : coeff 0 ((1 - C u * X) * F) = coeff 0 F := by
    rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_zero_X_mul, mul_zero, sub_zero]
  unfold lwSeq
  by_cases h1 : D ≤ n + 1
  · have e1 : n + 1 + 1 - D = (n + 1 - D) + 1 := by omega
    have e2 : n + 1 - (D - 1) = (n + 1 - D) + 1 := by omega
    simp only [show D ≤ n + 1 + 1 by omega, h1, show D - 1 ≤ n + 1 by omega, ↓reduceIte, e1, e2,
      hcoeff]
  · by_cases h2 : D = n + 2
    · subst h2
      simp only [show n + 2 ≤ n + 1 + 1 by omega, h1, show n + 2 - 1 ≤ n + 1 by omega,
        ↓reduceIte, show n + 1 + 1 - (n + 2) = 0 by omega, show n + 1 - (n + 2 - 1) = 0 by omega,
        hcoeff0, mul_zero, sub_zero]
    · simp only [show ¬D ≤ n + 1 + 1 by omega, h1, show ¬D - 1 ≤ n + 1 by omega, ↓reduceIte,
        mul_zero, sub_zero]

variable {A R : Type*} [CommRing A] [Algebra L A] [Ring R] [Algebra L R] (ψ : A →ₗ[L] R) (x : A)

/-- Removing one inverted dot `m` times multiplies the generating series by `(1 - z t)^m`. -/
theorem map_pow_mul_eq_lwSeq_of_pow (z : L) (w : A) (hw : (x - algebraMap L A z) * w = 1) :
    ∀ (m D : ℕ) (F : PowerSeries L) (e : A), m ≤ D →
      (∀ k, ψ (x ^ k * (w ^ m * e)) = algebraMap L R (lwSeq D F k)) →
      ∀ k, ψ (x ^ k * e) = algebraMap L R (lwSeq (D - m) ((1 - C z * X) ^ m * F) k) := by
  intro m
  induction m with
  | zero => intro D F e _ h k; simpa using h k
  | succ m ih =>
    intro D F e hm h k
    have h' := ih D F (w * e) (by omega)
      (fun k => by rw [← mul_assoc (w ^ m), ← pow_succ]; exact h k)
    have hx : x ^ k * e = x ^ (k + 1) * (w * e) - algebraMap L A z * (x ^ k * (w * e)) := by
      calc x ^ k * e = x ^ k * ((x - algebraMap L A z) * w) * e := by rw [hw, mul_one]
        _ = _ := by ring
    rw [hx, map_sub, h', ← Algebra.smul_def, map_smul, h', Algebra.smul_def, ← map_mul,
      ← map_sub, lwSeq_succ_sub (by omega), pow_succ', mul_assoc,
      show D - m - 1 = D - (m + 1) by omega]

/-- **Removing the inverted dots.** If `ψ (x^k ∏_{b ∈ S} w_b^{Λ_b} e)` is the shifted coefficient
sequence `lwSeq D F`, then `ψ (x^k e)` is `lwSeq (D - ∑_S Λ) (∏_S (1 - z_b t)^{Λ_b} F)`. -/
theorem map_pow_mul_eq_lwSeq_of_prod {B : Type*} [DecidableEq B] (z : B → L) (w : B → A)
    (hw : ∀ b, (x - algebraMap L A (z b)) * w b = 1) (Λ : B → ℕ) (S : Finset B) :
    ∀ (D : ℕ) (F : PowerSeries L) (e : A), ∑ b ∈ S, Λ b ≤ D →
      (∀ k, ψ (x ^ k * ((∏ b ∈ S, w b ^ Λ b) * e)) = algebraMap L R (lwSeq D F k)) →
      ∀ k, ψ (x ^ k * e) = algebraMap L R
        (lwSeq (D - ∑ b ∈ S, Λ b) ((∏ b ∈ S, (1 - C (z b) * X) ^ Λ b) * F) k) := by
  induction S using Finset.induction_on with
  | empty => intro D F e _ h k; simpa using h k
  | insert b S hb ih =>
    intro D F e hS h k
    rw [Finset.sum_insert hb] at hS ⊢
    rw [Finset.prod_insert hb] at h ⊢
    have h1 := map_pow_mul_eq_lwSeq_of_pow ψ x (z b) (w b) (hw b) (Λ b) D F
      ((∏ b ∈ S, w b ^ Λ b) * e) (by omega) (fun k => by rw [← mul_assoc (w b ^ Λ b)]; exact h k)
    rw [ih (D - Λ b) _ e (by omega) h1 k, mul_assoc, show D - Λ b - ∑ b ∈ S, Λ b =
      D - (Λ b + ∑ b ∈ S, Λ b) by omega, mul_left_comm]

end Seq

/-! ## The Jordan chain and the inverted dot -/

section Chain

variable {L : Type*} [CommRing L] {C : Type*} [Category C] [Preadditive C] [Linear L C]

theorem commute_of_mul_eq_one {M : Type*} [Monoid M] {a a' b : M} (h1 : a * a' = 1)
    (h2 : a' * a = 1) (hb : Commute a b) : Commute a' b := by
  show a' * b = b * a'
  calc a' * b = a' * b * (a * a') := by rw [h1, mul_one]
    _ = a' * (b * a) * a' := by simp only [mul_assoc]
    _ = a' * (a * b) * a' := by rw [hb.eq]
    _ = (a' * a) * (b * a') := by simp only [mul_assoc]
    _ = b * a' := by rw [h2, one_mul]

/-- **The Jordan chain and the inverted dot.** Let `σ : P → Q` satisfy the dot slide
`σ ≫ D - D' ≫ σ = κ ≫ ν`, let `w` be a left inverse of `D - z` (`(D - z) ≫ w = 𝟙`), and let
`u₁, …, u_Λ : V → P` be a Jordan chain of `D' - z` (`u_{m+1} ≫ (D' - z) = u_m`, `u₀ = 0`) with
`u_{m+1} ≫ κ = δ_{m,0}`. Then `u_{m+1} ≫ σ = ν ≫ w^{m+1}` for `m < Λ`. -/
theorem chain_comp_sigma {V P Q : C} (σ : P ⟶ Q) (κ : P ⟶ V) (ν : V ⟶ Q) (D : End Q)
    (D' : End P) (hrel : σ ≫ D - D' ≫ σ = κ ≫ ν) (z : L) (w : End Q)
    (hw : w * (D - algebraMap L (End Q) z) = 1) (Λ : ℕ) (u : ℕ → (V ⟶ P)) (hu0 : u 0 = 0)
    (hu : ∀ m, m < Λ → u (m + 1) ≫ (D' - algebraMap L (End P) z : End P) = u m)
    (huκ : ∀ m, m < Λ → u (m + 1) ≫ κ = if m = 0 then 𝟙 V else 0) :
    ∀ m, m < Λ → u (m + 1) ≫ σ = ν ≫ (w ^ (m + 1) : End Q) := by
  have hz : σ ≫ (algebraMap L (End Q) z : End Q) = (algebraMap L (End P) z : End P) ≫ σ := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Linear.comp_smul,
      Linear.smul_comp, End.one_def, End.one_def, Category.comp_id, Category.id_comp]
  have hrel' : σ ≫ (D - algebraMap L (End Q) z : End Q) -
      (D' - algebraMap L (End P) z : End P) ≫ σ = κ ≫ ν := by
    rw [Preadditive.comp_sub, Preadditive.sub_comp, hz, ← hrel]; abel
  have hσ : σ = (D' - algebraMap L (End P) z : End P) ≫ σ ≫ w + κ ≫ ν ≫ w := by
    have h := congrArg (· ≫ w) hrel'
    simp only [Preadditive.sub_comp, Category.assoc] at h
    have hw' : (D - algebraMap L (End Q) z : End Q) ≫ w = 𝟙 Q := by
      rw [← End.mul_def, hw, End.one_def]
    rw [hw', Category.comp_id] at h
    rw [← h]; abel
  intro m
  induction m with
  | zero =>
    intro hm
    rw [hσ, Preadditive.comp_add, ← Category.assoc, hu 0 hm, hu0, Limits.zero_comp, zero_add,
      ← Category.assoc, huκ 0 hm]
    simp only [↓reduceIte, Category.id_comp, zero_add, pow_one]
  | succ m ih =>
    intro hm
    rw [hσ, Preadditive.comp_add, ← Category.assoc, hu (m + 1) hm,
      ← Category.assoc (u (m + 1 + 1)) κ, huκ (m + 1) hm]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Limits.zero_comp, add_zero]
    rw [← Category.assoc, ih (by omega), Category.assoc, pow_succ' w (m + 1), End.mul_def]

end Chain

/-! ## The bubbles -/

section Bubbles

variable {L : Type*} [Field L] {C : Type*} [Category C] [Preadditive C] [Linear L C]

/-- **The clockwise bubbles on the generating object, labels of both signs** (Webster,
arXiv:1603.06311v3, proof of the theorem with label `nondegenerate`). Let `V` be an object with
cups `ν ≫ Dᵗ : V → Q` and a cap `d : Q → V` dual to them in degrees `t < n`, `n > 0`.

* Over the lowest weight labels `a`: `Q = ⊕ₐ Wₐ`, the cup with `n` dots is `νₐ ≫ (zₐ + yₐ)ⁿ` on
  the summand `a`, and `νₐ ≫ yₐ^m = 0` for `m ≥ hₐ`.
* Over the highest weight labels `b`: `w_b` is a two-sided inverse of `D - z_b`, and
  `u_{b,1}, …, u_{b,Λ_b} : V → P` is a Jordan chain of `D' - z_b` whose cap is `δ_{m,1}`.
* `σ : P → Q` satisfies the dot slide `σ ≫ D - D' ≫ σ = κ ≫ ν` and `σ ≫ d = 0`.
* `∑ₐ hₐ = n + ∑_b Λ_b`.

Then `ev (ν ≫ Dᵏ ≫ d) = [t^{k+1-n}] ∏_b (1 - z_b t)^{Λ_b} ∏ₐ (1 - zₐ t)^{-hₐ}`. -/
theorem ev_comp_eq_lwSeq {R : Type*} [CommRing R] [Algebra L R] {V Q P : C}
    (ev : End V →ₐ[L] R)
    {A : Type*} [Fintype A] {Wa : A → C} (π : ∀ a, Q ⟶ Wa a) (ι : ∀ a, Wa a ⟶ Q)
    (νa : ∀ a, V ⟶ Wa a) (y : ∀ a, End (Wa a)) (za : A → L) (hp : A → ℕ)
    (ν : V ⟶ Q) (d : Q ⟶ V) (D : End Q) (hπι : ∑ a, π a ≫ ι a = 𝟙 Q)
    (hc : ∀ n a, (ν ≫ (D ^ n : End Q)) ≫ π a =
      νa a ≫ ((algebraMap L (End (Wa a)) (za a) + y a) ^ n : End (Wa a)))
    (hν : ∀ a m, hp a ≤ m → νa a ≫ (y a ^ m : End (Wa a)) = 0)
    {B : Type*} [Fintype B] [DecidableEq B] (zb : B → L) (hzb : Function.Injective zb)
    (Λ : B → ℕ) (w : B → End Q) (hw₁ : ∀ b, (D - algebraMap L (End Q) (zb b)) * w b = 1)
    (hw₂ : ∀ b, w b * (D - algebraMap L (End Q) (zb b)) = 1)
    (σ : P ⟶ Q) (κ : P ⟶ V) (D' : End P) (hrel : σ ≫ D - D' ≫ σ = κ ≫ ν) (hσd : σ ≫ d = 0)
    (u : B → ℕ → (V ⟶ P)) (hu0 : ∀ b, u b 0 = 0)
    (hu : ∀ b m, m < Λ b → u b (m + 1) ≫ (D' - algebraMap L (End P) (zb b) : End P) = u b m)
    (huκ : ∀ b m, m < Λ b → u b (m + 1) ≫ κ = if m = 0 then 𝟙 V else 0)
    (n : ℕ) (hn : 0 < n) (hN : ∑ a, hp a = n + ∑ b, Λ b)
    (hd : ∀ t < n, ev (ν ≫ (D ^ t : End Q) ≫ d) = if t + 1 = n then 1 else 0) (k : ℕ) :
    ev (ν ≫ (D ^ k : End Q) ≫ d) = algebraMap L R (lwSeq n
      ((∏ b, (1 - PowerSeries.C (zb b) * X) ^ Λ b) *
        ((∏ a, oneSubUnit (za a) ^ (-(hp a : ℤ)) : (PowerSeries L)ˣ) : PowerSeries L)) k) := by
  classical
  -- the commutative subalgebra generated by `D` and the `w b`
  have hDw : ∀ b, Commute D (w b) := fun b =>
    (commute_of_mul_eq_one (hw₁ b) (hw₂ b)
      ((Commute.refl D).sub_left (Algebra.commute_algebraMap_left _ _))).symm
  have hww : ∀ b c, Commute (w b) (w c) := fun b c =>
    (commute_of_mul_eq_one (hw₁ c) (hw₂ c)
      ((hDw b).sub_left (Algebra.commute_algebraMap_left _ _))).symm
  let s : Set (End Q) := insert D (Set.range w)
  have hcomm : s.Pairwise Commute := by
    have key : ∀ p ∈ s, ∀ q ∈ s, Commute p q := by
      rintro p (rfl | ⟨b, rfl⟩) q (rfl | ⟨c, rfl⟩)
      · exact Commute.refl _
      · exact hDw c
      · exact (hDw b).symm
      · exact hww b c
    exact fun p hp q hq _ => key p hp q hq
  have hc' := Algebra.isMulCommutative_adjoin L hcomm
  let _ : CommRing (Algebra.adjoin L s) :=
    { (Algebra.adjoin L s).toRing with mul_comm := fun a b => hc'.is_comm.comm a b }
  let x : Algebra.adjoin L s := ⟨D, Algebra.subset_adjoin (Set.mem_insert _ _)⟩
  let w' : B → Algebra.adjoin L s := fun b =>
    ⟨w b, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨b, rfl⟩)⟩
  let ψE : End Q →ₗ[L] R :=
    { toFun := fun e => ev (ν ≫ e ≫ d)
      map_add' := fun e₁ e₂ => by
        change ev (ν ≫ ((e₁ : Q ⟶ Q) + e₂) ≫ d) = _
        rw [Preadditive.add_comp, Preadditive.comp_add, map_add]
      map_smul' := fun r e => by
        change ev (ν ≫ (r • (e : Q ⟶ Q)) ≫ d) = _
        rw [Linear.smul_comp, Linear.comp_smul, map_smul, RingHom.id_apply] }
  let ψ : Algebra.adjoin L s →ₗ[L] R := ψE ∘ₗ (Algebra.adjoin L s).val.toLinearMap
  have hψ : ∀ e, ψ e = ev (ν ≫ (e : End Q) ≫ d) := fun e => rfl
  have hw' : ∀ b, (x - algebraMap L _ (zb b)) * w' b = 1 := fun b => Subtype.ext (hw₁ b)
  have hxpow : ∀ t, ((x ^ t : Algebra.adjoin L s) : End Q) = D ^ t :=
    fun t => SubmonoidClass.coe_pow x t
  have hwpow : ∀ b j, ((w' b ^ j : Algebra.adjoin L s) : End Q) = w b ^ j :=
    fun b j => SubmonoidClass.coe_pow (w' b) j
  -- the values of `ψ` on the generators
  have hx : ∀ t < n, ψ (x ^ t) = if t + 1 = n then 1 else 0 := fun t ht => by
    rw [hψ, hxpow]; exact hd t ht
  have hwj : ∀ b j, 1 ≤ j → j ≤ Λ b → ψ (w' b ^ j) = if n = 0 ∧ j = 1 then 1 else 0 := by
    intro b j hj1 hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    rw [hψ, hwpow, ← Category.assoc, ← chain_comp_sigma σ κ ν D D' hrel (zb b) (w b) (hw₂ b)
      (Λ b) (u b) (hu0 b) (hu b) (huκ b) m (by omega), Category.assoc, hσd, Limits.comp_zero,
      map_zero]
    simp only [show ¬n = 0 by omega, false_and, ↓reduceIte]
  -- partial fractions
  have helim := map_pow_mul_prod_pow_eq ψ x hzb w' hw' Λ n hx hwj
  let W : Algebra.adjoin L s := ∏ b, w' b ^ Λ b
  have hcoe : ∀ t, ((x ^ t * W : Algebra.adjoin L s) : End Q) = (D ^ t : End Q) ≫ (W : End Q) := by
    intro t
    rw [mul_comm]
    show (W : End Q) * ((x ^ t : Algebra.adjoin L s) : End Q) = _
    rw [hxpow, End.mul_def]
  have hNpos : 0 < ∑ a, hp a := by omega
  have hd' : ∀ t < ∑ a, hp a, ev ((ν ≫ (D ^ t : End Q)) ≫ (W : End Q) ≫ d) =
      if t + 1 = ∑ a, hp a then 1 else 0 := by
    intro t ht
    rw [Category.assoc, ← Category.assoc (D ^ t : End Q), ← hcoe, ← hψ, hN]
    exact helim t (by omega)
  -- all values of the cap `W ≫ d`
  have hall : ∀ k, ψ (x ^ k * ((∏ b ∈ Finset.univ, w' b ^ Λ b) * 1)) = algebraMap L R
      (lwSeq (∑ a, hp a)
        ((∏ a, oneSubUnit (za a) ^ (-(hp a : ℤ)) : (PowerSeries L)ˣ) : PowerSeries L) k) := by
    intro k
    rw [mul_one, hψ, hcoe, Category.assoc, ← Category.assoc ν,
      ev_comp_eq_coeff π ι νa y za hp (fun n => ν ≫ (D ^ n : End Q)) ((W : End Q) ≫ d) ev hπι
        hc hν hNpos hd' k, lwSeq]
    split_ifs <;> simp
  -- removing the inverted dots
  have h := map_pow_mul_eq_lwSeq_of_prod ψ x zb w' hw' Λ Finset.univ (∑ a, hp a) _ 1
    (by omega) hall k
  rw [mul_one, hψ, hxpow, show ∑ a, hp a - ∑ b ∈ Finset.univ, Λ b = n by
    omega] at h
  exact h

end Bubbles

end Categorification.KLR.Unfurling
