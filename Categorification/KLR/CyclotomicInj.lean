/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicFree

/-!
# `P : K_1 → K_0` is injective: Kang–Kashiwara Lemmas 4.16, 4.17

S.-J. Kang, M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4, §4.2: Lemma 4.16 (multiplication by a
polynomial with invertible leading coefficient is injective on a free `A[t]`-module), Lemma 4.17
(`P` is injective).

* `singlePoly`: the KLR algebra of one strand is the polynomial ring, `R(i) ≅ k[t]`
  (`sec_singlePoly`, `singlePoly_sec`).
* `theta : R(i) ⊗ R(β) → R(β)[t]` (with left inverse `thetaInv`) identifies
  `R(i) ⊗ J` with the polynomials with coefficients in `J` (`mem_tJ_iff`).
* KK's element `A` (`aElt`) is `ι(A')` on `1_{i, β}`, and `theta A'` is, on each idempotent
  `e(𝐢')`, a unit times a monic polynomial in `t` (under KK's hypotheses: `a_i` monic, `Q_{ij}` with
  unit leading coefficient in its first variable). Hence right multiplication by `A'` is injective
  modulo `R(i) ⊗ J` (KK Lemma 4.16 in this case), and by `Q ∘ P = A` (KK Thm. 4.15) and the
  structure of `K_1` (`mem_cycL1_iff`), `P` is injective on `K_1 e(i, β)` (KK Lemma 4.17).

Domain `k` and factorized `Q` (as for the basis theorem); symmetric `Q` is implied.
-/

namespace Categorification.KLR

open Equiv TypeA PolyRep
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k}

/-! ### The KLR algebra of one strand -/

section Single

variable (i : I)

local notation "Si" => (Singleton.singleton i : Multiset I)

/-- The images of the generators of `R(i)` in `k[t]`. -/
noncomputable def singleGen : Gen Si → Polynomial k
  | .idem _ => 1
  | .dot _ => Polynomial.X
  | .cross _ => 0

omit [DecidableEq I] in
theorem card_single : Multiset.card Si = 1 := Multiset.card_singleton i

noncomputable instance : Unique (Seq Si) := { default := default, uniq := fun _ => Subsingleton.elim _ _ }

variable (Q) in
/-- `R(i) → k[t]`: `x ↦ t`. -/
noncomputable def singlePoly : KLRAlgebra k Q Si →ₐ[k] Polynomial k :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (singleGen i), fun _ _ h => by
    have hm : Multiset.card Si = 1 := card_single i
    cases h with
    | idem_mul s t =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply, singleGen, Subsingleton.elim s t,
        ↓reduceIte, mul_one]
    | idem_sum =>
      simp only [map_sum, FreeAlgebra.lift_ι_apply, singleGen, Finset.sum_const,
        Finset.card_univ, Fintype.card_unique, one_smul, map_one]
    | dot_idem a s => simp only [map_mul, FreeAlgebra.lift_ι_apply, singleGen, mul_one, one_mul]
    | cross_idem j s => simp only [map_mul, FreeAlgebra.lift_ι_apply, singleGen, mul_zero, zero_mul]
    | cross_zero j h => simp only [FreeAlgebra.lift_ι_apply, singleGen, map_zero]
    | dot_dot a b => simp only [map_mul, FreeAlgebra.lift_ι_apply, singleGen]
    | cross_cross j l h => simp only [map_mul, FreeAlgebra.lift_ι_apply, singleGen, mul_zero]
    | dot_cross a j h₁ h₂ =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply, singleGen, mul_zero, zero_mul]
    | dot_cross_left j h s => exact absurd h (by omega)
    | dot_cross_right j h s => exact absurd h (by omega)
    | cross_sq j h s => exact absurd h (by omega)
    | braid j h s => exact absurd h (by omega)⟩

theorem singlePoly_e (s : Seq Si) : singlePoly Q i (e s) = 1 :=
  (RingQuot.liftAlgHom_mkAlgHom_apply k _ _ (fe k Si s)).trans (FreeAlgebra.lift_ι_apply _ _)

theorem singlePoly_x (b : Fin (Multiset.card Si)) : singlePoly Q i (x b) = Polynomial.X :=
  (RingQuot.liftAlgHom_mkAlgHom_apply k _ _ (fx k Si b)).trans (FreeAlgebra.lift_ι_apply _ _)

theorem singlePoly_ψ (j : ℕ) : singlePoly Q i (ψ j) = 0 :=
  (RingQuot.liftAlgHom_mkAlgHom_apply k _ _ (fψ k Si j)).trans (FreeAlgebra.lift_ι_apply _ _)

variable (Q) in
/-- `k[t] → R(i)`: `t ↦ x`. -/
noncomputable def sec : Polynomial k →ₐ[k] KLRAlgebra k Q Si :=
  Polynomial.aeval (x ⟨0, by rw [card_single]; omega⟩)

theorem sec_singlePoly (u : KLRAlgebra k Q Si) : sec Q i (singlePoly Q i u) = u := by
  have h : (sec Q i).comp (singlePoly Q i) = AlgHom.id k _ := by
    apply RingQuot.ringQuot_ext'
    apply FreeAlgebra.hom_ext
    funext g
    cases g with
    | idem s =>
      change sec Q i (singlePoly Q i (e s)) = e s
      rw [singlePoly_e, map_one, e_single]
    | dot b =>
      change sec Q i (singlePoly Q i (x b)) = x b
      rw [singlePoly_x, sec, Polynomial.aeval_X]
      congr 1
      have hb := b.isLt
      simp only [Multiset.card_singleton] at hb
      exact Fin.ext (by simp only; omega)
    | cross j =>
      change sec Q i (singlePoly Q i (ψ j)) = ψ j
      rw [singlePoly_ψ, map_zero, ψ_eq_zero j (by rw [card_single]; omega)]
  exact congrArg (fun f => f u) h

theorem singlePoly_sec (p : Polynomial k) : singlePoly Q i (sec Q i p) = p := by
  have h : (singlePoly Q i).comp (sec Q i) = AlgHom.id k _ := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, sec, Polynomial.aeval_X, singlePoly_x, AlgHom.id_apply]
  exact congrArg (fun f => f p) h

end Single

/-! ### `R(i) ⊗ R(β) ≅ R(β)[t]` -/

section Theta

variable (i : I) (β : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "T" => KLRAlgebra k Q Si ⊗[k] KLRAlgebra k Q β
local notation "Rb" => KLRAlgebra k Q β

omit [DecidableEq I] in
theorem coeff_aeval_X {A : Type*} [Ring A] [Algebra k A] (p : Polynomial k) (n : ℕ) :
    (Polynomial.aeval (Polynomial.X : Polynomial A) p).coeff n = algebraMap k A (p.coeff n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, map_add]
  | monomial m c =>
    rw [Polynomial.aeval_monomial, Polynomial.algebraMap_apply (R := k),
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_monomial]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [map_zero]

omit [DecidableEq I] in
theorem commute_aeval_X_C {A : Type*} [Ring A] [Algebra k A] (p : Polynomial k) (b : A) :
    Commute (Polynomial.aeval (Polynomial.X : Polynomial A) p) (Polynomial.C b) :=
  Polynomial.ext fun n => by
    rw [Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, coeff_aeval_X, Algebra.commutes]

variable (Q) in
/-- `θ : R(i) ⊗ R(β) → R(β)[t]`, `x ⊗ 1 ↦ t`, `1 ⊗ b ↦ b`. -/
noncomputable def theta : T →ₐ[k] Polynomial Rb :=
  Algebra.TensorProduct.lift ((Polynomial.aeval (Polynomial.X : Polynomial Rb)).comp
    (singlePoly Q i)) (Polynomial.CAlgHom) (fun _ b => commute_aeval_X_C _ b)

theorem theta_tmul (a : KLRAlgebra k Q Si) (b : Rb) :
    theta Q i β (a ⊗ₜ b) =
      Polynomial.aeval (Polynomial.X : Polynomial Rb) (singlePoly Q i a) * Polynomial.C b :=
  Algebra.TensorProduct.lift_tmul _ _ _ a b

theorem coeff_theta_tmul (a : KLRAlgebra k Q Si) (b : Rb) (n : ℕ) :
    (theta Q i β (a ⊗ₜ b)).coeff n = algebraMap k Rb ((singlePoly Q i a).coeff n) * b := by
  rw [theta_tmul, Polynomial.coeff_mul_C, coeff_aeval_X]

variable (Q) in
/-- The inverse of `θ`: `∑ b_n t^n ↦ ∑ x^n ⊗ b_n`. -/
noncomputable def thetaInv : Polynomial Rb →ₗ[k] T :=
  Polynomial.lsum fun n : ℕ =>
    TensorProduct.mk k (KLRAlgebra k Q Si) Rb
      ((x ⟨0, by rw [card_single]; omega⟩ : KLRAlgebra k Q Si) ^ n)

theorem thetaInv_monomial (n : ℕ) (b : Rb) :
    thetaInv Q i β (Polynomial.monomial n b) =
      ((x ⟨0, by rw [card_single]; omega⟩ : KLRAlgebra k Q Si) ^ n) ⊗ₜ b := by
  rw [thetaInv, Polynomial.lsum_apply, Polynomial.sum_monomial_index]
  · rfl
  · exact TensorProduct.tmul_zero _ _

theorem thetaInv_theta (t : T) : thetaInv Q i β (theta Q i β t) = t := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    have key : ∀ p : Polynomial k, thetaInv Q i β
        (Polynomial.aeval (Polynomial.X : Polynomial Rb) p * Polynomial.C b) = sec Q i p ⊗ₜ b := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p q hp hq => rw [map_add, add_mul, map_add, hp, hq, map_add, TensorProduct.add_tmul]
      | monomial m c =>
        rw [Polynomial.aeval_monomial, Polynomial.algebraMap_apply (R := k), mul_assoc,
          (Polynomial.commute_X_pow (Polynomial.C b) m).eq, ← mul_assoc, ← Polynomial.C_mul,
          Polynomial.C_mul_X_pow_eq_monomial, thetaInv_monomial, sec, Polynomial.aeval_monomial,
          ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
    rw [theta_tmul, key, sec_singlePoly]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

theorem theta_thetaInv (q : Polynomial Rb) : theta Q i β (thetaInv Q i β q) = q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | monomial m b =>
    rw [thetaInv_monomial, theta_tmul, map_pow, singlePoly_x, map_pow, Polynomial.aeval_X,
      (Polynomial.commute_X_pow (Polynomial.C b) m).eq, Polynomial.C_mul_X_pow_eq_monomial]

variable (a : I → Polynomial k)

/-- `R(i) ⊗ J` consists of the elements whose image under `θ` has all coefficients in `J`. -/
theorem mem_tJ_iff (t : T) :
    t ∈ tJ (Q := Q) i β a ↔ ∀ n, (theta Q i β t).coeff n ∈ cycIdeal Q a β := by
  constructor
  · intro ht
    induction ht using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, j, hj, rfl⟩ := hy
      intro n
      rw [coeff_theta_tmul]
      exact TwoSidedIdeal.mul_mem_left _ _ _ hj
    | zero => intro n; rw [map_zero, Polynomial.coeff_zero]; exact TwoSidedIdeal.zero_mem _
    | add y z _ _ hy hz =>
      intro n; rw [map_add, Polynomial.coeff_add]; exact TwoSidedIdeal.add_mem _ (hy n) (hz n)
    | smul r y _ hy =>
      intro n
      rw [map_smul, Polynomial.coeff_smul, Algebra.smul_def]
      exact TwoSidedIdeal.mul_mem_left _ _ _ (hy n)
  · intro h
    rw [← thetaInv_theta (Q := Q) i β t, thetaInv, Polynomial.lsum_apply, Polynomial.sum_def]
    exact Submodule.sum_mem _ fun n _ => Submodule.subset_span ⟨_, _, h n, rfl⟩

end Theta

/-! ### Splitting off the first dot -/

section Split

variable (i : I) (β : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "T" => KLRAlgebra k Q Si ⊗[k] KLRAlgebra k Q β
local notation "Rb" => KLRAlgebra k Q β
local notation "Pb" => MvPolynomial (Fin (Multiset.card β)) k

omit [DecidableEq I] in
theorem card_single_add : Multiset.card (Si + β) = Multiset.card β + 1 := by
  rw [Multiset.card_add, Multiset.card_singleton, add_comm]

omit [DecidableEq I] in
theorem zero_lt_card_single_add : 0 < Multiset.card (Si + β) := by
  rw [card_single_add]; omega

/-- `Fin (n + 1) ≃ Fin (card ({i} + β))`. -/
def castFin : Fin (Multiset.card β + 1) ≃ Fin (Multiset.card (Si + β)) :=
  finCongr (card_single_add i β).symm

/-- `k[x_0, …, x_n] ≅ k[x_1, …, x_n][t]`, splitting off the first variable. -/
noncomputable def fSplit : MvPolynomial (Fin (Multiset.card (Si + β))) k →ₐ[k] Polynomial Pb :=
  (MvPolynomial.finSuccEquiv k (Multiset.card β)).toAlgHom.comp
    (MvPolynomial.rename (castFin i β).symm)

omit [DecidableEq I] in
theorem fSplit_X_zero (h : 0 < Multiset.card (Si + β)) :
    fSplit (k := k) i β (MvPolynomial.X ⟨0, h⟩) = Polynomial.X := by
  rw [fSplit, AlgHom.comp_apply, MvPolynomial.rename_X,
    show (castFin i β).symm ⟨0, h⟩ = 0 from Fin.ext rfl]
  exact MvPolynomial.finSuccEquiv_X_zero (R := k)

omit [DecidableEq I] in
theorem fSplit_X_succ (b : ℕ) (hb : b + 1 < Multiset.card (Si + β)) :
    fSplit (k := k) i β (MvPolynomial.X ⟨b + 1, hb⟩) =
      Polynomial.C (MvPolynomial.X ⟨b, by rw [card_single_add] at hb; omega⟩) := by
  rw [fSplit, AlgHom.comp_apply, MvPolynomial.rename_X,
    show (castFin i β).symm ⟨b + 1, hb⟩ =
      (⟨b, by rw [card_single_add] at hb; omega⟩ : Fin (Multiset.card β)).succ from Fin.ext rfl]
  exact MvPolynomial.finSuccEquiv_X_succ (R := k)

theorem thetaInv_mul (p q : Polynomial Rb) :
    thetaInv Q i β (p * q) = thetaInv Q i β p * thetaInv Q i β q := by
  conv_lhs => rw [← theta_thetaInv (Q := Q) i β p, ← theta_thetaInv (Q := Q) i β q, ← map_mul]
  rw [thetaInv_theta]

theorem thetaInv_one : thetaInv Q i β (1 : Polynomial Rb) = 1 := by
  conv_lhs => rw [← map_one (theta Q i β)]
  rw [thetaInv_theta]

variable (Q) in
/-- The element of `R(i) ⊗ R(β)` corresponding to a polynomial in the dots of `R({i} + β)`. -/
noncomputable def cOf (F : MvPolynomial (Fin (Multiset.card (Si + β))) k) : T :=
  thetaInv Q i β (Polynomial.map (pol : Pb →ₐ[k] Rb).toRingHom (fSplit i β F))

theorem theta_cOf (F : MvPolynomial (Fin (Multiset.card (Si + β))) k) :
    theta Q i β (cOf Q i β F) = Polynomial.map (pol : Pb →ₐ[k] Rb).toRingHom (fSplit i β F) :=
  theta_thetaInv i β _

theorem cOf_mul (F G : MvPolynomial (Fin (Multiset.card (Si + β))) k) :
    cOf Q i β (F * G) = cOf Q i β F * cOf Q i β G := by
  rw [cOf, map_mul, Polynomial.map_mul, thetaInv_mul, cOf, cOf]

/-- `ι(cOf F) = f(x) 1_{i, β}`. -/
theorem concat_cOf (F : MvPolynomial (Fin (Multiset.card (Si + β))) k) :
    concat Q Si β (cOf Q i β F) = pol F * oneConcat Q Si β := by
  have h0 : 0 < Multiset.card (Si + β) := by rw [card_single_add]; omega
  induction F using MvPolynomial.induction_on with
  | C c =>
    have hC : cOf Q i β (MvPolynomial.C c) =
        (1 : KLRAlgebra k Q Si) ⊗ₜ (algebraMap k Rb c) := by
      unfold cOf
      rw [MvPolynomial.algHom_C, Polynomial.algebraMap_apply (R := k), Polynomial.map_C,
        ← Polynomial.monomial_zero_left, thetaInv_monomial, pow_zero, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.algebraMap_eq, MvPolynomial.algHom_C]
    rw [hC, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, map_smul,
      ← Algebra.TensorProduct.one_def, concat_one, MvPolynomial.algHom_C, Algebra.smul_def]
  | add F G hF hG =>
    unfold cOf at hF hG ⊢
    rw [map_add, Polynomial.map_add, map_add, map_add, hF, hG, map_add, add_mul]
  | mul_X F b hF =>
    rw [cOf_mul, concat_mul, hF, map_mul, pol_X]
    simp only [mul_assoc]
    congr 1
    rw [oneConcat_mul_concat]
    obtain ⟨b, hb⟩ := b
    rcases b with _ | b
    · unfold cOf
      rw [fSplit_X_zero i β h0, Polynomial.map_X, ← Polynomial.monomial_one_one_eq_X,
        thetaInv_monomial, pow_one, concat_x_tmul_one, posL_single_zero]
    · unfold cOf
      rw [fSplit_X_succ i β b hb, Polynomial.map_C, ← Polynomial.monomial_zero_left,
        thetaInv_monomial, pow_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, pol_X,
        concat_one_tmul_x, posR_single]

end Split

/-! ### Unit times monic -/

section Monic

/-- A unit of `k` times a monic polynomial in `t` over `k[x_1, …, x_n]`. -/
def UMonic {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) k)) : Prop :=
  ∃ u : kˣ, ∃ M : Polynomial (MvPolynomial (Fin n) k), M.Monic ∧
    p = Polynomial.C (MvPolynomial.C (u : k)) * M

omit [DecidableEq I] in
theorem UMonic.of_monic {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) k)} (h : p.Monic) :
    UMonic p :=
  ⟨1, p, h, by simp⟩

omit [DecidableEq I] in
theorem UMonic.neg_one {n : ℕ} : UMonic (-1 : Polynomial (MvPolynomial (Fin n) k)) :=
  ⟨-1, 1, Polynomial.monic_one, by simp⟩

omit [DecidableEq I] in
theorem UMonic.mul {n : ℕ} {p q : Polynomial (MvPolynomial (Fin n) k)} (hp : UMonic p)
    (hq : UMonic q) : UMonic (p * q) := by
  obtain ⟨u, M, hM, rfl⟩ := hp
  obtain ⟨v, N, hN, rfl⟩ := hq
  refine ⟨u * v, M * N, hM.mul hN, ?_⟩
  rw [Units.val_mul, map_mul, map_mul]; ring

end Monic

section Lead

variable (i : I) (β : Multiset I) (a : I → Polynomial k)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Pb" => MvPolynomial (Fin (Multiset.card β)) k

omit [DecidableEq I] in
theorem aeval_X_eq_map {A : Type*} [Ring A] [Algebra k A] (g : Polynomial k) :
    Polynomial.aeval (Polynomial.X : Polynomial A) g = g.map (algebraMap k A) :=
  Polynomial.ext fun n => by rw [coeff_aeval_X, Polynomial.coeff_map]

omit [DecidableEq I] in
theorem umonic_fSplit_aeval {g : Polynomial k} (hg : g.Monic) :
    UMonic (fSplit (k := k) i β (Polynomial.aeval (MvPolynomial.X
      ⟨0, zero_lt_card_single_add i β⟩) g)) := by
  rw [← Polynomial.aeval_algHom_apply, fSplit_X_zero, aeval_X_eq_map]
  exact UMonic.of_monic (hg.map _)

omit [DecidableEq I] in
theorem fSplit_rename_vec2 (b : ℕ) (hb : b + 1 < Multiset.card (Si + β))
    (F : MvPolynomial (Fin 2) k) :
    fSplit (k := k) i β (MvPolynomial.rename ![⟨0, zero_lt_card_single_add i β⟩, ⟨b + 1, hb⟩] F) =
      MvPolynomial.aeval ![Polynomial.X, Polynomial.C (MvPolynomial.X
        ⟨b, by rw [card_single_add] at hb; omega⟩ : Pb)] F := by
  rw [← AlgHom.comp_apply, MvPolynomial.aeval_unique ((fSplit i β).comp (MvPolynomial.rename _))]
  congr 2
  funext c
  fin_cases c
  · rw [Function.comp_apply, AlgHom.comp_apply, MvPolynomial.rename_X]
    exact fSplit_X_zero i β _
  · rw [Function.comp_apply, AlgHom.comp_apply, MvPolynomial.rename_X]
    exact fSplit_X_succ i β b hb

omit [DecidableEq I] in
theorem umonic_aeval_Q [IsDomain k] (q : MvPolynomial (Fin 2) k)
    (hq : IsUnit (polyInY q).leadingCoeff) (z : Pb) :
    UMonic (MvPolynomial.aeval ![Polynomial.C z, Polynomial.X] q) := by
  obtain ⟨c, hc, hcq⟩ := Polynomial.isUnit_iff.1 hq
  set φ : Polynomial (Polynomial k) →ₐ[k] Polynomial Pb :=
    Polynomial.mapAlgHom (Polynomial.aeval z) with hφ
  have hmap : φ (polyInY q) = MvPolynomial.aeval ![Polynomial.C z, Polynomial.X] q := by
    rw [polyInY, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 2
    funext c
    fin_cases c
    · simp [hφ, Polynomial.mapAlgHom]
    · simp [hφ, Polynomial.mapAlgHom]
  have hM : (Polynomial.C (Polynomial.C ((hc.unit⁻¹ : kˣ) : k)) * polyInY q).Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [← hcq, ← Polynomial.C_mul, IsUnit.val_inv_mul hc, Polynomial.C_1]
  have hsplit : φ (polyInY q) = φ (Polynomial.C (Polynomial.C (hc.unit : k))) *
      φ (Polynomial.C (Polynomial.C ((hc.unit⁻¹ : kˣ) : k)) * polyInY q) := by
    rw [← map_mul, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul, Units.mul_inv,
      Polynomial.C_1, Polynomial.C_1, one_mul]
  refine ⟨hc.unit, φ (Polynomial.C (Polynomial.C ((hc.unit⁻¹ : kˣ) : k)) * polyInY q), ?_, ?_⟩
  · rw [hφ]; exact hM.map _
  · rw [← hmap, hsplit]
    congr 1
    simp [hφ, Polynomial.mapAlgHom]

end Lead

/-! ### KK's element `A` on `1_{i, β}`, and Lemmas 4.16, 4.17 -/

section Inj

variable (i : I) (β : Multiset I) (a : I → Polynomial k)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "T" => KLRAlgebra k Q Si ⊗[k] KLRAlgebra k Q β
local notation "Rb" => KLRAlgebra k Q β
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "Pb" => MvPolynomial (Fin (Multiset.card β)) k

/-- The sequence `i 𝐢'`. -/
noncomputable abbrev cons1 (s : Seq β) : Seq (Si + β) := (default : Seq Si).append s

variable (Q) in
/-- KK's polynomial `a_i(t) ∏ (−1 or Q_{i, i'_b}(t, x_b))` on `e(i 𝐢')`, as a polynomial in the
dots of `R({i} + β)`. -/
noncomputable def gPol (s : Seq β) : MvPolynomial (Fin (Multiset.card (Si + β))) k :=
  cycA a (zero_lt_card_single_add i β) (cons1 i β s) *
    cycF Q (cons1 i β s) (Multiset.card β)

variable (Q) in
/-- KK's `A`, as an element of `R(i) ⊗ R(β)`. -/
noncomputable def aPrime : T :=
  ∑ s : Seq β, cOf Q i β (gPol Q i β a s) * (1 ⊗ₜ e s)

theorem oneConcat_single_eq :
    (oneConcat Q Si β : R) = ∑ s : Seq β, e (cons1 i β s) := by
  rw [oneConcat_eq, Fintype.sum_prod_type, Fintype.sum_unique]

theorem aElt_mul_oneConcat :
    (aElt a (zero_lt_card_single_add i β) (Multiset.card β) * oneConcat Q Si β : R) =
      concat Q Si β (aPrime Q i β a) := by
  rw [oneConcat_single_eq, Finset.mul_sum, aPrime, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [concat_mul, concat_cOf, ← e_single (Q := Q) i (default : Seq Si), concat_e_tmul_e,
    mul_assoc, oneConcat, eSum_mul_e, ite_eq_left (append_mem_concatSet _ _), aElt,
    Finset.sum_mul, Finset.sum_eq_single (cons1 i β s)]
  · rw [mul_assoc, e_mul_self]; rfl
  · intro t _ ht; rw [mul_assoc, e_mul_e, ite_eq_right ht, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem theta_aPrime :
    theta Q i β (aPrime Q i β a) = ∑ s : Seq β,
      Polynomial.map (pol : Pb →ₐ[k] Rb).toRingHom (fSplit i β (gPol Q i β a s)) *
        Polynomial.C (e s) := by
  rw [aPrime, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, theta_cOf, theta_tmul, map_one, map_one, one_mul]

end Inj

section Final

variable [IsDomain k] (i : I) (β : Multiset I) (a : I → Polynomial k)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "T" => KLRAlgebra k Q Si ⊗[k] KLRAlgebra k Q β
local notation "Rb" => KLRAlgebra k Q β
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "Pb" => MvPolynomial (Fin (Multiset.card β)) k

omit [DecidableEq I] [IsDomain k] in
theorem cons1_zero (s : Seq β) : (cons1 i β s).1 ⟨0, zero_lt_card_single_add i β⟩ = i := by
  rw [Seq.append_apply_lt _ _ _ (by simp)]
  exact Multiset.mem_singleton.1 ((default : Seq Si).mem _)

/-- Each factor of KK's `A` is a unit times a monic polynomial in `t`. -/
theorem umonic_gPol (hsym : ∀ a b, a ≠ b → Q b a = MvPolynomial.rename ![1, 0] (Q a b))
    (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) (ha : (a i).Monic)
    (s : Seq β) : UMonic (fSplit (k := k) i β (gPol Q i β a s)) := by
  rw [gPol, map_mul]
  refine UMonic.mul ?_ ?_
  · rw [cycA, cons1_zero]; exact umonic_fSplit_aeval i β ha
  · rw [cycF, map_prod]
    refine Finset.prod_induction _ UMonic (fun _ _ => UMonic.mul) (by
      rw [show (1 : Polynomial Pb) = 1 from rfl]; exact UMonic.of_monic Polynomial.monic_one) ?_
    intro b hb
    unfold cycFac
    by_cases hbm : b < Multiset.card (Si + β)
    · simp only [hbm, ↓reduceDIte]
      split_ifs with h1 h2
      · rw [map_neg, map_one]; exact UMonic.neg_one
      · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        rw [cons1_zero, fSplit_rename_vec2]
        have hne : i ≠ (cons1 i β s).1 ⟨b' + 1, hbm⟩ := by
          intro h; apply h2; rw [cons1_zero]; exact h.symm
        rw [hsym _ _ hne.symm, MvPolynomial.aeval_rename]
        have hcomp : (![Polynomial.X, Polynomial.C (MvPolynomial.X
            ⟨b', by rw [card_single_add] at hbm; omega⟩ : Pb)] ∘ ![(1 : Fin 2), 0]) =
            ![Polynomial.C (MvPolynomial.X ⟨b', by rw [card_single_add] at hbm; omega⟩ : Pb),
              Polynomial.X] := by
          funext c; fin_cases c <;> rfl
        rw [hcomp]
        exact umonic_aeval_Q (β := β) _ (hQ _ _ hne.symm) _
      · rw [map_one]; exact UMonic.of_monic Polynomial.monic_one
    · simp only [hbm, ↓reduceDIte, map_one]; exact UMonic.of_monic Polynomial.monic_one

/-- **KK Lemma 4.16** in the case at hand: right multiplication by `θ(A)` is injective modulo
polynomials with coefficients in the cyclotomic ideal `J` of `R(β)`. -/
theorem coeff_mem_of_mul_theta_aPrime
    (hsym : ∀ a b, a ≠ b → Q b a = MvPolynomial.rename ![1, 0] (Q a b))
    (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) (ha : (a i).Monic)
    (q : Polynomial Rb) (h : ∀ n, (q * theta Q i β (aPrime Q i β a)).coeff n ∈ cycIdeal Q a β) :
    ∀ n, q.coeff n ∈ cycIdeal Q a β := by
  set π : Polynomial Rb →+* Polynomial (CycKLR k Q a β) :=
    Polynomial.mapRingHom (CycKLR.mk k Q a β).toRingHom with hπ
  have hzero : ∀ p : Polynomial Rb, π p = 0 ↔ ∀ n, p.coeff n ∈ cycIdeal Q a β := by
    intro p
    rw [Polynomial.ext_iff]
    simp only [hπ, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_zero,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, CycKLR.mk_eq_zero_iff]
  have hcomm : ∀ (F : Polynomial Pb) (s : Seq β),
      Polynomial.map (pol : Pb →ₐ[k] Rb).toRingHom F * Polynomial.C (e s) =
        Polynomial.C (e s) * Polynomial.map (pol : Pb →ₐ[k] Rb).toRingHom F := fun F s =>
    Polynomial.ext fun n => by
      rw [Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, Polynomial.coeff_map]
      exact ((commute_e_pol s _).eq).symm
  have hs : ∀ s₀ : Seq β, π (q * Polynomial.C (e s₀)) = 0 := by
    intro s₀
    have h1 : theta Q i β (aPrime Q i β a) * Polynomial.C (e s₀) = Polynomial.C (e s₀) *
        Polynomial.map (pol : Pb →ₐ[k] Rb).toRingHom (fSplit i β (gPol Q i β a s₀)) := by
      rw [theta_aPrime, Finset.sum_mul, Finset.sum_eq_single s₀]
      · rw [mul_assoc, ← Polynomial.C_mul, e_mul_self, hcomm]
      · intro s _ hs; rw [mul_assoc, ← Polynomial.C_mul, e_mul_e, ite_eq_right hs, map_zero,
          mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    obtain ⟨u, M, hM, hF⟩ := umonic_gPol i β a hsym hQ ha s₀
    have h2 : π (q * Polynomial.C (e s₀)) * Polynomial.C (algebraMap k _ (u : k)) *
        Polynomial.map (CycKLR.mk k Q a β).toRingHom
          (Polynomial.map (pol : Pb →ₐ[k] Rb).toRingHom M) = 0 := by
      have := (hzero _).2 h
      rw [map_mul] at this
      have h3 := congrArg (· * π (Polynomial.C (e s₀))) this
      simp only [zero_mul] at h3
      rw [mul_assoc, ← map_mul, h1, hF, Polynomial.map_mul, Polynomial.map_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.algHom_C, ← mul_assoc, map_mul,
        map_mul, ← mul_assoc] at h3
      simpa [hπ, Polynomial.map_C, mul_assoc] using h3
    have hmon : (Polynomial.map (CycKLR.mk k Q a β).toRingHom
        (Polynomial.map (pol : Pb →ₐ[k] Rb).toRingHom M)).Monic := (hM.map _).map _
    rw [hmon.mul_left_eq_zero_iff] at h2
    have h4 := congrArg (· * Polynomial.C (algebraMap k (CycKLR k Q a β) ((u⁻¹ : kˣ) : k))) h2
    simp only [zero_mul] at h4
    rwa [mul_assoc, ← Polynomial.C_mul, ← map_mul, Units.mul_inv, map_one, Polynomial.C_1,
      mul_one] at h4
  have : π q = 0 := by
    rw [← mul_one q, ← Polynomial.C_1, ← sum_e, map_sum, Finset.mul_sum, map_sum]
    exact Finset.sum_eq_zero fun s _ => hs s
  exact (hzero q).1 this

variable {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

omit [DecidableEq I] [IsDomain k] in
include hPQ in
theorem sym_of_factor : ∀ a b, a ≠ b → Q b a = MvPolynomial.rename ![1, 0] (Q a b) := by
  intro a b hab
  rw [hPQ a b hab, hPQ b a hab.symm, map_mul, rename_swap_rename_swap, mul_comm]

include hPQ hP in
/-- **Right multiplication by KK's `A` is injective on `K_1 e(i, β)`**: if
`r 1_{i,β} A ∈ R a^Λ(x_2) R^1(β)` then `r 1_{i,β} ∈ R a^Λ(x_2) R^1(β)`. -/
theorem mem_cycL1_of_mul_aElt
    (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) (ha : (a i).Monic)
    (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) (r : R)
    (h : r * oneConcat Q Si β * aElt a (zero_lt_card_single_add i β) (Multiset.card β) ∈
      cycL1 a h1) : r * oneConcat Q Si β ∈ cycL1 a h1 := by
  have hsym := sym_of_factor hPQ
  obtain ⟨t, ht⟩ := rfree_span hPQ hP r
  rw [ht] at h ⊢
  have haElt : aElt a (zero_lt_card_single_add i β) (Multiset.card β) ∈
      subR1 (k := k) (Q := Q) (Si + β) :=
    Subalgebra.sum_mem _ fun s _ => Subalgebra.mul_mem _ (pol_mem_subR1 _) (e_mem_subR1 s)
  have hmul : rFree t * aElt a (zero_lt_card_single_add i β) (Multiset.card β) =
      rFree (fun u => t u * aPrime Q i β a) := by
    rw [← rFree_mul_oneConcat, mul_assoc, ← commute_oneConcat_subR1 i β haElt,
      aElt_mul_oneConcat, rFree, rFree, Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ => by rw [mul_assoc, ← concat_mul]
  rw [hmul, mem_cycL1_iff hPQ hP i β a h1 hβ] at h
  rw [mem_cycL1_iff hPQ hP i β a h1 hβ]
  intro u
  have hu := (mem_tJ_iff i β a _).1 (h u)
  rw [map_mul] at hu
  exact (mem_tJ_iff i β a _).2
    (coeff_mem_of_mul_theta_aPrime i β a hsym hQ ha _ hu)

include hPQ hP in
/-- **Kang–Kashiwara, Lemma 4.17** (injectivity of `P : K_1 → K_0`), on `K_1 e(i, β)`. -/
theorem pMap_injective_first
    (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) (ha : (a i).Monic)
    (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) (r : R)
    (h : pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β) (card_single_add i β).symm
      (Submodule.Quotient.mk (r * oneConcat Q Si β)) = 0) :
    (Submodule.Quotient.mk (r * oneConcat Q Si β) : KOne Q (Si + β) a h1) = 0 := by
  have hq := congrArg (qMap a (sym_of_factor hPQ) (zero_lt_card_single_add i β) h1
    (Multiset.card β) (card_single_add i β).symm) h
  rw [qMap_pMap, map_zero, Submodule.Quotient.mk_eq_zero] at hq
  rw [Submodule.Quotient.mk_eq_zero]
  exact mem_cycL1_of_mul_aElt i β a hPQ hP hQ ha h1 hβ r hq

end Final

end KLRAlgebra

end Categorification.KLR
