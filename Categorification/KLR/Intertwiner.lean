/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.BasisTheorem
import Categorification.KLR.BaseChange

/-!
# Intertwiners in KLR algebras

S.-J. Kang, M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4, §4.2: the elements `g_a` of (4.7) and
Lemma 4.12. They are variants of the intertwiners (KK Remark 4.11) and are used in KK's proof of
Theorem 4.7 (the exact sequence for the cyclotomic induction functor).

In the conventions of this library (`ψ_j x_j - x_{j+1} ψ_j = e` on equal labels, the opposite sign
to KK's `τ_a`), the element is

`g_j = ψ_j` on `e(𝐢)` with `i_j ≠ i_{j+1}`, and
`g_j = (x_{j+1} - x_j) + (x_{j+1} - x_j)² ψ_j` on `e(𝐢)` with `i_j = i_{j+1}`.

In the polynomial representation `g_j` acts by `f ↦ c(x_j, x_{j+1}) · s_j f`, where `c` is
`x_{j+1} - x_j` for equal labels and `P_{i_j i_{j+1}}` otherwise (`polyRep_gInt`). The relations
of KK Lemma 4.12 are first proved by computing in the polynomial representation, which is faithful
for a domain `k` and factorized `Q` (KL I Cor. 2.6, `polyRep_injective`); applying this to the
universal symmetric KLR data (`Categorification.KLR.BaseChange`) and specializing gives them over
any commutative ring, for any symmetric `Q` (KK's setting).

## Main definitions and results

* `KLRAlgebra.gInt j h` (KK's `g_{j+1}`, zero-indexed).
* `x_mul_gInt`: `x_{s_j(b)} g_j = g_j x_b` (KK Lemma 4.12, first identity).
* `ψ_mul_gInt_mul_gInt`: `ψ_j g_{j+1} g_j = g_{j+1} g_j ψ_{j+1}` (KK Lemma 4.12,
  second identity).
-/

namespace Categorification.KLR

open MvPolynomial TypeA Equiv PolyRep

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

/-! ### The intertwining operators on polynomials -/

section intOp

variable {n : ℕ} (P : I → I → MvPolynomial (Fin 2) k)

/-- The coefficient of the intertwiner for labels `a, b` at positions `p, q`:
`x_q - x_p` if `a = b`, and `P_{ab}(x_p, x_q)` otherwise. -/
noncomputable def intCoef (a b : I) (p q : Fin n) : MvPolynomial (Fin n) k :=
  if a = b then X q - X p else rename ![p, q] (P a b)

/-- The intertwining operator `f ↦ intCoef · s_{pq} f`. -/
noncomputable def intOp (a b : I) (p q : Fin n) :
    MvPolynomial (Fin n) k →ₗ[k] MvPolynomial (Fin n) k :=
  (LinearMap.mulLeft k (intCoef P a b p q)).comp (rename (swap p q)).toLinearMap

theorem intOp_apply (a b : I) (p q : Fin n) (g : MvPolynomial (Fin n) k) :
    intOp P a b p q g = intCoef P a b p q * rename (swap p q) g := rfl

theorem rename_intCoef {n' : ℕ} (σ : Fin n → Fin n') (a b : I) (p q : Fin n) :
    rename σ (intCoef P a b p q) = intCoef P a b (σ p) (σ q) := by
  unfold intCoef
  split_ifs
  · simp
  · exact rename_rename_vec2 σ p q _

/-- For equal labels, the intertwiner is `(x_q - x_p) + (x_q - x_p)² ∂_{pq}`. -/
theorem intOp_self {p q : Fin n} (hpq : p ≠ q) (a : I) (g : MvPolynomial (Fin n) k) :
    intOp P a a p q g = (X q - X p) * g + (X q - X p) ^ 2 * ddiff p q g := by
  have := ddiff_spec hpq g
  simp only [intOp_apply, intCoef, ↓reduceIte]
  linear_combination (X q - X p) * this

theorem intOp_of_ne {a b : I} (hab : a ≠ b) (p q : Fin n) (g : MvPolynomial (Fin n) k) :
    intOp P a b p q g = crossOp P a b p q g := by
  simp only [intOp_apply, intCoef, hab, ↓reduceIte, crossOp_of_ne P hab]

/-- **The braid relation for intertwiners**, on polynomials, for distinct positions `p, q, r`
carrying (in the output component) the labels `a, b, c`: the polynomial-representation form of
`ψ_j g_{j+1} g_j = g_{j+1} g_j ψ_{j+1}` (`ψ_mul_gInt_mul_gInt`). -/
theorem intOp_braid {p q r : Fin n} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) (a b c : I)
    (F : MvPolynomial (Fin n) k) :
    crossOp P b a p q (intOp P c a q r (intOp P c b p q F)) =
      intOp P c b q r (intOp P c a p q (crossOp P b a q r F)) := by
  have hqp := hpq.symm
  have hrq := hqr.symm
  have hrp := hpr.symm
  have hperm : (⇑(swap p q) ∘ ⇑(swap q r) ∘ ⇑(swap p q) : Fin n → Fin n) =
      ⇑(swap q r) ∘ ⇑(swap p q) ∘ ⇑(swap q r) := by
    have := congrArg (fun σ : Perm (Fin n) => (⇑σ : Fin n → Fin n)) (swap_braid hpq hqr hpr)
    simpa [Perm.coe_mul, Function.comp_assoc] using this
  have e1 : swap q r p = p := swap_apply_of_ne_of_ne hpq hpr
  have e2 : swap p q r = r := swap_apply_of_ne_of_ne hrp hrq
  have hvec : ∀ g : Fin n → Fin n, ∀ u v : Fin n, g ∘ ![u, v] = ![g u, g v] := fun g u v => by
    funext t; fin_cases t <;> rfl
  by_cases hab : b = a
  · subst hab
    rw [crossOp_self, crossOp_self]
    simp only [intOp_apply, map_mul, rename_rename, rename_intCoef, swap_apply_left, e1]
    have hsym : rename (swap p q) (intCoef P c b q r * intCoef P c b p r) =
        intCoef P c b q r * intCoef P c b p r := by
      simp only [map_mul, rename_intCoef, swap_apply_left, swap_apply_right, e2]
      ring
    rw [← mul_assoc, ddiff_mul_of_rename_eq hpq hsym,
      rename_ddiff ((swap q r).injective.comp (swap p q).injective) hqr]
    simp only [Function.comp_apply, swap_apply_right, e1, e2]
    ring
  · rw [crossOp_of_ne P hab, crossOp_of_ne P hab]
    simp only [intOp_apply, map_mul, rename_rename, rename_intCoef, hvec, swap_apply_left,
      swap_apply_right, e1, e2]
    rw [hperm]
    ring

end intOp

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν

/-- **The element `g_j`** (KK (4.7), zero-indexed: KK's `g_{j+1}`): `ψ_j` on `e(𝐢)` with
`i_j ≠ i_{j+1}`, and `(x_{j+1} - x_j) + (x_{j+1} - x_j)² ψ_j` on `e(𝐢)` with `i_j = i_{j+1}`. -/
noncomputable def gInt (j : ℕ) (h : j + 1 < m) : KLRAlgebra k Q ν :=
  ∑ i : Seq ν, (if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then
      (x ⟨j + 1, h⟩ - x ⟨j, by omega⟩) + (x ⟨j + 1, h⟩ - x ⟨j, by omega⟩) ^ 2 * ψ j
    else ψ j) * e i

end KLRAlgebra

open KLRAlgebra

section factor

variable {P Q : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b)) {ν : Multiset I}

local notation "m" => Multiset.card ν

/-- **`g_j` in the polynomial representation**: the component `t` of `g_j f` is the intertwiner
(for the labels of `s_j t`) applied to `f (s_j t)`. -/
theorem polyRep_gInt (j : ℕ) (h : j + 1 < m) (f : Pol k ν) (t : Seq ν) :
    polyRep hPQ (gInt j h) f t =
      intOp P (t.1 ⟨j + 1, h⟩) (t.1 ⟨j, by omega⟩) ⟨j, by omega⟩ ⟨j + 1, h⟩
        (f (swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩ • t)) := by
  set p : Fin m := ⟨j, by omega⟩
  set q : Fin m := ⟨j + 1, h⟩
  have hpq : p ≠ q := fun e => by simp [p, q, Fin.ext_iff] at e
  have hΨ : ∀ g : Pol k ν, opΨ P j g t = crossOp P (t.1 q) (t.1 p) p q (g (swap p q • t)) :=
    fun g => opΨ_apply_of_eq P (j := j) (p := p) (q := q) rfl rfl g t
  have hX : ∀ (g : Pol k ν) (u : Seq ν),
      ((opX q - opX p : Module.End k (Pol k ν)) g) u = (X q - X p) * g u := fun g u => by
    simp only [LinearMap.sub_apply, Pi.sub_apply, opX_apply, sub_mul]
  have hX2 : ∀ (g : Pol k ν) (u : Seq ν),
      (((opX q - opX p) ^ 2 : Module.End k (Pol k ν)) g) u = (X q - X p) ^ 2 * g u :=
    fun g u => by rw [sq, Module.End.mul_apply, hX, hX, sq, mul_assoc]
  simp only [gInt, map_sum, map_mul]
  rw [LinearMap.sum_apply, Finset.sum_apply, Finset.sum_eq_single (swap p q • t)]
  · rw [Module.End.mul_apply, polyRep_e]
    split_ifs with hc'
    · change (swap p q • t).1 p = (swap p q • t).1 q at hc'
      rw [swap_smul_apply, swap_smul_apply, swap_apply_left, swap_apply_right] at hc'
      have hst : swap p q • t = t := swap_smul_eq_self hc'.symm
      rw [map_add, map_mul, map_pow, map_sub, polyRep_x, polyRep_x, polyRep_ψ, LinearMap.add_apply,
        Pi.add_apply, hX, Module.End.mul_apply, hX2, hΨ, opE_apply, opE_apply, hst,
        ite_eq_left rfl]
      have key : ∀ (A B : I), A = B → ∀ g, (X q - X p) * g + (X q - X p) ^ 2 * crossOp P A B p q g =
          intOp P A B p q g := by
        rintro A B rfl g; rw [crossOp_self, intOp_self P hpq]
      exact key _ _ hc' _
    · change ¬ (swap p q • t).1 p = (swap p q • t).1 q at hc'
      rw [swap_smul_apply, swap_smul_apply, swap_apply_left, swap_apply_right] at hc'
      rw [polyRep_ψ, hΨ, opE_apply, ite_eq_left rfl, intOp_of_ne P hc']
  · intro i _ hi
    rw [Module.End.mul_apply, polyRep_e]
    split_ifs with hc'
    · change i.1 p = i.1 q at hc'
      have hti : t ≠ i := by
        rintro rfl; exact hi (swap_smul_eq_self hc').symm
      rw [map_add, map_mul, map_pow, map_sub, polyRep_x, polyRep_x, polyRep_ψ, LinearMap.add_apply,
        Pi.add_apply, hX, Module.End.mul_apply, hX2, hΨ, opE_apply, opE_apply,
        ite_eq_right hti, ite_eq_right (Ne.symm hi)]
      simp
    · rw [polyRep_ψ, hΨ, opE_apply, ite_eq_right (Ne.symm hi)]
      simp
  · intro h'; exact absurd (Finset.mem_univ _) h'

variable (hP : ∀ a b, a ≠ b → P a b ≠ 0) [IsDomain k]

include hPQ hP in
/-- Kang–Kashiwara, Lemma 4.12, first identity, for factorized `Q` over a domain (via the faithful
polynomial representation). See `x_mul_gInt` for arbitrary rings. -/
theorem x_mul_gInt_of_factor (j : ℕ) (h : j + 1 < m) (b : Fin m) :
    (x (swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩ b) * gInt j h : KLRAlgebra k Q ν) =
      gInt j h * x b := by
  apply polyRep_injective hPQ hP
  refine LinearMap.ext fun f => funext fun t => ?_
  simp only [map_mul, Module.End.mul_apply, polyRep_x, opX_apply, polyRep_gInt hPQ, intOp_apply,
    map_mul, rename_X]
  ring

include hPQ hP in
/-- Kang–Kashiwara, Lemma 4.12, second identity, for factorized `Q` over a domain (via the
faithful polynomial representation). See `ψ_mul_gInt_mul_gInt` for arbitrary rings. -/
theorem ψ_mul_gInt_mul_gInt_of_factor (j : ℕ) (h : j + 2 < m) :
    (ψ j * gInt (j + 1) h * gInt j (by omega) : KLRAlgebra k Q ν) =
      gInt (j + 1) h * gInt j (by omega) * ψ (j + 1) := by
  apply polyRep_injective hPQ hP
  set p : Fin m := ⟨j, by omega⟩
  set q : Fin m := ⟨j + 1, by omega⟩
  set r : Fin m := ⟨j + 2, h⟩
  have hpq : p ≠ q := fun e => by simp [p, q, Fin.ext_iff] at e
  have hqr : q ≠ r := fun e => by simp [q, r, Fin.ext_iff] at e
  have hpr : p ≠ r := fun e => by simp [p, r, Fin.ext_iff] at e
  have e1 : swap q r p = p := swap_apply_of_ne_of_ne hpq hpr
  have e2 : swap p q r = r := swap_apply_of_ne_of_ne hpr.symm hqr.symm
  have hΨ0 : ∀ (g : Pol k ν) (t : Seq ν),
      opΨ P j g t = crossOp P (t.1 q) (t.1 p) p q (g (swap p q • t)) :=
    fun g t => opΨ_apply_of_eq P (j := j) (p := p) (q := q) rfl rfl g t
  have hΨ1 : ∀ (g : Pol k ν) (t : Seq ν),
      opΨ P (j + 1) g t = crossOp P (t.1 r) (t.1 q) q r (g (swap q r • t)) :=
    fun g t => opΨ_apply_of_eq P (j := j + 1) (p := q) (q := r) rfl rfl g t
  have hG0 : ∀ (g : Pol k ν) (t : Seq ν), polyRep hPQ (gInt j (by omega) : KLRAlgebra k Q ν) g t =
      intOp P (t.1 q) (t.1 p) p q (g (swap p q • t)) := fun g t => polyRep_gInt hPQ j _ g t
  have hG1 : ∀ (g : Pol k ν) (t : Seq ν), polyRep hPQ (gInt (j + 1) h : KLRAlgebra k Q ν) g t =
      intOp P (t.1 r) (t.1 q) q r (g (swap q r • t)) := fun g t => polyRep_gInt hPQ (j + 1) h g t
  refine LinearMap.ext fun f => funext fun t => ?_
  simp only [map_mul, Module.End.mul_apply, polyRep_ψ, hΨ0, hΨ1, hG0, hG1, swap_smul_apply,
    swap_apply_left, swap_apply_right, e1, e2]
  have hseq : swap p q • swap q r • swap p q • t = swap q r • swap p q • swap q r • t := by
    simp only [smul_smul]
    rw [← mul_assoc, ← mul_assoc, swap_braid hpq hqr hpr]
  rw [hseq]
  exact intOp_braid P hpq hqr hpr _ _ _ _

end factor

/-! ### Kang–Kashiwara Lemma 4.12 over an arbitrary commutative ring

Both identities are equalities between expressions in the generators, so they follow from the
case of the universal symmetric KLR data over the domain `UnivRing I` (where the polynomial
representation is faithful) by base change (`KLRAlgebra.mapRingHom`). -/

section general

theorem KLRAlgebra.mapRingHom_gInt {k' : Type*} [CommRing k'] (φ : k →+* k')
    {Q : I → I → MvPolynomial (Fin 2) k} {Q' : I → I → MvPolynomial (Fin 2) k'}
    (hQ : ∀ a b, a ≠ b → MvPolynomial.map φ (Q a b) = Q' a b) {ν : Multiset I} (j : ℕ)
    (h : j + 1 < Multiset.card ν) :
    mapRingHom φ hQ (gInt j h : KLRAlgebra k Q ν) = gInt j h := by
  simp only [gInt, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

variable {Q : I → I → MvPolynomial (Fin 2) k}
  (hsym : ∀ a b, a ≠ b → Q b a = rename ![1, 0] (Q a b)) {ν : Multiset I}

local notation "m" => Multiset.card ν

include hsym in
/-- **Kang–Kashiwara, Lemma 4.12**, first identity: `x_{s_j(b)} g_j = g_j x_b`, over any
commutative ring, for symmetric `Q` (`Q_{ba}(u, v) = Q_{ab}(v, u)`, as in KK (2.1)). -/
theorem x_mul_gInt (j : ℕ) (h : j + 1 < m) (b : Fin m) :
    (x (swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩ b) * gInt j h : KLRAlgebra k Q ν) =
      gInt j h * x b := by
  have h0 := x_mul_gInt_of_factor (k := UnivRing I) (P := univP Q) (Q := univQ Q) (ν := ν)
    (univQ_factor Q) (fun a b _ => univP_ne_zero Q a b) j h b
  have := congrArg (mapRingHom (univMap Q) (map_univQ Q hsym)) h0
  simpa only [map_mul, mapRingHom_x, mapRingHom_gInt] using this

include hsym in
/-- **Kang–Kashiwara, Lemma 4.12**, second identity: `ψ_j g_{j+1} g_j = g_{j+1} g_j ψ_{j+1}`,
over any commutative ring, for symmetric `Q`. -/
theorem ψ_mul_gInt_mul_gInt (j : ℕ) (h : j + 2 < m) :
    (ψ j * gInt (j + 1) h * gInt j (by omega) : KLRAlgebra k Q ν) =
      gInt (j + 1) h * gInt j (by omega) * ψ (j + 1) := by
  have h0 := ψ_mul_gInt_mul_gInt_of_factor (k := UnivRing I) (P := univP Q) (Q := univQ Q)
    (ν := ν) (univQ_factor Q) (fun a b _ => univP_ne_zero Q a b) j h
  have := congrArg (mapRingHom (univMap Q) (map_univQ Q hsym)) h0
  simpa only [map_mul, mapRingHom_ψ, mapRingHom_gInt] using this

end general

end Categorification.KLR
