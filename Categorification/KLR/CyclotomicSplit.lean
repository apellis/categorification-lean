/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicDiv

/-!
# `P : K_1 → K_0` is split injective as a map of right `R(β)`-modules

S.-J. Kang, M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4, §4.2. For `ν = {i} + β`:

* `cL b` (`b` on the first `n` strands, colour `i` on the last) and `cR b` (`b` on the last `n`
  strands, colour `i` on the first) are the two embeddings of `R(β)` into `R(ν)`; they give the
  right `R(β)`-module structures of `K_0` and `K_1` (`act0`, `act1`).
* `cL_mul_gProd`: `cL b · G = G · cR b` exactly (KK Props. 4.13, 4.14), so `Q : K_0 → K_1` is
  right `R(β)`-linear (`qMap_act`); `cR_mul_tauW_sub_mem`: `cR b · P̃ ≡ P̃ · cL b` modulo
  `R(ν) a^Λ(x_1) R(β)` (KK's lemma after (4.6)), so `P` is right `R(β)`-linear (`pMap_act`).
* `splitMap`: a right `R(β)`-linear left inverse of `P` on `K_1 e(i, β)` (`splitMap_pMap`,
  `splitMap_act`). It is `Q` followed by division by the central monic polynomial `M` of
  `θ(A) = λ M` in the coordinates `K_1 e(i, β) ≅ ⊕_{shuffles} R^Λ(β)[t]` (KK Lemma 4.19 with
  `h = Q`, using KK Thm. 4.15 `Q ∘ P = A`). Hence `0 → K_1 e(i, β) → K_0 → F^Λ → 0`
  (`range_pMap`) splits as a sequence of right `R(β)`-modules.

Domain `k`, factorized `Q` with unit leading coefficients, monic `a_i` (as for KK's Lemma 4.16).
-/

namespace Categorification.KLR

open Equiv TypeA PolyRep
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k}

/-- Induction over the generators of a KLR algebra. -/
theorem klr_induction {ν : Multiset I} {p : KLRAlgebra k Q ν → Prop}
    (hadd : ∀ u v, p u → p v → p (u + v)) (hmul : ∀ u v, p u → p v → p (u * v))
    (hr : ∀ r : k, p (algebraMap k _ r)) (he : ∀ s, p (e s)) (hx : ∀ b, p (x b))
    (hψ : ∀ j, p (ψ j)) (b : KLRAlgebra k Q ν) : p b := by
  obtain ⟨w, rfl⟩ := mk_surjective b
  induction w using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact hr r
  | grade1 g =>
    cases g with
    | idem s => exact he s
    | dot b => exact hx b
    | cross j => exact hψ j
  | mul u v hu hv => rw [map_mul]; exact hmul _ _ hu hv
  | add u v hu hv => rw [map_add]; exact hadd _ _ hu hv

section Embed

variable (i : I) (β : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "T" => KLRAlgebra k Q Si ⊗[k] KLRAlgebra k Q β
local notation "Rb" => KLRAlgebra k Q β
local notation "R" => KLRAlgebra k Q (Si + β)

variable (Q) in
/-- `b ↦ b ⊗ 1_i` on the first `n` strands of `R({i} + β)`. -/
noncomputable def cL (b : Rb) : R := castKLR Q (add_comm β Si) (concat Q β Si (b ⊗ₜ 1))

variable (Q) in
/-- `b ↦ 1_i ⊗ b` on the last `n` strands of `R({i} + β)`. -/
noncomputable def cR (b : Rb) : R := concat Q Si β (1 ⊗ₜ b)

theorem cL_mul (u v : Rb) : cL Q i β (u * v) = cL Q i β u * cL Q i β v := by
  rw [cL, cL, cL, ← map_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem cR_mul (u v : Rb) : cR Q i β (u * v) = cR Q i β u * cR Q i β v := by
  rw [cR, cR, cR, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem cL_add (u v : Rb) : cL Q i β (u + v) = cL Q i β u + cL Q i β v := by
  rw [cL, cL, cL, TensorProduct.add_tmul, map_add, map_add]

theorem cR_add (u v : Rb) : cR Q i β (u + v) = cR Q i β u + cR Q i β v := by
  rw [cR, cR, cR, TensorProduct.tmul_add, map_add]

theorem cL_smul (r : k) (u : Rb) : cL Q i β (r • u) = r • cL Q i β u := by
  rw [cL, cL, ← TensorProduct.smul_tmul', map_smul, map_smul]

theorem cR_smul (r : k) (u : Rb) : cR Q i β (r • u) = r • cR Q i β u := by
  rw [cR, cR, TensorProduct.tmul_smul, map_smul]

theorem cL_zero : cL Q i β 0 = 0 := by
  rw [← zero_smul k (0 : Rb), cL_smul, zero_smul]

theorem cR_zero : cR Q i β 0 = 0 := by
  rw [← zero_smul k (0 : Rb), cR_smul, zero_smul]

theorem cR_one : cR Q i β 1 = oneConcat Q Si β := concat_one_tmul_one

omit [DecidableEq I] in
/-- `c_n` moves the first strand to the end: `c_n (i 𝐢') = 𝐢' i`. -/
theorem cP_smul_cons1 (s : Seq β) :
    cP (Multiset.card (Si + β)) (Multiset.card β) • cons1 i β s =
      Seq.cast (add_comm β Si) (s.append default) := by
  apply Subtype.ext
  funext c
  rw [Seq.smul_apply, Seq.cast_apply]
  have hm := card_single_add i β
  have hc : c.val < Multiset.card β + 1 := lt_of_lt_of_eq c.2 hm
  have hv := cP_symm_val (Multiset.card (Si + β)) (Multiset.card β) (by omega) c
  by_cases h : c.val < Multiset.card β
  · have hcP : (cP (Multiset.card (Si + β)) (Multiset.card β)).symm c =
        ⟨c.val + 1, by omega⟩ := Fin.ext (by rw [hv]; simp [h])
    rw [hcP, cons1_succ, Seq.append_apply_lt _ _ _ (by simp only [Fin.val_cast]; exact h)]
    rfl
  · have hcP : (cP (Multiset.card (Si + β)) (Multiset.card β)).symm c =
        ⟨0, zero_lt_card_single_add i β⟩ :=
      Fin.ext (by rw [hv]; simp [show c.val = Multiset.card β by omega])
    rw [hcP, cons1_zero, Seq.append_apply_ge _ _ _ (by simp only [Fin.val_cast]; omega)]
    exact (Multiset.mem_singleton.1 (Seq.mem _ _)).symm

theorem cL_one : cL Q i β 1 = ∑ s : Seq β, e (Seq.cast (add_comm β Si) (s.append default)) := by
  rw [cL, concat_one_tmul_one, oneConcat_eq', map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_unique, castKLR_e]

theorem cR_one_eq : cR Q i β 1 = ∑ s : Seq β, e (cons1 i β s) := by
  rw [cR_one, oneConcat_single_eq]

theorem cL_e (s : Seq β) : cL Q i β (e s) = e (Seq.cast (add_comm β Si) (s.append default)) := by
  rw [cL, ← e_single (k := k) (Q := Q) i default, concat_e_tmul_e, castKLR_e]

theorem cR_e (s : Seq β) : cR Q i β (e s) = e (cons1 i β s) := by
  rw [cR, ← e_single (k := k) (Q := Q) i default, concat_e_tmul_e]

theorem cL_x (b : Fin (Multiset.card β)) :
    cL Q i β (x b) =
      x (Fin.cast (congrArg Multiset.card (add_comm β Si)) (Seq.posL Si b)) * cL Q i β 1 := by
  rw [cL, concat_x_tmul_one, map_mul, castKLR_x, cL, concat_one_tmul_one]

theorem cR_x (b : Fin (Multiset.card β)) : cR Q i β (x b) = x (Seq.posR Si b) * cR Q i β 1 := by
  rw [cR, concat_one_tmul_x, cR_one]

theorem cL_ψ {j : ℕ} (hj : j + 1 < Multiset.card β) : cL Q i β (ψ j) = ψ j * cL Q i β 1 := by
  rw [cL, concat_ψ_tmul_one hj, map_mul, castKLR_ψ, cL, concat_one_tmul_one]

theorem cR_ψ {j : ℕ} (hj : j + 1 < Multiset.card β) : cR Q i β (ψ j) = ψ (j + 1) * cR Q i β 1 := by
  rw [cR, concat_one_tmul_ψ hj, cR_one,
    show Multiset.card Si + j = j + 1 by rw [Multiset.card_singleton, add_comm]]

theorem cL_one_mem_subR0 : cL Q i β 1 ∈ subR0 (k := k) (Q := Q) (Si + β) := by
  rw [cL_one]; exact Subalgebra.sum_mem _ fun s _ => e_mem_subR0 _

theorem cL_mem_subR0 (b : Rb) : cL Q i β b ∈ subR0 (k := k) (Q := Q) (Si + β) := by
  induction b using klr_induction with
  | hadd u v hu hv => rw [cL_add]; exact Subalgebra.add_mem _ hu hv
  | hmul u v hu hv => rw [cL_mul]; exact Subalgebra.mul_mem _ hu hv
  | hr r =>
    rw [Algebra.algebraMap_eq_smul_one, cL_smul]
    exact Subalgebra.smul_mem _ (cL_one_mem_subR0 i β) r
  | he s => rw [cL_e]; exact e_mem_subR0 _
  | hx b => rw [cL_x]; exact Subalgebra.mul_mem _ (x_mem_subR0 _) (cL_one_mem_subR0 i β)
  | hψ j =>
    by_cases hj : j + 1 < Multiset.card β
    · rw [cL_ψ i β hj]
      exact Subalgebra.mul_mem _ (ψ_mem_subR0 (by rw [card_single_add]; omega))
        (cL_one_mem_subR0 i β)
    · rw [ψ_eq_zero j (by omega), cL_zero]; exact Subalgebra.zero_mem _

theorem cR_mem_subR1 (b : Rb) : cR Q i β b ∈ subR1 (k := k) (Q := Q) (Si + β) :=
  concat_one_tmul_mem_subR1 i β b

/-! #### `G = g_{n-1} ⋯ g_0` intertwines `cL` and `cR` -/

section G

variable (hsym : ∀ a b, a ≠ b → Q b a = MvPolynomial.rename ![1, 0] (Q a b))

include hsym in
/-- **KK Props. 4.13, 4.14** (exact form): `cL b · G = G · cR b`. -/
theorem cL_mul_gProd (b : Rb) :
    cL Q i β b * gProd (Multiset.card β) = gProd (Multiset.card β) * cR Q i β b := by
  have hlt : Multiset.card β < Multiset.card (Si + β) := by rw [card_single_add]; omega
  have he' : ∀ s : Seq β, (e (Seq.cast (add_comm β Si) (s.append default)) : R) *
      gProd (Multiset.card β) = gProd (Multiset.card β) * e (cons1 i β s) := fun s => by
    rw [gProd_mul_e _ hlt, cP_smul_cons1]
  have hone : cL Q i β 1 * gProd (Multiset.card β) = gProd (Multiset.card β) * cR Q i β 1 := by
    rw [cL_one, cR_one_eq, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => he' s
  induction b using klr_induction with
  | hadd u v hu hv => rw [cL_add, cR_add, add_mul, mul_add, hu, hv]
  | hmul u v hu hv => rw [cL_mul, cR_mul, mul_assoc, hv, ← mul_assoc, hu, mul_assoc]
  | hr r =>
    rw [Algebra.algebraMap_eq_smul_one, cL_smul, cR_smul, smul_mul_assoc, mul_smul_comm, hone]
  | he s => rw [cL_e, cR_e, he']
  | hx b =>
    rw [cL_x, cR_x, mul_assoc, hone, ← mul_assoc, ← mul_assoc, ← pol_X,
      pol_mul_gProd hsym _ hlt, MvPolynomial.rename_X, pol_X]
    congr 3
    apply Fin.ext
    rw [cP_symm_val _ _ hlt]
    simp only [Fin.val_cast, Seq.posL_val, Seq.posR_val, b.2, ↓reduceIte, Multiset.card_singleton]
    omega
  | hψ j =>
    by_cases hj : j + 1 < Multiset.card β
    · rw [cL_ψ i β hj, cR_ψ i β hj, mul_assoc, hone, ← mul_assoc, ← mul_assoc]
      have := ψ_mul_gProd_shift hsym (ν := Si + β) j (Multiset.card β - (j + 2))
        (by rw [card_single_add]; omega)
      rw [show j + 2 + (Multiset.card β - (j + 2)) = Multiset.card β by omega] at this
      rw [this]
    · rw [ψ_eq_zero j (by omega), cL_zero, cR_zero, zero_mul, mul_zero]

end G

/-! #### `P̃ = a^Λ(x_1) ψ_0 ⋯ ψ_{n-1}` intertwines `cR` and `cL` modulo `R(ν) a^Λ(x_1) R(β)` -/

section Ptilde

variable (a : I → Polynomial k)

/-- KK's lemma after (4.6) (`P̃` is right `R(β)`-linear): `cR b · P̃ ≡ P̃ · cL b`. -/
theorem cR_mul_tauW_sub_mem (b : Rb) :
    cR Q i β b * tauW a (zero_lt_card_single_add i β) (Multiset.card β) -
        tauW a (zero_lt_card_single_add i β) (Multiset.card β) * cL Q i β b ∈
      cycL0 a (zero_lt_card_single_add i β) := by
  set τ := (tauW a (zero_lt_card_single_add i β) (Multiset.card β) : R) with hτ
  have hn : Multiset.card β + 1 = Multiset.card (Si + β) := (card_single_add i β).symm
  have he' : ∀ s : Seq β, (e (cons1 i β s) : R) * τ =
      τ * e (Seq.cast (add_comm β Si) (s.append default)) := fun s => by
    rw [hτ, e_mul_tauW, cP_smul_cons1]
  have hone : cR Q i β 1 * τ = τ * cL Q i β 1 := by
    rw [cL_one, cR_one_eq, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => he' s
  induction b using klr_induction with
  | hadd u v hu hv =>
    rw [cR_add, cL_add, add_mul, mul_add, add_sub_add_comm]
    exact Submodule.add_mem _ hu hv
  | hmul u v hu hv =>
    have : cR Q i β u * cR Q i β v * τ - τ * (cL Q i β u * cL Q i β v) =
        cR Q i β u * (cR Q i β v * τ - τ * cL Q i β v) +
          (cR Q i β u * τ - τ * cL Q i β u) * cL Q i β v := by noncomm_ring
    rw [cR_mul, cL_mul, this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hv)
      (mul_mem_cycL0 a hu (cL_mem_subR0 i β v))
  | hr r =>
    rw [Algebra.algebraMap_eq_smul_one, cL_smul, cR_smul, smul_mul_assoc, mul_smul_comm, hone,
      sub_self]
    exact Submodule.zero_mem _
  | he s => rw [cR_e, cL_e, he', sub_self]; exact Submodule.zero_mem _
  | hx b =>
    have hc : cP (Multiset.card (Si + β)) (Multiset.card β) (Seq.posR Si b) =
        Fin.cast (congrArg Multiset.card (add_comm β Si)) (Seq.posL Si b) := by
      have := cP_apply_pos (ν := Si + β) (Multiset.card β) hn (b.val + 1) (by omega)
        (by have := b.2; omega)
      apply Fin.ext
      rw [show Seq.posR Si b = ⟨b.val + 1, by rw [card_single_add]; omega⟩ from
        Fin.ext (by simp [add_comm]), this]
      simp only [Fin.val_cast, Seq.posL_val, Nat.add_sub_cancel]
    rw [cR_x, cL_x, mul_assoc, hone, ← mul_assoc, ← mul_assoc, ← sub_mul, ← hc]
    exact mul_mem_cycL0 a (x_mul_tauW' a _ _ hn _) (cL_one_mem_subR0 i β)
  | hψ j =>
    by_cases hj : j + 1 < Multiset.card β
    · rw [cR_ψ i β hj, cL_ψ i β hj, mul_assoc, hone, ← mul_assoc, ← mul_assoc, ← sub_mul]
      have := ψ_mul_tauW (Q := Q) a (zero_lt_card_single_add i β) (Multiset.card β) hn (j + 1)
        (by omega) (by omega)
      rw [Nat.add_sub_cancel] at this
      exact mul_mem_cycL0 a this (cL_one_mem_subR0 i β)
    · rw [ψ_eq_zero j (by omega), cL_zero, cR_zero, zero_mul, mul_zero, sub_self]
      exact Submodule.zero_mem _

end Ptilde

end Embed


/-! ### Right module structures, right linearity of `P` and `Q` -/

section Act

variable (i : I) (β : Multiset I) (a : I → Polynomial k)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rb" => KLRAlgebra k Q β
local notation "R" => KLRAlgebra k Q (Si + β)

variable (Q) in
/-- The right action of `b ∈ R(β)` on `K_0`: right multiplication by `cL b`. -/
noncomputable def act0 (b : Rb) :
    KZero Q (Si + β) a (zero_lt_card_single_add i β) →ₗ[R]
      KZero Q (Si + β) a (zero_lt_card_single_add i β) :=
  (cycL0 a _).mapQ (cycL0 a _) (LinearMap.toSpanSingleton R R (cL Q i β b))
    (fun _ hz => mul_mem_cycL0 a hz (cL_mem_subR0 i β b))

variable (Q) in
/-- The right action of `b ∈ R(β)` on `K_1`: right multiplication by `cR b`. -/
noncomputable def act1 (h1 : 1 < Multiset.card (Si + β)) (b : Rb) :
    KOne Q (Si + β) a h1 →ₗ[R] KOne Q (Si + β) a h1 :=
  (cycL1 a h1).mapQ (cycL1 a h1) (LinearMap.toSpanSingleton R R (cR Q i β b))
    (fun _ hz => mul_mem_cycL1 a hz (cR_mem_subR1 i β b))

theorem act0_mk (b : Rb) (y : R) :
    act0 Q i β a b (Submodule.Quotient.mk y) = Submodule.Quotient.mk (y * cL Q i β b) := rfl

theorem act1_mk (h1 : 1 < Multiset.card (Si + β)) (b : Rb) (y : R) :
    act1 Q i β a h1 b (Submodule.Quotient.mk y) = Submodule.Quotient.mk (y * cR Q i β b) := rfl

/-- **KK's lemma after (4.6)**: `P : K_1 → K_0` is right `R(β)`-linear. -/
theorem pMap_act (h1 : 1 < Multiset.card (Si + β)) (b : Rb)
    (z : KOne Q (Si + β) a h1) :
    pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β) (card_single_add i β).symm
        (act1 Q i β a h1 b z) =
      act0 Q i β a b (pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β)
        (card_single_add i β).symm z) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [act1_mk, pMap_mk, pMap_mk, act0_mk, Submodule.Quotient.eq, mul_assoc, mul_assoc, ← mul_sub]
  exact Submodule.smul_mem _ y (cR_mul_tauW_sub_mem i β a b)

/-- **KK Props. 4.13, 4.14**: `Q : K_0 → K_1` is right `R(β)`-linear. -/
theorem qMap_act (hsym : ∀ a b, a ≠ b → Q b a = MvPolynomial.rename ![1, 0] (Q a b))
    (h1 : 1 < Multiset.card (Si + β)) (b : Rb)
    (z : KZero Q (Si + β) a (zero_lt_card_single_add i β)) :
    qMap a hsym (zero_lt_card_single_add i β) h1 (Multiset.card β) (card_single_add i β).symm
        (act0 Q i β a b z) =
      act1 Q i β a h1 b (qMap a hsym (zero_lt_card_single_add i β) h1 (Multiset.card β)
        (card_single_add i β).symm z) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [act0_mk, qMap_mk, qMap_mk, act1_mk, mul_assoc, cL_mul_gProd i β hsym, mul_assoc]

end Act

/-! ### The splitting -/

section Split

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (i : I) (β : Multiset I) (a : I → Polynomial k)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "T" => KLRAlgebra k Q Si ⊗[k] KLRAlgebra k Q β
local notation "Rb" => KLRAlgebra k Q β
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "Rl" => CycKLR k Q a β
local notation "Sh" => Shuffle (Seq.card_add' Si β)

omit [IsDomain k] in
theorem rFree_smul (c : k) (t : Sh → T) : rFree (c • t) = c • rFree t := by
  simp only [rFree, Pi.smul_apply, map_smul, mul_smul_comm, Finset.smul_sum]

omit [IsDomain k] in
theorem rFree_mul_concat (t : Sh → T) (c : T) :
    rFree t * concat Q Si β c = rFree (fun u => t u * c) := by
  simp only [rFree, Finset.sum_mul, mul_assoc, concat_mul]

variable (Q) in
/-- `R(i) ⊗ R(β) → R^Λ(β)[t]`. -/
noncomputable def thetaL : T →ₐ[k] Polynomial Rl :=
  (Polynomial.mapAlgHom (CycKLR.mk k Q a β)).comp (theta Q i β)

omit [IsDomain k] in
theorem thetaL_surjective : Function.Surjective (thetaL Q i β a) := by
  intro q
  obtain ⟨q', rfl⟩ := Polynomial.map_surjective (CycKLR.mk k Q a β : Rb →+* Rl)
    (CycKLR.mk_surjective) q
  exact ⟨thetaInv Q i β q', by rw [thetaL, AlgHom.comp_apply, theta_thetaInv]; rfl⟩

omit [IsDomain k] in
theorem thetaL_eq_zero_iff (t : T) : thetaL Q i β a t = 0 ↔ t ∈ tJ (Q := Q) i β a := by
  rw [mem_tJ_iff i β a t, thetaL, AlgHom.comp_apply, Polynomial.coe_mapAlgHom, Polynomial.ext_iff]
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero, RingHom.coe_coe, CycKLR.mk_eq_zero_iff]

omit [IsDomain k] in
theorem thetaL_one_tmul (b : Rb) :
    thetaL Q i β a (1 ⊗ₜ b) = Polynomial.C (CycKLR.mk k Q a β b) := by
  rw [thetaL, AlgHom.comp_apply, theta_tmul, map_one, map_one, one_mul, Polynomial.coe_mapAlgHom,
    Polynomial.map_C]
  rfl

variable (Q) in
/-- The coefficients `t` of `z 1_{i,β} = ∑_u ψ(ŵ_u) ι(t_u)`. -/
noncomputable def tco (z : R) : Sh → T := (rfree_span hPQ hP z).choose

theorem tco_spec (z : R) : z * oneConcat Q Si β = rFree (tco Q hPQ hP i β z) :=
  (rfree_span hPQ hP z).choose_spec

theorem tco_eq {z : R} {t : Sh → T} (h : z * oneConcat Q Si β = rFree t) :
    tco Q hPQ hP i β z = t := by
  funext u
  have := rfree_injective hPQ hP (t := tco Q hPQ hP i β z - t)
    (by rw [rFree_sub, ← tco_spec hPQ hP i β z, h, sub_self]) u
  rwa [Pi.sub_apply, sub_eq_zero] at this

variable (Q) in
/-- The coordinates of `z 1_{i,β}` in `⊕_u R^Λ(β)[t]`. -/
noncomputable def coordR : R →ₗ[k] (Sh → Polynomial Rl) where
  toFun z u := thetaL Q i β a (tco Q hPQ hP i β z u)
  map_add' z z' := by
    have : tco Q hPQ hP i β (z + z') = tco Q hPQ hP i β z + tco Q hPQ hP i β z' :=
      tco_eq hPQ hP i β (by rw [add_mul, tco_spec hPQ hP i β z, tco_spec hPQ hP i β z', rFree_add])
    funext u; simp only [this, Pi.add_apply, map_add]
  map_smul' c z := by
    have : tco Q hPQ hP i β (c • z) = c • tco Q hPQ hP i β z :=
      tco_eq hPQ hP i β (by rw [smul_mul_assoc, tco_spec hPQ hP i β z, rFree_smul])
    funext u; simp only [this, Pi.smul_apply, map_smul, RingHom.id_apply]

theorem coordR_apply (z : R) (u : Sh) :
    coordR Q hPQ hP i β a z u = thetaL Q i β a (tco Q hPQ hP i β z u) := rfl

theorem coordR_eq_zero (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) {z : R}
    (hz : z ∈ cycL1 a h1) : coordR Q hPQ hP i β a z = 0 := by
  have hz' : z * oneConcat Q Si β ∈ cycL1 a h1 := mul_mem_cycL1 a hz (oneConcat_mem_subR1 i β)
  rw [tco_spec hPQ hP i β z, mem_cycL1_iff hPQ hP i β a h1 hβ] at hz'
  funext u
  exact (thetaL_eq_zero_iff i β a _).2 (hz' u)

variable (Q) in
/-- The coordinates on `K_1`. -/
noncomputable def coordK (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) :
    KOne Q (Si + β) a h1 →ₗ[k] (Sh → Polynomial Rl) :=
  ((cycL1 a h1).restrictScalars k).liftQ (coordR Q hPQ hP i β a)
      (fun _ hz => LinearMap.mem_ker.2 (coordR_eq_zero hPQ hP i β a h1 hβ hz)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k (cycL1 a h1)).symm.toLinearMap

theorem coordK_mk (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) (y : R) :
    coordK Q hPQ hP i β a h1 hβ (Submodule.Quotient.mk y) = coordR Q hPQ hP i β a y := rfl

variable (Q) in
/-- `(t_u)_u ↦ (θ(t_u) mod J)_u`. -/
noncomputable def thetaS : (Sh → T) →ₗ[k] (Sh → Polynomial Rl) :=
  LinearMap.pi fun u => (thetaL Q i β a).toLinearMap ∘ₗ LinearMap.proj u

omit [IsDomain k] in
theorem thetaS_apply (t : Sh → T) (u : Sh) : thetaS Q i β a t u = thetaL Q i β a (t u) := rfl

omit [IsDomain k] in
theorem thetaS_surjective : Function.Surjective (thetaS Q i β a) := fun c =>
  ⟨fun u => (thetaL_surjective i β a (c u)).choose,
    funext fun u => (thetaL_surjective i β a (c u)).choose_spec⟩

variable (Q) in
/-- `t ↦ ∑_u ψ(ŵ_u) ι(t_u)` in `K_1`. -/
noncomputable def gK (h1 : 1 < Multiset.card (Si + β)) : (Sh → T) →ₗ[k] KOne Q (Si + β) a h1 :=
  ((cycL1 a h1).mkQ.restrictScalars k) ∘ₗ
    { toFun := rFree, map_add' := rFree_add, map_smul' := rFree_smul i β }

include hPQ hP in
theorem ker_thetaS_le (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) :
    LinearMap.ker (thetaS Q i β a) ≤ LinearMap.ker (gK Q i β a h1) := by
  intro t ht
  rw [LinearMap.mem_ker] at ht ⊢
  show Submodule.Quotient.mk (rFree t) = 0
  rw [Submodule.Quotient.mk_eq_zero, mem_cycL1_iff hPQ hP i β a h1 hβ]
  intro u
  exact (thetaL_eq_zero_iff i β a _).1 (congrFun ht u)

variable (Q) in
/-- The inverse of the coordinates: `⊕_u R^Λ(β)[t] → K_1 e(i, β)`. -/
noncomputable def embK (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) :
    (Sh → Polynomial Rl) →ₗ[k] KOne Q (Si + β) a h1 :=
  (LinearMap.ker (thetaS Q i β a)).liftQ (gK Q i β a h1) (ker_thetaS_le hPQ hP i β a h1 hβ) ∘ₗ
    ((thetaS Q i β a).quotKerEquivOfSurjective (thetaS_surjective i β a)).symm.toLinearMap

theorem embK_thetaS (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) (t : Sh → T) :
    embK Q hPQ hP i β a h1 hβ (thetaS Q i β a t) = Submodule.Quotient.mk (rFree t) := by
  rw [embK, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  rfl

variable (Q) in
/-- The image `M̄` of the monic central polynomial `M` in `R^Λ(β)[t]`. -/
noncomputable def aMonicL : Polynomial Rl :=
  Polynomial.mapAlgHom (CycKLR.mk k Q a β) (aMonic Q i β a)

theorem monic_aMonicL (hsym : ∀ a b, a ≠ b → Q b a = MvPolynomial.rename ![1, 0] (Q a b))
    (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) (ha : (a i).Monic) :
    (aMonicL Q i β a).Monic := by
  rw [aMonicL, Polynomial.coe_mapAlgHom]; exact (monic_aMonic i β a hsym hQ ha).map _

include hPQ hP in
theorem aMonicL_comm (q : Polynomial Rl) : Commute q (aMonicL Q i β a) := by
  obtain ⟨q', rfl⟩ := Polynomial.map_surjective (CycKLR.mk k Q a β : Rb →+* Rl)
    (CycKLR.mk_surjective) q
  rw [aMonicL, Polynomial.coe_mapAlgHom]
  exact (aMonic_comm i β a hPQ hP q').map (Polynomial.mapRingHom (CycKLR.mk k Q a β : Rb →+* Rl))

theorem thetaL_aPrime (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) :
    thetaL Q i β a (aPrime Q i β a) = lamA Q i β • aMonicL Q i β a := by
  rw [thetaL, AlgHom.comp_apply, theta_aPrime_eq_smul i β a hQ, map_smul, aMonicL]

variable (Q) in
/-- Coordinatewise `p ↦ λ⁻¹ (p div M̄)`. -/
noncomputable def divK {M : Polynomial Rl} (hM : M.Monic) :
    (Sh → Polynomial Rl) →ₗ[k] (Sh → Polynomial Rl) :=
  Ring.inverse (lamA Q i β) • LinearMap.pi fun u => divByMonicLin k hM ∘ₗ LinearMap.proj u

omit [IsDomain k] in
theorem divK_apply {M : Polynomial Rl} (hM : M.Monic) (c : Sh → Polynomial Rl) (u : Sh) :
    divK Q i β a hM c u = Ring.inverse (lamA Q i β) • (c u /ₘ M) := rfl

variable (Q) in
/-- **The splitting of `P`** (KK Lemma 4.19 with `h = Q`): `Q`, then coordinates, then
division by `M̄`. -/
noncomputable def splitMap (hsym : ∀ a b, a ≠ b → Q b a = MvPolynomial.rename ![1, 0] (Q a b))
    (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) (ha : (a i).Monic)
    (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) :
    KZero Q (Si + β) a (zero_lt_card_single_add i β) →ₗ[k] KOne Q (Si + β) a h1 :=
  embK Q hPQ hP i β a h1 hβ ∘ₗ divK Q i β a (monic_aMonicL i β a hsym hQ ha) ∘ₗ
    coordK Q hPQ hP i β a h1 hβ ∘ₗ
      (qMap a hsym (zero_lt_card_single_add i β) h1 (Multiset.card β)
        (card_single_add i β).symm).restrictScalars k

/-- **KK Lemma 4.19 / Theorem 4.5 (splitting)**: `splitMap ∘ P = id` on `K_1 e(i, β)`. -/
theorem splitMap_pMap (hsym : ∀ a b, a ≠ b → Q b a = MvPolynomial.rename ![1, 0] (Q a b))
    (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) (ha : (a i).Monic)
    (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) (y : R) :
    splitMap Q hPQ hP i β a hsym hQ ha h1 hβ
        (pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β) (card_single_add i β).symm
          (Submodule.Quotient.mk (y * oneConcat Q Si β))) =
      Submodule.Quotient.mk (y * oneConcat Q Si β) := by
  set t := tco Q hPQ hP i β y with ht
  have htA : tco Q hPQ hP i β (y * oneConcat Q Si β *
      aElt a (zero_lt_card_single_add i β) (Multiset.card β)) =
        fun u => t u * aPrime Q i β a := by
    apply tco_eq
    rw [mul_assoc _ (aElt _ _ _), aElt_mul_oneConcat, tco_spec hPQ hP i β y, rFree_mul_concat]
  have hM := monic_aMonicL i β a hsym hQ ha
  have hdiv : divK Q i β a hM (coordR Q hPQ hP i β a (y * oneConcat Q Si β *
      aElt a (zero_lt_card_single_add i β) (Multiset.card β))) = thetaS Q i β a t := by
    funext u
    rw [divK_apply, coordR_apply, htA, map_mul, thetaL_aPrime i β a hQ, mul_smul_comm,
      ← divByMonicLin_apply (k := k) hM, map_smul, divByMonicLin_apply,
      mul_divByMonic_of_commute hM (aMonicL_comm hPQ hP i β a _), smul_smul,
      Ring.inverse_mul_cancel _ (isUnit_lamA i β hQ), one_smul, thetaS_apply]
  rw [splitMap, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, qMap_pMap, coordK_mk, hdiv, embK_thetaS, ht,
    ← tco_spec hPQ hP i β y]

theorem coordK_act1 (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) (b : Rb)
    (w : KOne Q (Si + β) a h1) :
    coordK Q hPQ hP i β a h1 hβ (act1 Q i β a h1 b w) =
      fun u => coordK Q hPQ hP i β a h1 hβ w u * Polynomial.C (CycKLR.mk k Q a β b) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have h : tco Q hPQ hP i β (y * cR Q i β b) =
      fun u => tco Q hPQ hP i β y u * (1 ⊗ₜ b) := by
    apply tco_eq
    rw [mul_assoc, cR, concat_mul_oneConcat, ← oneConcat_mul_concat, ← mul_assoc,
      tco_spec hPQ hP i β y, rFree_mul_concat]
  funext u
  rw [act1_mk, coordK_mk, coordK_mk, coordR_apply, coordR_apply, h, map_mul, thetaL_one_tmul]

omit [IsDomain k] in
theorem divK_mul_C {M : Polynomial Rl} (hM : M.Monic) (c : Sh → Polynomial Rl) (r : Rl) :
    divK Q i β a hM (fun u => c u * Polynomial.C r) =
      fun u => divK Q i β a hM c u * Polynomial.C r := by
  funext u
  rw [divK_apply, divK_apply, divByMonic_mul_C' hM, smul_mul_assoc]

theorem embK_mul_C (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) (b : Rb)
    (c : Sh → Polynomial Rl) :
    embK Q hPQ hP i β a h1 hβ (fun u => c u * Polynomial.C (CycKLR.mk k Q a β b)) =
      act1 Q i β a h1 b (embK Q hPQ hP i β a h1 hβ c) := by
  obtain ⟨t, rfl⟩ := thetaS_surjective i β a c
  have h : (fun u => thetaS Q i β a t u * Polynomial.C (CycKLR.mk k Q a β b)) =
      thetaS Q i β a (fun u => t u * (1 ⊗ₜ b)) := by
    funext u; rw [thetaS_apply, thetaS_apply, map_mul, thetaL_one_tmul]
  rw [h, embK_thetaS, embK_thetaS, act1_mk, cR, rFree_mul_concat]

/-- **The splitting is right `R(β)`-linear**, so `P : K_1 e(i, β) → K_0` splits as a map of
right `R(β)`-modules (KK Theorem 4.5). -/
theorem splitMap_act (hsym : ∀ a b, a ≠ b → Q b a = MvPolynomial.rename ![1, 0] (Q a b))
    (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) (ha : (a i).Monic)
    (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) (b : Rb)
    (z : KZero Q (Si + β) a (zero_lt_card_single_add i β)) :
    splitMap Q hPQ hP i β a hsym hQ ha h1 hβ (act0 Q i β a b z) =
      act1 Q i β a h1 b (splitMap Q hPQ hP i β a hsym hQ ha h1 hβ z) := by
  rw [splitMap, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, qMap_act i β a hsym h1 b, coordK_act1, divK_mul_C,
    embK_mul_C]
  rfl

end Split

end KLRAlgebra

end Categorification.KLR
