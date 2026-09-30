/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaIndepTrunc
import Categorification.Flag.Free
import Categorification.Flag.Relabel

/-!
# Ring maps out of `H_{k^{+i}}` in bounded degree

Auxiliary material for the nondegeneracy argument of Khovanov–Lauda III (arXiv:0807.3250v1,
§6.4, TeX `sln-2008-ArXiv.tex` l. 9598–9790).

KL III §5.1.1: `H_{k^{+i}}` is generated over `H_k` (acting through `p_1^*`) by `ξ_i`, subject to
the single relation `∏_{v ∈ block i+1} (ξ_i - x_v) = 0`; it is free with basis
`1, ξ_i, …, ξ_i^{k_{i+1}-k_i-1}` (`Categorification.Flag.eBasisRight`). We record this as an
isomorphism `H_{k^{+i}} ≅ H_k[X] / (charPolyE)` (`eAdjoinEquiv`), which makes it easy to write
down ring maps out of `H_{k^{+i}}` (`liftE`).

In the truncated polynomial ring `Tr` (`Categorification.Flag.Indep.Tr`), with the ring map
`H_k → Tr` of total Chern classes `x_j` (`hLift`) and an element `Ξ` of weight `1` (the Chern root
`ξ_i` of the line `F_{k_i+1}/F_{k_i}`), `liftETr` sends `ξ_i ↦ Ξ`, and its restriction along
`p_2^* : H_{+_i k} → H_{k^{+i}}` is the map of total Chern classes of `+_i k`: block `i` is
multiplied by `1 + Ξ` and block `i + 1` divided by it (`liftETr_eLeft`), as dictated by
KL III (5.15), (5.16). All this requires the blocks to be larger than the truncation degree.
-/

noncomputable section

namespace Categorification.Flag.Indep

open Categorification.Flag

universe u

variable {K : Type u} [Field K] {m : ℕ}

/-! ## `H_{k^{+i}}` as `H_k[X]/(charPolyE)` -/

section Adjoin

attribute [local instance] eRightAlgebra

instance H_nontrivial {n : ℕ} (d : Fin n → ℕ) : Nontrivial (H K d) :=
  Module.nontrivial_of_finrank_pos (R := K) (by rw [finrank_H]; exact Nat.multinomial_pos _ _)

theorem eRight_apply (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) (z : H K d) :
    eRight K i d h z =
      pR K (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h) (hEquiv K d z) := rfl

variable (K) (i : Fin m) (d : Fin (m + 1) → ℕ)

/-- The characteristic polynomial `∑_{g ≤ b} (-1)^g x_{i+1,g} X^{b-g}` of `ξ_i` over `H_k`
(`b = d_{i+1}`, the size of block `i + 1`). -/
def charPolyE : Polynomial (H K d) :=
  ∑ g ∈ Finset.range (d i.succ + 1),
    Polynomial.C ((-1) ^ g * x K d i.succ g) * Polynomial.X ^ (d i.succ - g)

theorem charPolyE_eq : charPolyE K i d = Polynomial.X ^ d i.succ +
    ∑ g ∈ Finset.range (d i.succ),
      Polynomial.C ((-1) ^ (g + 1) * x K d i.succ (g + 1)) * Polynomial.X ^ (d i.succ - (g + 1)) := by
  rw [charPolyE, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, x_zero, map_one, Nat.sub_zero]
  exact add_comm _ _

theorem charPolyE_monic : (charPolyE K i d).Monic := by
  rw [charPolyE_eq]
  refine Polynomial.monic_X_pow_add ?_
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun g hg => ?_
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  have := Finset.mem_range.1 hg
  exact_mod_cast (show d i.succ - (g + 1) < d i.succ by omega)

theorem charPolyE_natDegree : (charPolyE K i d).natDegree = d i.succ := by
  rw [charPolyE_eq, Polynomial.natDegree_add_eq_left_of_degree_lt, Polynomial.natDegree_X_pow]
  rw [Polynomial.degree_X_pow]
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun g hg => ?_
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  have := Finset.mem_range.1 hg
  exact_mod_cast (show d i.succ - (g + 1) < d i.succ by omega)

theorem eval₂_charPolyE {S : Type*} [CommRing S] (f : H K d →+* S) (y : S) :
    (charPolyE K i d).eval₂ f y =
      ∑ g ∈ Finset.range (d i.succ + 1), (-1) ^ g * f (x K d i.succ g) * y ^ (d i.succ - g) := by
  rw [charPolyE, Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, map_mul, map_pow,
    map_neg, map_one]

variable (h : 0 < d i.succ)

/-- `ξ_i` is a root of `charPolyE` (the characteristic polynomial of `x_{v₀}` over the block of
`v₀`, `Categorification.Flag.split_monic`). -/
theorem charPolyE_xi :
    (charPolyE K i d).eval₂ (eRight K i d h).toRingHom (eXi K i d h) = 0 := by
  have hs := split_monic (k := K) (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h)
  rw [blockCard_movedVar] at hs
  rw [eval₂_charPolyE]
  have e : ∀ g, (eRight K i d h).toRingHom (x K d i.succ g) =
      pR K (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h)
        (xB K (Sigma.fst : Gen d → Fin (m + 1)) i.succ g) := fun g => by
    change eRight K i d h (x K d i.succ g) = _
    rw [eRight_apply, hEquiv_x]
  simp only [e]
  rw [← Finset.sum_range_reflect] at hs
  have hs' := congrArg (fun z => (-1 : ERing K i d h) ^ d i.succ * z) hs
  simp only [mul_zero, Finset.mul_sum] at hs'
  rw [← hs']
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg := Finset.mem_range.1 hg
  have e1 : d i.succ - (d i.succ + 1 - 1 - g) = g := by omega
  have e2 : d i.succ + 1 - 1 - g = d i.succ - g := by omega
  rw [e1, e2]
  have e3 : (-1 : ERing K i d h) ^ d i.succ * (-1) ^ (d i.succ - g) = (-1) ^ g := by
    rw [← pow_add, show d i.succ + (d i.succ - g) = g + 2 * (d i.succ - g) by omega, pow_add,
      pow_mul]
    simp
  show (-1) ^ g * pR K _ _ (xB K (Sigma.fst : Gen d → Fin (m + 1)) i.succ g) *
      xi K _ (movedVar i d h) ^ (d i.succ - g) =
    (-1) ^ d i.succ * ((-xi K _ (movedVar i d h)) ^ (d i.succ - g) *
      pR K _ _ (xB K (Sigma.fst : Gen d → Fin (m + 1)) i.succ g))
  rw [neg_pow (xi K _ (movedVar i d h))]
  linear_combination (pR K _ (movedVar i d h) (xB K (Sigma.fst : Gen d → Fin (m + 1)) i.succ g) *
    xi K _ (movedVar i d h) ^ (d i.succ - g)) * e3.symm

/-- `charPolyE_xi` for the structure map of `eRightAlgebra`. -/
theorem charPolyE_xi_ofId :
    letI := eRightAlgebra K i d h
    (charPolyE K i d).eval₂ (Algebra.ofId (H K d) (ERing K i d h) : H K d →+* ERing K i d h)
      (eXi K i d h) = 0 := by
  let _ := eRightAlgebra K i d h
  exact charPolyE_xi K i d h

/-- `H_k[X] / (charPolyE) → H_{k^{+i}}`, `X ↦ ξ_i`. -/
def eAdjoin :
    letI := eRightAlgebra K i d h
    AdjoinRoot (charPolyE K i d) →ₐ[H K d] ERing K i d h :=
  letI := eRightAlgebra K i d h
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (eXi K i d h) (charPolyE_xi_ofId K i d h)

theorem eAdjoin_bijective : Function.Bijective (eAdjoin K i d h) := by
  let _ := eRightAlgebra K i d h
  let pb := AdjoinRoot.powerBasis' (charPolyE_monic K i d)
  let e : Fin pb.dim ≃ Fin (d i.succ) := finCongr (charPolyE_natDegree K i d)
  let L := pb.basis.equiv (eBasisRight K i d h) e
  have hL : (eAdjoin K i d h).toLinearMap = L.toLinearMap := by
    refine pb.basis.ext fun a => ?_
    rw [AlgHom.toLinearMap_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply, eBasisRight_apply,
      PowerBasis.basis_eq_pow, map_pow, AdjoinRoot.powerBasis'_gen, eAdjoin,
      AdjoinRoot.liftAlgHom_root]
    rfl
  have : ⇑(eAdjoin K i d h) = ⇑L := by
    funext z
    exact LinearMap.congr_fun hL z
  rw [this]
  exact L.bijective

/-- **`H_{k^{+i}} ≅ H_k[X] / (charPolyE)`** (KL III §5.1.1). -/
def eAdjoinEquiv :
    letI := eRightAlgebra K i d h
    AdjoinRoot (charPolyE K i d) ≃ₐ[H K d] ERing K i d h :=
  letI := eRightAlgebra K i d h
  AlgEquiv.ofBijective (eAdjoin K i d h) (eAdjoin_bijective K i d h)

theorem eAdjoinEquiv_symm_eRight (z : H K d) :
    (eAdjoinEquiv K i d h).symm (eRight K i d h z) = AdjoinRoot.of _ z := by
  let _ := eRightAlgebra K i d h
  rw [AlgEquiv.symm_apply_eq]
  change eRight K i d h z = eAdjoin K i d h (algebraMap (H K d) _ z)
  rw [AlgHom.commutes]; rfl

theorem eAdjoinEquiv_symm_xi :
    (eAdjoinEquiv K i d h).symm (eXi K i d h) = AdjoinRoot.root _ := by
  let _ := eRightAlgebra K i d h
  rw [AlgEquiv.symm_apply_eq, eAdjoinEquiv, AlgEquiv.ofBijective_apply, eAdjoin,
    AdjoinRoot.liftAlgHom_root]

/-- **Ring maps out of `H_{k^{+i}}`**: a ring map `f` out of `H_k` and a root of `charPolyE`
under `f`. -/
def liftE {S : Type*} [CommRing S] (f : H K d →+* S) (y : S)
    (hy : (charPolyE K i d).eval₂ f y = 0) : ERing K i d h →+* S :=
  (AdjoinRoot.lift f y hy).comp (eAdjoinEquiv K i d h).symm.toRingEquiv.toRingHom

variable {K i d h}

theorem liftE_eRight {S : Type*} [CommRing S] (f : H K d →+* S) (y : S)
    (hy : (charPolyE K i d).eval₂ f y = 0) (z : H K d) :
    liftE K i d h f y hy (eRight K i d h z) = f z := by
  rw [liftE, RingHom.comp_apply]
  change AdjoinRoot.lift f y hy ((eAdjoinEquiv K i d h).symm (eRight K i d h z)) = _
  rw [eAdjoinEquiv_symm_eRight, AdjoinRoot.lift_of]

theorem liftE_xi {S : Type*} [CommRing S] (f : H K d →+* S) (y : S)
    (hy : (charPolyE K i d).eval₂ f y = 0) :
    liftE K i d h f y hy (eXi K i d h) = y := by
  rw [liftE, RingHom.comp_apply]
  change AdjoinRoot.lift f y hy ((eAdjoinEquiv K i d h).symm (eXi K i d h)) = _
  rw [eAdjoinEquiv_symm_xi, AdjoinRoot.lift_root]

/-- The canonical generators of `H_{k^{+i}}` under `liftE` (KL III (5.28), (5.29)). -/
theorem liftE_xB_split {S : Type*} [CommRing S] (f : H K d →+* S) (y : S)
    (hy : (charPolyE K i d).eval₂ f y = 0) (j : Fin (m + 1)) (α : ℕ) :
    liftE K i d h f y hy (xB K (splitLab (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h))
      (some j) α) =
      if j = i.succ then ∑ g ∈ Finset.range (α + 1), (-y) ^ g * f (x K d i.succ (α - g))
      else f (x K d j α) := by
  split_ifs with hj
  · subst hj
    have hs := xB_split_eq_sum (k := K) (lab := (Sigma.fst : Gen d → Fin (m + 1)))
      (v₀ := movedVar i d h) α
    change xB K _ (some (movedVar i d h).1) α = _ at hs
    rw [show (movedVar i d h).1 = i.succ from rfl] at hs
    rw [hs, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_mul, map_pow, map_neg]
    have e1 : xi K (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h) = eXi K i d h := rfl
    have e2 : pR K (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h)
        (xB K (Sigma.fst : Gen d → Fin (m + 1)) i.succ (α - g)) =
        eRight K i d h (x K d i.succ (α - g)) := by
      rw [eRight_apply, hEquiv_x]
    rw [e1, e2, liftE_xi, liftE_eRight]
  · have e2 : xB K (splitLab (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h)) (some j) α =
        eRight K i d h (x K d j α) := by
      rw [eRight_apply, hEquiv_x, pR_xB K (lab := (Sigma.fst : Gen d → Fin (m + 1)))
        (v₀ := movedVar i d h) j hj α]
    rw [e2, liftE_eRight]

end Adjoin

/-! ## The truncated model -/

section TrModel

variable {σ : Type} {w : σ → ℕ} {D : ℕ}

theorem coeff_sc_one_add (Ξ : Tr K w D)
    (hΞ : sc K w D Ξ = Polynomial.C Ξ * Polynomial.X) (y : Tr K w D) (α : ℕ) :
    (sc K w D (y * (1 + Ξ))).coeff (α + 1) =
      (sc K w D y).coeff (α + 1) + Ξ * (sc K w D y).coeff α := by
  rw [map_mul (sc K w D), map_add (sc K w D), map_one (sc K w D), hΞ, mul_add, mul_one,
    Polynomial.coeff_add, ← mul_assoc, Polynomial.coeff_mul_X, Polynomial.coeff_mul_C, mul_comm]

theorem sc_invOne (Ξ : Tr K w D) (hΞ : sc K w D Ξ = Polynomial.C Ξ * Polynomial.X) :
    sc K w D (invOne Ξ) =
      ∑ f ∈ Finset.range (D + 1), Polynomial.C ((-Ξ) ^ f) * Polynomial.X ^ f := by
  rw [invOne, map_sum (sc K w D)]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [map_pow (sc K w D), map_neg (sc K w D), hΞ, Polynomial.C_pow, Polynomial.C_neg, ← neg_mul,
    mul_pow (-Polynomial.C Ξ) Polynomial.X f]

theorem coeff_sc_invOne (hw : ∀ v, 0 < w v) {Ξ : Tr K w D}
    (hΞ : sc K w D Ξ = Polynomial.C Ξ * Polynomial.X) (hΞ0 : aug K w D Ξ = 0) (f : ℕ) :
    (sc K w D (invOne Ξ)).coeff f = (-Ξ) ^ f := by
  rw [sc_invOne Ξ hΞ, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hf
  · rfl
  · have : D + 1 ≤ f := by simp at hf; omega
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le this
    have hn : aug K w D (-Ξ) = 0 := by rw [map_neg, hΞ0, neg_zero]
    rw [pow_add, pow_eq_zero_of_aug hw hn, zero_mul]

theorem coeff_sc_mul_invOne (hw : ∀ v, 0 < w v) {Ξ : Tr K w D}
    (hΞ : sc K w D Ξ = Polynomial.C Ξ * Polynomial.X) (hΞ0 : aug K w D Ξ = 0) (y : Tr K w D)
    (α : ℕ) :
    (sc K w D (y * invOne Ξ)).coeff α =
      ∑ g ∈ Finset.range (α + 1), (-Ξ) ^ g * (sc K w D y).coeff (α - g) := by
  rw [map_mul (sc K w D), Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => (sc K w D y).coeff a * (sc K w D (invOne Ξ)).coeff b), ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg := Finset.mem_range.1 hg
  rw [coeff_sc_invOne hw hΞ hΞ0, show α + 1 - 1 - g = α - g by omega,
    show α - (α - g) = g by omega, mul_comm]

/-- **The total Chern classes across an upward strand** `E_i` (KL III (5.15), (5.16)): block `i`
(our `i.castSucc`) is multiplied by `1 + Ξ`, block `i + 1` (our `i.succ`) by `(1 + Ξ)^{-1}`. -/
def upData (i : Fin m) (Ξ : Tr K w D) (c : Fin (m + 1) → Tr K w D) : Fin (m + 1) → Tr K w D :=
  fun j => if j = i.castSucc then c j * (1 + Ξ) else if j = i.succ then c j * invOne Ξ else c j

theorem castSucc_ne_succ (i : Fin m) : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne

theorem upData_castSucc (i : Fin m) (Ξ : Tr K w D) (c : Fin (m + 1) → Tr K w D) :
    upData i Ξ c i.castSucc = c i.castSucc * (1 + Ξ) := by simp [upData]

theorem upData_succ (i : Fin m) (Ξ : Tr K w D) (c : Fin (m + 1) → Tr K w D) :
    upData i Ξ c i.succ = c i.succ * invOne Ξ := by simp [upData, (castSucc_ne_succ i).symm]

theorem upData_of_ne (i : Fin m) (Ξ : Tr K w D) (c : Fin (m + 1) → Tr K w D) {j : Fin (m + 1)}
    (h1 : j ≠ i.castSucc) (h2 : j ≠ i.succ) : upData i Ξ c j = c j := by simp [upData, h1, h2]

theorem prod_upData (hw : ∀ v, 0 < w v) (i : Fin m) {Ξ : Tr K w D} (hΞ0 : aug K w D Ξ = 0)
    (c : Fin (m + 1) → Tr K w D) : ∏ j, upData i Ξ c j = ∏ j, c j := by
  classical
  have hne := castSucc_ne_succ i
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i.castSucc),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ i.succ⟩),
    ← Finset.mul_prod_erase _ (fun j => c j) (Finset.mem_univ i.castSucc),
    ← Finset.mul_prod_erase _ (fun j => c j) (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ i.succ⟩)]
  have hrest : ∏ j ∈ (Finset.univ.erase i.castSucc).erase i.succ, upData i Ξ c j =
      ∏ j ∈ (Finset.univ.erase i.castSucc).erase i.succ, c j := by
    refine Finset.prod_congr rfl fun j hj => ?_
    exact upData_of_ne i Ξ c (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj))
      (Finset.ne_of_mem_erase hj)
  rw [hrest, upData_castSucc, upData_succ]
  have key := one_add_mul_invOne hw hΞ0
  linear_combination (c i.castSucc * c i.succ * ∏ j ∈ (Finset.univ.erase i.castSucc).erase i.succ,
    c j) * key

theorem coeff_sc_upData_zero (hw : ∀ v, 0 < w v) (i : Fin m) {Ξ : Tr K w D}
    (hΞ0 : aug K w D Ξ = 0) (c : Fin (m + 1) → Tr K w D) (h0 : ∀ j, (sc K w D (c j)).coeff 0 = 1)
    (j : Fin (m + 1)) : (sc K w D (upData i Ξ c j)).coeff 0 = 1 := by
  rw [coeff_sc_zero hw]
  have h0' := h0 j
  rw [coeff_sc_zero hw] at h0'
  have ha : aug K w D (c j) = 1 := by
    have hinj : Function.Injective (algebraMap K (Tr K w D)) := (algebraMap K _).injective
    exact hinj (by rw [h0', map_one])
  simp only [upData]
  split_ifs
  · rw [map_mul, map_add, ha, hΞ0, map_one]; simp
  · rw [map_mul, ha, aug_invOne hw hΞ0]; simp
  · rw [ha, map_one]

/-- `charPolyE` has the root `Ξ` in the truncated model, when block `i + 1` is larger than the
truncation degree. -/
theorem charPolyE_root (hw : ∀ v, 0 < w v) (i : Fin m) (d : Fin (m + 1) → ℕ) (hd : ∀ j, D ≤ d j)
    (hb : D < d i.succ) (c : Fin (m + 1) → Tr K w D) (h0 : ∀ j, (sc K w D (c j)).coeff 0 = 1)
    (hprod : ∏ j, c j = 1) {Ξ : Tr K w D} (hΞ : sc K w D Ξ = Polynomial.C Ξ * Polynomial.X)
    (hΞ0 : aug K w D Ξ = 0) :
    (charPolyE K i d).eval₂ (hLift d hd c h0 hprod).toRingHom Ξ = 0 := by
  rw [eval₂_charPolyE]
  have hc := coeff_sc_mul_invOne hw hΞ hΞ0 (c i.succ) (d i.succ)
  rw [coeff_sc_of_lt _ hb] at hc
  have hc' := congrArg (fun z => (-1 : Tr K w D) ^ d i.succ * z) hc
  simp only [mul_zero, Finset.mul_sum] at hc'
  rw [← Finset.sum_range_reflect] at hc'
  rw [hc']
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg := Finset.mem_range.1 hg
  change (-1) ^ g * hLift d hd c h0 hprod (Flag.x K d i.succ g) * Ξ ^ (d i.succ - g) = _
  rw [hLift_x, show d i.succ + 1 - 1 - g = d i.succ - g by omega,
    show d i.succ - (d i.succ - g) = g by omega, neg_pow Ξ]
  have e3 : (-1 : Tr K w D) ^ d i.succ * (-1) ^ (d i.succ - g) = (-1) ^ g := by
    rw [← pow_add, show d i.succ + (d i.succ - g) = g + 2 * (d i.succ - g) by omega, pow_add,
      pow_mul]
    rw [show (-1 : Tr K w D) ^ 2 = 1 by ring, one_pow, mul_one]
  linear_combination (Ξ ^ (d i.succ - g) * (sc K w D (c i.succ)).coeff g) * e3.symm

variable (hw : ∀ v, 0 < w v) (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ)
  (hd : ∀ j, D < d j) (c : Fin (m + 1) → Tr K w D) (h0 : ∀ j, (sc K w D (c j)).coeff 0 = 1)
  (hprod : ∏ j, c j = 1) (Ξ : Tr K w D) (hΞ : sc K w D Ξ = Polynomial.C Ξ * Polynomial.X)
  (hΞ0 : aug K w D Ξ = 0)

/-- **The ring map `H_{k^{+i}} → Tr`** extending the total Chern classes `c` of `H_k` by
`ξ_i ↦ Ξ`. -/
def liftETr : ERing K i d h →+* Tr K w D :=
  liftE K i d h (hLift d (fun j => (hd j).le) c h0 hprod).toRingHom Ξ
    (charPolyE_root hw i d (fun j => (hd j).le) (hd i.succ) c h0 hprod hΞ hΞ0)

theorem liftETr_eRight (z : H K d) :
    liftETr hw i d h hd c h0 hprod Ξ hΞ hΞ0 (eRight K i d h z) =
      hLift d (fun j => (hd j).le) c h0 hprod z :=
  liftE_eRight _ _ _ z

theorem liftETr_xi : liftETr hw i d h hd c h0 hprod Ξ hΞ hΞ0 (eXi K i d h) = Ξ :=
  liftE_xi _ _ _

theorem liftETr_algebraMap (a : K) :
    liftETr hw i d h hd c h0 hprod Ξ hΞ hΞ0 (algebraMap K _ a) = algebraMap K _ a := by
  rw [← (eRight K i d h).commutes, liftETr_eRight, AlgHom.commutes]

/-- `liftETr` as a `K`-algebra map. -/
def liftETrₐ : ERing K i d h →ₐ[K] Tr K w D :=
  { liftETr hw i d h hd c h0 hprod Ξ hΞ hΞ0 with
    commutes' := liftETr_algebraMap hw i d h hd c h0 hprod Ξ hΞ hΞ0 }

theorem raise_ge (i : Fin m) (d : Fin (m + 1) → ℕ) (hd : ∀ j, D < d j) (j : Fin (m + 1)) :
    D ≤ raise i d j := by
  have := hd j
  unfold raise
  split_ifs <;> omega

/-- **The left action**: `liftETr ∘ p_2^*` is the map of the total Chern classes `upData` of
`+_i k` (KL III (5.16)). -/
theorem liftETr_eLeft (z : H K (raise i d)) :
    liftETr hw i d h hd c h0 hprod Ξ hΞ hΞ0 (eLeft K i d h z) =
      hLift (raise i d) (raise_ge i d hd) (upData i Ξ c)
        (coeff_sc_upData_zero hw i hΞ0 c h0) (by rw [prod_upData hw i hΞ0, hprod]) z := by
  have := congrArg (fun F : H K (raise i d) →ₐ[K] Tr K w D => F z)
    (algHom_H_ext (f := (liftETrₐ hw i d h hd c h0 hprod Ξ hΞ hΞ0).comp (eLeft K i d h))
      (g := hLift (raise i d) (raise_ge i d hd) (upData i Ξ c)
        (coeff_sc_upData_zero hw i hΞ0 c h0) (by rw [prod_upData hw i hΞ0, hprod]))
      fun j α => ?_)
  · exact this
  rw [hLift_x, AlgHom.comp_apply]
  rcases α with _ | α
  · rw [x_zero, map_one, map_one, coeff_sc_upData_zero hw i hΞ0 c h0]
  rw [eLeft_x]
  change liftETr hw i d h hd c h0 hprod Ξ hΞ hΞ0 _ = _
  have hne := castSucc_ne_succ i
  rw [map_add, liftETr, liftE_xB_split]
  split_ifs with h1 h2 h2
  · exact absurd (h1.symm.trans h2) hne.symm
  · -- `j = i.succ`
    subst h1
    rw [upData_succ, coeff_sc_mul_invOne hw hΞ hΞ0, map_zero, add_zero]
    refine Finset.sum_congr rfl fun g _ => ?_
    erw [hLift_x]
  · -- `j = i.castSucc`
    subst h2
    rw [map_mul, liftE_xi, liftE_xB_split, ite_eq_right h1, upData_castSucc, coeff_sc_one_add Ξ hΞ,
      ]
    erw [hLift_x, hLift_x]
  · rw [map_zero, add_zero, upData_of_ne i Ξ c h2 h1]
    erw [hLift_x]

end TrModel

end Categorification.Flag.Indep

end
