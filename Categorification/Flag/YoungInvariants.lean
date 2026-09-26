/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.Esymm

/-!
# The fundamental theorem for Young subgroups

Let `d : Fin n → ℕ` be a list of block sizes and let `Gen d = Σ j, Fin (d j)` index the
variables `x_{j,a}` of `k[Gen d]`, the `j`-th block having `d j` variables. The Young subgroup
`S_{d_0} × ⋯ × S_{d_{n-1}}` is the group of permutations of `Gen d` preserving the block label
`Sigma.fst`. Over any commutative ring `k`, its invariants form a polynomial ring in the
elementary symmetric polynomials of the blocks:

  `k[x_{j,α} : j < n, 1 ≤ α ≤ d_j] ≅ k[Gen d]^{S_{d_0} × ⋯ × S_{d_{n-1}}}`,
  `x_{j,α} ↦ e_α(x_{j,0}, …, x_{j,d_j - 1})`.

The polynomial ring on the left is again `k[Gen d]`, with the generator `⟨j, a⟩` standing for
`x_{j, a+1}` (degree `a + 1`); this is the ring of generators of KL III (arXiv:0807.3250v1),
§5.1, eq. (5.2), before imposing the relations `I_{k,N}`.

## Main results

* `Flag.youngHom k d` : the `k`-algebra map `x_{j,α} ↦ e_α(block j)`.
* `Flag.youngHom_injective` : it is injective (algebraic independence of the block
  elementary symmetric polynomials).
* `Flag.youngHom_range` : its range is `labelInvariants k Sigma.fst`.
* `Flag.youngEquiv k d` : the resulting isomorphism onto the Young invariants.

## Proof

Induction on the number of blocks. Splitting off block `0`,
`k[Gen d] ≅ K[Fin d_0]` with `K = k[Gen d']`, `d' = Fin.tail d` (`splitEquiv`). Under this
identification `youngHom k d` becomes `F ↦ Φ(map (youngHom k d') F)`, where
`Φ : K[Fin d_0] → K[Fin d_0]` is the elementary-symmetric map over the coefficient ring `K`
(`splitEquiv_youngHom`). Mathlib's fundamental theorem of symmetric polynomials
(`MvPolynomial.esymmAlgHom_injective`, `esymmAlgHom_surjective`, valid over any commutative
ring) and the induction hypothesis on the coefficients give both statements.
-/

namespace Categorification.Flag

open MvPolynomial Equiv
open Finset (univ mem_map mem_univ sum_congr)

universe u

variable (k : Type u) [CommRing k]

/-- The variables of `k[Gen d]`: `⟨j, a⟩` is the `a`-th variable of block `j`. -/
abbrev Gen {n : ℕ} (d : Fin n → ℕ) : Type := (j : Fin n) × Fin (d j)

variable {n : ℕ}

/-- `e_r` of the variables of block `j`. -/
noncomputable def blockEsymm (d : Fin n → ℕ) (j : Fin n) (r : ℕ) : MvPolynomial (Gen d) k :=
  rename (Sigma.mk j) (esymm (Fin (d j)) k r)

theorem map_sigmaMk_univ (d : Fin n → ℕ) (j : Fin n) :
    (univ : Finset (Fin (d j))).map ⟨Sigma.mk j, sigma_mk_injective⟩ =
      labSet (Sigma.fst : Gen d → Fin n) (· = j) := by
  ext ⟨j', b⟩
  simp only [mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk, mem_labSet]
  constructor
  · rintro ⟨b', h⟩
    exact (congrArg Sigma.fst h).symm
  · rintro rfl
    exact ⟨b, rfl⟩

theorem blockEsymm_eq_setEsymm (d : Fin n → ℕ) (j : Fin n) (r : ℕ) :
    blockEsymm k d j r = setEsymm (labSet (Sigma.fst : Gen d → Fin n) (· = j)) r := by
  rw [blockEsymm, ← setEsymm_univ, ← map_sigmaMk_univ]
  exact rename_setEsymm (k := k) ⟨Sigma.mk j, sigma_mk_injective⟩ univ r

theorem blockEsymm_mem (d : Fin n → ℕ) (j : Fin n) (r : ℕ) :
    blockEsymm k d j r ∈ labelInvariants k (Sigma.fst : Gen d → Fin n) := by
  rw [blockEsymm_eq_setEsymm]
  exact setEsymm_labSet_mem _ _ r

/-- **The map `x_{j,α} ↦ e_α(block j)`** (generator `⟨j, a⟩ ↦ e_{a+1}(block j)`). -/
noncomputable def youngHom (d : Fin n → ℕ) : MvPolynomial (Gen d) k →ₐ[k] MvPolynomial (Gen d) k :=
  aeval fun v => blockEsymm k d v.1 (v.2 + 1)

theorem youngHom_X (d : Fin n → ℕ) (v : Gen d) :
    youngHom k d (X v) = blockEsymm k d v.1 (v.2 + 1) := by
  simp [youngHom]

theorem youngHom_mem (d : Fin n → ℕ) (F : MvPolynomial (Gen d) k) :
    youngHom k d F ∈ labelInvariants k (Sigma.fst : Gen d → Fin n) := by
  induction F using MvPolynomial.induction_on with
  | C a => rw [youngHom, aeval_C]; exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
  | mul_X p v hp =>
    rw [map_mul, youngHom_X]
    exact Subalgebra.mul_mem _ hp (blockEsymm_mem k d _ _)

/-! ### Splitting off the first block -/

section Split

variable {R S₁ S₂ : Type*} [CommRing R]

theorem sumAlgEquiv_rename_inl (p : MvPolynomial S₁ R) :
    sumAlgEquiv R S₁ S₂ (rename Sum.inl p) = map C p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [rename_C, map_C, ← algebraMap_eq, AlgEquiv.commutes]
    rfl
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp, rename_X, sumAlgEquiv_X_inl, map_X]

theorem sumAlgEquiv_rename_inr (p : MvPolynomial S₂ R) :
    sumAlgEquiv R S₁ S₂ (rename Sum.inr p) = C p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [rename_C, ← algebraMap_eq, AlgEquiv.commutes]
    rfl
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp, rename_X, sumAlgEquiv_X_inr]

theorem sumAlgEquiv_rename_sumCongr_right (τ : Perm S₂) (q : MvPolynomial (S₁ ⊕ S₂) R) :
    sumAlgEquiv R S₁ S₂ (rename (Equiv.sumCongr (Equiv.refl S₁) τ) q) =
      MvPolynomial.map (rename τ).toRingHom (sumAlgEquiv R S₁ S₂ q) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    rw [rename_C, ← algebraMap_eq, AlgEquiv.commutes]
    simp only [MvPolynomial.algebraMap_apply, map_C, algebraMap_eq, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, rename_C]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp, rename_X]
    rcases i with a | b
    · simp only [Equiv.sumCongr_apply, Sum.map_inl, sumAlgEquiv_X_inl, map_X, Equiv.refl_apply]
    · simp only [Equiv.sumCongr_apply, Sum.map_inr, sumAlgEquiv_X_inr, map_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X]

end Split

variable (d : Fin (n + 1) → ℕ)

/-- `Gen d ≃ Fin (d 0) ⊕ Gen (Fin.tail d)`: split off the variables of block `0`. -/
def genSplit : Gen d ≃ Fin (d 0) ⊕ Gen (Fin.tail d) where
  toFun v := Fin.cases (motive := fun j => Fin (d j) → Fin (d 0) ⊕ Gen (Fin.tail d))
    Sum.inl (fun j a => Sum.inr ⟨j, a⟩) v.1 v.2
  invFun := Sum.elim (fun a => ⟨0, a⟩) (fun v => ⟨v.1.succ, v.2⟩)
  left_inv := by
    rintro ⟨j, a⟩
    induction j using Fin.cases <;> rfl
  right_inv := by
    rintro (a | ⟨j, a⟩) <;> rfl

@[simp] theorem genSplit_zero (a : Fin (d 0)) : genSplit d ⟨0, a⟩ = Sum.inl a := rfl

@[simp] theorem genSplit_succ (j : Fin n) (a : Fin (d j.succ)) :
    genSplit d ⟨j.succ, a⟩ = Sum.inr ⟨j, a⟩ := rfl

@[simp] theorem genSplit_symm_inl (a : Fin (d 0)) : (genSplit d).symm (Sum.inl a) = ⟨0, a⟩ := rfl

@[simp] theorem genSplit_symm_inr (v : Gen (Fin.tail d)) :
    (genSplit d).symm (Sum.inr v) = ⟨v.1.succ, v.2⟩ := rfl

/-- `k[Gen d] ≅ K[Fin (d 0)]` with `K = k[Gen (Fin.tail d)]`. -/
noncomputable def splitEquiv :
    MvPolynomial (Gen d) k ≃ₐ[k] MvPolynomial (Fin (d 0)) (MvPolynomial (Gen (Fin.tail d)) k) :=
  (renameEquiv k (genSplit d)).trans (sumAlgEquiv k _ _)

theorem splitEquiv_apply (F : MvPolynomial (Gen d) k) :
    splitEquiv k d F = sumAlgEquiv k _ _ (rename (genSplit d) F) := rfl

theorem splitEquiv_X_zero (a : Fin (d 0)) : splitEquiv k d (X ⟨0, a⟩) = X a := by
  rw [splitEquiv_apply, rename_X, genSplit_zero, sumAlgEquiv_X_inl]

theorem splitEquiv_X_succ (j : Fin n) (a : Fin (d j.succ)) :
    splitEquiv k d (X ⟨j.succ, a⟩) = C (X ⟨j, a⟩) := by
  rw [splitEquiv_apply, rename_X, genSplit_succ, sumAlgEquiv_X_inr]

theorem splitEquiv_blockEsymm_zero (r : ℕ) :
    splitEquiv k d (blockEsymm k d 0 r) = esymm (Fin (d 0)) (MvPolynomial (Gen (Fin.tail d)) k) r := by
  rw [splitEquiv_apply, blockEsymm, rename_rename]
  have : (genSplit d ∘ Sigma.mk 0) = (Sum.inl : Fin (d 0) → _) := rfl
  rw [this, sumAlgEquiv_rename_inl, map_esymm]

theorem splitEquiv_blockEsymm_succ (j : Fin n) (r : ℕ) :
    splitEquiv k d (blockEsymm k d j.succ r) = C (blockEsymm k (Fin.tail d) j r) := by
  rw [splitEquiv_apply, blockEsymm, rename_rename]
  have : (genSplit d ∘ Sigma.mk j.succ) = (Sum.inr ∘ Sigma.mk (β := fun i => Fin (Fin.tail d i)) j) :=
    rfl
  rw [this, ← rename_rename, sumAlgEquiv_rename_inr]
  rfl

/-- The elementary-symmetric map over the coefficient ring `K`. -/
noncomputable abbrev esymmMap (m : ℕ) (K : Type*) [CommRing K] :
    MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K :=
  aeval fun a : Fin m => esymm (Fin m) K (a + 1)

theorem esymmMap_injective (m : ℕ) (K : Type*) [CommRing K] :
    Function.Injective (esymmMap m K) := by
  intro F G h
  apply esymmAlgHom_injective K (σ := Fin m) (n := m) (by simp)
  apply Subtype.ext
  rw [esymmAlgHom_apply, esymmAlgHom_apply]
  exact h

theorem map_esymmMap {m : ℕ} {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (F : MvPolynomial (Fin m) K) :
    map f (esymmMap m K F) = esymmMap m L (map f F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [esymmMap, aeval_C, algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, map_X, aeval_X, map_esymm]

/-- **Compatibility of `youngHom` with splitting off block `0`.** -/
theorem splitEquiv_youngHom (F : MvPolynomial (Gen d) k) :
    splitEquiv k d (youngHom k d F) =
      esymmMap (d 0) _ (map (youngHom k (Fin.tail d)).toRingHom (splitEquiv k d F)) := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    simp only [youngHom, aeval_C, algebraMap_eq, AlgEquiv.commutes, map_C]
    rw [← algebraMap_eq, AlgEquiv.commutes]
    simp [esymmMap, algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    rw [youngHom_X]
    obtain ⟨j, a⟩ := v
    revert a
    refine Fin.cases (fun a => ?_) (fun j a => ?_) j
    · rw [splitEquiv_blockEsymm_zero, splitEquiv_X_zero, map_X, esymmMap, aeval_X]
    · rw [splitEquiv_blockEsymm_succ, splitEquiv_X_succ, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        youngHom_X, esymmMap, aeval_C, algebraMap_eq]

/-- A permutation of `Gen d` of the form `σ ⊕ τ` (with `σ` on block `0`). -/
def splitPerm (σ : Perm (Fin (d 0))) (τ : Perm (Gen (Fin.tail d))) : Perm (Gen d) :=
  (genSplit d).trans ((Equiv.sumCongr σ τ).trans (genSplit d).symm)

theorem splitPerm_label (σ : Perm (Fin (d 0))) (τ : Perm (Gen (Fin.tail d)))
    (hτ : (Sigma.fst : Gen (Fin.tail d) → Fin n) ∘ τ = Sigma.fst) :
    (Sigma.fst : Gen d → Fin (n + 1)) ∘ splitPerm d σ τ = Sigma.fst := by
  funext v
  obtain ⟨j, a⟩ := v
  revert a
  refine Fin.cases (fun a => rfl) (fun j a => ?_) j
  simp only [Function.comp_apply, splitPerm, Equiv.trans_apply, genSplit_succ,
    Equiv.sumCongr_apply, Sum.map_inr, genSplit_symm_inr]
  rw [show (τ ⟨j, a⟩).1 = j from congrFun hτ ⟨j, a⟩]

theorem splitEquiv_rename_splitPerm (σ : Perm (Fin (d 0))) (τ : Perm (Gen (Fin.tail d)))
    (F : MvPolynomial (Gen d) k) :
    splitEquiv k d (rename (splitPerm d σ τ) F) = rename σ (map (rename τ).toRingHom (splitEquiv k d F)) := by
  rw [splitEquiv_apply, splitEquiv_apply, rename_rename]
  have h1 : (genSplit d ∘ splitPerm d σ τ) =
      (Equiv.sumCongr σ (Equiv.refl _)) ∘ (Equiv.sumCongr (Equiv.refl _) τ) ∘ genSplit d := by
    funext v
    rcases h : genSplit d v with a | w
    · simp [splitPerm, h]
    · simp [splitPerm, h]
  rw [h1, ← rename_rename, ← rename_rename, sumAlgEquiv_rename_sumCongr,
    sumAlgEquiv_rename_sumCongr_right]

/-! ### The main theorem -/

theorem youngHom_zero_eq_id (d : Fin 0 → ℕ) : youngHom k d = AlgHom.id k _ :=
  MvPolynomial.algHom_ext fun v => v.1.elim0

theorem youngHom_main : ∀ (n : ℕ) (d : Fin n → ℕ), Function.Injective (youngHom k d) ∧
    ∀ f ∈ labelInvariants k (Sigma.fst : Gen d → Fin n), f ∈ (youngHom k d).range
  | 0, d => by
    rw [youngHom_zero_eq_id]
    exact ⟨fun _ _ h => h, fun f _ => ⟨f, rfl⟩⟩
  | n + 1, d => by
    obtain ⟨ih_inj, ih_surj⟩ := youngHom_main n (Fin.tail d)
    refine ⟨fun F G h => ?_, fun f hf => ?_⟩
    · apply (splitEquiv k d).injective
      apply map_injective _ ih_inj
      apply esymmMap_injective
      rw [← splitEquiv_youngHom, ← splitEquiv_youngHom, h]
    · -- `splitEquiv f` is symmetric in the variables of block `0`
      have hsym : (splitEquiv k d f).IsSymmetric := by
        intro σ
        have := hf (splitPerm d σ (Equiv.refl _)) (splitPerm_label d σ _ rfl)
        have h2 := splitEquiv_rename_splitPerm k d σ (Equiv.refl _) f
        rw [this] at h2
        simp only [Equiv.coe_refl, rename_id] at h2
        rw [show (AlgHom.id k (MvPolynomial (Gen (Fin.tail d)) k)).toRingHom = RingHom.id _ from rfl,
          map_id] at h2
        exact h2.symm
      obtain ⟨F, hF⟩ := esymmAlgHom_surjective (MvPolynomial (Gen (Fin.tail d)) k)
        (σ := Fin (d 0)) (n := d 0) (by simp) ⟨_, hsym⟩
      have hF' : esymmMap (d 0) _ F = splitEquiv k d f := by
        rw [← esymmAlgHom_apply, hF]
      -- the coefficients of `F` are Young invariants for `Fin.tail d`
      have hcoeff : ∀ m, F.coeff m ∈ labelInvariants k (Sigma.fst : Gen (Fin.tail d) → Fin n) := by
        intro m τ hτ
        have hmap : map (rename τ).toRingHom F = F := by
          apply esymmMap_injective
          rw [← map_esymmMap, hF']
          have := hf (splitPerm d (Equiv.refl _) τ) (splitPerm_label d _ τ hτ)
          have h2 := splitEquiv_rename_splitPerm k d (Equiv.refl _) τ f
          rw [this] at h2
          simp only [Equiv.coe_refl, rename_id, AlgHom.id_apply] at h2
          exact h2.symm
        have := congrArg (coeff m) hmap
        rwa [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
      choose G hG using fun m => ih_surj _ (hcoeff m)
      set G' : MvPolynomial (Fin (d 0)) (MvPolynomial (Gen (Fin.tail d)) k) :=
        ∑ m ∈ F.support, monomial m (G m)
      have hG' : map (youngHom k (Fin.tail d)).toRingHom G' = F := by
        conv_rhs => rw [F.as_sum]
        simp only [G', map_sum, map_monomial]
        refine sum_congr rfl fun m _ => ?_
        rw [← hG m]
      refine ⟨(splitEquiv k d).symm G', (splitEquiv k d).injective ?_⟩
      change splitEquiv k d (youngHom k d ((splitEquiv k d).symm G')) = splitEquiv k d f
      rw [splitEquiv_youngHom, AlgEquiv.apply_symm_apply, hG', hF']

variable {k}

/-- **Algebraic independence**: the block elementary symmetric polynomials `e_α(block j)`,
`1 ≤ α ≤ d_j`, are algebraically independent over `k`. -/
theorem youngHom_injective {n : ℕ} (d : Fin n → ℕ) : Function.Injective (youngHom k d) :=
  (youngHom_main k n d).1

/-- **Fundamental theorem for Young subgroups**: the invariants of
`S_{d_0} × ⋯ × S_{d_{n-1}}` are the polynomials in the block elementary symmetric
polynomials. -/
theorem youngHom_range {n : ℕ} (d : Fin n → ℕ) :
    (youngHom k d).range = labelInvariants k (Sigma.fst : Gen d → Fin n) := by
  ext f
  exact ⟨fun ⟨F, hF⟩ => hF ▸ youngHom_mem k d F, (youngHom_main k n d).2 f⟩

variable (k)

/-- **`k[x_{j,α}] ≅ k[Gen d]^{S_d}`**: the polynomial ring on the block elementary symmetric
polynomials is isomorphic to the Young invariants. -/
noncomputable def youngEquiv {n : ℕ} (d : Fin n → ℕ) :
    MvPolynomial (Gen d) k ≃ₐ[k] labelInvariants k (Sigma.fst : Gen d → Fin n) :=
  AlgEquiv.ofBijective ((youngHom k d).codRestrict _ (youngHom_mem k d))
    ⟨fun F G h => youngHom_injective d (congrArg Subtype.val h), fun f => by
      obtain ⟨F, hF⟩ := (youngHom_main k n d).2 f.1 f.2
      exact ⟨F, Subtype.ext hF⟩⟩

@[simp] theorem youngEquiv_apply_coe {n : ℕ} (d : Fin n → ℕ) (F : MvPolynomial (Gen d) k) :
    (youngEquiv k d F : MvPolynomial (Gen d) k) = youngHom k d F := rfl

end Categorification.Flag
