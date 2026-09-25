/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Examples.Small

/-!
# `R(ν)` for pairwise non-interacting labels

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.2 ("Examples"), item 5): if `ν = i_1 + ⋯ + i_m` with `i_k · i_ℓ = 0`
for all `k ≠ ℓ`, then `R(ν)` is isomorphic to the ring of `m! × m!` matrices with coefficients
in `ℤ[x_1, …, x_m]`; rows and columns are indexed by `Seq(ν)` and `ψ_{w} 1_i` goes to the
elementary matrix `E_{w i, i}`.

Here the labels are assumed pairwise distinct (`ν.Nodup`; in KL I this is part of the
hypothesis since `i · i = 2`). To identify all the `Pol_i` with one polynomial ring we fix a
reference sequence `t₀`, and attach the variable `x_b` to the label `t₀ b`: the dot on the
`a`-th strand of `1_t` goes to `x_{var t a} E_{t,t}` where `t₀ (var t a) = t a`.

## Main results

* `NonInteracting.equiv` : for general data `Q` with `Q a b = 1` for distinct `a, b ∈ ν`, over
  any commutative ring `k`, `R(ν) ≃ₐ[k] Matrix (Seq ν) (Seq ν) k[x_1, …, x_m]`.
* `NonInteracting.KL1.equiv` : **KL I §2.2, Example 5** for the KL I data.
* `NonInteracting.card_seq` : `|Seq ν| = m!`.
* `NonInteracting.toMat_ψw_pol_e` : the image of `ψ_{ρ} p(x) 1_t` is the elementary matrix
  `E_{w t, t}` (`w = wordProd ρ`) with entry `p` in the variables attached to the labels.
-/

namespace Categorification.KLR

open MvPolynomial Equiv TypeA KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

namespace NonInteracting

variable {ν : Multiset I}

local notation "m" => Multiset.card ν

/-! ### Sequences with distinct labels -/

section seq

variable (hnd : ν.Nodup)

omit [DecidableEq I] in
include hnd in
theorem seq_injective (t : Seq ν) : Function.Injective t.1 := by
  have h : (Finset.univ.val.map t.1).Nodup := by rw [t.2]; exact hnd
  intro a b hab
  exact (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).1 h a (Finset.mem_univ _) b
    (Finset.mem_univ _) hab

omit [DecidableEq I] in
include hnd in
theorem smul_left_injective (t : Seq ν) {w w' : Perm (Fin m)} (h : w • t = w' • t) : w = w' := by
  have : w.symm = w'.symm := Equiv.ext fun a => seq_injective hnd t (by
    simpa [Seq.smul_apply] using congrFun (congrArg Subtype.val h) a)
  simpa using congrArg Equiv.symm this

omit [DecidableEq I] in
include hnd in
theorem exists_smul_eq (s t : Seq ν) : ∃ w : Perm (Fin m), w • t = s := by
  have hf : ∀ a, ∃ b, t.1 b = s.1 a := by
    intro a
    have : s.1 a ∈ Finset.univ.val.map t.1 := by rw [t.2]; exact s.mem a
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.1 this
    exact ⟨b, hb⟩
  choose f hf using hf
  have finj : Function.Injective f := fun a b h =>
    seq_injective hnd s (by rw [← hf a, ← hf b, h])
  refine ⟨(Equiv.ofBijective f (Finite.injective_iff_bijective.1 finj)).symm, ?_⟩
  apply Subtype.ext; funext a
  simp [Seq.smul_apply, hf]

variable (t₀ : Seq ν)

/-- The permutation carrying the reference sequence `t₀` to `t`. -/
noncomputable def toPerm (t : Seq ν) : Perm (Fin m) :=
  Classical.choose (exists_smul_eq hnd t t₀)

omit [DecidableEq I] in
theorem toPerm_smul (t : Seq ν) : toPerm hnd t₀ t • t₀ = t :=
  Classical.choose_spec (exists_smul_eq hnd t t₀)

/-- The variable attached to the strand at position `a` of `t`: `t₀ (var t a) = t a`. -/
noncomputable def var (t : Seq ν) : Perm (Fin m) := (toPerm hnd t₀ t).symm

omit [DecidableEq I] in
theorem t₀_var (t : Seq ν) (a : Fin m) : t₀.1 (var hnd t₀ t a) = t.1 a := by
  have := congrFun (congrArg Subtype.val (toPerm_smul hnd t₀ t)) a
  simpa [Seq.smul_apply, var] using this

omit [DecidableEq I] in
theorem var_eq_var {s t : Seq ν} {a b : Fin m} (h : s.1 a = t.1 b) :
    var hnd t₀ s a = var hnd t₀ t b :=
  seq_injective hnd t₀ (by rw [t₀_var, t₀_var, h])

/-- `Seq ν` is a torsor under `S_m`: `w ↦ w • t₀`. -/
noncomputable def permEquivSeq : Perm (Fin m) ≃ Seq ν :=
  Equiv.ofBijective (fun w => w • t₀)
    ⟨fun _ _ h => smul_left_injective hnd t₀ h, fun s => exists_smul_eq hnd s t₀⟩

omit [DecidableEq I] in
include hnd t₀ in
/-- `|Seq ν| = m!` (KL I: "`m! × m!` matrices"). -/
theorem card_seq : Fintype.card (Seq ν) = (Multiset.card ν).factorial := by
  rw [← Fintype.card_congr (permEquivSeq hnd t₀), Fintype.card_perm, Fintype.card_fin]

end seq

omit [DecidableEq I] in
theorem sadj_inv (n l : ℕ) : (sadj n l)⁻¹ = sadj n l := by
  unfold sadj; split_ifs <;> simp [swap_inv]

omit [DecidableEq I] in
theorem sadj_smul_sadj_smul (l : ℕ) (t : Seq ν) : sadj m l • sadj m l • t = t := by
  rw [← mul_smul]
  nth_rewrite 1 [← sadj_inv m l]
  rw [inv_mul_cancel, one_smul]

/-! ### The operators -/

local notation "Rm" => MvPolynomial (Fin (Multiset.card ν)) k
local notation "V" => (Seq ν → MvPolynomial (Fin (Multiset.card ν)) k)

variable (hnd : ν.Nodup) (t₀ : Seq ν)

variable (k) in
/-- `1_t`: projection to the `t`-th coordinate. -/
noncomputable def opE' (t : Seq ν) : Module.End Rm V :=
  (LinearMap.single Rm (fun _ => Rm) t).comp (LinearMap.proj t)

variable (k) in
/-- `x_a`: multiplication by `x_{var s a}` in the `s`-th coordinate. -/
noncomputable def opX' (a : Fin m) : Module.End Rm V :=
  LinearMap.pi fun s => (X (var hnd t₀ s a) : Rm) • LinearMap.proj s

variable (k) in
/-- `ψ_l`: the permutation `f ↦ f ∘ s_l` of coordinates (zero if `l + 1 ≥ m`). -/
noncomputable def opΨ' (l : ℕ) : Module.End Rm V :=
  if l + 1 < m then LinearMap.funLeft Rm Rm (fun s : Seq ν => sadj m l • s) else 0

theorem opE'_apply (t : Seq ν) (f : V) (s : Seq ν) :
    opE' k t f s = if s = t then f t else 0 := by
  simp [opE', Pi.single_apply]

omit [DecidableEq I] in
theorem opX'_apply (a : Fin m) (f : V) (s : Seq ν) :
    opX' k hnd t₀ a f s = X (var hnd t₀ s a) * f s := rfl

omit [DecidableEq I] in
theorem opΨ'_apply {l : ℕ} (h : l + 1 < m) (f : V) (s : Seq ν) :
    opΨ' k l f s = f (sadj m l • s) := by
  simp [opΨ', h, LinearMap.funLeft_apply]

omit [DecidableEq I] in
theorem opΨ'_eq_zero {l : ℕ} (h : ¬ l + 1 < m) : opΨ' k (ν := ν) l = 0 := by
  simp [opΨ', h]

omit [DecidableEq I] in
/-- The variable attached to a strand not moved by `s_l` is unchanged. -/
theorem var_sadj_smul (s : Seq ν) (l : ℕ) (a : Fin m) (h₁ : a.val ≠ l) (h₂ : a.val ≠ l + 1) :
    var hnd t₀ (sadj m l • s) a = var hnd t₀ s a := by
  apply var_eq_var
  rw [Seq.smul_apply, ← Perm.inv_def, sadj_inv, sadj_apply_of_ne a h₁ h₂]

omit [DecidableEq I] in
theorem var_sadj_smul_left (s : Seq ν) {l : ℕ} (h : l + 1 < m) :
    var hnd t₀ (sadj m l • s) ⟨l, by omega⟩ = var hnd t₀ s ⟨l + 1, h⟩ := by
  apply var_eq_var
  rw [Seq.smul_apply, ← Perm.inv_def, sadj_inv, sadj_apply_left h]

omit [DecidableEq I] in
theorem var_sadj_smul_right (s : Seq ν) {l : ℕ} (h : l + 1 < m) :
    var hnd t₀ (sadj m l • s) ⟨l + 1, h⟩ = var hnd t₀ s ⟨l, by omega⟩ := by
  apply var_eq_var
  rw [Seq.smul_apply, ← Perm.inv_def, sadj_inv, sadj_apply_right h]

variable (k) in
/-- The values of the generators. -/
noncomputable def genOp' : Gen ν → Module.End Rm V
  | .idem t => opE' k t
  | .dot a => opX' k hnd t₀ a
  | .cross l => opΨ' k l

omit [DecidableEq I] in
theorem ncEval_one {A : Type*} [Ring A] [Algebra k A] {n : ℕ} (y : Fin n → A) :
    ncEval y (1 : MvPolynomial (Fin n) k) = 1 := by
  unfold ncEval
  rw [show (1 : MvPolynomial (Fin n) k) = Finsupp.single 0 1 from rfl,
    Finsupp.sum_single_index (by simp)]
  simp

variable {Q : I → I → MvPolynomial (Fin 2) k} (hQ : ∀ a ∈ ν, ∀ b ∈ ν, a ≠ b → Q a b = 1)

include hQ in
theorem genOp'_rel ⦃a b : FreeAlgebra k (Gen ν)⦄ (h : Rel k Q ν a b) :
    FreeAlgebra.lift k (genOp' k hnd t₀) a = FreeAlgebra.lift k (genOp' k hnd t₀) b := by
  have hl : ∀ (t : Seq ν) (a b : Fin m), a ≠ b → t.lbl a ≠ t.lbl b :=
    fun t a b hab h => hab (seq_injective hnd t h)
  cases h with
  | idem_mul s t =>
    simp only [fe, map_mul, FreeAlgebra.lift_ι_apply, genOp']
    refine LinearMap.ext fun f => funext fun u => ?_
    split_ifs with hst
    · subst hst
      simp only [Module.End.mul_apply, opE'_apply, FreeAlgebra.lift_ι_apply, genOp']
      split_ifs <;> rfl
    · simp only [Module.End.mul_apply, opE'_apply, map_zero, LinearMap.zero_apply,
        Pi.zero_apply]
      split_ifs with h1 <;> simp_all
  | idem_sum =>
    simp only [fe, map_sum, FreeAlgebra.lift_ι_apply, genOp', map_one]
    refine LinearMap.ext fun f => funext fun u => ?_
    simp [LinearMap.sum_apply, Finset.sum_apply, opE'_apply]
  | dot_idem a t =>
    simp only [fe, fx, map_mul, FreeAlgebra.lift_ι_apply, genOp']
    refine LinearMap.ext fun f => funext fun u => ?_
    simp only [Module.End.mul_apply, opE'_apply, opX'_apply]
    split_ifs with h1
    · subst h1; rfl
    · simp
  | cross_idem l t =>
    simp only [fe, fψ, map_mul, FreeAlgebra.lift_ι_apply, genOp']
    by_cases h : l + 1 < m
    · refine LinearMap.ext fun f => funext fun u => ?_
      simp only [Module.End.mul_apply, opE'_apply, opΨ'_apply h]
      by_cases hu : u = sadj m l • t
      · subst hu; simp [sadj_smul_sadj_smul]
      · rw [if_neg hu, if_neg]
        rintro rfl; exact hu (sadj_smul_sadj_smul l u).symm
    · simp [opΨ'_eq_zero h]
  | cross_zero l h =>
    simp only [fψ, FreeAlgebra.lift_ι_apply, genOp', map_zero]
    exact opΨ'_eq_zero (by omega)
  | dot_dot a b =>
    simp only [fx, map_mul, FreeAlgebra.lift_ι_apply, genOp']
    refine LinearMap.ext fun f => funext fun u => ?_
    simp only [Module.End.mul_apply, opX'_apply]
    ring
  | cross_cross l l' h =>
    simp only [fψ, map_mul, FreeAlgebra.lift_ι_apply, genOp']
    by_cases h' : l' + 1 < m
    · refine LinearMap.ext fun f => funext fun u => ?_
      simp only [Module.End.mul_apply, opΨ'_apply h', opΨ'_apply (show l + 1 < m by omega)]
      rw [← mul_smul, ← mul_smul, sadj_comm m (Or.inl h)]
    · simp [opΨ'_eq_zero h']
  | dot_cross a l h₁ h₂ =>
    simp only [fx, fψ, map_mul, FreeAlgebra.lift_ι_apply, genOp']
    by_cases h : l + 1 < m
    · refine LinearMap.ext fun f => funext fun u => ?_
      simp only [Module.End.mul_apply, opΨ'_apply h, opX'_apply]
      rw [var_sadj_smul hnd t₀ u l a h₁ h₂]
    · simp [opΨ'_eq_zero h]
  | dot_cross_left l h t =>
    rw [if_neg (hl t _ _ (by simp [Fin.ext_iff])), map_zero]
    simp only [fe, fx, fψ, map_mul, map_sub, FreeAlgebra.lift_ι_apply, genOp']
    refine LinearMap.ext fun f => funext fun u => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, opΨ'_apply h, opX'_apply,
      LinearMap.zero_apply, Pi.zero_apply, Pi.sub_apply]
    rw [var_sadj_smul_right hnd t₀ u h, sub_self]
  | dot_cross_right l h t =>
    rw [if_neg (hl t _ _ (by simp [Fin.ext_iff])), map_zero]
    simp only [fe, fx, fψ, map_mul, map_sub, FreeAlgebra.lift_ι_apply, genOp']
    refine LinearMap.ext fun f => funext fun u => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, opΨ'_apply h, opX'_apply,
      LinearMap.zero_apply, Pi.zero_apply, Pi.sub_apply]
    rw [var_sadj_smul_left hnd t₀ u h, sub_self]
  | cross_sq l h t =>
    have hne := hl t ⟨l, by omega⟩ ⟨l + 1, h⟩ (by simp [Fin.ext_iff])
    rw [if_neg hne, hQ _ (t.mem _) _ (t.mem _) hne]
    simp only [fe, fψ, map_mul, FreeAlgebra.lift_ι_apply, genOp', PolyRep.algHom_ncEval,
      ncEval_one, one_mul]
    refine LinearMap.ext fun f => funext fun u => ?_
    simp only [Module.End.mul_apply, opΨ'_apply h, sadj_smul_sadj_smul]
  | braid l h t =>
    rw [if_neg (fun c => hl t _ _ (by simp [Fin.ext_iff]) c.1), map_zero]
    simp only [fe, fψ, map_mul, map_sub, FreeAlgebra.lift_ι_apply, genOp']
    refine LinearMap.ext fun f => funext fun u => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, opΨ'_apply (show l + 1 < m by omega),
      opΨ'_apply (show l + 1 + 1 < m by omega), LinearMap.zero_apply, Pi.zero_apply,
      Pi.sub_apply]
    rw [← mul_smul, ← mul_smul, ← mul_smul, ← mul_smul, sadj_braid h, sub_self]

variable (Q) in
/-- The action of `R(ν)` on `⊕_{t ∈ Seq ν} k[x_1, …, x_m]` by `k[x]`-linear maps. -/
noncomputable def toEnd : KLRAlgebra k Q ν →ₐ[k] Module.End Rm V :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (genOp' k hnd t₀), fun _ _ h =>
    genOp'_rel hnd t₀ hQ h⟩

theorem toEnd_mk (a : FreeAlgebra k (Gen ν)) :
    toEnd hnd t₀ Q hQ (mk k Q ν a) = FreeAlgebra.lift k (genOp' k hnd t₀) a :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem toEnd_e (t : Seq ν) : toEnd hnd t₀ Q hQ (e t) = opE' k t := by
  rw [e, toEnd_mk, FreeAlgebra.lift_ι_apply]; rfl

@[simp] theorem toEnd_x (a : Fin m) : toEnd hnd t₀ Q hQ (x a) = opX' k hnd t₀ a := by
  rw [x, toEnd_mk, FreeAlgebra.lift_ι_apply]; rfl

@[simp] theorem toEnd_ψ (l : ℕ) : toEnd hnd t₀ Q hQ (ψ l) = opΨ' k l := by
  rw [ψ, toEnd_mk, FreeAlgebra.lift_ι_apply]; rfl

theorem toEnd_pol_apply (p : Rm) (f : V) (s : Seq ν) :
    toEnd hnd t₀ Q hQ (pol p) f s = rename (var hnd t₀ s) p * f s := by
  induction p using MvPolynomial.induction_on generalizing f with
  | C c =>
    rw [algHom_C, AlgHom.commutes, rename_C, Module.algebraMap_end_apply, Pi.smul_apply,
      smul_eq_C_mul]
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, Pi.add_apply, hp, hq, map_add, add_mul]
  | mul_X p a hp =>
    rw [map_mul, map_mul, Module.End.mul_apply, hp, pol_X, toEnd_x, opX'_apply, map_mul,
      rename_X]
    ring

theorem toEnd_ψw_apply {ρ : List ℕ} (hρ : ValidWord m ρ) (f : V) (s : Seq ν) :
    toEnd hnd t₀ Q hQ (ψw ρ) f s = f ((wordProd m ρ)⁻¹ • s) := by
  induction ρ generalizing s with
  | nil => simp [wordProd]
  | cons l ρ ih =>
    have hl : l + 1 < m := hρ l (by simp)
    rw [ψw_cons, map_mul, Module.End.mul_apply, toEnd_ψ, opΨ'_apply hl,
      ih (fun l' hl' => hρ l' (by simp [hl'])), wordProd_cons', mul_inv_rev, sadj_inv, mul_smul]

/-- The image of `ψ_ρ p(x) 1_t`, `ρ` a valid word for `w`: `f ↦ (s ↦ [w⁻¹ s = t] p' f_t)`,
where `p'` is `p` with the variables renamed according to the labels of `t`. -/
theorem toEnd_ψw_pol_e_apply {ρ : List ℕ} (hρ : ValidWord m ρ) (p : Rm) (t : Seq ν) (f : V)
    (s : Seq ν) :
    toEnd hnd t₀ Q hQ (ψw ρ * pol p * e t) f s =
      if (wordProd m ρ)⁻¹ • s = t then rename (var hnd t₀ t) p * f t else 0 := by
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, toEnd_ψw_apply hnd t₀ hQ hρ,
    toEnd_pol_apply, toEnd_e, opE'_apply]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]

/-! ### The matrix algebra -/

variable (Q) in
/-- The map `R(ν) → Mat_{Seq ν}(k[x_1, …, x_m])`. -/
noncomputable def toMat : KLRAlgebra k Q ν →ₐ[k] Matrix (Seq ν) (Seq ν) Rm :=
  ((LinearMap.toMatrixAlgEquiv' (R := Rm) (n := Seq ν)).restrictScalars k).toAlgHom.comp
    (toEnd hnd t₀ Q hQ)

theorem toMat_apply (r : KLRAlgebra k Q ν) (s t : Seq ν) :
    toMat hnd t₀ Q hQ r s t = toEnd hnd t₀ Q hQ r (fun j => if j = t then 1 else 0) s :=
  LinearMap.toMatrixAlgEquiv'_apply _ _ _

/-- The image of `ψ_ρ p(x) 1_t` is the elementary matrix `E_{w t, t}` (`w = wordProd ρ`) with
entry `p` renamed according to the labels of `t`. -/
theorem toMat_ψw_pol_e {ρ : List ℕ} (hρ : ValidWord m ρ) (p : Rm) (t : Seq ν) :
    toMat hnd t₀ Q hQ (ψw ρ * pol p * e t) =
      Matrix.stdBasisMatrix (wordProd m ρ • t) t (rename (var hnd t₀ t) p) := by
  refine Matrix.ext fun s t' => ?_
  rw [toMat_apply, toEnd_ψw_pol_e_apply hnd t₀ hQ hρ, Matrix.stdBasisMatrix, Matrix.of_apply]
  have : (wordProd m ρ)⁻¹ • s = t ↔ wordProd m ρ • t = s := by
    constructor
    · rintro rfl; exact smul_inv_smul _ _
    · rintro rfl; exact inv_smul_smul _ _
  by_cases h1 : wordProd m ρ • t = s
  · rw [if_pos (this.2 h1)]
    by_cases h2 : t = t'
    · rw [if_pos h2, if_pos ⟨h1, h2⟩, mul_one]
    · rw [if_neg h2, mul_zero, if_neg (fun c => h2 c.2)]
  · rw [if_neg (fun c => h1 (this.1 c)), if_neg (fun c => h1 c.1)]

omit [DecidableEq I] in
theorem rename_var_injective (t : Seq ν) :
    Function.Injective (rename (var hnd t₀ t) : Rm → Rm) :=
  rename_injective _ (var hnd t₀ t).injective

theorem toMat_injective : Function.Injective (toMat hnd t₀ Q hQ) := by
  have hc : ∀ w, IsReduced m (canWord m w) ∧ wordProd m (canWord m w) = w :=
    fun w => ⟨isReduced_canWord m w, wordProd_canWord m w⟩
  rw [injective_iff_map_eq_zero]
  intro r hr
  have key : ∀ s t, e s * r * e t = 0 := by
    intro s t
    obtain ⟨w₀, hw₀⟩ := exists_smul_eq hnd s t
    have hmem : e s * (e s * r * e t) * e t = e s * r * e t := by
      simp only [← mul_assoc, e_mul_self]; rw [mul_assoc _ (e t), e_mul_self]
    have hspan := mem_span_corner' (Q := Q) (ν := ν) (canWord m) hc t s hmem
    let L : Rm →ₗ[k] KLRAlgebra k Q ν :=
      (LinearMap.mulRight k (e t)).comp ((LinearMap.mulLeft k (ψw (canWord m w₀))).comp
        (pol (k := k) (Q := Q) (ν := ν)).toLinearMap)
    have hle : Submodule.span k {b : KLRAlgebra k Q ν | ∃ (w : Perm (Fin m))
        (u : Fin m →₀ ℕ), w • t = s ∧ ψw (canWord m w) * pol (monomial u 1) * e t = b} ≤
        LinearMap.range L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨w, u, hw, rfl⟩
      obtain rfl : w = w₀ := smul_left_injective hnd t (hw.trans hw₀.symm)
      exact ⟨monomial u 1, rfl⟩
    obtain ⟨p, hp⟩ := hle hspan
    change ψw (canWord m w₀) * pol p * e t = e s * r * e t at hp
    have h0 : toMat hnd t₀ Q hQ (e s * r * e t) = 0 := by
      rw [map_mul, map_mul, hr, mul_zero, zero_mul]
    rw [← hp, toMat_ψw_pol_e hnd t₀ hQ (hc w₀).1.1, (hc w₀).2, hw₀] at h0
    have h1 := congrFun (congrFun h0 s) t
    rw [Matrix.StdBasisMatrix.apply_same, Matrix.zero_apply] at h1
    have hp0 : p = 0 := rename_var_injective hnd t₀ t (by rw [h1, map_zero])
    rw [← hp, hp0, map_zero, mul_zero, zero_mul]
  have hsum : r = ∑ s, ∑ t, e s * r * e t := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_e, one_mul, mul_one]
  rw [hsum]
  simp [key]

theorem toMat_surjective : Function.Surjective (toMat hnd t₀ Q hQ) := by
  intro M
  have hc : ∀ w, IsReduced m (canWord m w) ∧ wordProd m (canWord m w) = w :=
    fun w => ⟨isReduced_canWord m w, wordProd_canWord m w⟩
  have hunit : ∀ s t q, ∃ r, toMat hnd t₀ Q hQ r = Matrix.stdBasisMatrix s t q := by
    intro s t q
    obtain ⟨w, hw⟩ := exists_smul_eq hnd s t
    refine ⟨ψw (canWord m w) * pol (rename (var hnd t₀ t).symm q) * e t, ?_⟩
    rw [toMat_ψw_pol_e hnd t₀ hQ (hc w).1.1, (hc w).2, hw, rename_rename]
    have : (⇑(var hnd t₀ t) ∘ ⇑(var hnd t₀ t).symm) = id :=
      funext fun a => (var hnd t₀ t).apply_symm_apply a
    rw [this, rename_id_apply]
  choose g hg using hunit
  refine ⟨∑ s, ∑ t, g s t (M s t), ?_⟩
  rw [map_sum]
  simp only [map_sum, hg]
  exact (Matrix.matrix_eq_sum_stdBasisMatrix M).symm

/-- **KL I §2.2, Example 5** (general data): if the labels of `ν` are pairwise distinct and
`Q a b = 1` for all distinct `a, b ∈ ν`, then `R(ν)` is isomorphic to the ring of
`Seq ν × Seq ν` matrices (of size `m! × m!`, `card_seq`) over `k[x_1, …, x_m]`. -/
noncomputable def equiv : KLRAlgebra k Q ν ≃ₐ[k] Matrix (Seq ν) (Seq ν) Rm :=
  AlgEquiv.ofBijective (toMat hnd t₀ Q hQ) ⟨toMat_injective hnd t₀ hQ, toMat_surjective hnd t₀ hQ⟩

theorem equiv_apply (r : KLRAlgebra k Q ν) : equiv hnd t₀ hQ r = toMat hnd t₀ Q hQ r := rfl

/-- In particular `ψ_w 1_t` goes to the elementary matrix `E_{w t, t}`. -/
theorem equiv_ψw_e {ρ : List ℕ} (hρ : ValidWord m ρ) (t : Seq ν) :
    equiv hnd t₀ hQ (ψw ρ * e t) = Matrix.stdBasisMatrix (wordProd m ρ • t) t 1 := by
  have := toMat_ψw_pol_e hnd t₀ hQ hρ 1 t
  rwa [map_one, mul_one, map_one] at this

/-! ### The KL I statement -/

namespace KL1

variable (Γ : SimpleGraph I) [DecidableRel Γ.Adj]

omit [DecidableEq I] in
theorem klQ_eq_one {a b : I} (h : ¬ Γ.Adj a b) : (klQ Γ a b : MvPolynomial (Fin 2) k) = 1 := by
  simp [klQ, h]

/-- **KL I §2.2, Example 5**: if `ν = i_1 + ⋯ + i_m` with pairwise distinct labels no two of
which are joined by an edge (`i_k · i_ℓ = 0` for `k ≠ ℓ`), then `R(ν)` is isomorphic to the ring
of `m! × m!` matrices (indexed by `Seq ν`) with coefficients in `k[x_1, …, x_m]` (the paper:
`k = ℤ`). -/
noncomputable def equiv (hΓ : ∀ a ∈ ν, ∀ b ∈ ν, ¬ Γ.Adj a b) :
    R1 k Γ ν ≃ₐ[k] Matrix (Seq ν) (Seq ν) (MvPolynomial (Fin (Multiset.card ν)) k) :=
  NonInteracting.equiv hnd t₀ fun a ha b hb _ => klQ_eq_one Γ (hΓ a ha b hb)

end KL1

end NonInteracting

end Categorification.KLR
