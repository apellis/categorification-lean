/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Induction

/-!
# Associativity and unitality of concatenation

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6: the inclusions `ι_{ν,ν'} : R(ν) ⊗ R(ν') → R(ν + ν')`
("putting diagrams next to each other") are associative and unital. Since `(ν + ν') + ν''` and
`ν + (ν' + ν'')` are equal but not definitionally equal multisets, the statements involve the
canonical isomorphism `castKLR h : R(μ) ≃ R(μ')` for `h : μ = μ'`.

## Main results

* `KLRAlgebra.castKLR`, with its values on generators (`castKLR_e`, `castKLR_x`, `castKLR_ψ`)
  and compatibility with gradings (`GradingDatum.castKLR_mem_grade`).
* `Seq.cast`, `Seq.append_assoc`, `Seq.nil_append`, `Seq.append_nil`.
* `KLRAlgebra.ext_of_mul` : multiplicative `k`-linear maps out of `R(ν)` agreeing on `1` and on
  the generators are equal.
* `KLRAlgebra.concat_assoc` :
  `castKLR (ι_{ν+ν',ν''} (ι_{ν,ν'} (a ⊗ b) ⊗ d)) = ι_{ν,ν'+ν''} (a ⊗ ι_{ν',ν''} (b ⊗ d))`.
* `KLRAlgebra.concat_one_left`, `KLRAlgebra.concat_one_right` :
  `castKLR (ι_{0,ν} (1 ⊗ b)) = b` and `castKLR (ι_{ν,0} (b ⊗ 1)) = b`.
-/

noncomputable section

namespace Categorification.KLR

open scoped TensorProduct
open KLRAlgebra

variable {I : Type*}

/-! ### Transport of sequences -/

namespace Seq

variable {μ μ' : Multiset I}

/-- Transport of a sequence along an equality of weights. -/
def cast (h : μ = μ') (s : Seq μ) : Seq μ' :=
  ⟨fun a => s.1 (Fin.cast (congrArg Multiset.card h).symm a), by subst h; exact s.2⟩

@[simp] theorem cast_apply (h : μ = μ') (s : Seq μ) (a : Fin (Multiset.card μ')) :
    (cast h s).1 a = s.1 (Fin.cast (congrArg Multiset.card h).symm a) := rfl

@[simp] theorem cast_rfl (s : Seq μ) : cast rfl s = s := rfl

variable {ν ν' ν'' : Multiset I}

theorem apply_congr (s : Seq ν) {a b : Fin (Multiset.card ν)} (h : a.val = b.val) :
    s.1 a = s.1 b := congrArg s.1 (Fin.ext h)

theorem append_apply_lt (i : Seq ν) (j : Seq ν') (a : Fin (Multiset.card (ν + ν')))
    (h : a.val < Multiset.card ν) : (i.append j).1 a = i.1 ⟨a.val, h⟩ := by
  have := append_posL i j ⟨a.val, h⟩
  rwa [show posL ν' ⟨a.val, h⟩ = a from Fin.ext rfl] at this

theorem append_apply_ge (i : Seq ν) (j : Seq ν') (a : Fin (Multiset.card (ν + ν')))
    (h : Multiset.card ν ≤ a.val) :
    (i.append j).1 a = j.1 ⟨a.val - Multiset.card ν, by
      have := a.2; simp only [Multiset.card_add] at this; omega⟩ := by
  have := append_posR i j ⟨a.val - Multiset.card ν, by
      have := a.2; simp only [Multiset.card_add] at this; omega⟩
  rwa [show posR ν ⟨a.val - Multiset.card ν, _⟩ = a from Fin.ext (by simp; omega)] at this

/-- Concatenation of sequences is associative. -/
theorem append_assoc (i : Seq ν) (j : Seq ν') (l : Seq ν'') :
    cast (add_assoc ν ν' ν'') ((i.append j).append l) = i.append (j.append l) := by
  apply Subtype.ext
  funext a
  rw [cast_apply]
  have ha := a.2
  simp only [Multiset.card_add] at ha
  by_cases h1 : a.val < Multiset.card ν
  · rw [append_apply_lt _ _ _ (by simp; omega), append_apply_lt _ _ _ (by simpa using h1),
      append_apply_lt _ _ _ h1]
    exact i.apply_congr (by simp)
  · by_cases h2 : a.val < Multiset.card ν + Multiset.card ν'
    · rw [append_apply_lt _ _ _ (by simp; omega), append_apply_ge _ _ _ (by simp; omega),
        append_apply_ge _ _ _ (by omega), append_apply_lt _ _ _ (by simp; omega)]
      exact j.apply_congr (by simp)
    · rw [append_apply_ge _ _ _ (by simp; omega), append_apply_ge _ _ _ (by omega),
        append_apply_ge _ _ _ (by simp; omega)]
      exact l.apply_congr (by simp; omega)

theorem nil_append (i₀ : Seq (0 : Multiset I)) (i : Seq ν) :
    cast (zero_add ν) (i₀.append i) = i := by
  apply Subtype.ext
  funext a
  rw [cast_apply, append_apply_ge _ _ _ (by simp)]
  exact i.apply_congr (by simp)

theorem append_nil (i : Seq ν) (i₀ : Seq (0 : Multiset I)) :
    cast (add_zero ν) (i.append i₀) = i := by
  apply Subtype.ext
  funext a
  rw [cast_apply, append_apply_lt _ _ _ (by simp)]
  exact i.apply_congr (by simp)

/-- The unique sequence of weight `0`. -/
def nil : Seq (0 : Multiset I) := ⟨Fin.elim0, rfl⟩

theorem eq_nil (s : Seq (0 : Multiset I)) : s = nil :=
  Subtype.ext (funext fun a => Fin.elim0 a)

instance : Unique (Seq (0 : Multiset I)) := ⟨⟨nil⟩, eq_nil⟩

end Seq

variable [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

/-! ### Transport of KLR algebras -/

section Cast

variable {μ μ' : Multiset I}

variable (Q) in
/-- The canonical isomorphism `R(μ) ≃ R(μ')` for `μ = μ'`. -/
def castKLR (h : μ = μ') : KLRAlgebra k Q μ ≃ₐ[k] KLRAlgebra k Q μ' := by
  subst h; exact AlgEquiv.refl

@[simp] theorem castKLR_rfl (a : KLRAlgebra k Q μ) : castKLR Q rfl a = a := rfl

theorem castKLR_e (h : μ = μ') (i : Seq μ) : castKLR Q h (e i) = e (Seq.cast h i) := by
  subst h; rfl

theorem castKLR_x (h : μ = μ') (a : Fin (Multiset.card μ)) :
    castKLR Q h (x a) = x (Fin.cast (congrArg Multiset.card h) a) := by
  subst h; rfl

theorem castKLR_ψ (h : μ = μ') (j : ℕ) : castKLR Q h (ψ j) = ψ j := by
  subst h; rfl

@[simp] theorem castKLR_symm_castAlg (h : μ = μ') (a : KLRAlgebra k Q μ) :
    castKLR Q h.symm (castKLR Q h a) = a := by
  subst h; rfl

@[simp] theorem castKLR_castAlg_symm (h : μ = μ') (a : KLRAlgebra k Q μ') :
    castKLR Q h (castKLR Q h.symm a) = a := by
  subst h; rfl

theorem castKLR_symm_apply (h : μ = μ') (a : KLRAlgebra k Q μ') :
    (castKLR Q h).symm a = castKLR Q h.symm a := by
  subst h; rfl

end Cast

/-! ### Multiplicative maps out of `R(ν)` -/

/-- Two multiplicative `k`-linear maps out of `R(ν)` which agree on `1` and on the generators
`e_i`, `x_a`, `ψ_j` (`j + 1 < card ν`) are equal. -/
theorem ext_of_mul {ν : Multiset I} {B : Type*} [Ring B] [Algebra k B]
    (f g : KLRAlgebra k Q ν →ₗ[k] B) (hf : ∀ a b, f (a * b) = f a * f b)
    (hg : ∀ a b, g (a * b) = g a * g b) (h1 : f 1 = g 1) (he : ∀ i, f (e i) = g (e i))
    (hx : ∀ a, f (x a) = g (x a)) (hψ : ∀ j, j + 1 < Multiset.card ν → f (ψ j) = g (ψ j)) :
    f = g := by
  ext a
  obtain ⟨u, rfl⟩ := mk_surjective a
  induction u using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul, map_smul, h1]
  | grade1 g =>
    cases g with
    | idem i => exact he i
    | dot a => exact hx a
    | cross j =>
      change f (ψ j) = g (ψ j)
      by_cases hj : j + 1 < Multiset.card ν
      · exact hψ j hj
      · rw [ψ_eq_zero j (by omega), map_zero, map_zero]
  | mul u v hu hv => rw [map_mul, hf, hg, hu, hv]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]

/-! ### Concatenation with idempotents -/

section ConcatE

variable {ν ν' : Multiset I}

theorem concat_e_tmul_one (i : Seq ν) :
    concat Q ν ν' (e i ⊗ₜ 1) = ∑ j : Seq ν', e (i.append j) := by
  rw [← sum_e (ν := ν'), TensorProduct.tmul_sum, map_sum]
  simp only [concat_e_tmul_e]

theorem concat_one_tmul_e (j : Seq ν') :
    concat Q ν ν' (1 ⊗ₜ e j) = ∑ i : Seq ν, e (i.append j) := by
  rw [← sum_e (ν := ν), TensorProduct.sum_tmul, map_sum]
  simp only [concat_e_tmul_e]

theorem oneConcat_eq' :
    (oneConcat Q ν ν' : KLRAlgebra k Q (ν + ν')) = ∑ i : Seq ν, ∑ j : Seq ν', e (i.append j) := by
  rw [oneConcat_eq, Fintype.sum_prod_type]

theorem concat_one_tmul_one :
    concat Q ν ν' ((1 : KLRAlgebra k Q ν) ⊗ₜ (1 : KLRAlgebra k Q ν')) = oneConcat Q ν ν' :=
  concat_one

theorem oneConcat_mul_concat_tmul (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν') :
    oneConcat Q ν ν' * concat Q ν ν' (a ⊗ₜ b) = concat Q ν ν' (a ⊗ₜ b) :=
  oneConcat_mul_concat _

end ConcatE

/-! ### Associativity -/

section Assoc

variable (ν ν' ν'' : Multiset I)

/-- `ι_{ν+ν',ν''} (ι_{ν,ν'} (a ⊗ b) ⊗ d)`. -/
def concatL (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν') (d : KLRAlgebra k Q ν'') :
    KLRAlgebra k Q (ν + ν' + ν'') :=
  concat Q (ν + ν') ν'' (concat Q ν ν' (a ⊗ₜ b) ⊗ₜ d)

/-- `ι_{ν,ν'+ν''} (a ⊗ ι_{ν',ν''} (b ⊗ d))`. -/
def concatR (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν') (d : KLRAlgebra k Q ν'') :
    KLRAlgebra k Q (ν + (ν' + ν'')) :=
  concat Q ν (ν' + ν'') (a ⊗ₜ concat Q ν' ν'' (b ⊗ₜ d))

variable {ν ν' ν''}

theorem concatL_mul (a a' : KLRAlgebra k Q ν) (b b' : KLRAlgebra k Q ν')
    (d d' : KLRAlgebra k Q ν'') :
    concatL ν ν' ν'' (a * a') (b * b') (d * d') =
      concatL ν ν' ν'' a b d * concatL ν ν' ν'' a' b' d' := by
  simp only [concatL, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul]

theorem concatR_mul (a a' : KLRAlgebra k Q ν) (b b' : KLRAlgebra k Q ν')
    (d d' : KLRAlgebra k Q ν'') :
    concatR ν ν' ν'' (a * a') (b * b') (d * d') =
      concatR ν ν' ν'' a b d * concatR ν ν' ν'' a' b' d' := by
  simp only [concatR, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul]

theorem concatL_factor (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν') (d : KLRAlgebra k Q ν'') :
    concatL ν ν' ν'' a b d =
      concatL ν ν' ν'' a 1 1 * concatL ν ν' ν'' 1 b 1 * concatL ν ν' ν'' 1 1 d := by
  rw [← concatL_mul, ← concatL_mul]; simp

theorem concatR_factor (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν') (d : KLRAlgebra k Q ν'') :
    concatR ν ν' ν'' a b d =
      concatR ν ν' ν'' a 1 1 * concatR ν ν' ν'' 1 b 1 * concatR ν ν' ν'' 1 1 d := by
  rw [← concatR_mul, ← concatR_mul]; simp

theorem concatL_one :
    (concatL ν ν' ν'' 1 1 1 : KLRAlgebra k Q (ν + ν' + ν'')) =
      ∑ i : Seq ν, ∑ j : Seq ν', ∑ l : Seq ν'', e ((i.append j).append l) := by
  rw [concatL, concat_one_tmul_one, oneConcat_eq', TensorProduct.sum_tmul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.sum_tmul, map_sum]
  exact Finset.sum_congr rfl fun j _ => concat_e_tmul_one _

theorem concatR_one :
    (concatR ν ν' ν'' 1 1 1 : KLRAlgebra k Q (ν + (ν' + ν''))) =
      ∑ i : Seq ν, ∑ j : Seq ν', ∑ l : Seq ν'', e (i.append (j.append l)) := by
  rw [concatR, concat_one_tmul_one, oneConcat_eq', TensorProduct.tmul_sum, map_sum,
    ← sum_e (ν := ν), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [TensorProduct.tmul_sum, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [TensorProduct.sum_tmul, map_sum]
  simp only [concat_e_tmul_e]

theorem castKLR_sum_e {μ μ' : Multiset I} (h : μ = μ') {ι : Type*} (s : Finset ι)
    (f : ι → Seq μ) :
    castKLR Q h (∑ t ∈ s, e (f t)) = ∑ t ∈ s, e (Seq.cast h (f t)) := by
  rw [map_sum]; simp only [castKLR_e]

/-- The triple idempotents agree. -/
theorem castKLR_concatL_one :
    castKLR Q (add_assoc ν ν' ν'') (concatL ν ν' ν'' 1 1 1) = concatR ν ν' ν'' 1 1 1 := by
  rw [concatL_one, concatR_one, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [castKLR_sum_e]
  simp only [Seq.append_assoc]

/-! #### Factorizations through the triple idempotent -/

theorem concatL_one_eq : (concatL ν ν' ν'' 1 1 1 : KLRAlgebra k Q (ν + ν' + ν'')) =
    concat Q (ν + ν') ν'' (oneConcat Q ν ν' ⊗ₜ 1) := by
  rw [concatL, concat_one_tmul_one]

theorem concatR_one_eq : (concatR ν ν' ν'' 1 1 1 : KLRAlgebra k Q (ν + (ν' + ν''))) =
    concat Q ν (ν' + ν'') (1 ⊗ₜ oneConcat Q ν' ν'') := by
  rw [concatR, concat_one_tmul_one]

theorem concat_mul_oneConcat_tmul_one (X : KLRAlgebra k Q (ν + ν')) :
    concat Q (ν + ν') ν'' ((X * oneConcat Q ν ν') ⊗ₜ 1) =
      concat Q (ν + ν') ν'' (X ⊗ₜ 1) * concatL ν ν' ν'' 1 1 1 := by
  rw [concatL_one_eq, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem concat_oneConcat_tmul (d : KLRAlgebra k Q ν'') :
    concat Q (ν + ν') ν'' (oneConcat Q ν ν' ⊗ₜ d) =
      concat Q (ν + ν') ν'' (1 ⊗ₜ d) * concatL ν ν' ν'' 1 1 1 := by
  rw [concatL_one_eq, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem concat_one_tmul_mul_oneConcat (Z : KLRAlgebra k Q (ν' + ν'')) :
    concat Q ν (ν' + ν'') (1 ⊗ₜ (Z * oneConcat Q ν' ν'')) =
      concat Q ν (ν' + ν'') (1 ⊗ₜ Z) * concatR ν ν' ν'' 1 1 1 := by
  rw [concatR_one_eq, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem concat_tmul_oneConcat (a : KLRAlgebra k Q ν) :
    concat Q ν (ν' + ν'') (a ⊗ₜ oneConcat Q ν' ν'') =
      concat Q ν (ν' + ν'') (a ⊗ₜ 1) * concatR ν ν' ν'' 1 1 1 := by
  rw [concatR_one_eq, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem oneConcat_mul_concatL (y : KLRAlgebra k Q (ν + ν' + ν'')) :
    y * oneConcat Q (ν + ν') ν'' * concatL ν ν' ν'' 1 1 1 = y * concatL ν ν' ν'' 1 1 1 := by
  rw [mul_assoc, concatL, oneConcat_mul_concat]

theorem oneConcat_mul_concatR (y : KLRAlgebra k Q (ν + (ν' + ν''))) :
    y * oneConcat Q ν (ν' + ν'') * concatR ν ν' ν'' 1 1 1 = y * concatR ν ν' ν'' 1 1 1 := by
  rw [mul_assoc, concatR, oneConcat_mul_concat]

/-! #### The three slots -/

variable (ν ν' ν'') in
/-- `a ↦ castKLR (ι (ι (a ⊗ 1) ⊗ 1))`. -/
def slotL₁ : KLRAlgebra k Q ν →ₗ[k] KLRAlgebra k Q (ν + (ν' + ν'')) where
  toFun a := castKLR Q (add_assoc ν ν' ν'') (concatL ν ν' ν'' a 1 1)
  map_add' a a' := by simp [concatL, TensorProduct.add_tmul]
  map_smul' c a := by
    simp only [concatL, RingHom.id_apply]
    rw [← TensorProduct.smul_tmul', map_smul, ← TensorProduct.smul_tmul', map_smul, map_smul]

variable (ν ν' ν'') in
/-- `a ↦ ι (a ⊗ ι (1 ⊗ 1))`. -/
def slotR₁ : KLRAlgebra k Q ν →ₗ[k] KLRAlgebra k Q (ν + (ν' + ν'')) where
  toFun a := concatR ν ν' ν'' a 1 1
  map_add' a a' := by simp [concatR, TensorProduct.add_tmul]
  map_smul' c a := by
    simp only [concatR, RingHom.id_apply]
    rw [← TensorProduct.smul_tmul', map_smul]

variable (ν ν' ν'') in
/-- `b ↦ castKLR (ι (ι (1 ⊗ b) ⊗ 1))`. -/
def slotL₂ : KLRAlgebra k Q ν' →ₗ[k] KLRAlgebra k Q (ν + (ν' + ν'')) where
  toFun b := castKLR Q (add_assoc ν ν' ν'') (concatL ν ν' ν'' 1 b 1)
  map_add' b b' := by simp [concatL, TensorProduct.tmul_add, TensorProduct.add_tmul]
  map_smul' c b := by
    simp only [concatL, RingHom.id_apply]
    rw [TensorProduct.tmul_smul, map_smul, ← TensorProduct.smul_tmul', map_smul, map_smul]

variable (ν ν' ν'') in
/-- `b ↦ ι (1 ⊗ ι (b ⊗ 1))`. -/
def slotR₂ : KLRAlgebra k Q ν' →ₗ[k] KLRAlgebra k Q (ν + (ν' + ν'')) where
  toFun b := concatR ν ν' ν'' 1 b 1
  map_add' b b' := by simp [concatR, TensorProduct.tmul_add, TensorProduct.add_tmul]
  map_smul' c b := by
    simp only [concatR, RingHom.id_apply]
    rw [← TensorProduct.smul_tmul', map_smul, TensorProduct.tmul_smul, map_smul]

variable (ν ν' ν'') in
/-- `d ↦ castKLR (ι (ι (1 ⊗ 1) ⊗ d))`. -/
def slotL₃ : KLRAlgebra k Q ν'' →ₗ[k] KLRAlgebra k Q (ν + (ν' + ν'')) where
  toFun d := castKLR Q (add_assoc ν ν' ν'') (concatL ν ν' ν'' 1 1 d)
  map_add' d d' := by simp [concatL, TensorProduct.tmul_add]
  map_smul' c d := by
    simp only [concatL, RingHom.id_apply]
    rw [TensorProduct.tmul_smul, map_smul, map_smul]

variable (ν ν' ν'') in
/-- `d ↦ ι (1 ⊗ ι (1 ⊗ d))`. -/
def slotR₃ : KLRAlgebra k Q ν'' →ₗ[k] KLRAlgebra k Q (ν + (ν' + ν'')) where
  toFun d := concatR ν ν' ν'' 1 1 d
  map_add' d d' := by simp [concatR, TensorProduct.tmul_add]
  map_smul' c d := by
    simp only [concatR, RingHom.id_apply]
    rw [TensorProduct.tmul_smul, map_smul, TensorProduct.tmul_smul, map_smul]

theorem slotL₁_eq : slotL₁ (Q := Q) ν ν' ν'' = slotR₁ ν ν' ν'' := by
  refine ext_of_mul _ _ (fun a a' => ?_) (fun a a' => ?_) ?_ (fun i => ?_) (fun a => ?_)
    (fun j hj => ?_)
  · show castKLR Q _ (concatL ν ν' ν'' (a * a') 1 1) = _
    rw [show concatL ν ν' ν'' (a * a') (1 : KLRAlgebra k Q ν') (1 : KLRAlgebra k Q ν'') =
      concatL ν ν' ν'' (a * a') (1 * 1) (1 * 1) by simp, concatL_mul, map_mul]; rfl
  · show concatR ν ν' ν'' (a * a') 1 1 = _
    rw [show concatR ν ν' ν'' (a * a') (1 : KLRAlgebra k Q ν') (1 : KLRAlgebra k Q ν'') =
      concatR ν ν' ν'' (a * a') (1 * 1) (1 * 1) by simp, concatR_mul]; rfl
  · exact castKLR_concatL_one
  · show castKLR Q _ (concat Q (ν + ν') ν'' (concat Q ν ν' (e i ⊗ₜ 1) ⊗ₜ 1)) =
      concat Q ν (ν' + ν'') (e i ⊗ₜ concat Q ν' ν'' (1 ⊗ₜ 1))
    rw [concat_e_tmul_one, TensorProduct.sum_tmul, map_sum, map_sum, concat_one_tmul_one,
      oneConcat_eq',
      TensorProduct.tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [concat_e_tmul_one, castKLR_sum_e, TensorProduct.tmul_sum, map_sum]
    simp only [concat_e_tmul_e, Seq.append_assoc]
  · show castKLR Q _ (concat Q (ν + ν') ν'' (concat Q ν ν' (x a ⊗ₜ 1) ⊗ₜ 1)) =
      concat Q ν (ν' + ν'') (x a ⊗ₜ concat Q ν' ν'' (1 ⊗ₜ 1))
    rw [concat_x_tmul_one, concat_mul_oneConcat_tmul_one, concat_x_tmul_one,
      oneConcat_mul_concatL, map_mul, castKLR_concatL_one, castKLR_x, concat_one_tmul_one,
      concat_tmul_oneConcat, concat_x_tmul_one, oneConcat_mul_concatR]
    congr 2
  · have hj' : j + 1 < Multiset.card (ν + ν') := by simp; omega
    show castKLR Q _ (concat Q (ν + ν') ν'' (concat Q ν ν' (ψ j ⊗ₜ 1) ⊗ₜ 1)) =
      concat Q ν (ν' + ν'') (ψ j ⊗ₜ concat Q ν' ν'' (1 ⊗ₜ 1))
    rw [concat_ψ_tmul_one hj, concat_mul_oneConcat_tmul_one, concat_ψ_tmul_one hj',
      oneConcat_mul_concatL, map_mul, castKLR_concatL_one, castKLR_ψ, concat_one_tmul_one,
      concat_tmul_oneConcat, concat_ψ_tmul_one hj, oneConcat_mul_concatR]

theorem slotL₂_eq : slotL₂ (Q := Q) ν ν' ν'' = slotR₂ ν ν' ν'' := by
  refine ext_of_mul _ _ (fun b b' => ?_) (fun b b' => ?_) ?_ (fun j => ?_) (fun b => ?_)
    (fun j hj => ?_)
  · show castKLR Q _ (concatL ν ν' ν'' 1 (b * b') 1) = _
    rw [show concatL ν ν' ν'' (1 : KLRAlgebra k Q ν) (b * b') (1 : KLRAlgebra k Q ν'') =
      concatL ν ν' ν'' (1 * 1) (b * b') (1 * 1) by simp, concatL_mul, map_mul]; rfl
  · show concatR ν ν' ν'' 1 (b * b') 1 = _
    rw [show concatR ν ν' ν'' (1 : KLRAlgebra k Q ν) (b * b') (1 : KLRAlgebra k Q ν'') =
      concatR ν ν' ν'' (1 * 1) (b * b') (1 * 1) by simp, concatR_mul]; rfl
  · exact castKLR_concatL_one
  · show castKLR Q _ (concat Q (ν + ν') ν'' (concat Q ν ν' (1 ⊗ₜ e j) ⊗ₜ 1)) =
      concat Q ν (ν' + ν'') (1 ⊗ₜ concat Q ν' ν'' (e j ⊗ₜ 1))
    rw [concat_one_tmul_e, TensorProduct.sum_tmul, map_sum, map_sum, concat_e_tmul_one,
      TensorProduct.tmul_sum, map_sum]
    simp only [concat_e_tmul_one, concat_one_tmul_e, castKLR_sum_e, Seq.append_assoc]
    exact Finset.sum_comm
  · show castKLR Q _ (concat Q (ν + ν') ν'' (concat Q ν ν' (1 ⊗ₜ x b) ⊗ₜ 1)) =
      concat Q ν (ν' + ν'') (1 ⊗ₜ concat Q ν' ν'' (x b ⊗ₜ 1))
    rw [concat_one_tmul_x, concat_mul_oneConcat_tmul_one, concat_x_tmul_one,
      oneConcat_mul_concatL, map_mul, castKLR_concatL_one, castKLR_x, concat_x_tmul_one,
      concat_one_tmul_mul_oneConcat, concat_one_tmul_x, oneConcat_mul_concatR]
    congr 2
  · have hj₁ : Multiset.card ν + j + 1 < Multiset.card (ν + ν') := by simp; omega
    have hj₂ : j + 1 < Multiset.card (ν' + ν'') := by simp; omega
    show castKLR Q _ (concat Q (ν + ν') ν'' (concat Q ν ν' (1 ⊗ₜ ψ j) ⊗ₜ 1)) =
      concat Q ν (ν' + ν'') (1 ⊗ₜ concat Q ν' ν'' (ψ j ⊗ₜ 1))
    rw [concat_one_tmul_ψ hj, concat_mul_oneConcat_tmul_one, concat_ψ_tmul_one hj₁,
      oneConcat_mul_concatL, map_mul, castKLR_concatL_one, castKLR_ψ, concat_ψ_tmul_one hj,
      concat_one_tmul_mul_oneConcat, concat_one_tmul_ψ hj₂, oneConcat_mul_concatR]

theorem slotL₃_eq : slotL₃ (Q := Q) ν ν' ν'' = slotR₃ ν ν' ν'' := by
  refine ext_of_mul _ _ (fun d d' => ?_) (fun d d' => ?_) ?_ (fun l => ?_) (fun d => ?_)
    (fun j hj => ?_)
  · show castKLR Q _ (concatL ν ν' ν'' 1 1 (d * d')) = _
    rw [show concatL ν ν' ν'' (1 : KLRAlgebra k Q ν) (1 : KLRAlgebra k Q ν') (d * d') =
      concatL ν ν' ν'' (1 * 1) (1 * 1) (d * d') by simp, concatL_mul, map_mul]; rfl
  · show concatR ν ν' ν'' 1 1 (d * d') = _
    rw [show concatR ν ν' ν'' (1 : KLRAlgebra k Q ν) (1 : KLRAlgebra k Q ν') (d * d') =
      concatR ν ν' ν'' (1 * 1) (1 * 1) (d * d') by simp, concatR_mul]; rfl
  · exact castKLR_concatL_one
  · show castKLR Q _ (concat Q (ν + ν') ν'' (concat Q ν ν' (1 ⊗ₜ 1) ⊗ₜ e l)) =
      concat Q ν (ν' + ν'') (1 ⊗ₜ concat Q ν' ν'' (1 ⊗ₜ e l))
    rw [concat_one_tmul_one, concat_one_tmul_e, oneConcat_eq', TensorProduct.tmul_sum, map_sum]
    simp only [TensorProduct.sum_tmul, map_sum, concat_e_tmul_e, castKLR_e, concat_one_tmul_e,
      Seq.append_assoc]
    exact Finset.sum_comm
  · show castKLR Q _ (concat Q (ν + ν') ν'' (concat Q ν ν' (1 ⊗ₜ 1) ⊗ₜ x d)) =
      concat Q ν (ν' + ν'') (1 ⊗ₜ concat Q ν' ν'' (1 ⊗ₜ x d))
    rw [concat_one_tmul_one, concat_oneConcat_tmul, concat_one_tmul_x, oneConcat_mul_concatL,
      map_mul, castKLR_concatL_one, castKLR_x, concat_one_tmul_x,
      concat_one_tmul_mul_oneConcat, concat_one_tmul_x, oneConcat_mul_concatR]
    congr 2
    ext; simp [add_assoc]
  · have hj₁ : j + 1 < Multiset.card (ν' + ν'') := by simp; omega
    show castKLR Q _ (concat Q (ν + ν') ν'' (concat Q ν ν' (1 ⊗ₜ 1) ⊗ₜ ψ j)) =
      concat Q ν (ν' + ν'') (1 ⊗ₜ concat Q ν' ν'' (1 ⊗ₜ ψ j))
    rw [concat_one_tmul_one, concat_oneConcat_tmul, concat_one_tmul_ψ hj, oneConcat_mul_concatL,
      map_mul, castKLR_concatL_one, castKLR_ψ, concat_one_tmul_ψ hj,
      concat_one_tmul_mul_oneConcat, concat_one_tmul_ψ (by simp; omega),
      oneConcat_mul_concatR]
    congr 2
    simp [add_assoc]

/-- **Associativity of concatenation** (KL I, §2.6):
`ι_{ν+ν',ν''} (ι_{ν,ν'} (a ⊗ b) ⊗ d) = ι_{ν,ν'+ν''} (a ⊗ ι_{ν',ν''} (b ⊗ d))`, up to the
canonical isomorphism `R((ν + ν') + ν'') ≃ R(ν + (ν' + ν''))`. -/
theorem concat_assoc (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν') (d : KLRAlgebra k Q ν'') :
    castKLR Q (add_assoc ν ν' ν'')
        (concat Q (ν + ν') ν'' (concat Q ν ν' (a ⊗ₜ b) ⊗ₜ d)) =
      concat Q ν (ν' + ν'') (a ⊗ₜ concat Q ν' ν'' (b ⊗ₜ d)) := by
  have h1 := LinearMap.congr_fun (slotL₁_eq (Q := Q) (ν := ν) (ν' := ν') (ν'' := ν'')) a
  have h2 := LinearMap.congr_fun (slotL₂_eq (Q := Q) (ν := ν) (ν' := ν') (ν'' := ν'')) b
  have h3 := LinearMap.congr_fun (slotL₃_eq (Q := Q) (ν := ν) (ν' := ν') (ν'' := ν'')) d
  change castKLR Q _ (concatL ν ν' ν'' a b d) = concatR ν ν' ν'' a b d
  rw [concatL_factor, concatR_factor, map_mul, map_mul]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) h1 h2) h3

end Assoc

/-! ### Unitality -/

section Unit

variable {ν : Multiset I}

theorem castKLR_oneConcat_zero_left :
    castKLR Q (zero_add ν) (oneConcat Q 0 ν) = 1 := by
  rw [oneConcat_eq', map_sum, Fintype.sum_unique, castKLR_sum_e]
  simp only [Seq.nil_append]
  exact sum_e

theorem castKLR_oneConcat_zero_right :
    castKLR Q (add_zero ν) (oneConcat Q ν 0) = 1 := by
  rw [oneConcat_eq', map_sum]
  simp only [Fintype.sum_unique, castKLR_e, Seq.append_nil]
  exact sum_e

variable (ν) in
/-- `b ↦ castKLR (ι_{0,ν} (1 ⊗ b))`. -/
def unitL : KLRAlgebra k Q ν →ₗ[k] KLRAlgebra k Q ν where
  toFun b := castKLR Q (zero_add ν) (concat Q 0 ν (1 ⊗ₜ b))
  map_add' b b' := by simp [TensorProduct.tmul_add]
  map_smul' c b := by
    simp only [RingHom.id_apply]
    rw [TensorProduct.tmul_smul, map_smul, map_smul]

variable (ν) in
/-- `b ↦ castKLR (ι_{ν,0} (b ⊗ 1))`. -/
def unitR : KLRAlgebra k Q ν →ₗ[k] KLRAlgebra k Q ν where
  toFun b := castKLR Q (add_zero ν) (concat Q ν 0 (b ⊗ₜ 1))
  map_add' b b' := by simp [TensorProduct.add_tmul]
  map_smul' c b := by
    simp only [RingHom.id_apply]
    rw [← TensorProduct.smul_tmul', map_smul, map_smul]

theorem unitL_eq : unitL (Q := Q) ν = LinearMap.id := by
  refine ext_of_mul _ _ (fun b b' => ?_) (fun _ _ => rfl) ?_ (fun j => ?_) (fun b => ?_)
    (fun j hj => ?_)
  · show castKLR Q _ (concat Q 0 ν (1 ⊗ₜ (b * b'))) = castKLR Q _ (concat Q 0 ν (1 ⊗ₜ b)) *
      castKLR Q _ (concat Q 0 ν (1 ⊗ₜ b'))
    rw [← map_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · show castKLR Q _ (concat Q 0 ν (1 ⊗ₜ 1)) = 1
    rw [concat_one_tmul_one, castKLR_oneConcat_zero_left]
  · show castKLR Q _ (concat Q 0 ν (1 ⊗ₜ e j)) = e j
    rw [concat_one_tmul_e, Fintype.sum_unique, castKLR_e, Seq.nil_append]
  · show castKLR Q _ (concat Q 0 ν (1 ⊗ₜ x b)) = x b
    rw [concat_one_tmul_x, map_mul, castKLR_oneConcat_zero_left, mul_one, castKLR_x]
    congr 1
    ext; simp
  · show castKLR Q _ (concat Q 0 ν (1 ⊗ₜ ψ j)) = ψ j
    rw [concat_one_tmul_ψ hj, map_mul, castKLR_oneConcat_zero_left, mul_one, castKLR_ψ,
      Multiset.card_zero, zero_add]

theorem unitR_eq : unitR (Q := Q) ν = LinearMap.id := by
  refine ext_of_mul _ _ (fun b b' => ?_) (fun _ _ => rfl) ?_ (fun j => ?_) (fun b => ?_)
    (fun j hj => ?_)
  · show castKLR Q _ (concat Q ν 0 ((b * b') ⊗ₜ 1)) = castKLR Q _ (concat Q ν 0 (b ⊗ₜ 1)) *
      castKLR Q _ (concat Q ν 0 (b' ⊗ₜ 1))
    rw [← map_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · show castKLR Q _ (concat Q ν 0 (1 ⊗ₜ 1)) = 1
    rw [concat_one_tmul_one, castKLR_oneConcat_zero_right]
  · show castKLR Q _ (concat Q ν 0 (e j ⊗ₜ 1)) = e j
    rw [concat_e_tmul_one, Fintype.sum_unique, castKLR_e, Seq.append_nil]
  · show castKLR Q _ (concat Q ν 0 (x b ⊗ₜ 1)) = x b
    rw [concat_x_tmul_one, map_mul, castKLR_oneConcat_zero_right, mul_one, castKLR_x]
    congr 1
  · show castKLR Q _ (concat Q ν 0 (ψ j ⊗ₜ 1)) = ψ j
    rw [concat_ψ_tmul_one hj, map_mul, castKLR_oneConcat_zero_right, mul_one, castKLR_ψ]

/-- **Left unitality of concatenation**: `ι_{0,ν} (1 ⊗ b) = b` up to `R(0 + ν) ≃ R(ν)`. -/
theorem concat_one_left (b : KLRAlgebra k Q ν) :
    castKLR Q (zero_add ν) (concat Q 0 ν (1 ⊗ₜ b)) = b :=
  LinearMap.congr_fun unitL_eq b

/-- **Right unitality of concatenation**: `ι_{ν,0} (b ⊗ 1) = b` up to `R(ν + 0) ≃ R(ν)`. -/
theorem concat_one_right (b : KLRAlgebra k Q ν) :
    castKLR Q (add_zero ν) (concat Q ν 0 (b ⊗ₜ 1)) = b :=
  LinearMap.congr_fun unitR_eq b

end Unit

end KLRAlgebra

/-- `castKLR` is degree-preserving. -/
theorem GradingDatum.castKLR_mem_grade (G : GradingDatum Q) {μ μ' : Multiset I} (h : μ = μ')
    {a : KLRAlgebra k Q μ} {d : ℤ} (ha : a ∈ G.grade μ d) : castKLR Q h a ∈ G.grade μ' d := by
  subst h; exact ha

end Categorification.KLR

end
