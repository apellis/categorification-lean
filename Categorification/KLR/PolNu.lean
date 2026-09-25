/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.BasisTheorem
import Categorification.KLR.Symmetries
import Categorification.KLR.KL1Basis

/-!
# `R(ν)` is free over `Pol(ν)`

KL I (arXiv:0803.4121v2), §2.4, Proposition 2.7: `R(ν)` is a free module of rank `m!` over
the commutative subring

  `Pol(ν) = ∏_{i ∈ Seq(ν)} Pol(ν, i)`, `Pol(ν, i) = k[x_{1,i}, …, x_{m,i}] ⊆ 1_i R(ν) 1_i`,

for both the right and the left multiplication action, with basis `ŵ = ∑_i ψ_{ρ w} 1_i`
(`w ∈ S_m`), where `ρ w` is any choice of reduced words.

We model `Pol(ν)` as the commutative `k`-algebra `PolyRep.Pol k ν = Seq ν → k[x_1, …, x_m]`
(the same carrier as the polynomial representation), embedded in `R(ν)` by the algebra
homomorphism `polNu : f ↦ ∑_i pol (f i) * e i` (injective, `polNu_injective`). Since
`∑_i e i = 1`, the paper's `ŵ` is simply `ψw (ρ w)`.

## Main definitions

* `KLRAlgebra.polNu` : the embedding `Pol(ν) → R(ν)`.
* `KLRAlgebra.RightPolMod k Q ν`, `KLRAlgebra.LeftPolMod k Q ν` : type synonyms for `R(ν)`
  carrying the `Pol(ν)`-module structures `p • r = r * polNu p` and `p • r = polNu p * r`.

## Main results

* `KLRAlgebra.rightBasis` : **Proposition 2.7** (right action): the basis
  `w ↦ ψw (ρ w)` of `R(ν)` over `Pol(ν)`, for an integral domain `k` and data `Q`
  satisfying the hypotheses of the basis theorem (`KLRAlgebra.basis`).
* `KLRAlgebra.leftBasis` : **Proposition 2.7** (left action), deduced with the
  antiinvolution `hflip`.
* `KLRAlgebra.exists_unique_right_expansion`, `KLRAlgebra.exists_unique_left_expansion` :
  the same statements in elementary form: every `r` is uniquely `∑_w ψw (ρ w) * polNu (c w)`
  (resp. `∑_w polNu (c w) * ψw (ρ w)`).
* `KLRAlgebra.finrank_rightPolMod`, `KLRAlgebra.finrank_leftPolMod` : the rank is `m!`.
* `KL1.rightBasis`, `KL1.leftBasis`, `KL1.finrank_polMod` : the statements for the rings of
  KL I.

We also record that `Seq ν` is nonempty and that `S_m` acts transitively on it
(`Seq.exists_smul_eq`).
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA PolyRep

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν

namespace Seq

/-- There is a sequence of every weight. -/
instance : Nonempty (Seq ν) := by
  refine ⟨⟨fun a => ν.toList.get (Fin.cast (Multiset.length_toList ν).symm a), ?_⟩⟩
  rw [Fin.univ_val_map]
  conv_rhs => rw [← Multiset.coe_toList ν]
  congr 1
  apply List.ext_get
  · simp
  · intro n h1 h2; simp

/-- `S_m` acts transitively on the sequences of weight `ν`. -/
theorem exists_smul_eq (i j : Seq ν) : ∃ w : Perm (Fin m), w • i = j := by
  classical
  have hc : ∀ c, Fintype.card {a // i.1 a = c} = Fintype.card {a // j.1 a = c} := by
    intro c
    have h1 := congrArg (Multiset.count c) i.2
    have h2 := congrArg (Multiset.count c) j.2
    rw [Multiset.count_map] at h1 h2
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    simp only [eq_comm (a := c)] at h1 h2
    rw [h1, h2]
  let σ := Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c))
  refine ⟨σ, Subtype.ext (funext fun b => ?_)⟩
  rw [Seq.smul_apply]
  have := Equiv.ofFiberEquiv_map (fun c => Fintype.equivOfCardEq (hc c)) (σ.symm b)
  exact this.symm.trans (congrArg j.1 (σ.apply_symm_apply b))

instance : MulAction.IsPretransitive (Perm (Fin m)) (Seq ν) :=
  ⟨exists_smul_eq⟩

end Seq

namespace KLRAlgebra

/-! ### The subring `Pol(ν)` -/

theorem pol_mul_e_mul_pol_mul_e (p q : MvPolynomial (Fin m) k) (i j : Seq ν) :
    (pol p * e i * (pol q * e j) : KLRAlgebra k Q ν) =
      if i = j then pol (p * q) * e i else 0 := by
  have : (pol p * e i * (pol q * e j) : KLRAlgebra k Q ν) = pol p * pol q * (e i * e j) := by
    rw [mul_assoc, ← mul_assoc (e i), (e_commute_pol i q).eq]
    simp only [mul_assoc]
  rw [this, e_mul_e, map_mul]
  split_ifs <;> simp

/-- The embedding `Pol(ν) = ∏_i Pol(ν, i) → R(ν)`, `f ↦ ∑_i f_i(x) 1_i`. -/
noncomputable def polNu : Pol k ν →ₐ[k] KLRAlgebra k Q ν where
  toFun f := ∑ i, pol (f i) * e i
  map_one' := by simp only [Pi.one_apply, map_one, one_mul, sum_e]
  map_mul' f g := by
    simp only [Finset.sum_mul, Finset.mul_sum, pol_mul_e_mul_pol_mul_e, Pi.mul_apply]
    rw [Finset.sum_comm]
    simp
  map_zero' := by simp
  map_add' f g := by simp [add_mul, Finset.sum_add_distrib]
  commutes' c := by
    simp only [Pi.algebraMap_apply, AlgHom.commutes, ← Finset.mul_sum, sum_e, mul_one]

theorem polNu_apply (f : Pol k ν) : (polNu f : KLRAlgebra k Q ν) = ∑ i, pol (f i) * e i := rfl

theorem polNu_mul_e (f : Pol k ν) (i : Seq ν) :
    (polNu f * e i : KLRAlgebra k Q ν) = pol (f i) * e i := by
  rw [polNu_apply, Finset.sum_mul]
  simp only [mul_assoc, e_mul_e, mul_ite, mul_zero]
  simp

theorem e_mul_polNu (f : Pol k ν) (i : Seq ν) :
    (e i * polNu f : KLRAlgebra k Q ν) = pol (f i) * e i := by
  rw [polNu_apply, Finset.mul_sum]
  simp only [← mul_assoc, (e_commute_pol _ _).eq]
  simp only [mul_assoc, e_mul_e, mul_ite, mul_zero]
  simp

theorem e_commute_polNu (f : Pol k ν) (i : Seq ν) : Commute (e i : KLRAlgebra k Q ν) (polNu f) :=
  (e_mul_polNu f i).trans (polNu_mul_e f i).symm

theorem polNu_single (i : Seq ν) (p : MvPolynomial (Fin m) k) :
    (polNu (Pi.single i p) : KLRAlgebra k Q ν) = pol p * e i := by
  rw [polNu_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem polNu_commute (f g : Pol k ν) : Commute (polNu f : KLRAlgebra k Q ν) (polNu g) := by
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

section polyRep

variable {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))

theorem polyRep_polNu_apply (f : Pol k ν) (g : Pol k ν) (t : Seq ν) :
    polyRep hPQ (polNu f : KLRAlgebra k Q ν) g t = f t * g t := by
  rw [polNu_apply, map_sum]
  simp only [map_mul, polyRep_pol, polyRep_e, LinearMap.coeFn_sum, Finset.sum_apply,
    Module.End.mul_apply, opMul_apply, opE_apply]
  simp

include hPQ in
/-- `Pol(ν)` embeds in `R(ν)` (as soon as `R(ν)` has a polynomial representation). -/
theorem polNu_injective : Function.Injective (polNu : Pol k ν → KLRAlgebra k Q ν) := by
  intro f g h
  funext i
  have := congrArg (fun r => polyRep hPQ r (Pi.single i 1) i) h
  simpa [polyRep_polNu_apply] using this

end polyRep

/-! ### The right `Pol(ν)`-module structure -/

variable (k Q ν) in
/-- `R(ν)` regarded as a module over `Pol(ν)` acting by right multiplication,
`p • r = r * polNu p`. -/
def RightPolMod : Type _ := KLRAlgebra k Q ν

namespace RightPolMod

noncomputable instance : AddCommGroup (RightPolMod k Q ν) :=
  inferInstanceAs (AddCommGroup (KLRAlgebra k Q ν))

/-- The identification of `R(ν)` with `RightPolMod k Q ν`. -/
def of : KLRAlgebra k Q ν ≃+ RightPolMod k Q ν := AddEquiv.refl _

noncomputable instance : Module (Pol k ν) (RightPolMod k Q ν) where
  smul p r := of (of.symm r * polNu p)
  one_smul r := by
    show of (of.symm r * polNu 1) = r
    rw [map_one, mul_one]; rfl
  mul_smul p q r := by
    show of (of.symm r * polNu (p * q)) = of (of.symm (of (of.symm r * polNu q)) * polNu p)
    rw [AddEquiv.symm_apply_apply, mul_assoc, ← map_mul, mul_comm q p]
  smul_zero p := by
    show of (of.symm 0 * polNu p) = 0
    rw [map_zero, zero_mul, map_zero]
  smul_add p r s := by
    show of (of.symm (r + s) * polNu p) = of (of.symm r * polNu p) + of (of.symm s * polNu p)
    rw [map_add, add_mul, map_add]
  add_smul p q r := by
    show of (of.symm r * polNu (p + q)) = of (of.symm r * polNu p) + of (of.symm r * polNu q)
    rw [map_add, mul_add, map_add]
  zero_smul r := by
    show of (of.symm r * polNu 0) = 0
    rw [map_zero, mul_zero, map_zero]

theorem smul_def (p : Pol k ν) (r : RightPolMod k Q ν) :
    p • r = of (of.symm r * polNu p) := rfl

theorem smul_of (p : Pol k ν) (r : KLRAlgebra k Q ν) :
    p • of r = of (r * polNu p) := rfl

end RightPolMod

/-! ### The left `Pol(ν)`-module structure -/

variable (k Q ν) in
/-- `R(ν)` regarded as a module over `Pol(ν)` acting by left multiplication,
`p • r = polNu p * r`. -/
def LeftPolMod : Type _ := KLRAlgebra k Q ν

namespace LeftPolMod

noncomputable instance : AddCommGroup (LeftPolMod k Q ν) :=
  inferInstanceAs (AddCommGroup (KLRAlgebra k Q ν))

/-- The identification of `R(ν)` with `LeftPolMod k Q ν`. -/
def of : KLRAlgebra k Q ν ≃+ LeftPolMod k Q ν := AddEquiv.refl _

noncomputable instance : Module (Pol k ν) (LeftPolMod k Q ν) where
  smul p r := of (polNu p * of.symm r)
  one_smul r := by
    show of (polNu 1 * of.symm r) = r
    rw [map_one, one_mul]; rfl
  mul_smul p q r := by
    show of (polNu (p * q) * of.symm r) = of (polNu p * of.symm (of (polNu q * of.symm r)))
    rw [AddEquiv.symm_apply_apply, ← mul_assoc, ← map_mul]
  smul_zero p := by
    show of (polNu p * of.symm 0) = 0
    rw [map_zero, mul_zero, map_zero]
  smul_add p r s := by
    show of (polNu p * of.symm (r + s)) = of (polNu p * of.symm r) + of (polNu p * of.symm s)
    rw [map_add, mul_add, map_add]
  add_smul p q r := by
    show of (polNu (p + q) * of.symm r) = of (polNu p * of.symm r) + of (polNu q * of.symm r)
    rw [map_add, add_mul, map_add]
  zero_smul r := by
    show of (polNu 0 * of.symm r) = 0
    rw [map_zero, zero_mul, map_zero]

theorem smul_def (p : Pol k ν) (r : LeftPolMod k Q ν) :
    p • r = of (polNu p * of.symm r) := rfl

theorem smul_of (p : Pol k ν) (r : KLRAlgebra k Q ν) :
    p • of r = of (polNu p * r) := rfl

end LeftPolMod

/-! ### Expansion of products `ψ_ρ f` in the standard basis -/

theorem mul_pol_mul_e_eq_sum (r : KLRAlgebra k Q ν) (p : MvPolynomial (Fin m) k) (i : Seq ν)
    (U : Finset (Fin m →₀ ℕ)) (hU : p.support ⊆ U) :
    r * pol p * e i = ∑ u ∈ U, coeff u p • (r * pol (monomial u 1) * e i) := by
  conv_lhs => rw [p.as_sum, Finset.sum_subset hU (fun u _ hu => by
    rw [not_mem_support_iff.1 hu, monomial_zero])]
  simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  have : (monomial u (coeff u p) : MvPolynomial (Fin m) k) = coeff u p • monomial u 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, mul_smul_comm, smul_mul_assoc]

theorem sum_ψw_mul_polNu_eq (ρ : Perm (Fin m) → List ℕ) (c : Perm (Fin m) → Pol k ν)
    (U : Finset (Fin m →₀ ℕ)) (hU : ∀ w i, (c w i).support ⊆ U) :
    (∑ w, ψw (ρ w) * polNu (c w) : KLRAlgebra k Q ν) =
      ∑ x ∈ Finset.univ ×ˢ Finset.univ ×ˢ U, coeff x.2.2 (c x.2.1 x.1) • stdElt ρ x := by
  simp only [Finset.sum_product]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [polNu_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, mul_pol_mul_e_eq_sum _ _ _ U (hU w i)]
  rfl

/-- The paper's `ŵ = ∑_i ŵ_i`, `ŵ_i = ψ_{ρ w} 1_i`, is `ψw (ρ w)`. -/
theorem ψw_eq_sum_mul_e (ρ : List ℕ) : (ψw ρ : KLRAlgebra k Q ν) = ∑ i, ψw ρ * e i := by
  rw [← Finset.mul_sum, sum_e, mul_one]

/-! ### Proposition 2.7, right action -/

section Basis

variable {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)

include hρ in
/-- Every element of `R(ν)` is a right `Pol(ν)`-combination `∑_w ψ_{ρ w} f_w`. -/
theorem exists_sum_ψw_mul_polNu (r : KLRAlgebra k Q ν) :
    ∃ c : Perm (Fin m) → Pol k ν, ∑ w, ψw (ρ w) * polNu (c w) = r := by
  have hr : r ∈ Submodule.span k (Set.range (stdElt (k := k) (Q := Q) ρ)) := by
    rw [span_stdElt ρ hρ]; trivial
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨i, w, u⟩, rfl⟩ := hx
    refine ⟨Pi.single w (Pi.single i (monomial u 1)), ?_⟩
    rw [Finset.sum_eq_single w (fun w' _ hw' => by simp [hw']) (by simp)]
    simp [polNu_single, stdElt, mul_assoc]
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c', rfl⟩ := hy
    exact ⟨c + c', by simp [mul_add, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨c, rfl⟩ := hx
    exact ⟨a • c, by simp [Finset.smul_sum, mul_smul_comm]⟩

variable [IsDomain k]

include hPQ hP hρ in
/-- Right `Pol(ν)`-combinations of the `ψ_{ρ w}` are independent. -/
theorem eq_zero_of_sum_ψw_mul_polNu_eq_zero (c : Perm (Fin m) → Pol k ν)
    (h : (∑ w, ψw (ρ w) * polNu (c w) : KLRAlgebra k Q ν) = 0) : c = 0 := by
  classical
  set U : Finset (Fin m →₀ ℕ) :=
    Finset.univ.biUnion fun w => Finset.univ.biUnion fun i => (c w i).support
  have hU : ∀ w i, (c w i).support ⊆ U := fun w i u hu =>
    Finset.mem_biUnion.2 ⟨w, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hu⟩⟩
  rw [sum_ψw_mul_polNu_eq ρ c U hU] at h
  have := linearIndependent_iff'.1 (linearIndependent_stdElt hPQ hP ρ hρ) _ _ h
  funext w i
  ext u
  by_cases hu : u ∈ U
  · simpa using this (i, w, u) (by simp [hu])
  · simp only [Pi.zero_apply, coeff_zero]
    exact not_mem_support_iff.1 fun h' => hu (hU w i h')

/-- **KL I, Proposition 2.7** (right action). For an integral domain `k`, data `Q` as in the
basis theorem and any choice `ρ` of reduced words, `R(ν)` is a free right `Pol(ν)`-module
with basis `ŵ = ψ_{ρ w}` (`w ∈ S_m`); in particular it has rank `m!`. -/
noncomputable def rightBasis : Basis (Perm (Fin m)) (Pol k ν) (RightPolMod k Q ν) :=
  Basis.mk (v := fun w => RightPolMod.of (ψw (ρ w)))
    (Fintype.linearIndependent_iff.2 fun g hg w => by
      simp only [RightPolMod.smul_of, ← map_sum] at hg
      have := eq_zero_of_sum_ψw_mul_polNu_eq_zero hPQ hP ρ hρ g
        ((map_eq_zero_iff _ RightPolMod.of.injective).1 hg)
      exact congrFun this w)
    (fun r _ => by
      obtain ⟨c, hc⟩ := exists_sum_ψw_mul_polNu ρ hρ (RightPolMod.of.symm r)
      have : r = ∑ w, c w • RightPolMod.of (ψw (ρ w) : KLRAlgebra k Q ν) := by
        simp only [RightPolMod.smul_of, ← map_sum, hc, AddEquiv.apply_symm_apply]
      rw [this]
      exact Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩))

theorem rightBasis_apply (w : Perm (Fin m)) :
    rightBasis hPQ hP ρ hρ w = RightPolMod.of (ψw (ρ w) : KLRAlgebra k Q ν) := by
  simp [rightBasis]

omit hρ in
include hPQ hP in
/-- The rank of `R(ν)` over `Pol(ν)` (right action) is `m!`. -/
theorem finrank_rightPolMod :
    Module.finrank (Pol k ν) (RightPolMod k Q ν) = (Multiset.card ν).factorial := by
  rw [Module.finrank_eq_card_basis (rightBasis hPQ hP (fun w => canWord m w)
    (fun w => ⟨isReduced_canWord m w, wordProd_canWord m w⟩)), Fintype.card_perm,
    Fintype.card_fin]

include hPQ hP hρ in
/-- **KL I, Proposition 2.7** (right action), elementary form: every `r ∈ R(ν)` is uniquely
`∑_w ψ_{ρ w} f_w` with `f_w ∈ Pol(ν)`. -/
theorem exists_unique_right_expansion (r : KLRAlgebra k Q ν) :
    ∃! c : Perm (Fin m) → Pol k ν, ∑ w, ψw (ρ w) * polNu (c w) = r := by
  obtain ⟨c, hc⟩ := exists_sum_ψw_mul_polNu ρ hρ r
  refine ⟨c, hc, fun c' hc' => ?_⟩
  simp only at hc'
  have := eq_zero_of_sum_ψw_mul_polNu_eq_zero hPQ hP ρ hρ (c' - c) (by
    simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib, hc, hc', sub_self])
  exact sub_eq_zero.1 this

/-! ### Proposition 2.7, left action -/

omit [IsDomain k] in
theorem hflip_polNu (f : Pol k ν) : hflip (polNu f : KLRAlgebra k Q ν) = polNu f := by
  simp only [polNu_apply, hflip_sum, hflip_mul, hflip_e, hflip_pol, (e_commute_pol _ _).eq]

omit [IsDomain k] in
theorem hflip_ψw (σ : List ℕ) : hflip (ψw σ : KLRAlgebra k Q ν) = ψw σ.reverse := by
  induction σ with
  | nil => simp
  | cons j σ ih => simp [ih]

omit [IsDomain k] [DecidableEq I] in
theorem isReduced_reverse {σ : List ℕ} (h : IsReduced m σ) : IsReduced m σ.reverse :=
  ⟨validWord_reverse.2 h.1, by rw [List.length_reverse, wordProd_reverse, length_inv]; exact h.2⟩

variable (k Q ν) in
/-- The antiinvolution `hflip` as a `Pol(ν)`-linear isomorphism between the left and the
right `Pol(ν)`-module `R(ν)`. -/
noncomputable def flipPolMod : LeftPolMod k Q ν ≃ₗ[Pol k ν] RightPolMod k Q ν where
  toFun r := RightPolMod.of (hflip (LeftPolMod.of.symm r))
  invFun r := LeftPolMod.of (hflip (RightPolMod.of.symm r))
  map_add' r s := by simp only [map_add, hflip_add]
  map_smul' p r := by
    rw [LeftPolMod.smul_def, RingHom.id_apply, RightPolMod.smul_def, AddEquiv.symm_apply_apply,
      AddEquiv.symm_apply_apply, hflip_mul, hflip_polNu]
  left_inv r := by
    simp only [AddEquiv.symm_apply_apply, hflip_hflip, AddEquiv.apply_symm_apply]
  right_inv r := by
    simp only [AddEquiv.symm_apply_apply, hflip_hflip, AddEquiv.apply_symm_apply]

omit [DecidableEq I] [IsDomain k] in
include hρ in
/-- If `ρ w` are reduced words for `w`, then `(ρ w⁻¹).reverse` are reduced words for `w`. -/
theorem reverse_inv_reduced : ∀ w, IsReduced m ((ρ w⁻¹).reverse) ∧ wordProd m ((ρ w⁻¹).reverse) = w :=
  fun w => ⟨isReduced_reverse (hρ w⁻¹).1, by rw [wordProd_reverse, (hρ w⁻¹).2, inv_inv]⟩

/-- **KL I, Proposition 2.7** (left action). For an integral domain `k`, data `Q` as in the
basis theorem and any choice `ρ` of reduced words, `R(ν)` is a free left `Pol(ν)`-module
with basis `ŵ = ψ_{ρ w}` (`w ∈ S_m`). Deduced from the right action with `hflip`. -/
noncomputable def leftBasis : Basis (Perm (Fin m)) (Pol k ν) (LeftPolMod k Q ν) :=
  ((rightBasis hPQ hP (fun w => (ρ w⁻¹).reverse) (reverse_inv_reduced ρ hρ)).map
    (flipPolMod k Q ν).symm).reindex (Equiv.inv _)

theorem leftBasis_apply (w : Perm (Fin m)) :
    leftBasis hPQ hP ρ hρ w = LeftPolMod.of (ψw (ρ w) : KLRAlgebra k Q ν) := by
  simp only [leftBasis, Basis.reindex_apply, Basis.map_apply, rightBasis_apply]
  show LeftPolMod.of (hflip (ψw (ρ ((Equiv.inv _).symm w)⁻¹).reverse)) = _
  rw [hflip_ψw, List.reverse_reverse]
  simp

omit hρ in
include hPQ hP in
/-- The rank of `R(ν)` over `Pol(ν)` (left action) is `m!`. -/
theorem finrank_leftPolMod :
    Module.finrank (Pol k ν) (LeftPolMod k Q ν) = (Multiset.card ν).factorial := by
  rw [Module.finrank_eq_card_basis (leftBasis hPQ hP (fun w => canWord m w)
    (fun w => ⟨isReduced_canWord m w, wordProd_canWord m w⟩)), Fintype.card_perm,
    Fintype.card_fin]

include hPQ hP hρ in
/-- **KL I, Proposition 2.7** (left action), elementary form: every `r ∈ R(ν)` is uniquely
`∑_w f_w ψ_{ρ w}` with `f_w ∈ Pol(ν)`. -/
theorem exists_unique_left_expansion (r : KLRAlgebra k Q ν) :
    ∃! c : Perm (Fin m) → Pol k ν, ∑ w, polNu (c w) * ψw (ρ w) = r := by
  let b := leftBasis hPQ hP ρ hρ
  have key : ∀ c : Perm (Fin m) → Pol k ν,
      ∑ w, c w • b w = LeftPolMod.of (∑ w, polNu (c w) * ψw (ρ w)) := by
    intro c
    simp only [b, leftBasis_apply, LeftPolMod.smul_of, map_sum]
  refine ⟨fun w => b.repr (LeftPolMod.of r) w, ?_, fun c hc => ?_⟩
  · apply LeftPolMod.of.injective
    rw [← key, b.sum_repr]
  · have : ∑ w, c w • b w = LeftPolMod.of r := by rw [key, hc]
    rw [← this, b.repr_sum_self]

end Basis

end KLRAlgebra

/-! ### The rings of KL I -/

namespace KL1

open KLRAlgebra

variable {Γ : SimpleGraph I} [DecidableRel Γ.Adj]

/-- `Pol(ν) ⊆ R(ν)` for the rings of KL I, over any commutative ring. -/
theorem polNu_injective : Function.Injective (polNu : Pol k ν → R1 k Γ ν) :=
  KLRAlgebra.polNu_injective (klQ_eq_klP (Γ := Γ) stdOrient_spec)

variable [IsDomain k] (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)

/-- **KL I, Proposition 2.7** (right action) for the rings `R(ν)` of KL I (over `ℤ`, or any
integral domain): `R(ν)` is a free right `Pol(ν)`-module with basis `ψ_{ρ w}`, `w ∈ S_m`. -/
noncomputable def rightBasis :
    Basis (Perm (Fin (Multiset.card ν))) (Pol k ν) (RightPolMod k (klQ (k := k) Γ) ν) :=
  KLRAlgebra.rightBasis (klQ_eq_klP (Γ := Γ) stdOrient_spec) (fun a b _ => klP_ne_zero _ a b)
    ρ hρ

theorem rightBasis_apply (w : Perm (Fin m)) :
    KL1.rightBasis (k := k) (Γ := Γ) ρ hρ w = RightPolMod.of (ψw (ρ w) : R1 k Γ ν) :=
  KLRAlgebra.rightBasis_apply _ _ ρ hρ w

/-- **KL I, Proposition 2.7** (left action) for the rings `R(ν)` of KL I: `R(ν)` is a free
left `Pol(ν)`-module with basis `ψ_{ρ w}`, `w ∈ S_m`. -/
noncomputable def leftBasis :
    Basis (Perm (Fin (Multiset.card ν))) (Pol k ν) (LeftPolMod k (klQ (k := k) Γ) ν) :=
  KLRAlgebra.leftBasis (klQ_eq_klP (Γ := Γ) stdOrient_spec) (fun a b _ => klP_ne_zero _ a b)
    ρ hρ

theorem leftBasis_apply (w : Perm (Fin m)) :
    KL1.leftBasis (k := k) (Γ := Γ) ρ hρ w = LeftPolMod.of (ψw (ρ w) : R1 k Γ ν) :=
  KLRAlgebra.leftBasis_apply _ _ ρ hρ w

/-- The rank of `R(ν)` over `Pol(ν)` is `m!`, for both actions. -/
theorem finrank_polMod :
    Module.finrank (Pol k ν) (RightPolMod k (klQ (k := k) Γ) ν) = (Multiset.card ν).factorial ∧
      Module.finrank (Pol k ν) (LeftPolMod k (klQ (k := k) Γ) ν) =
        (Multiset.card ν).factorial :=
  ⟨finrank_rightPolMod (klQ_eq_klP (Γ := Γ) stdOrient_spec) (fun a b _ => klP_ne_zero _ a b),
    finrank_leftPolMod (klQ_eq_klP (Γ := Γ) stdOrient_spec) (fun a b _ => klP_ne_zero _ a b)⟩

end KL1

end Categorification.KLR
