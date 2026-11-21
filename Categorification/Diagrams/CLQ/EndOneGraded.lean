/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.Spanning
import Categorification.Diagrams.KL3.EndOneGraded

/-!
# The grading of `Π_λ → END_U(1_λ)` and KL III Corollary 3.7

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.1:
eq. (3.25) (label `homo_Pi_Uone`: "a surjective graded `k`-algebra homomorphism"), eq. (3.26)
(the series `π = ∏_{i ∈ I} ∏_{a ≥ 1} 1/(1 - q_i^{2a})`), and Corollary 3.7:
"`gdim HOM_U(1_λ, 1_λ) ≤ π` and `HOM_U(1_λ, 1_λ)` is a local graded ring".

## Gradings

`HDe λ d` is the degree-`d` part of `END_U(1_λ)` (the library's `homDeg` for the degrees `deg`
of `U`; `END_U(1_λ) = ⊕_d HDe λ d` by `isInternal_homDeg`). `Π_λ` is graded by the weights
`wPi` (`α (i·i)` for KL III's generator of index `(i, α)`). The monomials of weighted degree `d`
are `monDeg C d`; for `I` finite this is a finite set (`monDeg_finite`) and its cardinality is the
coefficient of `q^d` in `π` (`piTrunc_coeff`: `π` is represented, in degrees `≤ N`, by the finite
product `piTrunc C N` of truncated geometric series `∑_{e ≤ N} q^{e α (i·i)}`, `α ≤ N`, since
`q_i^{2α} = q^{2 d_i α} = q^{α (i·i)}`).

## Main results

* `bubMap_mem_HDe`: `bubMap` is graded (`Π_λ` in weighted degree `d` goes to `HDe λ d`).
* `homogeneousComponent_bubMap`: `bubMap` commutes with taking homogeneous components.
* For the image of `Π_λ` (unconditionally): `isBub_HDe_neg` (no elements of negative degree),
  `isBub_HDe_zero` (the degree-zero elements are the scalars), `isBub_HDe_mem_span` (the degree
  `d` elements are spanned by the images of the monomials of degree `d`).
* `piTrunc_coeff`: "the graded dimension of `Π_λ` is `π`" (the coefficient of `q^d` in `π` is
  the number of monomials of degree `d`).
* **Corollary 3.7**, assuming Proposition 3.6 (`Prop36`, proved for every Cartan datum in
  `Categorification.Diagrams.KL3.Lemma39`, where the unconditional forms `cor37_*_unconditional`
  are; proved for crossingless diagrams in
  `Categorification.Diagrams.KL3.Spanning`): `cor37_finrank_le` (`dim_k HOM_U(1_λ,1_λ)_d ≤
  #{monomials of degree d}`) and `cor37_gdim_le_pi` (`≤` the coefficient of `q^d` in `π`), i.e.
  `gdim ≤ π`, for a field `k` (or any commutative ring with the strong rank condition) and
  finite `I`;
  `cor37_HDe_neg`, `cor37_HDe_zero` and `cor37_isUnit` (the ring is nonnegatively graded with
  degree-zero part `k · 1`; so its homogeneous elements outside the ideal `⊕_{d > 0}` are units:
  KL III's "local graded ring"). Commutativity is `EndOne`'s `CommRing` instance
  (`endEmpty_comm`, Eckmann–Hilton).

Note that "local" presupposes `END_U(1_λ) ≠ 0`, i.e. `1_λ ≠ 0`; this does not follow from
Proposition 3.6 (it needs a nonzero representation of `U`) and is not proved here.
`cor37_isUnit` is the part of "local graded" that follows from Proposition 3.6.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-! ## The degree-`d` part of `END_U(1_λ)` -/

/-- The degree-`d` part of `END_U(1_λ)`. -/
abbrev HDe (lam : X) (d : ℤ) : Submodule k (End ((pres RD k sc).obj (ob RD lam []))) :=
  (pres RD k sc).homDeg (deg RD) (ob RD lam []) (ob RD lam []) d

/-- The underlying endomorphism, as a linear map. -/
def EndOne.valL (lam : X) : EndOne RD k sc lam →ₗ[k] End ((pres RD k sc).obj (ob RD lam [])) where
  toFun := EndOne.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The degree-`d` part of `END_U(1_λ)`, as a submodule of the commutative ring `EndOne`. -/
def HDo (lam : X) (d : ℤ) : Submodule k (EndOne RD k sc lam) :=
  (HDe RD k sc lam d).comap (EndOne.valL RD k sc lam)

variable {RD k sc}

theorem mem_HDo {lam : X} {d : ℤ} {x : EndOne RD k sc lam} : x ∈ HDo RD k sc lam d ↔ x.val ∈ HDe RD k sc lam d :=
  Submodule.mem_comap

instance (lam : X) : SetLike.GradedMonoid (HDo RD k sc lam) where
  one_mem := mem_HDo.2 ((pres RD k sc).id_mem_homDeg (deg RD) (ob RD lam []))
  mul_mem _ _ x y hx hy := by
    rw [mem_HDo, EndOne.val_mul, add_comm]
    exact Presentation.comp_mem_homDeg (mem_HDo.1 hy) (mem_HDo.1 hx)

variable (lam : X)

/-- The generators of `Π_λ` have the degrees of eq. (3.24): `α (i·i)`. -/
theorem bubGen_mem_HDe (i : I) (α : ℕ) :
    bubGen RD k sc lam i α ∈ HDe RD k sc lam (α * C.dot i i) := by
  unfold bubGen
  split_ifs
  · have := Presentation.lin_mem_homDeg (P := pres RD k sc)
      (cwL_mem (RD := RD) (k := k) lam i (ip RD i lam - 1 + α))
    convert this using 1 <;> first | rfl | (rw [← two_mul_di C i]; ring_nf)
  · have := Presentation.lin_mem_homDeg (P := pres RD k sc)
      (ccwL_mem (RD := RD) (k := k) lam i (-ip RD i lam - 1 + α))
    convert this using 1 <;> first | rfl | (rw [← two_mul_di C i]; ring_nf)

theorem bubMap_X_mem (x : I × ℕ) : bubMap RD k sc lam (MvPolynomial.X x) ∈ HDo RD k sc lam (wPi C x) := by
  simp only [bubMap, MvPolynomial.aeval_X, mem_HDo, EndOne.val_of, wPi]
  have := bubGen_mem_HDe (RD := RD) (k := k) lam x.1 (x.2 + 1)
  simpa using this

theorem bubMap_monomial_mem (s : (I × ℕ) →₀ ℕ) (c : k) :
    bubMap RD k sc lam (MvPolynomial.monomial s c) ∈ HDo RD k sc lam (Finsupp.weight (wPi C) s) := by
  rw [MvPolynomial.monomial_eq, map_mul, MvPolynomial.algHom_C, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]
  refine Submodule.smul_mem _ c ?_
  rw [Finsupp.prod, map_prod, Finsupp.weight_apply, Finsupp.sum]
  refine SetLike.prod_mem_graded _ _ _ fun x _ => ?_
  rw [map_pow]
  exact SetLike.pow_mem_graded _ (bubMap_X_mem lam x)

/-- **`bubMap` is graded**: a weighted homogeneous polynomial of degree `d` is mapped to the
degree-`d` part of `END_U(1_λ)` (KL III eq. (3.25): "graded"). -/
theorem bubMap_mem_HDe {p : PiLam I k} {d : ℤ} (hp : p.IsWeightedHomogeneous (wPi C) d) :
    (bubMap RD k sc lam p).val ∈ HDe RD k sc lam d := by
  rw [← mem_HDo, p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have := bubMap_monomial_mem (RD := RD) (k := k) lam s (p.coeff s)
  rwa [hp (MvPolynomial.mem_support_iff.1 hs)] at this


/-- `bubMap` commutes with the projections onto homogeneous components. -/
theorem homogeneousComponent_bubMap (d : ℤ) (p : PiLam I k) :
    homogeneousComponent (pres_isHomogeneous (RD := RD) (k := k)) d (bubMap RD k sc lam p).val =
      (bubMap RD k sc lam (MvPolynomial.weightedHomogeneousComponent (wPi C) d p)).val := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [weightedHomogeneousComponent_monomial]
    have hm := bubMap_monomial_mem (RD := RD) (k := k) lam s c
    split_ifs with h
    · rw [← h]; exact homogeneousComponent_of_mem _ (mem_HDo.1 hm)
    · rw [map_zero, EndOne.val_zero]; exact homogeneousComponent_of_mem_of_ne _ (mem_HDo.1 hm) h
  | add p q hp hq =>
    rw [map_add, EndOne.val_add, map_add, hp, hq, map_add, map_add, EndOne.val_add]

variable {lam}

/-- An element of the image of `Π_λ` of degree `d` is the image of the degree-`d` component. -/
theorem isBub_HDe {x : End ((pres RD k sc).obj (ob RD lam []))} {d : ℤ} (hx : IsBub RD k sc lam x)
    (hd : x ∈ HDe RD k sc lam d) :
    ∃ p : PiLam I k, p.IsWeightedHomogeneous (wPi C) d ∧ (bubMap RD k sc lam p).val = x := by
  obtain ⟨p, hp⟩ := hx
  have hx' : x = (bubMap RD k sc lam p).val := (congrArg EndOne.val hp).symm
  refine ⟨MvPolynomial.weightedHomogeneousComponent (wPi C) d p,
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous d p, ?_⟩
  rw [← homogeneousComponent_bubMap, ← hx']
  exact homogeneousComponent_of_mem _ hd



/-- The image of `Π_λ` has no nonzero elements of negative degree. -/
theorem isBub_HDe_neg {x : End ((pres RD k sc).obj (ob RD lam []))} {d : ℤ} (hd0 : d < 0)
    (hx : IsBub RD k sc lam x) (hd : x ∈ HDe RD k sc lam d) : x = 0 := by
  obtain ⟨p, hp, rfl⟩ := isBub_HDe hx hd
  have : p = 0 := by
    ext s
    by_contra hs
    have := hp hs
    have := weight_wPi_nonneg (C := C) s
    omega
  rw [this, map_zero]; rfl

/-- The degree-zero elements of the image of `Π_λ` are the scalars. -/
theorem isBub_HDe_zero {x : End ((pres RD k sc).obj (ob RD lam []))} (hx : IsBub RD k sc lam x)
    (hd : x ∈ HDe RD k sc lam 0) : ∃ c : k, x = c • 𝟙 _ := by
  classical
  obtain ⟨p, hp, rfl⟩ := isBub_HDe hx hd
  refine ⟨p.coeff 0, ?_⟩
  have : p = MvPolynomial.C (p.coeff 0) := by
    ext s
    rw [MvPolynomial.coeff_C]
    split_ifs with h
    · rw [h]
    · by_contra hs
      exact h (weight_wPi_eq_zero (hp hs)).symm
  rw [this, MvPolynomial.algHom_C, EndOne.val_algebraMap, MvPolynomial.coeff_C, ite_eq_left rfl]


variable (RD k lam) in
/-- The bubble monomial of exponent `s`, as an endomorphism of `1_λ`. -/
def bubMon (s : (I × ℕ) →₀ ℕ) : End ((pres RD k sc).obj (ob RD lam [])) :=
  (bubMap RD k sc lam (MvPolynomial.monomial s 1)).val

/-- The degree-`d` elements of the image of `Π_λ` are spanned by the bubble monomials of degree
`d`. -/
theorem isBub_HDe_mem_span {x : End ((pres RD k sc).obj (ob RD lam []))} {d : ℤ}
    (hx : IsBub RD k sc lam x) (hd : x ∈ HDe RD k sc lam d) :
    x ∈ Submodule.span k (bubMon RD k sc lam '' monDeg C d) := by
  obtain ⟨p, hp, rfl⟩ := isBub_HDe hx hd
  rw [p.as_sum, map_sum]
  simp only [EndOne.val]
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [← mul_one (p.coeff s), ← smul_eq_mul, ← MvPolynomial.smul_monomial, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, hp (MvPolynomial.mem_support_iff.1 hs), rfl⟩)




/-! ## The series `π` (eq. (3.26)) -/

section Pi

variable [Fintype I]






end Pi

/-! ## Corollary 3.7 (assuming Proposition 3.6) -/

section Cor37

variable (lam) (h36 : Prop36 RD k sc lam)
include h36

theorem isBub_of_prop36 (x : End ((pres RD k sc).obj (ob RD lam []))) : IsBub RD k sc lam x := by
  obtain ⟨p, hp⟩ := h36 (EndOne.of x)
  exact ⟨p, hp⟩

/-- **KL III Corollary 3.7, nonnegativity of degrees** (assuming Proposition 3.6):
`HOM_U(1_λ, 1_λ)` has no nonzero elements of negative degree. -/
theorem cor37_HDe_neg {d : ℤ} (hd : d < 0) : HDe RD k sc lam d = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact (Submodule.mem_bot k).2 (isBub_HDe_neg hd (isBub_of_prop36 lam h36 x) hx)

/-- **KL III Corollary 3.7, the degree-zero part** (assuming Proposition 3.6): the degree-zero
part of `HOM_U(1_λ, 1_λ)` is `k · 1`. -/
theorem cor37_HDe_zero : HDe RD k sc lam 0 = Submodule.span k {𝟙 _} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨c, rfl⟩ := isBub_HDe_zero (isBub_of_prop36 lam h36 x) hx
    exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact (pres RD k sc).id_mem_homDeg (deg RD) (ob RD lam [])

end Cor37

/-- **KL III Corollary 3.7, `gdim HOM_U(1_λ, 1_λ) ≤ π`** (assuming Proposition 3.6): for finite
`I` (and `k` a field, or any commutative ring with the strong rank condition), the degree-`d`
part of `END_U(1_λ)` has dimension at most the number of bubble monomials of degree `d`, the
coefficient of `q^d` in `π`. -/
theorem cor37_finrank_le [StrongRankCondition k] [Finite I] (lam : X) (h36 : Prop36 RD k sc lam)
    (d : ℤ) : Module.finrank k (HDe RD k sc lam d) ≤ (monDeg C d).ncard := by
  classical
  have hfin := monDeg_finite (C := C) d
  obtain ⟨T, hT⟩ : ∃ T : Finset (End ((pres RD k sc).obj (ob RD lam []))),
      T = hfin.toFinset.image (bubMon RD k sc lam) := ⟨_, rfl⟩
  have hle : HDe RD k sc lam d ≤ Submodule.span k (T : Set (End ((pres RD k sc).obj (ob RD lam [])))) := by
    intro x hx
    have := isBub_HDe_mem_span (isBub_of_prop36 lam h36 x) hx
    rw [hT, Finset.coe_image, Set.Finite.coe_toFinset]
    exact this
  have h₁ := Submodule.finrank_mono hle
  have h₂ := finrank_span_finset_le_card (R := k) T
  have h₃ : T.card ≤ hfin.toFinset.card := hT ▸ Finset.card_image_le
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact h₁.trans (h₂.trans h₃)

/-- **KL III Corollary 3.7, `gdim HOM_U(1_λ, 1_λ) ≤ π`, coefficientwise** (assuming
Proposition 3.6): the dimension of the degree-`d` part of `END_U(1_λ)` is at most the
coefficient of `q^d` in `π` (computed from the truncation `piTrunc C N`, `N ≥ d`). In negative
degrees both sides vanish (`cor37_HDe_neg`). -/
theorem cor37_gdim_le_pi [StrongRankCondition k] [Fintype I] (lam : X) (h36 : Prop36 RD k sc lam)
    (N d : ℕ) (hd : d ≤ N) :
    (Module.finrank k (HDe RD k sc lam d) : ℤ) ≤ (piTrunc C N).coeff d := by
  rw [piTrunc_coeff N d hd]
  exact_mod_cast cor37_finrank_le lam h36 d

/-- **KL III Corollary 3.7, "local graded ring"** (assuming Proposition 3.6; `k` a field): a
homogeneous element of `END_U(1_λ)` which is not in the ideal of elements of positive degree is
a unit. Together with `cor37_HDe_neg` this says that the elements of positive degree form the
unique maximal homogeneous ideal (when `END_U(1_λ) ≠ 0`). -/
theorem cor37_isUnit {K : Type w} [Field K] (lam : X) (h36 : Prop36 RD K lam) {x : EndOne RD K lam} {d : ℤ}
    (hx : x ∈ HDo RD K lam d) (hd : d ≤ 0) (hx0 : x ≠ 0) : IsUnit x := by
  rcases hd.lt_or_eq with hd | rfl
  · exact absurd (EndOne.val_injective (isBub_HDe_neg hd (isBub_of_prop36 lam h36 _) hx)) hx0
  · obtain ⟨c, hc⟩ := isBub_HDe_zero (isBub_of_prop36 lam h36 x.val) hx
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hx0 (EndOne.val_injective (by rw [hc, zero_smul]; rfl))
    have : x = algebraMap K (EndOne RD K lam) c :=
      EndOne.val_injective (by rw [hc, EndOne.val_algebraMap])
    rw [this]
    exact (IsUnit.mk0 c hc0).map (algebraMap K (EndOne RD K lam))


end Categorification.KL3.Diagram.CLQ
