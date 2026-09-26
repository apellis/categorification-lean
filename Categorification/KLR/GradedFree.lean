/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.GradedBasis
import Categorification.KLR.CenterFree
import Categorification.KLR.InductionFree

/-!
# Graded freeness: Proposition 2.7, Corollary 2.10 (2), Proposition 2.16

Khovanov–Lauda I (arXiv:0803.4121v2), §2.4 and §2.6, state that the bases of `R(ν)` over
`Pol(ν)` (Proposition 2.7), over `Sym(ν)` (Corollary 2.10 (2)) and of `1_{ν,ν'} R(ν + ν')`
over `R(ν) ⊗ R(ν')` (Proposition 2.16) exhibit these as *free graded* modules. We prove the
graded refinements of the existing (ungraded) basis theorems:

* **Proposition 2.7 (graded, right action)** (`GradingDatum.rightExpansion_isWeightedHomogeneous`):
  if `r ∈ R(ν)_d` and `r = ∑_w ψ_{ρ w} f_w` with `f_w ∈ Pol(ν)`, then each component
  `(f_w)_i ∈ k[x]` is weighted homogeneous of degree `d - deg(ψ_{ρ w} 1_i)` (for the weights
  `deg x_a = degX(i_a)`). Equivalently `R(ν) = ⨁_{w, i} ψ_{ρ w} 1_i · Pol(ν, i)` as graded
  spaces, where `ψ_{ρ w} 1_i` is homogeneous of degree `deg(ψ_{ρ w} 1_i)`
  (`GradingDatum.ψw_mul_e_mem_grade`). (The paper's `ŵ = ∑_i ψ_{ρ w} 1_i` is a sum of
  homogeneous elements of possibly different degrees, one for each `i`.)
* **Corollary 2.10 (2)** (`GradingDatum.exists_homogeneous_centerBasis`): `R(ν)` has a basis
  over its center `Z(R(ν)) = Sym(ν)` consisting of `(m!)²` homogeneous elements. For this we
  refine the parabolic Artin theorem: `k[V]` has a basis over the invariants of a Young
  subgroup consisting of *monomials* (`Categorification.exists_monomial_isInvBasis_label`).
* **Proposition 2.16 (graded)** (`GradingDatum.indElt_mem_grade`,
  `GradingDatum.ψw_mul_e_mem_grade`): the `k`-basis `ι(b ⊗ b') ŵ_u` of `1_{ν,ν'} R(ν + ν')`
  consists of homogeneous elements, and each component `ψ_{σ(u)} 1_s` of `ŵ_u` is homogeneous
  of degree `deg(ψ_{σ(u)} 1_s)`; also the dots-on-top basis `x^d ψ_{ρ w} 1_i` is homogeneous
  (`GradingDatum.lbasis_mem_grade`).
-/

open Equiv MvPolynomial

namespace Categorification

/-! ### A monomial basis in the parabolic Artin theorem -/

section MonomialArtin

universe u v

variable {k : Type u} [CommRing k] {V : Type v}

/-- A polynomial is a monic monomial `x^s`. -/
def IsMonicMonomial (f : MvPolynomial V k) : Prop := ∃ s, f = monomial s 1

theorem IsMonicMonomial.one : IsMonicMonomial (1 : MvPolynomial V k) := ⟨0, rfl⟩

theorem IsMonicMonomial.mul {f g : MvPolynomial V k} (hf : IsMonicMonomial f)
    (hg : IsMonicMonomial g) : IsMonicMonomial (f * g) := by
  obtain ⟨s, rfl⟩ := hf
  obtain ⟨t, rfl⟩ := hg
  exact ⟨s + t, by rw [monomial_mul, one_mul]⟩

theorem IsMonicMonomial.X_pow (v : V) (n : ℕ) : IsMonicMonomial (X v ^ n : MvPolynomial V k) :=
  ⟨Finsupp.single v n, X_pow_eq_monomial⟩

theorem IsMonicMonomial.prod {ι : Type*} (s : Finset ι) {f : ι → MvPolynomial V k}
    (hf : ∀ i, IsMonicMonomial (f i)) : IsMonicMonomial (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsMonicMonomial.one
  | insert a s ha ih => rw [Finset.prod_insert ha]; exact (hf a).mul ih

theorem IsMonicMonomial.rename {W : Type*} (σ : V → W) {f : MvPolynomial V k}
    (hf : IsMonicMonomial f) : IsMonicMonomial (MvPolynomial.rename σ f) := by
  obtain ⟨s, rfl⟩ := hf
  exact ⟨Finsupp.mapDomain σ s, rename_monomial _ _ _⟩

section Label

variable {J : Type*} [DecidableEq J] (lab : V → J) [Fintype V]

/-- The induction of `exists_isInvBasis_fibres`, keeping track of the fact that the basis
elements are monomials (products of staircase monomials of the fibres). -/
theorem exists_monomial_isInvBasis_fibres (T : Finset J) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → MvPolynomial V k),
      Fintype.card ι = ∏ c ∈ T, (Fintype.card {v // lab v = c}).factorial ∧
      IsInvBasis (fibresGroup lab T) b ∧ ∀ i, IsMonicMonomial (b i) := by
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ => 1, by simp, ?_, fun _ => IsMonicMonomial.one⟩
    rw [fibresGroup_empty]
    exact IsInvBasis.empty
  | @insert c T hcT ih =>
    obtain ⟨ι, _, b, hcard, hb, hmono⟩ := ih
    refine ⟨ι × {u : Fin (Fintype.card {v // lab v = c}) → ℕ // ∀ a, u a ≤ a}, inferInstance,
      fun q => b q.1 * ∏ a, X ((Fintype.equivFin {v // lab v = c}).symm a : V) ^ q.2.1 a,
      ?_, ?_, fun q => (hmono q.1).mul (IsMonicMonomial.prod _ fun a => IsMonicMonomial.X_pow _ _)⟩
    · rw [Fintype.card_prod, hcard, card_staircase, Finset.prod_insert hcT, mul_comm]
    · rw [fibresGroup_insert]
      refine IsInvBasis.mul hb (isInvBasis_fibre k (lab · = c)) (fun u => ?_) ?_
      · exact isInvariant_prod_fibre lab hcT _ (fun a => ((Fintype.equivFin _).symm a).2) _
      · rintro g ⟨c', hc', hg⟩ g' hg'
        exact fibreGroup_commute lab (fun h : c' = c => hcT (h ▸ hc')) hg hg'

variable (k) [DecidableEq V]

/-- **Parabolic Artin theorem with a monomial basis**: `k[V]` has a basis over the invariants of
the Young subgroup `G_lab` consisting of `|G_lab|` monomials. -/
theorem exists_monomial_isInvBasis_label :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → MvPolynomial V k),
      Fintype.card ι = Fintype.card {g : Perm V // lab ∘ g = lab} ∧
      (∀ g : ι → MvPolynomial V k, (∀ i, g i ∈ labelInvariants k lab) →
        ∑ i, g i * b i = 0 → ∀ i, g i = 0) ∧
      (∀ p : MvPolynomial V k, ∃ g : ι → MvPolynomial V k,
        (∀ i, g i ∈ labelInvariants k lab) ∧ ∑ i, g i * b i = p) ∧
      ∀ i, IsMonicMonomial (b i) := by
  obtain ⟨ι, _, b, hcard, hb, hmono⟩ :=
    exists_monomial_isInvBasis_fibres (k := k) lab (Finset.univ.image lab)
  refine ⟨ι, inferInstance, b, ?_, fun g hg => hb.indep g fun i =>
    (isInvariant_fibresGroup_iff lab).2 (hg i), fun p => ?_, hmono⟩
  · rw [hcard, DomMulAct.stabilizer_card']
  · obtain ⟨g, hg, hgp⟩ := hb.span p
    exact ⟨g, fun i => (isInvariant_fibresGroup_iff lab).1 (hg i), hgp⟩

end Label

end MonomialArtin

namespace KLR

open TypeA Graded KLRAlgebra PolyRep

universe uI

variable {I : Type uI} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (G : GradingDatum Q)

namespace GradingDatum

/-! ### Homogeneous elements -/

section Homogeneous

variable {μ : Multiset I}

/-- `ψ_ρ 1_i` is homogeneous of degree `deg(ψ_ρ 1_i)`. -/
theorem ψw_mul_e_mem_grade (ρ : List ℕ) (i : Seq μ) :
    (ψw ρ * e i : KLRAlgebra k Q μ) ∈ G.grade μ (G.degW ρ i) := by
  have h := G.ψw_mul_pol_mul_e_mem_grade ρ i (p := 1) (D := 0)
    (isWeightedHomogeneous_one k _)
  rwa [map_one, mul_one, add_zero] at h

/-- The standard element with dots on top, `x^d ψ_ρ 1_i`, is homogeneous of degree
`∑_a d_a degX((ρ • i)_a) + deg(ψ_ρ 1_i)`. -/
theorem pol_monomial_mul_ψw_mul_e_mem_grade (d : Fin (Multiset.card μ) →₀ ℕ) (ρ : List ℕ)
    (i : Seq μ) :
    (pol (monomial d 1) * ψw ρ * e i : KLRAlgebra k Q μ) ∈
      G.grade μ (Finsupp.weight (fun a => G.degX ((wordProd (Multiset.card μ) ρ • i).lbl a)) d +
        G.degW ρ i) := by
  have h1 := G.pol_monomial_mul_e_mem_grade d (wordProd (Multiset.card μ) ρ • i)
  have h2 := G.ψw_mul_e_mem_grade ρ i
  have := SetLike.GradedMul.mul_mem h1 h2
  rwa [mul_assoc, ← mul_assoc (e _), e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self,
    ← mul_assoc] at this

variable (ρ : Perm (Fin (Multiset.card μ)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card μ) (ρ w) ∧ wordProd (Multiset.card μ) (ρ w) = w)

/-- The basis with dots on top (`lbasis`) consists of homogeneous elements. -/
theorem lbasis_mem_grade (b : Seq μ × Perm (Fin (Multiset.card μ)) × (Fin (Multiset.card μ) →₀ ℕ)) :
    lbasis hPQ hP ρ hρ b ∈ G.grade μ
      (Finsupp.weight (fun a => G.degX ((b.2.1 • b.1).lbl a)) b.2.2 + G.degW (ρ b.2.1) b.1) := by
  rw [lbasis_apply]
  have := G.pol_monomial_mul_ψw_mul_e_mem_grade b.2.2 (ρ b.2.1) b.1
  rwa [(hρ b.2.1).2] at this

end Homogeneous

/-! ### Proposition 2.7, graded -/

section Prop27

variable {ν : Multiset I} (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)

/-- The coordinates of `∑_w ψ_{ρ w} f_w` in the basis `ψ_{ρ w} x^u 1_i` are the coefficients of
the polynomials `(f_w)_i`. -/
theorem basis_repr_sum_ψw_mul_polNu (c : Perm (Fin (Multiset.card ν)) → Pol k ν)
    (b : Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) :
    (KLRAlgebra.basis hPQ hP ρ hρ).repr (∑ w, ψw (ρ w) * polNu (c w)) b =
      coeff b.2.2 (c b.2.1 b.1) := by
  classical
  set B := KLRAlgebra.basis hPQ hP ρ hρ
  have key : ∀ (w : Perm (Fin (Multiset.card ν))) (i : Seq ν) (p : MvPolynomial _ k),
      (ψw (ρ w) * pol p * e i : KLRAlgebra k Q ν) =
        ∑ u ∈ p.support, coeff u p • B (i, w, u) := by
    intro w i p
    conv_lhs => rw [p.as_sum]
    simp only [map_sum, Finset.mul_sum, Finset.sum_mul, B, basis_apply]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [show (monomial u (coeff u p) : MvPolynomial _ k) = coeff u p • monomial u 1 by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, mul_smul_comm, smul_mul_assoc]
  have hr : (∑ w, ψw (ρ w) * polNu (c w) : KLRAlgebra k Q ν) =
      ∑ w, ∑ i, ∑ u ∈ (c w i).support, coeff u (c w i) • B (i, w, u) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [polNu_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, key]
  obtain ⟨i₀, w₀, u₀⟩ := b
  rw [hr]
  simp only [map_sum, map_smul, Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, Prod.mk.injEq, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_eq_single w₀ (fun w _ hw => by simp [hw]) (by simp)]
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hi]) (by simp)]
  simp only [true_and]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (not_mem_support_iff.1 h).symm

include hPQ hP hρ in
/-- **KL I, Proposition 2.7, graded (right action)**: if `r ∈ R(ν)_d` is written as
`r = ∑_w ψ_{ρ w} f_w` with `f_w ∈ Pol(ν)`, then each `(f_w)_i` is weighted homogeneous of degree
`d - deg(ψ_{ρ w} 1_i)` (weights `deg x_a = degX(i_a)`). So
`R(ν) = ⨁_{w, i} ψ_{ρ w} 1_i · Pol(ν, i)` is a decomposition into graded pieces, with
`ψ_{ρ w} 1_i` homogeneous of degree `deg(ψ_{ρ w} 1_i)` (`ψw_mul_e_mem_grade`). -/
theorem rightExpansion_isWeightedHomogeneous {r : KLRAlgebra k Q ν} {d : ℤ}
    (hr : r ∈ G.grade ν d) {c : Perm (Fin (Multiset.card ν)) → Pol k ν}
    (hc : ∑ w, ψw (ρ w) * polNu (c w) = r) (w : Perm (Fin (Multiset.card ν))) (i : Seq ν) :
    (c w i).IsWeightedHomogeneous (fun a => G.degX (i.lbl a)) (d - G.degW (ρ w) i) := by
  intro u hu
  rw [G.grade_eq_span hPQ hP ρ hρ d, Basis.mem_span_image] at hr
  have h1 : (i, w, u) ∈ ((KLRAlgebra.basis hPQ hP ρ hρ).repr r).support := by
    rw [Finsupp.mem_support_iff, ← hc, basis_repr_sum_ψw_mul_polNu]
    exact hu
  have h2 : G.stdDeg ρ (i, w, u) = d := hr h1
  simp only [stdDeg] at h2
  show Finsupp.weight _ u = _
  omega

end Prop27

/-! ### Corollary 2.10 (2) -/

section Cor210

variable {ν : Multiset I}

include hPQ hP in
/-- **KL I, Corollary 2.10 (2)**: `R(ν)` is a free graded module over its center
`Z(R(ν)) = Sym(ν)`: it has a basis over the center consisting of `(m!)²` homogeneous
elements. (The basis elements are `ψ_{ρ w} x^s 1_j`, standard basis elements, obtained from a
monomial basis of `k[x]` over the invariants of the stabiliser of a sequence.) -/
theorem exists_homogeneous_centerBasis :
    ∃ (ι : Type uI) (_ : Fintype ι)
      (B : Basis ι (Subalgebra.center k (KLRAlgebra k Q ν)) (KLRAlgebra k Q ν)) (deg : ι → ℤ),
      Fintype.card ι = (Multiset.card ν).factorial ^ 2 ∧ ∀ q, B q ∈ G.grade ν (deg q) := by
  classical
  let i : Seq ν := Classical.arbitrary _
  obtain ⟨ι, _, b, hcard, hind, hspan, hmono⟩ := exists_monomial_isInvBasis_label k i.1
  let ρ : Perm (Fin (Multiset.card ν)) → List ℕ := fun w => canWord _ w
  have hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w :=
    fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩
  let B := centerBasisOfInv hPQ hP ρ hρ i b hind hspan
  have hB : ∀ q, ∃ d, B q ∈ G.grade ν d := by
    intro q
    obtain ⟨s, hs⟩ := (hmono q.2.2).rename (Seq.toPerm i q.2.1)
    refine ⟨G.stdDeg ρ (q.2.1, q.1, s), ?_⟩
    rw [centerBasisOfInv_apply, hs, polNu_single, ← mul_assoc]
    exact G.stdElt_mem_grade ρ (q.2.1, q.1, s)
  choose deg hdeg using hB
  refine ⟨Perm (Fin (Multiset.card ν)) × (Seq ν × ι), inferInstance, B, deg, ?_, hdeg⟩
  rw [Fintype.card_prod, Fintype.card_prod, hcard, card_seq_mul_card_stab, Fintype.card_perm,
    Fintype.card_fin, sq]

end Cor210

/-! ### Proposition 2.16, graded -/

section Prop216

variable {ν ν' : Multiset I} (ρ₁ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (ρ₂ : Perm (Fin (Multiset.card ν')) → List ℕ)
  (σ : Shuffle (Seq.card_add' ν ν') → List ℕ)
  (hρ₁ : ∀ w, IsReduced (Multiset.card ν) (ρ₁ w) ∧ wordProd (Multiset.card ν) (ρ₁ w) = w)
  (hρ₂ : ∀ w, IsReduced (Multiset.card ν') (ρ₂ w) ∧ wordProd (Multiset.card ν') (ρ₂ w) = w)
  (hσ : ∀ u, IsReduced (Multiset.card (ν + ν')) (σ u) ∧
    wordProd (Multiset.card (ν + ν')) (σ u) = u.1)

include hσ in
/-- **KL I, Proposition 2.16, graded**: the `k`-basis `ι(b ⊗ b') ŵ_u` of `1_{ν,ν'} R(ν + ν')`
(`inductionBasis`) consists of homogeneous elements. Together with `ψw_mul_e_mem_grade` (each
component `ψ_{σ(u)} 1_s` of `ŵ_u` is homogeneous) this is the graded form of the freeness of
`1_{ν,ν'} R(ν + ν')` over `R(ν) ⊗ R(ν')`. -/
theorem indElt_mem_grade (x : IndIdx ν ν') :
    ∃ d, indElt hPQ hP ρ₁ ρ₂ σ hρ₁ hρ₂ x ∈ G.grade (ν + ν') d := by
  rw [indElt_eq hPQ hP ρ₁ ρ₂ σ hρ₁ hρ₂ hσ]
  exact ⟨_, G.lbasis_mem_grade hPQ hP _ (parWord_spec ρ₁ ρ₂ σ hρ₁ hρ₂ hσ) _⟩

/-- The components `ψ_{σ(u)} 1_s` of the basis elements `ŵ_u = ∑_s ψ_{σ(u)} 1_s` of
Proposition 2.16 are homogeneous of degree `deg(ψ_{σ(u)} 1_s)`. -/
theorem hatW_eq_sum_homogeneous (u : Shuffle (Seq.card_add' ν ν')) :
    (hatW σ u : KLRAlgebra k Q (ν + ν')) = ∑ p : Seq ν × Seq ν',
      ψw (σ u) * e ((wordProd (Multiset.card (ν + ν')) (σ u))⁻¹ • p.1.append p.2) ∧
    ∀ s : Seq (ν + ν'), (ψw (σ u) * e s : KLRAlgebra k Q (ν + ν')) ∈
      G.grade (ν + ν') (G.degW (σ u) s) :=
  ⟨hatW_eq_sum σ u, fun s => G.ψw_mul_e_mem_grade (σ u) s⟩

end Prop216

end GradingDatum

end KLR

end Categorification
