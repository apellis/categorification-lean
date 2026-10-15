/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.Triangular
import Categorification.Diagrams.KL3.SpanningPositive
import Categorification.Diagrams.KL3.KrullSchmidtU

/-!
# Nondegeneracy of the Khovanov–Lauda calculus from unfurled cyclotomic representations

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, Theorem with label
`nondegenerate` (the spanning set `B_{𝐢,𝐣,λ}` of KL III is a basis, for every Cartan datum), the
part of its proof headed "Triviality of a relation", for pairs of positive sequences. Together
with KL III (Khovanov–Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1),
Remark after the definition of nondegeneracy (`calculusNondeg_of_positive`), this gives the
nondegeneracy hypothesis of KL III Theorem 1.2 (`CalculusNondeg`) from the existence of the
representations that Webster's proof uses.

## The hypothesis

Webster lets `𝒰` act on a cyclotomic representation `𝒳` of an unfurled datum `g̃` with a
generating object `𝕍` (his Lemma `lem:g-action`), evaluates a relation among the elements of
`B_{𝐢,𝐣,λ}` on `𝕍`, and projects to the summand `Ẽ_𝐭 𝕍 → Ẽ_{𝐭'} 𝕍` for lifts `𝐭`, `𝐭'` with
generic labels `(i, z_{i,q})`, a different `q` on each strand. `UnfurledEval RD k μ i j N`
records exactly what the argument uses from this, for a pair `i, j ∈ Seq(ν)` of positive
sequences and a bound `N`:

* a field `L ⊇ k` and an unfurling datum `D` over `L` with no arrows and series
  `ϖ_a(x) = z_a + x` (as `UnfurlingDatum.ofGeneric`; the labels of the strands);
* a lift `t` of `i` to a weight `ν̃` of `D` with pairwise distinct labels, and a level `M ≥ N`
  of the cyclotomic quotient `𝖱^Λ(ν̃)` with `a_b = y^M` (`UnfCyc`);
* the evaluation `Θ : HOM_U(E_{+i} 1_λ, E_{+j} 1_λ) → 𝖱^Λ(ν̃)`, semilinear over `k → L`
  (the action on `𝕍`, followed by the restriction to the summand `Ẽ_t 𝕍`);
* the action `bub : Π_λ → L` of the bubbles on `𝕍`, with the bubbles of index `< N`
  algebraically independent over `k` (in the source they act through the symmetric functions
  of the independent `z`'s, so they are independent in the degrees below the number of
  labels: the step "bubbles map to generic elements" left implicit in the source);
* the images of the basis diagrams: `Θ(ψ_{ρ w} x^u 1_i · m) = bub(m) · Γ(ψ_{ρ w} x^u e(i)) e(t)`
  for `w • i = j`, where `Γ = cycGamma` is `γ` (Lemma `lem:gamma-homo`) followed by the
  cyclotomic quotient: the 2-functor sends the KLR part through `γ` and the bubbles on the far
  right to scalars on `𝕍`.

Discharging this hypothesis (the action of `𝒰` on the unfurled representations, Lemma
`lem:g-action`, and the evaluation on `𝕍`) is separate work; see the README.

## Main results

* `UnfurledEval`: the hypothesis above.
* `linearIndependent_posB_of_unfurledEval`: if `UnfurledEval RD k μ i j N` holds for every `N`,
  the elements of `B_{+i,+j,λ}` are linearly independent.
* `positiveNondeg_of_unfurledEval`, **`calculusNondeg_of_unfurledEval`**: if it holds for all
  `λ`, `i`, `j`, `N`, then `PositiveNondeg RD k` and `CalculusNondeg RD k` (the nondegeneracy
  hypothesis of KL III Theorem 1.2, for any field `k` and any Cartan datum with `I` finite).

## Proof (Webster's argument; the reduction to one column is ours)

Let `∑_x g_x posB x = 0`. Choose `N` larger than every dot exponent and every bubble index in
the relation, and apply `Θ` for a witness of `UnfurledEval RD k μ i j N`. Grouping the terms by
the KLR basis element `(w, u)` gives `Γ(∑_{(w,u)} c_{w,u} ψ_{ρ w} x^u e(i)) e(t) = 0` with
`c_{w,u} = bub(∑_{x ↦ (w,u)} g_x m_x)`. The triangularity of `Γ`
(`eq_zero_of_cycGamma_mul_e_eq_zero`: the maximal-crossing pairing, then the minimal dots, as in
the source) gives `c_{w,u} = 0`. The bubble monomials involved have indices `< N`, so the
independence of `bub` on them gives `g_x = 0`: an element of `B_{+i,+j,λ}` is determined by
`(w, u, m)` (`posKey_injective`).

Comparison with the source. Webster works with all pairs of signed sequences and with the
deformed cyclotomic quotient whose endomorphism ring `Z = End(𝕍)` is a polynomial ring in the
fake bubbles; here only positive sequences are needed (KL III's Remark, formalized as
`calculusNondeg_of_positive`), so there are no cups and caps, and `End(𝕍)` is the field `L`.
-/

noncomputable section

namespace Categorification.KLR.Unfurling

open CategoryTheory MvPolynomial KLRAlgebra Equiv QuantumGroup UDot KL3.Diagram
open scoped TensorProduct

universe u v w w₁ w₂

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k] [DecidableEq I]

/-! ### The elements of `B_{+i,+j,λ}` are determined by `(w, u, m)` -/

section Key

variable {ν : Multiset I} {i j : KLR.Seq ν}

omit [DecidableEq I] in
/-- An element of `B_{+i,+j,λ}` is determined by its permutation, its dots and its bubble
monomial. -/
theorem posKey_injective :
    Function.Injective fun x : SpanIdx (posW (Diagram.word i)) (posW (Diagram.word j)) =>
      (posPerm x.1, posDots x, x.2.2) := by
  rintro ⟨σ, dx, mx⟩ ⟨σ', dy, my⟩ hxy
  simp only [Prod.mk.injEq] at hxy
  obtain ⟨hp, hd, hm⟩ := hxy
  have hσ : σ = σ' := by
    apply Subtype.ext
    apply (bwE (i := i) (j := j)).injective
    rw [← blockPerm_posPerm, ← blockPerm_posPerm, hp]
  subst hσ hm
  have hdd : dx = dy := funext fun z => by
    obtain ⟨a, rfl⟩ := (posArc_bijective σ).2 z
    have := DFunLike.congr_fun hd a
    simpa [posDots] using this
  subst hdd
  rfl

end Key

/-! ### The hypothesis -/

variable (RD k) in
/-- **The evaluation of `𝒰` on an unfurled cyclotomic representation, on one Hom space**
(Webster, arXiv:1603.06311v3, proof of the theorem with label `nondegenerate`: the action of
Lemma `lem:g-action` on the generating object `𝕍`, restricted to the summand `Ẽ_t 𝕍` with
generic labels). For positive sequences `i, j ∈ Seq(ν)`, a weight `λ` and a bound `N` on the
dots and the bubble indices: a field `L ⊇ k`, an unfurling datum over `L` without arrows and
with linear series, a lift `t` of `i` with pairwise distinct labels, a cyclotomic level
`M ≥ N`, a `k`-semilinear map `Θ` from `HOM_U(E_{+i} 1_λ, E_{+j} 1_λ)` to the cyclotomic
quotient, and the action `bub` of the bubbles on `𝕍`, independent in the indices `< N`, such that
`Θ` sends the basis diagram `ψ_{ρ w} x^u 1_i` with the bubble monomial `m` to
`bub(m) · Γ(ψ_{ρ w} x^u e(i)) e(t)`. -/
structure UnfurledEval (μ : X) {ν : Multiset I} (i j : KLR.Seq ν) (N : ℕ) where
  /-- The field of definition of the representation, containing the `z`'s. -/
  L : Type w₁
  [instField : Field L]
  [instAlgebra : Algebra k L]
  /-- The labels. -/
  J : Type w₂
  [instDecEq : DecidableEq J]
  [instFintype : Fintype J]
  /-- The crossing polynomials of the KL II datum over `L`. -/
  P : I → I → MvPolynomial (Fin 2) L
  hPQ : ∀ a b, a ≠ b → KLR.klQ2 L C a b = P b a * rename ![1, 0] (P a b)
  /-- The unfurling datum of the labels. -/
  D : UnfurlingDatum L P J
  harr : ∀ a b, D.arrows a b = 0
  hlin : ∀ a, D.pw a = Polynomial.C ((D.pw a).coeff 0) + Polynomial.X
  /-- The weight of the lift. -/
  ν' : Multiset J
  hν : ν'.map D.π = ν
  hnd : ν'.Nodup
  /-- The lift of `i`. -/
  t : KLR.Seq ν'
  ht : down D.π hν t = i
  /-- The cyclotomic level. -/
  M : ℕ
  hM : N ≤ M
  /-- The action of the bubbles on `𝕍`. -/
  bub : PiLam I k →ₐ[k] L
  bub_indep : AlgebraicIndependent k fun p : {p : I × ℕ // p.2 < N} => bub (MvPolynomial.X p.1)
  /-- The evaluation on `𝕍`, restricted to the summand `Ẽ_t 𝕍`. -/
  Θ : ((KL3.Diagram.pres RD k).obj (ob RD μ (posW (Diagram.word i))) ⟶
      (KL3.Diagram.pres RD k).obj (ob RD μ (posW (Diagram.word j)))) →ₛₗ[algebraMap k L] UnfCyc D ν' M
  map_basis : ∀ (w : Perm (Fin (Multiset.card ν))) (u : Fin (Multiset.card ν) →₀ ℕ)
    (m : (I × ℕ) →₀ ℕ), w • i = j →
    Θ (phi RD k μ ν (KLR.KL2.basis (k := k) (C := C) (ν := ν) (ρc ν) (hρc ν) (i, w, u) ⊗ₜ
        monomial m 1) i j) =
      bub (monomial m 1) • (cycGamma D harr hν hnd M hPQ
        (ψw (ρc ν w) * pol (monomial u 1) * e i : KLRAlgebra L (KLR.klQ2 L C) ν) *
          cycMk D ν' M (e t))

attribute [instance] UnfurledEval.instField UnfurledEval.instAlgebra UnfurledEval.instDecEq
  UnfurledEval.instFintype

/-! ### The triangularity argument -/

section Bubbles

omit [DecidableEq I]

variable {L : Type*} [Field L] [Algebra k L]

/-- A polynomial in the variables `(i, n)`, `n < N`, killed by a `k`-algebra map that is
algebraically independent on these variables, is zero. -/
theorem eq_zero_of_bub_eq_zero {N : ℕ} (bub : PiLam I k →ₐ[k] L)
    (hind : AlgebraicIndependent k fun p : {p : I × ℕ // p.2 < N} => bub (MvPolynomial.X p.1))
    {F : PiLam I k} (hF : F ∈ (rename (R := k) (Subtype.val : {p : I × ℕ // p.2 < N} → I × ℕ)).range)
    (h0 : bub F = 0) : F = 0 := by
  obtain ⟨G, rfl⟩ := hF
  change bub (rename Subtype.val G) = 0 at h0
  have hG : aeval (fun p : {p : I × ℕ // p.2 < N} => bub (MvPolynomial.X p.1)) G = 0 := by
    rw [← h0]
    conv_rhs => rw [aeval_unique bub]
    rw [aeval_rename]
    rfl
  change rename Subtype.val G = 0
  rw [hind.eq_zero_of_aeval_eq_zero G hG, map_zero]

/-- A monomial in the variables `(i, n)`, `n < N`, is a renamed polynomial. -/
theorem monomial_mem_range_rename {N : ℕ} {m : (I × ℕ) →₀ ℕ} (hm : ∀ p ∈ m.support, p.2 < N) :
    (monomial m (1 : k)) ∈
      (rename (R := k) (Subtype.val : {p : I × ℕ // p.2 < N} → I × ℕ)).range := by
  obtain ⟨G, hG⟩ := exists_rename_eq_of_vars_subset_range (monomial m (1 : k))
    (Subtype.val : {p : I × ℕ // p.2 < N} → I × ℕ) Subtype.val_injective (by
      rw [vars_monomial one_ne_zero]
      intro p hp
      exact ⟨⟨p, hm p (by simpa using hp)⟩, rfl⟩)
  exact ⟨G, hG⟩

end Bubbles

section Main

/-- **The elements of `B_{+i,+j,λ}` are linearly independent** (Webster, arXiv:1603.06311v3,
proof of the theorem with label `nondegenerate`, "Triviality of a relation", for positive
sequences), given the evaluations `UnfurledEval RD k μ i j N` for every bound `N`. -/
theorem linearIndependent_posB_of_unfurledEval (μ : X) {ν : Multiset I} (i j : KLR.Seq ν)
    (H : ∀ N, Nonempty (UnfurledEval.{u, v, w, w₁, w₂} RD k μ i j N)) :
    LinearIndependent k (posB RD k μ : SpanIdx (posW (Diagram.word i)) (posW (Diagram.word j)) → _) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg x0 hx0
  -- the bound on dots and bubble indices
  let N : ℕ := s.sup (fun x => Finset.univ.sup (posDots x) ⊔ x.2.2.support.sup Prod.snd) + 1
  have hdots : ∀ x ∈ s, ∀ a, posDots x a < N := fun x hx a => Nat.lt_succ_of_le
    ((le_sup_left.trans' (Finset.le_sup (f := posDots x) (Finset.mem_univ a))).trans
      (Finset.le_sup (f := fun x => Finset.univ.sup (posDots x) ⊔ x.2.2.support.sup Prod.snd) hx))
  have hbub : ∀ x ∈ s, ∀ p ∈ x.2.2.support, p.2 < N := fun x hx p hp => Nat.lt_succ_of_le
    ((le_sup_right.trans' (Finset.le_sup (f := Prod.snd) hp)).trans
      (Finset.le_sup (f := fun x => Finset.univ.sup (posDots x) ⊔ x.2.2.support.sup Prod.snd) hx))
  obtain ⟨W⟩ := H N
  -- grouping by the KLR basis element
  let key : SpanIdx (posW (Diagram.word i)) (posW (Diagram.word j)) →
      Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ) :=
    fun x => (posPerm x.1, posDots x)
  let S := s.image key
  let F : Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ) → PiLam I k :=
    fun p => ∑ x ∈ s with key x = p, g x • monomial x.2.2 1
  let c := fun p => W.bub (F p)
  let std : Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ) →
      KLRAlgebra W.L (KLR.klQ2 W.L C) ν :=
    fun p => ψw (ρc ν p.1) * pol (monomial p.2 1) * e i
  let Γ := cycGamma W.D W.harr W.hν W.hnd W.M W.hPQ
  have himg : ∀ x ∈ s, W.Θ (posB RD k μ x) =
      W.bub (monomial x.2.2 1) • (Γ (std (key x)) * cycMk W.D W.ν' W.M (e W.t)) :=
    fun x _ => W.map_basis _ _ _ (posPerm_smul x.1)
  have h0 : Γ (∑ p ∈ S, c p • std p) * cycMk W.D W.ν' W.M (e W.t) = 0 := by
    have hΘ := congrArg W.Θ hg
    rw [map_sum, map_zero] at hΘ
    rw [← hΘ, ← Finset.sum_fiberwise_of_maps_to (g := key) (t := S)
      (fun x hx => Finset.mem_image_of_mem key hx), map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hc : c p = ∑ x ∈ s with key x = p, algebraMap k W.L (g x) * W.bub (monomial x.2.2 1) := by
      simp only [c, F, map_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [map_smul, Algebra.smul_def]
    rw [map_smul, smul_mul_assoc, hc, Finset.sum_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hxs, hkx⟩ := Finset.mem_filter.1 hx
    rw [LinearMap.map_smulₛₗ, himg x hxs, hkx, smul_smul]
  have hS : ∀ p ∈ S, ∀ a, p.2 a < W.M := by
    intro p hp a
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
    exact (hdots x hx a).trans_le W.hM
  have hc := eq_zero_of_cycGamma_mul_e_eq_zero W.D W.harr W.hν W.hnd W.M W.hPQ W.hlin W.ht
    (ρc ν) (hρc ν) S c hS h0
  -- the bubble part
  have hF0 : F (key x0) = 0 := by
    refine eq_zero_of_bub_eq_zero W.bub W.bub_indep (Subalgebra.sum_mem _ fun x hx => ?_)
      (hc _ (Finset.mem_image_of_mem key hx0))
    exact Subalgebra.smul_mem _
      (monomial_mem_range_rename (hbub x (Finset.mem_filter.1 hx).1)) _
  have hcoeff := congrArg (fun F : PiLam I k => F.coeff x0.2.2) hF0
  simp only [F, coeff_sum, coeff_smul, coeff_monomial] at hcoeff
  rw [Finset.sum_eq_single x0] at hcoeff
  · simpa using hcoeff
  · intro x hx hne
    rw [ite_eq_right_iff.2 fun hm => ?_, smul_zero]
    obtain ⟨-, hk⟩ := Finset.mem_filter.1 hx
    have hk : (posPerm x.1, posDots x) = (posPerm x0.1, posDots x0) := hk
    refine (hne (posKey_injective ?_)).elim
    simp only [Prod.mk.injEq] at hk ⊢
    exact ⟨hk.1, hk.2, hm⟩
  · intro hn
    exact (hn (Finset.mem_filter.2 ⟨hx0, rfl⟩)).elim

variable [Finite I]

/-- **Nondegeneracy for positive sequences from the unfurled representations** (Webster,
arXiv:1603.06311v3, Theorem with label `nondegenerate`, for positive sequences; the reduction of
the theorem to these evaluations is the "Triviality of a relation" part of its proof): if
`UnfurledEval RD k μ i j N` holds for all `λ`, all positive `i, j` and all `N`, then
`PositiveNondeg RD k`. -/
theorem positiveNondeg_of_unfurledEval
    (H : ∀ (μ : X) (ν : Multiset I) (i j : KLR.Seq ν) (N : ℕ),
      Nonempty (UnfurledEval.{u, v, w, w₁, w₂} RD k μ i j N)) :
    PositiveNondeg RD k :=
  positiveNondeg_iff.2 fun μ ν i j _ =>
    (linearIndependent_posB_of_unfurledEval μ i j (H μ ν i j)).comp Subtype.val
      Subtype.val_injective

/-- **The nondegeneracy hypothesis of KL III Theorem 1.2 from the unfurled representations**
(Webster, arXiv:1603.06311v3, Theorem with label `nondegenerate`, with KL III's Remark after the
definition of nondegeneracy): if `UnfurledEval RD k μ i j N` holds for all `λ`, all positive
`i, j` and all `N`, then `CalculusNondeg RD k` (any field `k`, any Cartan datum with `I`
finite). Conditional on these evaluations, which come from Webster's Lemma `lem:g-action`. -/
theorem calculusNondeg_of_unfurledEval
    (H : ∀ (μ : X) (ν : Multiset I) (i j : KLR.Seq ν) (N : ℕ),
      Nonempty (UnfurledEval.{u, v, w, w₁, w₂} RD k μ i j N)) :
    CalculusNondeg RD k :=
  calculusNondeg_of_positive homGdim (positiveNondeg_of_unfurledEval H)

end Main

end Categorification.KLR.Unfurling
