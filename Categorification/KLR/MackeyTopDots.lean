/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Mackey
import Categorification.KLR.MackeyIntertwine

/-!
# Subword spanning with dots on top, and the Mackey filtration in the basis with dots on top

Khovanov–Lauda I (arXiv:0803.4121v2), Theorem 2.5 with dots on top, refined by subwords as in the
proof of Proposition 2.18. For a valid word `γ`, the diagram `ψ_γ x^p 1_i` is a combination of the
elements `x^u ψ_{ρ w} 1_j` with dots on top and `w` a product of a subword of `γ`
(`KLRAlgebra.gen_mem_topSpan`). Hence the step `F_c` of the Mackey filtration (`mackeyFilt`) lies
in the span of the elements with dots on top whose permutation has at most `c` crossing strands
(`KLRAlgebra.mackeyFilt_le_topSpan`), so the coordinates of an element of `F_c` in the basis with
dots on top (`KLRAlgebra.lbasis`) vanish at permutations with more than `c` crossing strands
(`KLRAlgebra.lbasis_repr_eq_zero_of_mem_mackeyFilt`).

The proof moves dots to the top through `ψ_γ` (`x_mul_gen_sub_mem_strictSpan`), by induction on
the length of `γ`, and reduces the dotless case to the dots-at-the-bottom spanning theorem
(`gen_mem_stdSpan`) by the horizontal flip `hflip`, which reverses words.

All statements hold over any commutative ring and for any `Q`, except the last, which uses the
basis with dots on top and so symmetric `Q`.

## Main definitions

* `KLRAlgebra.topSpan ρ X`: the span of the elements `x^p ψ_{ρ w} 1_i` with `w ∈ X`.

## Main results

* `KLRAlgebra.gen_mem_topSpan`, `KLRAlgebra.mackeyFilt_le_topSpan`,
  `KLRAlgebra.lbasis_repr_eq_zero_of_mem_mackeyFilt`.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {μ : Multiset I}

local notation "m" => Multiset.card μ

section TopSpan

variable (Q) in
/-- The span of the elements `x^p ψ_{ρ w} 1_i` with dots on top and `w ∈ X`. -/
noncomputable def topSpan (ρ : Perm (Fin m) → List ℕ) (X : Set (Perm (Fin m))) :
    Submodule k (KLRAlgebra k Q μ) :=
  Submodule.span k {r | ∃ w ∈ X, ∃ (p : MvPolynomial (Fin m) k) (i : Seq μ),
    pol p * ψw (ρ w) * e i = r}

variable (ρ : Perm (Fin (Multiset.card μ)) → List ℕ)

theorem top_mem_topSpan {X : Set (Perm (Fin m))} {w : Perm (Fin m)} (hw : w ∈ X)
    (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    (pol p * ψw (ρ w) * e i : KLRAlgebra k Q μ) ∈ topSpan Q ρ X := by
  unfold topSpan
  exact Submodule.subset_span ⟨w, hw, p, i, rfl⟩

theorem topSpan_mono {X Y : Set (Perm (Fin m))} (h : X ⊆ Y) :
    topSpan Q ρ X ≤ topSpan Q ρ Y :=
  Submodule.span_mono (by rintro _ ⟨w, hw, p, i, hr⟩; exact ⟨w, h hw, p, i, hr⟩)

/-- `topSpan` is stable under left multiplication by polynomials. -/
theorem pol_mul_mem_topSpan (q : MvPolynomial (Fin m) k) {X : Set (Perm (Fin m))}
    {r : KLRAlgebra k Q μ} (hr : r ∈ topSpan Q ρ X) : pol q * r ∈ topSpan Q ρ X := by
  have : topSpan Q ρ X ≤ (topSpan Q ρ X).comap (LinearMap.mulLeft k (pol q)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, p, i, rfl⟩
    change pol q * (pol p * ψw (ρ w) * e i) ∈ topSpan Q ρ X
    rw [← mul_assoc, ← mul_assoc, ← map_mul]
    exact top_mem_topSpan ρ hw _ i
  exact this hr

variable (hρ : ∀ w, IsReduced (Multiset.card μ) (ρ w) ∧ wordProd (Multiset.card μ) (ρ w) = w)

/-- The flip of a dotless diagram `ψ_γ 1_i` is a diagram on the reversed word. -/
private theorem hflip_ψw_mul_e (γ : List ℕ) (i : Seq μ) :
    hflip (ψw γ * e i : KLRAlgebra k Q μ) = ψw γ.reverse * e ((wordProd m γ.reverse)⁻¹ • i) := by
  rw [hflip_mul, hflip_e, hflip_ψw, e_mul_ψw]

/-- The flip of a standard element for the words `ρ'(w) = (ρ(w⁻¹))ʳᵉᵛ` is an element with dots
on top for the words `ρ`. -/
private theorem hflip_stdSpan_le {Y : Set (Perm (Fin m))} {r : KLRAlgebra k Q μ}
    (hr : r ∈ stdSpan Q (revWord ρ) Y) : hflip r ∈ topSpan Q ρ {w | w⁻¹ ∈ Y} := by
  have : stdSpan Q (revWord ρ) Y ≤
      (topSpan Q ρ {w | w⁻¹ ∈ Y}).comap (hflipEquiv k Q μ : _ →ₗ[k] _) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨j, v, u⟩, hv, rfl⟩
    change (hflipEquiv k Q μ) (stdElt (revWord ρ) (j, v, u)) ∈ topSpan Q ρ {w | w⁻¹ ∈ Y}
    rw [hflipEquiv_apply, stdElt, hflip_mul, hflip_mul, hflip_e, hflip_pol, hflip_ψw, revWord,
      List.reverse_reverse, ← mul_assoc, (e_commute_pol j _).eq, mul_assoc, e_mul_ψw, ← mul_assoc]
    refine top_mem_topSpan ρ ?_ _ _
    change (v⁻¹)⁻¹ ∈ Y
    rwa [inv_inv]
  exact this hr

include hρ in
/-- **Dotless diagrams, dots on top.** For a valid word `γ`, `ψ_γ 1_i` is a combination of
elements `x^u ψ_{ρ w} 1_j` with `w` a product of a subword of `γ`. -/
theorem ψw_mul_e_mem_topSpan (γ : List ℕ) (hγ : ValidWord m γ) (i : Seq μ) :
    (ψw γ * e i : KLRAlgebra k Q μ) ∈ topSpan Q ρ (subProds m γ) := by
  have h1 := gen_mem_stdSpan (Q := Q) (revWord ρ) (revWord_spec ρ hρ) γ.reverse
    (validWord_reverse.2 hγ) 1 ((wordProd m γ.reverse)⁻¹ • i)
  rw [map_one, mul_one, ← hflip_ψw_mul_e] at h1
  have h2 := hflip_stdSpan_le ρ h1
  rw [hflip_hflip] at h2
  refine topSpan_mono ρ ?_ h2
  rintro w ⟨δ, hδ, hw⟩
  refine ⟨δ.reverse, List.reverse_sublist.1 (by rwa [List.reverse_reverse]), ?_⟩
  rw [wordProd_reverse, hw, inv_inv]

include hρ in
/-- **Subword spanning with dots on top.** For a valid word `γ`, `ψ_γ x^p 1_i` is a combination
of the elements `x^u ψ_{ρ w} 1_j` with `w` a product of a subword of `γ`. -/
theorem gen_mem_topSpan (γ : List ℕ) (hγ : ValidWord m γ) (p : MvPolynomial (Fin m) k)
    (i : Seq μ) : (ψw γ * pol p * e i : KLRAlgebra k Q μ) ∈ topSpan Q ρ (subProds m γ) := by
  induction hn : γ.length using Nat.strong_induction_on generalizing γ p i with
  | _ n ih =>
  have hstrict : strictSpan k Q μ γ ≤ topSpan Q ρ (subProds m γ) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨δ, q, j, hδ, hl, rfl⟩
    exact topSpan_mono ρ (subProds_mono hδ) (ih δ.length (hn ▸ hl) δ (hγ.sublist hδ) q j rfl)
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [algHom_C, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc]
    exact Submodule.smul_mem _ a (ψw_mul_e_mem_topSpan ρ hρ γ hγ i)
  | add p q hp hq => rw [map_add, mul_add, add_mul]; exact add_mem hp hq
  | mul_X p b hp =>
    have hd := x_mul_gen_sub_mem_strictSpan (Q := Q) γ (wordProd m γ b) p i
    rw [show (wordProd m γ)⁻¹ (wordProd m γ b) = b from (wordProd m γ).symm_apply_apply b] at hd
    have hx := pol_mul_mem_topSpan ρ (X (wordProd m γ b)) hp
    rw [pol_X] at hx
    have := sub_mem hx (hstrict hd)
    rw [sub_sub_cancel] at this
    rwa [mul_comm p]

variable {n n'' : ℕ}

include hρ in
/-- **The Mackey filtration with dots on top.** The step `F_c` lies in the span of the elements
`x^u ψ_{ρ w} 1_j` with at most `c` crossing strands. -/
theorem mackeyFilt_le_topSpan (c : ℕ) :
    mackeyFilt k Q μ n n'' c ≤ topSpan Q ρ {w | crossCount n n'' w ≤ c} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨γ, p, i, hv, hc, rfl⟩
  exact topSpan_mono ρ (fun v hv' => hc v hv') (gen_mem_topSpan ρ hρ γ hv p i)

end TopSpan

section Basis

variable (hsym : KLRSymm Q) (ρ : Perm (Fin (Multiset.card μ)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card μ) (ρ w) ∧ wordProd (Multiset.card μ) (ρ w) = w)

/-- `topSpan X` is the span of the basis elements with dots on top whose permutation lies in
`X`. -/
theorem topSpan_le_span_lbasis (X : Set (Perm (Fin m))) :
    topSpan Q ρ X ≤ Submodule.span k (lbasis hsym ρ hρ '' {b | b.2.1 ∈ X}) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨w, hw, p, i, rfl⟩
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [show monomial u a = a • monomial u (1 : k) by rw [smul_monomial, smul_eq_mul, mul_one],
      map_smul, smul_mul_assoc, smul_mul_assoc]
    refine Submodule.smul_mem _ a (Submodule.subset_span ⟨(i, w, u), hw, ?_⟩)
    rw [lbasis_apply]
  | add p q hp hq => rw [map_add, add_mul, add_mul]; exact add_mem hp hq

variable {n n'' : ℕ}

/-- **Coordinates of the Mackey filtration in the basis with dots on top.** An element of `F_c`
has coordinate `0` at every basis element `x^u ψ_{ρ w} 1_i` whose permutation `w` has more than
`c` crossing strands. -/
theorem lbasis_repr_eq_zero_of_mem_mackeyFilt {c : ℕ}
    {y : KLRAlgebra k Q μ} (hy : y ∈ mackeyFilt k Q μ n n'' c)
    (b : Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) (hb : c < crossCount n n'' b.2.1) :
    (lbasis hsym ρ hρ).repr y b = 0 := by
  have h := topSpan_le_span_lbasis hsym ρ hρ _ (mackeyFilt_le_topSpan ρ hρ c hy)
  rw [Module.Basis.mem_span_image] at h
  by_contra hne
  exact absurd (h (Finsupp.mem_support_iff.2 hne)) (by simpa using hb)

end Basis

end KLRAlgebra

end Categorification.KLR
