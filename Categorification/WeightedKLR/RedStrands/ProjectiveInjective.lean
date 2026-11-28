/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedFirstCopresentation
import Categorification.WeightedKLR.RedStrands.RedFirstInjective
import Categorification.Algebra.CornerFaithfulEmbedding
import Categorification.Algebra.InjectiveHull
import Categorification.Algebra.ModuleFiltrationEmbedding
import Categorification.WeightedKLR.RedStrands.PhiStandardLayers
import Categorification.WeightedKLR.RedStrands.StandardStratificationStd

set_option backward.isDefEq.respectTransparency false

/-!
# Projective-injective `T^λ`-modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 5.30
(v2: Theorem 5.27): an indecomposable projective `T^λ`-module is injective if and only if it is a
summand of the red-first projective `P⁰ = T^λ e⁰`, if and only if it is a summand of the
injective hull of an indecomposable standard module.

(3) ⇒ (1) is `injective_of_isSummand_redFirstProjective` (`P⁰` is self-dual). For (1) ⇒ (3),
every projective module `P` has no nonzero element killed by `e⁰ T^λ`, since `T^λ` itself has
none (`eq_zero_of_redFirstIdem_mul`, from the injectivity of Lemma 5.25). By the self-duality
of `P⁰` such a module embeds into a finite sum of copies of `P⁰`; when `P` is injective the
embedding splits, and when `P` is indecomposable it is then a summand of `P⁰` itself
(`exists_retraction_lIdeal_of_injective`).

Webster's proof of (1) ⇒ (3) passes through (2) (the injective hull of a standard module); the
argument here goes directly through the dominant dimension of `T^λ`. (1) ⇔ (2) is proved
separately, as in Webster: an indecomposable injective of finite length is uniform, and a nonzero
submodule of `P` embeds into a standard module through a standard filtration.

## Main results

* `eq_zero_of_redFirstIdem_smul_of_projective`: projective modules have no nonzero element killed
  by `e⁰ T^λ`.
* `injective_iff_isSummand_redFirstProjective`: **Theorem 5.30, (1) ⇔ (3)**.
* `injective_iff_isSummandOfInjectiveHull_standard`: **Theorem 5.30, (1) ⇔ (2)**.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

open scoped Classical

variable {I : Type} {k : Type} [Field k] {C : QuantumGroup.CartanDatum I}
  {Q : I → I → MvPolynomial (Fin 2) k} (hR : IsRouquierQ C Q)
  (hQs : KLRSymm Q)

local notation "QL" => Q

include hR hQs in
/-- **A projective `T^λ`-module has no nonzero element killed by `e⁰ T^λ`**: it is a summand of a
free module, and `T^λ` has none (Webster, arXiv:1309.3796v3, Lemma 5.25). -/
theorem eq_zero_of_redFirstIdem_smul_of_projective {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (ν : Multiset I) {P : Type} [AddCommGroup P] [Module (TensorProductAlgebra k QL Λ ν) P]
    [Module.Projective (TensorProductAlgebra k QL Λ ν) P] (m : P)
    (hm : ∀ a, (redFirstIdem QL Λ ν * a) • m = 0) : m = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective (TensorProductAlgebra k QL Λ ν) P›
  have hz : s m = 0 := by
    ext p
    refine eq_zero_of_redFirstIdem_mul hR hQs Λ ν (s m p) fun a => ?_
    have h := congrArg (fun f => f p) (s.map_smul (redFirstIdem QL Λ ν * a) m)
    simp only [hm, map_zero, Finsupp.zero_apply, Finsupp.smul_apply, smul_eq_mul] at h
    exact h.symm
  have := LinearMap.congr_fun hs m
  rw [LinearMap.comp_apply, hz, map_zero, LinearMap.id_apply] at this
  exact this.symm

include hR hQs in
/-- **Webster, arXiv:1309.3796v3, Theorem 5.30, (1) ⇔ (3)** (v2: Theorem 5.27): an indecomposable
finitely generated (equivalently, finite-dimensional) projective `T^λ`-module is injective if and
only if it is a summand of the red-first projective `P⁰ = T^λ e⁰` (`IsModuleSummand`).
Rouquier parameters with symmetric `Q`, over a field; the grading is not recorded, so "up to
grading shift" is implicit. -/
theorem injective_iff_isSummand_redFirstProjective {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (ν : Multiset I) {P : Type} [AddCommGroup P] [Module (TensorProductAlgebra k QL Λ ν) P]
    [Module.Finite (TensorProductAlgebra k QL Λ ν) P]
    [Module.Projective (TensorProductAlgebra k QL Λ ν) P]
    (hP : IsIndecomposableModule (TensorProductAlgebra k QL Λ ν) P) :
    Module.Injective (TensorProductAlgebra k QL Λ ν) P ↔
      IsModuleSummand (TensorProductAlgebra k QL Λ ν) P (lIdeal (redFirstIdem QL Λ ν)) := by
  constructor
  · intro hinj
    have : FiniteDimensional k (TensorProductAlgebra k QL Λ ν) :=
      tensorProductAlgebra_finite Λ ν hR
    let : Module k P := Module.compHom P (algebraMap k (TensorProductAlgebra k QL Λ ν))
    have : IsScalarTower k (TensorProductAlgebra k QL Λ ν) P :=
      ⟨fun c a m => by
        change (c • a) • m = algebraMap k (TensorProductAlgebra k QL Λ ν) c • a • m
        rw [Algebra.smul_def, mul_smul]⟩
    have : FiniteDimensional k P := Module.Finite.trans (TensorProductAlgebra k QL Λ ν) P
    obtain ⟨τ, hτ⟩ := redFirstIdem_pairing_nondegenerate hR hQs Λ ν
    exact exists_retraction_lIdeal_of_injective (τ := τ)
      (isIdempotentElem_redFirstIdem QL Λ ν) hτ (finrank_leftCorner_redFirstIdem Λ ν) hP
      (_root_.Module.Baer.of_injective hinj)
      (eq_zero_of_redFirstIdem_smul_of_projective hR hQs Λ ν)
  · rintro ⟨i, r, h⟩
    exact injective_of_isSummand_redFirstProjective hR hQs Λ ν i r h

include hR hQs in
/-- **Webster, arXiv:1309.3796v3, Theorem 5.30, (1) ⇔ (2)** (v2: Theorem 5.27): an indecomposable
finitely generated projective `T^λ`-module is injective if and only if it is a summand of an
injective hull of an indecomposable standard module, i.e. of an indecomposable summand `S` of
some `S_c` (`IsSummandOfInjectiveHull`). Rouquier parameters with symmetric `Q`, over a field;
ungraded, so "up to grading shift" is implicit.

(1) ⇒ (2): `P` is a summand of some `T^λ e(s)` (Krull–Schmidt exchange), which has a standard
filtration, so a nonzero submodule of `P` embeds into some `S_c`, and then into an indecomposable
summand `S` of `S_c`; as `P` is injective and uniform, it is a summand of the injective hull of
`S`. (2) ⇒ (1): a summand of an injective module is injective. -/
theorem injective_iff_isSummandOfInjectiveHull_standard {n : ℕ} (Λ : Fin n → I →₀ ℕ)
    (ν : Multiset I) {P : Type} [AddCommGroup P] [Module (TensorProductAlgebra k QL Λ ν) P]
    [Module.Finite (TensorProductAlgebra k QL Λ ν) P]
    [Module.Projective (TensorProductAlgebra k QL Λ ν) P]
    (hP : IsIndecomposableModule (TensorProductAlgebra k QL Λ ν) P) :
    Module.Injective (TensorProductAlgebra k QL Λ ν) P ↔
      ∃ (c : {t : Seq (stendhalWeight n ν) // IsRedOrdered t})
        (S : Submodule (TensorProductAlgebra k QL Λ ν) (stdModule QL Λ ν c)),
        IsIndecomposableModule (TensorProductAlgebra k QL Λ ν) S ∧
        IsModuleSummand (TensorProductAlgebra k QL Λ ν) S (stdModule QL Λ ν c) ∧
        IsSummandOfInjectiveHull (TensorProductAlgebra k QL Λ ν) P S := by
  constructor
  · intro hinj
    have : Module.Finite k (TensorProductAlgebra k QL Λ ν) := tensorProductAlgebra_finite Λ ν hR
    have : IsArtinianRing (TensorProductAlgebra k QL Λ ν) := IsArtinianRing.of_finite k _
    obtain ⟨m, f, g, -, -, hfg⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective (TensorProductAlgebra k QL Λ ν) P
    let X : Fin m × {s : Seq (stendhalWeight n ν) // IsRedOrdered s} → Type := fun p =>
      lIdeal (seqIdem QL Λ p.2.1 p.2.2)
    let Φ : (Fin m → TensorProductAlgebra k QL Λ ν) →ₗ[TensorProductAlgebra k QL Λ ν]
        (∀ p, X p) :=
      { toFun := fun x p => ⟨x p.1 * seqIdem QL Λ p.2.1 p.2.2, by
          change _ * _ * _ = _ * _
          rw [mul_assoc, seqIdem_mul_self]⟩
        map_add' := fun x y => funext fun p => Subtype.ext (add_mul _ _ _)
        map_smul' := fun a x => funext fun p => Subtype.ext (mul_assoc _ _ _) }
    let Ψ : (∀ p, X p) →ₗ[TensorProductAlgebra k QL Λ ν]
        (Fin m → TensorProductAlgebra k QL Λ ν) :=
      { toFun := fun y j => ∑ s, (y (j, s) : TensorProductAlgebra k QL Λ ν)
        map_add' := fun y z => funext fun j => by
          rw [Pi.add_apply, ← Finset.sum_add_distrib]
          rfl
        map_smul' := fun a y => funext fun j => by
          rw [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
          rfl }
    have hΨΦ : Ψ ∘ₗ Φ = LinearMap.id := LinearMap.ext fun x => funext fun j => by
      change ∑ s : {s : Seq (stendhalWeight n ν) // IsRedOrdered s},
        x j * seqIdem QL Λ s.1 s.2 = x j
      rw [← Finset.mul_sum, sum_seqIdem_eq_one n ν QL Λ, mul_one]
    obtain ⟨p, i, r, hri⟩ := hP.exists_retraction_of_retraction_pi (Φ ∘ₗ g) (f ∘ₗ Ψ) (by
      rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc g Φ Ψ, hΨΦ, LinearMap.id_comp, hfg])
    have hi : Function.Injective i := fun x y h => by
      rw [← LinearMap.id_apply (R := TensorProductAlgebra k QL Λ ν) x,
        ← LinearMap.id_apply (R := TensorProductAlgebra k QL Λ ν) y, ← hri,
        LinearMap.comp_apply, LinearMap.comp_apply, h]
    obtain ⟨l, hl⟩ := hasStandardFiltrations_of_rouquier hR hQs Λ ν p.2.1 p.2.2
    have : Nontrivial P := hP.1
    have hrange : LinearMap.range i ≠ ⊥ := by
      obtain ⟨x, hx⟩ := exists_ne (0 : P)
      intro h
      have hx' : i x ∈ LinearMap.range i := ⟨x, rfl⟩
      rw [h, Submodule.mem_bot] at hx'
      exact hx (hi (by rw [hx', map_zero]))
    obtain ⟨c, -, K', hK'le, hK', φ, hφ⟩ := hl.exists_injective_of_ne_bot (LinearMap.range i)
      hrange
    let K : Submodule (TensorProductAlgebra k QL Λ ν) P := K'.comap i
    have hK : K ≠ ⊥ := by
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK'
      obtain ⟨x, rfl⟩ := hK'le hy
      intro h
      have : x ∈ K := hy
      rw [h, Submodule.mem_bot] at this
      exact hy0 (by rw [this, map_zero])
    let ρ : K →ₗ[TensorProductAlgebra k QL Λ ν] K' := i.restrict fun x hx => hx
    have hρ : Function.Injective ρ := fun x y h => Subtype.ext (hi (congrArg Subtype.val h))
    exact ⟨c, hP.exists_isSummandOfInjectiveHull (Module.Baer.of_injective hinj) hK (φ ∘ₗ ρ)
      (hφ.comp hρ)⟩
  · rintro ⟨c, S, -, -, h⟩
    exact h.baer.injective

end Categorification.Stendhal
