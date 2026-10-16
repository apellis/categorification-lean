/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Reindex
import Categorification.KLR.Symmetries
import Categorification.KLR.Examples.Small

/-!
# Relabellings and the symmetries of KLR algebras

The relabelling isomorphisms `R(ν₁) ≃ R(ν₂)` of `KLR/Reindex.lean` commute with the horizontal
flip `hflip` (KL I, end of §2.1), and, when the bijection of sequences commutes with reversal,
with the vertical flip `σ`. Reindexing along an injection of labels is such a relabelling, also
when the parameters of the source are only known to agree with the pulled back ones
(`SeqRelabel.ofInjectiveOf`). Consequently the relabelling of cyclotomic quotients carries
`hflip (σ u)` to `hflip (σ u')` for the relabelled element `u'`
(`CycKLR.relabelEquiv_mk_hflip_sigma`).

This identifies the coefficients `hflip (σ (e(s) r e(t)))` of the action of a cyclotomic family
at its vacuum (`CyclotomicAction.wcoord_klrAct_wgen`) with those of a larger label set, as used
in B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`.

## Main results

* `KLRAlgebra.hflip_relabelHom`, `KLRAlgebra.sigma_relabelHom`.
* `SeqRelabel.ofInjectiveOf`: reindexing along an injection, for parameters agreeing with the
  pulled back ones.
* `CycKLR.relabelEquiv_mk_hflip_sigma`.
-/

open MulOpposite

namespace Categorification.KLR

variable {k : Type*} [CommRing k] {I₁ I₂ : Type*} [DecidableEq I₁] [DecidableEq I₂]
  {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k} {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}
  {ν₁ : Multiset I₁} {ν₂ : Multiset I₂} (R : SeqRelabel k Q₁ Q₂ ν₁ ν₂)

namespace KLRAlgebra

/-- **Relabelling commutes with the horizontal flip.** -/
theorem hflip_relabelHom (u : KLRAlgebra k Q₁ ν₁) :
    hflip (relabelHom R u) = relabelHom R (hflip u) := by
  have h : (flipAlgHom k Q₂ ν₂).comp (relabelHom R) =
      (AlgHom.op (relabelHom R)).comp (flipAlgHom k Q₁ ν₁) := by
    refine algHom_ext (fun i => ?_) (fun a => ?_) (fun j => ?_) <;>
      apply unop_injective
    · change hflip (relabelHom R (e i)) = relabelHom R (hflip (e i))
      simp
    · change hflip (relabelHom R (x a)) = relabelHom R (hflip (x a))
      simp
    · change hflip (relabelHom R (ψ j)) = relabelHom R (hflip (ψ j))
      simp
  exact congrArg (fun φ => (φ u).unop) h

theorem rev_cast {n n' : ℕ} (h : n = n') (a : Fin n) : (Fin.cast h a).rev = Fin.cast h a.rev := by
  subst h; rfl

variable (hQ₁ : KLRSymm Q₁) (hQ₂ : KLRSymm Q₂)
  (hrev : ∀ i : Seq ν₁, R.equiv i.rev = (R.equiv i).rev)
include hrev

omit hrev in
/-- The sign of the vertical flip of a crossing is preserved by a relabelling. -/
theorem sgn_relabel (j : ℕ) (i : Seq ν₁) : sgn k j (R.equiv i) = sgn k j i := by
  by_cases h : j + 1 < Multiset.card ν₁
  · have h' : j + 1 < Multiset.card ν₂ := R.card_eq ▸ h
    rw [sgn_of_lt h, sgn_of_lt h']
    have := R.lbl_eq_iff i ⟨j, by omega⟩ ⟨j + 1, h⟩
    simp only [Seq.lbl] at this
    simp only [Fin.cast_mk] at this
    exact if_congr this rfl rfl
  · have h' : ¬ j + 1 < Multiset.card ν₂ := R.card_eq ▸ h
    simp [sgn, h, h']

/-- **Relabelling commutes with the vertical flip**, for a bijection of sequences commuting with
reversal. -/
theorem sigma_relabelHom (u : KLRAlgebra k Q₁ ν₁) :
    sigma hQ₂ (relabelHom R u) = relabelHom R (sigma hQ₁ u) := by
  have h : (sigma hQ₂).toAlgHom.comp (relabelHom R) =
      (relabelHom R).comp (sigma hQ₁).toAlgHom := by
    refine algHom_ext (fun i => ?_) (fun a => ?_) (fun j => ?_)
    · simp [hrev]
    · simp [rev_cast]
    · change sigma hQ₂ (relabelHom R (ψ j)) = relabelHom R (sigma hQ₁ (ψ j))
      rw [relabelHom_ψ]
      by_cases hj : j + 1 < Multiset.card ν₁
      · have hj' : j + 1 < Multiset.card ν₂ := R.card_eq ▸ hj
        rw [sigma_ψ hQ₂ hj', sigma_ψ hQ₁ hj, map_sum, ← R.equiv.sum_comp]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, map_mul, relabelHom_ψ, relabelHom_e, sgn_relabel R, hrev, R.card_eq]
      · have hj' : ¬ j + 1 < Multiset.card ν₂ := R.card_eq ▸ hj
        rw [sigma_ψ_of_le (ν := ν₂) hQ₂ (by omega), sigma_ψ_of_le (ν := ν₁) hQ₁ (by omega),
          map_zero]
  exact congrArg (fun φ => φ u) h

end KLRAlgebra

namespace CycKLR

open Polynomial KLRAlgebra

variable {a₁ : I₁ → k[X]} {a₂ : I₂ → k[X]}
  (ha : ∀ (i : Seq ν₁) (h : 0 < Multiset.card ν₁),
    a₂ ((R.equiv i).lbl (Fin.cast R.card_eq ⟨0, h⟩)) = a₁ (i.lbl ⟨0, h⟩))
  (hQ₁ : KLRSymm Q₁) (hQ₂ : KLRSymm Q₂)
  (hrev : ∀ i : Seq ν₁, R.equiv i.rev = (R.equiv i).rev)

include hrev in
/-- **The relabelling of cyclotomic quotients carries `hflip ∘ σ` to `hflip ∘ σ`.** -/
theorem relabelEquiv_mk_hflip_sigma (u : KLRAlgebra k Q₁ ν₁) :
    relabelEquiv R ha (mk k Q₁ a₁ ν₁ (hflip (sigma hQ₁ u))) =
      mk k Q₂ a₂ ν₂ (hflip (sigma hQ₂ (KLRAlgebra.relabelHom R u))) := by
  rw [relabelEquiv_mk, ← KLRAlgebra.hflip_relabelHom,
    KLRAlgebra.sigma_relabelHom R hQ₁ hQ₂ hrev]

end CycKLR

section Reindex

variable {I J : Type*} [DecidableEq I] [DecidableEq J] {f : J → I}

omit [DecidableEq I] [DecidableEq J] in
theorem Seq.map_rev {ν' : Multiset J} (i : Seq ν') : Seq.map f i.rev = (Seq.map f i).rev :=
  Subtype.ext (funext fun b => by
    change f (i.1 (Fin.cast _ b).rev) = f (i.1 (Fin.cast _ b.rev))
    rw [KLRAlgebra.rev_cast])

variable (hf : Function.Injective f) (Q : I → I → MvPolynomial (Fin 2) k)
  (Q' : J → J → MvPolynomial (Fin 2) k) (hQ : ∀ a b, a ≠ b → Q (f a) (f b) = Q' a b)
  (ν' : Multiset J)

/-- **Reindexing along an injection of labels** `f : J → I`, from parameters `Q'` agreeing with
`Q ∘ (f × f)` at distinct labels: `𝐣 ↦ f ∘ 𝐣`. -/
noncomputable def SeqRelabel.ofInjectiveOf : SeqRelabel k Q' Q ν' (ν'.map f) where
  card_eq := (SeqRelabel.ofInjective hf Q ν').card_eq
  equiv := Seq.mapEquiv hf ν'
  equiv_smul := (SeqRelabel.ofInjective hf Q ν').equiv_smul
  lbl_eq_iff := (SeqRelabel.ofInjective hf Q ν').lbl_eq_iff
  Q_eq i a b h := ((SeqRelabel.ofInjective hf Q ν').Q_eq i a b h).trans (hQ _ _ h)

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem SeqRelabel.ofInjectiveOf_equiv (i : Seq ν') :
    (SeqRelabel.ofInjectiveOf hf Q Q' hQ ν').equiv i = Seq.map f i := rfl

omit [DecidableEq I] [DecidableEq J] in
theorem SeqRelabel.ofInjectiveOf_rev (i : Seq ν') :
    (SeqRelabel.ofInjectiveOf hf Q Q' hQ ν').equiv i.rev =
      ((SeqRelabel.ofInjectiveOf hf Q Q' hQ ν').equiv i).rev :=
  Seq.map_rev i

end Reindex

end Categorification.KLR
