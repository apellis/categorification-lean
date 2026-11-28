/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceStandardEquiv
import Categorification.WeightedKLR.RedStrands.TensorLayerFiltration
import Categorification.WeightedKLR.RedStrands.LoadingDecomposition
import Categorification.WeightedKLR.RedStrands.ParabolicStandardFiniteFiltration
import Categorification.Algebra.ModuleFiltrationMap

/-!
# Projectives of `T^λ` have standard filtrations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 5.20, in filtration form: for every red-ordered loading `s`, the projective
`T^λ e(s)` has a finite filtration whose successive quotients are standard modules `S_t`
(Definition 5.1) of red-ordered loadings `t`.

Webster states Proposition 5.20 for the particular filtration `P_{>φ} ⊆ P_{≥φ}` of `T^λ`
indexed by the set `Φ`, with `P_{≥φ}/P_{>φ} ≅ S_{iφ}^{κφ}`, and proves it by a surjection and a
dimension count (the identity for `v_i^κ` in the proof; v3: Lemma 5.19). We prove the existence of a filtration of each `T^λ e(s)` by
standard modules, by Webster's induction on the number of red strands:

* with no red strands, Webster's order is trivial, so `S_s = T^λ e(s)`
  (`hasStandardFiltrations_zero`);
* every red-ordered loading with `ℓ + 1` red strands is `(s₀, λ_{ℓ+1}, w)`
  (`exists_blackWordLoading_appendRed`), and `T^λ e(s₀, λ_{ℓ+1}, w)` is filtered by
  standardizations `S(T^{λ'} e(t) ⊠ R^{λ_{ℓ+1}} e(u))` (`hasFiltration_loadingProj_of_finite`,
  `exists_stdLayerModule_equiv_tensorLayer`); a standard filtration of `T^{λ'} e(t)` passes
  through `⊠` and standardization (`hasFiltration_tensorLayer`), and
  `S(S_{t'} ⊠ R e(u)) ≅ S_{t' λ_{ℓ+1} u}` (`twoPieceStandardEquiv`).

The step uses the route hypothesis `AllFiniteDeltaInjective` of Proposition 5.5 (the
`F`-part of Proposition 5.5 for finite-dimensional modules) at every number of red strands; it
holds for Rouquier parameters (`allFiniteDeltaInjective_of_rouquier`).

## Main definitions and results

* `HasStandardFiltrations Q Λ`: every `T^λ e(s)` has a filtration by standard modules.
* `hasStandardFiltrations_zero`, `hasStandardFiltrations_succ`, `hasStandardFiltrations`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR ModuleFiltration
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k)

/-- The standard module `S_t` of a red-ordered loading `t`, as a module over `T^λ`. -/
abbrev stdModule {n : ℕ} (Λ : Fin n → I →₀ ℕ) (ν : Multiset I)
    (c : {t : Seq (stendhalWeight n ν) // IsRedOrdered t}) :
    ModuleCat (TensorProductAlgebra k Q Λ ν) :=
  ModuleCat.of (TensorProductAlgebra k Q Λ ν) (leftStandard Q Λ c.1 c.2)

/-- **Projectives have standard filtrations** (Webster, arXiv:1309.3796v2, Proposition 5.20,
filtration form): for every red-ordered loading `s`, the projective `T^λ e(s)` has a finite
filtration whose subquotients are standard modules `S_t` of red-ordered loadings `t`. -/
def HasStandardFiltrations {n : ℕ} (Λ : Fin n → I →₀ ℕ) : Prop :=
  ∀ (ν : Multiset I) (s : Seq (stendhalWeight n ν)) (hs : IsRedOrdered s),
    ∃ m : List {t : Seq (stendhalWeight n ν) // IsRedOrdered t},
      HasFiltration (stdModule Q Λ ν) m
        (ModuleCat.of (TensorProductAlgebra k Q Λ ν) (lIdeal (seqIdem Q Λ s hs)))

/-- With no red strands, Webster's order is trivial, so `U_s = 0`. -/
theorem leftUpper_eq_bot_of_zero (Λ : Fin 0 → I →₀ ℕ) {ν : Multiset I}
    (s : Seq (stendhalWeight 0 ν)) (hs : IsRedOrdered s) : leftUpper Q Λ s hs = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨t, ht, a, hlt, -⟩
  exact (hlt.2 fun r => r.elim0).elim

/-- **Base of the induction**: with no red strands, `T^λ e(s) = S_s`. -/
theorem hasStandardFiltrations_zero (Λ : Fin 0 → I →₀ ℕ) : HasStandardFiltrations Q Λ := by
  intro ν s hs
  refine ⟨[⟨s, hs⟩], HasFiltration.single ?_⟩
  refine (Submodule.quotEquivOfEqBot _ ?_).symm
  rw [leftUpper_eq_bot_of_zero, Submodule.comap_bot, Submodule.ker_subtype]

variable {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)

local notation "old" => Λ ∘ Fin.castSucc
local notation "Told" => TensorProductAlgebra k Q (old)

/-- The standardization `S(S_t ⊠ R^{λ_{ℓ+1}} e(u))`, with its split `θ + β = ν`, is the
standard module of the two-piece loading `t λ_{ℓ+1} u` (`twoPieceStandardEquiv`). -/
theorem nonempty_stdLayerModule_twoPiece_equiv {θ β ν : Multiset I} (h : θ + β = ν)
    {t : Seq (stendhalWeight ℓ θ)} (ht : IsRedOrdered t) (u : Seq β) :
    Nonempty (stdLayerModule Q Λ hQ
        (tensorLayer Q Λ h (ModuleCat.of (Told θ) (leftStandard Q (old) t ht))
          (cycProj Q Λ β u)) ≃ₗ[TensorProductAlgebra k Q Λ ν]
      ModuleCat.of (TensorProductAlgebra k Q Λ ν)
        (leftStandard Q Λ (Seq.cast (congrArg (stendhalWeight (ℓ + 1)) h)
          (twoPieceLoading θ β t u))
          ((isRedOrdered_cast _ _).2 (isRedOrdered_twoPieceLoading ht u)))) := by
  subst h
  exact ⟨{ twoPieceStandardEquiv Q Λ ht u hQ with
    map_smul' := fun a x => (twoPieceStandardEquiv Q Λ ht u hQ).map_smul a x }⟩

/-- The two-piece loading `t λ_{ℓ+1} u`, transported along `θ + β = ν`. -/
def twoPieceLabel {θ β ν : Multiset I} (h : θ + β = ν) (u : Seq β)
    (d : {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t}) :
    {t : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered t} :=
  ⟨Seq.cast (congrArg (stendhalWeight (ℓ + 1)) h) (twoPieceLoading θ β d.1 u),
    (isRedOrdered_cast _ _).2 (isRedOrdered_twoPieceLoading d.2 u)⟩

variable {C : QuantumGroup.CartanDatum I}

/-- **Induction step** (Webster, arXiv:1309.3796v2, proof of Proposition 5.20): if the
projectives of the first `ℓ` red strands have standard filtrations, so have those of `T^λ`.
Route hypothesis: `AllFiniteDeltaInjective` (Proposition 5.5, `F`-part). -/
theorem hasStandardFiltrations_succ (hR : IsRouquierQ C Q)
    (hall : AllFiniteDeltaInjective Q Λ hQ) (hold : HasStandardFiltrations Q (old)) :
    HasStandardFiltrations Q Λ := by
  intro ν s hs
  obtain ⟨θ, w, s₀, hs₀, h, hc⟩ := exists_blackWordLoading_appendRed ν.card ν rfl s hs
  subst h
  rw [Seq.cast_rfl] at hc
  subst hc
  have hF : HasFiltration (stdLayerModule Q Λ hQ) ((redLayer Q Λ θ s₀ hs₀).wordLayers Q Λ w)
      (ModuleCat.of _ (lIdeal (seqIdem Q Λ _ hs))) :=
    hasFiltration_loadingProj_of_finite hR hall w s₀ hs₀
  refine hF.exists_refine fun c hc => ?_
  obtain ⟨t, ht, u, ⟨e⟩⟩ := exists_stdLayerModule_equiv_tensorLayer Q Λ hQ w s₀ hs₀ c hc
  obtain ⟨m', hm'⟩ := hold c.θ t ht
  have h₁ := hasFiltration_tensorLayer Q Λ hQ c.h (cycProj Q Λ c.β u)
    (X := oldProj Q Λ c.θ t ht) hm'
  have h₂ : HasFiltration (fun d => stdModule Q Λ _ (twoPieceLabel c.h u d)) m'
      (stdLayerModule Q Λ hQ (tensorLayer Q Λ c.h (oldProj Q Λ c.θ t ht)
        (cycProj Q Λ c.β u))) :=
    h₁.mono fun d => nonempty_stdLayerModule_twoPiece_equiv Q Λ hQ c.h d.2 u
  exact ⟨_, (HasFiltration.relabel (L := stdModule Q Λ _) (twoPieceLabel c.h u) h₂).of_equiv
    e.symm⟩

/-- **Projectives of `T^λ` have standard filtrations** (Webster, arXiv:1309.3796v2,
Proposition 5.20, filtration form), by induction on the number of red strands. Route
hypothesis: `AllFiniteDeltaInjective` (Proposition 5.5, `F`-part) for every sequence of
highest weights. -/
theorem hasStandardFiltrations (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ) :
    ∀ {n : ℕ} (Λ' : Fin n → I →₀ ℕ), HasStandardFiltrations Q Λ'
  | 0, Λ' => hasStandardFiltrations_zero Q Λ'
  | n + 1, Λ' => hasStandardFiltrations_succ Q Λ' hQ hR (hall n Λ')
      (hasStandardFiltrations hR hall (Λ' ∘ Fin.castSucc))

end Categorification.Stendhal
