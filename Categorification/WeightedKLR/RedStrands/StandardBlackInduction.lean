/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.BlockInsertLoading
import Categorification.WeightedKLR.RedStrands.ProjectiveStandardFiltration
import Categorification.WeightedKLR.RedStrands.LeftStandardGFin

/-!
# `Fᵢ` of a standard module is filtered by standard modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Proposition 5.5 (`Fᵢ`-part) for the full standardization `𝕊^{λ_1; …; λ_n}`, applied to a
standard module, as used in the proof of Proposition 5.6. For a red-ordered loading `t` with
`n` red strands, `Fᵢ S_t` has a filtration whose subquotients are the standard modules
`S_{t^{(k)}}`, `k = n, n - 1, …, 0`, from the top, where `t^{(k)}` adds a black strand `i` at
the right end of block `k` (`blockInsertLoading`). This is the categorification of the
coproduct formula for `Fᵢ` (Webster's (5.2)): the new strand ends in one of the `n + 1` blocks.

The proof is Webster's reduction to two tensor factors: `t = t' λ_n u`, and
`S_t ≅ 𝕊(S_{t'} ⊠ R^{λ_n} e(u))` (`twoPieceStandardEquiv`). The two-piece `Fᵢ`-part of
Proposition 5.5 (`hasFiltration_blackInd_stdLayer`) filters `Fᵢ 𝕊(S_{t'} ⊠ R e(u))` by
`𝕊(S_{t'} ⊠ R e(u i)) ≅ S_{t^{(n)}}` over `𝕊(Fᵢ S_{t'} ⊠ R e(u))`, and the latter is filtered
by induction on the number of red strands, through the exactness of `𝕊` and `⊠`.

The two-piece step uses the route hypothesis `AllFiniteDeltaInjective` (injectivity of the
first map of the two-piece `Fᵢ`-part for finite-dimensional inputs), which is proved at the
standard Khovanov–Lauda parameters (`allFiniteDeltaInjective_std`); with it this file has no
further hypothesis.

## Main definitions

* `blockInsertLabels i t`: the labels `t^{(n)}, …, t^{(0)}`.
* `BlackIndStandardFiltration Q Λ`: `Fᵢ S_t` has the filtration with these labels, for all
  `i`, `t`.

## Main results

* `blackIndStandardFiltration_zero`: with no red strands, `Fᵢ S_t = S_{t i}`.
* `blackIndStandardFiltration_succ`: the induction step.
* `blackIndStandardFiltration`: the filtration for every number of red strands.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.ModuleFiltration.HasFiltration

universe u v w w'

variable {A : Type u} [Ring A] {ι : Type w} {ι' : Type w'} {L : ι → ModuleCat.{v} A}
  {L' : ι' → ModuleCat.{v} A}

/-- Refining a filtration: if every subquotient `L c`, `c ∈ m`, has a filtration by `L'` with
labels `M c`, then `Y` has a filtration by `L'` with labels `m.flatMap M`. -/
theorem bind_of_mem {M : ι → List ι'} {m : List ι} {Y : ModuleCat.{v} A}
    (h : HasFiltration L m Y) (hL : ∀ c ∈ m, HasFiltration L' (M c) (L c)) :
    HasFiltration L' (m.flatMap M) Y := by
  induction h with
  | zero hY => simpa using HasFiltration.zero (L := L') hY
  | cons f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    have := ((hL c List.mem_cons_self).of_equiv e.symm).extension f g hf hfg hg
      (ih fun d hd => hL d (List.mem_cons_of_mem _ hd))
    simpa using this

/-- Filtrations whose label lists are equal. -/
theorem of_labels_eq {m m' : List ι} {Y : ModuleCat.{v} A} (h : HasFiltration L m Y)
    (hm : m = m') : HasFiltration L m' Y :=
  hm ▸ h

end Categorification.ModuleFiltration.HasFiltration

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra InductionAlong MulOpposite ModuleFiltration
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k)

local notation "Si" j => (Singleton.singleton j : Multiset I)

/-- `Fᵢ` on modules over `T^λ_ν`, for any number of red strands: induction along
`appendBlack`. -/
abbrev blackIndT {n : ℕ} (Λ : Fin n → I →₀ ℕ) (i : I) {ν : Multiset I}
    (X : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)) :
    ModuleCat.{0} (TensorProductAlgebra k Q Λ ((Si i) + ν)) :=
  ModuleCat.of _ (Ind X (appendBlackNU (Q := Q) (Λ := Λ) i ν))

/-- The labels `t^{(n)}, t^{(n-1)}, …, t^{(0)}` of the filtration of `Fᵢ S_t`. -/
def blockInsertLabels {n : ℕ} (i : I) {ν : Multiset I} (t : Seq (stendhalWeight n ν))
    (ht : IsRedOrdered t) : List {s : Seq (stendhalWeight n ((Si i) + ν)) // IsRedOrdered s} :=
  (List.range (n + 1)).reverse.map fun k =>
    ⟨blockInsertLoading i k t, isRedOrdered_blockInsertLoading i k ht⟩

/-- **Proposition 5.5, `Fᵢ`-part, on standard modules** (Webster, arXiv:1309.3796v3): for every
colour `i` and red-ordered loading `t`, `Fᵢ S_t` has a filtration by the standard modules
`S_{t^{(k)}}`, `k = n, …, 0` from the top. -/
def BlackIndStandardFiltration {n : ℕ} (Λ : Fin n → I →₀ ℕ) : Prop :=
  ∀ (i : I) (ν : Multiset I) (t : Seq (stendhalWeight n ν)) (ht : IsRedOrdered t),
    HasFiltration (stdModule Q Λ ((Si i) + ν)) (blockInsertLabels i t ht)
      (blackIndT Q Λ i (stdModule Q Λ ν ⟨t, ht⟩))

/-! ### No red strands -/

omit [DecidableEq I] in
theorem ofFn_appendBlackLoading' {n : ℕ} (i : I) (ν : Multiset I)
    (s : Seq (stendhalWeight n ν)) :
    List.ofFn (appendBlackLoading i ν s).lbl = List.ofFn s.lbl ++ [.inl i] := by
  rw [appendBlackLoading, ofFn_seqCast', KLR.ofFn_append, ofFn_seqSingleton']

/-- With no red strands, `S_t = T e(t)`. -/
def leftStandardEquivZero (Λ : Fin 0 → I →₀ ℕ) {ν : Multiset I}
    (s : Seq (stendhalWeight 0 ν)) (hs : IsRedOrdered s) :
    lIdeal (seqIdem Q Λ s hs) ≃ₗ[TensorProductAlgebra k Q Λ ν] leftStandard Q Λ s hs :=
  (Submodule.quotEquivOfEqBot _ (by
    rw [leftUpper_eq_bot_of_zero, Submodule.comap_bot, Submodule.ker_subtype])).symm

/-- **Base of the induction**: with no red strands, `Fᵢ S_t ≅ S_{t i}`. -/
theorem blackIndStandardFiltration_zero (Λ : Fin 0 → I →₀ ℕ) :
    BlackIndStandardFiltration Q Λ := by
  intro i ν t ht
  have hlab : (⟨blockInsertLoading i 0 t, isRedOrdered_blockInsertLoading i 0 ht⟩ :
      {s : Seq (stendhalWeight 0 ((Si i) + ν)) // IsRedOrdered s}) =
      ⟨appendBlackLoading i ν t, appendBlackLoading_ordered i ν t ht⟩ :=
    Subtype.ext (seq_ext_ofFn' (by
      rw [ofFn_blockInsertLoading_zero_red, ofFn_appendBlackLoading']))
  refine HasFiltration.of_labels_eq (m := [⟨appendBlackLoading i ν t,
    appendBlackLoading_ordered i ν t ht⟩]) ?_ (by simp [blockInsertLabels, hlab])
  refine HasFiltration.single ?_
  exact ((Ind.mapEquiv (φ := appendBlackNU (Q := Q) (Λ := Λ) i ν)
      (leftStandardEquivZero Q Λ t ht).symm).trans
    ((indLIdealEquiv (appendBlackNU (Q := Q) (Λ := Λ) i ν)
      (isIdempotentElem_mk_e t ht)).trans
    (LinearEquiv.ofEq _ _ (congrArg lIdeal (appendBlack_mk_e Q Λ i ν t ht))))).trans
    (leftStandardEquivZero Q Λ _ _)

/-! ### The induction step -/

section Step

variable {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)

local notation "old" => Λ ∘ Fin.castSucc
local notation "aΛ" => fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j
local notation "Told" => TensorProductAlgebra k Q (old)
local notation "Cyc" => CycKLR k Q (aΛ)

omit [DecidableEq I] in
/-- A module over a finite-dimensional algebra that is finite-dimensional with its own
`k`-structure is finite-dimensional as a `KMod`. -/
theorem finite_kMod {A : Type} [Ring A] [Algebra k A] (X : ModuleCat.{0} A)
    [Module k X] [IsScalarTower k A X] [Module.Finite k X] :
    Module.Finite k (KMod (k := k) X) :=
  Module.Finite.equiv (R := k) (M := X)
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => (algebraMap_smul A c x).symm
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable {C : QuantumGroup.CartanDatum I}

/-- The two-piece layer `S(S_{t'} ⊠ R e(u))` has a finite-dimensional input module. -/
theorem finiteDimensional_tensorFactor_standard (hR : IsRouquierQ C Q) {θ β : Multiset I}
    (t : Seq (stendhalWeight ℓ θ)) (ht : IsRedOrdered t) (u : Seq β) :
    FiniteDimensional k
      (tensorFactor Q Λ (stdModule Q (old) θ ⟨t, ht⟩) (cycProj Q Λ β u)).carrier := by
  have := tensorProductAlgebra_finite (Q := Q) (old) θ hR
  have hCyc : Module.Finite k (Cyc β) := CycKLR.module_finite (ν := β) (Q := Q)
    (fun i j hij => by
      obtain ⟨c, hc, h⟩ := hR.polyInY_leading i j hij
      rw [h]
      exact hc.map Polynomial.C) (fun j => Polynomial.monic_X_pow (Λ (Fin.last ℓ) j))
  have : Module.Finite k (leftStandard Q (old) t ht) := finite_leftStandard t ht
  have : Module.Finite k (lIdeal (CycKLR.mk k Q (aΛ) β (e u))) :=
    Module.Finite.of_injective ((lIdeal (CycKLR.mk k Q (aΛ) β (e u))).subtype.restrictScalars k)
      Subtype.val_injective
  have := finite_kMod (k := k) (stdModule Q (old) θ ⟨t, ht⟩)
  have := finite_kMod (k := k) (cycProj Q Λ β u)
  change Module.Finite k (KMod (k := k) (stdModule Q (old) θ ⟨t, ht⟩) ⊗[k]
    KMod (k := k) (cycProj Q Λ β u))
  infer_instance

/-- The labels of the first layer: `(t'^{(k)}) λ_{ℓ+1} u = (t' λ_{ℓ+1} u)^{(k)}` for `k ≤ ℓ`. -/
theorem map_twoPieceLabel_blockInsertLabels (i : I) {θ β : Multiset I}
    (t : Seq (stendhalWeight ℓ θ)) (ht : IsRedOrdered t) (u : Seq β) :
    (blockInsertLabels i t ht).map (twoPieceLabel (add_assoc (Si i) θ β) u) =
      (List.range (ℓ + 1)).reverse.map fun k =>
        ⟨blockInsertLoading i k (twoPieceLoading θ β t u),
          isRedOrdered_blockInsertLoading i k (isRedOrdered_twoPieceLoading ht u)⟩ := by
  rw [blockInsertLabels, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  have hk' : k ≤ ℓ := by
    simp only [List.mem_reverse, List.mem_range] at hk
    omega
  exact Subtype.ext (blockInsertLoading_twoPiece_of_le i hk' t u).symm

include hQ in
/-- **Induction step** (Webster, arXiv:1309.3796v3, proof of Proposition 5.5, reduction to two
tensor factors): if `Fᵢ S_{t'}` is filtered by the `S_{t'^{(k)}}` for the first `ℓ` red strands,
then `Fᵢ S_t` is filtered by the `S_{t^{(k)}}`. Route hypothesis: `AllFiniteDeltaInjective`. -/
theorem blackIndStandardFiltration_succ (hR : IsRouquierQ C Q)
    (hall : AllFiniteDeltaInjective Q Λ hQ) (hold : BlackIndStandardFiltration Q (old)) :
    BlackIndStandardFiltration Q Λ := by
  intro i ν t ht
  obtain ⟨θ, β, h, t', u, ht', rfl⟩ := exists_twoPieceLoading_eq ht
  subst h
  set X : ModuleCat.{0} (Told θ) := stdModule Q (old) θ ⟨t', ht'⟩ with hX
  set Y : ModuleCat.{0} (Cyc β) := cycProj Q Λ β u with hY
  set c : StdLayer Q Λ (θ + β) := tensorLayer Q Λ rfl X Y with hc
  -- `S_t ≅ S(S_{t'} ⊠ R e(u))`
  obtain ⟨e₀⟩ := nonempty_stdLayerModule_twoPiece_equiv Q Λ hQ (rfl : θ + β = θ + β) ht' u
  -- the two-piece `Fᵢ`-filtration
  have hfin : c.IsFiniteDim Q Λ := finiteDimensional_tensorFactor_standard Q Λ hR t' ht' u
  have hF := hasFiltration_blackInd_stdLayer (hQ := hQ) i c (hall i c.θ c.β c.M hfin)
  have hF' : HasFiltration (stdLayerModule Q Λ hQ) (c.blackIndLayers Q Λ i)
      (blackIndT Q Λ i (stdModule Q Λ (θ + β) ⟨_, ht⟩)) :=
    hF.of_equiv (Ind.mapEquiv (φ := appendBlackNU (Q := Q) (Λ := Λ) i (θ + β)) e₀)
  -- the last layer
  have hlast : HasFiltration (stdModule Q Λ ((Si i) + (θ + β)))
      [⟨blockInsertLoading i (ℓ + 1) (twoPieceLoading θ β t' u),
        isRedOrdered_blockInsertLoading i (ℓ + 1) ht⟩] (stdLayerModule Q Λ hQ (c.last Q Λ i)) := by
    have hl : θ + ((Si i) + β) = (Si i) + (θ + β) := add_left_comm θ _ β
    obtain ⟨e₁⟩ := nonempty_stdLayerModule_twoPiece_equiv Q Λ hQ hl ht'
      (Seq.cast (add_comm β (Si i)) (u.append default))
    have e₂ : stdLayerModule Q Λ hQ (c.last Q Λ i) ≃ₗ[TensorProductAlgebra k Q Λ
        ((Si i) + (θ + β))] stdLayerModule Q Λ hQ (tensorLayer Q Λ hl X
          (cycProj Q Λ ((Si i) + β) (Seq.cast (add_comm β (Si i)) (u.append default)))) :=
      stdLayerEquiv Q Λ hQ hl ((lastIndTensorEquiv Q Λ i X Y).trans
        (tensorFactorCongr Q Λ (LinearEquiv.refl _ _) (cycProjIndEquiv Q Λ i β u)))
    refine HasFiltration.single (e₂.trans (e₁.trans (LinearEquiv.ofEq _ _ ?_)))
    rw [blockInsertLoading_twoPiece_last]
  -- the first layer
  have hfirst : HasFiltration (stdModule Q Λ ((Si i) + (θ + β)))
      ((List.range (ℓ + 1)).reverse.map fun k =>
        ⟨blockInsertLoading i k (twoPieceLoading θ β t' u),
          isRedOrdered_blockInsertLoading i k ht⟩)
      (stdLayerModule Q Λ hQ (c.first Q Λ i)) := by
    have hl : ((Si i) + θ) + β = (Si i) + (θ + β) := add_assoc _ θ β
    have e₂ : stdLayerModule Q Λ hQ (c.first Q Λ i) ≃ₗ[TensorProductAlgebra k Q Λ
        ((Si i) + (θ + β))] stdLayerModule Q Λ hQ (tensorLayer Q Λ hl
          (oldIndModule Q Λ i X) Y) :=
      stdLayerEquiv Q Λ hQ hl (firstIndTensorEquiv Q Λ i X Y)
    have h₁ := hasFiltration_tensorLayer Q Λ hQ hl Y (hold i θ t' ht')
    have h₂ : HasFiltration (fun d => stdModule Q Λ _ (twoPieceLabel hl u d))
        (blockInsertLabels i t' ht') (stdLayerModule Q Λ hQ (tensorLayer Q Λ hl
          (oldIndModule Q Λ i X) Y)) :=
      h₁.mono fun d => nonempty_stdLayerModule_twoPiece_equiv Q Λ hQ hl d.2 u
    exact ((HasFiltration.relabel (L := stdModule Q Λ _) (twoPieceLabel hl u) h₂).of_equiv
      e₂.symm).of_labels_eq (map_twoPieceLabel_blockInsertLabels Q Λ i t' ht' u)
  -- assemble
  have := hF'.bind_of_mem (L' := stdModule Q Λ ((Si i) + (θ + β)))
    (M := fun d => if d = c.last Q Λ i then
      [⟨blockInsertLoading i (ℓ + 1) (twoPieceLoading θ β t' u),
        isRedOrdered_blockInsertLoading i (ℓ + 1) ht⟩]
      else (List.range (ℓ + 1)).reverse.map fun k =>
        ⟨blockInsertLoading i k (twoPieceLoading θ β t' u),
          isRedOrdered_blockInsertLoading i k ht⟩) (by
    intro d hd
    simp only [StdLayer.blackIndLayers, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl
    · rw [if_pos rfl]
      exact hlast
    · by_cases hdl : c.first Q Λ i = c.last Q Λ i
      · exact absurd (congrArg StdLayer.θ hdl) (by
          simp only [StdLayer.first, StdLayer.last]
          intro h'
          have := congrArg Multiset.card h'
          simp at this)
      · rw [if_neg hdl]
        exact hfirst)
  refine this.of_labels_eq ?_
  have hne : ¬ c.first Q Λ i = c.last Q Λ i := fun h' => by
    have := congrArg (fun d => Multiset.card d.θ) h'
    simp [StdLayer.first, StdLayer.last] at this
  simp only [StdLayer.blackIndLayers, List.flatMap_cons, List.flatMap_nil, if_pos rfl,
    if_neg hne, List.append_nil, blockInsertLabels]
  rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.map_cons]
  rfl

end Step

variable {C : QuantumGroup.CartanDatum I}

/-- **Proposition 5.5, `Fᵢ`-part, on standard modules** (Webster, arXiv:1309.3796v3, §5.1;
the filtration of `Fᵢ S` used in the proof of Proposition 5.6): for every number of red strands,
every colour `i` and every red-ordered loading `t`, `Fᵢ S_t` has a filtration whose
subquotients, from the top, are the standard modules `S_{t^{(n)}}, …, S_{t^{(0)}}`. Route
hypothesis: `AllFiniteDeltaInjective` (the two-piece `Fᵢ`-part for finite-dimensional inputs)
for every sequence of highest weights. -/
theorem blackIndStandardFiltration (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ) :
    ∀ {n : ℕ} (Λ' : Fin n → I →₀ ℕ), BlackIndStandardFiltration Q Λ'
  | 0, Λ' => blackIndStandardFiltration_zero Q Λ'
  | n + 1, Λ' => blackIndStandardFiltration_succ Q Λ' hQ hR (hall n Λ')
      (blackIndStandardFiltration hQ hR hall (Λ' ∘ Fin.castSucc))

end Categorification.Stendhal
