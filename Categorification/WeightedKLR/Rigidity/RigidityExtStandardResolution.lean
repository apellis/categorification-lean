/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtCone
import Categorification.WeightedKLR.Rigidity.RigidityExtIndResolution
import Categorification.WeightedKLR.Rigidity.RigidityExtLoadingWord
import Categorification.WeightedKLR.RedStrands.ParabolicStandardTensorProj
import Categorification.WeightedKLR.RedStrands.ParabolicStandardFiniteFiltration
import Categorification.WeightedKLR.RedStrands.StandardProjectiveDimension

/-!
# Projective resolutions of the standard modules (Webster, Proposition 7.6)

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Proposition 7.6 and its proof. For `X ≅ T^{λ'} e(t)` and a black word `w`, the standardization
`S(X ⊠ R^{λ_ℓ} e(w))` has a projective resolution, built by induction on `w`. For `w = j :: w'`,
the short exact sequence (7.25)

`0 → S(₁Fⱼ N) → Fⱼ S(N) → S(₂Fⱼ N) → 0`, `N = X ⊠ R e(w')`,

has outer terms `S(Fⱼ X ⊠ R e(w'))` and `S(X ⊠ R e(j :: w'))`. Induction along a black strand at
the right has projective corner, so it maps a resolution of `S(N)` to a resolution of `Fⱼ S(N)`;
the cone of a lift of the left map resolves the right term.

The injectivity of the left map of (7.25) is the route hypothesis `AllFiniteDeltaInjective`,
which holds at the standard Khovanov–Lauda parameters (`allFiniteDeltaInjective_std`).

## Main definitions and results

* `Stendhal.blackInd_shortExact`: (7.25) for a standard layer, as a short exact sequence.
* `Stendhal.stdResolution`: the resolution.
* `Stendhal.loadingSum_stdResolution`: its terms are sums of projectives `T^λ e(s)`, with the
  words `termWords`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra InductionAlong MulOpposite ModuleFiltration
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "old" => Λ ∘ Fin.castSucc
local notation "aΛ" => fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j
local notation "Told" => TensorProductAlgebra k Q (old)
local notation "Cyc" => CycKLR k Q (aΛ)

variable (hQ : KLRSymm Q) (i : I)

/-! ### The short exact sequence (7.25) of a standard layer -/

/-- A linear isomorphism of modules, as a morphism of `ModuleCat`. -/
abbrev homOfEquiv {R : Type} [Ring R] {X Y : ModuleCat.{0} R} (e : X ≃ₗ[R] Y) : X ⟶ Y :=
  ModuleCat.ofHom e.toLinearMap

section Canonical

variable (θ β : Multiset I) (M : FactorModule Q Λ θ β)

/-- `S(₁Fᵢ N)` is the module `FirstIndStandardT`. -/
def firstStdEquiv :
    stdLayerModule Q Λ hQ (StdLayer.first Q Λ i ⟨θ, β, rfl, M⟩) ≃ₗ[TensorProductAlgebra k Q Λ
      ((Si i) + (θ + β))] ModuleCat.of (TensorProductAlgebra k Q Λ ((Si i) + (θ + β))) (FirstIndStandardT Q Λ i θ β M.carrier hQ) :=
  { toFun := fun x => x
    invFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- `S(₂Fᵢ N)` is the module `LastIndStandardT`. -/
def lastStdEquiv :
    ModuleCat.of (TensorProductAlgebra k Q Λ ((Si i) + (θ + β))) (LastIndStandardT Q Λ i θ β M.carrier hQ) ≃ₗ[TensorProductAlgebra k Q Λ
      ((Si i) + (θ + β))] stdLayerModule Q Λ hQ (StdLayer.last Q Λ i ⟨θ, β, rfl, M⟩) :=
  { toFun := fun x => x
    invFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- `S(N)` is the module `ParabolicStandardT`. -/
def layerStdEquiv :
    stdLayerModule Q Λ hQ ⟨θ, β, rfl, M⟩ ≃ₗ[TensorProductAlgebra k Q Λ (θ + β)]
      ParabolicStandardT Q Λ θ β M.carrier hQ :=
  { toFun := fun x => x
    invFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- `Fᵢ S(N)` is the module `LastIndF`. -/
def blackIndStdEquiv :
    ModuleCat.of (TensorProductAlgebra k Q Λ ((Si i) + (θ + β))) (LastIndF Q Λ i θ β M.carrier hQ) ≃ₗ[TensorProductAlgebra k Q Λ
      ((Si i) + (θ + β))] blackIndModule Q Λ i (stdLayerModule Q Λ hQ ⟨θ, β, rfl, M⟩) :=
  (Ind.mapEquiv (φ := appendBlackNU (Q := Q) (Λ := Λ) i (θ + β))
    (layerStdEquiv Q Λ hQ θ β M)).symm

end Canonical

/-- The left map `S(₁Fᵢ N) → Fᵢ S(N)` of (7.25). -/
def blackIndFirstMap {ν : Multiset I} (c : StdLayer Q Λ ν) :
    stdLayerModule Q Λ hQ (c.first Q Λ i) ⟶ blackIndModule Q Λ i (stdLayerModule Q Λ hQ c) := by
  obtain ⟨θ, β, h, M⟩ := c
  subst h
  exact homOfEquiv (firstStdEquiv Q Λ hQ i θ β M) ≫
    ModuleCat.ofHom (firstIndDeltaT Q Λ i θ β M.carrier hQ) ≫
    homOfEquiv (blackIndStdEquiv Q Λ hQ i θ β M)

/-- The right map `Fᵢ S(N) → S(₂Fᵢ N)` of (7.25). -/
def blackIndLastMap {ν : Multiset I} (c : StdLayer Q Λ ν) :
    blackIndModule Q Λ i (stdLayerModule Q Λ hQ c) ⟶ stdLayerModule Q Λ hQ (c.last Q Λ i) := by
  obtain ⟨θ, β, h, M⟩ := c
  subst h
  exact homOfEquiv (blackIndStdEquiv Q Λ hQ i θ β M).symm ≫
    ModuleCat.ofHom (lastIndQuotientMap Q Λ i θ β M.carrier hQ) ≫
    homOfEquiv (lastStdEquiv Q Λ hQ i θ β M)

theorem blackIndFirstMap_mk (θ β : Multiset I) (M : FactorModule Q Λ θ β) :
    blackIndFirstMap Q Λ hQ i ⟨θ, β, rfl, M⟩ = homOfEquiv (firstStdEquiv Q Λ hQ i θ β M) ≫
      ModuleCat.ofHom (firstIndDeltaT Q Λ i θ β M.carrier hQ) ≫
      homOfEquiv (blackIndStdEquiv Q Λ hQ i θ β M) := rfl

theorem blackIndLastMap_mk (θ β : Multiset I) (M : FactorModule Q Λ θ β) :
    blackIndLastMap Q Λ hQ i ⟨θ, β, rfl, M⟩ = homOfEquiv (blackIndStdEquiv Q Λ hQ i θ β M).symm ≫
      ModuleCat.ofHom (lastIndQuotientMap Q Λ i θ β M.carrier hQ) ≫
      homOfEquiv (lastStdEquiv Q Λ hQ i θ β M) := rfl

/-- **The short exact sequence (7.25)** (Webster, arXiv:1309.3796v3, Proposition 5.5, `F`-part,
used in the proof of Proposition 7.6): given injectivity of `δ₁` for the layer (the route
hypothesis `FirstIndDeltaInjective`), `0 → S(₁Fᵢ N) → Fᵢ S(N) → S(₂Fᵢ N) → 0` is exact. -/
theorem blackInd_shortExact {ν : Multiset I} (c : StdLayer Q Λ ν)
    (hc : StdLayer.DeltaInjective Q Λ hQ i c) :
    Function.Injective (blackIndFirstMap Q Λ hQ i c).hom ∧
      Function.Exact (blackIndFirstMap Q Λ hQ i c).hom (blackIndLastMap Q Λ hQ i c).hom ∧
      Function.Surjective (blackIndLastMap Q Λ hQ i c).hom := by
  obtain ⟨θ, β, h, M⟩ := c
  subst h
  obtain ⟨hinj, hex, hsurj⟩ := firstIndDeltaT_shortExact Q Λ i θ β M.carrier hQ hc
  rw [blackIndFirstMap_mk, blackIndLastMap_mk]
  refine ⟨(blackIndStdEquiv Q Λ hQ i θ β M).injective.comp
      (hinj.comp (firstStdEquiv Q Λ hQ i θ β M).injective), ?_,
    (lastStdEquiv Q Λ hQ i θ β M).surjective.comp
      (hsurj.comp (blackIndStdEquiv Q Λ hQ i θ β M).symm.surjective)⟩
  refine (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := (firstStdEquiv Q Λ hQ i θ β M).symm) (e₂ := blackIndStdEquiv Q Λ hQ i θ β M)
    (e₃ := lastStdEquiv Q Λ hQ i θ β M)
    (f₁₂ := firstIndDeltaT Q Λ i θ β M.carrier hQ)
    (f₂₃ := lastIndQuotientMap Q Λ i θ β M.carrier hQ) ?_ ?_).2 hex
  · ext x; rfl
  · ext x
    exact congrArg (fun y => (lastStdEquiv Q Λ hQ i θ β M)
      (lastIndQuotientMap Q Λ i θ β M.carrier hQ y))
      ((blackIndStdEquiv Q Λ hQ i θ β M).symm_apply_apply x)

/-! ### Loading sums -/

section LoadingSum

variable {Q Λ}

/-- `M` is a direct sum of the projectives `T^λ e(s)`, one for each word in `L`: there are
red-ordered loadings `s_a` whose words are the elements of `L` (with multiplicity) and
`M ≅ ⊕_a T^λ e(s_a)`. -/
def LoadingSum {ν : Multiset I} (M : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))
    (L : Multiset (List (I ⊕ Fin (ℓ + 1)))) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (s : ι → Seq (stendhalWeight (ℓ + 1) ν))
    (hs : ∀ a, IsRedOrdered (s a)),
    Finset.univ.val.map (fun a => (s a).word) = L ∧
      Nonempty (M ≃ₗ[TensorProductAlgebra k Q Λ ν] (∀ a, loadingProj Q Λ (s a) (hs a)))

variable {ν : Multiset I}

theorem LoadingSum.of_equiv {M M' : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)}
    {L : Multiset (List (I ⊕ Fin (ℓ + 1)))} (e : M ≃ₗ[TensorProductAlgebra k Q Λ ν] M')
    (h : LoadingSum M' L) : LoadingSum M L := by
  obtain ⟨ι, _, s, hs, hL, ⟨f⟩⟩ := h
  exact ⟨ι, inferInstance, s, hs, hL, ⟨e.trans f⟩⟩

theorem LoadingSum.single {M : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)}
    (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s)
    (e : M ≃ₗ[TensorProductAlgebra k Q Λ ν] loadingProj Q Λ s hs) :
    LoadingSum M {s.word} :=
  ⟨Unit, inferInstance, fun _ => s, fun _ => hs, rfl,
    ⟨e.trans (LinearEquiv.funUnique Unit (TensorProductAlgebra k Q Λ ν) _).symm⟩⟩

theorem LoadingSum.zero {M : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)} [Subsingleton M] :
    LoadingSum M 0 :=
  ⟨Empty, inferInstance, Empty.elim, fun a => a.elim, rfl, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩

theorem LoadingSum.prod {M N : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)}
    {L₁ L₂ : Multiset (List (I ⊕ Fin (ℓ + 1)))} (h₁ : LoadingSum M L₁) (h₂ : LoadingSum N L₂) :
    LoadingSum (ModuleCat.of (TensorProductAlgebra k Q Λ ν) (M × N)) (L₁ + L₂) := by
  obtain ⟨ι₁, _, s₁, hs₁, hL₁, ⟨f₁⟩⟩ := h₁
  obtain ⟨ι₂, _, s₂, hs₂, hL₂, ⟨f₂⟩⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim s₁ s₂, fun | .inl a => hs₁ a | .inr a => hs₂ a, ?_, ⟨?_⟩⟩
  · rw [← hL₁, ← hL₂, ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.disjSum,
      Multiset.map_add, Multiset.map_map, Multiset.map_map]
    rfl
  · exact (f₁.prodCongr f₂).trans
      (LinearEquiv.sumPiEquivProdPi (TensorProductAlgebra k Q Λ ν) ι₁ ι₂
        (fun a => loadingProj Q Λ (Sum.elim s₁ s₂ a) (match a with
          | .inl a => hs₁ a | .inr a => hs₂ a))).symm

theorem LoadingSum.blackInd (j : I) {M : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)}
    {L : Multiset (List (I ⊕ Fin (ℓ + 1)))} (h : LoadingSum M L) :
    LoadingSum (blackIndModule Q Λ j M) (L.map (· ++ [Sum.inl j])) := by
  obtain ⟨ι, _, s, hs, hL, ⟨f⟩⟩ := h
  refine ⟨ι, inferInstance, fun a => appendBlackLoading j ν (s a),
    fun a => appendBlackLoading_ordered j ν (s a) (hs a), ?_, ⟨?_⟩⟩
  · rw [← hL, Multiset.map_map]
    congr 1
    funext a
    exact word_appendBlackLoading j ν (s a)
  · exact (Ind.mapEquiv (φ := appendBlackNU (Q := Q) (Λ := Λ) j ν) f).trans
      ((indPiIso (appendBlackNU (Q := Q) (Λ := Λ) j ν)
        (fun a => loadingProj Q Λ (s a) (hs a))).toLinearEquiv.trans
        (LinearEquiv.piCongrRight fun a => (loadingProjBlackEquiv Q Λ j (s a) (hs a)).symm))

end LoadingSum

/-! ### The first and second factors -/

/-- `X ≅ T^{λ'} e(t)` for some red-ordered loading `t` of the first `ℓ` red strands. -/
def IsLoadingProj {θ : Multiset I} (X : ModuleCat.{0} (Told θ)) : Prop :=
  ∃ (t : Seq (stendhalWeight ℓ θ)) (ht : IsRedOrdered t), Nonempty (X ≃ₗ[Told θ] oldProj Q Λ θ t ht)

variable {Q Λ} in
theorem IsLoadingProj.oldInd {θ : Multiset I} {X : ModuleCat.{0} (Told θ)}
    (h : IsLoadingProj Q Λ X) : IsLoadingProj Q Λ (oldIndModule Q Λ i X) := by
  obtain ⟨t, ht, ⟨f⟩⟩ := h
  exact ⟨_, _, ⟨(Ind.mapEquiv (φ := appendBlackNU (Q := Q) (Λ := old) i θ) f).trans
    (oldProjIndEquiv Q Λ i θ t ht)⟩⟩

/-- The projective `R^{λ_ℓ} e(w)` of a black word `w` (the last letter leftmost), built by
`Fᵢ` from `R^{λ_ℓ}_0`. -/
def cycWord : (w : List I) → ModuleCat.{0} (Cyc (wordWt w 0))
  | [] => ModuleCat.of (Cyc 0) (Cyc 0)
  | j :: w => cycIndModule Q Λ j (cycWord w)

theorem cycGen_cycWord : (w : List I) → CycGen Q Λ (wordWt w 0) (cycWord Q Λ w)
  | [] => .base
  | j :: w => .ind j _ (cycGen_cycWord w)

/-- A module isomorphic to a corner `A e` of a finite-dimensional algebra is finite-dimensional. -/
theorem finiteDimensional_kMod_of_equiv {A : Type} [Ring A] [Algebra k A] [Module.Finite k A]
    {e : A} (he : IsIdempotentElem e) (X : ModuleCat.{0} A) (f : X ≃ₗ[A] lIdeal e) :
    FiniteDimensional k (KMod (k := k) X) := by
  have : Module.Finite A (lIdeal e) := Module.Finite.of_surjective
    ({ toFun := fun b => ⟨b * e, by rw [mem_lIdeal, mul_assoc, he.eq]⟩
       map_add' := fun a b => Subtype.ext (add_mul a b e)
       map_smul' := fun a b => Subtype.ext (mul_assoc a b e) } : A →ₗ[A] lIdeal e)
    (fun z => ⟨z.1, Subtype.ext z.2⟩)
  have : Module.Finite A (KMod (k := k) X) := Module.Finite.equiv f.symm
  exact Module.Finite.trans A _

variable {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)

include hR in
theorem finiteDimensional_tensorFactor {θ β : Multiset I} {X : ModuleCat.{0} (Told θ)}
    (hX : IsLoadingProj Q Λ X) {Y : ModuleCat.{0} (Cyc β)} (hY : CycGen Q Λ β Y) :
    FiniteDimensional k (tensorFactor Q Λ X Y).carrier := by
  obtain ⟨t, ht, ⟨f⟩⟩ := hX
  obtain ⟨u, ⟨g⟩⟩ := hY.exists_equiv
  have := tensorProductAlgebra_finite (Q := Q) (old) θ hR
  have := CycKLR.module_finite (ν := β) (Q := Q) (fun i j hij => by
    obtain ⟨c, hc, h⟩ := hR.polyInY_leading i j hij
    rw [h]
    exact hc.map Polynomial.C) (fun j => Polynomial.monic_X_pow (Λ (Fin.last ℓ) j))
  have := finiteDimensional_kMod_of_equiv (k := k) (isIdempotentElem_mk_e t ht) X f
  have := finiteDimensional_kMod_of_equiv (k := k) (isIdempotentElem_cyc_e Q Λ β u) Y g
  exact inferInstanceAs (FiniteDimensional k (KMod (k := k) X ⊗[k] KMod (k := k) Y))

/-! ### The standardizations `S(X ⊠ Y)` -/

/-- The standardization `S(X ⊠ Y)` as a module over `T^λ_ν`, for a split `θ + β = ν`. -/
abbrev tensorStd {θ β ν : Multiset I} (h : θ + β = ν) (X : ModuleCat.{0} (Told θ))
    (Y : ModuleCat.{0} (Cyc β)) : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν) :=
  stdLayerModule Q Λ hQ (tensorLayer Q Λ h X Y)

/-- **The base of Proposition 7.6**: with empty last block, `S(T^{λ'} e(t) ⊠ R^{λ_ℓ}_0)` is the
projective `T^λ e(t, λ_ℓ)` (Proposition 4.18). -/
theorem exists_tensorStd_zero_equiv {θ : Multiset I} (X : ModuleCat.{0} (Told θ))
    (t : Seq (stendhalWeight ℓ θ)) (ht : IsRedOrdered t) (f : X ≃ₗ[Told θ] oldProj Q Λ θ t ht) :
    ∃ (s : Seq (stendhalWeight (ℓ + 1) (θ + 0))) (hs : IsRedOrdered s),
      s.word = t.word.map (addRedColor ℓ) ++ [Sum.inr (Fin.last ℓ)] ∧
      Nonempty (tensorStd Q Λ hQ (rfl : θ + 0 = θ + 0) X (cycWord Q Λ []) ≃ₗ[
        TensorProductAlgebra k Q Λ (θ + 0)] loadingProj Q Λ s hs) := by
  let s₀ : Seq (stendhalWeight ℓ (θ + 0)) :=
    Seq.cast (congrArg (stendhalWeight ℓ) (add_zero θ).symm) t
  have hs₀ : IsRedOrdered s₀ := (isRedOrdered_cast _ t).2 ht
  obtain ⟨t', ht', ht't, ⟨e'⟩⟩ := nonempty_zeroRestrict_redFactorModule_equiv Q Λ θ s₀ hs₀
  have htt : t' = t := by rw [ht't]; rfl
  subst htt
  let F : (tensorFactor Q Λ X (cycWord Q Λ [])).carrier ≃ₗ[parabolicFactorAlgebra Q Λ θ 0]
      (redFactorModule Q Λ θ s₀ hs₀).carrier :=
    (tensorFactorCongr Q Λ (f.trans e'.symm) (LinearEquiv.refl _ _)).trans
      (zeroTensorEquiv Q Λ (redFactorModule Q Λ θ s₀ hs₀))
  refine ⟨appendRedLoading s₀, (appendRedLoading_ordered_iff s₀).2 hs₀, ?_,
    ⟨(stdLayerEquiv Q Λ hQ rfl F).trans (loadingProjRedEquiv Q Λ θ hQ s₀ hs₀).symm⟩⟩
  rw [word_appendRedLoading, Seq.word_cast]

/-- Transport of a resolution of `S(X ⊠ Y)` between two splits `θ + β = ν`, `θ + β = ν'`. -/
def stdTransport {θ β ν ν' : Multiset I} (h : θ + β = ν) (h' : θ + β = ν')
    {X : ModuleCat.{0} (Told θ)} {Y : ModuleCat.{0} (Cyc β)}
    (P : ProjectiveResolution (tensorStd Q Λ hQ h X Y)) :
    ProjectiveResolution (tensorStd Q Λ hQ h' X Y) := by
  subst h; subst h'; exact P

theorem loadingSum_stdTransport {θ β ν ν' : Multiset I} (h : θ + β = ν) (h' : θ + β = ν')
    {X : ModuleCat.{0} (Told θ)} {Y : ModuleCat.{0} (Cyc β)}
    (P : ProjectiveResolution (tensorStd Q Λ hQ h X Y)) (n : ℕ)
    (L : Multiset (List (I ⊕ Fin (ℓ + 1)))) (hP : LoadingSum (P.complex.X n) L) :
    LoadingSum ((stdTransport Q Λ hQ h h' P).complex.X n) L := by
  subst h; subst h'; exact hP

/-! ### The resolution -/

variable (hall : AllFiniteDeltaInjective Q Λ hQ)

/-- The layer `S(X ⊠ R e(w))` at the split `θ + wordWt w 0`. -/
abbrev stepLayer (w : List I) {θ : Multiset I} (X : ModuleCat.{0} (Told θ)) :
    StdLayer Q Λ (θ + wordWt w 0) :=
  tensorLayer Q Λ rfl X (cycWord Q Λ w)

/-- The step `w ↦ j :: w` of the resolution of Proposition 7.6: from resolutions of
`S(Fⱼ X ⊠ R e(w))` and of `S(X ⊠ R e(w))`, the cone of a lift of the left map of (7.25)
resolves `S(X ⊠ R e(j :: w))`. -/
def stdResolutionStep (j : I) (w : List I) {θ : Multiset I} (X : ModuleCat.{0} (Told θ))
    (hX : IsLoadingProj Q Λ X) {ν : Multiset I} (h : θ + ((Si j) + wordWt w 0) = ν)
    (PA : ProjectiveResolution (tensorStd Q Λ hQ ((stepLayer Q Λ w X).first Q Λ j).h
      (oldIndModule Q Λ j X) (cycWord Q Λ w)))
    (PB₀ : ProjectiveResolution (stdLayerModule Q Λ hQ (stepLayer Q Λ w X))) :
    ProjectiveResolution (tensorStd Q Λ hQ h X (cycIndModule Q Λ j (cycWord Q Λ w))) := by
  have hc : StdLayer.DeltaInjective Q Λ hQ j (stepLayer Q Λ w X) :=
    hall j θ (wordWt w 0) _ (finiteDimensional_tensorFactor Q Λ hR hX (cycGen_cycWord Q Λ w))
  have hses := blackInd_shortExact Q Λ hQ j (stepLayer Q Λ w X) hc
  let e₁ := stdLayerEquiv Q Λ hQ ((stepLayer Q Λ w X).first Q Λ j).h
    (M := tensorFactor Q Λ (oldIndModule Q Λ j X) (cycWord Q Λ w))
    (M' := ((stepLayer Q Λ w X).first Q Λ j).M)
    (firstIndTensorEquiv Q Λ j X (cycWord Q Λ w)).symm
  let e₂ := stdLayerEquiv Q Λ hQ ((stepLayer Q Λ w X).last Q Λ j).h
    (M := ((stepLayer Q Λ w X).last Q Λ j).M)
    (M' := tensorFactor Q Λ X (cycIndModule Q Λ j (cycWord Q Λ w)))
    (lastIndTensorEquiv Q Λ j X (cycWord Q Λ w))
  let f : tensorStd Q Λ hQ ((stepLayer Q Λ w X).first Q Λ j).h (oldIndModule Q Λ j X)
      (cycWord Q Λ w) ⟶ blackIndModule Q Λ j (stdLayerModule Q Λ hQ (stepLayer Q Λ w X)) :=
    homOfEquiv e₁ ≫ blackIndFirstMap Q Λ hQ j (stepLayer Q Λ w X)
  let g : blackIndModule Q Λ j (stdLayerModule Q Λ hQ (stepLayer Q Λ w X)) ⟶
      tensorStd Q Λ hQ ((stepLayer Q Λ w X).last Q Λ j).h X
        (cycIndModule Q Λ j (cycWord Q Λ w)) :=
    blackIndLastMap Q Λ hQ j (stepLayer Q Λ w X) ≫ homOfEquiv e₂
  have hf : Function.Injective f := hses.1.comp e₁.injective
  have hfg : Function.Exact f g :=
    (Function.Exact.iff_of_ladder_linearEquiv (e₁ := e₁.symm)
      (e₂ := LinearEquiv.refl _ _) (e₃ := e₂)
      (f₁₂ := (blackIndFirstMap Q Λ hQ j (stepLayer Q Λ w X)).hom)
      (f₂₃ := (blackIndLastMap Q Λ hQ j (stepLayer Q Λ w X)).hom) (g₁₂ := f.hom) (g₂₃ := g.hom)
      (LinearMap.ext fun x => congrArg (blackIndFirstMap Q Λ hQ j (stepLayer Q Λ w X)).hom
        (e₁.apply_symm_apply x))
      (LinearMap.ext fun x => rfl)).2 hses.2.1
  have hg : Function.Surjective g := e₂.surjective.comp hses.2.2
  let PB : ProjectiveResolution (blackIndModule Q Λ j
      (stdLayerModule Q Λ hQ (stepLayer Q Λ w X))) :=
    @InductionAlong.indResolutionOf _ _ _ _ (appendBlackNU (Q := Q) (Λ := Λ) j (θ + wordWt w 0))
      (projective_appendBlackCorner (Q := Q) (Λ := Λ) j (θ + wordWt w 0) C hR) _ PB₀
  exact stdTransport Q Λ hQ ((stepLayer Q Λ w X).last Q Λ j).h h
    (ModuleCat.ProjectiveResolution.cone f g PA PB hf hfg hg)

/-- **The projective resolution of Proposition 7.6** (Webster, arXiv:1309.3796v3, §7.1) of the
standardization `S(X ⊠ R^{λ_ℓ} e(w))`, for `X ≅ T^{λ'} e(t)`: by induction on `w`, as the cone of
a lift of the left map of (7.25) to the resolutions of `S(Fᵢ X ⊠ R e(w'))` and of
`Fᵢ S(X ⊠ R e(w'))`, for `w = i :: w'` (`stdResolutionStep`). -/
def stdResolution : (w : List I) → {θ : Multiset I} → (X : ModuleCat.{0} (Told θ)) →
    IsLoadingProj Q Λ X → {ν : Multiset I} → (h : θ + wordWt w 0 = ν) →
    ProjectiveResolution (tensorStd Q Λ hQ h X (cycWord Q Λ w))
  | [], θ, X, hX, ν, h => by
      have : Projective (tensorStd Q Λ hQ h X (cycWord Q Λ [])) := by
        obtain ⟨t, ht, ⟨f⟩⟩ := hX
        subst h
        obtain ⟨s, hs, -, ⟨e⟩⟩ := exists_tensorStd_zero_equiv Q Λ hQ X t ht f
        have := projective_lIdeal_seqIdem Q Λ s hs
        exact Projective.of_iso e.toModuleIso.symm this
      exact ProjectiveResolution.self _
  | j :: w, θ, X, hX, ν, h =>
      stdResolutionStep Q Λ hQ hR hall j w X hX h
        (stdResolution w (oldIndModule Q Λ j X) (hX.oldInd j) _)
        (stdResolution w X hX rfl)

/-! ### The terms of the resolution -/

/-- The words of the loadings of the projective terms in homological degree `n` of the
resolution of `S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(w))`, where `t` has word `t`: for `w = []` the single
word `t λ_ℓ` in degree `0`; for `w = j :: w'`, the words of degree `n` for `w'` with `j`
appended (the strand `j` stays right of the last red strand), and the words of degree `n - 1` for
`w'` with `t` replaced by `t j` (the strand `j` moves left of the last red strand). -/
def termWords (t : List (I ⊕ Fin (ℓ + 1))) : List I → ℕ → Multiset (List (I ⊕ Fin (ℓ + 1)))
  | [], 0 => {t ++ [Sum.inr (Fin.last ℓ)]}
  | [], _ + 1 => 0
  | j :: w, 0 => (termWords t w 0).map (· ++ [Sum.inl j])
  | j :: w, n + 1 =>
      (termWords t w (n + 1)).map (· ++ [Sum.inl j]) + termWords (t ++ [Sum.inl j]) w n

/-- **The terms of the resolution of Proposition 7.6**: in degree `n`, the resolution of
`S(X ⊠ R^{λ_ℓ} e(w))`, `X ≅ T^{λ'} e(t)`, is a direct sum of projectives `T^λ e(s)`, one for
each word of `termWords t w n`. -/
theorem loadingSum_stdResolution : ∀ (w : List I) {θ : Multiset I} (X : ModuleCat.{0} (Told θ))
    (hX : IsLoadingProj Q Λ X) {ν : Multiset I} (h : θ + wordWt w 0 = ν)
    (t : Seq (stendhalWeight ℓ θ)) (ht : IsRedOrdered t) (_f : X ≃ₗ[Told θ] oldProj Q Λ θ t ht)
    (n : ℕ), LoadingSum ((stdResolution Q Λ hQ hR hall w X hX h).complex.X n)
      (termWords (t.word.map (addRedColor ℓ)) w n)
  | [], θ, X, hX, ν, h, t, ht, f, n => by
      subst h
      cases n with
      | zero =>
        obtain ⟨s, hs, hw, ⟨e⟩⟩ := exists_tensorStd_zero_equiv Q Λ hQ X t ht f
        have := LoadingSum.single s hs
          ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 _).toLinearEquiv.trans e)
        rw [hw] at this
        exact this
      | succ n =>
        have : Subsingleton ((stdResolution Q Λ hQ hR hall [] X hX
            (rfl : θ + wordWt [] 0 = _)).complex.X (n + 1)) :=
          ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _
            (by simp))
        exact LoadingSum.zero
  | j :: w, θ, X, hX, ν, h, t, ht, f, n => by
      rw [stdResolution]
      apply loadingSum_stdTransport
      cases n with
      | zero =>
        exact (loadingSum_stdResolution w X hX rfl t ht f 0).blackInd j
      | succ n =>
        have h₂ := loadingSum_stdResolution w (oldIndModule Q Λ j X) (hX.oldInd j)
          (show (Si j) + θ + wordWt w 0 = (Si j) + (θ + wordWt w 0) by rw [add_assoc])
          (appendBlackLoading j θ t) (appendBlackLoading_ordered j θ t ht)
          ((Ind.mapEquiv (φ := appendBlackNU (Q := Q) (Λ := old) j θ) f).trans
            (oldProjIndEquiv Q Λ j θ t ht)) n
        rw [word_appendBlackLoading, List.map_append] at h₂
        exact ((loadingSum_stdResolution w X hX rfl t ht f (n + 1)).blackInd j).prod h₂

end Categorification.Stendhal
