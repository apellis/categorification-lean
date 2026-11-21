/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardProjectiveFiltration
import Categorification.Algebra.InductionAlongTensor
import Categorification.WeightedKLR.RedStrands.ParabolicStandardExact

/-!
# Standard layers of tensor form and `Fᵢ`

The recursion in the proof of Proposition 5.21 of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, filters a projective over `T^λ` by
standardizations `S(X ⊠ Y)` of external tensor products of a module `X` over `T^{λ'}` (the
algebra of the first `ℓ` red strands) and a module `Y` over the cyclotomic quotient `R^{λ_ℓ}`.
This file shows that the two layers of `Fᵢ S(X ⊠ Y)` (Proposition 5.5, `F`-part,
`hasFiltration_blackInd_stdLayer`) again have this form, `S(Fᵢ X ⊠ Y)` and `S(X ⊠ Fᵢ Y)`.

## Main definitions and results

* `tensorFactor`, `tensorLayer`: the factor module `X ⊠ Y` and the layer `S(X ⊠ Y)`.
* `stdLayerEquiv`: standardization of an isomorphism of factor modules.
* `firstIndTensorEquiv`: `Ind (X ⊠ Y) ≅ Fᵢ X ⊠ Y` along `appendBlack ⊗ id`;
  `lastIndTensorEquiv`: `Ind (X ⊠ Y) ≅ X ⊠ Ind Y` along `id ⊗ cyclotomicLast`.
* `StdLayer.TensorForm`, `StdLayer.TensorForm.wordLayers`: every layer of `F_w` applied to a
  layer of tensor form has tensor form, for classes of modules closed under induction.

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

/-- A module over a `k`-algebra, with its `k`-module structure through the algebra map. -/
def KMod {A : Type} [Ring A] [Algebra k A] (X : ModuleCat.{0} A) : Type := X

instance {A : Type} [Ring A] [Algebra k A] (X : ModuleCat.{0} A) :
    AddCommGroup (KMod (k := k) X) := inferInstanceAs (AddCommGroup X)

instance {A : Type} [Ring A] [Algebra k A] (X : ModuleCat.{0} A) :
    Module A (KMod (k := k) X) := inferInstanceAs (Module A X)

instance {A : Type} [Ring A] [Algebra k A] (X : ModuleCat.{0} A) :
    Module k (KMod (k := k) X) := Module.compHom _ (algebraMap k A)

instance {A : Type} [Ring A] [Algebra k A] (X : ModuleCat.{0} A) :
    IsScalarTower k A (KMod (k := k) X) where
  smul_assoc c a x := by
    change (c • a) • x = algebraMap k A c • (a • x)
    rw [Algebra.smul_def, mul_smul]

/-- A module map, as a map of the modules `KMod`. -/
def KMod.map {A : Type} [Ring A] [Algebra k A] {X Y : ModuleCat.{0} A} (f : X →ₗ[A] Y) :
    KMod (k := k) X →ₗ[A] KMod (k := k) Y := f

/-- The factor module `X ⊠ Y` of a module over `T^{λ'}_θ` and one over `R^{λ_ℓ}_β`. -/
def tensorFactor {θ β : Multiset I}
    (X : ModuleCat.{0} (Told θ)) (Y : ModuleCat.{0} (Cyc β)) :
    FactorModule Q Λ θ β :=
  ⟨ExtTensor k (KMod (k := k) X) (KMod (k := k) Y)⟩

/-- The standard layer `S(X ⊠ Y)`. -/
def tensorLayer {θ β ν : Multiset I} (h : θ + β = ν)
    (X : ModuleCat.{0} (Told θ)) (Y : ModuleCat.{0} (Cyc β)) :
    StdLayer Q Λ ν :=
  ⟨θ, β, h, tensorFactor Q Λ X Y⟩

variable (hQ : KLRSymm Q)

/-- A map of factor modules induces a map of standard layers with the same split. -/
def stdLayerMap {θ β ν : Multiset I} (h : θ + β = ν) {M M' : FactorModule Q Λ θ β}
    (g : M.carrier →ₗ[parabolicFactorAlgebra Q Λ θ β] M'.carrier) :
    stdLayerModule Q Λ hQ ⟨θ, β, h, M⟩ →ₗ[TensorProductAlgebra k Q Λ ν]
      stdLayerModule Q Λ hQ ⟨θ, β, h, M'⟩ where
  toFun := parabolicStandardMap Q Λ θ β g
  map_add' := map_add _
  map_smul' _ z := parabolicStandardMap_action Q Λ θ β hQ g _ z

/-- An isomorphism of factor modules induces one of standard layers with the same split. -/
def stdLayerEquiv {θ β ν : Multiset I} (h : θ + β = ν) {M M' : FactorModule Q Λ θ β}
    (e : M.carrier ≃ₗ[parabolicFactorAlgebra Q Λ θ β] M'.carrier) :
    stdLayerModule Q Λ hQ ⟨θ, β, h, M⟩ ≃ₗ[TensorProductAlgebra k Q Λ ν]
      stdLayerModule Q Λ hQ ⟨θ, β, h, M'⟩ :=
  LinearEquiv.ofBijective (stdLayerMap Q Λ hQ h e.toLinearMap)
    ⟨parabolicStandardMap_injective Q Λ θ β hQ _ e.injective,
      parabolicStandardMap_surjective Q Λ θ β hQ _ e.surjective⟩

variable (i : I)

/-- `Fᵢ` on modules over `T^{λ'}_θ`: induction along `appendBlack`. -/
abbrev oldIndModule {θ : Multiset I} (X : ModuleCat.{0} (Told θ)) :
    ModuleCat.{0} (Told ((Si i) + θ)) :=
  ModuleCat.of _ (Ind X (appendBlackNU (Q := Q) (Λ := old) i θ))

/-- Induction along `cyclotomicLast` on modules over `R^{λ_ℓ}_β`. -/
abbrev cycIndModule {β : Multiset I} (Y : ModuleCat.{0} (Cyc β)) :
    ModuleCat.{0} (Cyc ((Si i) + β)) :=
  ModuleCat.of _ (Ind Y (NonUnitalRingHomClass.toNonUnitalRingHom
    (AbsentColour.cyclotomicLast Q i (aΛ) β)))

theorem appendBlack_smul' (θ : Multiset I) (c : k)
    (t : Told θ) :
    appendBlackNU (Q := Q) (Λ := old) i θ (c • t) =
      c • appendBlackNU (Q := Q) (Λ := old) i θ t :=
  map_smul (appendBlack Q (old) i θ) c t

theorem cyclotomicLast_smul' (β : Multiset I) (c : k) (t : Cyc β) :
    (NonUnitalRingHomClass.toNonUnitalRingHom (AbsentColour.cyclotomicLast Q i (aΛ) β) :
        _ →ₙ+* _) (c • t) =
      c • (NonUnitalRingHomClass.toNonUnitalRingHom
        (AbsentColour.cyclotomicLast Q i (aΛ) β) : _ →ₙ+* _) t :=
  map_smul (AbsentColour.cyclotomicLast Q i (aΛ) β) c t

theorem tensorLeft_eq_leftAppendHom (θ β : Multiset I)
    (t : parabolicFactorAlgebra Q Λ θ β) :
    leftAppendHom Q Λ i θ β t =
      tensorLeft k (Cyc β) (appendBlackNU (Q := Q) (Λ := old) i θ)
        (appendBlack_smul' Q Λ i θ) t := by
  induction t using TensorProduct.inductionOn with
  | tmul a c => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The `k`-module of `Fᵢ X` agrees with the induced module `Ind X` with scalars through
`T^{λ'}`. -/
def oldIndKEquiv {θ : Multiset I} (X : ModuleCat.{0} (Told θ)) :
    IndK k (KMod (k := k) X) (appendBlackNU (Q := Q) (Λ := old) i θ) ≃ₗ[Told ((Si i) + θ)]
      KMod (k := k) (oldIndModule Q Λ i X) :=
  LinearEquiv.refl _ _

/-- `Fᵢ` on the first factor of a tensor factor module: `Ind (X ⊠ Y) ≅ (Fᵢ X) ⊠ Y`. -/
def firstIndTensorEquiv {θ β : Multiset I}
    (X : ModuleCat.{0} (Told θ)) (Y : ModuleCat.{0} (Cyc β)) :
    FirstIndLeft Q Λ i θ β (tensorFactor Q Λ X Y).carrier ≃ₗ[parabolicFactorAlgebra Q Λ
      ((Si i) + θ) β] (tensorFactor Q Λ (oldIndModule Q Λ i X) Y).carrier :=
  let e₁ : FirstIndLeft Q Λ i θ β (tensorFactor Q Λ X Y).carrier ≃ₗ[parabolicFactorAlgebra
      Q Λ ((Si i) + θ) β] IndK k (ExtTensor k (KMod (k := k) X) (KMod (k := k) Y))
        (tensorLeft k (Cyc β) (appendBlackNU (Q := Q) (Λ := old) i θ)
          (appendBlack_smul' Q Λ i θ)) :=
    { Ind.transport (RingEquiv.refl _) (RingEquiv.refl _)
        (fun t => (tensorLeft_eq_leftAppendHom Q Λ i θ β t).symm) (AddEquiv.refl _)
        (fun _ _ => rfl) with
      map_smul' := fun b x => Ind.transport_smul (RingEquiv.refl _) (RingEquiv.refl _)
        (fun t => (tensorLeft_eq_leftAppendHom Q Λ i θ β t).symm) (AddEquiv.refl _)
        (fun _ _ => rfl) b x }
  e₁.trans ((extIndLeft k (Cyc β) (appendBlackNU (Q := Q) (Λ := old) i θ)
    (appendBlack_smul' Q Λ i θ) (KMod (k := k) X) (KMod (k := k) Y)).symm.trans
    (ExtTensor.congr (oldIndKEquiv Q Λ i X) (LinearEquiv.refl _ _)))

theorem tensorRight_eq_parabolicRightHom (θ β : Multiset I)
    (t : parabolicFactorAlgebra Q Λ θ β) :
    parabolicRightHom Q Λ i θ β t =
      tensorRight k (Told θ)
        (NonUnitalRingHomClass.toNonUnitalRingHom (AbsentColour.cyclotomicLast Q i (aΛ) β))
        (cyclotomicLast_smul' Q Λ i β) t := by
  induction t using TensorProduct.inductionOn with
  | tmul a c => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The `k`-module of the induced cyclotomic module agrees with `cycIndModule`. -/
def cycIndKEquiv {β : Multiset I} (Y : ModuleCat.{0} (Cyc β)) :
    IndK k (KMod (k := k) Y) (NonUnitalRingHomClass.toNonUnitalRingHom
      (AbsentColour.cyclotomicLast Q i (aΛ) β)) ≃ₗ[Cyc ((Si i) + β)]
      KMod (k := k) (cycIndModule Q Λ i Y) :=
  LinearEquiv.refl _ _

/-- `Fᵢ` on the last factor of a tensor factor module: `Ind (X ⊠ Y) ≅ X ⊠ Ind Y`. -/
def lastIndTensorEquiv {θ β : Multiset I}
    (X : ModuleCat.{0} (Told θ)) (Y : ModuleCat.{0} (Cyc β)) :
    LastIndRight Q Λ i θ β (tensorFactor Q Λ X Y).carrier ≃ₗ[parabolicFactorAlgebra Q Λ
      θ ((Si i) + β)] (tensorFactor Q Λ X (cycIndModule Q Λ i Y)).carrier :=
  let e₁ : LastIndRight Q Λ i θ β (tensorFactor Q Λ X Y).carrier ≃ₗ[parabolicFactorAlgebra
      Q Λ θ ((Si i) + β)] IndK k (ExtTensor k (KMod (k := k) X) (KMod (k := k) Y))
        (tensorRight k (Told θ)
          (NonUnitalRingHomClass.toNonUnitalRingHom (AbsentColour.cyclotomicLast Q i (aΛ) β))
          (cyclotomicLast_smul' Q Λ i β)) :=
    { Ind.transport (RingEquiv.refl _) (RingEquiv.refl _)
        (fun t => (tensorRight_eq_parabolicRightHom Q Λ i θ β t).symm) (AddEquiv.refl _)
        (fun _ _ => rfl) with
      map_smul' := fun b x => Ind.transport_smul (RingEquiv.refl _) (RingEquiv.refl _)
        (fun t => (tensorRight_eq_parabolicRightHom Q Λ i θ β t).symm) (AddEquiv.refl _)
        (fun _ _ => rfl) b x }
  e₁.trans ((extIndRight k (Told θ)
    (NonUnitalRingHomClass.toNonUnitalRingHom (AbsentColour.cyclotomicLast Q i (aΛ) β))
    (cyclotomicLast_smul' Q Λ i β) (KMod (k := k) Y) (KMod (k := k) X)).symm.trans
    (ExtTensor.congr (LinearEquiv.refl _ _) (cycIndKEquiv Q Λ i Y)))

/-- Induction along `leftAppendHom` of an isomorphism of factor modules. -/
def firstIndLeftCongr {θ β : Multiset I} {M M' : FactorModule Q Λ θ β}
    (e : M.carrier ≃ₗ[parabolicFactorAlgebra Q Λ θ β] M'.carrier) :
    FirstIndLeft Q Λ i θ β M.carrier ≃ₗ[parabolicFactorAlgebra Q Λ ((Si i) + θ) β]
      FirstIndLeft Q Λ i θ β M'.carrier :=
  { Ind.transport (RingEquiv.refl _) (RingEquiv.refl _) (fun _ => rfl) e.toAddEquiv
      (fun t n => e.map_smul t n) with
    map_smul' := fun b x => Ind.transport_smul (RingEquiv.refl _) (RingEquiv.refl _)
      (fun _ => rfl) e.toAddEquiv (fun t n => e.map_smul t n) b x }

/-- Induction along `parabolicRightHom` of an isomorphism of factor modules. -/
def lastIndRightCongr {θ β : Multiset I} {M M' : FactorModule Q Λ θ β}
    (e : M.carrier ≃ₗ[parabolicFactorAlgebra Q Λ θ β] M'.carrier) :
    LastIndRight Q Λ i θ β M.carrier ≃ₗ[parabolicFactorAlgebra Q Λ θ ((Si i) + β)]
      LastIndRight Q Λ i θ β M'.carrier :=
  { Ind.transport (RingEquiv.refl _) (RingEquiv.refl _) (fun _ => rfl) e.toAddEquiv
      (fun t n => e.map_smul t n) with
    map_smul' := fun b x => Ind.transport_smul (RingEquiv.refl _) (RingEquiv.refl _)
      (fun _ => rfl) e.toAddEquiv (fun t n => e.map_smul t n) b x }

/-- A factor module of the form `X ⊠ Y`, with `X` in the class `𝒳` of modules over `T^{λ'}`
and `Y` in the class `𝒴` of modules over `R^{λ_ℓ}`. -/
def FactorModule.TensorForm
    (𝒳 : ∀ θ : Multiset I, ModuleCat.{0} (Told θ) → Prop)
    (𝒴 : ∀ β : Multiset I, ModuleCat.{0} (Cyc β) → Prop)
    {θ β : Multiset I} (M : FactorModule Q Λ θ β) : Prop :=
  ∃ (X : ModuleCat.{0} (Told θ))
    (Y : ModuleCat.{0} (Cyc β)), 𝒳 θ X ∧ 𝒴 β Y ∧
    Nonempty (M.carrier ≃ₗ[parabolicFactorAlgebra Q Λ θ β] (tensorFactor Q Λ X Y).carrier)

/-- A standard layer whose factor module has tensor form. -/
def StdLayer.TensorForm
    (𝒳 : ∀ θ : Multiset I, ModuleCat.{0} (Told θ) → Prop)
    (𝒴 : ∀ β : Multiset I, ModuleCat.{0} (Cyc β) → Prop)
    {ν : Multiset I} (c : StdLayer Q Λ ν) : Prop :=
  c.M.TensorForm Q Λ 𝒳 𝒴

variable {Q Λ}

theorem FactorModule.TensorForm.first
    {𝒳 : ∀ θ : Multiset I, ModuleCat.{0} (Told θ) → Prop}
    {𝒴 : ∀ β : Multiset I, ModuleCat.{0} (Cyc β) → Prop}
    (h𝒳 : ∀ θ X, 𝒳 θ X → 𝒳 ((Si i) + θ) (oldIndModule Q Λ i X))
    {θ β : Multiset I} {M : FactorModule Q Λ θ β} (hM : M.TensorForm Q Λ 𝒳 𝒴) :
    (⟨FirstIndLeft Q Λ i θ β M.carrier⟩ : FactorModule Q Λ ((Si i) + θ) β).TensorForm Q Λ
      𝒳 𝒴 := by
  obtain ⟨X, Y, hX, hY, ⟨e⟩⟩ := hM
  exact ⟨oldIndModule Q Λ i X, Y, h𝒳 _ X hX, hY,
    ⟨(firstIndLeftCongr Q Λ i (M' := tensorFactor Q Λ X Y) e).trans
      (firstIndTensorEquiv Q Λ i X Y)⟩⟩

theorem FactorModule.TensorForm.last
    {𝒳 : ∀ θ : Multiset I, ModuleCat.{0} (Told θ) → Prop}
    {𝒴 : ∀ β : Multiset I, ModuleCat.{0} (Cyc β) → Prop}
    (h𝒴 : ∀ β Y, 𝒴 β Y → 𝒴 ((Si i) + β) (cycIndModule Q Λ i Y))
    {θ β : Multiset I} {M : FactorModule Q Λ θ β} (hM : M.TensorForm Q Λ 𝒳 𝒴) :
    (⟨LastIndRight Q Λ i θ β M.carrier⟩ : FactorModule Q Λ θ ((Si i) + β)).TensorForm Q Λ
      𝒳 𝒴 := by
  obtain ⟨X, Y, hX, hY, ⟨e⟩⟩ := hM
  exact ⟨X, cycIndModule Q Λ i Y, hX, h𝒴 _ Y hY,
    ⟨(lastIndRightCongr Q Λ i (M' := tensorFactor Q Λ X Y) e).trans
      (lastIndTensorEquiv Q Λ i X Y)⟩⟩

/-- Every layer of `F_w` applied to a layer of tensor form has tensor form, when the two
classes are closed under induction. -/
theorem StdLayer.TensorForm.wordLayers
    {𝒳 : ∀ θ : Multiset I, ModuleCat.{0} (Told θ) → Prop}
    {𝒴 : ∀ β : Multiset I, ModuleCat.{0} (Cyc β) → Prop}
    (h𝒳 : ∀ j θ X, 𝒳 θ X → 𝒳 ((Si j) + θ) (oldIndModule Q Λ j X))
    (h𝒴 : ∀ j β Y, 𝒴 β Y → 𝒴 ((Si j) + β) (cycIndModule Q Λ j Y))
    (w : List I) {ν : Multiset I} {c : StdLayer Q Λ ν} (hc : c.TensorForm Q Λ 𝒳 𝒴) :
    ∀ c' ∈ c.wordLayers Q Λ w, c'.TensorForm Q Λ 𝒳 𝒴 := by
  induction w with
  | nil => simpa [StdLayer.wordLayers] using hc
  | cons j w ih =>
    intro c' hc'
    simp only [StdLayer.wordLayers, List.mem_flatMap] at hc'
    obtain ⟨d, hd, hd'⟩ := hc'
    simp only [StdLayer.blackIndLayers, List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl
    · exact FactorModule.TensorForm.last j (h𝒴 j) (ih d hd)
    · exact FactorModule.TensorForm.first j (h𝒳 j) (ih d hd)

end Categorification.Stendhal
