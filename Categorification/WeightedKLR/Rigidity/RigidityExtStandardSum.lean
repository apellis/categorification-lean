/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtStandardResolution
import Categorification.WeightedKLR.Rigidity.RigidityExtSplitting
import Categorification.WeightedKLR.RedStrands.ParabolicStandardFunctor

/-!
# Standardizations of sums of copies of a module

Input for B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
§7.1, Corollary 7.7. The standardization `S(X ⊠ Y)` is additive in `Y`, so a bicone exhibiting
`Y'` as a sum of copies of `Y` gives one exhibiting `S(X ⊠ Y')` as a sum of copies of
`S(X ⊠ Y)` (`tensorStdBicone`). The projective `R^{λ_ℓ} e(w)` built by `Fᵢ` from `R^{λ_ℓ}_0`
(`cycWord w`) is the projective of the sequence `w` read backwards (`cycWord_equiv_cycProj`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Limits KLR KLRAlgebra InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "old" => Λ ∘ Fin.castSucc
local notation "aΛ" => fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j
local notation "Told" => TensorProductAlgebra k Q (old)
local notation "Cyc" => CycKLR k Q (aΛ)

/-! ### `S(X ⊠ −)` on maps -/

theorem _root_.Categorification.ExtTensor.map_add_right {A B : Type*} [Ring A] [Algebra k A]
    [Ring B] [Algebra k B]
    {P P' Q Q' : Type*} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
    [AddCommGroup Q] [Module k Q] [Module B Q] [IsScalarTower k B Q]
    [AddCommGroup P'] [Module k P'] [Module A P'] [IsScalarTower k A P']
    [AddCommGroup Q'] [Module k Q'] [Module B Q'] [IsScalarTower k B Q']
    (f : P →ₗ[A] P') (g g' : Q →ₗ[B] Q') :
    ExtTensor.map (k := k) f (g + g') = ExtTensor.map f g + ExtTensor.map f g' :=
  LinearMap.ext fun x => by
    induction x using ExtTensor.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul p q => exact ExtTensor.tmul_add _ _ _
    | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem _root_.Categorification.ExtTensor.map_zero_right {A B : Type*} [Ring A] [Algebra k A]
    [Ring B] [Algebra k B]
    {P P' Q Q' : Type*} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
    [AddCommGroup Q] [Module k Q] [Module B Q] [IsScalarTower k B Q]
    [AddCommGroup P'] [Module k P'] [Module A P'] [IsScalarTower k A P']
    [AddCommGroup Q'] [Module k Q'] [Module B Q'] [IsScalarTower k B Q']
    (f : P →ₗ[A] P') :
    ExtTensor.map (k := k) f (0 : Q →ₗ[B] Q') = 0 :=
  LinearMap.ext fun x => by
    induction x using ExtTensor.induction_on with
    | zero => simp
    | tmul p q =>
      change ExtTensor.tmul (f p) (0 : Q') = 0
      exact TensorProduct.tmul_zero _ _
    | add x y hx hy => simp only [map_add, hx, hy, LinearMap.zero_apply, add_zero]

variable (hQ : KLRSymm Q)

/-- The map `S(X ⊠ g) : S(X ⊠ Y) → S(X ⊠ Y')`. -/
def tensorStdMapRight {θ β ν : Multiset I} (h : θ + β = ν) (X : ModuleCat.{0} (Told θ))
    {Y Y' : ModuleCat.{0} (Cyc β)} (g : Y →ₗ[Cyc β] Y') :
    tensorStd Q Λ hQ h X Y →ₗ[TensorProductAlgebra k Q Λ ν] tensorStd Q Λ hQ h X Y' :=
  stdLayerMap Q Λ hQ h (M := tensorFactor Q Λ X Y) (M' := tensorFactor Q Λ X Y')
    (ExtTensor.map (k := k) (P := KMod (k := k) X) (P' := KMod (k := k) X)
      (Q := KMod (k := k) Y) (Q' := KMod (k := k) Y') LinearMap.id (KMod.map g))

section Functor

variable {θ β ν : Multiset I} (h : θ + β = ν)
  (X : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ))
  {Y Y' Y'' : ModuleCat.{0} (CycKLR k Q (fun j => Polynomial.X ^ Λ (Fin.last ℓ) j) β)}

/-- `S(X ⊠ g)` is the standardization of `X ⊠ g`. -/
theorem tensorStdMapRight_apply
    (g : Y →ₗ[CycKLR k Q (fun j => Polynomial.X ^ Λ (Fin.last ℓ) j) β] Y')
    (x : tensorStd Q Λ hQ h X Y) :
    tensorStdMapRight Q Λ hQ h X g x =
      parabolicStandardMap Q Λ θ β (N := (tensorFactor Q Λ X Y).carrier)
        (N' := (tensorFactor Q Λ X Y').carrier)
        (ExtTensor.map (k := k) (P := KMod (k := k) X) (P' := KMod (k := k) X)
          (Q := KMod (k := k) Y) (Q' := KMod (k := k) Y') LinearMap.id (KMod.map g)) x :=
  rfl

theorem tensorStdMapRight_id :
    tensorStdMapRight Q Λ hQ h X (LinearMap.id : Y →ₗ[Cyc β] Y) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  rw [tensorStdMapRight_apply]
  rw [show KMod.map (k := k) (LinearMap.id : Y →ₗ[Cyc β] Y) = LinearMap.id from rfl,
    ExtTensor.map_id, parabolicStandardMap_id]
  rfl

theorem tensorStdMapRight_comp (g : Y →ₗ[Cyc β] Y') (g' : Y' →ₗ[Cyc β] Y'') :
    tensorStdMapRight Q Λ hQ h X (g'.comp g) =
      (tensorStdMapRight Q Λ hQ h X g').comp (tensorStdMapRight Q Λ hQ h X g) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, tensorStdMapRight_apply, tensorStdMapRight_apply,
    tensorStdMapRight_apply]
  have hm := ExtTensor.map_comp (k := k)
    (LinearMap.id : KMod (k := k) X →ₗ[Told θ] KMod (k := k) X) (KMod.map (k := k) g)
    LinearMap.id (KMod.map (k := k) g')
  rw [LinearMap.id_comp] at hm
  rw [show KMod.map (k := k) (g'.comp g) = (KMod.map (k := k) g').comp (KMod.map g) from rfl,
    hm, parabolicStandardMap_comp]
  rfl

theorem tensorStdMapRight_add (g g' : Y →ₗ[Cyc β] Y') :
    tensorStdMapRight Q Λ hQ h X (g + g') =
      tensorStdMapRight Q Λ hQ h X g + tensorStdMapRight Q Λ hQ h X g' := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.add_apply, tensorStdMapRight_apply, tensorStdMapRight_apply,
    tensorStdMapRight_apply]
  rw [show KMod.map (k := k) (g + g') = KMod.map (k := k) g + KMod.map g' from rfl,
    ExtTensor.map_add_right, parabolicStandardMap_add]
  rfl

theorem tensorStdMapRight_zero :
    tensorStdMapRight Q Λ hQ h X (0 : Y →ₗ[Cyc β] Y') = 0 := by
  refine LinearMap.ext fun x => ?_
  rw [tensorStdMapRight_apply]
  rw [show KMod.map (k := k) (0 : Y →ₗ[Cyc β] Y') = 0 from rfl, ExtTensor.map_zero_right,
    parabolicStandardMap_zero]
  rfl

theorem tensorStdMapRight_sum {J : Type*} (s : Finset J) (g : J → Y →ₗ[Cyc β] Y') :
    tensorStdMapRight Q Λ hQ h X (∑ j ∈ s, g j) =
      ∑ j ∈ s, tensorStdMapRight Q Λ hQ h X (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, tensorStdMapRight_zero]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, tensorStdMapRight_add, ih]

end Functor

/-! ### Standardizations of sums -/

section Bicone

variable {θ β ν : Multiset I} (h : θ + β = ν)
  (X : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ))
  {J : Type*} [Fintype J] [DecidableEq J]
  {Y Y' : ModuleCat.{0} (CycKLR k Q (fun j => Polynomial.X ^ Λ (Fin.last ℓ) j) β)}
  (ι : J → (Y →ₗ[CycKLR k Q (fun j => Polynomial.X ^ Λ (Fin.last ℓ) j) β] Y'))
  (π : J → (Y' →ₗ[CycKLR k Q (fun j => Polynomial.X ^ Λ (Fin.last ℓ) j) β] Y))
  (hιπ : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0)

omit [Fintype J] in
include hιπ in
theorem tensorStdMapRight_comp_ite (i j : J) :
    (tensorStdMapRight Q Λ hQ h X (π j)).comp (tensorStdMapRight Q Λ hQ h X (ι i)) =
      if i = j then LinearMap.id else 0 := by
  rw [← tensorStdMapRight_comp, hιπ]
  split_ifs
  · exact tensorStdMapRight_id Q Λ hQ h X
  · exact tensorStdMapRight_zero Q Λ hQ h X

/-- The bicone exhibiting `S(X ⊠ Y')` as a sum of copies of `S(X ⊠ Y)`, from one exhibiting `Y'`
as a sum of copies of `Y`. -/
def tensorStdBicone : Bicone (fun _ : J => tensorStd Q Λ hQ h X Y) :=
  moduleBiconeOfLinear (X := tensorStd Q Λ hQ h X Y') (fun j => tensorStdMapRight Q Λ hQ h X (ι j))
    (fun j => tensorStdMapRight Q Λ hQ h X (π j)) (tensorStdMapRight_comp_ite Q Λ hQ h X ι π hιπ)

omit [Fintype J] in
theorem tensorStdBicone_pt : (tensorStdBicone Q Λ hQ h X ι π hιπ).pt = tensorStd Q Λ hQ h X Y' :=
  rfl

/-- `tensorStdBicone` is a bilimit. -/
def tensorStdBiconeIsBilimit (htot : ∑ j, (ι j).comp (π j) = LinearMap.id) :
    (tensorStdBicone Q Λ hQ h X ι π hιπ).IsBilimit :=
  moduleBiconeOfLinearIsBilimit _ _ _ (by
    simp_rw [← tensorStdMapRight_comp]
    rw [← tensorStdMapRight_sum, htot, tensorStdMapRight_id])

end Bicone

/-! ### The projectives `cycWord w` -/

omit [DecidableEq I] in
theorem _root_.Categorification.KLR.Seq.word_injective {α : Type*} {ν : Multiset α} :
    Function.Injective (Seq.word (ν := ν)) := by
  intro s t hst
  exact Subtype.ext (List.ofFn_injective hst)

omit [DecidableEq I] in
theorem _root_.Categorification.KLR.KLRAlgebra.Seq.word_ofList {ν : Multiset I} (l : List I)
    (h : (l : Multiset I) = ν) : (Seq.ofList l h).word = l := by
  apply List.ext_getElem
  · rw [Seq.length_word, ← h, Multiset.coe_card]
  · intro n h₁ h₂
    simp only [Seq.word, List.getElem_ofFn]
    rfl

omit [DecidableEq I] in
theorem coe_reverse_eq_wordWt (w : List I) : ((w.reverse : List I) : Multiset I) = wordWt w 0 := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    rw [List.reverse_cons, ← Multiset.coe_add, ih, wordWt, add_comm]
    rfl

/-- **`cycWord w` is the projective of `w` read backwards**: `R^{λ_ℓ} e(w.reverse)`. -/
theorem nonempty_cycWord_equiv_cycProj (w : List I) :
    Nonempty (cycWord Q Λ w ≃ₗ[Cyc (wordWt w 0)]
      cycProj Q Λ (wordWt w 0) (Seq.ofList w.reverse (coe_reverse_eq_wordWt w))) := by
  have key : ∀ w : List I, ∃ u : Seq (wordWt w 0), u.word = w.reverse ∧
      Nonempty (cycWord Q Λ w ≃ₗ[Cyc (wordWt w 0)] cycProj Q Λ (wordWt w 0) u) := by
    intro w
    induction w with
    | nil => exact ⟨Seq.ofList [] (by simp [wordWt]), Seq.word_ofList _ _,
        ⟨cycProjZeroEquiv Q Λ _⟩⟩
    | cons j w ih =>
      obtain ⟨u, hu, ⟨g⟩⟩ := ih
      refine ⟨_, ?_, ⟨(Ind.congr g).trans (cycProjIndEquiv Q Λ j _ u)⟩⟩
      rw [Seq.word_cast, Seq.word_append, hu, Seq.word_singleton, List.reverse_cons]
  obtain ⟨u, hu, ⟨g⟩⟩ := key w
  obtain rfl : u = Seq.ofList w.reverse (coe_reverse_eq_wordWt w) :=
    Seq.word_injective (hu.trans (Seq.word_ofList _ _).symm)
  exact ⟨g⟩

end Categorification.Stendhal
