/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidingEquivalence
import LieLean.GroupTheory.Coxeter.ArtinGroup
import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Monoidal.Skeleton

set_option backward.isDefEq.respectTransparency false

/-!
# The braid group action on the derived categories of the red orders

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Definition 6.16 and Corollary 6.17. Let `𝒱` be the product, over the permutations `u` of the
`ℓ + 1` red strands, of the derived categories of the corners of the braided Stendhal algebra at
the red orders `u = (u 1, …, u (ℓ + 1))`. For a permutation `w`, `𝔅_w : 𝒱 ⥤ 𝒱` applies at
`u` the braiding functor `𝔅(u w⁻¹, u)` to the component at `u w⁻¹` (`braidPermFunctor`).

* When the lengths of `v` and `w` add, `𝔅_v ⋙ 𝔅_w ≅ 𝔅_{v w}` (`braidPermFunctorCompIso`), by
  Lemma 6.12 after relabelling the red strands by `u (v w)⁻¹`
  (`braidingFunctorCompIsoOfRelabel`). Every `𝔅_w` is an equivalence (Theorem 6.15).
* So the classes of the `𝔅_{s_i}` in the group of isomorphism classes of autoequivalences of `𝒱`
  satisfy the braid relations, and the braid group on `ℓ + 1` strands (the Artin group of type
  `A_ℓ`) maps to that group (`braidActionHom`, sending `σ_i` to the class of `𝔅_{s_i}`).
* The positive lift along any reduced word of `w` maps to the class of `𝔅_w`
  (`braidActionHom_prod_reduced`).

Webster defines `𝔅_σ` (Definition 6.16) as `𝔅_τ^p 𝔅_{w₁} ⋯ 𝔅_{wₙ}` for the Garside
factorization `σ = τ^p ξ₁ ⋯ ξₙ` into a power of the positive lift `τ` of the longest element and
minimal positive lifts `ξⱼ` of permutations `wⱼ`; Corollary 6.17 says that any other such
factorization gives an isomorphic functor. Here `𝔅_σ` is the class `braidActionHom σ`, and
Corollary 6.17 is `braidActionHom_eq_factorization`: for every factorization of `σ` into a power
of `τ` and positive lifts of `w₁, …, wₙ` along reduced words, `braidActionHom σ` is the class of
`𝔅_{w₀}^p 𝔅_{w₁} ⋯ 𝔅_{wₙ}`; so two factorizations give isomorphic functors
(`braidPermUnit_factorization_eq`). This reading does not use Garside's normal form or the
injectivity of the positive braid monoid into the braid group.

Route hypotheses: those of Theorem 6.15 (`isEquivalence_braidingFunctor`), namely the injectivity
hypothesis of Lemma 6.8 inside `RowFigureFiveHypotheses`, at the Khovanov–Lauda scalars.
-/

noncomputable section

namespace Categorification

open CategoryTheory

section Conj

variable {X₂ X₁ X₀ Y₂ Y₁ Y₀ : Type*} [Category X₂] [Category X₁] [Category X₀]
  [Category Y₂] [Category Y₁] [Category Y₀]

/-- **Composites transported along fully faithful functors**: if `B_{ab} ⋙ T_b ≅ T_a ⋙ B'_{ab}`
for the three pairs and `B'₂₁ ⋙ B'₁₀ ≅ B'₂₀`, then `B₂₁ ⋙ B₁₀ ≅ B₂₀`, when `T₀` is fully
faithful. -/
def compIsoOfConj {B₂₁ : X₂ ⥤ X₁} {B₁₀ : X₁ ⥤ X₀} {B₂₀ : X₂ ⥤ X₀} {B'₂₁ : Y₂ ⥤ Y₁}
    {B'₁₀ : Y₁ ⥤ Y₀} {B'₂₀ : Y₂ ⥤ Y₀} {T₂ : X₂ ⥤ Y₂} {T₁ : X₁ ⥤ Y₁} {T₀ : X₀ ⥤ Y₀}
    (e₂₁ : B₂₁ ⋙ T₁ ≅ T₂ ⋙ B'₂₁) (e₁₀ : B₁₀ ⋙ T₀ ≅ T₁ ⋙ B'₁₀) (e₂₀ : B₂₀ ⋙ T₀ ≅ T₂ ⋙ B'₂₀)
    (hT : T₀.FullyFaithful) (c : B'₂₁ ⋙ B'₁₀ ≅ B'₂₀) : B₂₁ ⋙ B₁₀ ≅ B₂₀ :=
  (hT.whiskeringRight X₂).preimageIso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft B₂₁ e₁₀ ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₂₁ B'₁₀ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T₂ c ≪≫ e₂₀.symm)

end Conj

section Units

attribute [local instance] endofunctorMonoidalCategory

variable {X : Type*} [Category X]

/-- The class of an autoequivalence, as a unit of the monoid of isomorphism classes of
endofunctors. -/
def Skeleton.unitOfIsEquivalence (F : X ⥤ X) [F.IsEquivalence] : (Skeleton (X ⥤ X))ˣ where
  val := toSkeleton F
  inv := toSkeleton F.inv
  val_inv := by
    rw [← Skeleton.toSkeleton_tensorObj]
    exact congr_toSkeleton_of_iso F.asEquivalence.unitIso.symm
  inv_val := by
    rw [← Skeleton.toSkeleton_tensorObj]
    exact congr_toSkeleton_of_iso F.asEquivalence.counitIso

@[simp] theorem Skeleton.val_unitOfIsEquivalence (F : X ⥤ X) [F.IsEquivalence] :
    (Skeleton.unitOfIsEquivalence F : Skeleton (X ⥤ X)) = toSkeleton F := rfl

end Units

end Categorification

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory KLR Equiv
open scoped DG.DegreeZero

section Relabel

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  [∀ (Ω : Fin ℓ → I →₀ ℕ) (κ₀ : List (Fin ℓ)),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Ω) (ν := ν) κ₀)ᵐᵒᵖ]

/-- **Composites of braiding functors under relabelling**: an isomorphism
`𝔅^{λ ∘ σ}(κ₂, κ₁) ⋙ 𝔅^{λ ∘ σ}(κ₁, κ₀) ≅ 𝔅^{λ ∘ σ}(κ₂, κ₀)` gives
`𝔅^λ(σ κ₂, σ κ₁) ⋙ 𝔅^λ(σ κ₁, σ κ₀) ≅ 𝔅^λ(σ κ₂, σ κ₀)`. -/
def braidingFunctorCompIsoOfRelabel (σ : Perm (Fin ℓ)) {κ₂ κ₁ κ₀ : List (Fin ℓ)}
    (c : braidingFunctor.{0} k Q (Λ ∘ σ) ν κ₂ κ₁ ⋙ braidingFunctor.{0} k Q (Λ ∘ σ) ν κ₁ κ₀ ≅
      braidingFunctor.{0} k Q (Λ ∘ σ) ν κ₂ κ₀) :
    braidingFunctor.{0} k Q Λ ν (κ₂.map σ) (κ₁.map σ) ⋙
        braidingFunctor.{0} k Q Λ ν (κ₁.map σ) (κ₀.map σ) ≅
      braidingFunctor.{0} k Q Λ ν (κ₂.map σ) (κ₀.map σ) :=
  compIsoOfConj (braidingFunctorRelabelConjIso σ κ₂ κ₁) (braidingFunctorRelabelConjIso σ κ₁ κ₀)
    (braidingFunctorRelabelConjIso σ κ₂ κ₀) (twistEquivalence _).fullyFaithfulFunctor c

/-- The braiding functor from a red order to itself is the identity. -/
def braidingFunctorSelfIso (κ : List (Fin ℓ)) : braidingFunctor.{0} k Q Λ ν κ κ ≅ 𝟭 _ :=
  derivedRightTensorIsoOfEquiv (cornerBimoduleSelfTwistEquiv _) (fun _ _ => rfl) ≪≫
    twistFunctorReflIso

end Relabel

section Descent

open TypeA
open scoped List

variable {ℓ : ℕ}

theorem sadj_eq_swapAt {k : ℕ} (hk : k + 1 < ℓ) :
    sadj ℓ k = FirstWeight.swapAt k (ℓ - k - 2) (by omega) := by
  rw [FirstWeight.swapAt_eq_swap]
  simp only [sadj, hk, ↓reduceDIte]
  congr 1

/-- **The length condition at an ascent**: if `v k < v (k + 1)`, every pair of red strands
crossed by `v` is still crossed by `v s_k`. -/
theorem lengthAdditive_mul_sadj (v : Perm (Fin ℓ)) {k : ℕ} (hk : k + 1 < ℓ)
    (h : v ⟨k, (by omega)⟩ < v ⟨k + 1, hk⟩) :
    ∀ x y, [x, y] <+ (List.finRange ℓ).map ⇑(v * sadj ℓ k) →
      [y, x] <+ (List.finRange ℓ).map v → [y, x] <+ List.finRange ℓ := by
  have hs := sadj_eq_swapAt hk
  have := FirstWeight.lengthAdditive_mul_swapAt (v * sadj ℓ k) k (ℓ - k - 2) (by omega) (by
    rw [Perm.mul_apply, Perm.mul_apply]
    convert h using 2 <;> ext <;> simp [sadj_val_of_lt hk, swapNat])
  simp only [← hs, mul_assoc, sadj_mul_self, mul_one] at this
  exact this

theorem sadj_ne_one {k : ℕ} (hk : k + 1 < ℓ) : sadj ℓ k ≠ 1 := by
  intro h
  have := congrArg (fun f : Perm (Fin ℓ) => (f ⟨k, (by omega)⟩ : ℕ)) h
  simp [sadj_val_of_lt hk, swapNat] at this

/-- The prefix of a reduced word is reduced, and the last letter is an ascent of its product. -/
theorem isReduced_of_append_singleton {ω : List ℕ} {k : ℕ} (h : IsReduced ℓ (ω ++ [k])) :
    ∃ hk : k + 1 < ℓ, IsReduced ℓ ω ∧
      wordProd ℓ ω ⟨k, (by omega)⟩ < wordProd ℓ ω ⟨k + 1, hk⟩ := by
  have hv := h.validWord
  have hk : k + 1 < ℓ := hv k (by simp)
  have hω : ValidWord ℓ ω := fun a ha => hv a (by simp [ha])
  have hl := h.length_eq
  rw [wordProd_append] at hl
  have hp : wordProd ℓ [k] = sadj ℓ k := by simp [wordProd]
  rw [hp] at hl
  have hle := length_wordProd_le hω
  simp only [List.length_append, List.length_singleton] at hl
  refine ⟨hk, ⟨hω, ?_⟩, ?_⟩
  · rcases length_mul_sadj hk (wordProd ℓ ω) with h1 | h1 <;> omega
  · rcases lt_or_gt_of_ne (fun he : wordProd ℓ ω ⟨k, (by omega)⟩ = wordProd ℓ ω ⟨k + 1, hk⟩ =>
      absurd (congrArg Fin.val ((wordProd ℓ ω).injective he)) (by simp)) with h2 | h2
    · exact h2
    · have := length_mul_sadj_of_gt hk h2
      omega

theorem coxeterA_apply_of_ne {i i' : Fin ℓ} (h : i ≠ i') :
    CoxeterMatrix.A ℓ i i' = if (i' : ℕ) + 1 = i ∨ (i : ℕ) + 1 = i' then 3 else 2 := by
  simp [CoxeterMatrix.A, h]

end Descent

section KhovanovLauda

open QuantumGroup KL3.Diagram TypeA
open scoped Classical List

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra
attribute [local instance] endofunctorMonoidalCategory

variable {I : Type} {k : Type} [Field k] (C : CartanDatum I)
  (hQ : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) {ℓ : ℕ}
  {Y : Type*} [AddCommGroup Y] [Finite I]
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular)
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I),
    Module.Finite k (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Ω ν)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} ℤ]
  (H : ∀ (n m : ℕ), n + 2 + m = ℓ + 1 → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
    (u : Fin (n + 2 + m) → List I) (hu : u (FirstWeight.rightPos n m) = []),
    FirstWeight.RowFigureFiveHypotheses C hQ Ω u hu)

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "fin" => List.finRange (ℓ + 1)

include hQ hR H in
/-- **Webster, Lemma 6.12, second clause, at every red order** (arXiv:1309.3796v3): for red
orders `κ₂ = a`, `κ₁ = a v`, `κ₀ = a v w` with `w ≠ 1` and the lengths of `v` and `w` adding,
`𝔅(κ₂, κ₁) ⋙ 𝔅(κ₁, κ₀) ≅ 𝔅(κ₂, κ₀)`. Route hypotheses: those of Lemma 6.12. -/
def braidingFunctorCompIsoAt (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
    (wt : Fin (ℓ + 1) → LieLean.QuantumGroup.GrandLoop.Dom R)
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (a v w : Perm (Fin (ℓ + 1)))
    (hw : w ≠ 1)
    (hL : ∀ x y, [x, y] <+ (fin).map ⇑(v * w) → [y, x] <+ (fin).map v → [y, x] <+ fin)
    {κ₂ κ₁ κ₀ : List (Fin (ℓ + 1))} (h₂ : (fin).map a = κ₂) (h₁ : ((fin).map v).map a = κ₁)
    (h₀ : ((fin).map ⇑(v * w)).map a = κ₀) :
    braidingFunctor.{0} k QL Λ ν κ₂ κ₁ ⋙ braidingFunctor.{0} k QL Λ ν κ₁ κ₀ ≅
      braidingFunctor.{0} k QL Λ ν κ₂ κ₀ := by
  subst h₂ h₁ h₀
  exact braidingFunctorCompIsoOfRelabel a
    (FirstWeight.braidingFunctorCompIsoOfLengthAdd C hQ hR
      H (Λ ∘ a) (wt ∘ a)
      (fun r i => hwt (a r) i) ν v w hw hL)

variable (k) in
/-- The derived category of the corner at the red order `u = (u 1, …, u (ℓ + 1))`. -/
abbrev RedOrderDerived (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (u : Perm (Fin (ℓ + 1))) :
    Type _ :=
  DG.DerivedCategory.{0} (isIdempotentElem_violMk_redProj k QL Λ ν ((fin).map u)).Cornerᵐᵒᵖ

variable (k) in
/-- **The braiding functor of a permutation on all red orders**: `𝔅_w` applies at `u` the
braiding functor `𝔅(u w⁻¹, u)` to the component at `u w⁻¹`. -/
def braidPermFunctor (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (w : Perm (Fin (ℓ + 1))) :
    (∀ u, RedOrderDerived k C Λ ν u) ⥤ (∀ u, RedOrderDerived k C Λ ν u) :=
  Pi.comap (RedOrderDerived k C Λ ν) (fun u => u * w⁻¹) ⋙
    Functor.pi (fun u => braidingFunctor.{0} k QL Λ ν ((fin).map ⇑(u * w⁻¹)) ((fin).map u))

include hQ hR H in
/-- **Webster, Theorem 6.15, on all red orders**: every `𝔅_w` is an equivalence. -/
theorem isEquivalence_braidPermFunctor (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
    (wt : Fin (ℓ + 1) → LieLean.QuantumGroup.GrandLoop.Dom R)
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (w : Perm (Fin (ℓ + 1))) :
    (braidPermFunctor k C Λ ν w).IsEquivalence := by
  have : ∀ u : Perm (Fin (ℓ + 1)),
      (braidingFunctor.{0} k QL Λ ν ((fin).map ⇑(u * w⁻¹)) ((fin).map u)).IsEquivalence :=
    fun u => isEquivalence_braidingFunctor C hQ hR H Λ ν wt hwt
      (Equiv.Perm.map_finRange_perm _) (Equiv.Perm.map_finRange_perm _)
  have : (Pi.comap (RedOrderDerived k C Λ ν) (fun u => u * w⁻¹)).IsEquivalence :=
    Functor.isEquivalence_of_iso (F := (Pi.equivalenceOfEquiv (RedOrderDerived k C Λ ν)
      (Equiv.mulRight w⁻¹)).symm.functor) (NatIso.pi' fun _ => Iso.refl _)
  unfold braidPermFunctor
  infer_instance

include hQ hR H in
/-- **Webster, Lemma 6.12, on all red orders**: when the lengths of `v` and `w ≠ 1` add,
`𝔅_v ⋙ 𝔅_w ≅ 𝔅_{v w}`. -/
def braidPermFunctorCompIso (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
    (wt : Fin (ℓ + 1) → LieLean.QuantumGroup.GrandLoop.Dom R)
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (v w : Perm (Fin (ℓ + 1))) (hw : w ≠ 1)
    (hL : ∀ x y, [x, y] <+ (fin).map ⇑(v * w) → [y, x] <+ (fin).map v → [y, x] <+ fin) :
    braidPermFunctor k C Λ ν v ⋙ braidPermFunctor k C Λ ν w ≅
      braidPermFunctor k C Λ ν (v * w) :=
  NatIso.pi' fun u => (Functor.isoWhiskerLeft (Pi.eval (RedOrderDerived k C Λ ν) (u * (v * w)⁻¹))
    (braidingFunctorCompIsoAt C hQ hR H Λ ν wt hwt (u * (v * w)⁻¹) v w hw hL
      (κ₂ := (fin).map ⇑(u * (v * w)⁻¹)) (κ₁ := (fin).map ⇑(u * w⁻¹)) (κ₀ := (fin).map u) rfl
      (by rw [List.map_map]; congr 1; ext x; simp [mul_inv_rev])
      (by rw [List.map_map]; congr 1; ext x; simp [mul_inv_rev])) :)

include hQ hR H in
/-- The class of `𝔅_w` in the group of isomorphism classes of autoequivalences of the product of
the derived categories of all red orders. -/
def braidPermUnit (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
    (wt : Fin (ℓ + 1) → LieLean.QuantumGroup.GrandLoop.Dom R)
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (w : Perm (Fin (ℓ + 1))) :
    (Skeleton ((∀ u, RedOrderDerived k C Λ ν u) ⥤ (∀ u, RedOrderDerived k C Λ ν u)))ˣ :=
  haveI := isEquivalence_braidPermFunctor C hQ hR H Λ ν wt hwt w
  Skeleton.unitOfIsEquivalence (braidPermFunctor k C Λ ν w)

variable (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
  (wt : Fin (ℓ + 1) → LieLean.QuantumGroup.GrandLoop.Dom R)
  (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

theorem val_braidPermUnit (w : Perm (Fin (ℓ + 1))) :
    (braidPermUnit C hQ hR H Λ ν wt hwt w : Skeleton _) =
      toSkeleton (braidPermFunctor k C Λ ν w) := rfl

/-- `𝔅_v ⋙ 𝔅_w ≅ 𝔅_{v w}` when the lengths of `v` and `w ≠ 1` add. -/
theorem braidPermUnit_mul (v w : Perm (Fin (ℓ + 1))) (hw : w ≠ 1)
    (hL : ∀ x y, [x, y] <+ (fin).map ⇑(v * w) → [y, x] <+ (fin).map v → [y, x] <+ fin) :
    braidPermUnit C hQ hR H Λ ν wt hwt v * braidPermUnit C hQ hR H Λ ν wt hwt w =
      braidPermUnit C hQ hR H Λ ν wt hwt (v * w) :=
  Units.ext (by
    rw [Units.val_mul, val_braidPermUnit, val_braidPermUnit, val_braidPermUnit,
      ← Skeleton.toSkeleton_tensorObj]
    exact congr_toSkeleton_of_iso (braidPermFunctorCompIso C hQ hR H Λ ν wt hwt v w hw hL))

/-- `𝔅_v ⋙ 𝔅_{s_i} ≅ 𝔅_{v s_i}` when `v i < v (i + 1)`. -/
theorem braidPermUnit_mul_sadj (v : Perm (Fin (ℓ + 1))) {i : ℕ} (hi : i + 1 < ℓ + 1)
    (h : v ⟨i, (by omega)⟩ < v ⟨i + 1, hi⟩) :
    braidPermUnit C hQ hR H Λ ν wt hwt v * braidPermUnit C hQ hR H Λ ν wt hwt (sadj (ℓ + 1) i) =
      braidPermUnit C hQ hR H Λ ν wt hwt (v * sadj (ℓ + 1) i) :=
  braidPermUnit_mul C hQ hR H Λ ν wt hwt v _ (sadj_ne_one hi) (lengthAdditive_mul_sadj v hi h)

/-- `𝔅_1` is the identity. -/
theorem braidPermUnit_one : braidPermUnit C hQ hR H Λ ν wt hwt 1 = 1 :=
  Units.ext (congr_toSkeleton_of_iso (NatIso.pi' fun u =>
    (Functor.isoWhiskerLeft (Pi.eval (RedOrderDerived k C Λ ν) u)
      (braidingFunctorSelfIso ((fin).map u)) :)))

/-- The braid relation `𝔅_{s_a} 𝔅_{s_b} 𝔅_{s_a} ≅ 𝔅_{s_b} 𝔅_{s_a} 𝔅_{s_b}` for `b = a + 1`. -/
theorem braidPermUnit_braid {a b : ℕ} (hab : a + 1 = b) (hb : b + 1 < ℓ + 1) :
    braidPermUnit C hQ hR H Λ ν wt hwt (sadj (ℓ + 1) a) *
        braidPermUnit C hQ hR H Λ ν wt hwt (sadj (ℓ + 1) b) *
        braidPermUnit C hQ hR H Λ ν wt hwt (sadj (ℓ + 1) a) =
      braidPermUnit C hQ hR H Λ ν wt hwt (sadj (ℓ + 1) b) *
        braidPermUnit C hQ hR H Λ ν wt hwt (sadj (ℓ + 1) a) *
        braidPermUnit C hQ hR H Λ ν wt hwt (sadj (ℓ + 1) b) := by
  subst hab
  have ha : a + 1 < ℓ + 1 := by omega
  rw [braidPermUnit_mul_sadj C hQ hR H Λ ν wt hwt _ hb (by
      simp only [Fin.lt_def, sadj_val, swapNat]; split_ifs <;> omega),
    braidPermUnit_mul_sadj C hQ hR H Λ ν wt hwt _ ha (by
      simp only [Fin.lt_def, Perm.mul_apply, sadj_val, swapNat]; split_ifs <;> omega),
    braidPermUnit_mul_sadj C hQ hR H Λ ν wt hwt _ ha (by
      simp only [Fin.lt_def, sadj_val, swapNat]; split_ifs <;> omega),
    braidPermUnit_mul_sadj C hQ hR H Λ ν wt hwt _ hb (by
      simp only [Fin.lt_def, Perm.mul_apply, sadj_val, swapNat]; split_ifs <;> omega),
    sadj_braid (by omega)]

/-- Distant generators commute: `𝔅_{s_a} 𝔅_{s_b} ≅ 𝔅_{s_b} 𝔅_{s_a}` for `a + 1 < b`. -/
theorem braidPermUnit_comm {a b : ℕ} (hab : a + 1 < b) (hb : b + 1 < ℓ + 1) :
    braidPermUnit C hQ hR H Λ ν wt hwt (sadj (ℓ + 1) a) *
        braidPermUnit C hQ hR H Λ ν wt hwt (sadj (ℓ + 1) b) =
      braidPermUnit C hQ hR H Λ ν wt hwt (sadj (ℓ + 1) b) *
        braidPermUnit C hQ hR H Λ ν wt hwt (sadj (ℓ + 1) a) := by
  have ha : a + 1 < ℓ + 1 := by omega
  rw [braidPermUnit_mul_sadj C hQ hR H Λ ν wt hwt _ hb (by
      simp only [Fin.lt_def, sadj_val, swapNat]; split_ifs <;> omega),
    braidPermUnit_mul_sadj C hQ hR H Λ ν wt hwt _ ha (by
      simp only [Fin.lt_def, sadj_val, swapNat]; split_ifs <;> omega),
    sadj_comm _ (Or.inl hab)]

theorem braidPermUnit_braidWord (i i' : Fin ℓ) (hne : i ≠ i') :
    ((CoxeterSystem.braidWord (CoxeterMatrix.A ℓ) i i').map
        fun j : Fin ℓ => braidPermUnit C hQ hR H Λ ν wt hwt (sadj (ℓ + 1) j)).prod =
      ((CoxeterSystem.braidWord (CoxeterMatrix.A ℓ) i' i).map
        fun j : Fin ℓ => braidPermUnit C hQ hR H Λ ν wt hwt (sadj (ℓ + 1) j)).prod := by
  have hi := i.isLt
  have hi' := i'.isLt
  have hv : (i : ℕ) ≠ i' := fun h => hne (Fin.ext h)
  rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord, coxeterA_apply_of_ne hne,
    coxeterA_apply_of_ne hne.symm]
  by_cases hadj : (i' : ℕ) + 1 = i ∨ (i : ℕ) + 1 = i'
  · have hadj' : (i : ℕ) + 1 = i' ∨ (i' : ℕ) + 1 = i := hadj.symm
    simp only [hadj, hadj', ↓reduceIte]
    change [_, _, _].prod = [_, _, _].prod
    simp only [List.prod_cons, List.prod_nil, mul_one, ← mul_assoc]
    rcases hadj with h | h
    · exact braidPermUnit_braid C hQ hR H Λ ν wt hwt h (by omega)
    · exact (braidPermUnit_braid C hQ hR H Λ ν wt hwt h (by omega)).symm
  · have hadj' : ¬ ((i : ℕ) + 1 = i' ∨ (i' : ℕ) + 1 = i) := fun h => hadj h.symm
    simp only [hadj, hadj', ↓reduceIte]
    change [_, _].prod = [_, _].prod
    simp only [List.prod_cons, List.prod_nil, mul_one]
    rcases lt_or_gt_of_ne hv with h | h
    · exact braidPermUnit_comm C hQ hR H Λ ν wt hwt (by omega) (by omega)
    · exact (braidPermUnit_comm C hQ hR H Λ ν wt hwt (by omega) (by omega)).symm

/-- **The braid group acts on the derived categories of the red orders** (Webster,
arXiv:1309.3796v3, Definition 6.16): the braid group on `ℓ + 1` strands, the Artin group of type
`A_ℓ`, maps to the group of isomorphism classes of autoequivalences of the product of the derived
categories of all red orders, sending `σ_i` to the class of `𝔅_{s_i}`. Route hypotheses: those of
Theorem 6.15. -/
def braidActionHom :
    (CoxeterMatrix.A ℓ).ArtinGroup →*
      (Skeleton ((∀ u, RedOrderDerived k C Λ ν u) ⥤ (∀ u, RedOrderDerived k C Λ ν u)))ˣ :=
  CoxeterMatrix.artinLift (M := CoxeterMatrix.A ℓ)
    (fun j => braidPermUnit C hQ hR H Λ ν wt hwt (sadj (ℓ + 1) j))
    (fun i i' hne _ => braidPermUnit_braidWord C hQ hR H Λ ν wt hwt i i' hne)

theorem braidActionHom_artinGenerator (i : Fin ℓ) :
    braidActionHom C hQ hR H Λ ν wt hwt ((CoxeterMatrix.A ℓ).artinGenerator i) =
      braidPermUnit C hQ hR H Λ ν wt hwt (sadj (ℓ + 1) i) :=
  CoxeterMatrix.artinLift_artinGenerator _ _ i

/-- **Positive lifts** (Webster, arXiv:1309.3796v3, before Definition 6.16, and Lemma 6.12): the
positive lift of `w` along any reduced word maps to the class of `𝔅_w`. -/
theorem braidActionHom_prod_reduced (ω : List (Fin ℓ))
    (hω : IsReduced (ℓ + 1) (ω.map Fin.val)) :
    braidActionHom C hQ hR H Λ ν wt hwt (ω.map (CoxeterMatrix.A ℓ).artinGenerator).prod =
      braidPermUnit C hQ hR H Λ ν wt hwt (wordProd (ℓ + 1) (ω.map Fin.val)) := by
  induction ω using List.reverseRecOn with
  | nil => simp [braidPermUnit_one]
  | append_singleton ω i ih =>
    rw [List.map_append, List.map_singleton] at hω
    obtain ⟨hk, hred, hlt⟩ := isReduced_of_append_singleton hω
    rw [List.map_append, List.prod_append, map_mul, ih hred, List.map_singleton,
      List.prod_singleton, braidActionHom_artinGenerator,
      braidPermUnit_mul_sadj C hQ hR H Λ ν wt hwt _ hk hlt, List.map_append, List.map_singleton,
      wordProd_append, wordProd_singleton]

/-- A product of positive lifts along reduced words maps to the product of the classes. -/
theorem braidActionHom_prod_prod_reduced (ξ : List (List (Fin ℓ)))
    (hξ : ∀ ω ∈ ξ, IsReduced (ℓ + 1) (ω.map Fin.val)) :
    braidActionHom C hQ hR H Λ ν wt hwt
        (ξ.map fun ω => (ω.map (CoxeterMatrix.A ℓ).artinGenerator).prod).prod =
      (ξ.map fun ω => braidPermUnit C hQ hR H Λ ν wt hwt
        (wordProd (ℓ + 1) (ω.map Fin.val))).prod := by
  induction ξ with
  | nil => simp
  | cons ω ξ ih =>
    rw [List.map_cons, List.prod_cons, map_mul, List.map_cons, List.prod_cons,
      braidActionHom_prod_reduced C hQ hR H Λ ν wt hwt ω (hξ ω (by simp)),
      ih fun ω' h' => hξ ω' (by simp [h'])]

/-- **Webster, Corollary 6.17** (arXiv:1309.3796v3): for every factorization
`σ = τ^p ξ₁ ⋯ ξₙ` of a braid into a power of the positive lift `τ` of the longest element and
positive lifts `ξⱼ` of permutations `wⱼ` along reduced words, the class `𝔅_σ` of `σ` is that
of `𝔅_{w₀}^p 𝔅_{w₁} ⋯ 𝔅_{wₙ}`. Route hypotheses: those of Theorem 6.15. -/
theorem braidActionHom_eq_factorization (τw : List (Fin ℓ))
    (hτ : IsReduced (ℓ + 1) (τw.map Fin.val))
    (hτ₀ : wordProd (ℓ + 1) (τw.map Fin.val) = Fin.revPerm) (p : ℤ) (ξ : List (List (Fin ℓ)))
    (hξ : ∀ ω ∈ ξ, IsReduced (ℓ + 1) (ω.map Fin.val)) (σ : (CoxeterMatrix.A ℓ).ArtinGroup)
    (hσ : σ = (τw.map (CoxeterMatrix.A ℓ).artinGenerator).prod ^ p *
      (ξ.map fun ω => (ω.map (CoxeterMatrix.A ℓ).artinGenerator).prod).prod) :
    braidActionHom C hQ hR H Λ ν wt hwt σ =
      braidPermUnit C hQ hR H Λ ν wt hwt Fin.revPerm ^ p *
        (ξ.map fun ω => braidPermUnit C hQ hR H Λ ν wt hwt (wordProd (ℓ + 1) (ω.map Fin.val))).prod
    := by
  have h1 : braidActionHom C hQ hR H Λ ν wt hwt
      ((τw.map (CoxeterMatrix.A ℓ).artinGenerator).prod ^ p) =
      braidPermUnit C hQ hR H Λ ν wt hwt Fin.revPerm ^ p := by
    rw [map_zpow, braidActionHom_prod_reduced C hQ hR H Λ ν wt hwt τw hτ, hτ₀]
  rw [hσ, map_mul, h1, braidActionHom_prod_prod_reduced C hQ hR H Λ ν wt hwt ξ hξ]

/-- **Webster, Corollary 6.17, two factorizations** (arXiv:1309.3796v3): two factorizations
`τ^p ξ₁ ⋯ ξₙ = τ^{p'} ξ'₁ ⋯ ξ'ₘ` of the same braid into powers of the positive lift `τ` of the
longest element and positive lifts of permutations `wⱼ`, `w'ⱼ` along reduced words give
isomorphic functors `𝔅_{w₀}^p 𝔅_{w₁} ⋯ 𝔅_{wₙ} ≅ 𝔅_{w₀}^{p'} 𝔅_{w'₁} ⋯ 𝔅_{w'ₘ}`. Route hypotheses:
those of Theorem 6.15. -/
theorem braidPermUnit_factorization_eq (τw : List (Fin ℓ))
    (hτ : IsReduced (ℓ + 1) (τw.map Fin.val))
    (hτ₀ : wordProd (ℓ + 1) (τw.map Fin.val) = Fin.revPerm) (p p' : ℤ)
    (ξ ξ' : List (List (Fin ℓ))) (hξ : ∀ ω ∈ ξ, IsReduced (ℓ + 1) (ω.map Fin.val))
    (hξ' : ∀ ω ∈ ξ', IsReduced (ℓ + 1) (ω.map Fin.val))
    (h : (τw.map (CoxeterMatrix.A ℓ).artinGenerator).prod ^ p *
        (ξ.map fun ω => (ω.map (CoxeterMatrix.A ℓ).artinGenerator).prod).prod =
      (τw.map (CoxeterMatrix.A ℓ).artinGenerator).prod ^ p' *
        (ξ'.map fun ω => (ω.map (CoxeterMatrix.A ℓ).artinGenerator).prod).prod) :
    braidPermUnit C hQ hR H Λ ν wt hwt Fin.revPerm ^ p *
        (ξ.map fun ω => braidPermUnit C hQ hR H Λ ν wt hwt (wordProd (ℓ + 1) (ω.map Fin.val))).prod
      = braidPermUnit C hQ hR H Λ ν wt hwt Fin.revPerm ^ p' *
        (ξ'.map fun ω =>
          braidPermUnit C hQ hR H Λ ν wt hwt (wordProd (ℓ + 1) (ω.map Fin.val))).prod := by
  rw [← braidActionHom_eq_factorization C hQ hR H Λ ν wt hwt τw hτ hτ₀ p ξ hξ _ rfl,
    ← braidActionHom_eq_factorization C hQ hR H Λ ν wt hwt τw hτ hτ₀ p' ξ' hξ' _ rfl, h]

end KhovanovLauda

end Categorification.Stendhal.BraidedStendhalAlgebra
