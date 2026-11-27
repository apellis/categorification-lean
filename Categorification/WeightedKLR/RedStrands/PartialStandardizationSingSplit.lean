/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationCutRightZero
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSpectatorChange
import Categorification.WeightedKLR.RedStrands.PartialStandardizationPlusStaged

/-!
# The standardization in stages, split at a cut: definitions and the base case

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3 (proof of
Lemma 7.19, where the standardization with singleton blocks is computed in stages). For red
strands `λ_1, …, λ_{j+r}` the algebra of the singleton blocks maps to the tensor product of the
algebras of the singleton blocks of `λ_1, …, λ_j` and of `λ_{j+1}, …, λ_{j+r}` (`singSplit`),
and the weights add up (`singWeight_add`). The standardizations of the two blocks at the cut,
each with the other in the spectator, form `singOuter`. The comparison of the standardization
of all strands with the partial standardization at the cut of `singOuter` is an additive
isomorphism intertwining the actions (`IntertwiningEquiv`); this file proves the case `r = 0`
(`singCutEquivZero`).

## Main definitions

* `Stendhal.IntertwiningEquiv`: an additive isomorphism intertwining actions along a ring map.
* `Stendhal.singSplit`: the algebra map splitting the singleton blocks at the cut.
* `Stendhal.singOuter`: the standardizations of the two blocks at the cut.
* `Stendhal.singCutEquivZero`: the comparison when the second block is empty.

## Main results

* `Stendhal.singWeight_add`: the weights of the two blocks add up to the total weight.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)

omit [DecidableEq I] in
/-- The label of the last red strand, read in the second block. -/
theorem natAdd_natAdd_labels (j r : ℕ) (Λ : Fin (j + (r + 1)) → I →₀ ℕ) :
    Λ ∘ Fin.natAdd (j + r) = (Λ ∘ Fin.natAdd j) ∘ Fin.natAdd r :=
  funext fun _ => congrArg Λ (Fin.ext (Nat.add_assoc _ _ _))

/-- The algebra map `T^{λ_t'}(θ_t') ⊗ (T^{λ_{j+r+1}} ⊗ E) → T^{λ_t}(θ_t) ⊗ E` moving the last
singleton block from the spectator into the second block. -/
def singHeadMap (j r : ℕ) (Λ : Fin (j + (r + 1)) → I →₀ ℕ) (θ : Fin (j + (r + 1)) → Multiset I)
    (E : AlgCat.{u} k) :
    singAlg Q r ((Λ ∘ Fin.castSucc) ∘ Fin.natAdd j) ((θ ∘ Fin.castSucc) ∘ Fin.natAdd j) ⊗[k]
        (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k) →ₐ[k]
      singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E :=
  (Algebra.TensorProduct.assoc k k k
      (singAlg Q r ((Λ ∘ Fin.natAdd j) ∘ Fin.castSucc) ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc))
      (singLast Q (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)) E).symm.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id k _)
      (Algebra.TensorProduct.map
        (tensorProductAlgebraCast Q (natAdd_natAdd_labels j r Λ) (θ (Fin.last (j + r)))).toAlgHom
        (AlgHom.id k E)))

/-- **The splitting of the singleton blocks at a cut**: the algebra map
`(T^{λ_1}(θ_1) ⊗ ⋯ ⊗ T^{λ_{j+r}}(θ_{j+r})) ⊗ E → (T^{λ_1} ⊗ ⋯ ⊗ T^{λ_j}) ⊗ ((T^{λ_{j+1}} ⊗ ⋯ ⊗
T^{λ_{j+r}}) ⊗ E)`, by recursion on the number `r` of red strands in the second block. -/
def singSplit (j : ℕ) : (r : ℕ) → (Λ : Fin (j + r) → I →₀ ℕ) →
    (θ : Fin (j + r) → Multiset I) →
    (E : AlgCat.{u} k) →
    singAlg Q (j + r) Λ θ ⊗[k] E →ₐ[k]
      singAlg Q j (Λ ∘ Fin.castAdd r) (θ ∘ Fin.castAdd r) ⊗[k]
        (AlgCat.of k (singAlg Q r (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
          AlgCat.{u} k)
  | 0, _, _, _ => Algebra.TensorProduct.map (AlgHom.id k _) Algebra.TensorProduct.includeRight
  | r + 1, Λ, θ, E =>
    (Algebra.TensorProduct.map (AlgHom.id k _) (singHeadMap Q j r Λ θ E)).comp
      ((singSplit j r (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
          (AlgCat.of k (singLast Q Λ θ ⊗[k] E))).comp
        (Algebra.TensorProduct.assoc k k k _ (singLast Q Λ θ) E).toAlgHom)

omit [DecidableEq I] in
/-- The total weight of the singleton blocks is the sum of the weights of the two blocks. -/
theorem singWeight_add (j : ℕ) : (r : ℕ) → (θ : Fin (j + r) → Multiset I) →
    singWeight (j + r) θ =
      singWeight j (θ ∘ Fin.castAdd r) + singWeight r (θ ∘ Fin.natAdd j)
  | 0, _ => (add_zero _).symm
  | r + 1, θ => by
    change singWeight (j + r) (θ ∘ Fin.castSucc) + θ (Fin.last (j + r)) =
      singWeight j ((θ ∘ Fin.castSucc) ∘ Fin.castAdd r) +
        (singWeight r ((θ ∘ Fin.castSucc) ∘ Fin.natAdd j) + θ (Fin.last (j + r)))
    rw [singWeight_add j r (θ ∘ Fin.castSucc), add_assoc]

/-- An additive isomorphism of modules intertwining the actions along a ring map. -/
structure IntertwiningEquiv {A A' : Type*} [Ring A] [Ring A'] (f : A →+* A')
    (M M' : Type*) [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A' M'] where
  /-- The underlying additive isomorphism. -/
  equiv : M ≃+ M'
  map_smul (x : A) (m : M) : equiv (x • m) = f x • equiv m

namespace IntertwiningEquiv

variable {A A' A'' : Type*} [Ring A] [Ring A'] [Ring A''] {f : A →+* A'} {g : A' →+* A''}
  {M M' M'' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A' M']
  [AddCommGroup M''] [Module A'' M'']

/-- The composite of two intertwining isomorphisms. -/
def trans (e₁ : IntertwiningEquiv f M M') (e₂ : IntertwiningEquiv g M' M'') :
    IntertwiningEquiv (g.comp f) M M'' where
  equiv := e₁.equiv.trans e₂.equiv
  map_smul x m := (congrArg e₂.equiv (e₁.map_smul x m)).trans (e₂.map_smul _ _)

/-- An intertwining isomorphism along a ring map that agrees pointwise with another. -/
def ofEq (e : IntertwiningEquiv f M M') {f' : A →+* A'} (h : ∀ x, f x = f' x) :
    IntertwiningEquiv f' M M' where
  equiv := e.equiv
  map_smul x m := (e.map_smul x m).trans (congrArg (· • e.equiv m) (h x))

/-- A change of spectator, as an intertwining isomorphism. -/
def ofSpectator {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B]
    {E E' : Type*} [Ring E] [Algebra k E] [Ring E'] [Algebra k E'] {φ : E →ₐ[k] E'}
    {N N' : Type*} [AddCommGroup N] [Module (B ⊗[k] E) N] [AddCommGroup N']
    [Module (B ⊗[k] E') N'] (G : SpectatorEquiv B φ N N') :
    IntertwiningEquiv (Algebra.TensorProduct.map (AlgHom.id k B) φ).toRingHom N N' where
  equiv := G.equiv
  map_smul := G.map_smul

end IntertwiningEquiv

variable (hQ : KLRSymm Q)

/-- The rotation `(T^A ⊗ T^B) ⊗ E → T^B ⊗ (T^A ⊗ E)` moving the first block into the
spectator. -/
def singRotOut (j r : ℕ) (Λ : Fin (j + r) → I →₀ ℕ) (w₁ w₂ : Multiset I) (E : AlgCat.{u} k) :
    cutSpectAlgebra (a := j) (r := r) Q Λ w₁ w₂ E →ₐ[k]
      TensorProductAlgebra k Q (Λ ∘ Fin.natAdd j) w₂ ⊗[k]
        (AlgCat.of k (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd r) w₁ ⊗[k] E) :
          AlgCat.{u} k) :=
  (Algebra.TensorProduct.assoc k k k _ (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd r) w₁)
      E).toAlgHom.comp
    (Algebra.TensorProduct.map (Algebra.TensorProduct.comm k _ _).toAlgHom (AlgHom.id k E))

/-- **The standardizations of the two blocks at a cut**, in stages: the singleton blocks of
the first block with the second block in the spectator, then those of the second block with
the first block in the spectator. -/
def singOuter (j r : ℕ) (Λ : Fin (j + r) → I →₀ ℕ) (θ : Fin (j + r) → Multiset I)
    (E : AlgCat.{u} k) :
    ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd r) (θ ∘ Fin.castAdd r) ⊗[k]
        (AlgCat.of k (singAlg Q r (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
          AlgCat.{u} k)) ⥤
      ModuleCat.{u} (cutSpectAlgebra (a := j) (r := r) Q Λ
        (singWeight j (θ ∘ Fin.castAdd r)) (singWeight r (θ ∘ Fin.natAdd j)) E) :=
  singStd Q hQ j (Λ ∘ Fin.castAdd r) (θ ∘ Fin.castAdd r)
      (AlgCat.of k (singAlg Q r (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E)) ⋙
    ModuleCat.restrictScalars.{u} (Algebra.TensorProduct.leftComm k
      (singAlg Q r (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j))
      (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd r) (singWeight j (θ ∘ Fin.castAdd r)))
      E).toAlgHom.toRingHom ⋙
    singStd Q hQ r (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
      (AlgCat.of k (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd r)
        (singWeight j (θ ∘ Fin.castAdd r)) ⊗[k] E)) ⋙
    ModuleCat.restrictScalars.{u} (singRotOut Q j r Λ _ _ E).toRingHom

/-- The weight identification `T^λ(θ_1 + ⋯ + θ_{j+r}) ⊗ E ≅ T^λ(θ_h + θ_t) ⊗ E`. -/
abbrev singWeightCast (j r : ℕ) (Λ : Fin (j + r) → I →₀ ℕ) (θ : Fin (j + r) → Multiset I)
    (E : AlgCat.{u} k) :
    TensorProductAlgebra k Q Λ (singWeight (j + r) θ) ⊗[k] E →ₐ[k]
      TensorProductAlgebra k Q Λ
        (singWeight j (θ ∘ Fin.castAdd r) + singWeight r (θ ∘ Fin.natAdd j)) ⊗[k] E :=
  Algebra.TensorProduct.map (castTensorProductAlgebra Q Λ (singWeight_add j r θ)).toAlgHom
    (AlgHom.id k E)

section Zero
variable (j : ℕ) (Λ : Fin (j + 0) → I →₀ ℕ) (θ : Fin (j + 0) → Multiset I)
    (E : AlgCat.{u} k)
    (Z : ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd 0) (θ ∘ Fin.castAdd 0) ⊗[k]
        (AlgCat.of k (singAlg Q 0 (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
          AlgCat.{u} k)))

/-- The input of the partial standardization at the cut with an empty second block. -/
abbrev singZeroInput := CutSpectInput (a := j) (r := 0) Q Λ (singWeight j (θ ∘ Fin.castAdd 0))
  (singWeight 0 (θ ∘ Fin.natAdd j)) E ((singOuter Q hQ j 0 Λ θ E).obj Z)

/-- The carrier identity of the base case. -/
def singZeroCarrier : (singStd Q hQ j (Λ ∘ Fin.castAdd 0) (θ ∘ Fin.castAdd 0)
    (AlgCat.of k (singAlg Q 0 (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E))).obj Z ≃+
      singZeroInput Q hQ j Λ θ E Z := AddEquiv.refl _

/-- The partial standardization with an empty second block, along the unit. -/
def singZeroUnit : singZeroInput Q hQ j Λ θ E Z ≃+
    ((cutSpectFunctor (a := j) (r := 0) Q Λ _ _ E hQ).obj ((singOuter Q hQ j 0 Λ θ E).obj Z)) :=
  (cutStandardRightZeroEquiv (a := j) (r := 0) Q Λ _ (singWeight 0 (θ ∘ Fin.natAdd j))
      (singZeroInput Q hQ j Λ θ E Z) hQ (cutRightZero_weight (a := j))).toAddEquiv

/-- The change of spectator `E → T^∅(0) ⊗ E` at the base case. -/
def singZeroSpect : SpectatorEquiv (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 0)
      (singWeight j (θ ∘ Fin.castAdd 0)))
    (Algebra.TensorProduct.includeRight : E →ₐ[k]
      (AlgCat.of k (singAlg Q 0 (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) : AlgCat.{u} k))
    ((singStd Q hQ j (Λ ∘ Fin.castAdd 0) (θ ∘ Fin.castAdd 0) E).obj
        ((ModuleCat.restrictScalars.{u} (singSplit Q j 0 Λ θ E).toRingHom).obj Z))
    ((singStd Q hQ j (Λ ∘ Fin.castAdd 0) (θ ∘ Fin.castAdd 0)
      (AlgCat.of k (singAlg Q 0 (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E))).obj Z) :=
  singStdSpectatorEquiv Q hQ j (Λ ∘ Fin.castAdd 0) (θ ∘ Fin.castAdd 0) _
    (Z := (ModuleCat.restrictScalars.{u} (singSplit Q j 0 Λ θ E).toRingHom).obj Z) (Z' := Z)
    ⟨AddEquiv.refl _, fun _ _ => rfl⟩

/-- The base case `r = 0` of `singCutEquiv`. -/
def singCutEquivZero :
    IntertwiningEquiv (singWeightCast Q j 0 Λ θ E).toRingHom
      ((singStd Q hQ (j + 0) Λ θ E).obj
        ((ModuleCat.restrictScalars.{u} (singSplit Q j 0 Λ θ E).toRingHom).obj Z))
      ((cutSpectFunctor (a := j) (r := 0) Q Λ _ _ E hQ).obj
        ((singOuter Q hQ j 0 Λ θ E).obj Z)) where
  equiv := ((singZeroSpect Q hQ j Λ θ E Z).equiv.trans (singZeroCarrier Q hQ j Λ θ E Z)).trans
    (singZeroUnit Q hQ j Λ θ E Z)
  map_smul x m := by
    induction x using TensorProduct.inductionOn with
    | tmul t e =>
      exact (congrArg (cutStandardUnit (a := j) (r := 0) Q Λ _ (singWeight 0 (θ ∘ Fin.natAdd j))
          (singZeroInput Q hQ j Λ θ E Z))
        ((singZeroSpect Q hQ j Λ θ E Z).map_smul (t ⊗ₜ e) m)).trans
        (cutSpectStandardAction_right_zero_unit (a := j) Q Λ _ hQ E
          ((singOuter Q hQ j 0 Λ θ E).obj Z) t e _).symm
    | add x y hx hy =>
      exact (congrArg _ (add_smul x y m)).trans ((map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans ((add_smul _ _ _).symm.trans
          (congrArg (· • _) (map_add _ x y).symm))))

end Zero
end Categorification.Stendhal
