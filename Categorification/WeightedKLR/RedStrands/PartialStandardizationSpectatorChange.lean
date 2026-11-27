/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSingletons

/-!
# Changing the spectator of a partial standardization

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization functors after Definition 5.4. A partial standardization with a
spectator algebra `E` (`CutSpectStandard`, `singStd`) only standardizes the blocks; the spectator
is carried along by functoriality. So an additive isomorphism `M ≅ M'` of modules over
`A ⊗ E` and `A ⊗ E'` that intertwines the actions along `id ⊗ φ`, for an algebra map
`φ : E → E'` (a `SpectatorEquiv`), gives an isomorphism of the partial standardizations
intertwining the actions along `id ⊗ φ` (`cutSpectStandardEquivOf`, `singStdSpectatorEquiv`).
With `φ` the identity this is the action of the partial standardizations on isomorphisms; with
`φ` an associator or a braiding it moves the spectator between nestings of tensor products.

## Main definitions

* `Stendhal.SpectatorEquiv`: an additive isomorphism intertwining the actions along `id ⊗ φ`.
* `Stendhal.cutSpectStandardEquivOf`: its partial standardization at a cut with a spectator.
* `Stendhal.singStdSpectatorEquiv`: its standardization with singleton blocks, in stages.
-/

universe u

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

/-- **An isomorphism of modules changing the spectator**: an additive isomorphism `M ≅ M'` of a
module over `A ⊗ E` and a module over `A ⊗ E'` intertwining the actions along `id ⊗ φ`. -/
structure SpectatorEquiv {k : Type*} [CommRing k] (A : Type*) [Ring A] [Algebra k A]
    {E E' : Type*} [Ring E] [Algebra k E] [Ring E'] [Algebra k E'] (φ : E →ₐ[k] E')
    (M M' : Type*) [AddCommGroup M] [Module (A ⊗[k] E) M] [AddCommGroup M']
    [Module (A ⊗[k] E') M'] where
  /-- The underlying additive isomorphism. -/
  equiv : M ≃+ M'
  map_smul (x : A ⊗[k] E) (m : M) :
    equiv (x • m) = Algebra.TensorProduct.map (AlgHom.id k A) φ x • equiv m

/-! ### At a cut -/

section Cut

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)
  {E E' : Type*} [Ring E] [Algebra k E] [Ring E'] [Algebra k E'] (φ : E →ₐ[k] E')

local notation "D" => cutFactorAlgebra Q Λ θ β
local notation "ι" => cutSpectTmul Q Λ θ β

/-- The map `id ⊗ φ : D ⊗ E → D ⊗ E'`. -/
def cutSpectMapAlg : cutSpectAlgebra Q Λ θ β E →ₐ[k] cutSpectAlgebra Q Λ θ β E' :=
  Algebra.TensorProduct.map (AlgHom.id k (cutFactorAlgebra Q Λ θ β)) φ

theorem cutSpectMapAlg_tmul (d : D) (e : E) :
    cutSpectMapAlg Q Λ θ β φ (ι E d e) = ι E' d (φ e) := rfl

variable {N N' : Type*} [AddCommGroup N] [Module k N] [Module (cutSpectAlgebra Q Λ θ β E) N]
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β E) N]
  [AddCommGroup N'] [Module k N'] [Module (cutSpectAlgebra Q Λ θ β E') N']
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β E') N']
  (f : N ≃+ N') (hf : ∀ (x : cutSpectAlgebra Q Λ θ β E) (n : N),
    f (x • n) = cutSpectMapAlg Q Λ θ β φ x • f n)

include hf in
omit [Module k N] [Module k N'] [IsScalarTower k (cutSpectAlgebra Q Λ θ β E) N]
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β E') N'] in
theorem spectatorEquiv_factor_smul (d : D) (n : N) : f (ι E d 1 • n) = ι E' d 1 • f n :=
  (hf (ι E d 1) n).trans (congrArg (· • f n)
    ((cutSpectMapAlg_tmul Q Λ θ β φ d 1).trans (congrArg (ι E' d) (map_one φ))))

/-- An isomorphism changing the spectator, as an isomorphism over the factor algebra `D`. -/
def cutSpectInputEquivOf :
    CutSpectInput Q Λ θ β E N ≃ₗ[D] CutSpectInput Q Λ θ β E' N' where
  toFun n := f n
  invFun n := f.symm n
  map_add' := f.map_add
  map_smul' d n := spectatorEquiv_factor_smul Q Λ θ β φ f hf d n
  left_inv := f.symm_apply_apply
  right_inv := f.apply_symm_apply

variable (hQ : KLRSymm Q)

/-- **The partial standardization of an isomorphism changing the spectator.** -/
def cutSpectStandardEquivOf :
    CutSpectStandard Q Λ θ β E N hQ ≃+ CutSpectStandard Q Λ θ β E' N' hQ where
  toFun z := cutStandardMap Q Λ θ β (cutSpectInputEquivOf Q Λ θ β φ f hf).toLinearMap z
  invFun z := cutStandardMap Q Λ θ β (cutSpectInputEquivOf Q Λ θ β φ f hf).symm.toLinearMap z
  left_inv z := by
    refine (cutStandardMap_comp Q Λ θ β _ _ z).symm.trans ?_
    refine Eq.trans ?_ (LinearMap.congr_fun (cutStandardMap_id Q Λ θ β) z)
    exact congrArg (fun g => cutStandardMap Q Λ θ β g z)
      (LinearMap.ext fun n => (cutSpectInputEquivOf Q Λ θ β φ f hf).symm_apply_apply n)
  right_inv z := by
    refine (cutStandardMap_comp Q Λ θ β _ _ z).symm.trans ?_
    refine Eq.trans ?_ (LinearMap.congr_fun (cutStandardMap_id Q Λ θ β) z)
    exact congrArg (fun g => cutStandardMap Q Λ θ β g z)
      (LinearMap.ext fun n => (cutSpectInputEquivOf Q Λ θ β φ f hf).apply_symm_apply n)
  map_add' := map_add _

theorem cutSpectStandardEquivOf_apply (z : CutSpectStandard Q Λ θ β E N hQ) :
    cutSpectStandardEquivOf Q Λ θ β φ f hf hQ z =
      cutStandardMap Q Λ θ β (cutSpectInputEquivOf Q Λ θ β φ f hf).toLinearMap z := rfl

/-- **The partial standardization of an isomorphism changing the spectator intertwines the
actions along `id ⊗ φ`.** -/
theorem cutSpectStandardEquivOf_smul (x : TensorProductAlgebra k Q Λ (θ + β) ⊗[k] E)
    (z : CutSpectStandard Q Λ θ β E N hQ) :
    cutSpectStandardEquivOf Q Λ θ β φ f hf hQ (x • z) =
      Algebra.TensorProduct.map (AlgHom.id k _) φ x •
        cutSpectStandardEquivOf Q Λ θ β φ f hf hQ z := by
  set G := (cutSpectInputEquivOf Q Λ θ β φ f hf).toLinearMap
  change cutStandardMap Q Λ θ β G (cutSpectStandardAction Q Λ θ β E N hQ x z) =
    cutSpectStandardAction Q Λ θ β E' N' hQ (Algebra.TensorProduct.map (AlgHom.id k _) φ x)
      (cutStandardMap Q Λ θ β G z)
  induction x using TensorProduct.inductionOn generalizing z with
  | tmul t e =>
    change cutStandardMap Q Λ θ β G
        (cutStandardAction Q Λ θ β (CutSpectInput Q Λ θ β E N) hQ t
          (cutStandardMap Q Λ θ β (cutSpectEnd Q Λ θ β E N e) z)) =
      cutStandardAction Q Λ θ β (CutSpectInput Q Λ θ β E' N') hQ t
        (cutStandardMap Q Λ θ β (cutSpectEnd Q Λ θ β E' N' (φ e))
          (cutStandardMap Q Λ θ β G z))
    rw [cutStandardMap_action]
    exact congrArg _ (cutStandardMap_comm Q Λ θ β G _ _
      (fun n => (hf (ι E 1 e) n).trans rfl) z)
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    exact (congrArg _ (LinearMap.add_apply _ _ z)).trans ((map_add _ _ _).trans
      ((congrArg₂ (· + ·) (hx z) (hy z)).trans (LinearMap.add_apply _ _ _).symm))

end Cut

/-! ### Singleton blocks, in stages -/

section Singletons

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

/-- The spectator change `id ⊗ φ : T^{λ_{n+1}} ⊗ E → T^{λ_{n+1}} ⊗ E'` of the first stage. -/
def singLastMap {n : ℕ} (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    {E E' : AlgCat.{u} k} (φ : E →ₐ[k] E') :
    (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k) →ₐ[k]
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E') : AlgCat.{u} k) :=
  Algebra.TensorProduct.map (AlgHom.id k (singLast Q Λ θ)) φ

theorem singAssocIn_map (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    {E E' : AlgCat.{u} k} (φ : E →ₐ[k] E')
    (x : singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) ⊗[k]
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k)) :
    Algebra.TensorProduct.map (AlgHom.id k (singAlg Q (n + 1) Λ θ)) φ
        (singAssocIn Q n Λ θ E x) =
      singAssocIn Q n Λ θ E' (Algebra.TensorProduct.map
        (AlgHom.id k (singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)))
        (singLastMap Q Λ θ φ) x) :=
  LinearMap.congr_fun (TensorProduct.ext_threefold' (R := k)
    (g := (Algebra.TensorProduct.map (AlgHom.id k (singAlg Q (n + 1) Λ θ)) φ).toLinearMap ∘ₗ
      (Algebra.TensorProduct.assoc k k k (singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc))
        (singLast Q Λ θ) E).symm.toLinearMap)
    (h := (Algebra.TensorProduct.assoc k k k
        (singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)) (singLast Q Λ θ) E').symm.toLinearMap ∘ₗ
      (Algebra.TensorProduct.map
        (AlgHom.id k (singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)))
        (Algebra.TensorProduct.map (AlgHom.id k (singLast Q Λ θ)) φ)).toLinearMap)
    fun _ _ _ => rfl) x

theorem singAssocOut_map (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    {E E' : AlgCat.{u} k} (φ : E →ₐ[k] E')
    (x : cutSpectAlgebra (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
      (θ (Fin.last n)) E) :
    Algebra.TensorProduct.map
        (AlgHom.id k (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
          (singWeight n (θ ∘ Fin.castSucc)))) (singLastMap Q Λ θ φ)
        (singAssocOut Q n Λ θ E x) =
      singAssocOut Q n Λ θ E' (cutSpectMapAlg Q Λ _ _ φ x) :=
  LinearMap.congr_fun (TensorProduct.ext_threefold (R := k)
    (g := (Algebra.TensorProduct.map (AlgHom.id k (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
          (singWeight n (θ ∘ Fin.castSucc))))
        (Algebra.TensorProduct.map (AlgHom.id k (singLast Q Λ θ)) φ)).toLinearMap ∘ₗ
      (Algebra.TensorProduct.assoc k k k (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
          (singWeight n (θ ∘ Fin.castSucc))) (singLast Q Λ θ) E).toLinearMap)
    (h := (Algebra.TensorProduct.assoc k k k (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
          (singWeight n (θ ∘ Fin.castSucc))) (singLast Q Λ θ) E').toLinearMap ∘ₗ
      (Algebra.TensorProduct.map (AlgHom.id k (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
          (singWeight n (θ ∘ Fin.castSucc)) ⊗[k] singLast Q Λ θ)) φ).toLinearMap)
    fun _ _ _ => rfl) x

/-- The input of the first stage of the standardization in stages. -/
abbrev singInObj (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) (Z : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E)) :
    ModuleCat.{u} (singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) ⊗[k]
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k)) :=
  (ModuleCat.restrictScalars.{u} (singAssocIn Q n Λ θ E)).obj Z

/-- The input of the last stage of the standardization in stages. -/
abbrev singOutObj (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k)
    (Y : ModuleCat.{u} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
      (singWeight n (θ ∘ Fin.castSucc)) ⊗[k]
        (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k))) :
    ModuleCat.{u} (cutSpectAlgebra (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
      (θ (Fin.last n)) E) :=
  (ModuleCat.restrictScalars.{u} (singAssocOut Q n Λ θ E)).obj Y

/-- A spectator change of a module over the singleton blocks, on the input of the first
stage. -/
def SpectatorEquiv.singIn {n : ℕ} {Λ : Fin (n + 1) → I →₀ ℕ} {θ : Fin (n + 1) → Multiset I}
    {E E' : AlgCat.{u} k} {φ : E →ₐ[k] E'} {Z : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E)}
    {Z' : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E')}
    (F : SpectatorEquiv (singAlg Q (n + 1) Λ θ) φ Z Z') :
    SpectatorEquiv (singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)) (singLastMap Q Λ θ φ)
      (singInObj Q n Λ θ E Z) (singInObj Q n Λ θ E' Z') where
  equiv := F.equiv
  map_smul x z := (F.map_smul (singAssocIn Q n Λ θ E x) z).trans
    (congrArg (· • F.equiv z) (singAssocIn_map Q n Λ θ φ x))

/-- The last stage of the standardization in stages of a spectator change. -/
def SpectatorEquiv.singOut {n : ℕ} {Λ : Fin (n + 1) → I →₀ ℕ} {θ : Fin (n + 1) → Multiset I}
    {E E' : AlgCat.{u} k} {φ : E →ₐ[k] E'}
    {Y : ModuleCat.{u} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
      (singWeight n (θ ∘ Fin.castSucc)) ⊗[k] (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k))}
    {Y' : ModuleCat.{u} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
      (singWeight n (θ ∘ Fin.castSucc)) ⊗[k] (AlgCat.of k (singLast Q Λ θ ⊗[k] E') : AlgCat.{u} k))}
    (G : SpectatorEquiv (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
      (singWeight n (θ ∘ Fin.castSucc))) (singLastMap Q Λ θ φ) Y Y') :
    SpectatorEquiv (TensorProductAlgebra k Q Λ
        (singWeight n (θ ∘ Fin.castSucc) + θ (Fin.last n))) φ
      ((cutSpectFunctor (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) E hQ).obj (singOutObj Q n Λ θ E Y))
      ((cutSpectFunctor (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) E' hQ).obj (singOutObj Q n Λ θ E' Y')) where
  equiv := cutSpectStandardEquivOf (a := n) (r := 1) Q Λ _ _ φ
    (N := singOutObj Q n Λ θ E Y) (N' := singOutObj Q n Λ θ E' Y')
    G.equiv (fun x y => (G.map_smul (singAssocOut Q n Λ θ E x) y).trans
      (congrArg (· • G.equiv y) (singAssocOut_map Q n Λ θ φ x))) hQ
  map_smul := cutSpectStandardEquivOf_smul (a := n) (r := 1) Q Λ _ _ φ _ _ hQ

/-- **The standardization in stages of an isomorphism changing the spectator**: it intertwines
the actions of `T^λ(θ_1 + ⋯ + θ_n) ⊗ E` and `T^λ(θ_1 + ⋯ + θ_n) ⊗ E'` along `id ⊗ φ`. -/
def singStdSpectatorEquiv : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (θ : Fin n → Multiset I) →
    {E E' : AlgCat.{u} k} → (φ : E →ₐ[k] E') →
    {Z : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E)} → {Z' : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E')} →
    SpectatorEquiv (singAlg Q n Λ θ) φ Z Z' →
    SpectatorEquiv (TensorProductAlgebra k Q Λ (singWeight n θ)) φ
      ((singStd Q hQ n Λ θ E).obj Z) ((singStd Q hQ n Λ θ E').obj Z')
  | 0, _, _, _, _, _, _, _, F => F
  | n + 1, Λ, θ, _, _, φ, _, _, F =>
    SpectatorEquiv.singOut Q hQ (singStdSpectatorEquiv n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
      (singLastMap Q Λ θ φ) (SpectatorEquiv.singIn Q F))

end Singletons

end Categorification.Stendhal
