/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSpectatorTensor

/-!
# The standardization in stages commutes with tensoring the spectator

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization functors after Definition 5.4, and §7.3 (proof of Lemma 7.19, where
`S_+(Z ⊠ L)` is computed). The standardization with singleton blocks in stages (`singStd`)
acts on the blocks only, so a module `L` over a further algebra `B`, tensored onto the input
over `k`, passes through it. A `TensorSpectatorEquiv` along an algebra map `ψ : C ⊗ B → E`
identifies `M ⊗_k L` with `P`, for a module `M` over `T^{λ_1}(θ_1) ⊗ ⋯ ⊗ T^{λ_n}(θ_n) ⊗ C` and
a module `P` over `T^{λ_1}(θ_1) ⊗ ⋯ ⊗ T^{λ_n}(θ_n) ⊗ E`, so that `(a ⊗ c) m ⊗ b v` goes to
`(a ⊗ ψ(c ⊗ b))` applied to the image of `m ⊗ v`. The standardization in stages of `P` is then
that of `M` tensored with `L`, again along `ψ` (`singStdTensorEquiv`). The proof is by induction
on the number of red strands: the first stage moves the last block into both spectators
(`TensorSpectatorEquiv.singIn`, along `id ⊗ ψ`), and the last stage is the partial
standardization at a cut of a tensor isomorphism (`cutSpectTensorEquiv`) followed by the change
of spectator along `ψ` (`cutSpectStandardEquivOf`), in `TensorSpectatorEquiv.singOut`.

## Main definitions

* `Stendhal.TensorSpectatorEquiv`: an isomorphism `M ⊗ L ≅ P` compatible with the actions
  along `ψ`.
* `Stendhal.TensorSpectatorEquiv.singIn`, `Stendhal.TensorSpectatorEquiv.singOut`: the first
  and the last stage.
* `Stendhal.singStdTensorEquiv`: the standardization in stages of a `TensorSpectatorEquiv`.
-/

universe u

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

/-- **An isomorphism `M ⊗_k L ≅ P` compatible with the actions**: `M` is a module over `A ⊗ C`,
`L` a module over `B` and `P` a module over `A ⊗ E`, for an algebra map `ψ : C ⊗ B → E`, and
`(a ⊗ c) m ⊗ b v` goes to `(a ⊗ ψ(c ⊗ b))` applied to the image of `m ⊗ v`. -/
structure TensorSpectatorEquiv {k : Type*} [CommRing k] (A C B E : Type*) [Ring A] [Algebra k A]
    [Ring C] [Algebra k C] [Ring B] [Algebra k B] [Ring E] [Algebra k E]
    (ψ : C ⊗[k] B →ₐ[k] E) (M : Type*) [AddCommGroup M] [Module k M]
    [Module (A ⊗[k] C) M] (L : Type*) [AddCommGroup L] [Module k L] [Module B L] (P : Type*)
    [AddCommGroup P] [Module (A ⊗[k] E) P] where
  /-- The underlying additive isomorphism. -/
  equiv : M ⊗[k] L ≃+ P
  map_smul (a : A) (c : C) (b : B) (m : M) (v : L) :
    equiv (((a ⊗ₜ[k] c) • m) ⊗ₜ[k] (b • v)) = (a ⊗ₜ[k] ψ (c ⊗ₜ[k] b)) • equiv (m ⊗ₜ[k] v)

/-- An additive isomorphism of `k`-modules, tensored with `L`. -/
def tensorCongrOf {k : Type*} [CommRing k] {X Y : Type*} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] (L : Type*) [AddCommGroup L] [Module k L] (e : X ≃+ Y)
    (h : ∀ (c : k) (x : X), e (c • x) = c • e x) : X ⊗[k] L ≃+ Y ⊗[k] L :=
  (TensorProduct.congr ({ e with map_smul' := h } : X ≃ₗ[k] Y) (LinearEquiv.refl k L)).toAddEquiv

theorem tensorCongrOf_tmul {k : Type*} [CommRing k] {X Y : Type*} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] (L : Type*) [AddCommGroup L] [Module k L] (e : X ≃+ Y)
    (h : ∀ (c : k) (x : X), e (c • x) = c • e x) (x : X) (v : L) :
    tensorCongrOf L e h (x ⊗ₜ[k] v) = e x ⊗ₜ[k] v := rfl

section Singletons

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower in
/-- Restricting scalars along a map of `k`-algebras keeps the `k`-module structure. -/
theorem restrictScalars_algebraMap_smul {k : Type u} [CommRing k] {R S : Type u} [Ring R]
    [Algebra k R] [Ring S] [Algebra k S] (f : R →ₐ[k] S) (M : ModuleCat.{u} S) (c : k)
    (x : (ModuleCat.restrictScalars.{u} f.toRingHom).obj M) :
    AddEquiv.refl _ (c • x) = c • (show M from x) :=
  congrArg (fun r : S => r • (show M from x)) (f.commutes c)

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {C B E : AlgCat.{u} k} {L : Type u} [AddCommGroup L] [Module k L] [Module B L]

/-- The associator of the last stage, as a map of `k`-algebras. -/
def singAssocOutAlg (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) :
    cutSpectAlgebra (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) E →ₐ[k]
      (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (singWeight n (θ ∘ Fin.castSucc)) ⊗[k]
        (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k)) :=
  (Algebra.TensorProduct.assoc k k k
    (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (singWeight n (θ ∘ Fin.castSucc)))
    (singLast Q Λ θ) E).toAlgHom

/-- The algebra map `(T^{λ_{n+1}} ⊗ C) ⊗ B → T^{λ_{n+1}} ⊗ E` of the first stage, `l ⊗ c ⊗ b ↦
l ⊗ ψ(c ⊗ b)`. -/
def singTensorMap {n : ℕ} (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (ψ : C ⊗[k] B →ₐ[k] E) :
    (AlgCat.of k (singLast Q Λ θ ⊗[k] C) : AlgCat.{u} k) ⊗[k] B →ₐ[k]
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k) :=
  (Algebra.TensorProduct.map (AlgHom.id k (singLast Q Λ θ)) ψ).comp
    (Algebra.TensorProduct.assoc k k k (singLast Q Λ θ) C B).toAlgHom

theorem singTensorMap_tmul {n : ℕ} (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (ψ : C ⊗[k] B →ₐ[k] E) (l : singLast Q Λ θ) (c : C) (b : B) :
    singTensorMap Q Λ θ ψ ((show (AlgCat.of k (singLast Q Λ θ ⊗[k] C) : AlgCat.{u} k) from
      l ⊗ₜ[k] c) ⊗ₜ[k] b) = (show (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k) from
        l ⊗ₜ[k] ψ (c ⊗ₜ[k] b)) := rfl


/-- The tensor isomorphism on the input of the first stage of the standardization in
stages. -/
def TensorSpectatorEquiv.singIn {n : ℕ} {Λ : Fin (n + 1) → I →₀ ℕ}
    {θ : Fin (n + 1) → Multiset I} {ψ : C ⊗[k] B →ₐ[k] E}
    {M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] C)}
    {P : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E)}
    (F : TensorSpectatorEquiv (singAlg Q (n + 1) Λ θ) C B E ψ M L P) :
    TensorSpectatorEquiv (singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc))
      (AlgCat.of k (singLast Q Λ θ ⊗[k] C) : AlgCat.{u} k) B
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k) (singTensorMap Q Λ θ ψ)
      (singInObj Q n Λ θ C M) L (singInObj Q n Λ θ E P) where
  equiv := AddEquiv.trans (M := singInObj Q n Λ θ C M ⊗[k] L) (N := M ⊗[k] L)
    (tensorCongrOf (X := singInObj Q n Λ θ C M) (Y := M) L (AddEquiv.refl _)
      (restrictScalars_algebraMap_smul
      (Algebra.TensorProduct.assoc k k k (singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc))
        (singLast Q Λ θ) C).symm.toAlgHom M)) F.equiv
  map_smul a c₁ b m v := by
    induction c₁ using TensorProduct.inductionOn with
    | tmul l c => exact F.map_smul (a ⊗ₜ[k] l) c b m v
    | add x y hx hy =>
      simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, add_smul, map_add, hx, hy]

theorem cutSpectTmul_add_left {a r : ℕ} (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)
    {E : Type*} [Ring E] [Algebra k E] (d d' : cutFactorAlgebra Q Λ θ β) (e : E) :
    cutSpectTmul Q Λ θ β E (d + d') e = cutSpectTmul Q Λ θ β E d e + cutSpectTmul Q Λ θ β E d' e :=
  TensorProduct.add_tmul d d' e

/-- The input of the last stage over `E`, as a module over `D ⊗ (C ⊗ B)` by restriction along
`id ⊗ ψ`. -/
abbrev singOutTensorObj {n : ℕ} (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (ψ : C ⊗[k] B →ₐ[k] E)
    (Y' : ModuleCat.{u} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
      (singWeight n (θ ∘ Fin.castSucc)) ⊗[k]
        (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k))) :
    ModuleCat.{u} (cutSpectAlgebra (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
      (θ (Fin.last n)) (C ⊗[k] B)) :=
  (ModuleCat.restrictScalars.{u}
    (cutSpectMapAlg (a := n) (r := 1) Q Λ _ _ ψ).toRingHom).obj (singOutObj Q n Λ θ E Y')

variable {n : ℕ} {Λ : Fin (n + 1) → I →₀ ℕ} {θ : Fin (n + 1) → Multiset I}
  {ψ : C ⊗[k] B →ₐ[k] E}
  {Y : ModuleCat.{u} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
    (singWeight n (θ ∘ Fin.castSucc)) ⊗[k] (AlgCat.of k (singLast Q Λ θ ⊗[k] C) : AlgCat.{u} k))}
  {Y' : ModuleCat.{u} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
    (singWeight n (θ ∘ Fin.castSucc)) ⊗[k] (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k))}

/-- The tensor isomorphism on the input of the last stage. -/
def singOutTensorEquiv
    (G : TensorSpectatorEquiv (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
      (singWeight n (θ ∘ Fin.castSucc))) (AlgCat.of k (singLast Q Λ θ ⊗[k] C) : AlgCat.{u} k) B
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k) (singTensorMap Q Λ θ ψ) Y L Y') :
    singOutObj Q n Λ θ C Y ⊗[k] L ≃+ singOutTensorObj Q Λ θ ψ Y' :=
  AddEquiv.trans (M := singOutObj Q n Λ θ C Y ⊗[k] L) (N := Y ⊗[k] L)
    (tensorCongrOf (X := singOutObj Q n Λ θ C Y) (Y := Y) L (AddEquiv.refl _)
      fun c x => congrArg (fun r : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
          (singWeight n (θ ∘ Fin.castSucc)) ⊗[k]
            (AlgCat.of k (singLast Q Λ θ ⊗[k] C) : AlgCat.{u} k) => r • (show Y from x))
        ((singAssocOutAlg Q n Λ θ C).commutes c)) G.equiv

/-- The tensor isomorphism on the input of the last stage satisfies the tensor condition. -/
theorem isCutSpectTensor_singOutTensorEquiv
    (G : TensorSpectatorEquiv (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
      (singWeight n (θ ∘ Fin.castSucc))) (AlgCat.of k (singLast Q Λ θ ⊗[k] C) : AlgCat.{u} k) B
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k) (singTensorMap Q Λ θ ψ) Y L Y') :
    IsCutSpectTensor (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n))
      C B (singOutTensorEquiv Q G) := by
  intro d c b m v
  induction d using TensorProduct.inductionOn with
  | tmul t l => exact G.map_smul t (l ⊗ₜ[k] c) b m v
  | add x y hx hy =>
    rw [cutSpectTmul_add_left, cutSpectTmul_add_left, add_smul, add_smul,
      TensorProduct.add_tmul, map_add, hx, hy]

variable (hQ : KLRSymm Q)

/-- The partial standardization at the last cut of a tensor isomorphism, with the spectator
`C ⊗ B` changed to `E` along `ψ`. -/
def singOutTensorStd
    (G : TensorSpectatorEquiv (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
      (singWeight n (θ ∘ Fin.castSucc))) (AlgCat.of k (singLast Q Λ θ ⊗[k] C) : AlgCat.{u} k) B
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k) (singTensorMap Q Λ θ ψ) Y L Y') :
    CutStandard (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n))
        (CutSpectInput (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
          (θ (Fin.last n)) C (singOutObj Q n Λ θ C Y)) ⊗[k] L ≃+
      CutSpectStandard (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) E (singOutObj Q n Λ θ E Y') hQ :=
  (cutSpectTensorEquiv (a := n) (r := 1) Q Λ _ _ (singOutTensorEquiv Q G)
      (isCutSpectTensor_singOutTensorEquiv Q G) hQ).toAddEquiv.trans
    (cutSpectStandardEquivOf (a := n) (r := 1) Q Λ _ _ ψ (N := singOutTensorObj Q Λ θ ψ Y')
      (N' := singOutObj Q n Λ θ E Y') (AddEquiv.refl _) (fun _ _ => rfl) hQ)

/-- The last stage intertwines `(t ⊗ c) z ⊗ b v` and `(t ⊗ ψ(c ⊗ b))` applied to the image of
`z ⊗ v`. -/
theorem singOutTensorStd_smul
    (G : TensorSpectatorEquiv (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
      (singWeight n (θ ∘ Fin.castSucc))) (AlgCat.of k (singLast Q Λ θ ⊗[k] C) : AlgCat.{u} k) B
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k) (singTensorMap Q Λ θ ψ) Y L Y')
    (t : TensorProductAlgebra k Q Λ (singWeight n (θ ∘ Fin.castSucc) + θ (Fin.last n)))
    (c : C) (b : B)
    (z : CutStandard (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n))
      (CutSpectInput (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) C (singOutObj Q n Λ θ C Y))) (v : L) :
    singOutTensorStd Q hQ G (cutSpectStandardAction (a := n) (r := 1) Q Λ _ _ C
        (singOutObj Q n Λ θ C Y) hQ (t ⊗ₜ[k] c) z ⊗ₜ[k] (b • v)) =
      (t ⊗ₜ[k] ψ (c ⊗ₜ[k] b)) • singOutTensorStd Q hQ G (z ⊗ₜ[k] v) :=
  (congrArg (cutSpectStandardEquivOf (a := n) (r := 1) Q Λ _ _ ψ
      (N := singOutTensorObj Q Λ θ ψ Y') (N' := singOutObj Q n Λ θ E Y') (AddEquiv.refl _)
      (fun _ _ => rfl) hQ)
    (cutSpectTensorEquiv_smul (a := n) (r := 1) Q Λ _ _ (singOutTensorEquiv Q G)
      (isCutSpectTensor_singOutTensorEquiv Q G) hQ t c b z v)).trans
    (cutSpectStandardEquivOf_smul (a := n) (r := 1) Q Λ _ _ ψ _ _ hQ (t ⊗ₜ[k] (c ⊗ₜ[k] b)) _)

/-- The last stage of the standardization in stages of a tensor isomorphism. -/
def TensorSpectatorEquiv.singOut
    (G : TensorSpectatorEquiv (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
      (singWeight n (θ ∘ Fin.castSucc))) (AlgCat.of k (singLast Q Λ θ ⊗[k] C) : AlgCat.{u} k) B
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k) (singTensorMap Q Λ θ ψ) Y L Y') :
    TensorSpectatorEquiv (TensorProductAlgebra k Q Λ
        (singWeight n (θ ∘ Fin.castSucc) + θ (Fin.last n))) C B E ψ
      ((cutSpectFunctor (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) C hQ).obj (singOutObj Q n Λ θ C Y)) L
      ((cutSpectFunctor (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) E hQ).obj (singOutObj Q n Λ θ E Y')) where
  equiv := AddEquiv.trans
    (M := (cutSpectFunctor (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
      (θ (Fin.last n)) C hQ).obj (singOutObj Q n Λ θ C Y) ⊗[k] L)
    (N := CutStandard (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n))
      (CutSpectInput (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) C (singOutObj Q n Λ θ C Y)) ⊗[k] L)
    (tensorCongrOf
      (X := (cutSpectFunctor (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) C hQ).obj (singOutObj Q n Λ θ C Y))
      (Y := CutStandard (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) (CutSpectInput (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
          (θ (Fin.last n)) C (singOutObj Q n Λ θ C Y))) L (AddEquiv.refl _)
      fun c x => algebraMap_smul (TensorProductAlgebra k Q Λ
          (singWeight n (θ ∘ Fin.castSucc) + θ (Fin.last n)) ⊗[k] C) c
        (show CutSpectStandard (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
          (θ (Fin.last n)) C (singOutObj Q n Λ θ C Y) hQ from x))
    (singOutTensorStd Q hQ G)
  map_smul t c b z v := singOutTensorStd_smul Q hQ G t c b z v

/-- **The standardization in stages commutes with tensoring the spectator**: a tensor
isomorphism `M ⊗ L ≅ P` over `T^{λ_1}(θ_1) ⊗ ⋯ ⊗ T^{λ_n}(θ_n)`, along `ψ : C ⊗ B → E`, gives a
tensor isomorphism of the standardizations in stages over `T^λ(θ_1 + ⋯ + θ_n)`. -/
def singStdTensorEquiv : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (θ : Fin n → Multiset I) →
    {C E : AlgCat.{u} k} → (ψ : C ⊗[k] B →ₐ[k] E) →
    {M : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] C)} → {P : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E)} →
    TensorSpectatorEquiv (singAlg Q n Λ θ) C B E ψ M L P →
    TensorSpectatorEquiv (TensorProductAlgebra k Q Λ (singWeight n θ)) C B E ψ
      ((singStd Q hQ n Λ θ C).obj M) L ((singStd Q hQ n Λ θ E).obj P)
  | 0, _, _, _, _, _, _, _, F => F
  | n + 1, Λ, θ, _, _, ψ, _, _, F =>
    TensorSpectatorEquiv.singOut Q hQ (singStdTensorEquiv n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
      (singTensorMap Q Λ θ ψ) (TensorSpectatorEquiv.singIn Q F))

end Singletons

end Categorification.Stendhal
