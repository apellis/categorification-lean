/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutTopOneInd
import Categorification.KLR.Reindex

/-!
# The identity-shuffle part of a Mackey layer as an induced corner

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5; Khovanov–Lauda I
(arXiv:0803.4121v2), §2.6, Proposition 2.18.

`R(γ) ⊗ R(δ)` acts on the bottom corner `E N` (`E = quadBot 1`) through
`c ↦ quadBot (1 ⊗ c)` (`botCornerModuleRight`, a local instance), and `botTensorEquiv` is
linear for this action and for the action on `BotN` through `1 ⊗ c`
(`botTensorEquivRight`). With `topOneIndEquiv` this gives

  `mackeyTopOneSpan q N ≅ R(γ + δ) 1_{γ,δ} ⊗_{R(γ) ⊗ R(δ)} E N`

(`topOneCornerEquiv`), the form of the identity-shuffle part that is compared at the two cuts
of L5.

To compare `R(γ + δ)` at the two cuts, whose labels are those of a common multiset read along
two injections, `SeqRelabel.ofInjectivePair` relabels the sequences of `μ.map f` (data `Q₁`)
by those of `μ.map g` (data `Q₂`) when `Q₂ (g a) (g b) = Q₁ (f a) (f b)`.

Webster's proof does not spell this out. No new hypothesis.

## Main results

* `KLR.KLRAlgebra.botCornerModuleRight`, `KLR.KLRAlgebra.botTensorEquivRight`,
  `KLR.KLRAlgebra.topOneCornerEquiv`, `KLR.KLRAlgebra.topOneCornerEquiv_tmul`.
* `KLR.SeqRelabel.ofInjectivePair`, `KLR.SeqRelabel.ofInjectivePair_equiv_map`.
-/

noncomputable section

namespace Categorification.KLR

open Equiv TypeA MulOpposite
open scoped TensorProduct

/-! ### Relabelling along two injections -/

section Pair

variable {k : Type*} [CommRing k] {J I₁ I₂ : Type*} [DecidableEq J] [DecidableEq I₁]
  [DecidableEq I₂] {f : J → I₁} {g : J → I₂}

variable (k) in
/-- **Relabelling along two injections**: the sequences of `μ.map f` (data `Q₁`) are those of
`μ.map g` (data `Q₂`), `f ∘ 𝐣 ↦ g ∘ 𝐣`, when `Q₂ (g a) (g b) = Q₁ (f a) (f b)`. -/
def SeqRelabel.ofInjectivePair (hf : Function.Injective f) (hg : Function.Injective g)
    (Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k) (Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k)
    (hQ : ∀ a b, Q₂ (g a) (g b) = Q₁ (f a) (f b)) (μ : Multiset J) :
    SeqRelabel k Q₁ Q₂ (μ.map f) (μ.map g) where
  card_eq := by rw [Multiset.card_map, Multiset.card_map]
  equiv := (Seq.mapEquiv hf μ).symm.trans (Seq.mapEquiv hg μ)
  equiv_smul j i := by
    obtain ⟨i, rfl⟩ := (Seq.mapEquiv hf μ).surjective i
    have h1 := (SeqRelabel.ofInjective hf Q₁ μ).equiv_smul j i
    have h2 := (SeqRelabel.ofInjective hg Q₂ μ).equiv_smul j i
    change Seq.mapEquiv hf μ _ = _ • Seq.mapEquiv hf μ i at h1
    change Seq.mapEquiv hg μ _ = _ • Seq.mapEquiv hg μ i at h2
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply, ← h1,
      Equiv.symm_apply_apply, h2]
  lbl_eq_iff i a b := by
    obtain ⟨i, rfl⟩ := (Seq.mapEquiv hf μ).surjective i
    rw [Equiv.trans_apply, Equiv.symm_apply_apply]
    simp only [Seq.mapEquiv_apply, Seq.map_lbl, Fin.cast_cast, hf.eq_iff, hg.eq_iff]
  Q_eq i a b _ := by
    obtain ⟨i, rfl⟩ := (Seq.mapEquiv hf μ).surjective i
    rw [Equiv.trans_apply, Equiv.symm_apply_apply]
    simp only [Seq.mapEquiv_apply, Seq.map_lbl, Fin.cast_cast]
    exact hQ _ _

omit [DecidableEq J] [DecidableEq I₁] [DecidableEq I₂] in
theorem SeqRelabel.ofInjectivePair_equiv_map (hf : Function.Injective f)
    (hg : Function.Injective g) (Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k)
    (Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k) (hQ : ∀ a b, Q₂ (g a) (g b) = Q₁ (f a) (f b))
    {μ : Multiset J} (i : Seq μ) :
    (SeqRelabel.ofInjectivePair k hf hg Q₁ Q₂ hQ μ).equiv (Seq.map f i) = Seq.map g i := by
  change Seq.mapEquiv hg μ ((Seq.mapEquiv hf μ).symm (Seq.mapEquiv hf μ i)) = _
  rw [Equiv.symm_apply_apply]
  rfl

end Pair

/-! ### The corner form of the identity-shuffle part -/

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

variable {ν ν' ν'' ν''' : Multiset I} (q : MackeyQuad ν ν' ν'' ν''')
  (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]
  [IsScalarTower k (TensorKLR Q ν'' ν''') N]

/-- `MackeyBot_λ ⊗_{R''} N`, the right factor of a Mackey layer. -/
local notation "BotN" => BalancedTensor k (QuadAlg Q q) (TensorKLR Q ν'' ν''') (MackeyBot Q q) N

attribute [local instance] botNModuleRight

theorem quadBot_one_tmul_mul (c c' : TensorKLR Q q.γ q.δ) :
    (quadBot q (((1 : TensorKLR Q q.α q.β) ⊗ₜ (c * c') : QuadAlg Q q)) :
      TensorKLR Q ν'' ν''') = quadBot q ((1 : TensorKLR Q q.α q.β) ⊗ₜ c) *
        quadBot q ((1 : TensorKLR Q q.α q.β) ⊗ₜ c') := by
  rw [← quadBot_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- `R(γ) ⊗ R(δ)` acts on the corner `E N` through `c ↦ quadBot (1 ⊗ c)`. -/
@[instance_reducible]
def botCornerModuleRight : Module (TensorKLR Q q.γ q.δ) (botCorner Q q N) where
  smul c n := ⟨(quadBot q ((1 : TensorKLR Q q.α q.β) ⊗ₜ c) : TensorKLR Q ν'' ν''') • (n : N),
    quadBot_smul_mem_botCorner q N _ _⟩
  one_smul n := Subtype.ext (by
    change (quadBot q ((1 : TensorKLR Q q.α q.β) ⊗ₜ (1 : TensorKLR Q q.γ q.δ)) :
      TensorKLR Q ν'' ν''') • (n : N) = n
    rw [← Algebra.TensorProduct.one_def]
    exact n.2)
  mul_smul c c' n := Subtype.ext (by
    change (quadBot q ((1 : TensorKLR Q q.α q.β) ⊗ₜ (c * c')) : TensorKLR Q ν'' ν''') •
      (n : N) = _ • (_ • (n : N))
    rw [quadBot_one_tmul_mul, mul_smul])
  smul_zero c := Subtype.ext (smul_zero _)
  smul_add c n n' := Subtype.ext (smul_add _ (n : N) n')
  add_smul c c' n := Subtype.ext (by
    change (quadBot q ((1 : TensorKLR Q q.α q.β) ⊗ₜ (c + c')) : TensorKLR Q ν'' ν''') •
      (n : N) = _ • (n : N) + _ • (n : N)
    rw [TensorProduct.tmul_add, map_add, add_smul])
  zero_smul n := Subtype.ext (by
    change (quadBot q ((1 : TensorKLR Q q.α q.β) ⊗ₜ (0 : TensorKLR Q q.γ q.δ)) :
      TensorKLR Q ν'' ν''') • (n : N) = 0
    rw [TensorProduct.tmul_zero, map_zero, zero_smul])

attribute [local instance] botCornerModuleRight

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
/-- The action of `R(γ) ⊗ R(δ)` on `BotN` is `k`-bilinear. -/
theorem botNModuleRight_isScalarTower :
    IsScalarTower k (TensorKLR Q q.γ q.δ) BotN where
  smul_assoc c X y := by
    change (((1 : TensorKLR Q q.α q.β) ⊗ₜ (c • X) : QuadAlg Q q) • y) = c • (_ • y)
    rw [TensorProduct.tmul_smul, smul_assoc]
    rfl

/-- The action of `R(γ) ⊗ R(δ)` on `E N` is `k`-bilinear. -/
theorem botCornerModuleRight_isScalarTower :
    IsScalarTower k (TensorKLR Q q.γ q.δ) (botCorner Q q N) where
  smul_assoc c X n := Subtype.ext (by
    change (quadBot q ((1 : TensorKLR Q q.α q.β) ⊗ₜ (c • X)) : TensorKLR Q ν'' ν''') • (n : N) =
      c • ((quadBot q ((1 : TensorKLR Q q.α q.β) ⊗ₜ X) : TensorKLR Q ν'' ν''') • (n : N))
    rw [TensorProduct.tmul_smul, map_smul, smul_assoc])

attribute [local instance] botNModuleRight_isScalarTower botCornerModuleRight_isScalarTower

theorem coe_botCornerModuleRight_smul (c : TensorKLR Q q.γ q.δ) (n : botCorner Q q N) :
    ((c • n : botCorner Q q N) : N) =
      (quadBot q ((1 : TensorKLR Q q.α q.β) ⊗ₜ c) : TensorKLR Q ν'' ν''') • (n : N) := rfl

/-- `botTensorEquiv` is `R(γ) ⊗ R(δ)`-linear. -/
def botTensorEquivRight : BotN ≃ₗ[TensorKLR Q q.γ q.δ] botCorner Q q N :=
  { botTensorEquiv Q q N with
    map_smul' := fun c y => Subtype.ext (by
      change (botTensorEquiv Q q N (((1 : TensorKLR Q q.α q.β) ⊗ₜ c : QuadAlg Q q) • y) : N) = _
      rw [botTensorEquiv_smul]
      rfl) }

theorem botTensorEquivRight_apply (y : BotN) :
    botTensorEquivRight q N y = botTensorEquiv Q q N y := rfl

variable (hsym : KLRSymm Q)

/-- **`mackeyTopOneSpan q N ≅ R(γ + δ) 1_{γ,δ} ⊗_{R(γ) ⊗ R(δ)} E N`**: the identity-shuffle
part of a Mackey layer is induced from the bottom corner. -/
def topOneCornerEquiv : Ind Q q.γ q.δ (botCorner Q q N) ≃ₗ[k] mackeyTopOneSpan (Q := Q) q N :=
  ((BalancedTensor.congrRight (botTensorEquivRight q N)).restrictScalars k).symm.trans
    (topOneIndEquiv q N hsym)

/-- `topOneCornerEquiv (b ⊗ n) = (1 ⊗ b) · (1_λ ⊗ (E ⊗ n))`. -/
theorem topOneCornerEquiv_tmul (b : IndBimod Q q.γ q.δ) (n : botCorner Q q N) :
    (topOneCornerEquiv q N hsym (BalancedTensor.tmul b n) : MackeyLeftInd Q N q) =
      (((1 : KLRAlgebra k Q ν) ⊗ₜ castAlg Q q.h₂ (b : KLRAlgebra k Q (q.γ + q.δ)) :
        TensorKLR Q ν ν') • (BalancedTensor.tmul (mackeyTopOne q)
          (BalancedTensor.tmul (mackeyBotOne Q q) (n : N) : BotN) : MackeyLeftInd Q N q)) :=
  topOneIndMap_tmul q N b _

/-- `R(ν')` acts on `topOneCornerEquiv` through `R(γ + δ)`. -/
theorem topOneCornerEquiv_smul (r : KLRAlgebra k Q (q.γ + q.δ))
    (x : Ind Q q.γ q.δ (botCorner Q q N)) :
    (topOneCornerEquiv q N hsym (r • x) : MackeyLeftInd Q N q) =
      (((1 : KLRAlgebra k Q ν) ⊗ₜ castAlg Q q.h₂ r : TensorKLR Q ν ν') •
        (topOneCornerEquiv q N hsym x : MackeyLeftInd Q N q)) := by
  change topOneIndMap (Q := Q) q N
      ((BalancedTensor.congrRight (botTensorEquivRight q N)).symm (r • x)) =
    _ • topOneIndMap (Q := Q) q N ((BalancedTensor.congrRight (botTensorEquivRight q N)).symm x)
  rw [map_smul, topOneIndMap_smul]

end KLRAlgebra

end Categorification.KLR
