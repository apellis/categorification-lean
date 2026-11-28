/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutLeadingLayer

/-!
# The top algebra on the identity-shuffle spans of the leading Mackey layers

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the loading
idempotents on the leading summands, (T_w) of the handoff).

On the identity-shuffle part `mackeyTopOneSpan q N ≅ Ind_{γ,δ}(E N)` of a Mackey layer
(`topOneCornerEquiv`), an element `ι_{α,β}(X) ⊗ ι_{γ,δ}(r)` of the top algebra
`R(ν) ⊗ R(ν')` acts by `r` on the induced module and by `quadBot (X ⊗ 1)` on the bottom
corner `E N` (`botCornerLeftEnd`, an `R(γ) ⊗ R(δ)`-linear endomorphism of `E N`):
`topOneCornerEquiv_mapRight`.

`cutPlusInd` is natural in the bottom module (`cutPlusInd_mapRight`). Hence the comparison
`leadingTopOneSpanEquiv` of the identity-shuffle spans of the leading data carries the action of
`ι(X') ⊗ ι(r)` at `S_cut(Res X)` to the action of `ι(X₊) ⊗ ι(ρ r)` at `S_+(X)`, `ρ` the
relabelling `cutPlusRelabel`, whenever `plusBotCornerEquiv` carries `quadBot (X₊ ⊗ 1)` to
`quadBot (X' ⊗ 1)` on the bottom corners (`leadingTopOneSpanEquiv_smul`; with any bottom
endomorphisms: `leadingTopOneSpanEquiv_mapRight`). The intertwining argument `hX` is a datum of
that intermediate statement, not a hypothesis of Lemma 7.19.

For the head part `X₊ = ρ x ⊗ 1`, `X' = x ⊗ 1` (`x ∈ R(q'.α)`, `q.α = q'.α.map φ`:
`leadingQuad_α_eq_map`) the datum is discharged: on the bottom corner `quadBot ((x ⊗ 1) ⊗ 1)`
acts as `ι_{α,γ}(x ⊗ 1) ⊗ 1` (`quadBot_tmul_one_smul_of_mem`), hence through the identity
coordinate by its head factor (`botCornerBlocksEquiv_leftEnd`), and the head factors at the two
cuts agree (`relabel_cutPrefixProjection_leading_head_left`). So `plusBotCornerEquiv`
intertwines the head parts (`plusBotCornerEquiv_leftEnd_head`), and
`leadingTopOneSpanEquiv_head_smul` is (T_w) without the window factor. The window factor
`1 ⊗ e(w)` of `q.α + q.β` acts on `X` through the middle block; it is not treated here.

Webster's proof does not spell this out. No new hypothesis.

## Main definitions

* `KLR.KLRAlgebra.botCornerLeftEnd`.

## Main results

* `KLR.KLRAlgebra.tmul_one_smul_tmul_mackeyBotOne`, `KLR.KLRAlgebra.topOneCornerEquiv_mapRight`,
  `KLR.KLRAlgebra.topOneCornerEquiv_tmul_smul`, `KLR.KLRAlgebra.quadBot_tmul_one_smul_of_mem`,
  `KLR.KLRAlgebra.castKLR_concat_tmul_one_ofParams`.
* `Stendhal.botCornerBlocksEquiv_leftEnd`.
* `Stendhal.CupCap.cutPlusInd_mapRight`, `Stendhal.CupCap.leadingQuad_α_eq_map`,
  `Stendhal.CupCap.relabel_cutPrefixProjection_leading_head_left`,
  `Stendhal.CupCap.plusBotCornerEquiv_leftEnd_head`,
  `Stendhal.CupCap.leadingTopOneSpanEquiv_mapRight`, `Stendhal.CupCap.leadingTopOneSpanEquiv_smul`,
  `Stendhal.CupCap.leadingTopOneSpanEquiv_head_smul`.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' ν'' ν''' : Multiset I}
  (q : MackeyQuad ν ν' ν'' ν''')
  (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]
  [IsScalarTower k (TensorKLR Q ν'' ν''') N]

local notation "BotN" => BalancedTensor k (QuadAlg Q q) (TensorKLR Q ν'' ν''') (MackeyBot Q q) N

attribute [local instance] botCornerModuleRight botNModuleRight_isScalarTower
  botCornerModuleRight_isScalarTower

/-- `X ⊗ 1` and `1 ⊗ c` commute in `R(α) ⊗ R(β) ⊗ R(γ) ⊗ R(δ)`. -/
theorem quadBot_tmul_one_mul_comm (X : TensorKLR Q q.α q.β) (c : TensorKLR Q q.γ q.δ) :
    quadBot q (X ⊗ₜ (1 : TensorKLR Q q.γ q.δ)) * quadBot q ((1 : TensorKLR Q q.α q.β) ⊗ₜ c) =
      quadBot q ((1 : TensorKLR Q q.α q.β) ⊗ₜ c) * quadBot q (X ⊗ₜ (1 : TensorKLR Q q.γ q.δ)) := by
  rw [← quadBot_mul, ← quadBot_mul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_one, one_mul]

/-- **The left factor on the bottom corner**: `n ↦ quadBot (X ⊗ 1) n` on `E N`, linear for the
action of `R(γ) ⊗ R(δ)` through `quadBot (1 ⊗ c)`. -/
def botCornerLeftEnd (X : TensorKLR Q q.α q.β) :
    botCorner Q q N →ₗ[TensorKLR Q q.γ q.δ] botCorner Q q N where
  toFun n := ⟨(quadBot q (X ⊗ₜ (1 : TensorKLR Q q.γ q.δ)) : TensorKLR Q ν'' ν''') • (n : N),
    quadBot_smul_mem_botCorner q N _ _⟩
  map_add' n n' := Subtype.ext (smul_add _ (n : N) n')
  map_smul' c n := Subtype.ext (by
    change (quadBot q (X ⊗ₜ (1 : TensorKLR Q q.γ q.δ)) : TensorKLR Q ν'' ν''') •
        ((quadBot q ((1 : TensorKLR Q q.α q.β) ⊗ₜ c) : TensorKLR Q ν'' ν''') • (n : N)) =
      (quadBot q ((1 : TensorKLR Q q.α q.β) ⊗ₜ c) : TensorKLR Q ν'' ν''') •
        ((quadBot q (X ⊗ₜ (1 : TensorKLR Q q.γ q.δ)) : TensorKLR Q ν'' ν''') • (n : N))
    rw [smul_smul, smul_smul, quadBot_tmul_one_mul_comm])

theorem coe_botCornerLeftEnd (X : TensorKLR Q q.α q.β) (n : botCorner Q q N) :
    (botCornerLeftEnd q N X n : N) =
      (quadBot q (X ⊗ₜ (1 : TensorKLR Q q.γ q.δ)) : TensorKLR Q ν'' ν''') • (n : N) := rfl

/-- `(X ⊗ 1) · (E ⊗ n) = E ⊗ quadBot (X ⊗ 1) n` in `MackeyBot_λ ⊗_{R''} N`, for `n ∈ E N`. -/
theorem tmul_one_smul_tmul_mackeyBotOne (X : TensorKLR Q q.α q.β) (n : botCorner Q q N) :
    ((X ⊗ₜ (1 : TensorKLR Q q.γ q.δ) : QuadAlg Q q) •
      (BalancedTensor.tmul (mackeyBotOne Q q) (n : N) : BotN)) =
      BalancedTensor.tmul (mackeyBotOne Q q) (botCornerLeftEnd q N X n : N) := by
  apply (botTensorEquiv Q q N).injective
  apply Subtype.ext
  rw [botTensorEquiv_smul, botTensorEquiv_tmul, botTensorEquiv_tmul, coe_botCornerLeftEnd]
  change _ • ((quadBot q 1 : TensorKLR Q ν'' ν''') • (n : N)) =
    (quadBot q 1 : TensorKLR Q ν'' ν''') • (_ • (n : N))
  rw [show (quadBot q 1 : TensorKLR Q ν'' ν''') • (n : N) = n from n.2, smul_smul,
    ← quadBot_mul, one_mul]

/-- On the bottom corner, `quadBot ((x ⊗ 1) ⊗ 1)` acts as `ι_{α,γ}(x ⊗ 1) ⊗ 1`. -/
theorem quadBot_tmul_one_smul_of_mem (x : KLRAlgebra k Q q.α) {n : N}
    (hn : n ∈ botCorner Q q N) :
    (quadBot q ((x ⊗ₜ (1 : KLRAlgebra k Q q.β)) ⊗ₜ (1 : TensorKLR Q q.γ q.δ)) :
        TensorKLR Q ν'' ν''') • n =
      (castAlg Q q.h₃ (concat Q q.α q.γ (x ⊗ₜ 1)) ⊗ₜ (1 : KLRAlgebra k Q ν''') :
        TensorKLR Q ν'' ν''') • n := by
  conv_rhs => rw [← (mem_botCorner q N).1 hn, smul_smul]
  congr 1
  rw [show (1 : QuadAlg Q q) = ((1 : KLRAlgebra k Q q.α) ⊗ₜ (1 : KLRAlgebra k Q q.β)) ⊗ₜ
      ((1 : KLRAlgebra k Q q.γ) ⊗ₜ (1 : KLRAlgebra k Q q.δ)) from rfl,
    show (1 : TensorKLR Q q.γ q.δ) = (1 : KLRAlgebra k Q q.γ) ⊗ₜ (1 : KLRAlgebra k Q q.δ)
      from rfl, quadBot_tmul, quadBot_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    ← map_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]

variable (hsym : KLRSymm Q)

/-- **The parabolic part of the first top factor on the identity-shuffle span**: through
`topOneCornerEquiv`, `ι_{α,β}(X) ⊗ 1` acts by `quadBot (X ⊗ 1)` on the bottom corner. -/
theorem topOneCornerEquiv_mapRight (X : TensorKLR Q q.α q.β)
    (x : Ind Q q.γ q.δ (botCorner Q q N)) :
    ((castAlg Q q.h₁ (concat Q q.α q.β X) ⊗ₜ (1 : KLRAlgebra k Q ν') : TensorKLR Q ν ν') •
      (topOneCornerEquiv q N hsym x : MackeyLeftInd Q N q)) =
      (topOneCornerEquiv q N hsym
        (BalancedTensor.mapRight (botCornerLeftEnd q N X) x) : MackeyLeftInd Q N q) := by
  induction x using BalancedTensor.induction_on with
  | zero => simp only [map_zero, ZeroMemClass.coe_zero, smul_zero]
  | add x x' hx hx' => simp only [map_add, Submodule.coe_add, smul_add, hx, hx']
  | tmul b n =>
    rw [BalancedTensor.mapRight_tmul, topOneCornerEquiv_tmul, topOneCornerEquiv_tmul, smul_smul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      ← one_mul (castAlg Q q.h₁ (concat Q q.α q.β X)),
      ← mul_one (castAlg Q q.h₂ (b : KLRAlgebra k Q (q.γ + q.δ))),
      ← Algebra.TensorProduct.tmul_mul_tmul, mul_smul,
      castAlg_concat_tmul_one_smul_tmul_mackeyTopOne, tmul_one_smul_tmul_mackeyBotOne, mul_one]

/-- **The top algebra on the identity-shuffle span**: `ι_{α,β}(X) ⊗ ι_{γ,δ}(r)` acts on
`topOneCornerEquiv x` by `r` on the induced module and `quadBot (X ⊗ 1)` on the bottom corner. -/
theorem topOneCornerEquiv_tmul_smul (X : TensorKLR Q q.α q.β)
    (r : KLRAlgebra k Q (q.γ + q.δ)) (x : Ind Q q.γ q.δ (botCorner Q q N)) :
    ((castAlg Q q.h₁ (concat Q q.α q.β X) ⊗ₜ castAlg Q q.h₂ r : TensorKLR Q ν ν') •
      (topOneCornerEquiv q N hsym x : MackeyLeftInd Q N q)) =
      (topOneCornerEquiv q N hsym
        (r • BalancedTensor.mapRight (botCornerLeftEnd q N X) x) : MackeyLeftInd Q N q) := by
  rw [topOneCornerEquiv_smul, ← topOneCornerEquiv_mapRight, smul_smul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

section OfParams

variable {I₁ : Type*} [DecidableEq I₁] {Q₁ Q₁' : I₁ → I₁ → MvPolynomial (Fin 2) k}

/-- `ι_{α,γ}(· ⊗ 1)` commutes with the identity relabelling between parameters. -/
theorem castKLR_concat_tmul_one_ofParams (hQ : ∀ a b, a ≠ b → Q₁' a b = Q₁ a b)
    {α γ μ : Multiset I₁} (h : α + γ = μ) (c : KLRAlgebra k Q₁ α) :
    castKLR Q₁' h (concat Q₁' α γ (relabelHom (SeqRelabel.ofParams hQ α) c ⊗ₜ 1)) =
      relabelHom (SeqRelabel.ofParams hQ μ) (castKLR Q₁ h (concat Q₁ α γ (c ⊗ₜ 1))) := by
  subst h
  simp only [castKLR_rfl]
  rw [relabelHom_concat (SeqRelabel.ofParams hQ α) (SeqRelabel.ofParams hQ γ)
    (SeqRelabel.ofParams hQ (α + γ)) (fun _ _ => rfl), Algebra.TensorProduct.map_tmul, map_one]

end OfParams

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

section Blocks

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + (m + r)) → I →₀ ℕ)
  (θ β γ : Multiset I)

local notation "αi" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight m β)
local notation "δi" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd m)) (stendhalWeight r γ)
local notation "cR" => Sum.map (id : I → I) (Fin.natAdd a : Fin (m + r) → Fin (a + (m + r)))
local notation "So" => stendhalQ Q Λ

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (blocksFactorAlgebra Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N]
  (hQ : KLRSymm Q)

local notation "Nₒ" => CutInput Q Λ θ (β + γ) (BlocksMid Q Λ θ β γ N hQ)
local notation "Inner" => CutInput Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)
local notation "CSi" => CutStandard Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)

variable {ν ν' : Multiset (I ⊕ Fin (a + (m + r)))} {q : MackeyQuad ν ν'
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (m + r))) (stendhalWeight a θ))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight (m + r) (β + γ)))}

/-- **The head part of the first top factor on the bottom corner at the outer cut**: read
through the identity coordinate `botCornerBlocksEquiv`, `quadBot ((x ⊗ 1) ⊗ 1)` acts by the head
factor of `ι_{α,γ}(x ⊗ 1)`. -/
theorem botCornerBlocksEquiv_leftEnd (hβ : q.β = (αi).map cR) (x : KLRAlgebra k So q.α)
    (z : botCorner So q Nₒ) :
    (botCornerBlocksEquiv Q Λ θ β γ N hQ hβ
        (botCornerLeftEnd q Nₒ (x ⊗ₜ (1 : KLRAlgebra k So q.β)) z) : Inner) =
      blocksHeadEnd Q Λ θ β γ N
        (cutPrefixProjection (a := a) (r := m + r) Q Λ θ
          (castAlg So q.h₃ (concat So q.α q.γ (x ⊗ₜ 1))))
        (botCornerBlocksEquiv Q Λ θ β γ N hQ hβ z : Inner) := by
  rw [botCornerBlocksEquiv_apply, botCornerBlocksEquiv_apply]
  have hz : (botCornerLeftEnd q Nₒ (x ⊗ₜ (1 : KLRAlgebra k So q.β)) z : Nₒ) =
      (castAlg So q.h₃ (concat So q.α q.γ (x ⊗ₜ 1)) ⊗ₜ
        (1 : KLRAlgebra k So (Multiset.map (Sum.map (id : I → I) (Fin.natAdd a))
          (stendhalWeight (m + r) (β + γ)))) : TensorKLR So _ _) • (z : Nₒ) :=
    quadBot_tmul_one_smul_of_mem q Nₒ x z.2
  rw [hz]
  change (cutStandardShuffleEquiv Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ
      (blocksMidAction Q Λ θ β γ N hQ (cutInputMap Q Λ θ (β + γ)
        (castAlg So q.h₃ (concat So q.α q.γ (x ⊗ₜ 1)) ⊗ₜ
          (1 : KLRAlgebra k So (Multiset.map (Sum.map (id : I → I) (Fin.natAdd a))
            (stendhalWeight (m + r) (β + γ))))))
        ((z : Nₒ) : CSi)) : Shuffle (Seq.card_add' αi δi) → Inner) shufOne = _
  simp only [cutInputMap, Algebra.TensorProduct.map_tmul, map_one, blocksMidAction,
    Algebra.TensorProduct.lift_tmul, mul_one]
  exact cutStandardShuffleEquiv_blocksHeadAction Q Λ θ β γ N hQ _ _ _

end Blocks

end Categorification.Stendhal

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

section Natural

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  {γ' δ' : Multiset (I ⊕ Fin (j + (ℓ - j)))}
  {γ δ : Multiset (I ⊕ Fin (j + (2 + (ℓ - j))))}
  (hγ : γ'.map (cutToPlusColour (I := I) j hj) = γ)
  (hδ : δ'.map (cutToPlusColour (I := I) j hj) = δ)
  {N' N : Type*} [AddCommGroup N'] [Module k N']
  [Module (TensorKLR (stendhalQ Q (cutLabels j hj Λ)) γ' δ') N']
  [IsScalarTower k (TensorKLR (stendhalQ Q (cutLabels j hj Λ)) γ' δ') N']
  [AddCommGroup N] [Module k N]
  [Module (TensorKLR (stendhalQ Q (plusBlockLabels Λ Λc j hj)) γ δ) N]
  [IsScalarTower k (TensorKLR (stendhalQ Q (plusBlockLabels Λ Λc j hj)) γ δ) N]
  (g : N' ≃ₗ[k] N) (hg : ∀ (t : TensorKLR (stendhalQ Q (cutLabels j hj Λ)) γ' δ') (n : N'),
    g (t • n) = tensorRelabel (cutPlusRelabel j hj Q Λ Λc hγ)
      (cutPlusRelabel j hj Q Λ Λc hδ) t • g n)

/-- **`cutPlusInd` is natural in the bottom module**: for `g ∘ f' = f ∘ g`,
`cutPlusInd ∘ Ind(f') = Ind(f) ∘ cutPlusInd`. -/
theorem cutPlusInd_mapRight
    (f' : N' →ₗ[TensorKLR (stendhalQ Q (cutLabels j hj Λ)) γ' δ'] N')
    (f : N →ₗ[TensorKLR (stendhalQ Q (plusBlockLabels Λ Λc j hj)) γ δ] N)
    (hf : ∀ n, g (f' n) = f (g n)) (y : Ind (stendhalQ Q (cutLabels j hj Λ)) γ' δ' N') :
    cutPlusInd j hj Q Λ Λc hγ hδ g hg (BalancedTensor.mapRight f' y) =
      BalancedTensor.mapRight f (cutPlusInd j hj Q Λ Λc hγ hδ g hg y) := by
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add y y' hy hy' => simp only [map_add, hy, hy']
  | tmul m n => rw [BalancedTensor.mapRight_tmul, cutPlusInd_tmul, cutPlusInd_tmul,
      BalancedTensor.mapRight_tmul, hf]

end Natural

section Leading

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)

attribute [local instance] botCornerModuleRight botCornerModuleRight_isScalarTower

variable (X : Type*) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)

local notation "Yc" => CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
local notation "Nₒ" => CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
  (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)
local notation "Inner" => CutInput Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) ν₀ γ
  (BlocksInner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X))

variable (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))
  (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
  (q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))))
  (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
  (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
  (hq' : q'.β = 0)

omit [DecidableEq I] in
include hs hq hq' in
/-- The head weights of the leading data: `q'.α` and `q.α` are one weight `αh` of the head
labels, read in `λ` and in `λ⁺`. -/
theorem exists_leadingQuad_α :
    ∃ αh : Multiset (I ⊕ Fin j),
      q'.α = αh.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) ∧
      q.α = αh.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) := by
  obtain ⟨αh, hαh⟩ := exists_headWeight_prefixWt (hj := hj) s hs
  refine ⟨αh, ?_, ?_⟩
  · have h1 := q'.h₁
    rw [hq', add_zero] at h1
    refine h1.trans ?_
    rw [prefixWt_cutLoading, hαh, Multiset.map_map]
    refine Multiset.map_congr rfl fun x _ => ?_
    rcases x with b | u
    · rfl
    · exact congrArg Sum.inr (Fin.ext rfl)
  · have h1 := q.h₁.trans (prefixWt_windowLoading s w)
    rw [hq, hαh, Multiset.map_map, add_left_inj] at h1
    rw [h1]
    refine Multiset.map_congr rfl fun x _ => ?_
    rcases x with b | u
    · rfl
    · refine congrArg Sum.inr (Fin.ext ?_)
      simp [oldRed, u.2]

omit [DecidableEq I] in
include hs hq hq' in
/-- `q.α = q'.α.map φ` for the leading data, `φ = cutToPlusColour`. -/
theorem leadingQuad_α_eq_map : q'.α.map (cutToPlusColour (I := I) j hj) = q.α := by
  obtain ⟨αh, hα', hα⟩ := exists_leadingQuad_α s w hs q hq q' hq'
  rw [hα', hα, Multiset.map_map, cutToPlusColour_comp_castAdd]

include hs hq hq' in
/-- **(H) for the first factor**: for `a ∈ R(q'.α)`, the head factor of `ι_{q.α,q.γ}(a ⊗ 1)` at
the outer cut of `S_+` (`a` relabelled along `cutPlusRelabel`), relabelled along
`plusBlockLabels_head`, is the head factor of `ι_{q'.α,q'.γ}(a ⊗ 1)` at the cut of `S_cut`. -/
theorem relabel_cutPrefixProjection_leading_head_left (x : KLRAlgebra k Sc q'.α) :
    relabelTensorProductAlgebra Q (plusBlockLabels_head Λ Λc j hj) θ
        (cutPrefixProjection (a := j) (r := 2 + (ℓ - j)) Q (plusBlockLabels Λ Λc j hj) θ
          (castAlg Sp q.h₃ (concat Sp q.α q.γ
            (relabelHom (cutPlusRelabel j hj Q Λ Λc
              (leadingQuad_α_eq_map s w hs q hq q' hq')) x ⊗ₜ 1)))) =
      cutPrefixProjection (a := j) (r := ℓ - j) Q (cutLabels j hj Λ) θ
        (castAlg Sc q'.h₃ (concat Sc q'.α q'.γ (x ⊗ₜ 1))) := by
  obtain ⟨αh, hα', hα⟩ := exists_leadingQuad_α s w hs q hq q' hq'
  have hinj : Function.Injective (Sum.map (id : I → I) (Fin.castAdd (ℓ - j) : Fin j → _)) :=
    Sum.map_injective.2 ⟨Function.injective_id, Fin.castAdd_injective j (ℓ - j)⟩
  have hle : αh ≤ stendhalWeight j θ := by
    have h3 := Multiset.le_add_right q'.α q'.γ
    rw [q'.h₃, hα'] at h3
    exact (Multiset.map_le_map_iff hinj).1 h3
  have hh : αh + (stendhalWeight j θ - αh) = stendhalWeight j θ := add_tsub_cancel_of_le hle
  have hγ' : (stendhalWeight j θ - αh).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) =
      q'.γ := by
    have h3 : αh.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) + q'.γ =
        αh.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) +
          (stendhalWeight j θ - αh).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) := by
      rw [← Multiset.map_add, hh, ← hα', q'.h₃]
    exact (add_left_cancel h3).symm
  have hγp : (stendhalWeight j θ - αh).map
      (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) = q.γ := by
    rw [leadingQuad_γ_eq_map j hj s w q hq q' hq', ← hγ', Multiset.map_map,
      cutToPlusColour_comp_castAdd]
  obtain ⟨c, rfl⟩ : ∃ c, relabelHom (subfamilyRelabel Q (cutLabels j hj Λ)
      (Fin.castAdd_injective _ _) hα'.symm) c = x :=
    ⟨(relabelEquiv _).symm x, (relabelEquiv _).apply_symm_apply x⟩
  rw [cutPlusRelabel_subfamilyRelabel_head j hj Q Λ Λc hα'.symm _ hα.symm]
  have kp := redSubfamilyProjection_castAlg_concat Q (plusBlockLabels Λ Λc j hj)
    (Fin.castAdd_injective _ _) θ hh hα.symm hγp q.h₃
    (relabelHom (SeqRelabel.ofParams (fun a b _ => stendhalQ_head_eq j hj Q Λ Λc a b) _) c ⊗ₜ 1)
  have kc := redSubfamilyProjection_castAlg_concat Q (cutLabels j hj Λ)
    (Fin.castAdd_injective _ _) θ hh hα'.symm hγ' q'.h₃ (c ⊗ₜ 1)
  rw [Algebra.TensorProduct.map_tmul, map_one] at kp kc
  rw [kp, kc, castKLR_concat_tmul_one_ofParams]
  exact relabelTensorProductAlgebra_tensorOfKLR_ofParams Q θ (plusBlockLabels_head Λ Λc j hj) _ _

/-- **The bottom corners intertwine the head part of the first top factor** (Webster v3,
Lemma 7.19, trace half, step L5): `plusBotCornerEquiv` carries `quadBot ((ρ x ⊗ 1) ⊗ 1)` at the
outer cut of `S_+(X)` to `quadBot ((x ⊗ 1) ⊗ 1)` at the cut of `S_cut(Res X)`, for
`x ∈ R(q'.α)` and `ρ = cutPlusRelabel`. -/
theorem plusBotCornerEquiv_leftEnd_head (x : KLRAlgebra k Sc q'.α)
    (z : botCorner Sp q Nₒ) :
    plusBotCornerEquiv X hQ s w hs q hq q' hq'
        (botCornerLeftEnd q Nₒ (relabelHom (cutPlusRelabel j hj Q Λ Λc
          (leadingQuad_α_eq_map s w hs q hq q' hq')) x ⊗ₜ (1 : KLRAlgebra k Sp q.β)) z) =
      botCornerLeftEnd q' Yc (x ⊗ₜ (1 : KLRAlgebra k Sc q'.β))
        (plusBotCornerEquiv X hQ s w hs q hq q' hq' z) := by
  have hβ := hq.trans (windowWeight_eq_map j hj ν₀)
  have hfz : ∀ z' : botCorner Sp q Nₒ, (plusBotCornerEquiv X hQ s w hs q hq q' hq' z' : Yc) =
      innerToRes j hj Q Λ Λc θ γ ν₀ X
        (botCornerBlocksEquiv Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
          (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ hβ z' : Inner) := by
    intro z'
    rw [plusBotCornerEquiv_apply, botCornerBlocksEquiv_apply]
  apply Subtype.ext
  rw [coe_botCornerLeftEnd q' Yc, quadBot_tmul_one_smul_of_mem q' Yc x
    (plusBotCornerEquiv X hQ s w hs q hq q' hq' z).2, hfz, hfz, botCornerBlocksEquiv_leftEnd]
  change (plusFactorEquiv Q Λ Λc j hj θ ν₀ γ
      (cutPrefixProjection (a := j) (r := 2 + (ℓ - j)) Q (plusBlockLabels Λ Λc j hj) θ
          (castAlg Sp q.h₃ (concat Sp q.α q.γ
            (relabelHom (cutPlusRelabel j hj Q Λ Λc
              (leadingQuad_α_eq_map s w hs q hq q' hq')) x ⊗ₜ 1))) ⊗ₜ 1) •
      (show X from (botCornerBlocksEquiv Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
          (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ hβ z : Inner)) : X) =
    (plusOuterIncl j hj Q Λ Λc θ γ ν₀ (cutInputMap (a := j) (r := ℓ - j) Q
        (cutLabels j hj Λ) θ γ (castAlg Sc q'.h₃ (concat Sc q'.α q'.γ (x ⊗ₜ 1)) ⊗ₜ 1)) •
      (show X from (botCornerBlocksEquiv Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
          (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ hβ z : Inner)) : X)
  rw [plusFactorEquiv, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    map_one, AlgEquiv.coe_toAlgHom,
    relabel_cutPrefixProjection_leading_head_left s w hs q hq q' hq', cutInputMap,
    Algebra.TensorProduct.map_tmul, map_one]
  rfl

/-- **`leadingTopOneSpanEquiv` and the induced bottom endomorphisms**: if `plusBotCornerEquiv`
carries `f` to `f'`, then `leadingTopOneSpanEquiv` carries `r · Ind(f')` to `ρ(r) · Ind(f)`,
`ρ = cutPlusRelabel`. -/
theorem leadingTopOneSpanEquiv_mapRight
    (f' : botCorner Sc q' Yc →ₗ[TensorKLR Sc q'.γ q'.δ] botCorner Sc q' Yc)
    (f : botCorner Sp q Nₒ →ₗ[TensorKLR Sp q.γ q.δ] botCorner Sp q Nₒ)
    (hf : ∀ z, plusBotCornerEquiv X hQ s w hs q hq q' hq' (f z) =
      f' (plusBotCornerEquiv X hQ s w hs q hq q' hq' z))
    (r : KLRAlgebra k Sc (q'.γ + q'.δ)) (x : Ind Sc q'.γ q'.δ (botCorner Sc q' Yc)) :
    leadingTopOneSpanEquiv X hQ s w hs q hq q' hq'
        (topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)
          (r • BalancedTensor.mapRight f' x)) =
      topOneCornerEquiv q Nₒ (stendhalQ_symm Q (plusBlockLabels Λ Λc j hj) hQ)
        (relabelHom (cutPlusRelabel j hj Q Λ Λc (leadingQuad_add_eq_map j hj s w q hq q' hq')) r •
          BalancedTensor.mapRight f
            ((topOneCornerEquiv q Nₒ (stendhalQ_symm Q (plusBlockLabels Λ Λc j hj) hQ)).symm
              (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq'
                (topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ) x)))) := by
  have hfg : ∀ n, (plusBotCornerEquiv X hQ s w hs q hq q' hq').symm (f' n) =
      f ((plusBotCornerEquiv X hQ s w hs q hq q' hq').symm n) := by
    intro n
    apply (plusBotCornerEquiv X hQ s w hs q hq q' hq').injective
    rw [LinearEquiv.apply_symm_apply, hf, LinearEquiv.apply_symm_apply]
  have hL : ∀ y, (topOneCornerEquiv q Nₒ (stendhalQ_symm Q (plusBlockLabels Λ Λc j hj) hQ)).symm
      (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq'
        (topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ) y)) =
      cutPlusInd j hj Q Λ Λc (leadingQuad_γ_eq_map j hj s w q hq q' hq').symm
        (leadingQuad_δ_eq_map j hj s w q hq q' hq').symm
        (plusBotCornerEquiv X hQ s w hs q hq q' hq').symm
        (plusBotCornerEquiv_symm_smul X hQ s w hs q hq q' hq') y := by
    intro y
    simp only [leadingTopOneSpanEquiv_eq, leadingTopOneEquiv, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply]
  have key := cutPlusInd_mapRight (N' := botCorner Sc q' Yc) (N := botCorner Sp q Nₒ) j hj Q Λ Λc
    (leadingQuad_γ_eq_map j hj s w q hq q' hq').symm
    (leadingQuad_δ_eq_map j hj s w q hq q' hq').symm
    (plusBotCornerEquiv X hQ s w hs q hq q' hq').symm
    (plusBotCornerEquiv_symm_smul X hQ s w hs q hq q' hq') f' f hfg x
  rw [← LinearEquiv.symm_apply_eq]
  refine (hL _).trans ((cutPlusInd_smul _ _ _ _ _ _ _ _ _ r _).trans ?_)
  refine congrArg _ (key.trans ?_)
  exact congrArg _ (hL x).symm

/-- **`leadingTopOneSpanEquiv` carries the top algebra of `S_cut(Res X)` to that of `S_+(X)`**:
if `plusBotCornerEquiv` carries `quadBot (X₊ ⊗ 1)` to `quadBot (X' ⊗ 1)` (`hX`, a datum of this
intermediate statement), then `ι(X') ⊗ ι(r)` at `q'` corresponds to `ι(X₊) ⊗ ι(ρ r)` at `q`. -/
theorem leadingTopOneSpanEquiv_smul (X' : TensorKLR Sc q'.α q'.β) (Xp : TensorKLR Sp q.α q.β)
    (hX : ∀ z, plusBotCornerEquiv X hQ s w hs q hq q' hq' (botCornerLeftEnd q Nₒ Xp z) =
      botCornerLeftEnd q' Yc X' (plusBotCornerEquiv X hQ s w hs q hq q' hq' z))
    (r : KLRAlgebra k Sc (q'.γ + q'.δ)) (y y' : mackeyTopOneSpan (Q := Sc) q' Yc)
    (hy : (y' : MackeyLeftInd Sc Yc q') =
      ((castAlg Sc q'.h₁ (concat Sc q'.α q'.β X') ⊗ₜ castAlg Sc q'.h₂ r :
        TensorKLR Sc _ _) • (y : MackeyLeftInd Sc Yc q'))) :
    (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq' y' : MackeyLeftInd Sp Nₒ q) =
      ((castAlg Sp q.h₁ (concat Sp q.α q.β Xp) ⊗ₜ castAlg Sp q.h₂
          (relabelHom (cutPlusRelabel j hj Q Λ Λc (leadingQuad_add_eq_map j hj s w q hq q' hq'))
            r) : TensorKLR Sp _ _) •
        (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq' y : MackeyLeftInd Sp Nₒ q)) := by
  have hx := (topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).apply_symm_apply y
  have hy' : y' = topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)
      (r • BalancedTensor.mapRight (botCornerLeftEnd q' Yc X')
        ((topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm y)) :=
    Subtype.ext (hy.trans ((congrArg (fun z : mackeyTopOneSpan (Q := Sc) q' Yc =>
      ((castAlg Sc q'.h₁ (concat Sc q'.α q'.β X') ⊗ₜ castAlg Sc q'.h₂ r : TensorKLR Sc _ _) •
        (z : MackeyLeftInd Sc Yc q'))) hx.symm).trans
      (topOneCornerEquiv_tmul_smul q' Yc _ X' r _)))
  have h1 := congrArg (fun z : mackeyTopOneSpan (Q := Sc) q' Yc =>
    (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq' z : MackeyLeftInd Sp Nₒ q)) hy'
  have h2 := congrArg Subtype.val (leadingTopOneSpanEquiv_mapRight X hQ s w hs q hq q' hq' _ _
    hX r ((topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm y))
  refine h1.trans (h2.trans ((topOneCornerEquiv_tmul_smul q Nₒ _ Xp _ _).symm.trans ?_))
  exact congrArg (HSMul.hSMul _) (congrArg Subtype.val ((LinearEquiv.apply_symm_apply _ _).trans
    (congrArg (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq') hx)))

/-- **(T_w), head part, on the identity-shuffle spans**: `leadingTopOneSpanEquiv` carries the
action of `ι(x ⊗ 1) ⊗ ι(r)` at `S_cut(Res X)` to that of `ι(ρ x ⊗ 1) ⊗ ι(ρ r)` at `S_+(X)`, for
`x ∈ R(q'.α)`, `r ∈ R(q'.γ + q'.δ)` and `ρ = cutPlusRelabel`. -/
theorem leadingTopOneSpanEquiv_head_smul (x : KLRAlgebra k Sc q'.α)
    (r : KLRAlgebra k Sc (q'.γ + q'.δ)) (y y' : mackeyTopOneSpan (Q := Sc) q' Yc)
    (hy : (y' : MackeyLeftInd Sc Yc q') =
      ((castAlg Sc q'.h₁ (concat Sc q'.α q'.β (x ⊗ₜ (1 : KLRAlgebra k Sc q'.β))) ⊗ₜ
        castAlg Sc q'.h₂ r : TensorKLR Sc _ _) • (y : MackeyLeftInd Sc Yc q'))) :
    (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq' y' : MackeyLeftInd Sp Nₒ q) =
      ((castAlg Sp q.h₁ (concat Sp q.α q.β (relabelHom (cutPlusRelabel j hj Q Λ Λc
            (leadingQuad_α_eq_map s w hs q hq q' hq')) x ⊗ₜ (1 : KLRAlgebra k Sp q.β))) ⊗ₜ
          castAlg Sp q.h₂
            (relabelHom (cutPlusRelabel j hj Q Λ Λc (leadingQuad_add_eq_map j hj s w q hq q' hq'))
              r) : TensorKLR Sp _ _) •
        (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq' y : MackeyLeftInd Sp Nₒ q)) :=
  leadingTopOneSpanEquiv_smul X hQ s w hs q hq q' hq' _ _
    (plusBotCornerEquiv_leftEnd_head X hQ s w hs q hq q' hq' x) r y y' hy

end Leading

end Categorification.Stendhal.CupCap
