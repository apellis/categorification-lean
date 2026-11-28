/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutLeadingCorner

/-!
# The window factor on the identity-shuffle spans of the leading Mackey layers

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the window factor
of (T_w) of the handoff).

Let `q` (outer cut of `S_+(X)`, `q.β` the weight of the window) and `q'` (cut of `S_cut(Res X)`,
`q'.β = 0`) be the leading Mackey data at a loading `s`. For `b̃` in the KLR algebra of the middle
block of `λ⁺` and `b` its relabelling into `R(q.β)`, the image of `ι_{q.β,q.δ}(b ⊗ 1)` in the
algebra of the two inner blocks is that of `ι(b̃ ⊗ 1)` (`cutSuffixProjection_plus_window`). On the
bottom corner `quadBot ((1 ⊗ b) ⊗ 1)` acts as `1 ⊗ ι(b ⊗ 1)` (`quadBot_one_tmul_smul_of_mem`),
hence through the identity coordinate by `ι(b̃ ⊗ 1)` on the inner input
(`botCornerBlocksEquiv_leftEnd_mid`), that is by `1 ⊗ (b̄ ⊗ 1)` on `X`, `b̄` the image of `b̃` in
`T^{μ μ*}(ν₀)`. This element commutes with the two blocks of `λ` inside the three blocks of `λ⁺`
(`one_tmul_tmul_one_mul_map_includeRight`), so it is an endomorphism of `Res X`
(`plusMidEnd`), and restricts to the bottom corner `E' · Res X` (`botCornerEnd`): the window
factor `ε_{b̃}` (`plusWindowEnd`).

`plusBotCornerEquiv` carries `quadBot ((1 ⊗ b) ⊗ 1)` to `ε_{b̃}`
(`plusBotCornerEquiv_leftEnd_window`), so `leadingTopOneSpanEquiv` carries `Ind(ε_{b̃})` to the
action of `ι(1 ⊗ b) ⊗ 1` (`leadingTopOneSpanEquiv_window_smul`). With the head part of
`CupCapTraceCutLeadingCorner` this is (T_w) on the identity-shuffle spans: `ι(x ⊗ 1) ⊗ ι(r)`
after `ε_{b̃}` at `S_cut(Res X)` corresponds to `ι(ρ x ⊗ b) ⊗ ι(ρ r)` at `S_+(X)`
(`leadingTopOneSpanEquiv_head_window_smul`).

Webster's proof does not spell this out. No new hypothesis.

## Main definitions

* `KLR.KLRAlgebra.botCornerEnd`.
* `Stendhal.CupCap.plusMidEnd`, `Stendhal.CupCap.plusWindowEnd`.

## Main results

* `KLR.KLRAlgebra.quadBot_one_tmul_smul_of_mem`.
* `Stendhal.botCornerBlocksEquiv_leftEnd_mid`.
* `Stendhal.CupCap.leadingQuad_β_eq_map`, `Stendhal.CupCap.cutSuffixProjection_plus_window`,
  `Stendhal.CupCap.one_tmul_tmul_one_mul_map_includeRight`,
  `Stendhal.CupCap.plusMid_mul_plusOuterIncl`,
  `Stendhal.CupCap.plusBotCornerEquiv_leftEnd_window`,
  `Stendhal.CupCap.leadingTopOneSpanEquiv_window_smul`,
  `Stendhal.CupCap.leadingTopOneSpanEquiv_head_window_smul`.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' ν'' ν''' : Multiset I}
  (q : MackeyQuad ν ν' ν'' ν''')
  (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]
  [IsScalarTower k (TensorKLR Q ν'' ν''') N]

attribute [local instance] botCornerModuleRight

/-- **A module endomorphism on the bottom corner**: an `R(ν'') ⊗ R(ν''')`-linear endomorphism
of `N` restricts to an `R(γ) ⊗ R(δ)`-linear endomorphism of `E N`. -/
def botCornerEnd (g : N →ₗ[TensorKLR Q ν'' ν'''] N) :
    botCorner Q q N →ₗ[TensorKLR Q q.γ q.δ] botCorner Q q N where
  toFun n := ⟨g n, by
    rw [mem_botCorner, ← g.map_smul]
    exact congrArg g n.2⟩
  map_add' n n' := Subtype.ext (g.map_add _ _)
  map_smul' c n := Subtype.ext (g.map_smul (quadBot q ((1 : TensorKLR Q q.α q.β) ⊗ₜ c)) _)

theorem coe_botCornerEnd (g : N →ₗ[TensorKLR Q ν'' ν'''] N) (n : botCorner Q q N) :
    (botCornerEnd q N g n : N) = g n := rfl

/-- On the bottom corner, `quadBot ((1 ⊗ b) ⊗ 1)` acts as `1 ⊗ ι_{β,δ}(b ⊗ 1)`. -/
theorem quadBot_one_tmul_smul_of_mem (b : KLRAlgebra k Q q.β) {n : N}
    (hn : n ∈ botCorner Q q N) :
    (quadBot q (((1 : KLRAlgebra k Q q.α) ⊗ₜ b) ⊗ₜ (1 : TensorKLR Q q.γ q.δ)) :
        TensorKLR Q ν'' ν''') • n =
      ((1 : KLRAlgebra k Q ν'') ⊗ₜ castAlg Q q.h₄ (concat Q q.β q.δ (b ⊗ₜ 1)) :
        TensorKLR Q ν'' ν''') • n := by
  conv_rhs => rw [← (mem_botCorner q N).1 hn, smul_smul]
  congr 1
  rw [show (1 : QuadAlg Q q) = ((1 : KLRAlgebra k Q q.α) ⊗ₜ (1 : KLRAlgebra k Q q.β)) ⊗ₜ
      ((1 : KLRAlgebra k Q q.γ) ⊗ₜ (1 : KLRAlgebra k Q q.δ)) from rfl,
    show (1 : TensorKLR Q q.γ q.δ) = (1 : KLRAlgebra k Q q.γ) ⊗ₜ (1 : KLRAlgebra k Q q.δ)
      from rfl, quadBot_tmul, quadBot_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    ← map_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]

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
local notation "Si" => stendhalQ Q (blocksTailLabels Λ)
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

/-- **The middle part of the first top factor on the bottom corner at the outer cut**: if the
image of `ι_{β,δ}(b ⊗ 1)` in `T^{MR}(β + γ)` is the image of an affine diagram `ι(t)` of the two
inner blocks (`hb`), then, read through the identity coordinate `botCornerBlocksEquiv`,
`quadBot ((1 ⊗ b) ⊗ 1)` acts by `t` on the inner input. -/
theorem botCornerBlocksEquiv_leftEnd_mid (hβ : q.β = (αi).map cR) (b : KLRAlgebra k So q.β)
    (t : TensorKLR Si αi δi)
    (hb : cutSuffixProjection (a := a) (r := m + r) Q Λ (β + γ)
        (castAlg So q.h₄ (concat So q.β q.δ (b ⊗ₜ 1))) =
      affineToTensor (a := m) (r := r) Q (blocksTailLabels Λ) β γ (concat Si αi δi t))
    (z : botCorner So q Nₒ) :
    (botCornerBlocksEquiv Q Λ θ β γ N hQ hβ
        (botCornerLeftEnd q Nₒ ((1 : KLRAlgebra k So q.α) ⊗ₜ b) z) : Inner) =
      t • (botCornerBlocksEquiv Q Λ θ β γ N hQ hβ z : Inner) := by
  have hz : ((z : Nₒ) : CSi) = cutStandardUnit Q (blocksTailLabels Λ) β γ
      (BlocksInner Q Λ θ β γ N) (botCornerBlocksEquiv Q Λ θ β γ N hQ hβ z : Inner) := by
    have := botCornerBlocksEquiv_symm_apply Q Λ θ β γ N hQ hβ
      (botCornerBlocksEquiv Q Λ θ β γ N hQ hβ z)
    rw [LinearEquiv.symm_apply_apply] at this
    exact this
  rw [botCornerBlocksEquiv_apply Q Λ θ β γ N hQ hβ
    (botCornerLeftEnd q Nₒ ((1 : KLRAlgebra k So q.α) ⊗ₜ b) z)]
  have hz' : (botCornerLeftEnd q Nₒ ((1 : KLRAlgebra k So q.α) ⊗ₜ b) z : Nₒ) =
      ((1 : KLRAlgebra k So (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (m + r)))
          (stendhalWeight a θ))) ⊗ₜ castAlg So q.h₄ (concat So q.β q.δ (b ⊗ₜ 1)) :
        TensorKLR So _ _) • (z : Nₒ) :=
    quadBot_one_tmul_smul_of_mem q Nₒ b z.2
  rw [hz']
  change (cutStandardShuffleEquiv Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ
      (blocksMidAction Q Λ θ β γ N hQ (cutInputMap Q Λ θ (β + γ)
        ((1 : KLRAlgebra k So (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (m + r)))
          (stendhalWeight a θ))) ⊗ₜ castAlg So q.h₄ (concat So q.β q.δ (b ⊗ₜ 1))))
        ((z : Nₒ) : CSi)) : Shuffle (Seq.card_add' αi δi) → Inner) shufOne = _
  simp only [cutInputMap, Algebra.TensorProduct.map_tmul, blocksMidAction,
    Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rw [hb, hz]
  exact cutStandardShuffleEquiv_affineToTensor_concat_unit Q (blocksTailLabels Λ) β γ
    (BlocksInner Q Λ θ β γ N) hQ t _

end Blocks

end Categorification.Stendhal

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

section Generic

variable {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [Semiring C] [Algebra R C]

/-- In `A ⊗ (B ⊗ C)`, the elements `1 ⊗ (u ⊗ 1)` commute with the image of `A ⊗ C`. -/
theorem one_tmul_tmul_one_mul_map_includeRight (u : B) (d : A ⊗[R] C) :
    ((1 : A) ⊗ₜ[R] (u ⊗ₜ[R] (1 : C)) : A ⊗[R] (B ⊗[R] C)) *
        Algebra.TensorProduct.map (AlgHom.id R A) Algebra.TensorProduct.includeRight d =
      Algebra.TensorProduct.map (AlgHom.id R A) Algebra.TensorProduct.includeRight d *
        ((1 : A) ⊗ₜ[R] (u ⊗ₜ[R] (1 : C)) : A ⊗[R] (B ⊗[R] C)) := by
  induction d using TensorProduct.inductionOn with
  | add d d' hd hd' => rw [map_add, mul_add, add_mul, hd, hd']
  | tmul a c =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul, mul_one, one_mul, mul_one]

end Generic

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
include hq in
/-- The weight of the window, read in the labels of the two inner blocks and then in `λ⁺`, is
`q.β`. -/
theorem leadingQuad_β_eq_map :
    ((stendhalWeight 2 ν₀).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))).map
      (Sum.map (id : I → I) (Fin.natAdd j)) = q.β :=
  (windowWeight_eq_map j hj ν₀).symm.trans hq.symm

omit [DecidableEq I] in
/-- **(T), the window factor at the outer cut of `S_+`**: the image of `ι_{q.β,q.δ}(b ⊗ 1)` in
the algebra of the two inner blocks, for `b` the relabelling of `b̃` from the middle block, is
the image of `ι(b̃ ⊗ 1)` of the two inner blocks. -/
theorem cutSuffixProjection_plus_window [DecidableEq I]
    (b : KLRAlgebra k (stendhalQ Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)))
      ((stendhalWeight 2 ν₀).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))))) :
    cutSuffixProjection (a := j) (r := 2 + (ℓ - j)) Q (plusBlockLabels Λ Λc j hj) (ν₀ + γ)
        (castAlg Sp q.h₄ (concat Sp q.β q.δ
          (relabelHom (subfamilyRelabel Q (plusBlockLabels Λ Λc j hj)
            (Fin.natAdd_injective _ j) (leadingQuad_β_eq_map s w q hq)) b ⊗ₜ 1))) =
      affineToTensor (a := 2) (r := ℓ - j) Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) ν₀ γ
        (concat (stendhalQ Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)))
          ((stendhalWeight 2 ν₀).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))))
          ((stendhalWeight (ℓ - j) γ).map (Sum.map (id : I → I) (Fin.natAdd 2))) (b ⊗ₜ 1)) := by
  have hδ : ((stendhalWeight (ℓ - j) γ).map (Sum.map (id : I → I) (Fin.natAdd 2))).map
      (Sum.map (id : I → I) (Fin.natAdd j)) = q.δ := by
    have e : Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ)) =
        ((stendhalWeight 2 ν₀).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))).map
          (Sum.map (id : I → I) (Fin.natAdd j)) +
        ((stendhalWeight (ℓ - j) γ).map (Sum.map (id : I → I) (Fin.natAdd 2))).map
          (Sum.map (id : I → I) (Fin.natAdd j)) := by
      rw [← Multiset.map_add, cutInputWeights_add (a := 2) (r := ℓ - j) ν₀ γ]
    have h4 := ((congrArg (· + q.δ) (leadingQuad_β_eq_map s w q hq)).trans q.h₄).trans e
    exact (add_left_cancel h4).symm
  have key := redSubfamilyProjection_castAlg_concat Q (plusBlockLabels Λ Λc j hj)
    (Fin.natAdd_injective _ j) (ν₀ + γ) (cutInputWeights_add (a := 2) (r := ℓ - j) ν₀ γ)
    (leadingQuad_β_eq_map s w q hq) hδ q.h₄ (b ⊗ₜ 1)
  rw [Algebra.TensorProduct.map_tmul, map_one] at key
  exact key

omit [DecidableEq I] in
/-- The middle block commutes with the two blocks of `λ` at the cut inside the three blocks of
`λ⁺`. -/
theorem plusMid_mul_plusOuterIncl [DecidableEq I] (u : TensorProductAlgebra k Q Λc ν₀)
    (d : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) :
    ((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ) ⊗ₜ
        (u ⊗ₜ (1 : TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ)) :
        PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) * plusOuterIncl j hj Q Λ Λc θ γ ν₀ d =
      plusOuterIncl j hj Q Λ Λc θ γ ν₀ d *
        ((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ) ⊗ₜ
          (u ⊗ₜ (1 : TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ)) :
          PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) :=
  one_tmul_tmul_one_mul_map_includeRight u d

/-- **The middle block acting on `Res X`**: `x ↦ (1 ⊗ (u ⊗ 1)) · x`, linear over the two
blocks of `λ` at the cut. -/
def plusMidEnd (u : TensorProductAlgebra k Q Λc ν₀) :
    PlusRes j hj Q Λ Λc θ γ ν₀ X →ₗ[cutFactorAlgebra Q (cutLabels j hj Λ) θ γ]
      PlusRes j hj Q Λ Λc θ γ ν₀ X where
  toFun x := (((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ) ⊗ₜ
      (u ⊗ₜ (1 : TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ)) :
      PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) • (show X from x) : X)
  map_add' x x' := smul_add _ (show X from x) x'
  map_smul' d x := by
    change (((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ) ⊗ₜ
        (u ⊗ₜ (1 : TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ)) :
        PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) •
        (plusOuterIncl j hj Q Λ Λc θ γ ν₀ d • (show X from x)) : X) =
      plusOuterIncl j hj Q Λ Λc θ γ ν₀ d • (((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ) ⊗ₜ
        (u ⊗ₜ (1 : TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ)) :
        PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) • (show X from x))
    rw [smul_smul, smul_smul]
    exact congrArg (· • (show X from x)) (plusMid_mul_plusOuterIncl u d)

omit [Module k X] [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] in
theorem plusMidEnd_apply (u : TensorProductAlgebra k Q Λc ν₀) (x : PlusRes j hj Q Λ Λc θ γ ν₀ X) :
    (plusMidEnd X u x : X) = (((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ) ⊗ₜ
      (u ⊗ₜ (1 : TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ)) :
      PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) • (show X from x) : X) := rfl

/-- **The window factor `ε_b` on the bottom corner of `S_cut(Res X)`**: `b` in the middle block
of `λ⁺` acts on `E' · Res X` through `1 ⊗ (b ⊗ 1)`. -/
def plusWindowEnd
    (b : KLRAlgebra k (stendhalQ Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)))
      ((stendhalWeight 2 ν₀).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))))) :
    botCorner Sc q' Yc →ₗ[TensorKLR Sc q'.γ q'.δ] botCorner Sc q' Yc :=
  botCornerEnd q' Yc (cutInputHom (a := j) (r := ℓ - j) Q (cutLabels j hj Λ) θ γ
    (plusMidEnd X (relabelTensorProductAlgebra Q (plusBlockLabels_cup Λ Λc j hj) ν₀
      (cutPrefixProjection (a := 2) (r := ℓ - j) Q (blocksTailLabels (plusBlockLabels Λ Λc j hj))
        ν₀ b))))

/-- **The bottom corners intertwine the window part of the first top factor** (Webster v3,
Lemma 7.19, trace half, step L5): `plusBotCornerEquiv` carries `quadBot ((1 ⊗ b) ⊗ 1)` at the
outer cut of `S_+(X)` to the window factor `ε_{b̃}` (`plusWindowEnd`) on `E' · Res X`, for `b`
the relabelling of `b̃` from the middle block of `λ⁺`. -/
theorem plusBotCornerEquiv_leftEnd_window
    (b : KLRAlgebra k (stendhalQ Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)))
      ((stendhalWeight 2 ν₀).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))))
    (z : botCorner Sp q Nₒ) :
    plusBotCornerEquiv X hQ s w hs q hq q' hq'
        (botCornerLeftEnd q Nₒ ((1 : KLRAlgebra k Sp q.α) ⊗ₜ
          relabelHom (subfamilyRelabel Q (plusBlockLabels Λ Λc j hj)
            (Fin.natAdd_injective _ j) (leadingQuad_β_eq_map s w q hq)) b) z) =
      plusWindowEnd X s q' b (plusBotCornerEquiv X hQ s w hs q hq q' hq' z) := by
  have hβ := hq.trans (windowWeight_eq_map j hj ν₀)
  have hfz : ∀ z' : botCorner Sp q Nₒ, (plusBotCornerEquiv X hQ s w hs q hq q' hq' z' : Yc) =
      innerToRes j hj Q Λ Λc θ γ ν₀ X
        (botCornerBlocksEquiv Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
          (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ hβ z' : Inner) := by
    intro z'
    rw [plusBotCornerEquiv_apply, botCornerBlocksEquiv_apply]
  apply Subtype.ext
  rw [plusWindowEnd, coe_botCornerEnd, hfz, hfz,
    botCornerBlocksEquiv_leftEnd_mid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
      (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ hβ _ (b ⊗ₜ 1)
      (cutSuffixProjection_plus_window s w q hq b)]
  change (plusFactorEquiv Q Λ Λc j hj θ ν₀ γ
      ((1 : TensorProductAlgebra k Q (plusBlockLabels Λ Λc j hj ∘ Fin.castAdd (2 + (ℓ - j))) θ) ⊗ₜ
        cutInputMap (a := 2) (r := ℓ - j) Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) ν₀ γ
          (b ⊗ₜ 1)) •
      (show X from (botCornerBlocksEquiv Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
          (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ hβ z : Inner)) : X) =
    (((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ) ⊗ₜ
        (relabelTensorProductAlgebra Q (plusBlockLabels_cup Λ Λc j hj) ν₀
          (cutPrefixProjection (a := 2) (r := ℓ - j) Q
            (blocksTailLabels (plusBlockLabels Λ Λc j hj)) ν₀ b) ⊗ₜ
          (1 : TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ)) :
        PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) •
      (show X from (botCornerBlocksEquiv Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
          (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ hβ z : Inner)) : X)
  rw [cutInputMap, Algebra.TensorProduct.map_tmul, map_one, plusFactorEquiv,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one,
    AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    map_one]
  rfl

/-- **(T_w), window part, on the identity-shuffle spans**: `leadingTopOneSpanEquiv` carries the
window factor `ε_{b̃}` at `S_cut(Res X)` (induced on `Ind (E' · Res X)`) to the action of
`ι(1 ⊗ b) ⊗ 1` at `S_+(X)`, for `b` the relabelling of `b̃` from the middle block. -/
theorem leadingTopOneSpanEquiv_window_smul
    (b : KLRAlgebra k (stendhalQ Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)))
      ((stendhalWeight 2 ν₀).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))))
    (x : Ind Sc q'.γ q'.δ (botCorner Sc q' Yc)) :
    (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq'
        (topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)
          (BalancedTensor.mapRight (plusWindowEnd X s q' b) x)) : MackeyLeftInd Sp Nₒ q) =
      ((castAlg Sp q.h₁ (concat Sp q.α q.β ((1 : KLRAlgebra k Sp q.α) ⊗ₜ
          relabelHom (subfamilyRelabel Q (plusBlockLabels Λ Λc j hj)
            (Fin.natAdd_injective _ j) (leadingQuad_β_eq_map s w q hq)) b)) ⊗ₜ
          (1 : KLRAlgebra k Sp (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
            (midPos j s + Multiset.card (stendhalWeight 2 ν₀))
            (midPos_add_le_card (hj := hj) s))) : TensorKLR Sp _ _) •
        (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq'
          (topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ) x) :
          MackeyLeftInd Sp Nₒ q)) := by
  have key := leadingTopOneSpanEquiv_mapRight X hQ s w hs q hq q' hq' (plusWindowEnd X s q' b)
    (botCornerLeftEnd q Nₒ ((1 : KLRAlgebra k Sp q.α) ⊗ₜ
      relabelHom (subfamilyRelabel Q (plusBlockLabels Λ Λc j hj)
        (Fin.natAdd_injective _ j) (leadingQuad_β_eq_map s w q hq)) b))
    (plusBotCornerEquiv_leftEnd_window X hQ s w hs q hq q' hq' b) 1 x
  have h1 := congrArg (fun y => (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq'
      (topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ) y) :
      MackeyLeftInd Sp Nₒ q))
    (one_smul (KLRAlgebra k Sc (q'.γ + q'.δ))
      (BalancedTensor.mapRight (plusWindowEnd X s q' b) x)).symm
  have h2 := congrArg (fun r => (topOneCornerEquiv q Nₒ
      (stendhalQ_symm Q (plusBlockLabels Λ Λc j hj) hQ) (r •
        BalancedTensor.mapRight (botCornerLeftEnd q Nₒ ((1 : KLRAlgebra k Sp q.α) ⊗ₜ
          relabelHom (subfamilyRelabel Q (plusBlockLabels Λ Λc j hj)
            (Fin.natAdd_injective _ j) (leadingQuad_β_eq_map s w q hq)) b))
          ((topOneCornerEquiv q Nₒ (stendhalQ_symm Q (plusBlockLabels Λ Λc j hj) hQ)).symm
            (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq'
              (topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ) x)))) :
      MackeyLeftInd Sp Nₒ q))
    ((map_one (relabelHom (cutPlusRelabel j hj Q Λ Λc
      (leadingQuad_add_eq_map j hj s w q hq q' hq')))).trans rfl)
  refine h1.trans ((congrArg Subtype.val key).trans (h2.trans ?_))
  refine (congrArg (fun y => (topOneCornerEquiv q Nₒ
      (stendhalQ_symm Q (plusBlockLabels Λ Λc j hj) hQ) y : MackeyLeftInd Sp Nₒ q))
    (one_smul _ _)).trans ?_
  refine (topOneCornerEquiv_mapRight q Nₒ _ _ _).symm.trans ?_
  exact congrArg (HSMul.hSMul _) (congrArg Subtype.val (LinearEquiv.apply_symm_apply _ _))

/-- **(T_w) on the identity-shuffle spans** (Webster v3, Lemma 7.19, trace half, step L5):
`leadingTopOneSpanEquiv` carries `ι(x ⊗ 1) ⊗ ι(r)` after the window factor `ε_{b̃}` at
`S_cut(Res X)` to the action of `ι(ρ x ⊗ b) ⊗ ι(ρ r)` at `S_+(X)`, for `x ∈ R(q'.α)`,
`r ∈ R(q'.γ + q'.δ)`, `ρ = cutPlusRelabel` and `b` the relabelling of `b̃` from the middle
block. -/
theorem leadingTopOneSpanEquiv_head_window_smul (x : KLRAlgebra k Sc q'.α)
    (b : KLRAlgebra k (stendhalQ Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)))
      ((stendhalWeight 2 ν₀).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))))
    (r : KLRAlgebra k Sc (q'.γ + q'.δ)) (y y' : mackeyTopOneSpan (Q := Sc) q' Yc)
    (hy : (y' : MackeyLeftInd Sc Yc q') =
      ((castAlg Sc q'.h₁ (concat Sc q'.α q'.β (x ⊗ₜ (1 : KLRAlgebra k Sc q'.β))) ⊗ₜ
        castAlg Sc q'.h₂ r : TensorKLR Sc _ _) •
        (topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)
          (BalancedTensor.mapRight (plusWindowEnd X s q' b)
            ((topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm y)) :
          MackeyLeftInd Sc Yc q'))) :
    (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq' y' : MackeyLeftInd Sp Nₒ q) =
      ((castAlg Sp q.h₁ (concat Sp q.α q.β (relabelHom (cutPlusRelabel j hj Q Λ Λc
            (leadingQuad_α_eq_map s w hs q hq q' hq')) x ⊗ₜ
            relabelHom (subfamilyRelabel Q (plusBlockLabels Λ Λc j hj)
              (Fin.natAdd_injective _ j) (leadingQuad_β_eq_map s w q hq)) b)) ⊗ₜ
          castAlg Sp q.h₂
            (relabelHom (cutPlusRelabel j hj Q Λ Λc (leadingQuad_add_eq_map j hj s w q hq q' hq'))
              r) : TensorKLR Sp _ _) •
        (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq' y : MackeyLeftInd Sp Nₒ q)) := by
  have hH := leadingTopOneSpanEquiv_head_smul X hQ s w hs q hq q' hq' x r _ y' hy
  have hW := leadingTopOneSpanEquiv_window_smul X hQ s w hs q hq q' hq' b
    ((topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm y)
  refine hH.trans ((congrArg (HSMul.hSMul _) hW).trans ((smul_smul _ _ _).trans ?_))
  refine congrArg₂ (· • ·) ?_ (congrArg Subtype.val (congrArg
    (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq') (LinearEquiv.apply_symm_apply _ _)))
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← map_mul, ← concat_mul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Leading

end Categorification.Stendhal.CupCap
