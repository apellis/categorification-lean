/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelBottom

/-!
# Injectivity on a bottom column of the braiding bimodule

Webster, arXiv:1309.3796v2, §6.1, proof after (6.21) in Lemma 6.8. A loading column
`B e(s)` splits off the braiding as a left module over the *source* ordered algebra.
When the exchanged reds occupy consecutive positions of `s`, tensoring the higher
submodule inclusion with this column is injective. This is the actual inclusion on
both balanced tensors, not a statement about its image in a diagram quotient.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR TypeA
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ) (s : KLR.Seq (stendhalWeight ℓ ν))
local notation "V" => ViolQuotient k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "E" => mk (redProj k Q Λ ν (redWord t))
local notation "F" => mk (redProj k Q Λ ν (redWord s))
local notation "p" => mk (ofKLR k Q Λ ν (KLRAlgebra.e s))
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "B" => RedBlock.crossingSpace (k := k) E F
local notation "C" => RedBlock.crossingSpace (k := k) E p
local notation "P" => rIdeal (orderedLoadingIdem Q Λ t)
local notation "K" => blockLoadingKernel Q Λ t a b

private local instance {R : Type*} [Ring R] [Algebra k R] {u v : R} (hu : IsIdempotentElem u) :
    IsScalarTower k hu.Corner (RedBlock.crossingSpace (k := k) u v) where
  smul_assoc c r x := Subtype.ext (smul_mul_assoc c r.1 x.1)

private def columnIn : C →ₗ[T] B where
  toFun x := ⟨x.1,x.2.1,by
    calc x.1 * F = (x.1 * p) * F := congrArg (· * F) x.2.2.symm
         _ = x.1 := by rw [mul_assoc, ← map_mul, e_mul_redProj, ite_eq_left rfl, x.2.2]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem loading_sq : p * p = p := by rw [← map_mul,← map_mul,KLRAlgebra.e_mul_self]

private def columnOut : B →ₗ[T] C where
  toFun x := ⟨x.1 * p, by rw [← mul_assoc,x.2.1], by rw [mul_assoc,loading_sq]⟩
  map_add' x y := Subtype.ext (add_mul x.1 y.1 p)
  map_smul' r x := Subtype.ext (mul_assoc r.1 x.1 p)

/-- The map in (6.21) on the right loading `s`, formed by tensoring `K ↪ e(t)T`
with `B e(s)` over `T`. -/
def blockKernelColumnInclusion : BalancedTensor k k T K C →ₗ[k] BalancedTensor k k T P C :=
  BalancedTensor.mapLeftBimodule k C ((K).subtype.restrictScalars k) (fun _ _ => rfl)

local notation "emb" => BalancedTensor.mapRight (k := k) («B» := k) (M := K) (columnIn Q Λ t s)
local notation "out" => BalancedTensor.mapRight (k := k) («B» := k) (M := K) (columnOut Q Λ t s)
local notation "botMap" => blockKernelBottom Q Λ t a b s

private theorem recoverColumn : (out).comp ((botMap).comp emb) = LinearMap.id := by
  apply BalancedTensor.ext; intro x y
  change BalancedTensor.tmul x _ = (BalancedTensor.tmul x y : BalancedTensor k k T K C)
  apply congrArg; apply Subtype.ext
  change (y.1 * p) * p = y.1
  rw [y.2.2,y.2.2]

local notation "embP" => BalancedTensor.mapRight (k := k) («B» := k) (M := P) (columnIn Q Λ t s)

private theorem includeColumn (z : BalancedTensor k k T K C) :
    blockKernelTensorInclusion Q Λ t a b (redWord s) (emb z) = embP (blockKernelColumnInclusion Q Λ t a b s z) :=
  LinearMap.congr_fun (show (blockKernelTensorInclusion Q Λ t a b (redWord s)).comp emb =
    (embP).comp (blockKernelColumnInclusion Q Λ t a b s) from BalancedTensor.ext fun _ _ => rfl) z

private theorem columnInjective {X Y U D : Type*} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] [AddCommGroup U] [Module k U] [AddCommGroup D] [Module k D]
    (i : X →ₗ[k] Y) (j : U →ₗ[k] D) (b : U →ₗ[k] U)
    (u : X →ₗ[k] U) (v : Y →ₗ[k] D) (w : U →ₗ[k] X) (hu : w.comp (b.comp u) = LinearMap.id)
    (H : LinearMap.ker j ≤ LinearMap.ker b) (hn : ∀ z, j (u z) = v (i z)) : Function.Injective i := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have zero : j (u z) = 0 := (hn z).trans (hz ▸ map_zero _)
  have hb : b (u z) = 0 := H zero
  exact (LinearMap.congr_fun hu z).symm.trans ((congrArg w hb).trans (map_zero _))

/-- **Injectivity in (6.21) at consecutive exchanged reds.** Webster v2, §6.1, Lemma
6.8. The top may be any source loading, with arbitrary spectators and black contents.
The consecutive-position restriction is only on the bottom column; the proof uses a
common last red crossing, which need not exist when the bottom reds enclose a black. -/
theorem blockKernelColumnInclusion_injective (hQ : KLRSymm Q)
    (L M : List (Fin ℓ)) (ht : redWord t = L ++ a :: b :: M)
    (u : KLR.Seq (stendhalWeight ℓ ν)) (hu : redWord u = redWord t)
    (n : ℕ) (hn : n+1 < (stendhalWeight ℓ ν).card)
    (ha : u.lbl ⟨n,by omega⟩ = .inr a) (hb : u.lbl ⟨n+1,hn⟩ = .inr b)
    (hs : sadj (stendhalWeight ℓ ν).card n • u = s) :
    Function.Injective (blockKernelColumnInclusion Q Λ t a b s) :=
  columnInjective (k := k) (X := BalancedTensor k k T K C) (Y := BalancedTensor k k T P C)
    (U := BalancedTensor k k T K B) (D := BalancedTensor k k T P B)
    (blockKernelColumnInclusion Q Λ t a b s) (blockKernelTensorInclusion Q Λ t a b (redWord s))
    botMap emb embP out (recoverColumn Q Λ t a b s)
    (ker_blockKernelTensorInclusion_le_ker_bottom Q Λ t a b s hQ L M ht u hu n hn ha hb hs)
    (includeColumn Q Λ t a b s)

end Categorification.Stendhal.BraidedStendhalAlgebra
