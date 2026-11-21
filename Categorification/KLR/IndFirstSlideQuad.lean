/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.IndFirstSlide

/-!
# Sliding all of `R(ν₀) ⊗ R(ν') ⊗ R(i)` through `G`

For `G = 1_{ν₀ + i, ν'} ψ_d^* 1_{ν₀ + ν', i}` (`firstG`) and every element `r` of
`R' = (R(ν₀) ⊗ R(ν')) ⊗ (R(i) ⊗ R(0))`, the identity
`G ι(ι_T r) u = ι''(ι_B r) G u` holds on every vector `u` killed by the idempotents
`e_s ι(T)` whose last label lies in the second block. This extends
`firstG_mul_appendR_concat_smul` (the case `r = t ⊗ 1`) to dots on the last strand.

This is KLR input for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Proposition 5.5.

## Main results

* `tensorHflip_quadTop`, `tensorHflip_quadBot`: the horizontal flip commutes with the embeddings
  of `R'`;
* `firstG_mul_concat_quadTop_smul`: the slide identity for all of `R'`.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

local notation "Si" i:max => (Singleton.singleton i : Multiset I)

namespace KLRAlgebra

section QuadFlip

variable {ν ν' ν'' ν''' : Multiset I} (q : MackeyQuad ν ν' ν'' ν''')

/-- The horizontal flip on each of the four factors of `R'`. -/
noncomputable def quadHflip : QuadAlg Q q →ₗ[k] QuadAlg Q q :=
  TensorProduct.map (tensorHflip q.α q.β) (tensorHflip q.γ q.δ)

theorem quadHflip_quadHflip (r : QuadAlg Q q) : quadHflip q (quadHflip q r) = r := by
  induction r using TensorProduct.inductionOn with
  | add s t hs ht => rw [map_add, map_add, hs, ht]
  | tmul x y =>
    simp only [quadHflip, TensorProduct.map_tmul, tensorHflip_tensorHflip]

theorem tensorHflip_quadTop (r : QuadAlg Q q) :
    tensorHflip ν ν' (quadTop q r) = quadTop q (quadHflip q r) := by
  induction r using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul x y =>
    induction x using TensorProduct.inductionOn with
    | add s t hs ht => simp only [TensorProduct.add_tmul, map_add, hs, ht]
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | add s t hs ht => simp only [TensorProduct.tmul_add, map_add, hs, ht]
      | tmul c d =>
        simp only [quadHflip, TensorProduct.map_tmul, tensorHflip_tmul]
        rw [quadTop_tmul, quadTop_tmul, tensorHflip_tmul, hflip_castAlg, hflip_castAlg,
          hflip_concat, hflip_concat, tensorHflip_tmul, tensorHflip_tmul]

theorem tensorHflip_quadBot (r : QuadAlg Q q) :
    tensorHflip ν'' ν''' (quadBot q r) = quadBot q (quadHflip q r) := by
  induction r using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul x y =>
    induction x using TensorProduct.inductionOn with
    | add s t hs ht => simp only [TensorProduct.add_tmul, map_add, hs, ht]
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | add s t hs ht => simp only [TensorProduct.tmul_add, map_add, hs, ht]
      | tmul c d =>
        simp only [quadHflip, TensorProduct.map_tmul, tensorHflip_tmul]
        rw [quadBot_tmul, quadBot_tmul, tensorHflip_tmul, hflip_castAlg, hflip_castAlg,
          hflip_concat, hflip_concat, tensorHflip_tmul, tensorHflip_tmul]

end QuadFlip

section Slide

variable {ν₀ ν' : Multiset I} {i : I}
variable {M : Type*} [AddCommGroup M] [Module k M]
  [Module (KLRAlgebra k Q (ν₀ + ν' + ({i} : Multiset I))) M]
  [IsScalarTower k (KLRAlgebra k Q (ν₀ + ν' + ({i} : Multiset I))) M]

/-- **The slide identity for all of `R'`**: on vectors killed by the idempotents `e_s ι(T)` whose
last label lies in the second block, `G ι(ι_T r) u = ι''(ι_B r) G u`. -/
theorem firstG_mul_concat_quadTop_smul {u : M}
    (hu : ∀ s ∈ concatSet (ν₀ + ν') (Si i), s ∈ botSet (firstQuad_h ν₀ ν' i) →
      ∀ T : TensorKLR Q (ν₀ + ν') (Si i), (e s * concat Q (ν₀ + ν') (Si i) T) • u = 0)
    (r : QuadAlg Q (firstQuad ν₀ ν' i)) :
    (firstG Q ν₀ ν' i * concat Q (ν₀ + ν') (Si i) (quadTop (firstQuad ν₀ ν' i) r)) • u =
      (botConcat Q (firstQuad_h ν₀ ν' i) (quadBot (firstQuad ν₀ ν' i) r) *
        firstG Q ν₀ ν' i) • u := by
  set X := concat Q (ν₀ + ν') (Si i) (quadTop (firstQuad ν₀ ν' i) r) with hXdef
  set B := botConcat Q (firstQuad_h ν₀ ν' i) (quadBot (firstQuad ν₀ ν' i) r) with hBdef
  set D := quadDefect (firstQuad_h ν₀ ν' i) (firstQuad ν₀ ν' i)
    (quadHflip (firstQuad ν₀ ν' i) r) with hDdef
  have hD : D = concat Q (ν₀ + ν') (Si i)
        (quadTop (firstQuad ν₀ ν' i) (quadHflip (firstQuad ν₀ ν' i) r)) * firstψ Q ν₀ ν' i -
      firstψ Q ν₀ ν' i * botConcat Q (firstQuad_h ν₀ ν' i)
        (quadBot (firstQuad ν₀ ν' i) (quadHflip (firstQuad ν₀ ν' i) r)) :=
    rfl
  have hfD : hflip D = hflip (firstψ Q ν₀ ν' i) * X - B * hflip (firstψ Q ν₀ ν' i) := by
    rw [hD, hflip_sub, hflip_mul, hflip_mul, hflip_concat, hflip_botConcat, tensorHflip_quadTop,
      tensorHflip_quadBot, quadHflip_quadHflip]
  have hX : X = X * oneConcat Q (ν₀ + ν') (Si i) := (concat_mul_oneConcat _).symm
  have hX' : oneConcat Q (ν₀ + ν') (Si i) * X = X := oneConcat_mul_concat _
  have h1 : hflip (firstψ Q ν₀ ν' i) * X = hflip D + B * hflip (firstψ Q ν₀ ν' i) := by
    rw [hfD]; abel
  have hB : botOne Q (firstQuad_h ν₀ ν' i) * B = B * botOne Q (firstQuad_h ν₀ ν' i) := by
    rw [hBdef, botOne_mul_botConcat, botConcat_mul_botOne]
  have key : firstG Q ν₀ ν' i * X =
      hflip (oneConcat Q (ν₀ + ν') (Si i) * D * botOne Q (firstQuad_h ν₀ ν' i)) +
        B * firstG Q ν₀ ν' i := by
    calc firstG Q ν₀ ν' i * X
        = botOne Q (firstQuad_h ν₀ ν' i) * (hflip (firstψ Q ν₀ ν' i) * X) *
            oneConcat Q (ν₀ + ν') (Si i) := by
          rw [firstG, mul_assoc, hX', mul_assoc (botOne Q _) _ (oneConcat Q _ _),
            mul_assoc (hflip _) X, ← hX, mul_assoc]
      _ = botOne Q (firstQuad_h ν₀ ν' i) * hflip D * oneConcat Q (ν₀ + ν') (Si i) +
            botOne Q (firstQuad_h ν₀ ν' i) * B * hflip (firstψ Q ν₀ ν' i) *
              oneConcat Q (ν₀ + ν') (Si i) := by
          rw [h1, mul_add, add_mul, mul_assoc (botOne Q _) B]
      _ = _ := by
          rw [hflip_mul, hflip_mul, hflip_oneConcat, hflip_botOne, hB, firstG]
          simp only [mul_assoc]
  rw [key, add_smul, hflip_defect_smul_eq_zero hu
    (quad_intertwine (firstQuad_h ν₀ ν' i) (firstQuad ν₀ ν' i) _), zero_add]

end Slide

end KLRAlgebra

end Categorification.KLR
