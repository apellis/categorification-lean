/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTransportEquiv

/-!
# Naturality of transport along ring isomorphisms

The transports of induction and restriction along ring isomorphisms (`Ind.transport`,
`Res.transport`) commute with `Ind.map` and `Res.map` of module maps related by the given
semilinear isomorphisms (`Ind.transport_map`, `Res.transport_map`). Hence the transported
commutation isomorphisms `resIndEquivTransport` and `indResEquivTransport` are natural in the
module whenever the isomorphisms they transport are (`resIndEquivTransport_map`,
`indResEquivTransport_map`).

This is the step that carries the naturality of Webster's commutation relation
`Eᵢ Fᵢ ≅ Fᵢ Eᵢ ⊕ 1^{⊕ n}` (arXiv:1309.3796v3, Theorem 4.31) from the all-down matrix ring to the
tensor product algebra, as used in the proof of Proposition 5.5 there.
-/

noncomputable section

namespace Categorification.InductionAlong

universe u w

section Basic

variable {A B A' B' : Type u} [Ring A] [Ring B] [Ring A'] [Ring B'] {φ : A →ₙ+* B}
  {φ' : A' →ₙ+* B'} (a : A ≃+* A') (c : B ≃+* B') (h : ∀ t, φ' (a t) = c (φ t))

/-- `Ind.transport` commutes with `Ind.map`. -/
theorem Ind.transport_map {N N₂ : Type w} [AddCommGroup N] [Module A N] [AddCommGroup N₂]
    [Module A N₂] {N' N₂' : Type w} [AddCommGroup N'] [Module A' N'] [AddCommGroup N₂']
    [Module A' N₂'] (e : N ≃+ N') (he : ∀ (t : A) n, e (t • n) = a t • e n)
    (e₂ : N₂ ≃+ N₂') (he₂ : ∀ (t : A) n, e₂ (t • n) = a t • e₂ n)
    (g : N →ₗ[A] N₂) (g' : N' →ₗ[A'] N₂') (hg : ∀ n, e₂ (g n) = g' (e n)) (x : Ind N φ) :
    Ind.transport a c h e₂ he₂ (Ind.map g x) = Ind.map g' (Ind.transport a c h e he x) := by
  induction x using Ind.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul z n =>
    rw [Ind.map_tmul, Ind.transport_tmul, Ind.transport_tmul, Ind.map_tmul, hg]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

/-- `Res.transport` commutes with `Res.map`. -/
theorem Res.transport_map {M M₂ : Type w} [AddCommGroup M] [Module B M] [AddCommGroup M₂]
    [Module B M₂] {M' M₂' : Type w} [AddCommGroup M'] [Module B' M'] [AddCommGroup M₂']
    [Module B' M₂'] (e : M ≃+ M') (he : ∀ (b : B) m, e (b • m) = c b • e m)
    (e₂ : M₂ ≃+ M₂') (he₂ : ∀ (b : B) m, e₂ (b • m) = c b • e₂ m)
    (g : M →ₗ[B] M₂) (g' : M' →ₗ[B'] M₂') (hg : ∀ m, e₂ (g m) = g' (e m)) (x : Res φ M) :
    Res.transport a c h e₂ he₂ (Res.map g x) = Res.map g' (Res.transport a c h e he x) :=
  Res.ext (hg x.val)

end Basic

section Equiv

variable {A₀ A B A₀' A' B' : Type u} [Ring A₀] [Ring A] [Ring B] [Ring A₀'] [Ring A'] [Ring B']
  {φ₂ : A₀ →ₙ+* A} {φ₁ : A →ₙ+* B} {φ₂' : A₀' →ₙ+* A'} {φ₁' : A' →ₙ+* B'}
  (a₀ : A₀ ≃+* A₀') (a : A ≃+* A') (b : B ≃+* B')
  (h₂ : ∀ t, φ₂' (a₀ t) = a (φ₂ t)) (h₁ : ∀ t, φ₁' (a t) = b (φ₁ t))
  {M M' M₂ M₂' : Type w} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A' M']
  [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₂'] [Module A' M₂']
  (e : M ≃+ M') (he : ∀ (t : A) m, e (t • m) = a t • e m)
  (e₂ : M₂ ≃+ M₂') (he₂ : ∀ (t : A) m, e₂ (t • m) = a t • e₂ m)
  (g : M →ₗ[A] M₂) (g' : M' →ₗ[A'] M₂') (hg : ∀ m, e₂ (g m) = g' (e m))

include hg

theorem resIndTransport_map (x : Res φ₁ (Ind M φ₁)) :
    resIndTransport a b h₁ e₂ he₂ (Res.map (Ind.map g) x) =
      Res.map (Ind.map g') (resIndTransport a b h₁ e he x) :=
  Res.transport_map a b h₁ _ _ _ _ _ _
    (fun y => Ind.transport_map a b h₁ e he e₂ he₂ g g' hg y) x

theorem indResTransport_map (x : Ind (Res φ₂ M) φ₂) :
    indResTransport a₀ a h₂ e₂ he₂ (Ind.map (Res.map g) x) =
      Ind.map (Res.map g') (indResTransport a₀ a h₂ e he x) :=
  Ind.transport_map a₀ a h₂ _ _ _ _ _ _
    (fun y => Res.transport_map a₀ a h₂ e he e₂ he₂ g g' hg y) x

/-- **Naturality of `resIndEquivTransport`**: if the transported isomorphisms `L`, `L₂` carry
`Res (Ind g')` to `Ind (Res g') × g'^ι`, the transports carry `Res (Ind g)` to
`Ind (Res g) × g^ι`. -/
theorem resIndEquivTransport_map (ι : Type*)
    (L : Res φ₁' (Ind M' φ₁') ≃ₗ[A'] Ind (Res φ₂' M') φ₂' × (ι → M'))
    (L₂ : Res φ₁' (Ind M₂' φ₁') ≃ₗ[A'] Ind (Res φ₂' M₂') φ₂' × (ι → M₂'))
    (hL : ∀ y, L₂ (Res.map (Ind.map g') y) =
      (Ind.map (Res.map g') (L y).1, fun s => g' ((L y).2 s)))
    (x : Res φ₁ (Ind M φ₁)) :
    resIndEquivTransport a₀ a b h₂ h₁ e₂ he₂ ι L₂ (Res.map (Ind.map g) x) =
      (Ind.map (Res.map g) (resIndEquivTransport a₀ a b h₂ h₁ e he ι L x).1,
        fun s => g ((resIndEquivTransport a₀ a b h₂ h₁ e he ι L x).2 s)) := by
  apply ((indResTransport a₀ a h₂ e₂ he₂).prodCongr
    (AddEquiv.piCongrRight fun _ => e₂)).injective
  change ((indResTransport a₀ a h₂ e₂ he₂).prodCongr _)
      (((indResTransport a₀ a h₂ e₂ he₂).prodCongr _).symm
        (L₂ (resIndTransport a b h₁ e₂ he₂ (Res.map (Ind.map g) x)))) = _
  rw [AddEquiv.apply_symm_apply, resIndTransport_map a b h₁ e he e₂ he₂ g g' hg, hL]
  set y := ((indResTransport a₀ a h₂ e he).prodCongr (AddEquiv.piCongrRight fun _ => e)).symm
    (L (resIndTransport a b h₁ e he x)) with hy
  have hy' : L (resIndTransport a b h₁ e he x) =
      ((indResTransport a₀ a h₂ e he).prodCongr (AddEquiv.piCongrRight fun _ => e)) y := by
    rw [hy, AddEquiv.apply_symm_apply]
  change _ = ((indResTransport a₀ a h₂ e₂ he₂).prodCongr _)
    (Ind.map (Res.map g) y.1, fun s => g (y.2 s))
  rw [hy']
  refine Prod.ext ?_ (funext fun s => ?_)
  · exact (indResTransport_map a₀ a h₂ e he e₂ he₂ g g' hg y.1).symm
  · exact (hg (y.2 s)).symm

/-- **Naturality of `indResEquivTransport`**: if the transported isomorphisms `L`, `L₂` carry
`Ind (Res g')` to `Res (Ind g') × g'^ι`, the transports carry `Ind (Res g)` to
`Res (Ind g) × g^ι`. -/
theorem indResEquivTransport_map (ι : Type*)
    (L : Ind (Res φ₂' M') φ₂' ≃ₗ[A'] Res φ₁' (Ind M' φ₁') × (ι → M'))
    (L₂ : Ind (Res φ₂' M₂') φ₂' ≃ₗ[A'] Res φ₁' (Ind M₂' φ₁') × (ι → M₂'))
    (hL : ∀ y, L₂ (Ind.map (Res.map g') y) =
      (Res.map (Ind.map g') (L y).1, fun s => g' ((L y).2 s)))
    (x : Ind (Res φ₂ M) φ₂) :
    indResEquivTransport a₀ a b h₂ h₁ e₂ he₂ ι L₂ (Ind.map (Res.map g) x) =
      (Res.map (Ind.map g) (indResEquivTransport a₀ a b h₂ h₁ e he ι L x).1,
        fun s => g ((indResEquivTransport a₀ a b h₂ h₁ e he ι L x).2 s)) := by
  apply ((resIndTransport a b h₁ e₂ he₂).prodCongr
    (AddEquiv.piCongrRight fun _ => e₂)).injective
  change ((resIndTransport a b h₁ e₂ he₂).prodCongr _)
      (((resIndTransport a b h₁ e₂ he₂).prodCongr _).symm
        (L₂ (indResTransport a₀ a h₂ e₂ he₂ (Ind.map (Res.map g) x)))) = _
  rw [AddEquiv.apply_symm_apply, indResTransport_map a₀ a h₂ e he e₂ he₂ g g' hg, hL]
  set y := ((resIndTransport a b h₁ e he).prodCongr (AddEquiv.piCongrRight fun _ => e)).symm
    (L (indResTransport a₀ a h₂ e he x)) with hy
  have hy' : L (indResTransport a₀ a h₂ e he x) =
      ((resIndTransport a b h₁ e he).prodCongr (AddEquiv.piCongrRight fun _ => e)) y := by
    rw [hy, AddEquiv.apply_symm_apply]
  change _ = ((resIndTransport a b h₁ e₂ he₂).prodCongr _)
    (Res.map (Ind.map g) y.1, fun s => g (y.2 s))
  rw [hy']
  refine Prod.ext ?_ (funext fun s => ?_)
  · exact (resIndTransport_map a b h₁ e he e₂ he₂ g g' hg y.1).symm
  · exact (hg (y.2 s)).symm

end Equiv

end Categorification.InductionAlong
