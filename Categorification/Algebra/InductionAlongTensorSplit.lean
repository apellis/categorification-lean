/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongEndAlg
import Categorification.Algebra.InductionAlongTransportNaturality

/-!
# Induction along a map that splits as `φ ⊗ 1`

Let `φ₀ : A₀ → B₀` be a nonunital map of `k`-algebras and suppose that, through algebra
isomorphisms `A₀ ≅ A ⊗ C` and `B₀ ≅ B ⊗ C`, it becomes `φ ⊗ 1` for a `k`-linear nonunital map
`φ : A → B`. For an `A₀`-module `M` whose restriction to `A` (through `x ↦ x ⊗ 1`) is identified
with an `A`-module `N`, induction of `M` along `φ₀` is induction of `N` along `φ`
(`splitInd`): linearly over `B` (`splitInd_smul`), compatibly with the actions of `C`
(`splitInd_one_tmul_smul`) and naturally in `M` (`splitInd_map`). In B. Webster,
*Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, this says that `ₖFᵢ` commutes with restriction to the first red strands.
-/

noncomputable section

namespace Categorification

namespace InductionAlong

open scoped TensorProduct

universe u w

variable {k : Type*} [CommRing k] {A₀ B₀ A B C : Type u} [Ring A₀] [Ring B₀] [Ring A] [Ring B]
  [Ring C] [Algebra k A₀] [Algebra k B₀] [Algebra k A] [Algebra k B] [Algebra k C]
  (a : A₀ ≃ₐ[k] A ⊗[k] C) (c : B₀ ≃ₐ[k] B ⊗[k] C) (φ₀ : A₀ →ₙ+* B₀) (φ : A →ₙ+* B)
  (hφ : ∀ (r : k) (t : A), φ (r • t) = r • φ t)
  (h : ∀ t, tensorLeft k C φ hφ (a t) = c (φ₀ t))

/-- An `A₀`-module as a module over `A ⊗ C` through `A₀ ≅ A ⊗ C`. -/
@[nolint unusedArguments]
def SplitRes (_a : A₀ ≃ₐ[k] A ⊗[k] C) (M : Type w) : Type w := M

variable (M : Type w) [AddCommGroup M] [Module k M] [Module A₀ M] [IsScalarTower k A₀ M]

instance : AddCommGroup (SplitRes a M) := inferInstanceAs (AddCommGroup M)
instance : Module k (SplitRes a M) := inferInstanceAs (Module k M)
/-- The action of `A ⊗ C` through `a⁻¹`, stated over the ring structure of `A ⊗ C` that
induction uses. -/
instance instModuleSplitResTensor : @Module (A ⊗[k] C) (SplitRes a M) Ring.toSemiring _ :=
  letI : Semiring (A ⊗[k] C) := Ring.toSemiring
  Module.compHom M a.symm.toRingEquiv.toRingHom

instance : IsScalarTower k (A ⊗[k] C) (SplitRes a M) where
  smul_assoc r t m := by
    change a.symm (r • t) • (show M from m) = r • (a.symm t • (show M from m))
    rw [map_smul]
    exact smul_assoc r (a.symm t) (show M from m)

/-- The identity `M → SplitRes M`. -/
def toSplitRes : M ≃+ SplitRes a M := AddEquiv.refl M

variable {M} {N : Type w} [AddCommGroup N] [Module A N] (e : M ≃+ N)
  (he : ∀ (x : A) (m : M), e (a.symm ((x ⊗ₜ (1 : C) : A ⊗[k] C)) • m) = x • e m)

/-- The restriction of `SplitRes M` to `A`, identified with `N`. -/
def splitResLeftEquiv : LeftFactorRes k A C (SplitRes a M) ≃ₗ[A] N where
  toFun m := e (show M from m)
  invFun n := (show LeftFactorRes k A C (SplitRes a M) from e.symm n)
  map_add' m m' := e.map_add (show M from m) (show M from m')
  map_smul' x m := he x (show M from m)
  left_inv m := e.symm_apply_apply (show M from m)
  right_inv n := e.apply_symm_apply n

/-- The transport of `Ind_{φ₀} M` to induction along `φ ⊗ 1`. -/
def splitTransport : IndK k M φ₀ ≃+ IndK k (SplitRes a M) (tensorLeft k C φ hφ) :=
  Ind.transport a.toRingEquiv c.toRingEquiv h (toSplitRes a M) fun t m => by
    change t • m = a.symm (a t) • m
    rw [AlgEquiv.symm_apply_apply]

omit [Module k M] [IsScalarTower k A₀ M] in
theorem splitTransport_smul (t : B₀) (w : IndK k M φ₀) :
    splitTransport a c φ₀ φ hφ h (t • w) = c t • splitTransport a c φ₀ φ hφ h w :=
  Ind.transport_smul _ _ _ _ _ t w

/-- **Induction along `φ₀ ≅ φ ⊗ 1`**: `Ind_{φ₀} M ≅ Ind_φ N`. -/
def splitInd : IndK k M φ₀ ≃+ IndK k N φ :=
  ((splitTransport a c φ₀ φ hφ h).trans
    (indLeftFactorEquiv φ hφ (tensorLeft k C φ hφ) (tensorLeft_tmul k C φ hφ)).toAddEquiv).trans
    (Ind.mapEquiv (splitResLeftEquiv a e he)).toAddEquiv

theorem splitInd_apply (w : IndK k M φ₀) :
    splitInd a c φ₀ φ hφ h e he w = Ind.mapEquiv (splitResLeftEquiv a e he)
      (indLeftFactorEquiv φ hφ (tensorLeft k C φ hφ) (tensorLeft_tmul k C φ hφ)
        (splitTransport a c φ₀ φ hφ h w)) := rfl

/-- **`splitInd` is `B`-linear.** -/
theorem splitInd_smul (x : B) (w : IndK k M φ₀) :
    splitInd a c φ₀ φ hφ h e he (c.symm ((x ⊗ₜ (1 : C) : B ⊗[k] C)) • w) =
      x • splitInd a c φ₀ φ hφ h e he w := by
  rw [splitInd_apply, splitTransport_smul, AlgEquiv.apply_symm_apply]
  rw [indLeftFactorEquiv_tmul_one_smul φ hφ (tensorLeft k C φ hφ) (tensorLeft_tmul k C φ hφ) x
    (splitTransport a c φ₀ φ hφ h w)]
  exact map_smul (Ind.mapEquiv (splitResLeftEquiv a e he)) x _

/-- **`splitInd` intertwines the actions of `C`.** -/
theorem splitInd_one_tmul_smul (y : C) (f : N →ₗ[A] N)
    (hf : ∀ m, e (a.symm (((1 : A) ⊗ₜ y : A ⊗[k] C)) • m) = f (e m)) (w : IndK k M φ₀) :
    splitInd a c φ₀ φ hφ h e he (c.symm (((1 : B) ⊗ₜ y : B ⊗[k] C)) • w) =
      IndK.map f (splitInd a c φ₀ φ hφ h e he w) := by
  rw [splitInd_apply, splitTransport_smul, AlgEquiv.apply_symm_apply]
  rw [indLeftFactorEquiv_one_tmul_smul φ hφ (tensorLeft k C φ hφ) (tensorLeft_tmul k C φ hφ) y
    (splitTransport a c φ₀ φ hφ h w)]
  exact IndK.map_comm_apply (k := k) (e := (splitResLeftEquiv a e he).toLinearMap)
    (fun m => hf (show M from m)) _

/-- **`splitInd` is natural.** -/
theorem splitInd_map (g : M →ₗ[A₀] M) (gN : N →ₗ[A] N) (hg : ∀ m, e (g m) = gN (e m))
    (w : IndK k M φ₀) :
    splitInd a c φ₀ φ hφ h e he (IndK.map g w) = IndK.map gN (splitInd a c φ₀ φ hφ h e he w) := by
  let gS : SplitRes a M →ₗ[A ⊗[k] C] SplitRes a M :=
    { toFun := fun m => (show SplitRes a M from g (show M from m))
      map_add' := fun m m' => g.map_add (show M from m) (show M from m')
      map_smul' := fun t m => g.map_smul (a.symm t) (show M from m) }
  have h1 : splitTransport a c φ₀ φ hφ h (IndK.map g w) =
      IndK.map gS (splitTransport a c φ₀ φ hφ h w) :=
    Ind.transport_map _ _ _ _ _ _ _ g gS (fun _ => rfl) w
  rw [splitInd_apply, splitInd_apply, h1,
    indLeftFactorEquiv_map φ hφ (tensorLeft k C φ hφ) (tensorLeft_tmul k C φ hφ) gS
      (splitTransport a c φ₀ φ hφ h w)]
  exact IndK.map_comm_apply (k := k) (e := (splitResLeftEquiv a e he).toLinearMap)
    (fun m => hg (show M from m)) _

end InductionAlong

end Categorification
