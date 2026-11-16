/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Induction.K0
import Categorification.WeightedKLR.Induction.Reflection
import Categorification.WeightedKLR.Mackey.MiddleCorner

/-!
# Restriction of finitely generated projective modules over weighted KLR algebras

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4, Theorem 2.19:
the coproduct `Δ[L] = Σ [Res_{ν';ν''} L]` of `⊕_ν K₀(W_ν)`. This file proves, over every
commutative ring `k`, the input that makes `Δ` well defined with values in
`K₀(W_{ν'} ⊗ W_{ν''})`: restriction `Res_{ν';ν''} L = e_{ν';ν''} L` sends finitely generated
projective `W_{ν'+ν''}`-modules to finitely generated projective `W_{ν'} ⊗ W_{ν''}`-modules.
The proof follows Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.16, as Webster's proof of
Theorem 2.19 indicates.

## Main definitions and results

* `InductionAlong.Res.projective_of_regular`, `InductionAlong.Res.finite_of_regular`: if
  `Res φ B` is finitely generated projective over `A`, then so is `Res φ M` for every finitely
  generated projective `B`-module `M`.
* `InductionAlong.Res.projective_of_corner`, `InductionAlong.Res.finite_of_corner`: an
  anti-involution of `B` compatible with `φ` turns the right module `B φ(1)` into the left
  module `φ(1) B = Res φ B`.
* `GalleryAlgebra.rowEquiv`: `W_ν ι(1) ≅ ⊕_{(D, u)} (e G'_u ⊗ e G''_u) (W_{ν'} ⊗ W_{ν''})` as
  right `W_{ν'} ⊗ W_{ν''}`-modules, `x ↦ Σ c_u ι(x_{(D,u)})` (the freeness step of
  Khovanov–Lauda, Proposition 2.16, from `GalleryAlgebra.parabolicCornerEquiv`).
* `Juxtapose.res_projective`, `Juxtapose.res_finite`: `Res_{ν';ν''} L` is finitely generated
  projective for `L` finitely generated projective.
* `Juxtapose.resProj`, `Juxtapose.resK0`: the coproduct component
  `Δ_{ν';ν''} : K₀(W_{ν'+ν''}) → K₀(W_{ν'} ⊗ W_{ν''})`, `[L] ↦ [Res_{ν';ν''} L]`.
-/

namespace Categorification

open MulOpposite
open scoped TensorProduct

noncomputable section

namespace InductionAlong

universe u w

variable {A : Type u} [Ring A] {B : Type u} [Ring B] (φ : A →ₙ+* B)

/-! ### Restriction of projective modules -/

section Regular

variable (M : Type w) [AddCommGroup M] [Module B M]

/-- The finite sum map `(Fin n → Res φ B) → Res φ M` attached to a map `(Fin n → B) → M`. -/
def Res.piMap {n : ℕ} (f : (Fin n → B) →ₗ[B] M) : (Fin n → Res φ B) →ₗ[A] Res φ M where
  toFun x := Res.mk (f fun i => (x i).val) (by
    rw [← map_smul]
    congr 1
    funext i
    exact (x i).prop)
  map_add' x y := Res.ext (by
    rw [Res.val_add, Res.val_mk, Res.val_mk, Res.val_mk, ← map_add]
    rfl)
  map_smul' a x := Res.ext (by
    rw [Res.val_smul, Res.val_mk, Res.val_mk, RingHom.id_apply, ← map_smul]
    rfl)

/-- The map `Res φ M → (Fin n → Res φ B)` attached to a map `M → (Fin n → B)`. -/
def Res.piSection {n : ℕ} (s : M →ₗ[B] (Fin n → B)) : Res φ M →ₗ[A] (Fin n → Res φ B) where
  toFun m i := Res.mk (s m.val i) (by
    rw [← Pi.smul_apply, ← map_smul, m.prop])
  map_add' m m' := funext fun i => Res.ext (by
    simp only [Res.val_add, Res.val_mk, map_add, Pi.add_apply])
  map_smul' a m := funext fun i => Res.ext (by
    simp only [Res.val_smul, Res.val_mk, map_smul, Pi.smul_apply, RingHom.id_apply])

theorem Res.piMap_comp_piSection {n : ℕ} (f : (Fin n → B) →ₗ[B] M) (s : M →ₗ[B] (Fin n → B))
    (h : f.comp s = LinearMap.id) :
    (Res.piMap φ M f).comp (Res.piSection φ M s) = LinearMap.id :=
  LinearMap.ext fun m => Res.ext (by
    change f (fun i => s m.val i) = m.val
    exact LinearMap.congr_fun h m.val)

theorem Res.exists_piMap [Module.Finite B M] [Module.Projective B M] :
    ∃ (n : ℕ) (f : (Fin n → B) →ₗ[B] M) (s : M →ₗ[B] (Fin n → B)), f.comp s = LinearMap.id := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' B M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  exact ⟨n, f, s, hs⟩

/-- **Restriction of finitely generated projective modules**: if `Res φ B` is projective over
`A`, then `Res φ M` is projective for every finitely generated projective `B`-module `M`. -/
theorem Res.projective_of_regular [Module.Projective A (Res φ B)] [Module.Finite B M]
    [Module.Projective B M] : Module.Projective A (Res φ M) := by
  obtain ⟨n, f, s, h⟩ := Res.exists_piMap (B := B) M
  have : Module.Projective A (Fin n → Res φ B) :=
    Module.Projective.of_equiv' (DFinsupp.linearEquivFunOnFintype (R := A))
  exact Module.Projective.of_split (Res.piSection φ M s) (Res.piMap φ M f)
    (Res.piMap_comp_piSection φ M f s h)

/-- If `Res φ B` is finitely generated over `A`, then so is `Res φ M` for every finitely
generated projective `B`-module `M`. -/
theorem Res.finite_of_regular [Module.Finite A (Res φ B)] [Module.Finite B M]
    [Module.Projective B M] : Module.Finite A (Res φ M) := by
  obtain ⟨n, f, s, h⟩ := Res.exists_piMap (B := B) M
  exact Module.Finite.of_surjective (Res.piMap φ M f) fun m =>
    ⟨Res.piSection φ M s m, LinearMap.congr_fun (Res.piMap_comp_piSection φ M f s h) m⟩

end Regular

/-! ### From the right corner to the left corner -/

section Reflection

variable {φ} (ρ : B →+ B) (hρ : ∀ x y, ρ (x * y) = ρ y * ρ x) (hρρ : ∀ x, ρ (ρ x) = x)
  (τ : A ≃+* Aᵐᵒᵖ) (hτ : ∀ a, ρ (φ a) = φ (τ a).unop)

include hτ in
theorem rho_unit : ρ (φ 1) = φ 1 := by rw [hτ, map_one, unop_one]

/-- An anti-involution `ρ` of `B` with `ρ ∘ φ = φ ∘ τ` identifies the right `A`-module `B φ(1)`
with the left `A`-module `φ(1) B = Res φ B` (`cornerResAddEquiv_smul`). -/
def cornerResAddEquiv : Corner φ ≃+ Res φ B where
  toFun z := Res.mk (ρ z.1) (by
    obtain ⟨y, hy⟩ := z
    change φ 1 * ρ y = ρ y
    conv_lhs => rw [← rho_unit ρ τ hτ, ← hρ, mem_lIdeal.1 hy])
  invFun m := ⟨ρ m.val, by
    change ρ m.val * φ 1 = ρ m.val
    rw [← rho_unit ρ τ hτ, ← hρ]
    exact congrArg ρ m.prop⟩
  map_add' z z' := Res.ext (by simp)
  left_inv z := Subtype.ext (hρρ z.1)
  right_inv m := Res.ext (hρρ m.val)

/-- `cornerResAddEquiv` is semilinear along `τ⁻¹ : Aᵐᵒᵖ → A`. -/
theorem cornerResAddEquiv_smul (r : Aᵐᵒᵖ) (z : Corner φ) :
    cornerResAddEquiv ρ hρ hρρ τ hτ (r • z) = τ.symm r • cornerResAddEquiv ρ hρ hρρ τ hτ z :=
  Res.ext (by
    change ρ (z.1 * φ r.unop) = φ (τ.symm r) * ρ z.1
    rw [hρ]
    congr 1
    rw [← hρρ (φ (τ.symm r)), hτ (τ.symm r), RingEquiv.apply_symm_apply])

include hρ hρρ hτ in
/-- `Res φ B` is projective over `A` if `B φ(1)` is projective over `Aᵐᵒᵖ`. -/
theorem Res.projective_of_corner [Module.Projective Aᵐᵒᵖ (Corner φ)] :
    Module.Projective A (Res φ B) := by
  have := RingHomInvPair.of_ringEquiv τ.symm
  have := RingHomInvPair.of_ringEquiv_symm τ.symm
  let e : Corner φ ≃ₛₗ[(τ.symm : Aᵐᵒᵖ →+* A)] Res φ B :=
    { cornerResAddEquiv ρ hρ hρρ τ hτ with
      map_smul' := cornerResAddEquiv_smul ρ hρ hρρ τ hτ }
  exact Module.Projective.of_equiv e

include hρ hρρ hτ in
/-- `Res φ B` is finitely generated over `A` if `B φ(1)` is finitely generated over `Aᵐᵒᵖ`. -/
theorem Res.finite_of_corner [Module.Finite Aᵐᵒᵖ (Corner φ)] : Module.Finite A (Res φ B) := by
  have := RingHomInvPair.of_ringEquiv τ.symm
  have := RingHomInvPair.of_ringEquiv_symm τ.symm
  let e : Corner φ ≃ₛₗ[(τ.symm : Aᵐᵒᵖ →+* A)] Res φ B :=
    { cornerResAddEquiv ρ hρ hρρ τ hτ with
      map_smul' := cornerResAddEquiv_smul ρ hρ hρρ τ hτ }
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

end Reflection

/-! ### Isomorphisms and direct sums -/

section Congr

variable {M M' : Type w} [AddCommGroup M] [Module B M] [AddCommGroup M'] [Module B M']

/-- `Res φ M ≅ Res φ M'` for `M ≅ M'`. -/
def Res.congr (e : M ≃ₗ[B] M') : Res φ M ≃ₗ[A] Res φ M' :=
  LinearEquiv.ofLinearMap (Res.map (φ := φ) e.toLinearMap) (Res.map (φ := φ) e.symm.toLinearMap)
    (LinearMap.ext fun m => Res.ext (e.apply_symm_apply m.val))
    (LinearMap.ext fun m => Res.ext (e.symm_apply_apply m.val))

variable (M M') in
/-- `Res φ (M × M') ≅ Res φ M × Res φ M'`. -/
def Res.prodEquiv : Res φ (M × M') ≃ₗ[A] Res φ M × Res φ M' where
  toFun m := (Res.mk m.val.1 (congrArg Prod.fst m.prop), Res.mk m.val.2 (congrArg Prod.snd m.prop))
  invFun m := Res.mk (m.1.val, m.2.val) (Prod.ext m.1.prop m.2.prop)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end Congr

end InductionAlong

/-! ### Right ideals of idempotents -/

section RightIdeal

variable {R : Type*} [Ring R] {f : R}

/-- `y ↦ f y`, the projection of `R` onto the right ideal `f R`. -/
def rIdealProj (hf : IsIdempotentElem f) : R →ₗ[Rᵐᵒᵖ] rIdeal f where
  toFun y := ⟨f * y, by rw [mem_rIdeal, ← mul_assoc, hf.eq]⟩
  map_add' x y := Subtype.ext (mul_add f x y)
  map_smul' r y := Subtype.ext (by
    change f * (y * r.unop) = f * y * r.unop
    rw [mul_assoc])

theorem rIdealProj_comp_subtype (hf : IsIdempotentElem f) :
    (rIdealProj hf).comp (rIdeal f).subtype = LinearMap.id :=
  LinearMap.ext fun y => Subtype.ext y.2

variable (R) in
/-- `R` is the regular right `R`-module. -/
def opRegularEquiv : Rᵐᵒᵖ ≃ₗ[Rᵐᵒᵖ] R where
  toFun := unop
  invFun := op
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The right ideal `f R` is a projective right `R`-module. -/
theorem rIdeal_projective (hf : IsIdempotentElem f) : Module.Projective Rᵐᵒᵖ (rIdeal f) :=
  have : Module.Projective Rᵐᵒᵖ R := Module.Projective.of_equiv (opRegularEquiv R)
  Module.Projective.of_split (rIdeal f).subtype (rIdealProj hf) (rIdealProj_comp_subtype hf)

/-- The right ideal `f R` is a cyclic right `R`-module. -/
theorem rIdeal_finite (hf : IsIdempotentElem f) : Module.Finite Rᵐᵒᵖ (rIdeal f) :=
  have : Module.Finite Rᵐᵒᵖ R := Module.Finite.equiv (opRegularEquiv R)
  Module.Finite.of_surjective (rIdealProj hf) fun y =>
    ⟨y, LinearMap.congr_fun (rIdealProj_comp_subtype hf) y⟩

end RightIdeal

namespace WeightedKLR

open FullChamber GalleryAlgebra Juxtapose InductionAlong

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace GalleryAlgebra

attribute [local instance] ColPerm.fintype

open scoped Classical

section Unit

variable {ν : I →₀ ℕ}

/-- `1 = ∑_C e C` in `W_ν`, over the rank-ordered chambers `C`. -/
theorem one_eq_sum_rankE : (1 : WeightedKLRAlgebra k Γ ν) =
    ∑ C : {C : FullChamber Γ ν // C.IsRankOrdered}, rankE k C.2 := by
  refine Subtype.ext ?_
  refine Eq.trans ?_ (map_sum (IsIdempotentElem.cornerVal (R := k)
    (isIdempotentElem_rankIdem (k := k) (Γ := Γ) (ν := ν)))
    (fun C : {C : FullChamber Γ ν // C.IsRankOrdered} => rankE k C.2) Finset.univ).symm
  exact Finset.sum_subtype _ (fun C => by simp) (fun C => (e C : GalleryAlgebra k Γ ν))

variable (k) in
/-- `x ↦ e G x e C`, from `W_ν` to the corner `e G A e C`. -/
def sandW (G C : FullChamber Γ ν) : WeightedKLRAlgebra k Γ ν →ₗ[k] cornerSpace k G C where
  toFun x := ⟨e G * x.1 * e C, ⟨x.1, sandwich_apply _ _ _⟩⟩
  map_add' x y := Subtype.ext (by
    change e G * (x.1 + y.1) * e C = e G * x.1 * e C + e G * y.1 * e C
    rw [mul_add, add_mul])
  map_smul' c x := Subtype.ext (by
    change e G * (c • x.1) * e C = c • (e G * x.1 * e C)
    rw [mul_smul_comm, smul_mul_assoc])

theorem cornerW_sandW {G C : FullChamber Γ ν} (hG : G.IsRankOrdered) (hC : C.IsRankOrdered)
    (x : WeightedKLRAlgebra k Γ ν) :
    cornerW k hG hC (sandW k G C x) = rankE k hG * x * rankE k hC := rfl

theorem cornerW_injective {G C : FullChamber Γ ν} (hG : G.IsRankOrdered)
    (hC : C.IsRankOrdered) : Function.Injective (cornerW k hG hC) :=
  fun _ _ h => Subtype.ext (congrArg (fun w => (w : WeightedKLRAlgebra k Γ ν).1) h)

end Unit

section Row

variable {ν' ν'' : I →₀ ℕ}

variable (k) in
/-- The piece `e G'_u A e C' ⊗ e G''_u A e C''` attached to `p = (D, u)`; this is
`ParabolicPiece k D C' C'' u`, written with `repLeft`, `repRight`. -/
abbrev RowPiece (p : RowGen Γ ν' ν'') (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') :
    Type _ :=
  cornerSpace k (repLeft p.2) C' ⊗[k] cornerSpace k (repRight p.2) C''

variable (k) in
/-- The idempotent `e G'_u ⊗ e G''_u` of `W_{ν'} ⊗ W_{ν''}` attached to an index `(D, u)`. -/
noncomputable def rowIdem (p : RowGen Γ ν' ν'') :
    WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'' :=
  rankE k (isRankOrdered_repLeft p.2) ⊗ₜ rankE k (isRankOrdered_repRight p.2)

theorem isIdempotentElem_rowIdem (p : RowGen Γ ν' ν'') : IsIdempotentElem (rowIdem k p) := by
  rw [IsIdempotentElem, rowIdem, Algebra.TensorProduct.tmul_mul_tmul, rankE_mul_rankE,
    rankE_mul_rankE]

/-- `1 = ∑_{C', C''} e C' ⊗ e C''` in `W_{ν'} ⊗ W_{ν''}`. -/
theorem one_tensor_eq_sum :
    (1 : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') =
      ∑ C' : {C : FullChamber Γ ν' // C.IsRankOrdered},
        ∑ C'' : {C : FullChamber Γ ν'' // C.IsRankOrdered}, rankE k C'.2 ⊗ₜ rankE k C''.2 := by
  rw [Algebra.TensorProduct.one_def, one_eq_sum_rankE, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun C' _ => ?_
  rw [one_eq_sum_rankE, TensorProduct.tmul_sum]

variable (k) in
/-- The component of `y ∈ W_{ν'} ⊗ W_{ν''}` in the piece `e G'_u A e C' ⊗ e G''_u A e C''`. -/
noncomputable def pieceProj (p : RowGen Γ ν' ν'') (C' : FullChamber Γ ν')
    (C'' : FullChamber Γ ν'') :
    WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'' →ₗ[k]
      RowPiece k p C' C'' :=
  TensorProduct.map (sandW k (repLeft p.2) C') (sandW k (repRight p.2) C'')

/-- `(e G' ⊗ e G'') y (e C' ⊗ e C'')` is the image of the component `pieceProj`. -/
theorem rowIdem_mul_mul_eq (p : RowGen Γ ν' ν'') {C' : FullChamber Γ ν'}
    {C'' : FullChamber Γ ν''} (hC' : C'.IsRankOrdered) (hC'' : C''.IsRankOrdered)
    (y : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :
    rowIdem k p * y * (rankE k hC' ⊗ₜ rankE k hC'') =
      TensorProduct.map (cornerW k (isRankOrdered_repLeft p.2) hC')
        (cornerW k (isRankOrdered_repRight p.2) hC'') (pieceProj k p C' C'' y) := by
  induction y using TensorProduct.inductionOn with
  | tmul a b =>
    rw [rowIdem, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      pieceProj, TensorProduct.map_tmul, TensorProduct.map_tmul, cornerW_sandW, cornerW_sandW]
  | add a b ha hb => rw [mul_add, add_mul, ha, hb, map_add, map_add]

/-- `ι` on a piece is `galleryTensorHom` on the underlying tensor. -/
theorem inductionMap_map_cornerW (p : RowGen Γ ν' ν'') {C' : FullChamber Γ ν'}
    {C'' : FullChamber Γ ν''} (hC' : C'.IsRankOrdered) (hC'' : C''.IsRankOrdered)
    (y : RowPiece k p C' C'') :
    (inductionMap k Γ ν' ν'' (TensorProduct.map (cornerW k (isRankOrdered_repLeft p.2) hC')
      (cornerW k (isRankOrdered_repRight p.2) hC'') y)).1 =
      (galleryTensorHom k Γ ν' ν''
        (TensorProduct.map (Submodule.subtype _) (Submodule.subtype _) y)).1 := by
  induction y using TensorProduct.inductionOn with
  | tmul a b => rw [TensorProduct.map_tmul, TensorProduct.map_tmul, inductionMap_tmul]; rfl
  | add a b ha hb => simp only [map_add]; exact congrArg₂ (· + ·) ha hb

variable (k) in
/-- The element `∑_p c_p ι(x_p)` of `W_{ν'+ν''} ι(1)`. -/
noncomputable def rowVal (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (x : ∀ p : RowGen Γ ν' ν'', rIdeal (rowIdem k p)) : WeightedKLRAlgebra k Γ (ν' + ν'') :=
  ∑ p, rowGen k hD hZ p * inductionMap k Γ ν' ν'' (x p).1

variable (k) in
/-- The map `⊕_{(D, u)} (e G'_u ⊗ e G''_u)(W_{ν'} ⊗ W_{ν''}) → W_{ν'+ν''} ι(1)`,
`x ↦ ∑ c_u ι(x_{(D,u)})`, of right `W_{ν'} ⊗ W_{ν''}`-modules. -/
noncomputable def rowMap (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) :
    (∀ p : RowGen Γ ν' ν'', rIdeal (rowIdem k p)) →ₗ[(WeightedKLRAlgebra k Γ ν' ⊗[k]
      WeightedKLRAlgebra k Γ ν'')ᵐᵒᵖ] Corner (inductionRingHom k Γ ν' ν'') where
  toFun x := ⟨rowVal k hD hZ x, Submodule.sum_mem _ fun p _ =>
    mul_mem_corner (inductionRingHom k Γ ν' ν'') _ _⟩
  map_add' x y := Subtype.ext (by
    change rowVal k hD hZ (x + y) = rowVal k hD hZ x + rowVal k hD hZ y
    simp only [rowVal, Pi.add_apply, Submodule.coe_add, map_add, mul_add,
      Finset.sum_add_distrib])
  map_smul' r x := Subtype.ext (by
    change ∑ p, rowGen k hD hZ p * inductionMap k Γ ν' ν'' ((x p).1 * r.unop) =
      (∑ p, rowGen k hD hZ p * inductionMap k Γ ν' ν'' (x p).1) * inductionMap k Γ ν' ν'' r.unop
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, mul_assoc])

variable {P : FullChamber Γ (ν' + ν'') → FullChamber Γ (ν' + ν'') →
    (Strand (ν' + ν'') → 𝕜) × (Strand (ν' + ν'') → 𝕜)}
  {P' : FullChamber Γ ν' → FullChamber Γ ν' → (Strand ν' → 𝕜) × (Strand ν' → 𝕜)}
  {P'' : FullChamber Γ ν'' → FullChamber Γ ν'' → (Strand ν'' → 𝕜) × (Strand ν'' → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hP' : ∀ C E, IsChamberSegment C E (P' C E))
  (hP'' : ∀ C E, IsChamberSegment C E (P'' C E))
  (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hΓ : Γ.PSymm)
  (hW : ∀ w : Wall Γ (ν' + ν''), IsRegular (w.factor (k := k)))
  (hW' : ∀ w : Wall Γ ν', IsRegular (w.factor (k := k)))
  (hW'' : ∀ w : Wall Γ ν'', IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand (ν' + ν'')), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))
  (hL' : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν'), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))
  (hL'' : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν''), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

variable (k) in
/-- `parabolicCornerEquiv`, with the pieces written as `RowPiece`. -/
noncomputable def rowCornerEquiv {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    (hC' : C'.IsRankOrdered) (hC'' : C''.IsRankOrdered)
    (D : {D : FullChamber Γ (ν' + ν'') // D.IsRankOrdered}) :
    (∀ u : ParabolicRep ν' D.1, RowPiece k ⟨D, u⟩ C' C'') ≃ₗ[k]
      cornerSpace k D.1 (chamber C' C'') :=
  parabolicCornerEquiv hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL''
    ((isRankOrdered_chamber_iff C' C'').2 ⟨hC', hC''⟩) D.2

/-- `rowCornerEquiv` of a single piece, in `W_{ν'+ν''}`. -/
theorem cornerW_rowCornerEquiv_single {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    (hC' : C'.IsRankOrdered) (hC'' : C''.IsRankOrdered) (D : {D : FullChamber Γ (ν' + ν'') //
      D.IsRankOrdered}) (u : ParabolicRep ν' D.1) (y : RowPiece k ⟨D, u⟩ C' C'') :
    cornerW k D.2 ((isRankOrdered_chamber_iff C' C'').2 ⟨hC', hC''⟩)
      (rowCornerEquiv k hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' hC' hC'' D
        (Pi.single u y)) =
      rowGen k hD hZ ⟨D, u⟩ * inductionMap k Γ ν' ν''
        (TensorProduct.map (cornerW k (isRankOrdered_repLeft u) hC')
          (cornerW k (isRankOrdered_repRight u) hC'') y) := by
  refine Subtype.ext ?_
  have h := parabolicCornerEquiv_single hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL''
    ((isRankOrdered_chamber_iff C' C'').2 ⟨hC', hC''⟩) D.2 u y
  refine h.trans ?_
  exact congrArg (cosetElt k hD hZ ν' u.1 D.1 * ·)
    (inductionMap_map_cornerW (p := ⟨D, u⟩) hC' hC'' y).symm

/-- **The pieces of `x` are the corners of `∑ c_p ι(x_p)`**: `parabolicCornerEquiv` of the
components of `x` at `(D, -)` is `e D (∑ c_p ι(x_p)) ι(e C' ⊗ e C'')`. -/
theorem cornerW_parabolicCornerEquiv_pieceProj {C' : FullChamber Γ ν'}
    {C'' : FullChamber Γ ν''} (hC' : C'.IsRankOrdered) (hC'' : C''.IsRankOrdered)
    (D : {D : FullChamber Γ (ν' + ν'') // D.IsRankOrdered})
    (x : ∀ p : RowGen Γ ν' ν'', rIdeal (rowIdem k p)) :
    cornerW k D.2 ((isRankOrdered_chamber_iff C' C'').2 ⟨hC', hC''⟩)
      (rowCornerEquiv k hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' hC' hC'' D
        (fun u => pieceProj k ⟨D, u⟩ C' C'' (x ⟨D, u⟩).1)) =
      rankE k D.2 * rowVal k hD hZ x * inductionMap k Γ ν' ν'' (rankE k hC' ⊗ₜ rankE k hC'') := by
  rw [← Finset.univ_sum_single (fun u => pieceProj k ⟨D, u⟩ C' C'' (x ⟨D, u⟩).1), map_sum,
    map_sum]
  simp only [cornerW_rowCornerEquiv_single hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'']
  rw [rowVal, Finset.mul_sum, Finset.sum_mul, Fintype.sum_sigma,
    Finset.sum_eq_single D]
  · refine Finset.sum_congr rfl fun u _ => ?_
    have hx : rowIdem k ⟨D, u⟩ * (x ⟨D, u⟩).1 = (x ⟨D, u⟩).1 := (x ⟨D, u⟩).2
    have hc : rankE k D.2 * rowGen k hD hZ ⟨D, u⟩ = rowGen k hD hZ ⟨D, u⟩ := by
      rw [rowGen, rankE_mul_cosetW]
      exact ite_eq_left rfl
    rw [← rowIdem_mul_mul_eq ⟨D, u⟩ hC' hC'' (x ⟨D, u⟩).1, hx, map_mul, ← mul_assoc,
      ← mul_assoc, hc]
  · intro D' _ hD'
    refine Finset.sum_eq_zero fun u _ => ?_
    have hc : rankE k D.2 * rowGen k hD hZ ⟨D', u⟩ = 0 := by
      rw [rowGen, rankE_mul_cosetW]
      exact ite_eq_right (fun h => hD' (Subtype.ext h.symm))
    rw [← mul_assoc, hc, zero_mul, zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem rowVal_single (p : RowGen Γ ν' ν'') (y : rIdeal (rowIdem k p)) :
    rowVal k hD hZ (Pi.single p y) = rowGen k hD hZ p * inductionMap k Γ ν' ν'' y.1 := by
  rw [rowVal, Finset.sum_eq_single p (fun p' _ hp' => by
    rw [Pi.single_eq_of_ne hp', ZeroMemClass.coe_zero, map_zero, mul_zero])
    (fun h => (h (Finset.mem_univ _)).elim), Pi.single_eq_same]

theorem rowVal_zero : rowVal k hD hZ (0 : ∀ p : RowGen Γ ν' ν'', rIdeal (rowIdem k p)) = 0 := by
  rw [rowVal]
  exact Finset.sum_eq_zero fun p _ => by
    rw [Pi.zero_apply, ZeroMemClass.coe_zero, map_zero, mul_zero]

theorem rowVal_add (x y : ∀ p : RowGen Γ ν' ν'', rIdeal (rowIdem k p)) :
    rowVal k hD hZ (x + y) = rowVal k hD hZ x + rowVal k hD hZ y := by
  rw [rowVal, rowVal, rowVal, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Pi.add_apply, Submodule.coe_add, map_add, mul_add]

theorem rowVal_sub (x y : ∀ p : RowGen Γ ν' ν'', rIdeal (rowIdem k p)) :
    rowVal k hD hZ (x - y) = rowVal k hD hZ x - rowVal k hD hZ y := by
  rw [rowVal, rowVal, rowVal, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Pi.sub_apply, Submodule.coe_sub, map_sub, mul_sub]

theorem rowVal_smul (c : k) (x : ∀ p : RowGen Γ ν' ν'', rIdeal (rowIdem k p)) :
    rowVal k hD hZ (fun p => MulOpposite.op (algebraMap k
      (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') c) • x p) =
      c • rowVal k hD hZ x := by
  rw [rowVal, rowVal, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Submodule.coe_smul, op_smul_eq_mul, Algebra.algebraMap_eq_smul_one,
    mul_smul_comm, mul_one, map_smul, mul_smul_comm]

include hP hP' hP'' hΓ hW hW' hW'' hL hL' hL'' in
theorem eq_zero_of_rowVal_eq_zero {x : ∀ p : RowGen Γ ν' ν'', rIdeal (rowIdem k p)}
    (hx : rowVal k hD hZ x = 0) : x = 0 := by
  have hpiece : ∀ (p : RowGen Γ ν' ν'') (C' : {C : FullChamber Γ ν' // C.IsRankOrdered})
      (C'' : {C : FullChamber Γ ν'' // C.IsRankOrdered}),
      pieceProj k p C'.1 C''.1 (x p).1 = 0 := by
    intro p C' C''
    have h := cornerW_parabolicCornerEquiv_pieceProj hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL'
      hL'' C'.2 C''.2 p.1 x
    rw [hx, mul_zero, zero_mul, ← map_zero (cornerW k p.1.2
      ((isRankOrdered_chamber_iff C'.1 C''.1).2 ⟨C'.2, C''.2⟩))] at h
    have h2 := (rowCornerEquiv k hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' C'.2 C''.2
      p.1).injective ((cornerW_injective _ _ h).trans (map_zero _).symm)
    exact congrFun h2 p.2
  funext p
  refine Subtype.ext ?_
  rw [Pi.zero_apply, ZeroMemClass.coe_zero]
  have hx2 : rowIdem k p * (x p).1 = (x p).1 := (x p).2
  rw [← hx2, ← mul_one (rowIdem k p * (x p).1), one_tensor_eq_sum, Finset.mul_sum]
  refine Finset.sum_eq_zero fun C' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun C'' _ => ?_
  rw [rowIdem_mul_mul_eq p C'.2 C''.2, hpiece, map_zero]

include hP hP' hP'' hΓ hW hW' hW'' hL hL' hL'' in
theorem rowMap_injective : Function.Injective (rowMap k hD hZ (ν' := ν') (ν'' := ν'')) := by
  intro x y hxy
  have h : rowVal k hD hZ x = rowVal k hD hZ y := congrArg Subtype.val hxy
  have h' : rowVal k hD hZ (x - y) = 0 := by rw [rowVal_sub hD hZ, h, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_rowVal_eq_zero hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' h')

include hP hΓ hW hL in
theorem rowMap_surjective : Function.Surjective (rowMap k hD hZ (ν' := ν') (ν'' := ν'')) := by
  intro z
  suffices h : ∃ x, rowVal k hD hZ x = z.1 from
    let ⟨x, hx⟩ := h; ⟨x, Subtype.ext hx⟩
  have hz : z.1 * inductionMap k Γ ν' ν'' 1 = z.1 := z.2
  rw [← hz]
  refine Submodule.span_induction (p := fun w _ => ∃ x, rowVal k hD hZ x = w) ?_ ?_ ?_ ?_
    (mul_inductionMap_one_mem_span hP hD hZ hΓ hW hL z.1)
  · rintro _ ⟨⟨p, y⟩, rfl⟩
    refine ⟨Pi.single p (rIdealProj (isIdempotentElem_rowIdem p) y), ?_⟩
    rw [rowVal_single]
    show rowGen k hD hZ p * inductionMap k Γ ν' ν'' (rowIdem k p * y) = _
    rw [map_mul, ← mul_assoc, rowIdem, rowGen, cosetW_mul_inductionMap_rankE]
    rfl
  · exact ⟨0, rowVal_zero hD hZ⟩
  · rintro _ _ _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, rowVal_add hD hZ x y⟩
  · rintro c _ _ ⟨x, rfl⟩
    exact ⟨_, rowVal_smul hD hZ c x⟩

include hP hP' hP'' hΓ hW hW' hW'' hL hL' hL'' in
theorem rowMap_bijective : Function.Bijective (rowMap k hD hZ (ν' := ν') (ν'' := ν'')) :=
  ⟨rowMap_injective hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'',
    rowMap_surjective hP hD hZ hΓ hW hL⟩

variable (k) in
/-- **Freeness of `W_{ν'+ν''} ι(1)` over `W_{ν'} ⊗ W_{ν''}`** (the step of Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.16, used in Webster, arXiv:1209.2463v4, Theorem 2.19): as a
right `W_{ν'} ⊗ W_{ν''}`-module, `W_{ν'+ν''} ι(1) ≅ ⊕_{(D, u)} (e G'_u ⊗ e G''_u)
(W_{ν'} ⊗ W_{ν''})`, `x ↦ ∑ c_u ι(x_{(D,u)})`, over the rank-ordered chambers `D` and the
representatives `u` for `D`. -/
noncomputable def rowEquiv :
    (∀ p : RowGen Γ ν' ν'', rIdeal (rowIdem k p)) ≃ₗ[(WeightedKLRAlgebra k Γ ν' ⊗[k]
      WeightedKLRAlgebra k Γ ν'')ᵐᵒᵖ] Corner (inductionRingHom k Γ ν' ν'') :=
  { rowMap k hD hZ, Equiv.ofBijective _
      (rowMap_bijective hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'') with }

theorem rowEquiv_apply (x : ∀ p : RowGen Γ ν' ν'', rIdeal (rowIdem k p)) :
    (rowEquiv k hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' x).1 =
      ∑ p, rowGen k hD hZ p * inductionMap k Γ ν' ν'' (x p).1 := rfl

include hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' in
/-- `W_{ν'+ν''} ι(1)` is a projective right `W_{ν'} ⊗ W_{ν''}`-module. -/
theorem corner_projective :
    Module.Projective (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')ᵐᵒᵖ
      (Corner (inductionRingHom k Γ ν' ν'')) := by
  have : ∀ p : RowGen Γ ν' ν'', Module.Projective _ (rIdeal (rowIdem k p)) :=
    fun p => rIdeal_projective (isIdempotentElem_rowIdem p)
  have : Module.Projective (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')ᵐᵒᵖ
      (∀ p : RowGen Γ ν' ν'', rIdeal (rowIdem k p)) :=
    Module.Projective.of_equiv' (DFinsupp.linearEquivFunOnFintype (R := _))
  exact Module.Projective.of_equiv (rowEquiv k hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'')

include hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' in
/-- `W_{ν'+ν''} ι(1)` is a finitely generated right `W_{ν'} ⊗ W_{ν''}`-module. -/
theorem corner_finite :
    Module.Finite (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')ᵐᵒᵖ
      (Corner (inductionRingHom k Γ ν' ν'')) := by
  have : ∀ p : RowGen Γ ν' ν'', Module.Finite _ (rIdeal (rowIdem k p)) :=
    fun p => rIdeal_finite (isIdempotentElem_rowIdem p)
  exact Module.Finite.equiv (rowEquiv k hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'')

end Row

end GalleryAlgebra

namespace Juxtapose

section Restriction

variable {ν' ν'' : I →₀ ℕ}

variable (k ν' ν'') in
/-- The reflection `ρ ⊗ ρ` of `W_{ν'} ⊗ W_{ν''}`. -/
noncomputable def reflectTensor (hΓ : Γ.PSymm) :
    WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'' →ₗ[k]
      WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'' :=
  TensorProduct.map (reflectW k ν' hΓ) (reflectW k ν'' hΓ)

theorem reflectTensor_reflectTensor (hΓ : Γ.PSymm)
    (z : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :
    reflectTensor k ν' ν'' hΓ (reflectTensor k ν' ν'' hΓ z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp [reflectTensor, reflectW_reflectW]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem reflectTensor_mul (hΓ : Γ.PSymm)
    (z w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :
    reflectTensor k ν' ν'' hΓ (z * w) =
      reflectTensor k ν' ν'' hΓ w * reflectTensor k ν' ν'' hΓ z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [add_mul, map_add, hx, hy, map_add, mul_add]
  | tmul x y =>
    induction w using TensorProduct.inductionOn with
    | add u u' hu hu' => rw [mul_add, map_add, hu, hu', map_add, add_mul]
    | tmul u u' =>
      simp only [reflectTensor, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul,
        reflectW_mul]

variable (k ν' ν'') in
/-- `ρ ⊗ ρ` as a ring isomorphism `W_{ν'} ⊗ W_{ν''} ≅ (W_{ν'} ⊗ W_{ν''})ᵐᵒᵖ`. -/
noncomputable def reflectTensorEquiv (hΓ : Γ.PSymm) :
    WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'' ≃+*
      (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')ᵐᵒᵖ where
  toFun z := op (reflectTensor k ν' ν'' hΓ z)
  invFun z := reflectTensor k ν' ν'' hΓ z.unop
  left_inv z := reflectTensor_reflectTensor hΓ z
  right_inv z := unop_injective (reflectTensor_reflectTensor hΓ z.unop)
  map_mul' z w := by
    rw [reflectTensor_mul, op_mul]
  map_add' z w := by rw [map_add, op_add]

variable (Γ ν' ν'') in
/-- **Restriction preserves projectivity** (Webster, arXiv:1209.2463v4, §2.4, input to
Theorem 2.19; Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.16): under Webster's standing
hypothesis, `Res_{ν';ν''} L` is a projective `W_{ν'} ⊗ W_{ν''}`-module for every finitely
generated projective `W_{ν'+ν''}`-module `L`, over any commutative ring `k`. -/
theorem res_projective (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) (L : Type*)
    [AddCommGroup L] [Module (WeightedKLRAlgebra k Γ (ν' + ν'')) L]
    [Module.Finite (WeightedKLRAlgebra k Γ (ν' + ν'')) L]
    [Module.Projective (WeightedKLRAlgebra k Γ (ν' + ν'')) L] :
    Module.Projective (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (res k Γ ν' ν'' L) := by
  choose P hP using fun C E : FullChamber Γ (ν' + ν'') => exists_isChamberSegment hD hZ C E
  choose P' hP' using fun C E : FullChamber Γ ν' => exists_isChamberSegment hD hZ C E
  choose P'' hP'' using fun C E : FullChamber Γ ν'' => exists_isChamberSegment hD hZ C E
  have := corner_projective hP hP' hP'' hD hZ hS.psymm (fun w => hS.isRegular_factor w)
    (fun w => hS.isRegular_factor w) (fun w => hS.isRegular_factor w)
    hS.isRegular_loopFactor' hS.isRegular_loopFactor' hS.isRegular_loopFactor'
  have : Module.Projective (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (InductionAlong.Res (inductionRingHom k Γ ν' ν'') (WeightedKLRAlgebra k Γ (ν' + ν''))) :=
    Res.projective_of_corner (reflectW k (ν' + ν'') hS.psymm).toAddMonoidHom
      (reflectW_mul hS.psymm) (reflectW_reflectW hS.psymm) (reflectTensorEquiv k ν' ν'' hS.psymm)
      (fun a => reflectW_inductionMap hS.psymm a)
  exact Res.projective_of_regular _ L

variable (Γ ν' ν'') in
/-- **Restriction preserves finite generation** (Webster, arXiv:1209.2463v4, §2.4): under
Webster's standing hypothesis, `Res_{ν';ν''} L` is finitely generated over
`W_{ν'} ⊗ W_{ν''}` for every finitely generated projective `W_{ν'+ν''}`-module `L`. -/
theorem res_finite (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) (L : Type*)
    [AddCommGroup L] [Module (WeightedKLRAlgebra k Γ (ν' + ν'')) L]
    [Module.Finite (WeightedKLRAlgebra k Γ (ν' + ν'')) L]
    [Module.Projective (WeightedKLRAlgebra k Γ (ν' + ν'')) L] :
    Module.Finite (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (res k Γ ν' ν'' L) := by
  choose P hP using fun C E : FullChamber Γ (ν' + ν'') => exists_isChamberSegment hD hZ C E
  choose P' hP' using fun C E : FullChamber Γ ν' => exists_isChamberSegment hD hZ C E
  choose P'' hP'' using fun C E : FullChamber Γ ν'' => exists_isChamberSegment hD hZ C E
  have := corner_finite hP hP' hP'' hD hZ hS.psymm (fun w => hS.isRegular_factor w)
    (fun w => hS.isRegular_factor w) (fun w => hS.isRegular_factor w)
    hS.isRegular_loopFactor' hS.isRegular_loopFactor' hS.isRegular_loopFactor'
  have : Module.Finite (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (InductionAlong.Res (inductionRingHom k Γ ν' ν'') (WeightedKLRAlgebra k Γ (ν' + ν''))) :=
    Res.finite_of_corner (reflectW k (ν' + ν'') hS.psymm).toAddMonoidHom
      (reflectW_mul hS.psymm) (reflectW_reflectW hS.psymm) (reflectTensorEquiv k ν' ν'' hS.psymm)
      (fun a => reflectW_inductionMap hS.psymm a)
  exact Res.finite_of_regular _ L

/-- The `k`-module structure of `Res_{ν';ν''} L` through `W_{ν'} ⊗ W_{ν''}`. -/
abbrev resModuleK (L : Type*) [AddCommGroup L] [Module (WeightedKLRAlgebra k Γ (ν' + ν'')) L] :
    Module k (res k Γ ν' ν'' L) :=
  Module.compHom _ (algebraMap k (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν''))

variable (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)

variable (ν' ν'') in
/-- `Res_{ν';ν''} L` as a finitely generated projective `W_{ν'} ⊗ W_{ν''}`-module (Webster,
arXiv:1209.2463v4, §2.4), under the standing hypothesis. -/
noncomputable def resProj (L : FGProj k (WeightedKLRAlgebra k Γ (ν' + ν''))) :
    FGProj k (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :=
  letI := resModuleK (k := k) (Γ := Γ) (ν' := ν') (ν'' := ν'') L.carrier
  haveI : IsScalarTower k (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (res k Γ ν' ν'' L.carrier) := IsScalarTower.of_compHom _ _ _
  haveI := res_projective Γ ν' ν'' hD hZ hS L.carrier
  haveI := res_finite Γ ν' ν'' hD hZ hS L.carrier
  FGProj.of (res k Γ ν' ν'' L.carrier)

/-- `Res L ≅ Res L'` for `L ≅ L'`. -/
noncomputable def resProjCongr {L L' : FGProj k (WeightedKLRAlgebra k Γ (ν' + ν''))}
    (e : L.Iso L') : (resProj ν' ν'' hD hZ hS L).Iso (resProj ν' ν'' hD hZ hS L') :=
  Res.congr (inductionRingHom k Γ ν' ν'') e

/-- `Res (L × L') ≅ Res L × Res L'`. -/
noncomputable def resProjProd (L L' : FGProj k (WeightedKLRAlgebra k Γ (ν' + ν''))) :
    (resProj ν' ν'' hD hZ hS (L.prod L')).Iso
      ((resProj ν' ν'' hD hZ hS L).prod (resProj ν' ν'' hD hZ hS L')) :=
  Res.prodEquiv (inductionRingHom k Γ ν' ν'') L.carrier L'.carrier

variable (ν' ν'') in
/-- **The coproduct component of Webster's Theorem 2.19 on Grothendieck groups**
(arXiv:1209.2463v4, §2.4): `Δ_{ν';ν''} : K₀(W_{ν'+ν''}) → K₀(W_{ν'} ⊗ W_{ν''})`,
`[L] ↦ [Res_{ν';ν''} L]`, additive, over any commutative ring `k`, under Webster's standing
hypothesis. -/
noncomputable def resK0 : ProjK0 k (WeightedKLRAlgebra k Γ (ν' + ν'')) →+
    ProjK0 k (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :=
  ProjK0.lift (fun L => ProjK0.of (resProj ν' ν'' hD hZ hS L))
    (fun _ _ e => ProjK0.of_eq_of_iso (resProjCongr hD hZ hS e))
    (fun L L' => by rw [ProjK0.of_eq_of_iso (resProjProd hD hZ hS L L'), ProjK0.of_prod])

@[simp] theorem resK0_of (L : FGProj k (WeightedKLRAlgebra k Γ (ν' + ν''))) :
    resK0 ν' ν'' hD hZ hS (ProjK0.of L) = ProjK0.of (resProj ν' ν'' hD hZ hS L) :=
  ProjK0.lift_of _ _ _ L

end Restriction

end Juxtapose

end WeightedKLR

end

end Categorification
