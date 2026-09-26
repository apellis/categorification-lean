/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Prop33
import Categorification.KLR.MackeyRes
import Categorification.KLR.GradedFree

/-!
# Graded Proposition 2.19 and Proposition 3.3 (4) on the modules `P_s`

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, Proposition 2.19 (first formula) and §3.1,
Proposition 3.3 (4). For `s ∈ Seq(ν + ν')`,

`Res_{ν,ν'} P_s ≅ ⊕_u (P_{i_u} ⊠ P_{j_u}){deg(ψ_{σ(u)} 1_s)}`

as graded `R(ν) ⊗ R(ν')`-modules, the sum over the ways `u` of writing `s` as a shuffle of
`i_u ∈ Seq ν` and `j_u ∈ Seq ν'` (minimal coset representatives with `u • s = i_u j_u`), with
`σ(u)` a reduced word of `u`. The ungraded isomorphism, `(t_u)_u ↦ ∑_u ι(t_u) ψ_{σ(u)} 1_s`, is
`KLRAlgebra.resProjEquiv` (`Categorification.KLR.MackeyRes`); here we check that it is
degree-preserving for these shifts (`ψ_{σ(u)} 1_s` is homogeneous of degree
`deg(ψ_{σ(u)} 1_s) = G.degW (σ u) s`, `GradingDatum.ψw_mul_e_mem_grade`).

We record the consequence for the forms `gdim HOM`: for every `Y ∈ (R(ν) ⊗ R(ν'))-pmod`,

`gdim HOM(Y, Res P_s) = ∑_u q^{deg(ψ_{σ(u)} 1_s)} gdim HOM(Y, P_{i_u} ⊠ P_{j_u})`

(`GradingDatum.homGdim_resGProj_projP`, `GradingDatum.homForm_resK0_projP`), and hence
**Proposition 3.3 (4) evaluated on `P_s`** (`GradingDatum.homForm_indK0_projP_eq_sum`):

`(x x', [P_s]) = ∑_u q^{deg(ψ_{σ(u)} 1_s)} (x, [P_{i_u}]) (x', [P_{j_u}])`

for `x`, `x'` in the `ℤ[q, q⁻¹]`-spans of the classes of modules `R(ν) e` (degree-zero
idempotents `e`), e.g. `x = [P_i]`, `x' = [P_j]`. We use the canonical reduced words
`σ(u) = canWord u`. The direct sum is modelled as the finite product `Π_u` with the product
grading `Graded.piGrading`.

## Generic results

* `Graded.piGrading` : the grading of a finite product, a `Decomposition`
  (`Graded.isInternal_piGrading`), graded for a graded action.
* `Graded.homGradePiRight` : `HOM(N, Π_u M_u)_d ≅ Π_u HOM(N, M_u)_d`.
* `Graded.gdim_eq_sum_of_finrank_eq`, `Graded.GProj.homGdim_eq_sum_of_iso_pi` :
  `gdim HOM(Y, X) = ∑_u gdim HOM(Y, M_u)` if `X ≅ Π_u M_u`.
* `Graded.extIdemEquivLeftIdeal` : `A e ⊠ B e' ≅ (A ⊗ B)(e ⊗ e')`.
-/

noncomputable section

universe u v

namespace Categorification

open scoped TensorProduct
open DirectSum Module

namespace Graded

/-! ### Finite products of graded modules -/

section Pi

variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [CommRing k] {M : ι → Type*}
  [∀ t, AddCommGroup (M t)] [∀ t, Module k (M t)]

/-- The grading `(Π_t M_t)_d = Π_t (M_t)_d` of a finite product. -/
def piGrading (ℳ : ∀ t, ℤ → Submodule k (M t)) (d : ℤ) : Submodule k (∀ t, M t) where
  carrier := {f | ∀ t, f t ∈ ℳ t d}
  add_mem' hf hg t := add_mem (hf t) (hg t)
  zero_mem' _ := zero_mem _
  smul_mem' c _ hf t := Submodule.smul_mem _ c (hf t)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem mem_piGrading {ℳ : ∀ t, ℤ → Submodule k (M t)} {d : ℤ} {f : ∀ t, M t} :
    f ∈ piGrading ℳ d ↔ ∀ t, f t ∈ ℳ t d := Iff.rfl

theorem isInternal_piGrading (ℳ : ∀ t, ℤ → Submodule k (M t)) [∀ t, Decomposition (ℳ t)] :
    IsInternal (piGrading ℳ) := by
  refine isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · intro d
    rw [disjoint_iff, eq_bot_iff]
    rintro f ⟨hf1, hf2⟩
    rw [Submodule.mem_bot]
    funext t
    have hind := (Decomposition.isInternal (ℳ t)).submodule_iSupIndep d
    have hle : (⨆ (j) (_ : j ≠ d), piGrading ℳ j) ≤
        (⨆ (j) (_ : j ≠ d), ℳ t j).comap (LinearMap.proj t) :=
      iSup₂_le fun j hj g hg => le_iSup₂ (f := fun j (_ : j ≠ d) => ℳ t j) j hj (hg t)
    have h2 : f t ∈ ℳ t d ⊓ ⨆ (j) (_ : j ≠ d), ℳ t j := ⟨hf1 t, hle hf2⟩
    rw [disjoint_iff.1 hind] at h2
    exact (Submodule.mem_bot k).1 h2
  · rw [eq_top_iff]
    intro f _
    rw [← Finset.univ_sum_single f]
    refine Submodule.sum_mem _ fun t _ => ?_
    have ht : f t ∈ ⨆ d, ℳ t d :=
      (Decomposition.isInternal (ℳ t)).submodule_iSup_eq_top ▸ Submodule.mem_top
    have h1 : Pi.single t (f t) ∈ (⨆ d, ℳ t d).map (LinearMap.single k M t) :=
      ⟨f t, ht, rfl⟩
    rw [Submodule.map_iSup] at h1
    refine (show (⨆ d, (ℳ t d).map (LinearMap.single k M t)) ≤ ⨆ d, piGrading ℳ d from
      iSup_mono fun d => ?_) h1
    rintro _ ⟨x, hx, rfl⟩ t'
    by_cases h : t' = t
    · subst h; simpa using hx
    · simp [Pi.single_apply, h]

noncomputable instance (ℳ : ∀ t, ℤ → Submodule k (M t)) [∀ t, Decomposition (ℳ t)] :
    Decomposition (piGrading ℳ) :=
  (isInternal_piGrading ℳ).chooseDecomposition

instance {A : Type*} [Ring A] [Algebra k A] [∀ t, Module A (M t)] {𝒜 : ℤ → Submodule k A}
    (ℳ : ∀ t, ℤ → Submodule k (M t)) [∀ t, SetLike.GradedSMul 𝒜 (ℳ t)] :
    SetLike.GradedSMul 𝒜 (piGrading ℳ) where
  smul_mem _ _ _ _ ha hf t := SetLike.GradedSMul.smul_mem ha (hf t)

end Pi

section PiHom

variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [Field k] {A : Type*} [Ring A] [Algebra k A]
  {M : ι → Type*} [∀ t, AddCommGroup (M t)] [∀ t, Module k (M t)] [∀ t, Module A (M t)]
  [∀ t, IsScalarTower k A (M t)] {N : Type*} [AddCommGroup N] [Module A N] [Module k N]

/-- `HOM(N, Π_t M_t)_d ≅ Π_t HOM(N, M_t)_d`. -/
def homGradePiRight (𝒩 : ℤ → Submodule k N) (ℳ : ∀ t, ℤ → Submodule k (M t)) (d : ℤ) :
    homGrade A 𝒩 (piGrading ℳ) d ≃ₗ[k] ((t : ι) → homGrade A 𝒩 (ℳ t) d) where
  toFun φ t := ⟨(LinearMap.proj t).comp φ.1, fun _ _ hx => φ.2 hx t⟩
  invFun ψ := ⟨LinearMap.pi fun t => (ψ t).1, fun _ _ hx t => (ψ t).2 hx⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end PiHom

/-- `gdim` of a family whose dimensions are the sums of those of finitely many families. -/
theorem gdim_eq_sum_of_finrank_eq {ι k V : Type*} [Fintype ι] [Field k] [AddCommGroup V]
    [Module k V] {W : ι → Type*} [∀ t, AddCommGroup (W t)] [∀ t, Module k (W t)]
    {𝒩 : ℤ → Submodule k V} {𝒲 : ∀ t, ℤ → Submodule k (W t)} [HasGdim 𝒩] [∀ t, HasGdim (𝒲 t)]
    (h : ∀ d, finrank k (𝒩 d) = ∑ t, finrank k (𝒲 t d)) :
    gdim 𝒩 = ∑ t, gdim (𝒲 t) := by
  ext d
  rw [HahnSeries.coeff_sum, coeff_gdim, h d]
  push_cast
  exact Finset.sum_congr rfl fun t _ => (coeff_gdim (𝒲 t) d).symm

namespace GProj

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] [HasGdim 𝒜]

/-- If `X ≅ Π_t M_t` (graded), then `gdim HOM(Y, X) = ∑_t gdim HOM(Y, M_t)`. -/
theorem homGdim_eq_sum_of_iso_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (Y X : GProj 𝒜)
    (Ms : ι → GProj 𝒜) (e : X.grading ≃ᵍ[A] piGrading fun t => (Ms t).grading) :
    homGdim Y X = ∑ t, homGdim Y (Ms t) :=
  gdim_eq_sum_of_finrank_eq fun d => by
    rw [finrank_homGrade_congr_right e d, (homGradePiRight Y.grading _ d).finrank_eq,
      Module.finrank_pi_fintype]

end GProj

/-! ### `A e ⊠ B e' ≅ (A ⊗ B)(e ⊗ e')` -/

section ExtIdem

variable {k : Type v} [Field k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]

theorem extIdemIncl_mul {e : A} {e' : B} (n : ExtTensor k (leftIdeal e) (leftIdeal e')) :
    extIdemIncl e e' n * (e ⊗ₜ[k] e') = extIdemIncl e e' n := by
  induction n using ExtTensor.induction_on with
  | zero => rw [map_zero, zero_mul]
  | tmul x y =>
    rw [extIdemIncl_tmul, Algebra.TensorProduct.tmul_mul_tmul, mem_leftIdeal.1 x.2,
      mem_leftIdeal.1 y.2]
  | add n n' hn hn' => rw [map_add, add_mul, hn, hn']

theorem extIdemIncl_injective (e : A) (e' : B) :
    Function.Injective (extIdemIncl (k := k) e e') := by
  intro x y h
  have h' := (ExtTensor.selfEquiv k A B).injective h
  exact TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Subtype.val_injective h'

/-- `A e ⊠ B e' ≅ (A ⊗ B)(e ⊗ e')` as left `A ⊗ B`-modules. -/
def extIdemEquivLeftIdeal {e : A} {e' : B} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') :
    ExtTensor k (leftIdeal e) (leftIdeal e') ≃ₗ[A ⊗[k] B] leftIdeal (e ⊗ₜ[k] e') :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict _ (extIdemIncl e e') fun n => extIdemIncl_mul n)
    ⟨fun x y h => extIdemIncl_injective e e' (congrArg Subtype.val h), fun r => by
      refine ⟨(r : A ⊗[k] B) • extIdemUnit k he he', Subtype.ext ?_⟩
      rw [LinearMap.codRestrict_apply, map_smul, extIdemUnit, extIdemIncl_tmul, smul_eq_mul]
      exact mem_leftIdeal.1 r.2⟩

@[simp] theorem coe_extIdemEquivLeftIdeal {e : A} {e' : B} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (n : ExtTensor k (leftIdeal e) (leftIdeal e')) :
    ((extIdemEquivLeftIdeal he he' n : leftIdeal (e ⊗ₜ[k] e')) : A ⊗[k] B) =
      extIdemIncl e e' n := rfl

end ExtIdem

end Graded

namespace KLR

open Graded KLRAlgebra TypeA Equiv MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν ν' : Multiset I}

namespace KLRAlgebra

theorem projPP_eq_leftIdeal (i : Seq ν) (j : Seq ν') :
    projPP Q i j = leftIdeal ((e i : KLRAlgebra k Q ν) ⊗ₜ[k] (e j : KLRAlgebra k Q ν')) := by
  ext t
  rw [mem_projPP, mem_leftIdeal]

theorem projP_eq_leftIdeal {μ : Multiset I} (s : Seq μ) :
    projP Q s = leftIdeal (e s : KLRAlgebra k Q μ) := by
  ext r
  rw [mem_projP, mem_leftIdeal]

/-- `Res (P_s)` for the two models `span {1_s}` and `R 1_s` of `P_s`. -/
def resProjPEquiv (s : Seq (ν + ν')) :
    Res Q ν ν' (projP Q s) ≃ₗ[TensorKLR Q ν ν']
      ResIdem Q ν ν' (leftIdeal (e s : KLRAlgebra k Q (ν + ν'))) where
  toFun n := ⟨⟨((n : projP Q s) : KLRAlgebra k Q (ν + ν')),
      mem_leftIdeal.2 (mem_projP.1 (n : projP Q s).2)⟩, by
    have h := n.2
    rw [mem_resSubgroup] at h
    exact Subtype.ext (show (oneConcat Q ν ν' : KLRAlgebra k Q (ν + ν')) *
      ((n : projP Q s) : KLRAlgebra k Q (ν + ν')) = _ from congrArg Subtype.val h)⟩
  invFun n := ⟨⟨((n : leftIdeal (e s : KLRAlgebra k Q (ν + ν'))) : KLRAlgebra k Q (ν + ν')),
      mem_projP.2 (mem_leftIdeal.1 (n : leftIdeal (e s : KLRAlgebra k Q (ν + ν'))).2)⟩, by
    have h := n.2
    rw [mem_idemSubspace] at h
    exact Subtype.ext (show (oneConcat Q ν ν' : KLRAlgebra k Q (ν + ν')) *
      ((n : leftIdeal (e s : KLRAlgebra k Q (ν + ν'))) : KLRAlgebra k Q (ν + ν')) = _ from
        congrArg Subtype.val h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

/-- The canonical reduced word of a shuffle. -/
abbrev shuffleWord (u : Shuffle (Seq.card_add' ν ν')) : List ℕ := canWord _ u.1

omit [DecidableEq I] in
theorem shuffleWord_spec (u : Shuffle (Seq.card_add' ν ν')) :
    IsReduced (Multiset.card (ν + ν')) (shuffleWord u) ∧
      wordProd (Multiset.card (ν + ν')) (shuffleWord u) = u.1 :=
  ⟨isReduced_canWord _ u.1, wordProd_canWord _ u.1⟩

/-- `P_i ⊠ P_j ≅ P_i ⊗ P_j`, the latter the left ideal `(R(ν) ⊗ R(ν'))(1_i ⊗ 1_j)`. -/
def extProjPPEquiv (i : Seq ν) (j : Seq ν') :
    ExtTensor k (leftIdeal (e i : KLRAlgebra k Q ν)) (leftIdeal (e j : KLRAlgebra k Q ν'))
      ≃ₗ[TensorKLR Q ν ν'] projPP Q i j :=
  (extIdemEquivLeftIdeal (e_mul_self i) (e_mul_self j)).trans
    (LinearEquiv.ofEq _ _ (projPP_eq_leftIdeal i j).symm)

theorem coe_extProjPPEquiv (i : Seq ν) (j : Seq ν')
    (n : ExtTensor k (leftIdeal (e i : KLRAlgebra k Q ν)) (leftIdeal (e j : KLRAlgebra k Q ν'))) :
    ((extProjPPEquiv i j n : projPP Q i j) : TensorKLR Q ν ν') =
      extIdemIncl (e i : KLRAlgebra k Q ν) (e j : KLRAlgebra k Q ν') n := rfl

variable (ν ν') in
/-- The domain `⊕_u P_{i_u} ⊠ P_{j_u}` of Proposition 2.19. -/
abbrev ResProjDom (s : Seq (ν + ν')) : Type _ :=
  (u : ShuffleOf ν ν' s) →
    ExtTensor k (leftIdeal (e u.split.1 : KLRAlgebra k Q ν))
      (leftIdeal (e u.split.2 : KLRAlgebra k Q ν'))

/-- **KL I, Proposition 2.19** (ungraded), in terms of external tensor products:
`⊕_u P_{i_u} ⊠ P_{j_u} ≅ Res_{ν,ν'} P_s`, `(t_u)_u ↦ ∑_u ι(t_u) ψ_{σ(u)} 1_s`. -/
def resProjExtEquiv (s : Seq (ν + ν')) :
    ResProjDom (Q := Q) ν ν' s ≃ₗ[TensorKLR Q ν ν']
      ResIdem Q ν ν' (leftIdeal (e s : KLRAlgebra k Q (ν + ν'))) :=
  let e₁ : ResProjDom (Q := Q) ν ν' s ≃ₗ[TensorKLR Q ν ν']
      ((u : ShuffleOf ν ν' s) → projPP Q u.split.1 u.split.2) :=
    LinearEquiv.piCongrRight fun u => extProjPPEquiv u.split.1 u.split.2
  let e₂ : ((u : ShuffleOf ν ν' s) → projPP Q u.split.1 u.split.2) ≃ₗ[TensorKLR Q ν ν']
      Res Q ν ν' (projP Q s) :=
    resProjEquiv shuffleWord shuffleWord_spec hPQ hP (canWord _) (canWord _)
      (fun a => ⟨isReduced_canWord _ a, wordProd_canWord _ a⟩)
      (fun b => ⟨isReduced_canWord _ b, wordProd_canWord _ b⟩) s
  e₁.trans (e₂.trans (resProjPEquiv s))

theorem coe_resProjExtEquiv (s : Seq (ν + ν')) (t : ResProjDom (Q := Q) ν ν' s) :
    (((resProjExtEquiv hPQ hP s t :
      ResIdem Q ν ν' (leftIdeal (e s : KLRAlgebra k Q (ν + ν')))) :
        leftIdeal (e s : KLRAlgebra k Q (ν + ν'))) : KLRAlgebra k Q (ν + ν')) =
      ∑ u, concat Q ν ν' (extIdemIncl (e u.split.1 : KLRAlgebra k Q ν)
        (e u.split.2 : KLRAlgebra k Q ν') (t u)) * (ψw (shuffleWord u.1) * e s) := rfl

end KLRAlgebra

namespace GradingDatum

variable (G : GradingDatum Q) {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

variable (ν ν') in
/-- The summand `(P_{i_u} ⊠ P_{j_u}){deg(ψ_{σ(u)} 1_s)}` of `Res P_s`. -/
def resSummand (s : Seq (ν + ν')) (u : ShuffleOf ν ν' s) :
    GProj (tensorGrading (G.grade ν) (G.grade ν')) :=
  ((G.projP u.split.1).extTensor (G.projP u.split.2)).shift (G.degW (shuffleWord u.1) s)

/-- The isomorphism of Proposition 2.19 is degree-preserving, with the summand indexed by `u`
shifted by `deg(ψ_{σ(u)} 1_s)`. -/
theorem resProjExtEquiv_mem (s : Seq (ν + ν')) {d : ℤ} {t : ResProjDom (Q := Q) ν ν' s}
    (ht : ∀ u, t u ∈ ExtTensor.grading
      (Graded.submodule (G.grade ν) (leftIdeal (e u.split.1 : KLRAlgebra k Q ν)))
      (Graded.submodule (G.grade ν') (leftIdeal (e u.split.2 : KLRAlgebra k Q ν')))
      (d - G.degW (shuffleWord u.1) s)) :
    (((resProjExtEquiv hPQ hP s t :
      ResIdem Q ν ν' (leftIdeal (e s : KLRAlgebra k Q (ν + ν')))) :
        leftIdeal (e s : KLRAlgebra k Q (ν + ν'))) : KLRAlgebra k Q (ν + ν')) ∈
      G.grade (ν + ν') d := by
  rw [coe_resProjExtEquiv]
  refine Submodule.sum_mem _ fun u _ => ?_
  have h2 := SetLike.GradedMul.mul_mem (A := G.grade (ν + ν'))
    (G.concat_mem_grade (extIdemIncl_mem (ht u))) (G.ψw_mul_e_mem_grade (shuffleWord u.1) s)
  rwa [sub_add_cancel] at h2

/-- **KL I, Proposition 2.19, graded**:
`Res_{ν,ν'} P_s ≅ ⊕_u (P_{i_u} ⊠ P_{j_u}){deg(ψ_{σ(u)} 1_s)}` as graded
`R(ν) ⊗ R(ν')`-modules. -/
def resProjGradedEquiv (s : Seq (ν + ν')) :
    GradedEquiv (TensorKLR Q ν ν') (M := ∀ u, (G.resSummand ν ν' s u).carrier)
      (N := (G.resGProj ν ν' hPQ hP (G.projP s)).carrier)
      (piGrading fun u => (G.resSummand ν ν' s u).grading)
      (G.resGProj ν ν' hPQ hP (G.projP s)).grading :=
  GradedEquiv.ofPreserves (resProjExtEquiv hPQ hP s) (by
    intro d t ht
    exact G.resProjExtEquiv_mem hPQ hP s ht)

variable [HasGdim (G.grade ν)] [HasGdim (G.grade ν')]

/-- `gdim HOM(Y, Res P_s) = ∑_u q^{deg(ψ_{σ(u)} 1_s)} gdim HOM(Y, P_{i_u} ⊠ P_{j_u})` for every
`Y ∈ (R(ν) ⊗ R(ν'))-pmod`. -/
theorem homGdim_resGProj_projP (Y : GProj (tensorGrading (G.grade ν) (G.grade ν')))
    (s : Seq (ν + ν')) :
    GProj.homGdim Y (G.resGProj ν ν' hPQ hP (G.projP s)) =
      ∑ u : ShuffleOf ν ν' s, HahnSeries.single (G.degW (shuffleWord u.1) s) 1 *
        GProj.homGdim Y ((G.projP u.split.1).extTensor (G.projP u.split.2)) := by
  rw [GProj.homGdim_eq_sum_of_iso_pi Y _ (G.resSummand ν ν' s)
    (G.resProjGradedEquiv hPQ hP s).symm]
  exact Finset.sum_congr rfl fun u _ => GProj.homGdim_shift_right _ _ _

/-- **`[Res] [P_s] = ∑_u q^{deg(ψ_{σ(u)} 1_s)} [P_{i_u}] ⊗ [P_{j_u}]`, tested against the
form**: `(z, [Res] [P_s]) = ∑_u q^{deg(ψ_{σ(u)} 1_s)} (z, [P_{i_u}] ⊗ [P_{j_u}])` for all
`z ∈ K₀(R(ν) ⊗ R(ν'))`. -/
theorem homForm_resK0_projP (z : K0 (tensorGrading (G.grade ν) (G.grade ν')))
    (s : Seq (ν + ν')) :
    K0.homForm (tensorGrading (G.grade ν) (G.grade ν')) z
        (G.resK0 ν ν' hPQ hP (K0.of (G.projP s))) =
      ∑ u : ShuffleOf ν ν' s, HahnSeries.single (G.degW (shuffleWord u.1) s) 1 *
        K0.homForm (tensorGrading (G.grade ν) (G.grade ν')) z
          (K0.extTensor (G.grade ν) (G.grade ν') (K0.of (G.projP u.split.1))
            (K0.of (G.projP u.split.2))) := by
  induction z using K0.induction_on with
  | of Y =>
    simp only [resK0_of, K0.extTensor_of, K0.homForm_of]
    exact G.homGdim_resGProj_projP hPQ hP Y s
  | zero => simp
  | add z z' hz hz' =>
    simp only [map_add, AddMonoidHom.add_apply, hz, hz', mul_add, Finset.sum_add_distrib]
  | neg z hz =>
    simp only [map_neg, AddMonoidHom.neg_apply, hz, mul_neg, Finset.sum_neg_distrib]

include hPQ hP in
/-- **KL I, Proposition 3.3 (4) on `P_s`**: for `x`, `x'` in the `ℤ[q, q⁻¹]`-spans of the
classes of modules `R(ν) e`, `R(ν') e'` (degree-zero idempotents; e.g. `x = [P_i]`,
`x' = [P_j]`) and `s ∈ Seq(ν + ν')`,
`(x x', [P_s]) = ∑_u q^{deg(ψ_{σ(u)} 1_s)} (x, [P_{i_u}]) (x', [P_{j_u}])`,
the sum over the ways `u` of writing `s` as a shuffle of `i_u ∈ Seq ν` and `j_u ∈ Seq ν'`. -/
theorem homForm_indK0_projP_eq_sum [HasGdim (G.grade (ν + ν'))] {x : K0 (G.grade ν)}
    {x' : K0 (G.grade ν')}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν)))
    (hx' : x' ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν')))
    (s : Seq (ν + ν')) :
    K0.homForm (G.grade (ν + ν')) (G.indK0 ν ν' x x') (K0.of (G.projP s)) =
      ∑ u : ShuffleOf ν ν' s, HahnSeries.single (G.degW (shuffleWord u.1) s) 1 *
        (K0.homForm (G.grade ν) x (K0.of (G.projP u.split.1)) *
          K0.homForm (G.grade ν') x' (K0.of (G.projP u.split.2))) := by
  rw [G.homForm_indK0 hPQ hP, G.homForm_resK0_projP hPQ hP]
  exact Finset.sum_congr rfl fun u _ => by rw [K0.homForm_extTensor_of_mem_span hx hx']

end GradingDatum

end KLR

end Categorification

end
