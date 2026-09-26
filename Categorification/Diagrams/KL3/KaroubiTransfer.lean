/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Karoubi
import Categorification.Diagrams.KLR.MatEnd
import Categorification.Algebra.IdempotentEquiv

/-!
# Idempotents of a graded algebra acting on 1-morphisms, as objects of `U̇`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.5 and
§3.8.4: "any degree `0` idempotent `e` of `R(ν)` gives rise to the idempotent `ϕ_{ν,λ}(e)` of
`E_ν 1_λ` and to the 1-morphism `(E_ν 1_λ, ϕ_{ν,λ}(e))` of `U̇`", and, in §3.8.4, the same for
the idempotents of `R(ν) ⊗ R(ν') ⊗ Π_λ` acting on `E_{ν,-ν'} 1_λ` through `α` (3.101).

`Categorification.Diagrams.KL3.KaroubiKLR` treats `R(ν)` acting on upward strands. Here the
construction is generic: `A` is a `ℤ`-graded `k`-algebra, `x : ι → (l ⟶ m)` a finite family of
1-morphisms of a graded presented 2-category, and `α : A →ₐ[k] MatEnd (P.obj ∘ x)` an algebra
homomorphism to the endomorphism algebra of `⨁_i x_i` (as a matrix algebra) which preserves
degrees and sends given elements `eι i ∈ A` to the diagonal matrix units (`TransferData`).

## Main results

* `TCorner D i`: idempotents `f ∈ eι i · A` of degree `0`; `tobj D F t`: the 1-morphism
  `(x_i {t}, α(f))` of `U̇(l, m)`; `thom`: the morphisms given by homogeneous elements of
  `f' A f`, with `thom_comp`, `thom_self`, `thom_congr`, `thom_eq_zero`, `sum_thom`;
* `tIso`: **equivalent idempotents give isomorphic 1-morphisms**;
* `tOrthIso`: **orthogonal decompositions give direct sum decompositions**;
* `tobj_shift`: `[(x_i {t}, α(f))] = q^t [(x_i {0}, α(f))]`.
-/

noncomputable section

namespace Categorification.GradedBicat

open CategoryTheory CategoryTheory.Limits StringDiagrams Presentation KLR.Diagram

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {k : Type w} [CommRing k] {P : Presentation.{w, v} S k}
  {deg : S.Gen → ℤ} {l m : P.Bicat}

variable {A : Type*} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Transfer data**: an algebra homomorphism `α : A → END(⨁_i x_i)` (matrices of
2-morphisms `x_i ⟶ x_j`) sending `eι i` to the `i`-th diagonal matrix unit and elements of
degree `d` to matrices of 2-morphisms of degree `d`. -/
structure TransferData (x : ι → Bicat.Hom l m) (eι : ι → A) where
  /-- The algebra homomorphism. -/
  α : A →ₐ[k] MatEnd (fun i => P.obj (x i).obj)
  α_e : ∀ i, α (eι i) = MatEnd.single i i (𝟙 _)
  α_mem : ∀ {d : ℤ} {r : A}, r ∈ 𝒜 d → ∀ i j, α r i j ∈ P.homDeg deg (x i).obj (x j).obj d

variable {𝒜} {x : ι → Bicat.Hom l m} {eι : ι → A} (D : TransferData (deg := deg) 𝒜 x eι)

namespace TransferData

theorem α_eq_zero {z : A} {j : ι} (hz : eι j * z = z) (i l : ι) (hl : l ≠ j) :
    D.α z i l = 0 := by
  rw [← hz, map_mul, D.α_e, MatEnd.mul_apply]
  refine Finset.sum_eq_zero fun l' _ => ?_
  rw [MatEnd.single_apply_of_ne _ (fun h => hl h.2), Limits.comp_zero]

theorem α_mul {y z : A} {j : ι} (hz : eι j * z = z) (i l : ι) :
    D.α (y * z) i l = D.α z i j ≫ D.α y j l := by
  rw [map_mul, MatEnd.mul_apply, Finset.sum_eq_single j]
  · intro j' _ hj
    rw [D.α_eq_zero hz i j' hj, Limits.zero_comp]
  · intro h; exact absurd (Finset.mem_univ _) h

end TransferData

variable (𝒜) in
/-- An idempotent `f ∈ eι i · A` of degree `0`. -/
structure TCorner (eι : ι → A) (i : ι) where
  /-- The idempotent. -/
  f : A
  deg0 : f ∈ 𝒜 0
  idem : f * f = f
  left : eι i * f = f

variable {D}

theorem TCorner.α_idem {i : ι} (F : TCorner 𝒜 eι i) :
    D.α F.f i i ≫ D.α F.f i i = D.α F.f i i := by
  rw [← D.α_mul F.left, F.idem]

variable (D) in
/-- **The 1-morphism `(x_i {t}, α(f))` of `U̇(l, m)`.** -/
abbrev tobj {i : ι} (F : TCorner 𝒜 eι i) (t : ℤ) : UDotHom P deg l m :=
  idemObj (x i) t (D.α F.f i i) (D.α_mem F.deg0 i i) F.α_idem

section Hom

omit [Fintype ι] [DecidableEq ι] in
theorem tcorner_left {i i' : ι} {F : TCorner 𝒜 eι i} {F' : TCorner 𝒜 eι i'} {y : A}
    (hyc : F'.f * y * F.f = y) : eι i' * y = y := by
  rw [← hyc, ← mul_assoc, ← mul_assoc, F'.left]

omit [Fintype ι] [DecidableEq ι] in
theorem tcorner_mul_left {i i' : ι} {F : TCorner 𝒜 eι i} {F' : TCorner 𝒜 eι i'} {y : A}
    (hyc : F'.f * y * F.f = y) : F'.f * y = y := by
  conv_lhs => rw [← hyc]
  rw [← mul_assoc, ← mul_assoc, F'.idem, hyc]

omit [Fintype ι] [DecidableEq ι] in
theorem tcorner_mul_right {i i' : ι} {F : TCorner 𝒜 eι i} {F' : TCorner 𝒜 eι i'} {y : A}
    (hyc : F'.f * y * F.f = y) : y * F.f = y := by
  conv_lhs => rw [← hyc]
  rw [mul_assoc, F.idem, hyc]

theorem α_tcorner {i i' : ι} {F : TCorner 𝒜 eι i} {F' : TCorner 𝒜 eι i'} {y : A}
    (hyc : F'.f * y * F.f = y) :
    D.α y i i' = D.α F.f i i ≫ D.α y i i' ≫ D.α F'.f i' i' := by
  conv_lhs => rw [← hyc]
  rw [D.α_mul F.left, D.α_mul (tcorner_left hyc)]

/-- The morphism `(x_i {t}, α(f)) ⟶ (x_{i'} {t'}, α(f'))` given by `y ∈ f' A f` of degree
`t - t'`. -/
def thom {i i' : ι} {F : TCorner 𝒜 eι i} {F' : TCorner 𝒜 eι i'} {t t' : ℤ} (y : A)
    (hy : y ∈ 𝒜 (t - t')) (hyc : F'.f * y * F.f = y) : tobj D F t ⟶ tobj D F' t' :=
  idemHom (D.α y i i') (D.α_mem hy i i') (α_tcorner hyc)

theorem thom_comp [SetLike.GradedMonoid 𝒜] {i i' i'' : ι} {F : TCorner 𝒜 eι i} {F' : TCorner 𝒜 eι i'}
    {F'' : TCorner 𝒜 eι i''} {t t' t'' : ℤ} (y z : A) (hy : y ∈ 𝒜 (t - t'))
    (hz : z ∈ 𝒜 (t' - t'')) (hyc : F'.f * y * F.f = y) (hzc : F''.f * z * F'.f = z) :
    (thom (D := D) (F := F) (F' := F') y hy hyc) ≫ (thom (F' := F'') z hz hzc) =
      thom (z * y) (by
          have := SetLike.mul_mem_graded hz hy
          rwa [show t' - t'' + (t - t') = t - t'' by ring] at this)
        (by rw [← mul_assoc, tcorner_mul_left hzc, mul_assoc, tcorner_mul_right hyc]) := by
  rw [thom, thom, idemHom_comp]
  apply idemHom_congr
  exact (D.α_mul (tcorner_left hyc) i i'').symm

theorem thom_self {i : ι} (F : TCorner 𝒜 eι i) (t : ℤ) (hy : F.f ∈ 𝒜 (t - t))
    (hyc : F.f * F.f * F.f = F.f) : thom (D := D) (F := F) (F' := F) F.f hy hyc = 𝟙 _ :=
  idemHom_eq_id rfl _ _

theorem thom_congr {i i' : ι} {F : TCorner 𝒜 eι i} {F' : TCorner 𝒜 eι i'} {t t' : ℤ}
    {y y' : A} (h : y = y') (hy : y ∈ 𝒜 (t - t')) (hy' : y' ∈ 𝒜 (t - t'))
    (hyc : F'.f * y * F.f = y) (hyc' : F'.f * y' * F.f = y') :
    thom (D := D) (F := F) (F' := F') y hy hyc = thom y' hy' hyc' := by
  subst h; rfl

theorem thom_eq_zero {i i' : ι} {F : TCorner 𝒜 eι i} {F' : TCorner 𝒜 eι i'} {t t' : ℤ} {y : A}
    (h : y = 0) (hy : y ∈ 𝒜 (t - t')) (hyc : F'.f * y * F.f = y) :
    thom (D := D) (F := F) (F' := F') y hy hyc = 0 := by
  subst h
  exact idemHom_eq_zero (by rw [map_zero]; rfl) _ _

theorem sum_thom {i i' : ι} {F : TCorner 𝒜 eι i} {F' : TCorner 𝒜 eι i'} {t t' : ℤ}
    {κ : Type*} (s : Finset κ) (y : κ → A) (hy : ∀ j, y j ∈ 𝒜 (t - t'))
    (hyc : ∀ j, F'.f * y j * F.f = y j) :
    ∑ j ∈ s, thom (D := D) (F := F) (F' := F') (y j) (hy j) (hyc j) =
      thom (∑ j ∈ s, y j) (Submodule.sum_mem _ fun j _ => hy j)
        (by rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => hyc j) := by
  simp only [thom]
  rw [sum_idemHom]
  apply idemHom_congr
  rw [map_sum, MatEnd.sum_apply]

/-- **Equivalent idempotents give isomorphic 1-morphisms of `U̇`**: if `a b = f`, `b a = f'`
(`IsEquivPair`), `a` of degree `d` and `b` of degree `-d`, then
`(x_i {t}, α(f)) ≅ (x_{i'} {t + d}, α(f'))`. -/
def tIso [SetLike.GradedMonoid 𝒜] {i i' : ι} (F : TCorner 𝒜 eι i) (F' : TCorner 𝒜 eι i') {a b : A}
    (h : IsEquivPair a b F.f F'.f) {d : ℤ} (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 (-d)) (t : ℤ) :
    tobj D F t ≅ tobj D F' (t + d) where
  hom := thom b (by rwa [show t - (t + d) = -d by ring]) (by rw [h.left_mul', h.mul_right'])
  inv := thom a (by rwa [show t + d - t = d by ring]) (by rw [h.left_mul, h.mul_right])
  hom_inv_id := by
    rw [thom_comp, thom_congr h.1 _ (by rw [sub_self]; exact F.deg0) _ (by rw [F.idem, F.idem])]
    exact thom_self F t _ _
  inv_hom_id := by
    rw [thom_comp, thom_congr h.2.1 _ (by rw [sub_self]; exact F'.deg0) _
      (by rw [F'.idem, F'.idem])]
    exact thom_self F' (t + d) _ _

theorem tgrade_sub_self {r : A} (h : r ∈ 𝒜 0) (t : ℤ) : r ∈ 𝒜 (t - t) := by
  rwa [sub_self]

/-- **Orthogonal decompositions**: if `f = ∑_j g_j` with `g_j` mutually orthogonal idempotents
of degree `0` in `eι i · A`, then `(x_i {t}, α(f)) ≅ ⨁_j (x_i {t}, α(g_j))`. -/
def tOrthIso [SetLike.GradedMonoid 𝒜] [HasFiniteBiproducts (UDotHom P deg l m)] {i : ι} (F : TCorner 𝒜 eι i) {κ : Type}
    [Fintype κ] [DecidableEq κ] (Gs : κ → TCorner 𝒜 eι i) (hsum : ∑ j, (Gs j).f = F.f)
    (horth : ∀ j j', j ≠ j' → (Gs j).f * (Gs j').f = 0) (t : ℤ) :
    tobj D F t ≅ ⨁ fun j => tobj D (Gs j) t :=
  have hl : ∀ j, (Gs j).f * F.f = (Gs j).f := fun j => by
    rw [← hsum, Finset.mul_sum, Finset.sum_eq_single j (fun j' _ h => horth j j' (Ne.symm h))
      (fun h => absurd (Finset.mem_univ j) h), (Gs j).idem]
  have hr : ∀ j, F.f * (Gs j).f = (Gs j).f := fun j => by
    rw [← hsum, Finset.sum_mul, Finset.sum_eq_single j (fun j' _ h => horth j' j h)
      (fun h => absurd (Finset.mem_univ j) h), (Gs j).idem]
  OrthDecomp.iso
    { a := fun j => thom (Gs j).f (tgrade_sub_self (Gs j).deg0 t) (by rw [(Gs j).idem, hl])
      b := fun j => thom (Gs j).f (tgrade_sub_self (Gs j).deg0 t) (by rw [hr, (Gs j).idem])
      total := by
        simp only [thom_comp]
        rw [Finset.sum_congr rfl fun j _ => thom_congr (Gs j).idem _
          (tgrade_sub_self (Gs j).deg0 t) _ (by rw [hr, hl])]
        rw [sum_thom, thom_congr hsum _ (tgrade_sub_self F.deg0 t) _ (by rw [F.idem, F.idem])]
        exact thom_self F t _ _
      b_a_self := fun j => by
        rw [thom_comp, thom_congr (Gs j).idem _ (tgrade_sub_self (Gs j).deg0 t) _
          (by rw [(Gs j).idem, (Gs j).idem])]
        exact thom_self (Gs j) t _ _
      b_a_ne := fun j j' h => by
        rw [thom_comp]
        exact thom_eq_zero (horth j' j (Ne.symm h)) _ _ }

end Hom

end Categorification.GradedBicat
