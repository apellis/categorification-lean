/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Sl2Categorification.DividedPowerSocle
import Categorification.Sl2Categorification.WeakCategorificationOp

/-!
# The top divided power of a simple object is simple

Chuang–Rouquier, arXiv:math/0407205v2, **Proposition 5.20 (a)**: for a simple object `S` of a
weak `𝔰𝔩₂`-categorification with nilHecke actions on `E` and `F`, and `n = h₊([S])`, the
divided power `E^{(n)} S` is simple.

The argument is that of Chuang–Rouquier. Let `r = h₋([S])` and let `L` be a simple quotient of
`F^r S`. Then `F L = 0`, and adjunction gives an embedding `S ⊆ E^r L`, so
`E^{(n)} S ⊆ E^n E^r L = E^{n+r} L ≅ (n+r)! · T` with `T = E^{(n+r)} L` simple
(`WeakSl2.simple_divObj_top_of_F_eq_zero`). Hence every composition factor of `E^{(n)} S` is `T`,
with multiplicity at most `dim Hom(E^{(n)} S, T)` (`WeakSl2.repr_cls_le_finrank_hom`). Finally
`n! · dim Hom(E^{(n)} S, T) = dim Hom(E^n S, T) = dim Hom(S, F^n T) = n! · dim Hom(S, F^{(n)} T)`,
and `dim Hom(S, F^{(n)} T) ≤ 1` by the `F`-version of Proposition 5.20 (b), socle part
(`WeakSl2.finiteDimensional_hom_divObj` for the categorification with `E` and `F` exchanged,
`WeakSl2.swap`), since `E T = 0`.

Chuang–Rouquier's category is artinian and noetherian (§5.1.1); both hypotheses are used, the
second to produce the simple quotient `L`.

## Main results

* `epowHomLinearEquiv`: an adjunction `E ⊣ F` gives `Hom(Eⁿ M, N) ≃ Hom(M, Fⁿ N)`.
* `WeakSl2.swap`: the weak categorification with `E` and `F` exchanged.
* `WeakSl2.simple_divObj_top`: **Chuang–Rouquier, Proposition 5.20 (a)**.
-/

namespace Categorification.Sl2

open CategoryTheory Limits Module Opposite

universe v u

variable {C : Type u} [Category.{v} C]

/-! ### Iterated adjunctions -/

section Adjunction

/-- `Eⁿ (E N) ≅ E (Eⁿ N)`. -/
def epowObjIso (E : C ⥤ C) : ∀ (n : ℕ) (N : C),
    (Epow E n).obj (E.obj N) ≅ E.obj ((Epow E n).obj N)
  | 0, _ => Iso.refl _
  | n + 1, N => E.mapIso (epowObjIso E n N)

variable [Preadditive C] (k : Type*) [CommRing k] [Linear k C] {E F : C ⥤ C}

/-- The hom-set bijection of an adjunction `E ⊣ F` with `F` additive and `k`-linear, as a
`k`-linear equivalence. -/
def adjHomLinearEquiv [F.Additive] [F.Linear k] (adj : E ⊣ F) (X Y : C) :
    (E.obj X ⟶ Y) ≃ₗ[k] (X ⟶ F.obj Y) :=
  { adj.homEquiv X Y with
    map_add' := fun a b => by simp [Adjunction.homEquiv_unit]
    map_smul' := fun c a => by simp [Adjunction.homEquiv_unit] }

/-- An adjunction `E ⊣ F` gives `Hom(Eⁿ M, N) ≃ Hom(M, Fⁿ N)`. -/
def epowHomLinearEquiv [F.Additive] [F.Linear k] (adj : E ⊣ F) :
    ∀ (n : ℕ) (M N : C), ((Epow E n).obj M ⟶ N) ≃ₗ[k] (M ⟶ (Epow F n).obj N)
  | 0, _, _ => LinearEquiv.refl k _
  | n + 1, M, N =>
    (adjHomLinearEquiv k adj ((Epow E n).obj M) N).trans
      ((epowHomLinearEquiv adj n M (F.obj N)).trans
        (Linear.homCongr k (Iso.refl M) (epowObjIso F n N)))

end Adjunction

/-! ### Hom spaces out of and into finite biproducts -/

section Biproduct

variable [Preadditive C] [HasFiniteBiproducts C] (k : Type*) [CommRing k] [Linear k C]

/-- `Hom(⨁_J Z, T) ≃ (J → Hom(Z, T))`. -/
noncomputable def biproductHomLinearEquiv {J : Type} [Fintype J] (Z T : C) :
    ((⨁ fun _ : J => Z) ⟶ T) ≃ₗ[k] (J → (Z ⟶ T)) where
  toFun φ j := biproduct.ι (fun _ : J => Z) j ≫ φ
  invFun g := biproduct.desc g
  left_inv φ := biproduct.hom_ext' _ _ fun j => by simp
  right_inv g := funext fun j => by simp
  map_add' a b := funext fun j => by simp
  map_smul' c a := funext fun j => by simp

/-- `Hom(T, ⨁_J Z) ≃ (J → Hom(T, Z))`. -/
noncomputable def homBiproductLinearEquiv {J : Type} [Fintype J] (Z T : C) :
    (T ⟶ ⨁ fun _ : J => Z) ≃ₗ[k] (J → (T ⟶ Z)) where
  toFun φ j := φ ≫ biproduct.π (fun _ : J => Z) j
  invFun g := biproduct.lift g
  left_inv φ := biproduct.hom_ext _ _ fun j => by simp
  right_inv g := funext fun j => by simp
  map_add' a b := funext fun j => by simp
  map_smul' c a := funext fun j => by simp

end Biproduct

/-! ### Composition factors detected by maps to a simple object -/

attribute [local instance] Abelian.hasFiniteBiproducts

namespace K0Data

variable [Abelian C] {ι V : Type*} [AddCommGroup V] [Module ℚ V] (K : K0Data C ι V)
variable (k : Type*) [Field k] [Linear k C]

/-- An object of class zero is zero. -/
lemma isZero_of_cls_eq_zero [∀ X : C, IsArtinianObject X] {X : C} (h : K.cls X = 0) :
    IsZero X := by
  by_contra hX
  obtain ⟨j, hj⟩ := K.exists_repr_pos_of_not_isZero hX
  rw [h, map_zero, Finsupp.zero_apply] at hj
  exact lt_irrefl _ hj

/-- If every nonzero map into `X` stays nonzero after some map `X ⟶ T` to a simple `T`, and
`Hom(X, T)` is finite-dimensional, then every composition factor of `X` is `T`, with
multiplicity at most `dim Hom(X, T)`. -/
theorem repr_cls_le_finrank_hom {X T : C} [hT : Simple T] [FiniteDimensional k (X ⟶ T)]
    (hX : ∀ {Y : C} (w : Y ⟶ X), w ≠ 0 → ∃ g : X ⟶ T, w ≫ g ≠ 0) :
    (∀ j, j ≠ K.idx T hT → K.B.repr (K.cls X) j = 0) ∧
      K.B.repr (K.cls X) (K.idx T hT) ≤ finrank k (X ⟶ T) := by
  classical
  set d := finrank k (X ⟶ T)
  let b := Module.finBasis k (X ⟶ T)
  let β : X ⟶ ⨁ fun _ : Fin d => T := biproduct.lift fun i => b i
  have hβ : Mono β := by
    refine Preadditive.mono_of_cancel_zero _ fun {Y} w hw => ?_
    by_contra hne
    obtain ⟨g, hg⟩ := hX w hne
    apply hg
    have hwb : ∀ i, w ≫ b i = 0 := fun i => by
      have : w ≫ β ≫ biproduct.π _ i = 0 := by rw [← Category.assoc, hw, zero_comp]
      simpa [β] using this
    rw [← b.sum_repr g, Preadditive.comp_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [Linear.comp_smul, hwb, smul_zero]
  have hadd := K.cls_add_of_mono β
  rw [K.cls_biproduct _ _ rfl, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    K.cls_simple T hT] at hadd
  have hcoord : ∀ j, (d : ℚ) * (if j = K.idx T hT then 1 else 0) =
      K.B.repr (K.cls X) j + K.B.repr (K.cls (cokernel β)) j := by
    intro j
    have := congrArg (fun v => K.B.repr v j) hadd
    simp only [map_nsmul, map_add, Finsupp.add_apply, Finsupp.smul_apply,
      Module.Basis.repr_self, Finsupp.single_apply, nsmul_eq_mul] at this
    rw [← this]
    by_cases hj : j = K.idx T hT
    · simp [hj]
    · simp [hj, Ne.symm hj]
  refine ⟨fun j hj => ?_, ?_⟩
  · have h1 := hcoord j
    simp only [hj, ↓reduceIte, mul_zero] at h1
    have := K.cls_mem_cone X j
    have := K.cls_mem_cone (cokernel β) j
    linarith
  · have h1 := hcoord (K.idx T hT)
    simp only [↓reduceIte, mul_one] at h1
    have := K.cls_mem_cone (cokernel β) (K.idx T hT)
    linarith

end K0Data

/-! ### Simple quotients -/

/-- A nonzero noetherian object of an abelian category has a simple quotient. -/
theorem exists_simple_epi [Abelian C] {X : C} [IsNoetherianObject X] (hX : ¬IsZero X) :
    ∃ (L : C) (_ : Simple L) (p : X ⟶ L), Epi p := by
  have : IsArtinianObject (op X) := isArtinianObject_op X
  have hX' : ¬IsZero (op X) := fun h => hX h.unop
  have hL : Simple (simpleSubobject hX') := inferInstance
  exact ⟨unop (simpleSubobject hX'), (simple_op_iff _).1 hL, (simpleSubobjectArrow hX').unop,
    inferInstance⟩

/-! ### The categorification with `E` and `F` exchanged -/

namespace WeakSl2

variable [Abelian C] {ι V : Type*} [AddCommGroup V] [Module ℚ V] (A : WeakSl2 C ι V)

/-- The weak `𝔰𝔩₂`-categorification with `E` and `F` exchanged and the weights negated
(Chuang–Rouquier, §5.1.1: the definition is symmetric in `E` and `F`). -/
@[reducible] def swap : WeakSl2 C ι V where
  toK0Data := A.toK0Data
  E := A.F
  F := A.E
  adjEF := A.adjFE
  adjFE := A.adjEF
  e := A.f
  f := A.e
  cls_E := A.cls_F
  cls_F := A.cls_E
  sl2 := A.sl2.swap
  wt i := -A.wt i
  wt_eq i := by rw [hOp_swap, LinearMap.neg_apply, A.wt_eq]; push_cast; rw [neg_smul]
  locFin w := by
    obtain ⟨U, h1, h2, h3, h4⟩ := A.locFin w
    exact ⟨U, h1, h2, h4, h3⟩


variable [∀ X : C, IsArtinianObject X] [∀ X : C, IsNoetherianObject X]
variable [A.E.Additive] [A.F.Additive] (DE : NilHeckeData A.E) (DF : NilHeckeData A.F)
variable (k : Type*) [Field k] [Linear k C] [A.E.Linear k] [A.F.Linear k]

/-- **Chuang–Rouquier, Proposition 5.20 (a)**: for a simple object `S` and `n = h₊([S])`, the
top divided power `E^{(n)} S` is simple.

The hypothesis `hXF` is the nilpotence of the dot on `F` (Chuang–Rouquier, §5.2.1, eigenvalue
`0`), and `hEnd` is the condition `End(S) = k` for simple `S` (Chuang–Rouquier, §5.1.1). -/
theorem simple_divObj_top
    (hXF : ∀ M, IsNilpotent (R := End (A.F.obj M)) (DF.X.app M))
    (hEnd : ∀ S : C, Simple S → finrank k (S ⟶ S) = 1)
    {S : C} (hS : Simple S) :
    Simple (DE.divObj k (hPlus A.e (A.cls S)) S) := by
  classical
  have : A.E.IsRightAdjoint := A.adjFE.isRightAdjoint
  set b := A.idx S hS
  have hclsS : A.cls S = A.B b := A.cls_simple S hS
  obtain ⟨hstr, hne, -, hfne, hfz⟩ := A.posBasis.strings b
  rw [hclsS]
  set n := hPlus A.e (A.B b)
  set r := hPlus A.f (A.B b)
  -- (1) a simple quotient `L` of `F^r S`
  have hY : ¬IsZero ((Epow A.F r).obj S) := by
    intro h
    apply hfne
    rw [← hclsS, ← A.toK0Data.cls_Epow_obj A.cls_F]
    exact A.toK0Data.cls_eq_zero_of_isZero h
  obtain ⟨L, hL, p, hp⟩ := exists_simple_epi hY
  -- (2) `F L = 0`
  have hfL : A.f (A.B (A.idx L hL)) = 0 := by
    have hpos := A.repr_cls_pos_of_mono_of_epi (hS := hL) p (𝟙 L)
    rw [A.toK0Data.cls_Epow_obj A.cls_F, hclsS] at hpos
    refine A.posBasis.pos_f.apply_basis_eq_zero ((A.posBasis.pos_f.pow r) b) ?_ hpos.ne'
    rw [← Module.End.mul_apply, ← pow_succ']
    exact hfz
  have hFL : IsZero (A.F.obj L) := by
    refine A.toK0Data.isZero_of_cls_eq_zero ?_
    rw [A.cls_F, A.cls_simple L hL, hfL]
  -- (3) the adjoint embedding `S ⟶ E^r L`
  set s := epowHomLinearEquiv k A.adjFE r S L p
  have hp0 : p ≠ 0 := fun h ↦ by
    have : IsZero L := by
      rw [IsZero.iff_id_eq_zero, ← cancel_epi p, h, zero_comp, zero_comp]
    exact Simple.not_isZero L this
  have hs0 : s ≠ 0 := fun h ↦ hp0 ((epowHomLinearEquiv k A.adjFE r S L).map_eq_zero_iff.1 h)
  have : Mono s := mono_of_nonzero_from_simple hs0
  -- (4) weights: `h₊([L]) = r + n`
  have hwt : A.wt b = -(hPlus A.e (A.cls L) : ℤ) + 2 * r := A.wt_of_mono_Epow hL hFL r hS s
  have hhL : hPlus A.e (A.cls L) = r + n := by omega
  set N := r + n
  have hT : Simple (DE.divObj k N L) := by
    have := A.simple_divObj_top_of_F_eq_zero DE k DF hL hFL
    rwa [hhL] at this
  set T := DE.divObj k N L
  -- (5) `E T = 0` and `n ≤ h₋([T])`
  set l := A.idx L hL
  have hclsL : A.cls L = A.B l := A.cls_simple L hL
  have hhl : hPlus A.e (A.B l) = N := by rw [← hclsL]; exact hhL
  have hNf : (0 : ℚ) < N.factorial := by exact_mod_cast N.factorial_pos
  have hclsT : (A.e ^ N) (A.B l) = (N.factorial : ℚ) • A.cls T := by
    have h1 := DE.cls_Epow k A.toK0Data N L
    rw [A.toK0Data.cls_Epow_obj A.cls_E, hclsL, ← Nat.cast_smul_eq_nsmul ℚ] at h1
    exact h1
  have hET : IsZero (A.E.obj T) := by
    refine A.toK0Data.isZero_of_cls_eq_zero ?_
    rw [A.cls_E]
    have h0 : (A.e ^ (N + 1)) (A.B l) = 0 := by
      have := (A.posBasis.strings l).2.2.1
      rwa [hhl] at this
    rw [pow_succ', Module.End.mul_apply, hclsT, map_smul] at h0
    exact (smul_eq_zero.1 h0).resolve_left hNf.ne'
  set c := A.idx T hT
  have hclsT' : A.cls T = A.B c := A.cls_simple T hT
  have hwc : A.wt c = N := by
    have hwl := A.posBasis.wt_of_f_eq_zero hfL
    rw [hhl] at hwl
    refine A.posBasis.wt_eq_of_repr_ne_zero (v := (A.e ^ N) (A.B l)) (ν := (N : ℤ)) ?_ ?_
    · rw [A.posBasis.hOp_pow_e_basis, hwl]; congr 1; push_cast; ring
    · rw [hclsT, hclsT', map_smul, Module.Basis.repr_self]; simp [hNf.ne']
  have hfT : n ≤ hPlus A.f (A.cls T) := by
    have := (A.posBasis.strings c).1
    rw [hclsT']
    omega
  -- (6) the `F`-version of (b): `dim Hom(S, F^{(n)} T) ≤ 1`
  obtain ⟨hfin, hle⟩ := A.swap.finiteDimensional_hom_divObj DF k DE hXF hEnd hT hET hfT S
  -- (7) `dim Hom(E^{(n)} S, T) ≤ 1`, from `E^n ≅ n! · E^{(n)}`, `F^n ≅ n! · F^{(n)}` and
  -- `Hom(E^n S, T) ≅ Hom(S, F^n T)`
  have hnf : 0 < n.factorial := n.factorial_pos
  obtain ⟨J, _, _, hJ, ⟨eF⟩⟩ := DF.exists_iso_biproduct_divObj k n T
  obtain ⟨J', _, _, hJ', ⟨eE⟩⟩ := DE.exists_iso_biproduct_divObj k n S
  set X := DE.divObj k n S
  let φF : (S ⟶ (Epow A.F n).obj T) ≃ₗ[k] (J → (S ⟶ DF.divObj k n T)) :=
    (Linear.homCongr k (Iso.refl S) eF.symm).trans (homBiproductLinearEquiv k _ S)
  let φE : ((Epow A.E n).obj S ⟶ T) ≃ₗ[k] (J' → (X ⟶ T)) :=
    (Linear.homCongr k eE.symm (Iso.refl T)).trans (biproductHomLinearEquiv k X T)
  let ψ := (φE.symm.trans (epowHomLinearEquiv k A.adjEF n S T)).trans φF
  have : FiniteDimensional k (J' → (X ⟶ T)) := LinearEquiv.finiteDimensional ψ.symm
  have hJ'ne : Nonempty J' := Fintype.card_pos_iff.1 (hJ' ▸ hnf)
  have : FiniteDimensional k (X ⟶ T) :=
    Module.Finite.of_surjective (LinearMap.proj (R := k) (φ := fun _ : J' => X ⟶ T) hJ'ne.some)
      fun x => ⟨fun _ => x, rfl⟩
  have hfinXT : finrank k (X ⟶ T) ≤ 1 := by
    have h := ψ.finrank_eq
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, Finset.card_univ, hJ, hJ', smul_eq_mul, smul_eq_mul] at h
    have := Nat.eq_of_mul_eq_mul_left hnf h
    omega
  -- (8) every nonzero map into `X` survives some map `X ⟶ T`
  have hdet : ∀ {Y : C} (w : Y ⟶ X), w ≠ 0 → ∃ g : X ⟶ T, w ≫ g ≠ 0 := by
    intro Y w hw
    let ιX : X ⟶ (Epow A.E (r + n)).obj L := DE.divι k n S ≫ liftMap s n
    have : Mono (liftMap (E := A.E) s n) := mono_liftMap _ n
    have : Mono ιX := mono_comp _ _
    have hw' : w ≫ ιX ≠ 0 := fun h ↦ hw ((cancel_mono ιX).1 (by rw [h, zero_comp]))
    obtain ⟨y, hy⟩ := DE.exists_comp_divπ_ne_zero (k := k) hw'
    exact ⟨ιX ≫ y ≫ DE.divπ k (r + n) L, by simpa only [Category.assoc] using hy⟩
  -- (9) so `[X] = [T]` and `X` is simple
  obtain ⟨h0, h1⟩ := A.toK0Data.repr_cls_le_finrank_hom k hdet
  have hXnz : ¬IsZero X := by
    intro h
    apply hne
    have h1 := DE.cls_Epow k A.toK0Data n S
    rw [A.toK0Data.cls_Epow_obj A.cls_E, hclsS, A.toK0Data.cls_eq_zero_of_isZero h,
      smul_zero] at h1
    exact h1
  have h2 := A.toK0Data.one_le_repr_of_not_isZero hXnz h0
  have h3 : A.B.repr (A.cls X) c = 1 := by
    have : (finrank k (X ⟶ T) : ℚ) ≤ 1 := by exact_mod_cast hfinXT
    linarith
  refine A.toK0Data.simple_of_cls_eq_basis (c := c) ?_
  apply A.B.repr.injective
  ext j
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hj : j = c
  · simp [hj, h3]
  · simp [h0 j hj, Ne.symm hj]

end WeakSl2

end Categorification.Sl2
