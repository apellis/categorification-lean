/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.SplitK0
import Categorification.Algebra.Graded.ProjectiveCover
import Mathlib.Tactic.Abel

/-!
# Krull–Schmidt for Hom-finite idempotent complete linear categories

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.6
(TeX `\subsection{$K_0(\dot{\cal{U}})$ and homomorphism $\gamma$}`): "The space of homs between
any two objects in `U̇(λ, μ)` is a finite-dimensional `k`-vector space. In particular, the
Krull–Schmidt decomposition theorem holds […] Any object of `U̇(λ, μ)` has a unique
presentation, up to permutation of factors and isomorphisms, as a direct sum of
indecomposables. Choose one representative `b` for each isomorphism class of indecomposables,
up to grading shifts […] Then `{[b]}_b` is a basis of `K₀(U̇(λ, μ))`, viewed as a free
`ℤ[q, q⁻¹]`-module"; and §3.8.2, Proposition 3.31 (label `prop-freemod`) with its proof
("Boundedness […] ensures that an indecomposable […] is not isomorphic to itself with a shifted
grading").

We prove this for an arbitrary `k`-linear category `𝒞` over a field, with binary biproducts,
idempotent complete, whose Hom-spaces are finite-dimensional (`HomFinite`):

* `of_mem_closure_indec`: **existence of decompositions**: the class of every object in the split
  Grothendieck group is a sum of classes of indecomposables (induction on `dim End(X)`);
* `isLocalRing_end`: the endomorphism ring of an indecomposable is local (Fitting's lemma);
* `multK hZ : K₀(𝒞) →+ ℤ`: for an indecomposable `Z`, the additive invariant
  `[X] ↦ dim Hom(Z, X) - dim rad(Z, X)` (`rad(Z, X)` = the maps `f` with `f ≫ g` never invertible);
  it is positive on `Z` (`multK_self_pos`) and zero on indecomposables not isomorphic to `Z`
  (`multK_of_not_iso`) — this is the uniqueness part of Krull–Schmidt;
* with grading shifts (`SplitK0.K0Shift`) such that no indecomposable is isomorphic to a nonzero
  shift of itself (`hrig`): `IndecClass 𝒞` (indecomposables up to isomorphism and shift),
  `indecBasis hrig : Basis (IndecClass 𝒞) ℤ[q, q⁻¹] K₀(𝒞)` with `indecBasis b = [rep b]`, and
  `free hrig : Module.Free ℤ[q, q⁻¹] K₀(𝒞)`.
-/

noncomputable section

namespace Categorification.KrullSchmidtCat

open CategoryTheory CategoryTheory.Limits Module

universe v u

/-- A `k`-linear category is **Hom-finite** if all its Hom-spaces are finite-dimensional. -/
class HomFinite (k : Type*) [Field k] (𝒞 : Type u) [Category.{v} 𝒞] [Preadditive 𝒞]
    [Linear k 𝒞] : Prop where
  finiteDimensional : ∀ X Y : 𝒞, FiniteDimensional k (X ⟶ Y)

attribute [instance] HomFinite.finiteDimensional

variable {𝒞 : Type u} [Category.{v} 𝒞] [Preadditive 𝒞]

/-- An object is **indecomposable** if it is nonzero and its only idempotent endomorphisms are
`0` and `1`. -/
def IsIndec (X : 𝒞) : Prop := ¬ IsZero X ∧ ∀ e : X ⟶ X, e ≫ e = e → e = 0 ∨ e = 𝟙 X

/-! ## Splitting idempotents -/

section Split

variable [HasBinaryBiproducts 𝒞]

/-- The isomorphism `X ≅ Y ⊞ Z` given by a complete family of orthogonal retractions. -/
@[simps]
def isoOfData {X Y Z : 𝒞} (i : Y ⟶ X) (p : X ⟶ Y) (i' : Z ⟶ X) (p' : X ⟶ Z)
    (h₁ : i ≫ p = 𝟙 Y) (h₂ : i' ≫ p' = 𝟙 Z) (h₃ : i ≫ p' = 0) (h₄ : i' ≫ p = 0)
    (h₅ : p ≫ i + p' ≫ i' = 𝟙 X) : X ≅ Y ⊞ Z where
  hom := biprod.lift p p'
  inv := biprod.desc i i'
  hom_inv_id := by rw [biprod.lift_desc, h₅]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [h₁, h₂, h₃, h₄]

omit [HasBinaryBiproducts 𝒞] in
theorem idem_one_sub {X : 𝒞} {e : X ⟶ X} (he : e ≫ e = e) : (𝟙 X - e) ≫ (𝟙 X - e) = 𝟙 X - e := by
  simp [Preadditive.sub_comp, Preadditive.comp_sub, he]

omit [HasBinaryBiproducts 𝒞] in
/-- **Splitting an idempotent** in an idempotent complete category: `X ≅ im e ⊞ im (1 - e)`. -/
theorem exists_split [IsIdempotentComplete 𝒞] {X : 𝒞} (e : X ⟶ X) (he : e ≫ e = e) :
    ∃ (Y Z : 𝒞) (i : Y ⟶ X) (p : X ⟶ Y) (i' : Z ⟶ X) (p' : X ⟶ Z), i ≫ p = 𝟙 Y ∧
      i' ≫ p' = 𝟙 Z ∧ i ≫ p' = 0 ∧ i' ≫ p = 0 ∧ p ≫ i = e ∧ p' ≫ i' = 𝟙 X - e := by
  obtain ⟨Y, i, p, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split X e he
  obtain ⟨Z, i', p', h₁', h₂'⟩ :=
    IsIdempotentComplete.idempotents_split X (𝟙 X - e) (idem_one_sub he)
  have hi : i = i ≫ e := by rw [← h₂, ← Category.assoc, h₁, Category.id_comp]
  have hp' : p' = (𝟙 X - e) ≫ p' := by rw [← h₂', Category.assoc, h₁', Category.comp_id]
  have hi' : i' = i' ≫ (𝟙 X - e) := by rw [← h₂', ← Category.assoc, h₁', Category.id_comp]
  have hp : p = e ≫ p := by rw [← h₂, Category.assoc, h₁, Category.comp_id]
  refine ⟨Y, Z, i, p, i', p', h₁, h₁', ?_, ?_, h₂, h₂'⟩
  · rw [hi, hp', Category.assoc, ← Category.assoc e]
    simp [Preadditive.comp_sub, he]
  · rw [hi', hp, Category.assoc, ← Category.assoc (𝟙 X - e)]
    simp [Preadditive.sub_comp, he]

/-- An indecomposable object does not split into two nonzero summands. -/
theorem IsIndec.isZero_or_isZero {X Y Z : 𝒞} (hX : IsIndec X) (φ : X ≅ Y ⊞ Z) :
    IsZero Y ∨ IsZero Z := by
  set e := φ.hom ≫ biprod.fst ≫ biprod.inl ≫ φ.inv
  have he : e ≫ e = e := by simp [e]
  rcases hX.2 e he with h | h
  · left
    rw [IsZero.iff_id_eq_zero]
    have : biprod.inl ≫ φ.inv ≫ e ≫ φ.hom ≫ biprod.fst = 𝟙 Y := by simp [e]
    rw [← this, h]; simp
  · right
    rw [IsZero.iff_id_eq_zero]
    have : biprod.inr ≫ φ.inv ≫ (𝟙 X - e) ≫ φ.hom ≫ biprod.snd = 𝟙 Z := by
      simp [e, Preadditive.sub_comp, Preadditive.comp_sub]
    rw [← this, h, sub_self]; simp

/-- **Indecomposability via biproducts** (idempotent complete categories). -/
theorem isIndec_iff [IsIdempotentComplete 𝒞] {X : 𝒞} :
    IsIndec X ↔ ¬ IsZero X ∧ ∀ Y Z : 𝒞, Nonempty (X ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z := by
  refine ⟨fun h => ⟨h.1, fun Y Z ⟨φ⟩ => h.isZero_or_isZero φ⟩, fun ⟨h0, h⟩ => ⟨h0, fun e he => ?_⟩⟩
  obtain ⟨Y, Z, i, p, i', p', h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_split e he
  rcases h Y Z ⟨isoOfData i p i' p' h₁ h₂ h₃ h₄ (by rw [h₅, h₆, add_sub_cancel])⟩ with hY | hZ
  · left; rw [← h₅, hY.eq_of_src i, Limits.comp_zero]
  · right
    have : 𝟙 X - e = 0 := by rw [← h₆, hZ.eq_of_src i', Limits.comp_zero]
    exact (sub_eq_zero.1 this).symm

end Split

/-! ## Existence of decompositions -/

section Existence

variable (k : Type*) [Field k] [Linear k 𝒞] [HomFinite k 𝒞] [HasBinaryBiproducts 𝒞]
  [IsIdempotentComplete 𝒞]

omit [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
theorem finrank_end_pos {X : 𝒞} (hX : ¬ IsZero X) : 0 < finrank k (X ⟶ X) := by
  refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨𝟙 X, fun h => hX ?_⟩
  rwa [IsZero.iff_id_eq_zero]

omit [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
/-- A proper summand has a smaller endomorphism algebra. -/
theorem finrank_end_lt {X Y Z : 𝒞} (i : Y ⟶ X) (p : X ⟶ Y) (i' : Z ⟶ X) (p' : X ⟶ Z)
    (h₁ : i ≫ p = 𝟙 Y) (h₂ : i' ≫ p' = 𝟙 Z) (h₃ : i ≫ p' = 0) (h₄ : i' ≫ p = 0)
    (hZ : ¬ IsZero Z) : finrank k (Y ⟶ Y) < finrank k (X ⟶ X) := by
  let Φ : ((Y ⟶ Y) × (Z ⟶ Z)) →ₗ[k] (X ⟶ X) :=
    (Linear.leftComp k X p ∘ₗ Linear.rightComp k Y i) ∘ₗ LinearMap.fst k _ _ +
      (Linear.leftComp k X p' ∘ₗ Linear.rightComp k Z i') ∘ₗ LinearMap.snd k _ _
  have hΦ' : ∀ fg, Φ fg = p ≫ fg.1 ≫ i + p' ≫ fg.2 ≫ i' := fun fg => rfl
  have hΦ : Function.Injective Φ := by
    intro a b hab
    rw [hΦ', hΦ'] at hab
    have e₁ := congrArg (fun g => i ≫ g ≫ p) hab
    have e₂ := congrArg (fun g => i' ≫ g ≫ p') hab
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      Category.assoc, reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, h₁, h₂, h₃,
      h₄, Limits.zero_comp, Limits.comp_zero, add_zero, zero_add, Category.comp_id] at e₁ e₂
    exact Prod.ext e₁ e₂
  have := LinearMap.finrank_le_finrank_of_injective hΦ
  rw [Module.finrank_prod] at this
  have := finrank_end_pos k hZ
  omega

include k in
/-- **Existence of Krull–Schmidt decompositions**: the class of every object is a sum of
classes of indecomposable objects. -/
theorem of_mem_closure_indec (X : 𝒞) :
    SplitK0.of X ∈ AddSubmonoid.closure {x | ∃ Z : 𝒞, IsIndec Z ∧ x = SplitK0.of Z} := by
  induction h : finrank k (X ⟶ X) using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    by_cases h0 : IsZero X
    · rw [SplitK0.of_isZero h0]; exact AddSubmonoid.zero_mem _
    by_cases hi : IsIndec X
    · exact AddSubmonoid.subset_closure ⟨X, hi, rfl⟩
    obtain ⟨e, he, he0, he1⟩ : ∃ e : X ⟶ X, e ≫ e = e ∧ e ≠ 0 ∧ e ≠ 𝟙 X := by
      by_contra hne
      push_neg at hne
      exact hi ⟨h0, fun e he => by
        by_cases h' : e = 0
        · exact Or.inl h'
        · exact Or.inr (hne e he h')⟩
    obtain ⟨Y, Z, i, p, i', p', h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_split e he
    have hY : ¬ IsZero Y := fun hY => he0 (by rw [← h₅, hY.eq_of_src i, Limits.comp_zero])
    have hZ : ¬ IsZero Z := fun hZ => he1 (by
      have : 𝟙 X - e = 0 := by rw [← h₆, hZ.eq_of_src i', Limits.comp_zero]
      exact (sub_eq_zero.1 this).symm)
    rw [SplitK0.of_eq_add_of_iso (isoOfData i p i' p' h₁ h₂ h₃ h₄
      (by rw [h₅, h₆, add_sub_cancel]))]
    refine AddSubmonoid.add_mem _ (ih _ ?_ Y rfl) (ih _ ?_ Z rfl)
    · rw [← h]; exact finrank_end_lt k i p i' p' h₁ h₂ h₃ h₄ hZ
    · rw [← h]; exact finrank_end_lt k i' p' i p h₂ h₁ h₄ h₃ hY

end Existence

/-! ## Local endomorphism rings and the multiplicity functionals -/

section Mult

variable (k : Type*) [Field k] [Linear k 𝒞] [HomFinite k 𝒞]

include k in
/-- **Fitting's lemma**: an endomorphism of an indecomposable object is nilpotent or invertible. -/
theorem IsIndec.isNilpotent_or_isUnit {X : 𝒞} (hX : IsIndec X) (f : End X) :
    IsNilpotent f ∨ IsUnit f := by
  haveI : FiniteDimensional k (End X) := HomFinite.finiteDimensional X X
  refine Graded.isNilpotent_or_isUnit_of_idempotent k (fun e he => ?_) f
  have he' : e ≫ e = e := by rw [← End.mul_def]; exact he.eq
  rcases hX.2 e he' with h | h
  · exact Or.inl h
  · exact Or.inr h

omit [HomFinite k 𝒞] [Linear k 𝒞] in
theorem IsIndec.nontrivial {X : 𝒞} (hX : IsIndec X) : Nontrivial (End X) :=
  ⟨⟨0, 1, fun h => hX.1 ((IsZero.iff_id_eq_zero _).2 h.symm)⟩⟩

include k in
/-- **The endomorphism ring of an indecomposable object is local.** -/
theorem IsIndec.isLocalRing {X : 𝒞} (hX : IsIndec X) : IsLocalRing (End X) :=
  haveI := hX.nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    (hX.isNilpotent_or_isUnit k a).elim (fun h => Or.inr h.isUnit_one_sub) Or.inl

omit [HomFinite k 𝒞] [Linear k 𝒞] in
/-- In a (possibly noncommutative) local ring, a sum of nonunits is a nonunit. -/
theorem nonunits_add' {R : Type*} [Ring R] [IsLocalRing R] {a b : R} (ha : ¬ IsUnit a)
    (hb : ¬ IsUnit b) : ¬ IsUnit (a + b) := by
  rintro ⟨u, hu⟩
  have h : (↑u⁻¹ * a) + (↑u⁻¹ * b) = 1 := by rw [← mul_add, ← hu, Units.inv_mul]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h with h' | h'
  · exact ha ((Units.isUnit_units_mul u⁻¹ a).1 h')
  · exact hb ((Units.isUnit_units_mul u⁻¹ b).1 h')

/-- The radical `rad(Z, X)`: the morphisms `f : Z → X` such that `f ≫ g` is never invertible. -/
def rad {Z : 𝒞} (hZ : IsIndec Z) (X : 𝒞) : Submodule k (Z ⟶ X) where
  carrier := {f | ∀ g : X ⟶ Z, ¬ IsUnit (M := End Z) (f ≫ g)}
  zero_mem' g h := by
    haveI := hZ.nontrivial
    rw [Limits.zero_comp] at h
    exact not_isUnit_zero h
  add_mem' {f f'} hf hf' g := by
    haveI := hZ.isLocalRing k
    rw [Preadditive.add_comp]
    exact nonunits_add' (R := End Z) (hf g) (hf' g)
  smul_mem' c f hf g h := by
    rw [Linear.smul_comp] at h
    have hi : IsIso (c • (f ≫ g)) := (isUnit_iff_isIso (X := Z) _).1 h
    refine hf g ⟨⟨f ≫ g, c • inv (c • (f ≫ g)), ?_, ?_⟩, rfl⟩
    · rw [End.mul_def, Linear.smul_comp, ← Linear.comp_smul, IsIso.inv_hom_id]; rfl
    · rw [End.mul_def, Linear.comp_smul, ← Linear.smul_comp, IsIso.hom_inv_id]; rfl

variable {k}

theorem mem_rad {Z X : 𝒞} {hZ : IsIndec Z} {f : Z ⟶ X} :
    f ∈ rad k hZ X ↔ ∀ g : X ⟶ Z, ¬ IsUnit (M := End Z) (f ≫ g) := Iff.rfl

variable (k)

/-- Postcomposition with an isomorphism. -/
@[simps]
def postIso (Z : 𝒞) {X X' : 𝒞} (φ : X ≅ X') : (Z ⟶ X) ≃ₗ[k] (Z ⟶ X') where
  toFun f := f ≫ φ.hom
  invFun f := f ≫ φ.inv
  map_add' := by simp
  map_smul' := by simp
  left_inv f := by simp
  right_inv f := by simp

theorem rad_map_postIso {Z : 𝒞} (hZ : IsIndec Z) {X X' : 𝒞} (φ : X ≅ X') :
    (rad k hZ X).map (postIso k Z φ).toLinearMap = rad k hZ X' := by
  ext f
  constructor
  · rintro ⟨f₀, hf₀, rfl⟩ g
    simpa using hf₀ (φ.hom ≫ g)
  · intro hf
    refine ⟨f ≫ φ.inv, fun g => ?_, by simp⟩
    simpa using hf (φ.inv ≫ g)

/-- The multiplicity invariant `dim Hom(Z, X) - dim rad(Z, X)`. -/
def mult {Z : 𝒞} (hZ : IsIndec Z) (X : 𝒞) : ℤ :=
  (finrank k (Z ⟶ X) : ℤ) - finrank k (rad k hZ X)

theorem mult_iso {Z : 𝒞} (hZ : IsIndec Z) {X X' : 𝒞} (φ : X ≅ X') :
    mult k hZ X = mult k hZ X' := by
  unfold mult
  rw [(postIso k Z φ).finrank_eq, ← rad_map_postIso k hZ φ, LinearEquiv.finrank_map_eq]

theorem finrank_submodule_prod {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k N] [FiniteDimensional k M] [FiniteDimensional k N] (p : Submodule k M)
    (q : Submodule k N) : finrank k (p.prod q) = finrank k p + finrank k q := by
  let e : p.prod q ≃ₗ[k] p × q :=
    { toFun := fun x => (⟨x.1.1, (Submodule.mem_prod.1 x.2).1⟩, ⟨x.1.2, (Submodule.mem_prod.1 x.2).2⟩)
      invFun := fun y => ⟨(y.1.1, y.2.1), Submodule.mem_prod.2 ⟨y.1.2, y.2.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e.finrank_eq, Module.finrank_prod]

variable [HasBinaryBiproducts 𝒞]

/-- `Hom(Z, X ⊞ Y) ≅ Hom(Z, X) × Hom(Z, Y)`. -/
@[simps]
def biprodEquiv (Z X Y : 𝒞) : (Z ⟶ X ⊞ Y) ≃ₗ[k] (Z ⟶ X) × (Z ⟶ Y) where
  toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
  invFun ab := biprod.lift ab.1 ab.2
  map_add' f g := by simp
  map_smul' c f := by simp
  left_inv f := by apply biprod.hom_ext <;> simp
  right_inv ab := by simp

theorem rad_map_biprodEquiv {Z : 𝒞} (hZ : IsIndec Z) (X Y : 𝒞) :
    (rad k hZ (X ⊞ Y)).map (biprodEquiv k Z X Y).toLinearMap = (rad k hZ X).prod (rad k hZ Y) := by
  ext ⟨a, b⟩
  simp only [Submodule.mem_map, Submodule.mem_prod, LinearEquiv.coe_coe, biprodEquiv_apply,
    Prod.mk.injEq]
  constructor
  · rintro ⟨f, hf, rfl, rfl⟩
    exact ⟨fun g => by simpa using hf (biprod.fst ≫ g), fun g => by simpa using hf (biprod.snd ≫ g)⟩
  · rintro ⟨ha, hb⟩
    refine ⟨biprod.lift a b, fun g => ?_, by simp, by simp⟩
    haveI := hZ.isLocalRing k
    rw [biprod.lift_eq, Preadditive.add_comp, Category.assoc, Category.assoc]
    exact nonunits_add' (R := End Z) (ha _) (hb _)

theorem mult_biprod {Z : 𝒞} (hZ : IsIndec Z) (X Y : 𝒞) :
    mult k hZ (X ⊞ Y) = mult k hZ X + mult k hZ Y := by
  unfold mult
  rw [(biprodEquiv k Z X Y).finrank_eq, Module.finrank_prod, ← LinearEquiv.finrank_map_eq
    (biprodEquiv k Z X Y), rad_map_biprodEquiv, finrank_submodule_prod]
  push_cast; ring

/-- **The multiplicity functional** `K₀(𝒞) → ℤ` of an indecomposable object `Z`. -/
def multK {Z : 𝒞} (hZ : IsIndec Z) : SplitK0 𝒞 →+ ℤ :=
  SplitK0.lift (mult k hZ) (fun _ _ e => mult_iso k hZ e) (mult_biprod k hZ)

@[simp] theorem multK_of {Z : 𝒞} (hZ : IsIndec Z) (X : 𝒞) :
    multK k hZ (SplitK0.of X) = mult k hZ X := SplitK0.lift_of _ _ _ _

theorem multK_self_pos {Z : 𝒞} (hZ : IsIndec Z) : 0 < multK k hZ (SplitK0.of Z) := by
  rw [multK_of, mult, sub_pos, Nat.cast_lt]
  refine Submodule.finrank_lt fun h => ?_
  have : 𝟙 Z ∈ rad k hZ Z := h ▸ Submodule.mem_top
  exact this (𝟙 Z) (by rw [Category.comp_id]; exact isUnit_one)

/-- **Uniqueness part of Krull–Schmidt**: the multiplicity functional of `Z` vanishes on the
indecomposables not isomorphic to `Z`. -/
theorem multK_of_not_iso {Z Z' : 𝒞} (hZ : IsIndec Z) (hZ' : IsIndec Z')
    (h : ¬ Nonempty (Z ≅ Z')) : multK k hZ (SplitK0.of Z') = 0 := by
  have htop : rad k hZ Z' = ⊤ := by
    refine eq_top_iff.2 fun f _ g hfg => h ?_
    obtain ⟨u, hu⟩ := hfg
    have hv : f ≫ g ≫ (↑u⁻¹ : End Z) = 𝟙 Z := by
      have := u.inv_mul
      rw [End.mul_def, hu] at this
      rw [← Category.assoc]; exact this
    set g' : Z' ⟶ Z := g ≫ (↑u⁻¹ : End Z)
    have he : (g' ≫ f) ≫ (g' ≫ f) = g' ≫ f := by
      rw [Category.assoc, ← Category.assoc f, hv, Category.id_comp]
    rcases hZ'.2 _ he with h0 | h1
    · exfalso
      apply hZ.1
      rw [IsZero.iff_id_eq_zero]
      calc 𝟙 Z = (f ≫ g') ≫ (f ≫ g') := by rw [hv, Category.id_comp]
        _ = f ≫ (g' ≫ f) ≫ g' := by simp only [Category.assoc]
        _ = 0 := by rw [h0]; simp
    · exact ⟨⟨f, g', hv, h1⟩⟩
  rw [multK_of, mult, htop, finrank_top, sub_self]

end Mult

/-! ## Grading shifts and the basis of `K₀` -/

section Shift

variable (k : Type*) [Field k] [Linear k 𝒞] [HomFinite k 𝒞] [HasBinaryBiproducts 𝒞]
  [IsIdempotentComplete 𝒞] [SplitK0.K0Shift 𝒞]

open SplitK0 SplitK0.K0Shift

omit [IsIdempotentComplete 𝒞] [SplitK0.K0Shift 𝒞] in
include k in
theorem isZero_of_iso_biprod_self {A : 𝒞} (e : A ≅ A ⊞ A) : IsZero A := by
  have h := (postIso k A e).finrank_eq
  rw [(biprodEquiv k A A A).finrank_eq, Module.finrank_prod] at h
  have h0 : finrank k (A ⟶ A) = 0 := by omega
  rw [IsZero.iff_id_eq_zero]
  haveI := Module.finrank_zero_iff.1 h0
  exact Subsingleton.elim _ _

omit [IsIdempotentComplete 𝒞] in
include k in
theorem isZero_sh (n : ℤ) {X : 𝒞} (hX : IsZero X) : IsZero (sh n X) := by
  have e : X ≅ X ⊞ X :=
    { hom := biprod.lift 0 0
      inv := biprod.desc 0 0
      hom_inv_id := hX.eq_of_src _ _
      inv_hom_id := biprod.hom_ext _ _ (hX.eq_of_tgt _ _) (hX.eq_of_tgt _ _) }
  obtain ⟨e'⟩ := sh_iso n e
  obtain ⟨b⟩ := sh_biprod n X X
  exact isZero_of_iso_biprod_self k (e' ≪≫ b)

omit [IsIdempotentComplete 𝒞] [HomFinite k 𝒞] [Linear k 𝒞] in
theorem nonempty_sh_neg_sh (n : ℤ) (X : 𝒞) : Nonempty (sh (-n) (sh n X) ≅ X) := by
  obtain ⟨e₁⟩ := sh_add n (-n) X
  obtain ⟨e₂⟩ := sh_zero (C := 𝒞) X
  rw [add_neg_cancel] at e₁
  exact ⟨e₁.symm ≪≫ e₂⟩

omit [IsIdempotentComplete 𝒞] in
include k in
theorem isZero_of_isZero_sh (n : ℤ) {X : 𝒞} (h : IsZero (sh n X)) : IsZero X := by
  obtain ⟨e⟩ := nonempty_sh_neg_sh n X
  exact (isZero_sh k (-n) h).of_iso e.symm

include k in
/-- **Shifts of indecomposables are indecomposable.** -/
theorem IsIndec.sh (n : ℤ) {X : 𝒞} (hX : IsIndec X) : IsIndec (sh n X) := by
  refine isIndec_iff.2 ⟨fun h => hX.1 (isZero_of_isZero_sh k n h), fun Y Z ⟨φ⟩ => ?_⟩
  obtain ⟨e₁⟩ := nonempty_sh_neg_sh n X
  obtain ⟨e₂⟩ := sh_iso (-n) φ
  obtain ⟨e₃⟩ := sh_biprod (-n) Y Z
  rcases hX.isZero_or_isZero (e₁.symm ≪≫ e₂ ≪≫ e₃) with h | h
  · exact Or.inl (isZero_of_isZero_sh k (-n) h)
  · exact Or.inr (isZero_of_isZero_sh k (-n) h)

omit [IsIdempotentComplete 𝒞] [HomFinite k 𝒞] [Linear k 𝒞] in
theorem nonempty_sh_sh (m n : ℤ) (X : 𝒞) : Nonempty (sh n (sh m X) ≅ sh (m + n) X) := by
  obtain ⟨e⟩ := sh_add m n X
  exact ⟨e.symm⟩

variable (𝒞) in
/-- Indecomposables up to isomorphism and grading shift: `X ~ Y` iff `X ≅ Y{n}` for some `n`. -/
def indecSetoid : Setoid {X : 𝒞 // IsIndec X} where
  r X Y := ∃ n : ℤ, Nonempty (X.1 ≅ sh n Y.1)
  iseqv := by
    refine ⟨fun X => ⟨0, ?_⟩, fun {X Y} ⟨n, ⟨e⟩⟩ => ⟨-n, ?_⟩, fun {X Y W} ⟨n, ⟨e⟩⟩ ⟨m, ⟨f⟩⟩ =>
      ⟨m + n, ?_⟩⟩
    · obtain ⟨e⟩ := sh_zero (C := 𝒞) X.1; exact ⟨e.symm⟩
    · obtain ⟨e'⟩ := sh_iso (-n) e
      obtain ⟨e''⟩ := nonempty_sh_neg_sh n Y.1
      exact ⟨(e' ≪≫ e'').symm⟩
    · obtain ⟨f'⟩ := sh_iso n f
      obtain ⟨g⟩ := nonempty_sh_sh m n W.1
      exact ⟨e ≪≫ f' ≪≫ g⟩

variable (𝒞) in
/-- **The index set of the basis of `K₀`**: indecomposable objects up to isomorphism and grading
shift (KL III's `Ḃ(λ, μ)`). -/
def IndecClass : Type _ := Quotient (indecSetoid 𝒞)

omit [IsIdempotentComplete 𝒞] [HomFinite k 𝒞] [Linear k 𝒞] in
/-- The chosen representative of a class of indecomposables. -/
def IndecClass.rep (b : IndecClass 𝒞) : 𝒞 := (Quotient.out b).1

omit [IsIdempotentComplete 𝒞] [HomFinite k 𝒞] [Linear k 𝒞] in
theorem IndecClass.isIndec_rep (b : IndecClass 𝒞) : IsIndec b.rep := (Quotient.out b).2

omit [IsIdempotentComplete 𝒞] [HomFinite k 𝒞] [Linear k 𝒞] in
theorem IndecClass.exists_iso_sh_rep {X : 𝒞} (hX : IsIndec X) :
    ∃ n : ℤ, Nonempty (X ≅ sh n (IndecClass.rep (Quotient.mk (indecSetoid 𝒞) ⟨X, hX⟩))) := by
  obtain ⟨n, ⟨e⟩⟩ := Quotient.mk_out (s := indecSetoid 𝒞) ⟨X, hX⟩
  obtain ⟨e'⟩ := sh_iso (-n) e
  obtain ⟨e''⟩ := nonempty_sh_neg_sh n X
  exact ⟨-n, ⟨(e' ≪≫ e'').symm⟩⟩

omit [IsIdempotentComplete 𝒞] [HomFinite k 𝒞] [Linear k 𝒞] in
theorem IndecClass.eq_of_iso {b b' : IndecClass 𝒞} {n : ℤ} (e : b.rep ≅ sh n b'.rep) : b = b' := by
  rw [← Quotient.out_eq b, ← Quotient.out_eq b']
  exact Quotient.sound ⟨n, ⟨e⟩⟩

variable (hrig : ∀ (n : ℤ) (X : 𝒞), IsIndec X → Nonempty (sh n X ≅ X) → n = 0)
include hrig

omit [IsIdempotentComplete 𝒞] [HomFinite k 𝒞] [Linear k 𝒞] in
theorem eq_of_sh_iso_sh {X : 𝒞} (hX : IsIndec X) {m n : ℤ} (e : sh m X ≅ sh n X) : m = n := by
  obtain ⟨e₁⟩ := sh_iso (-n) e
  obtain ⟨e₂⟩ := nonempty_sh_neg_sh n X
  obtain ⟨e₃⟩ := nonempty_sh_sh m (-n) X
  have := hrig (m + -n) X hX ⟨e₃.symm ≪≫ e₁ ≪≫ e₂⟩
  omega

omit hrig [IsIdempotentComplete 𝒞] [HomFinite k 𝒞] [Linear k 𝒞] in
theorem addHom_smul (ψ : SplitK0 𝒞 →+ ℤ) (p : LaurentPolynomial ℤ) (x : SplitK0 𝒞) :
    ψ (p • x) = Finsupp.sum p fun n a => a * ψ (shiftHom n x) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [add_smul, map_add, hp, hq, Finsupp.sum_add_index' (by simp) (by intros; ring)]
  | C_mul_T n a =>
    rw [C_mul_T_smul, map_zsmul, ← LaurentPolynomial.single_eq_C_mul_T,
      Finsupp.sum_single_index (by simp), smul_eq_mul]

include k

open Classical in
theorem multK_sh_rep (b₀ : IndecClass 𝒞) (n : ℤ) (b : IndecClass 𝒞) (m : ℤ) :
    multK k (b₀.isIndec_rep.sh k n) (of (sh m b.rep)) =
      if b = b₀ ∧ m = n then multK k (b₀.isIndec_rep.sh k n) (of (sh n b₀.rep)) else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · refine multK_of_not_iso k _ (b.isIndec_rep.sh k m) fun ⟨e⟩ => h ?_
    obtain ⟨e₁⟩ := sh_iso (-n) e
    obtain ⟨e₂⟩ := nonempty_sh_neg_sh n b₀.rep
    obtain ⟨e₃⟩ := nonempty_sh_sh m (-n) b.rep
    have hb : b₀ = b := IndecClass.eq_of_iso (e₂.symm ≪≫ e₁ ≪≫ e₃)
    subst hb
    exact ⟨rfl, (eq_of_sh_iso_sh hrig b₀.isIndec_rep e.symm)⟩

/-- **Linear independence of the classes of indecomposables up to shift.** -/
theorem linearIndependent_indec :
    LinearIndependent (LaurentPolynomial ℤ) fun b : IndecClass 𝒞 => of b.rep := by
  classical
  rw [linearIndependent_iff']
  intro s g hg b₀ hb₀
  ext n
  have key := congrArg (multK k (b₀.isIndec_rep.sh k n)) hg
  rw [map_sum, map_zero] at key
  simp only [addHom_smul, shiftHom_of] at key
  have hpos := multK_self_pos k (b₀.isIndec_rep.sh k n)
  obtain ⟨D, hD⟩ : ∃ D, multK k (b₀.isIndec_rep.sh k n) (of (sh n b₀.rep)) = D := ⟨_, rfl⟩
  rw [hD] at hpos
  have hval : ∀ b m, multK k (b₀.isIndec_rep.sh k n) (of (sh m b.rep)) =
      if b = b₀ ∧ m = n then D else 0 := by
    intro b m
    rw [multK_sh_rep k hrig b₀ n b m, hD]
  simp only [hval] at key
  rw [Finset.sum_eq_single b₀] at key
  · rw [Finsupp.sum, Finset.sum_eq_single n] at key
    · simp only [and_self, if_true, and_true] at key
      rcases mul_eq_zero.1 key with h | h
      · exact h
      · omega
    · intro m _ hm
      simp [hm]
    · intro hn
      simp [Finsupp.not_mem_support_iff.1 hn]
  · intro b _ hb
    simp [hb]
  · intro h; exact absurd hb₀ h

omit hrig in
theorem of_mem_span (X : 𝒞) :
    of X ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range fun b : IndecClass 𝒞 => of b.rep) := by
  have h := of_mem_closure_indec k X
  refine (AddSubmonoid.closure_le (S := (Submodule.span (LaurentPolynomial ℤ)
    (Set.range fun b : IndecClass 𝒞 => of b.rep)).toAddSubmonoid)).2 ?_ h
  rintro _ ⟨Z, hZ, rfl⟩
  obtain ⟨n, ⟨e⟩⟩ := IndecClass.exists_iso_sh_rep hZ
  change of Z ∈ Submodule.span _ _
  rw [of_iso e, ← T_smul_of]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

omit hrig in
theorem mem_span_indec (x : SplitK0 𝒞) :
    x ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range fun b : IndecClass 𝒞 => of b.rep) := by
  induction x using SplitK0.induction_on with
  | of X => exact of_mem_span k X
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | neg x hx => exact Submodule.neg_mem _ hx

/-- **KL III §3.6 / Proposition 3.31**: `K₀(𝒞)` is a free `ℤ[q, q⁻¹]`-module with basis the
classes of the indecomposable objects up to isomorphism and grading shift. -/
def indecBasis : Basis (IndecClass 𝒞) (LaurentPolynomial ℤ) (SplitK0 𝒞) :=
  Basis.mk (linearIndependent_indec k hrig) fun x _ => mem_span_indec k x

theorem indecBasis_apply (b : IndecClass 𝒞) : indecBasis k hrig b = of b.rep := by
  simp [indecBasis]

theorem free : Module.Free (LaurentPolynomial ℤ) (SplitK0 𝒞) :=
  Module.Free.of_basis (indecBasis k hrig)

/-- **`K₀(𝒞)` has no `ℤ[q, q⁻¹]`-torsion.** -/
theorem eq_zero_of_smul_eq_zero {p : LaurentPolynomial ℤ}
    (hp : p ∈ nonZeroDivisors (LaurentPolynomial ℤ)) {x : SplitK0 𝒞} (h : p • x = 0) : x = 0 := by
  refine (indecBasis k hrig).ext_elem fun b => ?_
  have := congrArg (fun y => (indecBasis k hrig).repr y b) h
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
  rw [map_zero, Finsupp.zero_apply]
  exact (mem_nonZeroDivisors_iff.1 hp) _ (by rw [mul_comm]; exact this)

end Shift

/-! ## Retracts of indecomposables through sums of factorizations -/

section Retract

variable (k : Type*) [Field k] [Linear k 𝒞] [HomFinite k 𝒞]

omit [HomFinite k 𝒞] [Linear k 𝒞] in
/-- In a local ring, if a finite sum is a unit then one of the summands is a unit. -/
theorem exists_isUnit_of_isUnit_sum {R : Type*} [Ring R] [IsLocalRing R] {ι : Type*}
    (s : Finset ι) (x : ι → R) (h : IsUnit (∑ i ∈ s, x i)) : ∃ i ∈ s, IsUnit (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at h
  | insert j s hj ih =>
    rw [Finset.sum_insert hj] at h
    by_cases hx : IsUnit (x j)
    · exact ⟨j, Finset.mem_insert_self _ _, hx⟩
    · by_cases hs : IsUnit (∑ i ∈ s, x i)
      · obtain ⟨i, hi, hu⟩ := ih hs
        exact ⟨i, Finset.mem_insert_of_mem hi, hu⟩
      · exact absurd h (nonunits_add' hx hs)

include k in
/-- **Retracts of indecomposables through sums**: if an indecomposable `Z` is a retract of `W`
and `1_W = ∑_i a_i ≫ b_i` with `a_i : W ⟶ V_i`, `b_i : V_i ⟶ W`, then `Z` is a retract of some
`V_i`. -/
theorem IsIndec.exists_retract_of_sum {Z W : 𝒞} (hZ : IsIndec Z) (f : Z ⟶ W) (g : W ⟶ Z)
    (hfg : f ≫ g = 𝟙 Z) {ι : Type*} (s : Finset ι) (V : ι → 𝒞) (a : ∀ i, W ⟶ V i)
    (b : ∀ i, V i ⟶ W) (htot : ∑ i ∈ s, a i ≫ b i = 𝟙 W) :
    ∃ i ∈ s, ∃ (f' : Z ⟶ V i) (g' : V i ⟶ Z), f' ≫ g' = 𝟙 Z := by
  haveI := hZ.isLocalRing k
  let x : ι → End Z := fun i => (f ≫ a i) ≫ (b i ≫ g)
  have hsum : ∑ i ∈ s, x i = (1 : End Z) := by
    show ∑ i ∈ s, (f ≫ a i) ≫ (b i ≫ g) = 𝟙 Z
    calc ∑ i ∈ s, (f ≫ a i) ≫ (b i ≫ g) = f ≫ (∑ i ∈ s, a i ≫ b i) ≫ g := by
          simp [Preadditive.sum_comp, Preadditive.comp_sum]
      _ = 𝟙 Z := by rw [htot, Category.id_comp, hfg]
  obtain ⟨i, hi, ⟨u, hu⟩⟩ := exists_isUnit_of_isUnit_sum s x (by rw [hsum]; exact isUnit_one)
  refine ⟨i, hi, f ≫ a i, b i ≫ g ≫ (↑u⁻¹ : End Z), ?_⟩
  have := u.inv_mul
  rw [End.mul_def, hu] at this
  have e : x i ≫ (↑u⁻¹ : End Z) = (f ≫ a i) ≫ (b i ≫ g ≫ (↑u⁻¹ : End Z)) := by
    simp only [x, Category.assoc]
  rw [← e]
  exact this

end Retract

/-! ## Uniqueness of decompositions -/

section Unique

variable (k : Type*) [Field k] [Linear k 𝒞] [HomFinite k 𝒞] [HasBinaryBiproducts 𝒞]

open Classical in
theorem multK_sum_indec {Z : 𝒞} (hZ : IsIndec Z) :
    ∀ L : List 𝒞, (∀ Y ∈ L, IsIndec Y) →
      multK k hZ (L.map SplitK0.of).sum =
        (L.countP fun Y => Nonempty (Y ≅ Z)) * multK k hZ (SplitK0.of Z)
  | [], _ => by simp
  | Y :: L, hL => by
    rw [List.map_cons, List.sum_cons, map_add, multK_sum_indec hZ L
      (fun Y' hY' => hL Y' (List.mem_cons_of_mem _ hY')), List.countP_cons]
    by_cases hY : Nonempty (Y ≅ Z)
    · obtain ⟨e⟩ := hY
      have hd : decide (Nonempty (Y ≅ Z)) = true := decide_eq_true ⟨e⟩
      rw [SplitK0.of_iso e, if_pos hd]; push_cast; ring
    · have hd : decide (Nonempty (Y ≅ Z)) = false := decide_eq_false hY
      rw [multK_of_not_iso k hZ (hL Y List.mem_cons_self) fun ⟨e⟩ => hY ⟨e.symm⟩, if_neg (by
        rw [hd]; exact Bool.false_ne_true)]
      simp

include k in
open Classical in
/-- **Uniqueness of Krull–Schmidt decompositions** (KL III §3.6: "Any object of `U̇(λ, μ)` has a
unique presentation, up to permutation of factors and isomorphisms, as a direct sum of
indecomposables"): if two lists of indecomposable objects have the same sum of classes in the
split Grothendieck group (e.g. isomorphic direct sums), then every indecomposable `Z` is
isomorphic to the same number of members of each list. -/
theorem countP_iso_eq_of_sum_eq {Z : 𝒞} (hZ : IsIndec Z) {L L' : List 𝒞}
    (hL : ∀ Y ∈ L, IsIndec Y) (hL' : ∀ Y ∈ L', IsIndec Y)
    (h : (L.map SplitK0.of).sum = (L'.map SplitK0.of).sum) :
    (L.countP fun Y => Nonempty (Y ≅ Z)) = L'.countP fun Y => Nonempty (Y ≅ Z) := by
  have e := congrArg (multK k hZ) h
  rw [multK_sum_indec k hZ L hL, multK_sum_indec k hZ L' hL'] at e
  have hpos := multK_self_pos k hZ
  exact_mod_cast Int.eq_of_mul_eq_mul_right hpos.ne' e

end Unique

end Categorification.KrullSchmidtCat
