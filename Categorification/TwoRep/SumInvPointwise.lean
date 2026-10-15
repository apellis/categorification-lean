/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqDual
import Categorification.TwoRep.PiLinear

/-!
# Explicit inverses of maps into and out of direct sums, componentwise

Rouquier's invertibility conditions (Brundan, arXiv:1501.00350v1, (1.8), (1.9)) are recorded by
explicit inverse components (`SumInvTo`, `SumInvFrom`). This file moves such data between
categories, as needed to assemble the weight-indexed cyclotomic Rouquier family of KL III
Thm. 1.2 from its blocks:

* `SumInvTo.map`, `SumInvFrom.map`: images under an additive functor;
* `SumInvTo.ofFullyFaithful`, `SumInvFrom.ofFullyFaithful`: preimages under a fully faithful
  additive functor (for instance the inclusion of the additive or linear functors);
* `SumInvTo.pi`, `SumInvFrom.pi`: in a product of categories, from each factor;
* `SumInvTo.ofApp`, `SumInvFrom.ofApp`: in a functor category, from each object. The inverse
  components of a natural transformation that is pointwise invertible are natural.
* `SumInvTo.ofIsZero`, `SumInvFrom.ofIsZero`: when the source of `f` is a zero object.

For the bicategory `LinearCat k`, `LinearCat.homForget` is the inclusion of a hom category into
the functor category, and `LinearCat.sigma_hom` writes Rouquier's rightward crossing as a
natural transformation.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits

section Map

variable {D D' : Type*} [Category D] [Preadditive D] [Category D'] [Preadditive D']
  (Φ : D ⥤ D') [Φ.Additive] {X Y Z : D} {n : ℕ}

/-- The image of an explicit inverse under an additive functor. -/
def SumInvTo.map {f : X ⟶ Y} {g : ℕ → (X ⟶ Z)} (S : SumInvTo f g n) :
    SumInvTo (Φ.map f) (fun m => Φ.map (g m)) n where
  f' := Φ.map S.f'
  g' m := Φ.map (S.g' m)
  total := by simpa [Functor.map_add, Functor.map_sum] using congrArg Φ.map S.total
  ff := by rw [← Φ.map_comp, S.ff, Φ.map_id]
  fg m hm := by rw [← Φ.map_comp, S.fg m hm, Φ.map_zero]
  gf m hm := by rw [← Φ.map_comp, S.gf m hm, Φ.map_zero]
  gg m m' hm hm' := by
    rw [← Φ.map_comp, S.gg m m' hm hm']
    split_ifs <;> simp

/-- The image of an explicit inverse under an additive functor. -/
def SumInvFrom.map {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)} (S : SumInvFrom f g n) :
    SumInvFrom (Φ.map f) (fun m => Φ.map (g m)) n where
  f' := Φ.map S.f'
  g' m := Φ.map (S.g' m)
  total := by simpa [Functor.map_add, Functor.map_sum] using congrArg Φ.map S.total
  ff := by rw [← Φ.map_comp, S.ff, Φ.map_id]
  fg m hm := by rw [← Φ.map_comp, S.fg m hm, Φ.map_zero]
  gf m hm := by rw [← Φ.map_comp, S.gf m hm, Φ.map_zero]
  gg m m' hm hm' := by
    rw [← Φ.map_comp, S.gg m m' hm hm']
    split_ifs <;> simp

variable [Φ.Full] [Φ.Faithful]

/-- An explicit inverse of the image under a fully faithful additive functor comes from one in
the source. -/
def SumInvTo.ofFullyFaithful {f : X ⟶ Y} {g : ℕ → (X ⟶ Z)}
    (S : SumInvTo (Φ.map f) (fun m => Φ.map (g m)) n) : SumInvTo f g n where
  f' := Φ.preimage S.f'
  g' m := Φ.preimage (S.g' m)
  total := Φ.map_injective (by simpa [Functor.map_add, Functor.map_sum] using S.total)
  ff := Φ.map_injective (by simpa using S.ff)
  fg m hm := Φ.map_injective (by simpa using S.fg m hm)
  gf m hm := Φ.map_injective (by simpa using S.gf m hm)
  gg m m' hm hm' := Φ.map_injective (by
    have h := S.gg m m' hm hm'
    split_ifs at h ⊢ <;> simpa using h)

/-- An explicit inverse of the image under a fully faithful additive functor comes from one in
the source. -/
def SumInvFrom.ofFullyFaithful {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)}
    (S : SumInvFrom (Φ.map f) (fun m => Φ.map (g m)) n) : SumInvFrom f g n where
  f' := Φ.preimage S.f'
  g' m := Φ.preimage (S.g' m)
  total := Φ.map_injective (by simpa [Functor.map_add, Functor.map_sum] using S.total)
  ff := Φ.map_injective (by simpa using S.ff)
  fg m hm := Φ.map_injective (by simpa using S.fg m hm)
  gf m hm := Φ.map_injective (by simpa using S.gf m hm)
  gg m m' hm hm' := Φ.map_injective (by
    have h := S.gg m m' hm hm'
    split_ifs at h ⊢ <;> simpa using h)

end Map

section Pi

variable {J : Type*} {D : J → Type*} [∀ j, Category (D j)] [∀ j, Preadditive (D j)]
  {X Y Z : ∀ j, D j} {n : ℕ}

/-- An explicit inverse in a product of categories, from one in each factor. -/
def SumInvTo.pi {f : X ⟶ Y} {g : ℕ → (X ⟶ Z)} (S : ∀ j, SumInvTo (f j) (fun m => g m j) n) :
    SumInvTo f g n where
  f' j := (S j).f'
  g' m j := (S j).g' m
  total := funext fun j => by
    have e := (Pi.eval D j).map_sum (fun m => g m ≫ fun j => (S j).g' m) (Finset.range n)
    exact (congrArg (fun t => f j ≫ (S j).f' + t) e).trans (S j).total
  ff := funext fun j => (S j).ff
  fg m hm := funext fun j => (S j).fg m hm
  gf m hm := funext fun j => (S j).gf m hm
  gg m m' hm hm' := funext fun j => by
    rw [pi_comp_apply, (S j).gg m m' hm hm']
    split_ifs <;> rfl

/-- An explicit inverse in a product of categories, from one in each factor. -/
def SumInvFrom.pi {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)} (S : ∀ j, SumInvFrom (f j) (fun m => g m j) n) :
    SumInvFrom f g n where
  f' j := (S j).f'
  g' m j := (S j).g' m
  total := funext fun j => by
    have e := (Pi.eval D j).map_sum (fun m => (fun j => (S j).g' m) ≫ g m) (Finset.range n)
    exact (congrArg (fun t => (S j).f' ≫ f j + t) e).trans (S j).total
  ff := funext fun j => (S j).ff
  fg m hm := funext fun j => (S j).fg m hm
  gf m hm := funext fun j => (S j).gf m hm
  gg m m' hm hm' := funext fun j => by
    rw [pi_comp_apply, (S j).gg m m' hm hm']
    split_ifs <;> rfl

end Pi

section App

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] [Preadditive 𝒟] {F G H : 𝒞 ⥤ 𝒟} {n : ℕ}

/-- **Explicit inverses in a functor category, from each object**: the inverse components of a
pointwise invertible map are natural. -/
def SumInvTo.ofApp {f : F ⟶ G} {g : ℕ → (F ⟶ H)}
    (S : ∀ M, SumInvTo (f.app M) (fun m => (g m).app M) n) : SumInvTo f g n where
  f' :=
    { app M := (S M).f'
      naturality M M' φ := by
        calc G.map φ ≫ (S M').f' = (S M).f' ≫ f.app M ≫ G.map φ ≫ (S M').f' := by
              rw [reassoc_of% (S M).ff]
          _ = (S M).f' ≫ F.map φ ≫ f.app M' ≫ (S M').f' := by rw [f.naturality_assoc]
          _ = (S M).f' ≫ F.map φ ≫ (f.app M' ≫ (S M').f' +
                ∑ m ∈ Finset.range n, (g m).app M' ≫ (S M').g' m) := by
              rw [Preadditive.comp_add, Preadditive.comp_add, Preadditive.comp_sum,
                Preadditive.comp_sum, Finset.sum_eq_zero, add_zero]
              intro m hm
              rw [(g m).naturality_assoc, reassoc_of% ((S M).fg m (Finset.mem_range.1 hm)),
                zero_comp]
          _ = (S M).f' ≫ F.map φ := by rw [(S M').total, Category.comp_id] }
  g' m :=
    { app M := if m < n then (S M).g' m else 0
      naturality M M' φ := by
        split_ifs with hm
        · calc H.map φ ≫ (S M').g' m =
                ∑ m' ∈ Finset.range n, (if m = m' then H.map φ ≫ (S M').g' m' else 0) := by
                rw [Finset.sum_ite_eq]
                simp [hm]
            _ = (S M).g' m ≫ F.map φ ≫ (f.app M' ≫ (S M').f' +
                  ∑ m' ∈ Finset.range n, (g m').app M' ≫ (S M').g' m') := by
                rw [Preadditive.comp_add, Preadditive.comp_add, Preadditive.comp_sum,
                  Preadditive.comp_sum, f.naturality_assoc, reassoc_of% ((S M).gf m hm),
                  zero_comp, zero_add]
                refine Finset.sum_congr rfl fun m' hm' => ?_
                rw [(g m').naturality_assoc,
                  reassoc_of% ((S M).gg m m' hm (Finset.mem_range.1 hm'))]
                split_ifs <;> simp
            _ = (S M).g' m ≫ F.map φ := by rw [(S M').total, Category.comp_id]
        · simp }
  total := by
    ext M
    simp only [NatTrans.app_add, NatTrans.app_sum, NatTrans.comp_app, NatTrans.id_app]
    refine Eq.trans ?_ (S M).total
    congr 1
    exact Finset.sum_congr rfl fun m hm => by simp [Finset.mem_range.1 hm]
  ff := by
    ext M
    exact (S M).ff
  fg m hm := by
    ext M
    exact (S M).fg m hm
  gf m hm := by
    ext M
    change (if m < n then (S M).g' m else 0) ≫ f.app M = 0
    simp only [hm, ↓reduceIte]
    exact (S M).gf m hm
  gg m m' hm hm' := by
    ext M
    change (if m < n then (S M).g' m else 0) ≫ (g m').app M = _
    simp only [hm, ↓reduceIte]
    rw [(S M).gg m m' hm hm']
    split_ifs <;> simp

/-- **Explicit inverses in a functor category, from each object**: the inverse components of a
pointwise invertible map are natural. -/
def SumInvFrom.ofApp {f : F ⟶ G} {g : ℕ → (H ⟶ G)}
    (S : ∀ M, SumInvFrom (f.app M) (fun m => (g m).app M) n) : SumInvFrom f g n where
  f' :=
    { app M := (S M).f'
      naturality M M' φ := by
        calc G.map φ ≫ (S M').f' = ((S M).f' ≫ f.app M +
              ∑ m ∈ Finset.range n, (S M).g' m ≫ (g m).app M) ≫ G.map φ ≫ (S M').f' := by
              rw [(S M).total, Category.id_comp]
          _ = (S M).f' ≫ F.map φ ≫ f.app M' ≫ (S M').f' := by
              rw [Preadditive.add_comp, Preadditive.sum_comp, Finset.sum_eq_zero, add_zero]
              · simp only [Category.assoc]
                rw [← f.naturality_assoc]
              · intro m hm
                simp only [Category.assoc]
                rw [← (g m).naturality_assoc, (S M').gf m (Finset.mem_range.1 hm), comp_zero,
                  comp_zero]
          _ = (S M).f' ≫ F.map φ := by rw [(S M').ff, Category.comp_id] }
  g' m :=
    { app M := if m < n then (S M).g' m else 0
      naturality M M' φ := by
        split_ifs with hm
        · calc G.map φ ≫ (S M').g' m = ((S M).f' ≫ f.app M +
                ∑ m' ∈ Finset.range n, (S M).g' m' ≫ (g m').app M) ≫ G.map φ ≫ (S M').g' m := by
                rw [(S M).total, Category.id_comp]
            _ = ∑ m' ∈ Finset.range n, (if m' = m then (S M).g' m' ≫ H.map φ else 0) := by
                rw [Preadditive.add_comp, Preadditive.sum_comp]
                simp only [Category.assoc]
                rw [← f.naturality_assoc, (S M').fg m hm, comp_zero, comp_zero, zero_add]
                refine Finset.sum_congr rfl fun m' hm' => ?_
                rw [← (g m').naturality_assoc, (S M').gg m' m (Finset.mem_range.1 hm') hm]
                split_ifs <;> simp
            _ = (S M).g' m ≫ H.map φ := by
                rw [Finset.sum_ite_eq']
                simp [hm]
        · simp }
  total := by
    ext M
    simp only [NatTrans.app_add, NatTrans.app_sum, NatTrans.comp_app, NatTrans.id_app]
    refine Eq.trans ?_ (S M).total
    congr 1
    exact Finset.sum_congr rfl fun m hm => by simp [Finset.mem_range.1 hm]
  ff := by
    ext M
    exact (S M).ff
  fg m hm := by
    ext M
    change f.app M ≫ (if m < n then (S M).g' m else 0) = 0
    simp only [hm, ↓reduceIte]
    exact (S M).fg m hm
  gf m hm := by
    ext M
    exact (S M).gf m hm
  gg m m' hm hm' := by
    ext M
    change (g m).app M ≫ (if m' < n then (S M).g' m' else 0) = _
    simp only [hm', ↓reduceIte]
    rw [(S M).gg m m' hm hm']
    split_ifs <;> simp

end App

section Zero

variable {D : Type*} [Category D] [Preadditive D] {X Y Z : D}

/-- With no summands, a map between zero objects has an explicit inverse. -/
def SumInvTo.ofIsZero (f : X ⟶ Y) (g : ℕ → (X ⟶ Z)) (hX : IsZero X) (hY : IsZero Y) :
    SumInvTo f g 0 where
  f' := 0
  g' _ := 0
  total := hX.eq_of_src _ _
  ff := hY.eq_of_src _ _
  fg _ hm := absurd hm (Nat.not_lt_zero _)
  gf _ hm := absurd hm (Nat.not_lt_zero _)
  gg _ _ hm := absurd hm (Nat.not_lt_zero _)

/-- If the source `Y` of `f : Y ⟶ X` is a zero object, an explicit inverse of
`(f, g 0, …, g (n-1))` is a decomposition of `X` into `n` copies of `Z`. -/
def SumInvFrom.ofIsZero {n : ℕ} (f : Y ⟶ X) (g : ℕ → (Z ⟶ X)) (hY : IsZero Y)
    (g' : ℕ → (X ⟶ Z)) (total : ∑ m ∈ Finset.range n, g' m ≫ g m = 𝟙 X)
    (gg : ∀ m m', m < n → m' < n → g m ≫ g' m' = if m = m' then 𝟙 Z else 0) :
    SumInvFrom f g n where
  f' := 0
  g' := g'
  total := by rw [zero_comp, zero_add, total]
  ff := hY.eq_of_src _ _
  fg _ _ := hY.eq_of_src _ _
  gf _ _ := comp_zero
  gg := gg

end Zero

/-- Functors preserve powers of endomorphisms. -/
theorem map_powComp {D D' : Type*} [Category D] [Category D'] (Φ : D ⥤ D') {X : D} (f : X ⟶ X) :
    ∀ n, Φ.map (powComp f n) = powComp (Φ.map f) n
  | 0 => by simp
  | n + 1 => by rw [powComp_succ, Φ.map_comp, map_powComp Φ f n, powComp_succ]

namespace LinearCat

open CategoryTheory.Bicategory

universe w v u

variable {k : Type w} [CommRing k]

/-- The inclusion of a hom category of `LinearCat k` into the functor category. -/
def homForget (C D : LinearCat.{w, v, u} k) : (C ⟶ D) ⥤ (C ⥤ D) :=
  ObjectProperty.ι (linearFunctor k C D)

instance (C D : LinearCat.{w, v, u} k) : (homForget C D).Full :=
  inferInstanceAs (ObjectProperty.ι (linearFunctor k C D)).Full

instance (C D : LinearCat.{w, v, u} k) : (homForget C D).Faithful :=
  inferInstanceAs (ObjectProperty.ι (linearFunctor k C D)).Faithful

instance (C D : LinearCat.{w, v, u} k) : (homForget C D).Additive :=
  inferInstanceAs (ObjectProperty.ι (linearFunctor k C D)).Additive

@[simp] theorem homForget_map {C D : LinearCat.{w, v, u} k} {F G : C ⟶ D} (η : F ⟶ G) :
    (homForget C D).map η = η.hom := rfl

theorem powComp_hom {C D : LinearCat.{w, v, u} k} {F : C ⟶ D} (η : F ⟶ F) (n : ℕ) :
    (powComp η n).hom = powComp η.hom n :=
  map_powComp (homForget C D) η n

/-- Rouquier's rightward crossing in `LinearCat k` is the usual mate of natural
transformations. -/
theorem sigma_hom {A B C : LinearCat.{w, v, u} k} {E₁ : A ⟶ B} {R₁ : B ⟶ A}
    {E₂ : B ⟶ C} {R₂ : C ⟶ B} (η : 𝟙 B ⟶ E₂ ≫ R₂)
    (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (κ : R₁ ≫ E₁ ⟶ 𝟙 B) :
    (RightwardCrossing.sigma η τ κ).hom =
      Functor.whiskerLeft (R₁.obj ⋙ E₁.obj) η.hom ≫
      Functor.whiskerRight (Functor.whiskerLeft R₁.obj τ.hom) R₂.obj ≫
      Functor.whiskerRight κ.hom (E₂.obj ⋙ R₂.obj) := by
  rw [RightwardCrossing.sigma_eq]
  ext X
  change 𝟙 _ ≫ η.hom.app (E₁.obj.obj (R₁.obj.obj X)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
      R₂.obj.map (τ.hom.app (R₁.obj.obj X)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
      R₂.obj.map (E₂.obj.map (κ.hom.app X)) ≫ 𝟙 _ =
    η.hom.app (E₁.obj.obj (R₁.obj.obj X)) ≫ R₂.obj.map (τ.hom.app (R₁.obj.obj X)) ≫
      R₂.obj.map (E₂.obj.map (κ.hom.app X))
  simp only [Category.id_comp, Category.comp_id]

end LinearCat

end Categorification.TwoRep
