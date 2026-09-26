/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Grading
import StringDiagrams.Bicategory
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.CategoryTheory.Idempotents.Biproducts
import Mathlib.CategoryTheory.Linear.Basic

/-!
# Grading shifts, direct sums and the Karoubi envelope of a graded presented 2-category

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1,
Definition 3.1 (1-morphisms `E_i 1_λ {t}` and their formal direct sums, 2-morphisms of degree
`t - t'` from `x{t}` to `y{t'}`), and §3.4, Definition 3.21 (TeX label `subsec_Karoubi`:
`U̇(λ, λ') = Kar(U(λ, λ'))`).

Let `P` be a presentation of an even signature (so that `P.Bicat` is a strict bicategory; its
2-morphisms have all degrees) with a grading `deg : S.Gen → ℤ`. For objects `l m : P.Bicat` we
build, generically:

* `GrObj P deg l m`: pairs `x{t}` of a 1-morphism `x : l ⟶ m` and a shift `t ∈ ℤ`; morphisms
  `x{t} ⟶ y{t'}` are the 2-morphisms of degree `t - t'` (`P.homDeg deg`). This is a `k`-linear
  category (`grCategory`, `grPreadditive`, `grLinear`).
* `UHom P deg l m = Mat_ (GrObj P deg l m)`: formal finite direct sums (matrices of degree-zero
  morphisms). With `P` the presentation of KL III's `U` this is the Hom category `U(λ, λ')` of
  Definition 3.1 (the presented bicategory `P.Bicat` itself has the 2-morphisms of all
  degrees, i.e. `HOM_U`, but no shifts and no sums).
* `UDotHom P deg l m = Karoubi (UHom P deg l m)`: the Hom category `U̇(λ, λ')` of Definition 3.21.
  It is `k`-linear (`karoubiLinear`, which Mathlib does not provide), additive (finite
  biproducts, `Karoubi.karoubi_hasFiniteBiproducts`) and idempotent complete.
* `incl P deg : GrObj P deg l m ⥤ UDotHom P deg l m`, fully faithful and additive: a
  homogeneous 2-morphism of degree `t - t'` is a morphism `x{t} ⟶ y{t'}` of `U̇`
  (`homOf`, with `homOf_comp`, `homOf_id`, `homOf_add`, `homOf_sum`, …).
* Composition with 1-morphisms: `wLDot a : UDotHom l m ⥤ UDotHom j m` (left whiskering by
  `a : j ⟶ l`) and `wRDot b : UDotHom l m ⥤ UDotHom l n` (right whiskering by `b : m ⟶ n`),
  additive and `k`-linear, induced by the whiskerings of `P.Bicat` (which preserve degrees);
  in particular composition with `E_i` and `F_i`.

Generic tools:

* `Categorification.matLinear`, `Categorification.karoubiLinear`, `mapKaroubi`: `k`-linear
  structures on `Mat_ C` and `Karoubi C`, and the functor `Karoubi C ⥤ Karoubi D` induced by
  a functor `C ⥤ D`.
* `SumDecomp A B Cs` and `SumDecomp.iso : A ≅ B ⊞ ⨁ Cs`: a decomposition of `A` given by maps
  `a₀ : A ⟶ B`, `b₀ : B ⟶ A`, `a_s : A ⟶ C_s`, `b_s : C_s ⟶ A` with
  `a₀ b₀ + ∑ a_s b_s = 1`, `b₀ a₀ = 1`, `b_s a₀ = 0`, `b_s a_t = δ_{st}`; the remaining relation
  `b₀ a_s = 0` is automatic (`SumDecomp.b0_a`). `SumDecomp.map` transports it along additive
  functors (e.g. whiskerings).

The horizontal composition `U̇(λ, λ') × U̇(λ', λ'') ⥤ U̇(λ, λ'')` is in
`Categorification.Diagrams.KL3.KaroubiHcomp`; the 2-categorical coherence of `U̇` is not
formalized.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits

universe w v u₀ u₁ u₂

/-! ## Linear structures on matrix categories and Karoubi envelopes -/

section LinearEnvelopes

variable (k : Type*) [CommRing k] {C : Type*} [Category C] [Preadditive C] [Linear k C]

/-- The `k`-module structure on the morphisms of `Mat_ C` (entrywise). -/
instance matHomModule (M N : Mat_ C) : Module k (M ⟶ N) := by
  change Module k (∀ i j, M.X i ⟶ N.X j)
  infer_instance

@[simp] theorem mat_smul_apply {M N : Mat_ C} (r : k) (f : M ⟶ N) (i : M.ι) (j : N.ι) :
    (r • f) i j = r • f i j := rfl

/-- `Mat_ C` is `k`-linear if `C` is. -/
instance matLinear : Linear k (Mat_ C) where
  homModule := matHomModule k
  smul_comp M N K r f g := by
    ext i j
    simp [Finset.smul_sum, Linear.smul_comp]
  comp_smul M N K f r g := by
    ext i j
    simp [Finset.smul_sum, Linear.comp_smul]

/-- Scalar multiplication of morphisms of the Karoubi envelope. -/
instance karoubiHomSMul {P Q : Karoubi C} : SMul k (P ⟶ Q) where
  smul r f := ⟨r • f.f, by rw [Linear.smul_comp, Linear.comp_smul, ← f.comm]⟩

@[simp] theorem karoubi_smul_f {P Q : Karoubi C} (r : k) (f : P ⟶ Q) : (r • f).f = r • f.f :=
  rfl

/-- The `k`-module structure on the morphisms of `Karoubi C`. -/
instance karoubiHomModule (P Q : Karoubi C) : Module k (P ⟶ Q) :=
  Function.Injective.module k (Karoubi.inclusionHom P Q) (fun _ _ h => Karoubi.hom_ext _ _ h)
    (fun _ _ => rfl)

/-- The Karoubi envelope of a `k`-linear category is `k`-linear. -/
instance karoubiLinear : Linear k (Karoubi C) where
  homModule := karoubiHomModule k
  smul_comp P Q R r f g := Karoubi.hom_ext _ _ (by simp [Linear.smul_comp])
  comp_smul P Q R f r g := Karoubi.hom_ext _ _ (by simp [Linear.comp_smul])

instance toKaroubi_linear : (toKaroubi C).Linear k where
  map_smul _ _ := rfl

variable {k} {D : Type*} [Category D]

/-- The functor between Karoubi envelopes induced by a functor. -/
@[simps]
def mapKaroubi (F : C ⥤ D) : Karoubi C ⥤ Karoubi D where
  obj P := ⟨F.obj P.X, F.map P.p, by rw [← F.map_comp, P.idem]⟩
  map {P Q} f := ⟨F.map f.f, by
    show F.map f.f = F.map P.p ≫ F.map f.f ≫ F.map Q.p
    rw [← F.map_comp, ← F.map_comp, ← f.comm]⟩
  map_id _ := Karoubi.hom_ext _ _ rfl
  map_comp _ _ := Karoubi.hom_ext _ _ (F.map_comp _ _)

instance mapKaroubi_additive [Preadditive D] (F : C ⥤ D) [F.Additive] :
    (mapKaroubi F).Additive where
  map_add := Karoubi.hom_ext _ _ (F.map_add)

instance mapKaroubi_linear [Preadditive D] [Linear k D] (F : C ⥤ D) [F.Additive] [F.Linear k] :
    (mapKaroubi F).Linear k where
  map_smul _ _ := Karoubi.hom_ext _ _ (F.map_smul _ _)

variable {D : Type*} [Category D] [Preadditive D] [Linear k D]

instance mapMat_additive {C : Type u₁} [Category.{v} C] [Preadditive C] {D : Type u₂}
    [Category.{v} D] [Preadditive D] (F : C ⥤ D) [F.Additive] : F.mapMat_.Additive where
  map_add := by
    intros
    ext
    simp

instance mapMat_linear {C : Type u₁} [Category.{v} C] [Preadditive C] [Linear k C] {D : Type u₂}
    [Category.{v} D] [Preadditive D] [Linear k D] (F : C ⥤ D) [F.Additive] [F.Linear k] :
    F.mapMat_.Linear k where
  map_smul _ _ := by
    ext
    simp

end LinearEnvelopes

/-! ## Decompositions into direct sums -/

section Decomp

variable {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [HasFiniteBiproducts 𝒞]
  [HasBinaryBiproducts 𝒞]

/-- Data exhibiting `A ≅ B ⊕ ⨁_s C_s`: maps `a₀ : A ⟶ B`, `b₀ : B ⟶ A`, `a_s : A ⟶ C_s`,
`b_s : C_s ⟶ A` with `a₀ b₀ + ∑_s a_s b_s = 1_A` (composition in diagrammatic order),
`b₀ a₀ = 1_B`, `b_s a₀ = 0` and `b_s a_t = δ_{st}`. -/
structure SumDecomp (A B : 𝒞) {ι : Type} [Fintype ι] [DecidableEq ι] (Cs : ι → 𝒞) where
  /-- The component `A ⟶ B`. -/
  a0 : A ⟶ B
  /-- The component `B ⟶ A`. -/
  b0 : B ⟶ A
  /-- The components `A ⟶ C_s`. -/
  a : ∀ s, A ⟶ Cs s
  /-- The components `C_s ⟶ A`. -/
  b : ∀ s, Cs s ⟶ A
  total : a0 ≫ b0 + ∑ s, a s ≫ b s = 𝟙 A
  b0_a0 : b0 ≫ a0 = 𝟙 B
  b_a0 : ∀ s, b s ≫ a0 = 0
  b_a_self : ∀ s, b s ≫ a s = 𝟙 _
  b_a_ne : ∀ s t, s ≠ t → b s ≫ a t = 0

namespace SumDecomp

variable {A B : 𝒞} {ι : Type} [Fintype ι] [DecidableEq ι] {Cs : ι → 𝒞}

omit [HasFiniteBiproducts 𝒞] [HasBinaryBiproducts 𝒞] in
/-- The relation `b₀ a_t = 0` follows from the others (the endomorphism `b ≫ a` of
`B ⊕ ⨁ C_s` is an idempotent which is the identity up to the block `b₀ a_t`). -/
theorem b0_a (D : SumDecomp A B Cs) (t : ι) : D.b0 ≫ D.a t = 0 := by
  have h := congrArg (fun f => D.b0 ≫ f ≫ D.a t) D.total
  simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
    Preadditive.comp_sum, Category.assoc, Category.id_comp] at h
  have hs : ∀ s ∈ Finset.univ, D.b0 ≫ D.a s ≫ D.b s ≫ D.a t =
      if s = t then D.b0 ≫ D.a t else 0 := by
    intro s _
    split_ifs with hst
    · subst hst; rw [D.b_a_self, Category.comp_id]
    · rw [D.b_a_ne s t hst, Limits.comp_zero, Limits.comp_zero]
  rw [Finset.sum_congr rfl hs, Finset.sum_ite_eq' Finset.univ t, if_pos (Finset.mem_univ _),
    ← Category.assoc D.b0 D.a0, D.b0_a0, Category.id_comp] at h
  have h2 : D.b0 ≫ D.a t + D.b0 ≫ D.a t - D.b0 ≫ D.a t = 0 := by rw [h, sub_self]
  rwa [add_sub_cancel_right] at h2

/-- **The isomorphism `A ≅ B ⊕ ⨁_s C_s`** given by a `SumDecomp`. -/
def iso (D : SumDecomp A B Cs) : A ≅ B ⊞ ⨁ Cs where
  hom := biprod.lift D.a0 (biproduct.lift D.a)
  inv := biprod.desc D.b0 (biproduct.desc D.b)
  hom_inv_id := by
    rw [biprod.lift_desc, biproduct.lift_desc, D.total]
  inv_hom_id := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Category.comp_id]
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, D.b0_a0, biprod.inl_fst]
      · rw [Category.assoc, biprod.lift_snd, biprod.inl_snd]
        apply biproduct.hom_ext
        intro t
        rw [Category.assoc, biproduct.lift_π, D.b0_a, Limits.zero_comp]
    · rw [biprod.inr_desc_assoc, Category.comp_id]
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, biprod.inr_fst]
        apply biproduct.hom_ext'
        intro s
        rw [biproduct.ι_desc_assoc, D.b_a0, Limits.comp_zero]
      · rw [Category.assoc, biprod.lift_snd, biprod.inr_snd]
        apply biproduct.hom_ext'
        intro s
        apply biproduct.hom_ext
        intro t
        rw [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.comp_id,
          biproduct.ι_π]
        split_ifs with hst
        · subst hst; rw [D.b_a_self, eqToHom_refl]
        · exact D.b_a_ne s t hst

/-- Transport of a decomposition along an additive functor. -/
@[simps]
def map {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟] (D : SumDecomp A B Cs) (F : 𝒞 ⥤ 𝒟)
    [F.Additive] : SumDecomp (F.obj A) (F.obj B) (fun s => F.obj (Cs s)) where
  a0 := F.map D.a0
  b0 := F.map D.b0
  a s := F.map (D.a s)
  b s := F.map (D.b s)
  total := by
    rw [← F.map_id, ← D.total, F.map_add, F.map_comp, F.map_sum]
    simp only [F.map_comp]
  b0_a0 := by rw [← F.map_comp, D.b0_a0, F.map_id]
  b_a0 s := by rw [← F.map_comp, D.b_a0, F.map_zero]
  b_a_self s := by rw [← F.map_comp, D.b_a_self, F.map_id]
  b_a_ne s t h := by rw [← F.map_comp, D.b_a_ne s t h, F.map_zero]

end SumDecomp

/-- Data exhibiting `A ≅ ⨁_s C_s`: maps `a_s : A ⟶ C_s`, `b_s : C_s ⟶ A` with
`∑_s a_s b_s = 1_A` and `b_s a_t = δ_{st}`. -/
structure OrthDecomp (A : 𝒞) {ι : Type} [Fintype ι] [DecidableEq ι] (Cs : ι → 𝒞) where
  /-- The components `A ⟶ C_s`. -/
  a : ∀ s, A ⟶ Cs s
  /-- The components `C_s ⟶ A`. -/
  b : ∀ s, Cs s ⟶ A
  total : ∑ s, a s ≫ b s = 𝟙 A
  b_a_self : ∀ s, b s ≫ a s = 𝟙 _
  b_a_ne : ∀ s t, s ≠ t → b s ≫ a t = 0

/-- The isomorphism `A ≅ ⨁_s C_s` given by an `OrthDecomp`. -/
def OrthDecomp.iso {A : 𝒞} {ι : Type} [Fintype ι] [DecidableEq ι] {Cs : ι → 𝒞}
    (D : OrthDecomp A Cs) : A ≅ ⨁ Cs where
  hom := biproduct.lift D.a
  inv := biproduct.desc D.b
  hom_inv_id := by rw [biproduct.lift_desc, D.total]
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro s
    apply biproduct.hom_ext
    intro t
    rw [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.comp_id,
      biproduct.ι_π]
    split_ifs with hst
    · subst hst; rw [D.b_a_self, eqToHom_refl]
    · exact D.b_a_ne s t hst

/-- **An isomorphism of direct sums given by matrices** `F : ⨁ P ⟶ ⨁ Q`, `G : ⨁ Q ⟶ ⨁ P`
whose products are the identity matrices. -/
def matrixIso {M N : Type} [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N] {P : M → 𝒞}
    {Q : N → 𝒞} (F : ∀ m n, P m ⟶ Q n) (G : ∀ n m, Q n ⟶ P m)
    (hFG : ∀ m m', ∑ n, F m n ≫ G n m' = if h : m = m' then eqToHom (congrArg P h) else 0)
    (hGF : ∀ n n', ∑ m, G n m ≫ F m n' = if h : n = n' then eqToHom (congrArg Q h) else 0) :
    ⨁ P ≅ ⨁ Q where
  hom := biproduct.matrix F
  inv := biproduct.matrix G
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro m
    apply biproduct.hom_ext
    intro m'
    rw [biproduct.ι_matrix_assoc, Category.assoc, biproduct.matrix_π, biproduct.lift_desc,
      Category.comp_id, biproduct.ι_π, hFG]
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro n
    apply biproduct.hom_ext
    intro n'
    rw [biproduct.ι_matrix_assoc, Category.assoc, biproduct.matrix_π, biproduct.lift_desc,
      Category.comp_id, biproduct.ι_π, hGF]

end Decomp

/-! ## The graded Hom categories of a presented 2-category -/

namespace GradedBicat

open StringDiagrams Presentation

variable {S : Signature.{u₀, u₁, u₂}} {k : Type w} [CommRing k]
  (P : Presentation.{w, v} S k) (deg : S.Gen → ℤ)

/-- An object `x{t}` of `U(l, m)` before direct sums: a 1-morphism `x : l ⟶ m` of `P.Bicat`
together with a grading shift `t`. -/
@[ext, nolint unusedArguments]
structure GrObj (P : Presentation.{w, v} S k) (deg : S.Gen → ℤ) (l m : P.Bicat) where
  /-- The underlying 1-morphism. -/
  x : Bicat.Hom l m
  /-- The grading shift. -/
  t : ℤ

variable {P deg}

theorem mem_homDeg_of_eq {a b : Obj S} {f : P.obj a ⟶ P.obj b} {d d' : ℤ}
    (h : f ∈ P.homDeg deg a b d) (e : d = d') : f ∈ P.homDeg deg a b d' :=
  e ▸ h

theorem eqToHom_mem_homDeg {a b : Obj S} (h : a = b) :
    (eqToHom (congrArg P.obj h) : P.obj a ⟶ P.obj b) ∈ P.homDeg deg a b 0 := by
  subst h
  simpa using P.id_mem_homDeg deg a

theorem wL_mem_homDeg (a : Obj S) {b b' : Obj S} {f : P.obj b ⟶ P.obj b'} {d : ℤ}
    (hf : f ∈ P.homDeg deg b b' d) : P.wL a f ∈ P.homDeg deg _ _ d := by
  have := comp_mem_homDeg (eqToHom_mem_homDeg (P := P) (deg := deg) (Obj.tensor_eq_whisker_nil a b))
    (comp_mem_homDeg (whisk_mem_homDeg hf a [])
      (eqToHom_mem_homDeg (P := P) (deg := deg) (Obj.tensor_eq_whisker_nil a b').symm))
  rw [zero_add, add_zero] at this
  exact this

theorem wRAt_mem_homDeg {r : S.Region} {a a' : Obj S} {f : P.obj a ⟶ P.obj a'} {d : ℤ}
    (hf : f ∈ P.homDeg deg a a' d) (b : Obj S) (ha : a.start = r) (ha' : a'.start = r) :
    P.wRAt r f b ha ha' ∈ P.homDeg deg _ _ d := by
  have := comp_mem_homDeg
    (eqToHom_mem_homDeg (P := P) (deg := deg) (Obj.tensor_eq_whisker_nil_of_start b ha))
    (comp_mem_homDeg (whisk_mem_homDeg hf (Obj.nil r) b.word)
      (eqToHom_mem_homDeg (P := P) (deg := deg) (Obj.tensor_eq_whisker_nil_of_start b ha').symm))
  rw [zero_add, add_zero] at this
  exact this

variable (P deg)

/-- The morphisms `x{t} ⟶ y{t'}`: the 2-morphisms `x ⟶ y` of degree `t - t'`. -/
def GrObj.Hom {l m : P.Bicat} (X Y : GrObj P deg l m) : Type _ :=
  P.homDeg deg X.x.obj Y.x.obj (X.t - Y.t)

instance grCategory (l m : P.Bicat) : Category (GrObj P deg l m) where
  Hom X Y := GrObj.Hom P deg X Y
  id X := ⟨𝟙 _, mem_homDeg_of_eq (P.id_mem_homDeg deg _) (sub_self _).symm⟩
  comp f g := ⟨f.1 ≫ g.1, mem_homDeg_of_eq (comp_mem_homDeg f.2 g.2) (by ring)⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

variable {P deg} {l m : P.Bicat}

@[ext] theorem GrObj.hom_ext {X Y : GrObj P deg l m} {f g : X ⟶ Y} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

@[simp] theorem GrObj.id_val (X : GrObj P deg l m) : (𝟙 X : X ⟶ X).1 = 𝟙 (P.obj X.x.obj) := rfl

@[simp] theorem GrObj.comp_val {X Y Z : GrObj P deg l m} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

variable (P deg l m)

instance grPreadditive : Preadditive (GrObj P deg l m) where
  homGroup X Y := inferInstanceAs (AddCommGroup (P.homDeg deg X.x.obj Y.x.obj (X.t - Y.t)))
  add_comp _ _ _ f f' g := Subtype.ext (Preadditive.add_comp _ _ _ f.1 f'.1 g.1)
  comp_add _ _ _ f g g' := Subtype.ext (Preadditive.comp_add _ _ _ f.1 g.1 g'.1)

instance grLinear : Linear k (GrObj P deg l m) where
  homModule X Y := inferInstanceAs (Module k (P.homDeg deg X.x.obj Y.x.obj (X.t - Y.t)))
  smul_comp _ _ _ r f g := Subtype.ext (Linear.smul_comp _ _ _ r f.1 g.1)
  comp_smul _ _ _ f r g := Subtype.ext (Linear.comp_smul _ _ _ f.1 r g.1)

variable {P deg l m}

@[simp] theorem GrObj.add_val {X Y : GrObj P deg l m} (f g : X ⟶ Y) : (f + g).1 = f.1 + g.1 :=
  rfl

@[simp] theorem GrObj.neg_val {X Y : GrObj P deg l m} (f : X ⟶ Y) : (-f).1 = -f.1 := rfl

@[simp] theorem GrObj.zero_val {X Y : GrObj P deg l m} : (0 : X ⟶ Y).1 = 0 := rfl

@[simp] theorem GrObj.smul_val {X Y : GrObj P deg l m} (r : k) (f : X ⟶ Y) : (r • f).1 = r • f.1 :=
  rfl

@[simp] theorem GrObj.sum_val {X Y : GrObj P deg l m} {ι : Type*} (s : Finset ι)
    (f : ι → (X ⟶ Y)) : (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 :=
  Submodule.coe_sum _ _ _

variable (P deg l m)

/-- **The Hom category `U(l, m)`** (KL III Definition 3.1): formal finite direct sums of shifted
1-morphisms `x{t}`, with matrices of degree-zero 2-morphisms (`t - t'` for `x{t} ⟶ y{t'}`). -/
abbrev UHom : Type _ := Mat_ (GrObj P deg l m)

/-- **The Hom category `U̇(l, m)`** (KL III Definition 3.21): the Karoubi envelope of `U(l, m)`. -/
abbrev UDotHom : Type _ := Karoubi (UHom P deg l m)

example : Preadditive (UDotHom P deg l m) := inferInstance
example : Linear k (UDotHom P deg l m) := inferInstance
example : HasFiniteBiproducts (UDotHom P deg l m) := inferInstance

instance : HasBinaryBiproducts (UDotHom P deg l m) := hasBinaryBiproducts_of_finite_biproducts _
example : IsIdempotentComplete (UDotHom P deg l m) := inferInstance

/-- The inclusion `x{t} ↦ x{t}` of shifted 1-morphisms into `U̇(l, m)` (fully faithful). -/
abbrev incl : GrObj P deg l m ⥤ UDotHom P deg l m :=
  Mat_.embedding (GrObj P deg l m) ⋙ toKaroubi (UHom P deg l m)

example : (incl P deg l m).Full := inferInstance
example : (incl P deg l m).Faithful := inferInstance
example : (incl P deg l m).Additive := inferInstance

instance incl_linear : (incl P deg l m).Linear k where
  map_smul _ _ := rfl

variable {P deg l m}

/-- The object `x{t}` of `U̇(l, m)`. -/
abbrev objOf (x : Bicat.Hom l m) (t : ℤ) : UDotHom P deg l m := (incl P deg l m).obj ⟨x, t⟩

/-- A homogeneous 2-morphism `f : x ⟶ y` of degree `t - t'`, as a morphism `x{t} ⟶ y{t'}`
of `U̇(l, m)`. -/
abbrev homOf {x y : Bicat.Hom l m} {t t' : ℤ} (f : P.obj x.obj ⟶ P.obj y.obj)
    (hf : f ∈ P.homDeg deg x.obj y.obj (t - t')) :
    (objOf x t : UDotHom P deg l m) ⟶ objOf y t' :=
  (incl P deg l m).map (X := ⟨x, t⟩) (Y := ⟨y, t'⟩) ⟨f, hf⟩

section HomOf

variable {x y z : Bicat.Hom l m} {t t' t'' : ℤ}

theorem homOf_comp (f : P.obj x.obj ⟶ P.obj y.obj) (g : P.obj y.obj ⟶ P.obj z.obj)
    (hf : f ∈ P.homDeg deg x.obj y.obj (t - t')) (hg : g ∈ P.homDeg deg y.obj z.obj (t' - t'')) :
    (homOf f hf : (objOf x t : UDotHom P deg l m) ⟶ _) ≫ homOf g hg =
      homOf (f ≫ g) (mem_homDeg_of_eq (comp_mem_homDeg hf hg) (by ring)) :=
  ((incl P deg l m).map_comp _ _).symm

theorem homOf_id : (homOf (𝟙 (P.obj x.obj)) (mem_homDeg_of_eq (P.id_mem_homDeg deg _)
    (sub_self t).symm) : (objOf x t : UDotHom P deg l m) ⟶ _) = 𝟙 _ :=
  (incl P deg l m).map_id _

theorem homOf_congr {f g : P.obj x.obj ⟶ P.obj y.obj} (e : f = g)
    (hf : f ∈ P.homDeg deg x.obj y.obj (t - t')) (hg : g ∈ P.homDeg deg x.obj y.obj (t - t')) :
    (homOf f hf : (objOf x t : UDotHom P deg l m) ⟶ _) = homOf g hg := by
  subst e; rfl

theorem homOf_eq_id {f : P.obj x.obj ⟶ P.obj x.obj} (e : f = 𝟙 _)
    (hf : f ∈ P.homDeg deg x.obj x.obj (t - t)) :
    (homOf f hf : (objOf x t : UDotHom P deg l m) ⟶ _) = 𝟙 _ := by
  subst e; exact homOf_id

theorem homOf_eq_zero {f : P.obj x.obj ⟶ P.obj y.obj} (e : f = 0)
    (hf : f ∈ P.homDeg deg x.obj y.obj (t - t')) :
    (homOf f hf : (objOf x t : UDotHom P deg l m) ⟶ _) = 0 := by
  subst e; exact (incl P deg l m).map_zero _ _

theorem homOf_add (f g : P.obj x.obj ⟶ P.obj y.obj) (hf : f ∈ P.homDeg deg x.obj y.obj (t - t'))
    (hg : g ∈ P.homDeg deg x.obj y.obj (t - t')) :
    (homOf (f + g) (Submodule.add_mem _ hf hg) : (objOf x t : UDotHom P deg l m) ⟶ _) =
      homOf f hf + homOf g hg := by
  rw [← Functor.map_add]; rfl

theorem homOf_neg (f : P.obj x.obj ⟶ P.obj y.obj) (hf : f ∈ P.homDeg deg x.obj y.obj (t - t')) :
    (homOf (-f) (Submodule.neg_mem _ hf) : (objOf x t : UDotHom P deg l m) ⟶ _) =
      -homOf f hf := by
  rw [← Functor.map_neg]; rfl

theorem homOf_smul (r : k) (f : P.obj x.obj ⟶ P.obj y.obj)
    (hf : f ∈ P.homDeg deg x.obj y.obj (t - t')) :
    (homOf (r • f) (Submodule.smul_mem _ r hf) : (objOf x t : UDotHom P deg l m) ⟶ _) =
      r • homOf f hf := by
  rw [← Functor.map_smul]; rfl

theorem homOf_sum {ι : Type*} (s : Finset ι) (f : ι → (P.obj x.obj ⟶ P.obj y.obj))
    (hf : ∀ i ∈ s, f i ∈ P.homDeg deg x.obj y.obj (t - t')) :
    (homOf (∑ i ∈ s, f i) (Submodule.sum_mem _ hf) : (objOf x t : UDotHom P deg l m) ⟶ _) =
      ∑ i ∈ s.attach, homOf (f i.1) (hf i.1 i.2) := by
  have e : (⟨∑ i ∈ s, f i, Submodule.sum_mem _ hf⟩ : (⟨x, t⟩ : GrObj P deg l m) ⟶ ⟨y, t'⟩) =
      ∑ i ∈ s.attach, ⟨f i.1, hf i.1 i.2⟩ :=
    GrObj.hom_ext (by rw [GrObj.sum_val]; exact (Finset.sum_attach s f).symm)
  rw [homOf, e, Functor.map_sum]

theorem sum_homOf {ι : Type*} (s : Finset ι) (f : ι → (P.obj x.obj ⟶ P.obj y.obj))
    (hf : ∀ i, f i ∈ P.homDeg deg x.obj y.obj (t - t')) :
    ∑ i ∈ s, (homOf (f i) (hf i) : (objOf x t : UDotHom P deg l m) ⟶ _) =
      homOf (∑ i ∈ s, f i) (Submodule.sum_mem _ fun i _ => hf i) := by
  have e : (⟨∑ i ∈ s, f i, Submodule.sum_mem _ fun i _ => hf i⟩ :
      (⟨x, t⟩ : GrObj P deg l m) ⟶ ⟨y, t'⟩) = ∑ i ∈ s, ⟨f i, hf i⟩ :=
    GrObj.hom_ext (by rw [GrObj.sum_val])
  rw [homOf, e, Functor.map_sum]

theorem add_homOf (f g : P.obj x.obj ⟶ P.obj y.obj) (hf : f ∈ P.homDeg deg x.obj y.obj (t - t'))
    (hg : g ∈ P.homDeg deg x.obj y.obj (t - t')) :
    (homOf f hf : (objOf x t : UDotHom P deg l m) ⟶ _) + homOf g hg =
      homOf (f + g) (Submodule.add_mem _ hf hg) :=
  (homOf_add f g hf hg).symm

end HomOf

/-- An idempotent 2-morphism `e` of degree `0` on `x` gives the object `(x{t}, e)` of `U̇(l, m)`
(the image of `e`). -/
def idemObj (x : Bicat.Hom l m) (t : ℤ) (e : P.obj x.obj ⟶ P.obj x.obj)
    (he : e ∈ P.homDeg deg x.obj x.obj 0) (hee : e ≫ e = e) : UDotHom P deg l m where
  X := (Mat_.embedding _).obj ⟨x, t⟩
  p := (Mat_.embedding (GrObj P deg l m)).map (X := ⟨x, t⟩) (Y := ⟨x, t⟩)
    ⟨e, mem_homDeg_of_eq he (sub_self t).symm⟩
  idem := by
    rw [← Functor.map_comp]
    congr 1
    exact Subtype.ext hee

section IdemHom

variable {x y z : Bicat.Hom l m} {t t' t'' : ℤ} {e : P.obj x.obj ⟶ P.obj x.obj}
  {e' : P.obj y.obj ⟶ P.obj y.obj} {e'' : P.obj z.obj ⟶ P.obj z.obj}
  {he : e ∈ P.homDeg deg x.obj x.obj 0} {he' : e' ∈ P.homDeg deg y.obj y.obj 0}
  {he'' : e'' ∈ P.homDeg deg z.obj z.obj 0} {hee : e ≫ e = e} {hee' : e' ≫ e' = e'}
  {hee'' : e'' ≫ e'' = e''}

theorem left_absorb {X Y : P.Presented} {e : X ⟶ X} {e' : Y ⟶ Y} {f : X ⟶ Y}
    (hc : f = e ≫ f ≫ e') (hee : e ≫ e = e) : e ≫ f = f := by
  rw [hc, ← Category.assoc, hee]

theorem right_absorb {X Y : P.Presented} {e : X ⟶ X} {e' : Y ⟶ Y} {f : X ⟶ Y}
    (hc : f = e ≫ f ≫ e') (hee' : e' ≫ e' = e') : f ≫ e' = f := by
  rw [hc]; simp only [Category.assoc, hee']

/-- A homogeneous 2-morphism `f` of degree `t - t'` with `f = e f e'` as a morphism
`(x{t}, e) ⟶ (y{t'}, e')` of `U̇(l, m)`. -/
def idemHom (f : P.obj x.obj ⟶ P.obj y.obj) (hf : f ∈ P.homDeg deg x.obj y.obj (t - t'))
    (hc : f = e ≫ f ≫ e') : idemObj x t e he hee ⟶ idemObj y t' e' he' hee' where
  f := (Mat_.embedding (GrObj P deg l m)).map (X := ⟨x, t⟩) (Y := ⟨y, t'⟩) ⟨f, hf⟩
  comm := by
    show _ = (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact Subtype.ext hc

theorem idemHom_comp (f : P.obj x.obj ⟶ P.obj y.obj) (g : P.obj y.obj ⟶ P.obj z.obj)
    (hf : f ∈ P.homDeg deg x.obj y.obj (t - t')) (hg : g ∈ P.homDeg deg y.obj z.obj (t' - t''))
    (hcf : f = e ≫ f ≫ e') (hcg : g = e' ≫ g ≫ e'') :
    (idemHom (he := he) (hee := hee) (he' := he') (hee' := hee') f hf hcf) ≫
        (idemHom (he := he') (hee := hee') (he' := he'') (hee' := hee'') g hg hcg) =
      idemHom (f ≫ g) (mem_homDeg_of_eq (comp_mem_homDeg hf hg) (by ring))
        (by rw [Category.assoc, right_absorb hcg hee'', ← Category.assoc,
          left_absorb hcf hee]) :=
  Karoubi.hom_ext _ _ ((Mat_.embedding _).map_comp _ _).symm

theorem idemHom_self :
    (idemHom (he := he) (hee := hee) (he' := he) (hee' := hee) (t := t) (t' := t) e
      (mem_homDeg_of_eq he (sub_self t).symm) (by rw [hee, hee])) = 𝟙 _ :=
  Karoubi.hom_ext _ _ rfl

theorem idemHom_congr {f g : P.obj x.obj ⟶ P.obj y.obj} (h : f = g)
    (hf : f ∈ P.homDeg deg x.obj y.obj (t - t')) (hg : g ∈ P.homDeg deg x.obj y.obj (t - t'))
    (hcf : f = e ≫ f ≫ e') (hcg : g = e ≫ g ≫ e') :
    (idemHom (he := he) (hee := hee) (he' := he') (hee' := hee') f hf hcf) = idemHom g hg hcg := by
  subst h; rfl

theorem idemHom_eq_id {f : P.obj x.obj ⟶ P.obj x.obj} (h : f = e)
    (hf : f ∈ P.homDeg deg x.obj x.obj (t - t)) (hcf : f = e ≫ f ≫ e) :
    (idemHom (he := he) (hee := hee) (he' := he) (hee' := hee) f hf hcf) = 𝟙 _ := by
  subst h; exact idemHom_self

theorem idemHom_eq_zero {f : P.obj x.obj ⟶ P.obj y.obj} (h : f = 0)
    (hf : f ∈ P.homDeg deg x.obj y.obj (t - t')) (hcf : f = e ≫ f ≫ e') :
    (idemHom (he := he) (hee := hee) (he' := he') (hee' := hee') f hf hcf) = 0 := by
  subst h
  exact Karoubi.hom_ext _ _ ((Mat_.embedding _).map_zero _ _)

theorem sum_idemHom {ι : Type*} (s : Finset ι) (f : ι → (P.obj x.obj ⟶ P.obj y.obj))
    (hf : ∀ i, f i ∈ P.homDeg deg x.obj y.obj (t - t')) (hc : ∀ i, f i = e ≫ f i ≫ e') :
    ∑ i ∈ s, (idemHom (he := he) (hee := hee) (he' := he') (hee' := hee') (f i) (hf i) (hc i)) =
      idemHom (∑ i ∈ s, f i) (Submodule.sum_mem _ fun i _ => hf i)
        (by simp only [Preadditive.sum_comp, Preadditive.comp_sum]
            exact Finset.sum_congr rfl fun i _ => hc i) := by
  apply Karoubi.hom_ext
  rw [Karoubi.sum_hom]
  show ∑ i ∈ s, (Mat_.embedding _).map _ = (Mat_.embedding _).map _
  rw [← Functor.map_sum]
  congr 1
  exact GrObj.hom_ext (by rw [GrObj.sum_val])

theorem idemObj_congr {e₁ e₂ : P.obj x.obj ⟶ P.obj x.obj} (h : e₁ = e₂)
    (he₁ : e₁ ∈ P.homDeg deg x.obj x.obj 0) (he₂ : e₂ ∈ P.homDeg deg x.obj x.obj 0)
    (hee₁ : e₁ ≫ e₁ = e₁) (hee₂ : e₂ ≫ e₂ = e₂) :
    idemObj x t e₁ he₁ hee₁ = idemObj x t e₂ he₂ hee₂ := by
  subst h; rfl

/-- The object `(x{t}, 1)` is `x{t}`. -/
theorem idemObj_id (he : 𝟙 (P.obj x.obj) ∈ P.homDeg deg x.obj x.obj 0)
    (hee : 𝟙 (P.obj x.obj) ≫ 𝟙 (P.obj x.obj) = 𝟙 _) :
    idemObj x t (𝟙 _) he hee = (objOf x t : UDotHom P deg l m) := by
  show Karoubi.mk _ _ _ = Karoubi.mk _ _ _
  congr 1
  exact (Mat_.embedding (GrObj P deg l m)).map_id _

end IdemHom

/-! ## Whiskering by 1-morphisms -/

section Whisker

variable {j n : P.Bicat}

variable (deg) in
/-- Left whiskering `a ∘ -` by a 1-morphism `a : j ⟶ l` (library order: `a` is written to the
left), on shifted 1-morphisms; it preserves degrees. -/
@[simps]
def wLGr (a : Bicat.Hom j l) : GrObj P deg l m ⥤ GrObj P deg j m where
  obj X := ⟨a.comp X.x, X.t⟩
  map f := ⟨P.wL a.obj f.1, wL_mem_homDeg a.obj f.2⟩
  map_id X := Subtype.ext (P.wL_id_of_composable (a.composable X.x))
  map_comp f g := Subtype.ext (P.wL_comp a.obj f.1 g.1)

instance wLGr_additive (a : Bicat.Hom j l) : (wLGr (m := m) deg a).Additive where
  map_add := Subtype.ext (P.wL_add _ _ _)

instance wLGr_linear (a : Bicat.Hom j l) : (wLGr (m := m) deg a).Linear k where
  map_smul _ _ := Subtype.ext (P.wL_smul _ _ _)

variable (deg) in
/-- Right whiskering `- ∘ b` by a 1-morphism `b : m ⟶ n`, on shifted 1-morphisms. -/
@[simps]
def wRGr (b : Bicat.Hom m n) : GrObj P deg l m ⥤ GrObj P deg l n where
  obj X := ⟨X.x.comp b, X.t⟩
  map {X Y} f := ⟨P.wRAt l.region f.1 b.obj X.x.start_eq Y.x.start_eq,
    wRAt_mem_homDeg f.2 b.obj _ _⟩
  map_id X := Subtype.ext (P.wRAt_id X.x.start_eq b.obj (X.x.composable b).ok_endR)
  map_comp {X Y Z} f g :=
    Subtype.ext (P.wRAt_comp X.x.start_eq Y.x.start_eq Z.x.start_eq f.1 g.1 b.obj)

instance wRGr_additive (b : Bicat.Hom m n) : (wRGr (l := l) deg b).Additive where
  map_add {X Y f g} := Subtype.ext (P.wRAt_add X.x.start_eq Y.x.start_eq f.1 g.1 b.obj)

instance wRGr_linear (b : Bicat.Hom m n) : (wRGr (l := l) deg b).Linear k where
  map_smul {X Y} f r := Subtype.ext (P.wRAt_smul X.x.start_eq Y.x.start_eq r f.1 b.obj)

variable (deg) in
/-- **Left composition with a 1-morphism `a : j ⟶ l`** as an additive `k`-linear functor
`U̇(l, m) ⥤ U̇(j, m)`. -/
abbrev wLDot (a : Bicat.Hom j l) : UDotHom P deg l m ⥤ UDotHom P deg j m :=
  mapKaroubi (wLGr (m := m) deg a).mapMat_

variable (deg) in
/-- **Right composition with a 1-morphism `b : m ⟶ n`** as an additive `k`-linear functor
`U̇(l, m) ⥤ U̇(l, n)`. -/
abbrev wRDot (b : Bicat.Hom m n) : UDotHom P deg l m ⥤ UDotHom P deg l n :=
  mapKaroubi (wRGr (l := l) deg b).mapMat_

example (a : Bicat.Hom j l) : (wLDot (m := m) deg a).Additive := inferInstance
example (a : Bicat.Hom j l) : (wLDot (m := m) deg a).Linear k := inferInstance
example (b : Bicat.Hom m n) : (wRDot (l := l) deg b).Additive := inferInstance

end Whisker

end GradedBicat

end Categorification
