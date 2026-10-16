/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqReparam
import Categorification.TwoRep.SumInvPointwise

/-!
# Sum inverses from isomorphisms of biproducts

J. Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1, (1.8) and (1.9)
ask for the invertibility of `(σ, caps) : F E ⟶ E F ⊕ 1^{⊕ n}` and of `(σ, cups)`. This file
produces the explicit inverses `SumInvTo`, `SumInvFrom` from isomorphisms in a category with finite
biproducts, and transports them:

* `SumInvTo.ofIsIsoLift'`, `SumInvFrom.ofIsIsoDesc'`: from an isomorphism
  `X ≅ Y ⊞ ⨁_{t < n} Z` (resp. `Y ⊞ ⨁_{t < n} Z ≅ X`);
* `SumInvTo.biprodMap`, `SumInvFrom.biprodMap`: adding an isomorphism as a direct summand;
* `SumInvTo.ofMat`, `SumInvFrom.ofMat`: from an isomorphism in the additive envelope `Mat_ 𝒞`
  of the form of the coproduct theorem (`isIso_rouqMap_of_nonneg`, `isIso_rouqMap_of_nonpos`),
  through the extension `matLift Ψ : Mat_ 𝒞 ⥤ 𝒟` of an additive functor `Ψ : 𝒞 ⥤ 𝒟` to a
  category with finite biproducts (`Mat_.lift`, without its universe constraint).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

section Biprod

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]

/-- The family `g 0, …, g (n-1)`, extended by zero. -/
def finExt {X Z : D} {n : ℕ} (g : Fin n → (X ⟶ Z)) (m : ℕ) : X ⟶ Z :=
  if h : m < n then g ⟨m, h⟩ else 0

omit [HasFiniteBiproducts D] in
theorem sum_range_finExt {X Z W : D} {n : ℕ} (g : Fin n → (X ⟶ Z)) (g' : Fin n → (Z ⟶ W)) :
    ∑ m ∈ Finset.range n, finExt g m ≫ finExt g' m = ∑ t : Fin n, g t ≫ g' t := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [finExt, t.2]

/-- **A sum inverse from an isomorphism** `X ≅ Y ⊞ ⨁_{t < n} Z` with components `f` and
`g 0, …, g (n-1)`. -/
def SumInvTo.ofIsIsoLift' {X Y Z : D} (f : X ⟶ Y) {n : ℕ} (g : Fin n → (X ⟶ Z))
    (hI : IsIso (biprod.lift f (biproduct.lift g))) : SumInvTo f (finExt g) n :=
  let K := inv (biprod.lift f (biproduct.lift g))
  have h1 : biprod.lift f (biproduct.lift g) ≫ K = 𝟙 _ := IsIso.hom_inv_id _
  have h2 : K ≫ biprod.lift f (biproduct.lift g) = 𝟙 _ := IsIso.inv_hom_id _
  { f' := biprod.inl ≫ K
    g' := finExt fun t => biproduct.ι (fun _ : Fin n => Z) t ≫ biprod.inr ≫ K
    total := by
      rw [sum_range_finExt, ← h1, biprod.lift_eq, Preadditive.add_comp, biproduct.lift_eq,
        Preadditive.sum_comp, Preadditive.sum_comp]
      simp only [Category.assoc]
    ff := by
      have := congrArg (fun φ => biprod.inl ≫ φ ≫ biprod.fst) h2
      simpa only [Category.assoc, biprod.lift_fst, Category.id_comp, biprod.inl_fst] using this
    fg := fun m hm => by
      have := congrArg (fun φ => biprod.inl ≫ φ ≫ biprod.snd ≫
        biproduct.π (fun _ : Fin n => Z) ⟨m, hm⟩) h2
      simp only [Category.assoc, biprod.lift_snd_assoc, biproduct.lift_π, Category.id_comp,
        biprod.inl_snd_assoc, Limits.zero_comp] at this
      simpa only [finExt, hm, ↓reduceDIte, Category.assoc] using this
    gf := fun m hm => by
      have := congrArg (fun φ => biproduct.ι (fun _ : Fin n => Z) ⟨m, hm⟩ ≫ biprod.inr ≫ φ ≫
        biprod.fst) h2
      simp only [Category.assoc, biprod.lift_fst, Category.id_comp, biprod.inr_fst,
        Limits.comp_zero] at this
      simpa only [finExt, hm, ↓reduceDIte, Category.assoc] using this
    gg := fun m m' hm hm' => by
      have := congrArg (fun φ => biproduct.ι (fun _ : Fin n => Z) ⟨m, hm⟩ ≫ biprod.inr ≫ φ ≫
        biprod.snd ≫ biproduct.π (fun _ : Fin n => Z) ⟨m', hm'⟩) h2
      simp only [Category.assoc, biprod.lift_snd_assoc, biproduct.lift_π, Category.id_comp,
        biprod.inr_snd_assoc, biproduct.ι_π] at this
      simp only [finExt, hm, hm', ↓reduceDIte, Category.assoc]
      rw [this]
      by_cases hmm : m = m'
      · subst hmm; simp
      · simp [hmm] }

/-- **A sum inverse from an isomorphism** `Y ⊞ ⨁_{t < n} Z ≅ X` with components `f` and
`g 0, …, g (n-1)`. -/
def SumInvFrom.ofIsIsoDesc' {X Y Z : D} (f : Y ⟶ X) {n : ℕ} (g : Fin n → (Z ⟶ X))
    (hI : IsIso (biprod.desc f (biproduct.desc g))) : SumInvFrom f (finExt g) n :=
  let K := inv (biprod.desc f (biproduct.desc g))
  have h1 : biprod.desc f (biproduct.desc g) ≫ K = 𝟙 _ := IsIso.hom_inv_id _
  have h2 : K ≫ biprod.desc f (biproduct.desc g) = 𝟙 _ := IsIso.inv_hom_id _
  { f' := K ≫ biprod.fst
    g' := finExt fun t => K ≫ biprod.snd ≫ biproduct.π (fun _ : Fin n => Z) t
    total := by
      rw [sum_range_finExt, ← h2, biprod.desc_eq, Preadditive.comp_add, biproduct.desc_eq,
        Preadditive.comp_sum, Preadditive.comp_sum]
      simp only [Category.assoc]
    ff := by
      have := congrArg (fun φ => biprod.inl ≫ φ ≫ biprod.fst) h1
      simpa only [Category.assoc, biprod.inl_desc_assoc, Category.id_comp, biprod.inl_fst]
        using this
    fg := fun m hm => by
      have := congrArg (fun φ => biprod.inl ≫ φ ≫ biprod.snd ≫
        biproduct.π (fun _ : Fin n => Z) ⟨m, hm⟩) h1
      simp only [Category.assoc, biprod.inl_desc_assoc, Category.id_comp,
        biprod.inl_snd_assoc, Limits.zero_comp] at this
      simpa only [finExt, hm, ↓reduceDIte, Category.assoc] using this
    gf := fun m hm => by
      have := congrArg (fun φ => biproduct.ι (fun _ : Fin n => Z) ⟨m, hm⟩ ≫ biprod.inr ≫ φ ≫
        biprod.fst) h1
      simp only [Category.assoc, biprod.inr_desc_assoc, biproduct.ι_desc_assoc,
        Category.id_comp, biprod.inr_fst, Limits.comp_zero] at this
      simpa only [finExt, hm, ↓reduceDIte, Category.assoc] using this
    gg := fun m m' hm hm' => by
      have := congrArg (fun φ => biproduct.ι (fun _ : Fin n => Z) ⟨m, hm⟩ ≫ biprod.inr ≫ φ ≫
        biprod.snd ≫ biproduct.π (fun _ : Fin n => Z) ⟨m', hm'⟩) h1
      simp only [Category.assoc, biprod.inr_desc_assoc, biproduct.ι_desc_assoc,
        Category.id_comp, biprod.inr_snd_assoc, biproduct.ι_π] at this
      simp only [finExt, hm, hm', ↓reduceDIte]
      rw [this]
      by_cases hmm : m = m'
      · subst hmm; simp
      · simp [hmm] }

end Biprod

section BiprodMap

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]

/-- **Adding an isomorphism as a direct summand**: from a sum inverse of `(f₀, g₀)` and an
isomorphism `f₁`, a sum inverse of `(f₀ ⊞ f₁, g₀ ∘ fst)`. -/
def SumInvTo.biprodMap {X₀ Y₀ X₁ Y₁ Z : D} {f₀ : X₀ ⟶ Y₀} {g₀ : ℕ → (X₀ ⟶ Z)} {n : ℕ}
    (S : SumInvTo f₀ g₀ n) (f₁ : X₁ ⟶ Y₁) [IsIso f₁] :
    SumInvTo (biprod.map f₀ f₁) (fun m => biprod.fst ≫ g₀ m) n where
  f' := biprod.map S.f' (inv f₁)
  g' m := S.g' m ≫ biprod.inl
  total := by
    have e : (∑ m ∈ Finset.range n, (biprod.fst ≫ g₀ m) ≫ S.g' m ≫ biprod.inl :
        X₀ ⊞ X₁ ⟶ X₀ ⊞ X₁) =
        biprod.fst ≫ (∑ m ∈ Finset.range n, g₀ m ≫ S.g' m) ≫ (biprod.inl : X₀ ⟶ X₀ ⊞ X₁) := by
      rw [Preadditive.sum_comp, Preadditive.comp_sum]
      simp only [Category.assoc]
    rw [e, ← sub_eq_iff_eq_add'.mpr S.total.symm]
    ext <;> simp
  ff := by ext <;> simp [S.ff]
  fg m hm := by simp [S.fg m hm]
  gf m hm := by simp [reassoc_of% S.gf m hm]
  gg m m' hm hm' := by simp [S.gg m m' hm hm']

/-- **Adding an isomorphism as a direct summand**: from a sum inverse of `(f₀, g₀)` and an
isomorphism `f₁`, a sum inverse of `(f₀ ⊞ f₁, g₀ ≫ inl)`. -/
def SumInvFrom.biprodMap {X₀ Y₀ X₁ Y₁ Z : D} {f₀ : Y₀ ⟶ X₀} {g₀ : ℕ → (Z ⟶ X₀)} {n : ℕ}
    (S : SumInvFrom f₀ g₀ n) (f₁ : Y₁ ⟶ X₁) [IsIso f₁] :
    SumInvFrom (biprod.map f₀ f₁) (fun m => g₀ m ≫ biprod.inl) n where
  f' := biprod.map S.f' (inv f₁)
  g' m := biprod.fst ≫ S.g' m
  total := by
    have e : (∑ m ∈ Finset.range n, (biprod.fst ≫ S.g' m) ≫ g₀ m ≫ biprod.inl :
        X₀ ⊞ X₁ ⟶ X₀ ⊞ X₁) =
        biprod.fst ≫ (∑ m ∈ Finset.range n, S.g' m ≫ g₀ m) ≫ (biprod.inl : X₀ ⟶ X₀ ⊞ X₁) := by
      rw [Preadditive.sum_comp, Preadditive.comp_sum]
      simp only [Category.assoc]
    rw [e, ← sub_eq_iff_eq_add'.mpr S.total.symm]
    ext <;> simp
  ff := by ext <;> simp [S.ff]
  fg m hm := by simp [S.fg m hm]
  gf m hm := by simp [reassoc_of% S.gf m hm]
  gg m m' hm hm' := by simp [S.gg m m' hm hm']

end BiprodMap

section Mat

variable {𝒞 : Type u} [Category.{v} 𝒞] [Preadditive 𝒞]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]
  (Ψ : 𝒞 ⥤ D) [Ψ.Additive]

/-- The extension `Mat_ 𝒞 ⥤ D` of an additive functor `Ψ : 𝒞 ⥤ D` to a category with finite
biproducts: `Mat_.lift`, for categories with morphisms in different universes. -/
@[simps]
abbrev matLift : Mat_ 𝒞 ⥤ D where
  obj M := ⨁ fun i => Ψ.obj (M.X i)
  map f := biproduct.matrix fun i j => Ψ.map (f i j)
  map_id M := by
    ext i j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  map_comp f g := by
    ext i k
    simp [Mat_.comp_apply, Ψ.map_sum, biproduct.ι_matrix_assoc, biproduct.matrix_π,
      biproduct.lift_desc]

theorem matLift_map_add {M N : Mat_ 𝒞} (f g : M ⟶ N) :
    (matLift Ψ).map (f + g) = (matLift Ψ).map f + (matLift Ψ).map g :=
  biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun j => by
    simp only [Category.assoc, Preadditive.add_comp, Preadditive.comp_add,
      biproduct.matrix_π, biproduct.ι_desc]
    exact Ψ.map_add

theorem matLift_map_zero {M N : Mat_ 𝒞} : (matLift Ψ).map (0 : M ⟶ N) = 0 :=
  biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun j => by
    simp only [Category.assoc, biproduct.matrix_π, biproduct.ι_desc,
      Limits.zero_comp, Limits.comp_zero]
    exact Ψ.map_zero _ _


instance : (matLift Ψ).Additive where
  map_add := matLift_map_add Ψ _ _

theorem matLift_map_π {M : Mat_ 𝒞} {o : 𝒞} {n : ℕ} (caps : M ⟶ oMat o (Fin n)) (t : Fin n) :
    (matLift Ψ).map caps ≫ biproduct.π (fun i => Ψ.obj ((oMat o (Fin n)).X i)) t =
      biproduct.desc fun a => Ψ.map (caps a t) :=
  biproduct.matrix_π _ _

theorem ι_matLift_map {N : Mat_ 𝒞} {o : 𝒞} {n : ℕ} (cups : oMat o (Fin n) ⟶ N) (t : Fin n) :
    biproduct.ι (fun i => Ψ.obj ((oMat o (Fin n)).X i)) t ≫ (matLift Ψ).map cups =
      biproduct.lift fun c => Ψ.map (cups t c) :=
  biproduct.ι_matrix _ _

omit [HasFiniteBiproducts D] in
theorem isIso_biprod_lift_map {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜] [HasBinaryBiproducts 𝒜]
    {ℬ : Type*} [Category ℬ] [Preadditive ℬ] [HasBinaryBiproducts ℬ] (Φ : 𝒜 ⥤ ℬ) [Φ.Additive]
    (X Y : 𝒜) : IsIso (biprod.lift (Φ.map (biprod.fst : X ⊞ Y ⟶ X)) (Φ.map biprod.snd)) :=
  ⟨⟨biprod.desc (Φ.map biprod.inl) (Φ.map biprod.inr),
    by rw [biprod.lift_desc, ← Φ.map_comp, ← Φ.map_comp, ← Φ.map_add, biprod.total, Φ.map_id],
    by
      apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
        simp [← Φ.map_comp]⟩⟩

omit [HasFiniteBiproducts D] in
theorem isIso_biprod_desc_map {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜] [HasBinaryBiproducts 𝒜]
    {ℬ : Type*} [Category ℬ] [Preadditive ℬ] [HasBinaryBiproducts ℬ] (Φ : 𝒜 ⥤ ℬ) [Φ.Additive]
    (X Y : 𝒜) : IsIso (biprod.desc (Φ.map (biprod.inl : X ⟶ X ⊞ Y)) (Φ.map biprod.inr)) :=
  ⟨⟨biprod.lift (Φ.map biprod.fst) (Φ.map biprod.snd),
    by
      apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
        simp [← Φ.map_comp],
    by rw [biprod.lift_desc, ← Φ.map_comp, ← Φ.map_comp, ← Φ.map_add, biprod.total, Φ.map_id]⟩⟩

/-- **A sum inverse from an isomorphism in the additive envelope**: if
`(φ, caps) : ⊞ₐ Fₐ ⟶ ⊞_c G_c ⊞ o^{⊕ n}` is invertible in `Mat_ 𝒞` (the form of the coproduct
theorem), then its image under an additive functor `Ψ : 𝒞 ⥤ D` gives a sum inverse of
`(Ψ φ, Ψ caps)` on the biproducts in `D`. -/
def SumInvTo.ofMat {M M' : Mat_ 𝒞} {o : 𝒞} {n : ℕ} (φ : M ⟶ M') (caps : M ⟶ oMat o (Fin n))
    (hI : IsIso (biprod.lift φ caps)) :
    SumInvTo ((matLift Ψ).map φ) (finExt fun t =>
      ((matLift Ψ).map caps ≫ biproduct.π (fun i => Ψ.obj ((oMat o (Fin n)).X i)) t :
      _ ⟶ Ψ.obj o)) n := by
  have e : (matLift Ψ).map (biprod.lift φ caps) ≫
      biprod.lift ((matLift Ψ).map biprod.fst) ((matLift Ψ).map biprod.snd) =
      biprod.lift ((matLift Ψ).map φ) (biproduct.lift fun t =>
        ((matLift Ψ).map caps ≫ biproduct.π (fun i => Ψ.obj ((oMat o (Fin n)).X i)) t :
          _ ⟶ Ψ.obj o)) := by
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst, ← Functor.map_comp, biprod.lift_fst, biprod.lift_fst]
    · rw [Category.assoc, biprod.lift_snd, ← Functor.map_comp, biprod.lift_snd, biprod.lift_snd]
      exact biproduct.hom_ext _ _ fun t =>
        (biproduct.lift_π (f := fun i => Ψ.obj ((oMat o (Fin n)).X i))
          (fun t => (matLift Ψ).map caps ≫ biproduct.π _ t) t).symm
  have hI' : IsIso (biprod.lift ((matLift Ψ).map φ) (biproduct.lift fun t =>
      ((matLift Ψ).map caps ≫ biproduct.π (fun i => Ψ.obj ((oMat o (Fin n)).X i)) t :
        _ ⟶ Ψ.obj o))) := by
    have h1 : IsIso ((matLift Ψ).map (biprod.lift φ caps)) := Functor.map_isIso _ _
    have h2 := isIso_biprod_lift_map (matLift Ψ) M' (oMat o (Fin n))
    rw [← e]; exact IsIso.comp_isIso
  exact SumInvTo.ofIsIsoLift' _ _ hI'

/-- **A sum inverse from an isomorphism in the additive envelope**, the dual of
`SumInvTo.ofMat`: `(φ, cups) : ⊞ₐ Fₐ ⊞ o^{⊕ n} ⟶ ⊞_c G_c` in `Mat_ 𝒞`. -/
def SumInvFrom.ofMat {M M' : Mat_ 𝒞} {o : 𝒞} {n : ℕ} (φ : M ⟶ M') (cups : oMat o (Fin n) ⟶ M')
    (hI : IsIso (biprod.desc φ cups)) :
    SumInvFrom ((matLift Ψ).map φ) (finExt fun t =>
      (biproduct.ι (fun i => Ψ.obj ((oMat o (Fin n)).X i)) t ≫ (matLift Ψ).map cups :
      Ψ.obj o ⟶ _)) n := by
  have e : biprod.desc ((matLift Ψ).map biprod.inl) ((matLift Ψ).map biprod.inr) ≫
      (matLift Ψ).map (biprod.desc φ cups) =
      biprod.desc ((matLift Ψ).map φ) (biproduct.desc fun t =>
        (biproduct.ι (fun i => Ψ.obj ((oMat o (Fin n)).X i)) t ≫ (matLift Ψ).map cups :
          Ψ.obj o ⟶ _)) := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, ← Functor.map_comp, biprod.inl_desc, biprod.inl_desc]
    · rw [biprod.inr_desc_assoc, ← Functor.map_comp, biprod.inr_desc, biprod.inr_desc]
      exact biproduct.hom_ext' _ _ fun t =>
        (biproduct.ι_desc (f := fun i => Ψ.obj ((oMat o (Fin n)).X i))
          (fun t => biproduct.ι (fun i => Ψ.obj ((oMat o (Fin n)).X i)) t ≫ (matLift Ψ).map cups)
          t).symm
  have hI' : IsIso (biprod.desc ((matLift Ψ).map φ) (biproduct.desc fun t =>
      (biproduct.ι (fun i => Ψ.obj ((oMat o (Fin n)).X i)) t ≫ (matLift Ψ).map cups :
        Ψ.obj o ⟶ _))) := by
    have h1 : IsIso ((matLift Ψ).map (biprod.desc φ cups)) := Functor.map_isIso _ _
    have h2 := isIso_biprod_desc_map (matLift Ψ) M (oMat o (Fin n))
    rw [← e]; exact IsIso.comp_isIso
  exact SumInvFrom.ofIsIsoDesc' _ _ hI'

end Mat

end Categorification.TwoRep
