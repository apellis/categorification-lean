/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.SplitK0
import Categorification.Diagrams.KL3.KaroubiHcomp

/-!
# The split Grothendieck groups `K₀(U̇(λ, μ))`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.6
(TeX `\subsection{$K_0(\dot{\cal{U}})$ and homomorphism $\gamma$}`, eqs. (3.62)–(3.69)).

For a presentation `P` of an even signature with a grading `deg`, and objects `l m` of the
presented bicategory, we equip the Hom category `U̇(l, m) = UDotHom P deg l m`
(`Categorification.Diagrams.KL3.Karoubi`) with the grading shift `{n}` and form

* `K0U P deg l m = SplitK0 (UDotHom P deg l m)`: the split Grothendieck group of the additive
  category `U̇(l, m)` (KL III: "generators `[P]`, over all objects `P` of `A`, and relations
  `[P] = [P'] + [P'']` whenever `P ≅ P' ⊕ P''`"), a `ℤ[q, q⁻¹]`-module with `q^n [X] = [X{n}]`
  (KL III (3.65): "`[E_i 1_λ {t + 1}, e{1}] = q [E_i 1_λ {t}, e]`"; `K0U.T_smul_of`).
* `K0U.wL a`, `K0U.wR b`: the `ℤ[q, q⁻¹]`-linear maps induced by composition with a
  1-morphism on either side.
* `K0U.mul : K0U l m →+ K0U m n →+ K0U l n`: the biadditive map induced by the composition
  functor `hcompDot` (KL III (3.67)–(3.68)); it is `ℤ[q, q⁻¹]`-bilinear (`K0U.mul_shift_left`,
  `K0U.mul_shift_right`), and on classes of shifted 1-morphisms
  `[x{t}] · [y{s}] = [(x y){t + s}]` (`K0U.mul_objOf`).

Here "the product" is taken in the library's order of composition (a 1-morphism `l ⟶ m` followed
by `m ⟶ n`), which for KL III's `U` is the order of the words `E_s E_t` read from left to right.
The associativity of `K0U.mul` is in `Categorification.Diagrams.KL3.KaroubiAssoc`.

## Generic tool

`karIsoOfPerm`: two objects `A`, `B` of the Karoubi envelope of a matrix category are isomorphic
if there is a bijection `e` of the index sets with `B_{e i} = A_i` and the idempotent of `B` is
the conjugate of that of `A`. All isomorphisms of this file (shifts `X{0} ≅ X`,
`X{m + n} ≅ X{m}{n}`, compatibility of shifts with composition) are of this form.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits

universe w v u₀ u₁ u₂

/-! ## Permutation matrices in `Mat_ C` and isomorphisms in `Karoubi (Mat_ C)` -/

section Perm

variable {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]

open Classical in
/-- The permutation matrix `M ⟶ N` of a bijection `e : M.ι ≃ N.ι` with `N_{e i} = M_i`. -/
def permMat {M N : Mat_ 𝒞} (e : M.ι ≃ N.ι) (h : ∀ i, N.X (e i) = M.X i) : M ⟶ N :=
  fun i j => if hij : e i = j then eqToHom ((h i).symm.trans (congrArg N.X hij)) else 0

theorem permMat_apply_self {M N : Mat_ 𝒞} (e : M.ι ≃ N.ι) (h : ∀ i, N.X (e i) = M.X i) (i : M.ι) :
    (permMat e h : M ⟶ N) i (e i) = eqToHom (h i).symm := by
  simp [permMat]

theorem permMat_apply_of_eq {M N : Mat_ 𝒞} (e : M.ι ≃ N.ι) (h : ∀ i, N.X (e i) = M.X i)
    (i : M.ι) (j : N.ι) (hij : e i = j) :
    (permMat e h : M ⟶ N) i j = eqToHom ((h i).symm.trans (congrArg N.X hij)) := by
  simp [permMat, hij]

theorem permMat_apply_ne {M N : Mat_ 𝒞} (e : M.ι ≃ N.ι) (h : ∀ i, N.X (e i) = M.X i) (i : M.ι)
    (j : N.ι) (hij : e i ≠ j) : (permMat e h : M ⟶ N) i j = 0 := by
  simp [permMat, hij]

theorem comp_permMat_apply {L M N : Mat_ 𝒞} (e : M.ι ≃ N.ι) (h : ∀ i, N.X (e i) = M.X i)
    (f : L ⟶ M) (i : L.ι) (j : M.ι) :
    (f ≫ permMat e h : L ⟶ N) i (e j) = f i j ≫ eqToHom (h j).symm := by
  rw [Mat_.comp_apply, Finset.sum_eq_single j]
  · rw [permMat_apply_self]
  · intro j' _ hj'
    rw [permMat_apply_ne e h j' (e j) (fun h' => hj' (e.injective h')), comp_zero]
  · intro h'; exact absurd (Finset.mem_univ j) h'

theorem permMat_comp_apply {M N K : Mat_ 𝒞} (e : M.ι ≃ N.ι) (h : ∀ i, N.X (e i) = M.X i)
    (f : N ⟶ K) (i : M.ι) (k : K.ι) :
    (permMat e h ≫ f : M ⟶ K) i k = eqToHom (h i).symm ≫ f (e i) k := by
  rw [Mat_.comp_apply, Finset.sum_eq_single (e i)]
  · rw [permMat_apply_self]
  · intro j' _ hj'
    rw [permMat_apply_ne e h i j' (Ne.symm hj'), zero_comp]
  · intro h'; exact absurd (Finset.mem_univ _) h'

theorem permMat_comp_permMat {M N : Mat_ 𝒞} (e : M.ι ≃ N.ι) (h : ∀ i, N.X (e i) = M.X i)
    (h' : ∀ j, M.X (e.symm j) = N.X j) :
    permMat e h ≫ permMat e.symm h' = 𝟙 M := by
  ext i k
  rw [permMat_comp_apply]
  by_cases hik : i = k
  · subst hik
    rw [permMat_apply_of_eq e.symm h' (e i) i (e.symm_apply_apply i), eqToHom_trans,
      Mat_.id_apply_self, eqToHom_refl]
  · rw [permMat_apply_ne e.symm h' (e i) k (by simpa using hik), comp_zero,
      Mat_.id_apply_of_ne _ _ _ hik]

/-- **Isomorphism of Karoubi objects by a permutation matrix**: if `e : A.ι ≃ B.ι` with
`B_{e i} = A_i` and `B.p_{e i, e j} = A.p_{i j}` (conjugated by the identifications), then
`A ≅ B`. -/
def karIsoOfPerm (A B : Karoubi (Mat_ 𝒞)) (e : A.X.ι ≃ B.X.ι) (h : ∀ i, B.X.X (e i) = A.X.X i)
    (hp : ∀ i j, B.p (e i) (e j) = eqToHom (h i) ≫ A.p i j ≫ eqToHom (h j).symm) : A ≅ B := by
  have h' : ∀ j, A.X.X (e.symm j) = B.X.X j := fun j => by
    rw [← h (e.symm j), Equiv.apply_symm_apply]
  have hcomm : permMat e h ≫ B.p = A.p ≫ permMat e h := by
    ext i k
    obtain ⟨k, rfl⟩ := e.surjective k
    rw [comp_permMat_apply, permMat_comp_apply, hp]
    simp
  have hcomm' : permMat e.symm h' ≫ A.p = B.p ≫ permMat e.symm h' := by
    have h1 := permMat_comp_permMat e h h'
    have h2 : permMat e.symm h' ≫ permMat e h = 𝟙 B.X := by
      ext j k
      rw [permMat_comp_apply]
      by_cases hjk : j = k
      · subst hjk
        rw [permMat_apply_of_eq e h (e.symm j) j (e.apply_symm_apply j), eqToHom_trans,
          Mat_.id_apply_self, eqToHom_refl]
      · rw [permMat_apply_ne e h (e.symm j) k (by simpa using hjk), comp_zero,
          Mat_.id_apply_of_ne _ _ _ hjk]
    calc permMat e.symm h' ≫ A.p
        = permMat e.symm h' ≫ A.p ≫ permMat e h ≫ permMat e.symm h' := by
          rw [h1, Category.comp_id]
      _ = permMat e.symm h' ≫ permMat e h ≫ B.p ≫ permMat e.symm h' := by
          rw [← Category.assoc A.p, ← hcomm, Category.assoc]
      _ = B.p ≫ permMat e.symm h' := by rw [← Category.assoc, h2, Category.id_comp]
  exact
    { hom := ⟨A.p ≫ permMat e h, by
        rw [Category.assoc, hcomm, ← Category.assoc, ← Category.assoc, A.idem, A.idem]⟩
      inv := ⟨B.p ≫ permMat e.symm h', by
        rw [Category.assoc, hcomm', ← Category.assoc, ← Category.assoc, B.idem, B.idem]⟩
      hom_inv_id := by
        apply Karoubi.hom_ext
        simp only [Karoubi.comp_f, Karoubi.id_f, Category.assoc]
        rw [← Category.assoc (permMat e h), hcomm, Category.assoc, permMat_comp_permMat e h h',
          Category.comp_id]
        exact A.idem
      inv_hom_id := by
        apply Karoubi.hom_ext
        simp only [Karoubi.comp_f, Karoubi.id_f, Category.assoc]
        have h2 : permMat e.symm h' ≫ permMat e h = 𝟙 B.X := by
          ext j k
          rw [permMat_comp_apply]
          by_cases hjk : j = k
          · subst hjk
            rw [permMat_apply_of_eq e h (e.symm j) j (e.apply_symm_apply j), eqToHom_trans,
              Mat_.id_apply_self, eqToHom_refl]
          · rw [permMat_apply_ne e h (e.symm j) k (by simpa using hjk), comp_zero,
              Mat_.id_apply_of_ne _ _ _ hjk]
        rw [← Category.assoc (permMat e.symm h'), hcomm', Category.assoc, h2,
          Category.comp_id]
        exact B.idem }

end Perm

/-! ## Functors additive in each variable -/

section Mul

variable {𝒜 ℬ ℰ : Type*} [Category 𝒜] [Category ℬ] [Category ℰ] [Preadditive 𝒜] [Preadditive ℬ]
  [Preadditive ℰ]

/-- A functor additive in each variable is additive in the first variable. -/
theorem IsBiadditive.additive_left {H : 𝒜 × ℬ ⥤ ℰ} (hH : IsBiadditive H) (Y : ℬ) :
    (Prod.sectL 𝒜 Y ⋙ H).Additive where
  map_add {_ _ f g} := hH.map_add_left f g (𝟙 Y)

/-- A functor additive in each variable is additive in the second variable. -/
theorem IsBiadditive.additive_right {H : 𝒜 × ℬ ⥤ ℰ} (hH : IsBiadditive H) (X : 𝒜) :
    (Prod.sectR X ℬ ⋙ H).Additive where
  map_add {_ _ f g} := hH.map_add_right (𝟙 X) f g

end Mul

section MulBi

variable {𝒜 : Type u₀} {ℬ : Type u₁} {ℰ : Type u₂} [Category.{v} 𝒜] [Category.{v} ℬ]
  [Category.{v} ℰ] [Preadditive 𝒜] [Preadditive ℬ] [Preadditive ℰ]

theorem matBi_isBiadditive (H : 𝒜 × ℬ ⥤ ℰ) (hH : IsBiadditive H) : IsBiadditive (matBi H hH) where
  map_add_left _ _ _ := by
    ext q q'
    exact hH.map_add_left _ _ _
  map_add_right _ _ _ := by
    ext q q'
    exact hH.map_add_right _ _ _

theorem karProd_isBiadditive (H : 𝒜 × ℬ ⥤ ℰ) (hH : IsBiadditive H) : IsBiadditive (karProd H) where
  map_add_left _ _ _ := Karoubi.hom_ext _ _ (hH.map_add_left _ _ _)
  map_add_right _ _ _ := Karoubi.hom_ext _ _ (hH.map_add_right _ _ _)

end MulBi

/-! ## Shifts and `K₀` of the graded Hom categories -/

namespace GradedBicat

open StringDiagrams Presentation

variable {S : Signature.{u₀, u₁, u₂}} {k : Type w} [CommRing k] {P : Presentation.{w, v} S k}
  {deg : S.Gen → ℤ} {l m n : P.Bicat}

theorem GrObj.eqToHom_val {X Y : GrObj P deg l m} (h : X = Y) :
    (eqToHom h).1 = eqToHom (congrArg (fun Z : GrObj P deg l m => P.obj Z.x.obj) h) := by
  subst h; rfl

/-- **Isomorphism criterion in `U̇(l, m)`**: `A ≅ B` if there is a bijection `e` of the index
sets of the underlying formal sums such that the summands `x_i{t_i}` of `A` and `B` agree
(`B_{e i}` has the same 1-morphism and the same shift as `A_i`) and the idempotents have the same
underlying 2-morphisms. -/
def udIso (A B : UDotHom P deg l m) (e : A.X.ι ≃ B.X.ι)
    (hx : ∀ i, (B.X.X (e i)).x = (A.X.X i).x) (ht : ∀ i, (B.X.X (e i)).t = (A.X.X i).t)
    (hp : ∀ i j, (B.p (e i) (e j)).1 =
      eqToHom (congrArg (fun z : Bicat.Hom l m => P.obj z.obj) (hx i)) ≫ (A.p i j).1 ≫
        eqToHom (congrArg (fun z : Bicat.Hom l m => P.obj z.obj) (hx j)).symm) : A ≅ B :=
  karIsoOfPerm A B e (fun i => GrObj.ext (hx i) (ht i)) fun i j => by
    apply GrObj.hom_ext
    rw [hp, GrObj.comp_val, GrObj.comp_val, GrObj.eqToHom_val, GrObj.eqToHom_val]

variable (deg) in
/-- The grading shift `x{t} ↦ x{t + n}` on shifted 1-morphisms (the identity on 2-morphisms). -/
@[simps]
def shGr (n : ℤ) : GrObj P deg l m ⥤ GrObj P deg l m where
  obj X := ⟨X.x, X.t + n⟩
  map f := ⟨f.1, mem_homDeg_of_eq f.2 (by ring)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance shGr_additive (n : ℤ) : (shGr (l := l) (m := m) deg n).Additive where
  map_add := rfl

instance shGr_linear (n : ℤ) : (shGr (l := l) (m := m) deg n).Linear k where
  map_smul _ _ := rfl

variable (deg) in
/-- **The grading shift `{n}` on `U̇(l, m)`** (KL III Definition 3.1: `x{t} ↦ x{t + n}`),
an additive `k`-linear functor. -/
abbrev shDot (n : ℤ) : UDotHom P deg l m ⥤ UDotHom P deg l m :=
  mapKaroubi (shGr deg n).mapMat_

theorem additive_biprod_iso {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] [Preadditive 𝒜] [Preadditive ℬ]
    [HasBinaryBiproducts 𝒜] [HasBinaryBiproducts ℬ] (F : 𝒜 ⥤ ℬ) [F.Additive] (X Y : 𝒜) :
    Nonempty (F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y) := by
  haveI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  exact ⟨F.mapBiprod X Y⟩

/-- `X{0} ≅ X`. -/
def shDotZero (A : UDotHom P deg l m) : (shDot deg 0).obj A ≅ A :=
  udIso _ _ (Equiv.refl _) (fun _ => rfl) (fun _ => by simp) fun i j => by
    simp

/-- `X{m + n} ≅ X{m}{n}`. -/
def shDotAdd (a b : ℤ) (A : UDotHom P deg l m) :
    (shDot deg (a + b)).obj A ≅ (shDot deg b).obj ((shDot deg a).obj A) :=
  udIso _ _ (Equiv.refl _) (fun _ => rfl) (fun _ => by simp; ring) fun i j => by
    simp

instance k0Shift : SplitK0.K0Shift (UDotHom P deg l m) where
  sh n A := (shDot deg n).obj A
  sh_iso n _ _ e := ⟨(shDot deg n).mapIso e⟩
  sh_biprod n X Y := additive_biprod_iso (shDot deg n) X Y
  sh_zero A := ⟨shDotZero A⟩
  sh_add a b A := ⟨shDotAdd a b A⟩

variable (P deg l m) in
/-- **`K₀(U̇(l, m))`** (KL III §3.6): the split Grothendieck group of `U̇(l, m)`, a
`ℤ[q, q⁻¹]`-module with `q` acting by the grading shift `{1}`. -/
abbrev K0U : Type _ := SplitK0 (UDotHom P deg l m)

namespace K0U

open SplitK0

/-- The class `[A]` of an object of `U̇(l, m)`. -/
abbrev cl (A : UDotHom P deg l m) : K0U P deg l m := SplitK0.of A

/-- `q^n [A] = [A{n}]` (KL III (3.65)). -/
theorem T_smul_of (a : ℤ) (A : UDotHom P deg l m) :
    (LaurentPolynomial.T a : LaurentPolynomial ℤ) • cl A = cl ((shDot deg a).obj A) :=
  SplitK0.T_smul_of a A

/-- `[x{t}] = q^t [x{0}]`. -/
theorem objOf_shift (x : Bicat.Hom l m) (t : ℤ) :
    cl (objOf (P := P) (deg := deg) x t) =
      (LaurentPolynomial.T t : LaurentPolynomial ℤ) • cl (objOf x 0) := by
  rw [T_smul_of]
  exact of_iso (udIso _ _ (Equiv.refl _) (fun _ => rfl) (fun _ => by simp) fun i j => by
    cases i; cases j; simp [Mat_.id_apply_self])

/-- `(x{t + s}, e) ≅ (x{t}, e){s}`. -/
def idemObjShift (x : Bicat.Hom l m) (t s : ℤ) (e : P.obj x.obj ⟶ P.obj x.obj)
    (he : e ∈ P.homDeg deg x.obj x.obj 0) (hee : e ≫ e = e) :
    idemObj x (t + s) e he hee ≅ (shDot deg s).obj (idemObj x t e he hee) :=
  udIso _ _ (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) fun i j => by
    cases i; cases j; simp [idemObj]

/-- `[(x{t}, e)] = q^t [(x{0}, e)]`. -/
theorem idemObj_shift (x : Bicat.Hom l m) (t : ℤ) (e : P.obj x.obj ⟶ P.obj x.obj)
    (he : e ∈ P.homDeg deg x.obj x.obj 0) (hee : e ≫ e = e) :
    cl (idemObj x t e he hee) = (LaurentPolynomial.T t : LaurentPolynomial ℤ) •
      cl (idemObj x 0 e he hee) := by
  rw [T_smul_of]
  have := of_iso (idemObjShift x 0 t e he hee)
  rw [zero_add] at this
  exact this

end K0U

/-! ## Composition with 1-morphisms -/

section Whisker

variable {j n : P.Bicat}

/-- Left composition commutes with the shift. -/
def wLDotShift (a : Bicat.Hom j l) (s : ℤ) (A : UDotHom P deg l m) :
    (wLDot deg a).obj ((shDot deg s).obj A) ≅ (shDot deg s).obj ((wLDot deg a).obj A) :=
  udIso _ _ (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) fun i j => by simp

/-- Right composition commutes with the shift. -/
def wRDotShift (b : Bicat.Hom m n) (s : ℤ) (A : UDotHom P deg l m) :
    (wRDot deg b).obj ((shDot deg s).obj A) ≅ (shDot deg s).obj ((wRDot deg b).obj A) :=
  udIso _ _ (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) fun i j => by simp

namespace K0U

open SplitK0

/-- The `ℤ[q, q⁻¹]`-linear map `K₀(U̇(l, m)) → K₀(U̇(j, m))`, `[A] ↦ [a A]`. -/
def wL (a : Bicat.Hom j l) : K0U P deg l m →ₗ[LaurentPolynomial ℤ] K0U P deg j m :=
  linearOfShift (map (wLDot deg a)) fun s A => by
    rw [map_of, map_of, shiftHom_of]
    exact of_iso (wLDotShift a s A)

/-- The `ℤ[q, q⁻¹]`-linear map `K₀(U̇(l, m)) → K₀(U̇(l, n))`, `[A] ↦ [A b]`. -/
def wR (b : Bicat.Hom m n) : K0U P deg l m →ₗ[LaurentPolynomial ℤ] K0U P deg l n :=
  linearOfShift (map (wRDot deg b)) fun s A => by
    rw [map_of, map_of, shiftHom_of]
    exact of_iso (wRDotShift b s A)

@[simp] theorem wL_of (a : Bicat.Hom j l) (A : UDotHom P deg l m) :
    wL a (cl A) = cl ((wLDot deg a).obj A) := map_of _ _

@[simp] theorem wR_of (b : Bicat.Hom m n) (A : UDotHom P deg l m) :
    wR b (cl A) = cl ((wRDot deg b).obj A) := map_of _ _

/-- Shifts commute with composition by 1-morphisms on both sides, in `K₀`. -/
theorem ctx_shift {j' n' : P.Bicat} (a : Bicat.Hom j' l) (b : Bicat.Hom m n') (s : ℤ)
    (A : UDotHom P deg l m) :
    cl ((wRDot deg b).obj ((wLDot deg a).obj ((shDot deg s).obj A))) =
      (LaurentPolynomial.T s : LaurentPolynomial ℤ) •
        cl ((wRDot deg b).obj ((wLDot deg a).obj A)) := by
  calc cl ((wRDot deg b).obj ((wLDot deg a).obj ((shDot deg s).obj A)))
      = wR b (wL a (cl ((shDot deg s).obj A))) := by rw [wL_of, wR_of]
    _ = wR b (wL a ((LaurentPolynomial.T s : LaurentPolynomial ℤ) • cl A)) := by rw [T_smul_of]
    _ = (LaurentPolynomial.T s : LaurentPolynomial ℤ) • wR b (wL a (cl A)) := by
      rw [map_smul, map_smul]
    _ = _ := by rw [wL_of, wR_of]

end K0U

/-- `a · x{t} = (a x){t}`. -/
theorem wLDot_objOf (a : Bicat.Hom j l) (x : Bicat.Hom l m) (t : ℤ) :
    (wLDot deg a).obj (objOf (P := P) x t) = objOf (a.comp x) t := by
  fapply Karoubi.ext
  · rfl
  · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    exact (wLGr deg a).mapMat_.map_id _

/-- `x{t} · b = (x b){t}`. -/
theorem wRDot_objOf (b : Bicat.Hom m n) (x : Bicat.Hom l m) (t : ℤ) :
    (wRDot deg b).obj (objOf (P := P) x t) = objOf (x.comp b) t := by
  fapply Karoubi.ext
  · rfl
  · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    exact (wRGr deg b).mapMat_.map_id _

end Whisker

/-! ## The composition `K₀(U̇(l, m)) × K₀(U̇(m, n)) → K₀(U̇(l, n))` -/

section MulU

variable [S.IsEven]

theorem hcompDot_isBiadditive : IsBiadditive (hcompDot deg (l := l) (m := m) (n := n)) :=
  karProd_isBiadditive _ (matBi_isBiadditive _ (hcompGr_isBiadditive deg))

/-- Composition commutes with shifts in the first variable. -/
def hcompDotShiftLeft (s : ℤ) (A : UDotHom P deg l m) (B : UDotHom P deg m n) :
    (hcompDot deg).obj ((shDot deg s).obj A, B) ≅ (shDot deg s).obj ((hcompDot deg).obj (A, B)) :=
  udIso _ _ (Equiv.refl _) (fun _ => rfl) (fun _ => by simp [hcompDot, karProd, matBi, hcompGr]; ring)
    fun i j => by simp [hcompDot, karProd, matBi, hcompGr]

/-- Composition commutes with shifts in the second variable. -/
def hcompDotShiftRight (s : ℤ) (A : UDotHom P deg l m) (B : UDotHom P deg m n) :
    (hcompDot deg).obj (A, (shDot deg s).obj B) ≅ (shDot deg s).obj ((hcompDot deg).obj (A, B)) :=
  udIso _ _ (Equiv.refl _) (fun _ => rfl) (fun _ => by simp [hcompDot, karProd, matBi, hcompGr]; ring)
    fun i j => by simp [hcompDot, karProd, matBi, hcompGr]

/-- `x{t} y{s} ≅ (x y){t + s}` in `U̇` (KL III (3.18)). -/
def hcompDotObjOf (x : Bicat.Hom l m) (y : Bicat.Hom m n) (t s : ℤ) :
    (hcompDot deg).obj ((objOf x t : UDotHom P deg l m), (objOf y s : UDotHom P deg m n)) ≅
      objOf (x.comp y) (t + s) :=
  udIso _ _ (Equiv.prodPUnit _) (fun _ => rfl) (fun _ => rfl) fun i j => by
    rw [hcompDot_objOf_p]
    obtain ⟨⟨⟩, ⟨⟩⟩ := i
    obtain ⟨⟨⟩, ⟨⟩⟩ := j
    simp [Mat_.id_apply_self]

namespace K0U

open SplitK0

/-- **The product on `K₀(U̇)`** (KL III (3.68)): `[A] · [B] = [A B]`, induced by the composition
functor `U̇(l, m) × U̇(m, n) ⥤ U̇(l, n)`. -/
def mul : K0U P deg l m →+ K0U P deg m n →+ K0U P deg l n :=
  lift₂ (fun A B => cl ((hcompDot deg).obj (A, B)))
    (fun _ _ B e => of_iso ((Prod.sectL _ B ⋙ hcompDot deg).mapIso e))
    (fun A _ _ e => of_iso ((Prod.sectR A _ ⋙ hcompDot deg).mapIso e))
    (fun A A' B => by
      haveI := (hcompDot_isBiadditive (deg := deg) (l := l) (m := m) (n := n)).additive_left B
      exact (of_eq_of_nonempty (additive_biprod_iso (Prod.sectL _ B ⋙ hcompDot deg) A A')).trans
        (of_biprod _ _))
    (fun A B B' => by
      haveI := (hcompDot_isBiadditive (deg := deg) (l := l) (m := m) (n := n)).additive_right A
      exact (of_eq_of_nonempty (additive_biprod_iso (Prod.sectR A _ ⋙ hcompDot deg) B B')).trans
        (of_biprod _ _))

@[simp] theorem mul_of (A : UDotHom P deg l m) (B : UDotHom P deg m n) :
    mul (cl A) (cl B) = cl ((hcompDot deg).obj (A, B)) := lift₂_of _ _ _ _ _ _ _

theorem mul_shift_left (s : ℤ) (x : K0U P deg l m) (y : K0U P deg m n) :
    mul ((LaurentPolynomial.T s : LaurentPolynomial ℤ) • x) y =
      (LaurentPolynomial.T s : LaurentPolynomial ℤ) • mul x y := by
  rw [T_smul, T_smul]
  induction x using SplitK0.induction_on generalizing y with
  | of A =>
    induction y using SplitK0.induction_on with
    | of B =>
      rw [shiftHom_of, mul_of, mul_of, shiftHom_of]
      exact of_iso (hcompDotShiftLeft s A B)
    | zero => simp
    | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add]
    | neg y hy => rw [map_neg, map_neg, hy, map_neg]
  | zero => simp
  | add x x' hx hx' => simp [hx, hx']
  | neg x hx => simp [hx]

theorem mul_shift_right (s : ℤ) (x : K0U P deg l m) (y : K0U P deg m n) :
    mul x ((LaurentPolynomial.T s : LaurentPolynomial ℤ) • y) =
      (LaurentPolynomial.T s : LaurentPolynomial ℤ) • mul x y := by
  rw [T_smul, T_smul]
  induction x using SplitK0.induction_on generalizing y with
  | of A =>
    induction y using SplitK0.induction_on with
    | of B =>
      rw [shiftHom_of, mul_of, mul_of, shiftHom_of]
      exact of_iso (hcompDotShiftRight s A B)
    | zero => simp
    | add y y' hy hy' => simp [hy, hy']
    | neg y hy => simp [hy]
  | zero => simp
  | add x x' hx hx' => simp [hx, hx']
  | neg x hx => simp [hx]

/-- `[x{t}] · [y{s}] = [(x y){t + s}]`. -/
theorem mul_objOf (x : Bicat.Hom l m) (y : Bicat.Hom m n) (t s : ℤ) :
    mul (cl (objOf (P := P) (deg := deg) x t)) (cl (objOf y s)) = cl (objOf (x.comp y) (t + s)) := by
  rw [mul_of]
  exact of_iso (hcompDotObjOf x y t s)

end K0U

end MulU

end GradedBicat

end Categorification
