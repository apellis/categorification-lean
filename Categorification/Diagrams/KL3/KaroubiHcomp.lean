/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Karoubi

/-!
# Horizontal composition in `U̇`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.4,
Definition 3.21: "The composition functor `U̇(λ, λ') × U̇(λ', λ'') → U̇(λ, λ'')` is induced by the
universal property of the Karoubi envelope from the composition functor for `U`."

We construct this composition functor for the graded Hom categories of a presented even
2-category (`Categorification.Diagrams.KL3.Karoubi`), in three steps:

* `hcompGr : GrObj l m × GrObj m n ⥤ GrObj l n`: `(x{t}, y{s}) ↦ (x y){t + s}` on objects
  (KL III (3.18)) and the horizontal composite `P.hcomp` on 2-morphisms (degrees add); it is
  additive in each variable (`IsBiadditive`).
* `matBi`: a functor `C × D ⥤ E` additive in each variable extends to formal direct sums,
  `Mat_ C × Mat_ D ⥤ Mat_ E` (`(⊕_a X_a, ⊕_b Y_b) ↦ ⊕_{a,b} H(X_a, Y_b)`).
* `karProd`: any functor `A × B ⥤ E` extends to Karoubi envelopes,
  `Karoubi A × Karoubi B ⥤ Karoubi E` (`((X, p), (Y, q)) ↦ (H(X, Y), H(p, q))`).

The result is `hcompDot : U̇(l, m) × U̇(m, n) ⥤ U̇(l, n)`. The coherence of this composition
(associativity and unit isomorphisms, making `U̇` a bicategory) is not formalized here.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits

universe w v u₀ u₁ u₂

/-! ## Functors additive in each variable -/

section Biadditive

variable {C D E : Type*} [Category C] [Category D] [Category E] [Preadditive C] [Preadditive D]
  [Preadditive E]

/-- A functor out of a product category which is additive in each variable. -/
structure IsBiadditive (H : C × D ⥤ E) : Prop where
  map_add_left : ∀ {X X' : C} {Y Y' : D} (f f' : X ⟶ X') (g : Y ⟶ Y'),
    H.map (X := (X, Y)) (Y := (X', Y')) (f + f', g) =
      H.map (X := (X, Y)) (Y := (X', Y')) (f, g) + H.map (X := (X, Y)) (Y := (X', Y')) (f', g)
  map_add_right : ∀ {X X' : C} {Y Y' : D} (f : X ⟶ X') (g g' : Y ⟶ Y'),
    H.map (X := (X, Y)) (Y := (X', Y')) (f, g + g') =
      H.map (X := (X, Y)) (Y := (X', Y')) (f, g) + H.map (X := (X, Y)) (Y := (X', Y')) (f, g')

namespace IsBiadditive

variable {H : C × D ⥤ E} (hH : IsBiadditive H)
include hH

theorem map_zero_left {X X' : C} {Y Y' : D} (g : Y ⟶ Y') :
    H.map (X := (X, Y)) (Y := (X', Y')) (0, g) = 0 := by
  have := hH.map_add_left (0 : X ⟶ X') 0 g
  rw [add_zero] at this
  exact (left_eq_add.1 this)

theorem map_zero_right {X X' : C} {Y Y' : D} (f : X ⟶ X') :
    H.map (X := (X, Y)) (Y := (X', Y')) (f, 0) = 0 := by
  have := hH.map_add_right f (0 : Y ⟶ Y') 0
  rw [add_zero] at this
  exact (left_eq_add.1 this)

theorem map_sum_left {X X' : C} {Y Y' : D} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ X'))
    (g : Y ⟶ Y') :
    H.map (X := (X, Y)) (Y := (X', Y')) (∑ i ∈ s, f i, g) =
      ∑ i ∈ s, H.map (X := (X, Y)) (Y := (X', Y')) (f i, g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hH.map_zero_left g
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hH.map_add_left, ih]

theorem map_sum_right {X X' : C} {Y Y' : D} {ι : Type*} (s : Finset ι) (f : X ⟶ X')
    (g : ι → (Y ⟶ Y')) :
    H.map (X := (X, Y)) (Y := (X', Y')) (f, ∑ i ∈ s, g i) =
      ∑ i ∈ s, H.map (X := (X, Y)) (Y := (X', Y')) (f, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hH.map_zero_right f
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hH.map_add_right, ih]

end IsBiadditive

end Biadditive

/-! ## Extension to formal direct sums -/

section MatBi

variable {C : Type u₀} {D : Type u₁} {E : Type u₂} [Category.{v} C] [Category.{v} D]
  [Category.{v} E] [Preadditive C] [Preadditive D] [Preadditive E]

/-- A functor `C × D ⥤ E` additive in each variable, extended to formal direct sums:
`(⊕_a X_a, ⊕_b Y_b) ↦ ⊕_{(a, b)} H(X_a, Y_b)`, with the tensor product of matrices. -/
def matBi (H : C × D ⥤ E) (hH : IsBiadditive H) : Mat_ C × Mat_ D ⥤ Mat_ E where
  obj p := ⟨p.1.ι × p.2.ι, fun q => H.obj (p.1.X q.1, p.2.X q.2)⟩
  map {p p'} φ := fun q q' =>
    H.map (X := (p.1.X q.1, p.2.X q.2)) (Y := (p'.1.X q'.1, p'.2.X q'.2)) (φ.1 q.1 q'.1, φ.2 q.2 q'.2)
  map_id p := by
    classical
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp only [prod_id_fst, prod_id_snd]
    by_cases ha : a = a'
    · subst ha
      by_cases hb : b = b'
      · subst hb
        rw [Mat_.id_apply_self, Mat_.id_apply_self, Mat_.id_apply_self, ← prod_id]
        exact H.map_id _
      · rw [Mat_.id_apply_of_ne _ _ _ hb, hH.map_zero_right,
          Mat_.id_apply_of_ne _ _ _ (fun h => hb (congrArg Prod.snd h))]
    · rw [Mat_.id_apply_of_ne _ _ _ ha, hH.map_zero_left,
        Mat_.id_apply_of_ne _ _ _ (fun h => ha (congrArg Prod.fst h))]
  map_comp {p p' p''} φ ψ := by
    ext ⟨a, b⟩ ⟨a'', b''⟩
    simp only [prod_comp, Mat_.comp_apply]
    rw [hH.map_sum_left, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hH.map_sum_right]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← H.map_comp]
    rfl

end MatBi

/-! ## Extension to Karoubi envelopes -/

section KarProd

variable {A : Type u₀} {B : Type u₁} {E : Type u₂} [Category.{v} A] [Category.{v} B]
  [Category.{v} E]

/-- A functor `A × B ⥤ E` extended to Karoubi envelopes:
`((X, p), (Y, q)) ↦ (H(X, Y), H(p, q))`. -/
def karProd (H : A × B ⥤ E) : Karoubi A × Karoubi B ⥤ Karoubi E where
  obj p := ⟨H.obj (p.1.X, p.2.X), H.map (X := (p.1.X, p.2.X)) (Y := (p.1.X, p.2.X)) (p.1.p, p.2.p),
    by rw [← H.map_comp, prod_comp, p.1.idem, p.2.idem]⟩
  map {p p'} φ := ⟨H.map (X := (p.1.X, p.2.X)) (Y := (p'.1.X, p'.2.X)) (φ.1.f, φ.2.f), by
    show _ = H.map _ ≫ H.map _ ≫ H.map _
    rw [← H.map_comp, ← H.map_comp, prod_comp, prod_comp, ← φ.1.comm, ← φ.2.comm]⟩
  map_id _ := Karoubi.hom_ext _ _ rfl
  map_comp φ ψ := Karoubi.hom_ext _ _ (by
    show H.map _ = H.map _ ≫ H.map _
    rw [← H.map_comp, prod_comp]
    rfl)

end KarProd

/-! ## Horizontal composition of shifted 1-morphisms -/

namespace GradedBicat

open StringDiagrams Presentation

variable {S : Signature.{u₀, u₁, u₂}} [S.IsEven] {k : Type w} [CommRing k]
  {P : Presentation.{w, v} S k} (deg : S.Gen → ℤ) {l m n : P.Bicat}

omit [S.IsEven] in
theorem hcomp_mem_homDeg {r : S.Region} {a a' b b' : Obj S} {f : P.obj a ⟶ P.obj a'}
    {g : P.obj b ⟶ P.obj b'} {d e : ℤ} (hf : f ∈ P.homDeg deg a a' d)
    (hg : g ∈ P.homDeg deg b b' e) (ha : a.start = r) (ha' : a'.start = r) :
    P.hcomp r f g ha ha' ∈ P.homDeg deg _ _ (d + e) :=
  comp_mem_homDeg (wRAt_mem_homDeg hf b ha ha') (wL_mem_homDeg a' hg)

/-- **Horizontal composition of shifted 1-morphisms** (KL III (3.18)):
`(x{t}, y{s}) ↦ (x y){t + s}`, and the horizontal composite of 2-morphisms. -/
def hcompGr : GrObj P deg l m × GrObj P deg m n ⥤ GrObj P deg l n where
  obj p := ⟨p.1.x.comp p.2.x, p.1.t + p.2.t⟩
  map {p p'} φ := ⟨P.hcomp l.region φ.1.1 φ.2.1 p.1.x.start_eq p'.1.x.start_eq,
    mem_homDeg_of_eq (hcomp_mem_homDeg deg φ.1.2 φ.2.2 _ _) (by ring)⟩
  map_id p := Subtype.ext (P.hcomp_id (p.1.x.composable p.2.x) p.1.x.start_eq)
  map_comp {p p' p''} φ ψ := Subtype.ext (P.hcomp_comp (p'.1.x.composable p.2.x) φ.1.1 ψ.1.1
    φ.2.1 ψ.2.1 p.1.x.start_eq p'.1.x.start_eq p''.1.x.start_eq)

theorem hcompGr_isBiadditive : IsBiadditive (hcompGr deg (l := l) (m := m) (n := n)) where
  map_add_left {X X' Y Y'} f f' g := Subtype.ext (by
    show P.wRAt _ (f.1 + f'.1) _ _ _ ≫ P.wL _ g.1 =
      P.wRAt _ f.1 _ _ _ ≫ P.wL _ g.1 + P.wRAt _ f'.1 _ _ _ ≫ P.wL _ g.1
    rw [P.wRAt_add, Preadditive.add_comp])
  map_add_right {X X' Y Y'} f g g' := Subtype.ext (by
    show P.wRAt _ f.1 _ _ _ ≫ P.wL _ (g.1 + g'.1) =
      P.wRAt _ f.1 _ _ _ ≫ P.wL _ g.1 + P.wRAt _ f.1 _ _ _ ≫ P.wL _ g'.1
    rw [P.wL_add, Preadditive.comp_add])

/-- **The composition functor `U̇(l, m) × U̇(m, n) ⥤ U̇(l, n)`** of KL III Definition 3.21,
induced from the horizontal composition of `U` by extension to direct sums and to the Karoubi
envelope. -/
def hcompDot : UDotHom P deg l m × UDotHom P deg m n ⥤ UDotHom P deg l n :=
  karProd (matBi (hcompGr deg) (hcompGr_isBiadditive deg))

/-- On shifted 1-morphisms `x{t}`, `y{s}` (objects with trivial idempotent), `hcompDot` gives the
object with trivial idempotent on the one-entry matrix `H(x{t}, y{s}) = (x y){t + s}`. -/
theorem hcompDot_objOf_p (x : Bicat.Hom l m) (y : Bicat.Hom m n) (t s : ℤ) :
    ((hcompDot deg).obj ((objOf x t : UDotHom P deg l m), (objOf y s : UDotHom P deg m n))).p =
      𝟙 _ := by
  ext ⟨⟨⟩, ⟨⟩⟩ ⟨⟨⟩, ⟨⟩⟩
  simp only [hcompDot, karProd, matBi, hcompGr, Mat_.id_apply_self, GrObj.id_val, objOf,
    Functor.comp_obj, toKaroubi_obj_X, toKaroubi_obj_p, Mat_.embedding_obj_X]
  exact P.hcomp_id (x.composable y) x.start_eq

end GradedBicat

end Categorification
