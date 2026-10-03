import Categorification.TwoRep.DownwardNilHeckeSlides
import Categorification.KLR.Examples.NilHecke

/-!
# Braid on actual downward words

The local braid is propagated through the genuine associators and right whiskering.
The word `fWord n r` has `n + 1` factors, with positions counted from the right.
The normalized operators are the existing uniform `-rQ⁻¹` rescaling. Together with
the previously established relations, they give `fWord_isNilHeckeFamily` on every
nonempty word. Supplied adjunctions and graded coherence/linearity remain explicit;
this does not prove automatic biadjointness or the unrestricted Cautis–Lauda theorem.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open GradedHomBicat
universe w v u

private def tripleIso {D : Type*} [Bicategory D] {a b c d e : D}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    ((f ≫ g) ≫ h) ≫ i ≅ f ≫ ((g ≫ h) ≫ i) :=
  whiskerRightIso (α_ f g h) i ≪≫ α_ f (g ≫ h) i

private theorem triple_left {D : Type*} [Bicategory D] {a b c d e : D}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) (t : g ≫ h ⟶ g ≫ h) :
    ((α_ f g h).hom ≫ (f ◁ t) ≫ (α_ f g h).inv) ▷ i =
      (tripleIso f g h i).hom ≫ (f ◁ (t ▷ i)) ≫ (tripleIso f g h i).inv := by
  simp only [tripleIso, Iso.trans_hom, Iso.trans_inv, whiskerRightIso_hom,
    whiskerRightIso_inv, comp_whiskerRight, Category.assoc]
  rw [← associator_naturality_middle_assoc, Iso.hom_inv_id_assoc]

private theorem triple_right {D : Type*} [Bicategory D] {a b c d e : D}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) (t : h ≫ i ⟶ h ≫ i) :
    (α_ (f ≫ g) h i).hom ≫ ((f ≫ g) ◁ t) ≫ (α_ (f ≫ g) h i).inv =
      (tripleIso f g h i).hom ≫
        (f ◁ ((α_ g h i).hom ≫ (g ◁ t) ≫ (α_ g h i).inv)) ≫
        (tripleIso f g h i).inv := by
  simp only [tripleIso, Iso.trans_hom, Iso.trans_inv, whiskerRightIso_hom,
    whiskerRightIso_inv, whiskerLeft_comp, Category.assoc]
  rw [pentagon_assoc, ← associator_naturality_right_assoc,
    pentagon_hom_inv_inv_inv_hom_assoc]
  simp only [← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight, Category.comp_id]

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.ShiftCoherence B]
namespace StrongSl2
variable {k : Type*} [Field k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  (S : StrongSl2 k B)

/-- The original homogeneous braid at every valid right-counted position. -/
theorem fWordCross_braid (n j : ℕ) (r : ℤ) (hj : j + 1 < n) :
    ((S.fWordCross n r j).comp (S.fWordCross n r (j + 1))
      (by norm_num : (-2 : ℤ) + -2 = -4)).comp (S.fWordCross n r j)
      (by norm_num : (-2 : ℤ) + -4 = -6) =
    ((S.fWordCross n r (j + 1)).comp (S.fWordCross n r j)
      (by norm_num : (-2 : ℤ) + -2 = -4)).comp (S.fWordCross n r (j + 1))
      (by norm_num : (-2 : ℤ) + -4 = -6) := by
  induction n generalizing r j with
  | zero => omega
  | succ n ih =>
    cases j with
    | succ j =>
      simpa only [fWordCross, fWord, shWhiskerRight_comp] using
        congrArg (fun t => shWhiskerRight t (S.F r)) (ih j (r + 1) (by omega))
    | zero =>
      cases n with
      | zero => omega
      | succ n =>
        cases n with
        | zero => exact (S.fffCross_braid r).symm
        | succ n =>
          apply of₂_injective (-6)
          let f := of₁ (S.fWord n (r + 1 + 1 + 1))
          let g := of₁ (S.F (r + 1 + 1))
          let h := of₁ (S.F (r + 1))
          let i := of₁ (S.F r)
          have hh := congrArg (fun t => (tripleIso f g h i).hom ≫
            (f ◁ of₂ (-6) t) ≫ (tripleIso f g h i).inv)
            (S.fffCross_braid r).symm
          simp only [← of₂_comp_of₂, whiskerLeft_comp] at hh
          simp only [fWordCross, fWordBottomCross, fWord, ← of₂_comp_of₂,
            ← incl₂_eq_of₂, ← associator_hom_eq, ← associator_inv_eq,
            ← whiskerLeft_of₂, ← of₂_whiskerRight]
          simp only [← of₁_comp]
          simp only [triple_right, triple_left]
          simpa only [fffCrossLeft, fffCrossRight, ← of₂_comp_of₂,
            ← incl₂_eq_of₂, ← associator_hom_eq, ← associator_inv_eq,
            ← whiskerLeft_of₂, ← of₂_whiskerRight, Category.assoc,
            Iso.inv_hom_id_assoc] using hh

variable [GradedBicategory.IsLinear B k]

/-- Uniform scalar normalization preserves braid; zero extension covers every index. -/
theorem fWordNormalizedCross_braid (n j : ℕ) (r : ℤ) :
    ((S.fWordNormalizedCross n r j).comp (S.fWordNormalizedCross n r (j + 1))
      (by norm_num : (-2 : ℤ) + -2 = -4)).comp (S.fWordNormalizedCross n r j)
      (by norm_num : (-2 : ℤ) + -4 = -6) =
    ((S.fWordNormalizedCross n r (j + 1)).comp (S.fWordNormalizedCross n r j)
      (by norm_num : (-2 : ℤ) + -2 = -4)).comp (S.fWordNormalizedCross n r (j + 1))
      (by norm_num : (-2 : ℤ) + -4 = -6) := by
  simp only [fWordNormalizedCross, ShiftedHom.smul_comp', ShiftedHom.comp_smul']
  by_cases hj : j + 1 < n
  · rw [S.fWordCross_braid n j r hj]
  · rw [S.fWordCross_eq_zero n (j + 1) r (by omega)]
    simp only [ShiftedHom.comp_zero, ShiftedHom.zero_comp, smul_zero]

/-- Native endomorphism-ring braid for the actual globally normalized operators. -/
theorem fWordNormalizedCross_end_braid (n j : ℕ) (r : ℤ) :
    let D : ℕ → End (of₁ (S.fWord n r)) :=
      fun i => of₂ (-2) (S.fWordNormalizedCross n r i)
    D j * D (j + 1) * D j = D (j + 1) * D j * D (j + 1) := by
  change of₂ (-2) (S.fWordNormalizedCross n r j) ≫
      (of₂ (-2) (S.fWordNormalizedCross n r (j + 1)) ≫
        of₂ (-2) (S.fWordNormalizedCross n r j)) =
    of₂ (-2) (S.fWordNormalizedCross n r (j + 1)) ≫
      (of₂ (-2) (S.fWordNormalizedCross n r j) ≫
        of₂ (-2) (S.fWordNormalizedCross n r (j + 1)))
  simp only [← Category.assoc]
  rw [of₂_comp_of₂ _ _ (by norm_num : (-2 : ℤ) + -2 = -4),
    of₂_comp_of₂ _ _ (by norm_num : (-2 : ℤ) + -2 = -4),
    of₂_comp_of₂ _ _ (by norm_num : (-2 : ℤ) + -4 = -6),
    of₂_comp_of₂ _ _ (by norm_num : (-2 : ℤ) + -4 = -6),
    S.fWordNormalizedCross_braid]

/-- The existing dots and uniformly normalized crossings form a nilHecke family
on every nonempty actual downward word. This makes no automatic biadjointness claim. -/
theorem fWord_isNilHeckeFamily (n : ℕ) (r : ℤ) :
    KLR.NilHecke.IsNilHeckeFamily (B := End (of₁ (S.fWord n r))) (n + 1)
      (fun a : Fin (n + 1) => (of₂ 2 (S.fWordDot n r a.val) : End (of₁ (S.fWord n r))))
      (fun j => of₂ (-2) (S.fWordNormalizedCross n r j)) where
  x_comm a b := by
    change of₂ 2 (S.fWordDot n r b.val) ≫ of₂ 2 (S.fWordDot n r a.val) =
      of₂ 2 (S.fWordDot n r a.val) ≫ of₂ 2 (S.fWordDot n r b.val)
    simp only [of₂_comp_of₂ _ _ (by norm_num : (2 : ℤ) + 2 = 4)]
    rw [S.fWordDot_comm]
  d_x_comm j a h₀ h₁ := by
    change of₂ 2 (S.fWordDot n r a.val) ≫ of₂ (-2) (S.fWordNormalizedCross n r j) =
      of₂ (-2) (S.fWordNormalizedCross n r j) ≫ of₂ 2 (S.fWordDot n r a.val)
    rw [of₂_comp_of₂ _ _ (by norm_num : (-2 : ℤ) + 2 = 0),
      of₂_comp_of₂ _ _ (by norm_num : (2 : ℤ) + -2 = 0)]
    simp only [fWordNormalizedCross, ShiftedHom.smul_comp', ShiftedHom.comp_smul']
    rw [S.fWordCross_dot_comm n j a.val r h₀ h₁]
  d_comm j l h := by
    change of₂ (-2) (S.fWordNormalizedCross n r l) ≫
        of₂ (-2) (S.fWordNormalizedCross n r j) =
      of₂ (-2) (S.fWordNormalizedCross n r j) ≫
        of₂ (-2) (S.fWordNormalizedCross n r l)
    simp only [of₂_comp_of₂ _ _ (by norm_num : (-2 : ℤ) + -2 = -4),
      fWordNormalizedCross, ShiftedHom.smul_comp', ShiftedHom.comp_smul']
    rw [S.fWordCross_comm n j l r h]
  d_sq j := by
    change of₂ (-2) (S.fWordNormalizedCross n r j) ≫
      of₂ (-2) (S.fWordNormalizedCross n r j) = 0
    rw [of₂_comp_of₂ _ _ (by norm_num : (-2 : ℤ) + -2 = -4)]
    simp only [fWordNormalizedCross, ShiftedHom.smul_comp', ShiftedHom.comp_smul',
      S.fWordCross_sq, smul_zero, of₂_zero]
  braid j := S.fWordNormalizedCross_end_braid n j r
  x_d_sub j h := S.fWordNormalizedCross_end_x_d n j r (by omega)
  d_x_sub j h := S.fWordNormalizedCross_end_d_x n j r (by omega)
  d_zero j h := by
    simp only [fWordNormalizedCross, S.fWordCross_eq_zero n j r (by omega),
      smul_zero, of₂_zero]

end StrongSl2
end Categorification.TwoRep
