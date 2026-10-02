import Categorification.TwoRep.DownwardNilHeckeNormalization

/-!
# Mixed dot/crossing relations on actual downward words

Both normalized mixed relations hold at every valid position `i < n` of the
actual left-associated word `fWord n r`, which has `n + 1` factors. Positions
are counted from the right. The normalization is uniformly `-rQ⁻¹` times the
existing `fWordCross`, not a replacement family of assumed operators.

The bottom pair is transported with its genuine associator conjugation;
upper positions are propagated by right whiskering. Scalar compatibility
uses exactly the existing `GradedBicategory.IsLinear` assumption. No extra
nonvanishing assumption is needed because `rQ` is already a unit.

This supplies only the two mixed relations, not braid propagation, a full
nilHecke family, or an algebra action.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open GradedHomBicat
universe w v u
variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.ShiftCoherence B]

private def pairLift {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    {m : ℤ} (t : ShiftedHom (g ≫ h) (g ≫ h) m) :
    ShiftedHom ((f ≫ g) ≫ h) ((f ≫ g) ≫ h) m :=
  (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ f g h).hom).comp
    ((shWhiskerLeft f t).comp (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ f g h).inv)
      (zero_add m)) (add_zero m)

private theorem of₂_pairLift {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    {m : ℤ} (t : ShiftedHom (g ≫ h) (g ≫ h) m) :
    of₂ m (pairLift f g h t) =
      (α_ (of₁ f) (of₁ g) (of₁ h)).hom ≫ (of₁ f ◁ of₂ m t) ≫
        (α_ (of₁ f) (of₁ g) (of₁ h)).inv := by
  simp only [pairLift, ← of₂_comp_of₂, ← incl₂_eq_of₂, ← associator_hom_eq,
    ← associator_inv_eq, ← whiskerLeft_of₂]

private theorem pairLift_comp {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    {m n s : ℤ} (t : ShiftedHom (g ≫ h) (g ≫ h) m)
    (v : ShiftedHom (g ≫ h) (g ≫ h) n) (hs : n + m = s) :
    (pairLift f g h t).comp (pairLift f g h v) hs = pairLift f g h (t.comp v hs) := by
  apply of₂_injective s
  simp only [← of₂_comp_of₂, of₂_pairLift, Category.assoc, Iso.inv_hom_id_assoc]
  simp only [whiskerLeft_comp, Category.assoc]

private theorem pairLift_sub {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    {m : ℤ} (t v : ShiftedHom (g ≫ h) (g ≫ h) m) :
    pairLift f g h (t - v) = pairLift f g h t - pairLift f g h v := by
  apply of₂_injective m
  simp only [of₂_sub, of₂_pairLift]
  change _ ≫ whiskerLeftHom _ _ _ (of₂ m t - of₂ m v) ≫ _ = _
  rw [map_sub, Preadditive.sub_comp, Preadditive.comp_sub]
  rfl

private theorem pairLift_id {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    pairLift f g h (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (g ≫ h))) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 ((f ≫ g) ≫ h)) := by
  apply of₂_injective 0
  simp only [of₂_pairLift, ← incl₂_eq_of₂, incl₂_id]
  change (α_ (of₁ f) (of₁ g) (of₁ h)).hom ≫
    (of₁ f ◁ 𝟙 (of₁ g ≫ of₁ h)) ≫ (α_ (of₁ f) (of₁ g) (of₁ h)).inv = 𝟙 _
  rw [Bicategory.whiskerLeft_id, Category.id_comp, Iso.hom_inv_id]

omit [GradedBicategory.ShiftCoherence B] in
private theorem shWhiskerRight_sub {a b c : B} {f g : a ⟶ b} {m : ℤ}
    (t v : ShiftedHom f g m) (h : b ⟶ c) :
    shWhiskerRight (t - v) h = shWhiskerRight t h - shWhiskerRight v h := by
  simp only [shWhiskerRight, ShiftedHom.map, Functor.map_sub, Preadditive.sub_comp]
  rfl

namespace StrongSl2
variable {k : Type*} [Field k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.IsLinear B k] (S : StrongSl2 k B)

omit [GradedBicategory.ShiftCoherence B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
private theorem shWhiskerRight_smul {a b c : B} {f g : a ⟶ b} {m : ℤ}
    (t : ShiftedHom f g m) (h : b ⟶ c) (z : k) :
    shWhiskerRight (z • t) h = z • shWhiskerRight t h := by
  simp only [shWhiskerRight, ShiftedHom.map, Functor.map_smul, Linear.smul_comp]
  rfl

omit [GradedBicategory.ShiftCoherence B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
private theorem pairLift_smul {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    {m : ℤ} (t : ShiftedHom (g ≫ h) (g ≫ h) m) (z : k) :
    pairLift f g h (z • t) = z • pairLift f g h t := by
  have hh : shWhiskerLeft f (z • t) = z • shWhiskerLeft f t := by
    simp only [shWhiskerLeft, ShiftedHom.map, Functor.map_smul, Linear.smul_comp]
    rfl
  unfold pairLift
  rw [hh, ShiftedHom.smul_comp', ShiftedHom.comp_smul']

/-- The same global scalar normalization at every right-counted position. -/
def fWordNormalizedCross (n : ℕ) (r : ℤ) (i : ℕ) :
    ShiftedHom (S.fWord n r) (S.fWord n r) (-2 : ℤ) :=
  -((S.rQ : k)⁻¹) • S.fWordCross n r i

omit [GradedBicategory.ShiftCoherence B] in
private theorem normalizedCross_succ (n i : ℕ) (r : ℤ) :
    S.fWordNormalizedCross (n + 1) r (i + 1) =
      shWhiskerRight (S.fWordNormalizedCross n (r + 1) i) (S.F r) := by
  simp only [fWordNormalizedCross, fWordCross, shWhiskerRight_smul]
  rfl

omit [GradedBicategory.ShiftCoherence B] in
private theorem normalizedCross_bottom (n : ℕ) (r : ℤ) :
    S.fWordNormalizedCross (n + 2) r 0 =
      pairLift (S.fWord n (r + 1 + 1)) (S.F (r + 1)) (S.F r)
        (S.ffNormalizedCross r) := by
  change -((S.rQ : k)⁻¹) • pairLift _ _ _ (S.ffCross r) =
    pairLift _ _ _ (-((S.rQ : k)⁻¹) • S.ffCross r)
  rw [pairLift_smul]
  rfl

omit [GradedBicategory.IsLinear B k] in
private theorem dot_bottom_zero (n : ℕ) (r : ℤ) :
    S.fWordDot (n + 2) r 0 =
      pairLift (S.fWord n (r + 1 + 1)) (S.F (r + 1)) (S.F r) (S.ffDotSecond r) := by
  rw [S.ffDotSecond_eq]
  exact shWhiskerLeft_of_comp (S.fWord n (r + 1 + 1)) (S.F (r + 1)) (S.fDot r)

omit [GradedBicategory.IsLinear B k] in
private theorem dot_bottom_one (n : ℕ) (r : ℤ) :
    S.fWordDot (n + 2) r 1 =
      pairLift (S.fWord n (r + 1 + 1)) (S.F (r + 1)) (S.F r) (S.ffDotFirst r) := by
  rw [S.ffDotFirst_eq]
  exact shWhisker_assoc (S.fWord n (r + 1 + 1)) (S.fDot (r + 1)) (S.F r)

/-- The first normalized mixed relation at every valid crossing position. -/
theorem fWordNormalizedCross_x_d (n i : ℕ) (r : ℤ) (hi : i < n) :
    (S.fWordNormalizedCross n r i).comp (S.fWordDot n r i)
        (by norm_num : (2 : ℤ) + -2 = 0) -
      (S.fWordDot n r (i + 1)).comp (S.fWordNormalizedCross n r i)
        (by norm_num : (-2 : ℤ) + 2 = 0) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (S.fWord n r)) := by
  induction n generalizing r i with
  | zero => omega
  | succ n ih =>
    cases i with
    | succ i =>
      have h := congrArg (fun t : ShiftedHom (S.fWord n (r + 1))
        (S.fWord n (r + 1)) (0 : ℤ) => shWhiskerRight t (S.F r))
        (ih i (r + 1) (by omega))
      simp only [shWhiskerRight_sub, shWhiskerRight_comp,
        shWhiskerRight_mk₀, id_whiskerRight] at h
      simp only [normalizedCross_succ, fWordDot]
      exact h
    | zero =>
      cases n with
      | zero =>
        change (S.ffNormalizedCross r).comp (shWhiskerLeft (S.F (r + 1)) (S.fDot r)) _ -
          (shWhiskerRight (S.fDot (r + 1)) (S.F r)).comp (S.ffNormalizedCross r) _ = _
        rw [← S.ffDotSecond_eq, ← S.ffDotFirst_eq]
        exact S.ffNormalizedCross_x_d r
      | succ n =>
        have h := congrArg (fun t : ShiftedHom (S.F (r + 1) ≫ S.F r)
          (S.F (r + 1) ≫ S.F r) (0 : ℤ) =>
            pairLift (S.fWord n (r + 1 + 1)) (S.F (r + 1)) (S.F r) t)
          (S.ffNormalizedCross_x_d r)
        simp only [pairLift_sub, ← pairLift_comp, pairLift_id] at h
        simp only [Nat.zero_add, normalizedCross_bottom, dot_bottom_zero, dot_bottom_one]
        exact h

/-- The second normalized mixed relation at every valid crossing position. -/
theorem fWordNormalizedCross_d_x (n i : ℕ) (r : ℤ) (hi : i < n) :
    (S.fWordDot n r i).comp (S.fWordNormalizedCross n r i)
        (by norm_num : (-2 : ℤ) + 2 = 0) -
      (S.fWordNormalizedCross n r i).comp (S.fWordDot n r (i + 1))
        (by norm_num : (2 : ℤ) + -2 = 0) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (S.fWord n r)) := by
  induction n generalizing r i with
  | zero => omega
  | succ n ih =>
    cases i with
    | succ i =>
      have h := congrArg (fun t : ShiftedHom (S.fWord n (r + 1))
        (S.fWord n (r + 1)) (0 : ℤ) => shWhiskerRight t (S.F r))
        (ih i (r + 1) (by omega))
      simp only [shWhiskerRight_sub, shWhiskerRight_comp,
        shWhiskerRight_mk₀, id_whiskerRight] at h
      simp only [normalizedCross_succ, fWordDot]
      exact h
    | zero =>
      cases n with
      | zero =>
        change (shWhiskerLeft (S.F (r + 1)) (S.fDot r)).comp (S.ffNormalizedCross r) _ -
          (S.ffNormalizedCross r).comp (shWhiskerRight (S.fDot (r + 1)) (S.F r)) _ = _
        rw [← S.ffDotSecond_eq, ← S.ffDotFirst_eq]
        exact S.ffNormalizedCross_d_x r
      | succ n =>
        have h := congrArg (fun t : ShiftedHom (S.F (r + 1) ≫ S.F r)
          (S.F (r + 1) ≫ S.F r) (0 : ℤ) =>
            pairLift (S.fWord n (r + 1 + 1)) (S.F (r + 1)) (S.F r) t)
          (S.ffNormalizedCross_d_x r)
        simp only [pairLift_sub, ← pairLift_comp, pairLift_id] at h
        simp only [Nat.zero_add, normalizedCross_bottom, dot_bottom_zero, dot_bottom_one]
        exact h

/-- Native `x_d_sub` on the actual word, with positions counted from the right. -/
theorem fWordNormalizedCross_end_x_d (n i : ℕ) (r : ℤ) (hi : i < n) :
    let X₀ : End (of₁ (S.fWord n r)) := of₂ 2 (S.fWordDot n r i)
    let X₁ : End (of₁ (S.fWord n r)) := of₂ 2 (S.fWordDot n r (i + 1))
    let D : End (of₁ (S.fWord n r)) := of₂ (-2) (S.fWordNormalizedCross n r i)
    X₀ * D - D * X₁ = 1 := by
  change of₂ (-2) (S.fWordNormalizedCross n r i) ≫ of₂ 2 (S.fWordDot n r i) -
    of₂ 2 (S.fWordDot n r (i + 1)) ≫ of₂ (-2) (S.fWordNormalizedCross n r i) = 𝟙 _
  rw [of₂_comp_of₂ _ _ (by norm_num : (2 : ℤ) + -2 = 0),
    of₂_comp_of₂ _ _ (by norm_num : (-2 : ℤ) + 2 = 0), ← of₂_sub,
    S.fWordNormalizedCross_x_d n i r hi, ← incl₂_eq_of₂, incl₂_id]

/-- Native `d_x_sub` on the actual word, with the same global normalization. -/
theorem fWordNormalizedCross_end_d_x (n i : ℕ) (r : ℤ) (hi : i < n) :
    let X₀ : End (of₁ (S.fWord n r)) := of₂ 2 (S.fWordDot n r i)
    let X₁ : End (of₁ (S.fWord n r)) := of₂ 2 (S.fWordDot n r (i + 1))
    let D : End (of₁ (S.fWord n r)) := of₂ (-2) (S.fWordNormalizedCross n r i)
    D * X₀ - X₁ * D = 1 := by
  change of₂ 2 (S.fWordDot n r i) ≫ of₂ (-2) (S.fWordNormalizedCross n r i) -
    of₂ (-2) (S.fWordNormalizedCross n r i) ≫ of₂ 2 (S.fWordDot n r (i + 1)) = 𝟙 _
  rw [of₂_comp_of₂ _ _ (by norm_num : (-2 : ℤ) + 2 = 0),
    of₂_comp_of₂ _ _ (by norm_num : (2 : ℤ) + -2 = 0), ← of₂_sub,
    S.fWordNormalizedCross_d_x n i r hi, ← incl₂_eq_of₂, incl₂_id]

end StrongSl2
end Categorification.TwoRep
