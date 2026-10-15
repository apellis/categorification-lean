/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqCoproduct

/-!
# The `sl₂` coproduct: the block through the identity, nonpositive total weight

The mirror of `RouqCoproduct.isIso_rouqMap_of_nonneg`. Let finitely many labels `a` each carry
Rouquier's `sl₂` data at a common object `b` (`RouqLoc`; J. Brundan, *On the definition of
Kac–Moody 2-category*, arXiv:1501.00350v1, Definition 1.1) of weight `h a`, with nilpotent dots,
in a `k`-linear bicategory. Shift the dots of label `a` by pairwise distinct scalars `u a ∈ k`. For
`M = -∑ₐ h a ≥ 0`, the block of Rouquier's map for `E = ⊞ₐ Eₐ`

  `⊞ₐ Eₐ Fₐ 1_b ⊕ 1_b^{⊕ M} → ⊞ₐ Fₐ Eₐ 1_b`

is invertible (`RouqCoproduct.isIso_rouqMap_of_nonpos`). Its entries are the labelwise rightward
crossings, the rightward crossings of the inverses of the dumbbells, and the cups of label `a`
with `t` shifted dots `(u_a + x_a)ᵗ`. This is the block-`(2)` part of KM3 for the coproduct of
`sl₂` data, for nonpositive weights (B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*,
arXiv:1603.06311v3, Theorem `th:coproduct`; J. Brundan, A. Savage, B. Webster,
arXiv:1812.03255v3, §5, Theorem 5.4).

**Proof.** As for nonnegative weights, by a matrix argument: Gaussian elimination against the
labelwise inverses, after which the Schur complement is, modulo nilpotent closed diagrams, the
transpose of the partial-fraction matrix `crtMatrix` (for the reversed roles of the labels with
positive and negative weight) with its second column block negated (`telCoeff_neg_swap`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits Finset

open scoped Matrix

universe w v u

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-! ## A symmetry of the teleporter coefficients -/

section Tel

variable {k : Type*} [Field k]

/-- `1 / (-d + w - z) = -1 / (d + z - w)`: `telCoeff (-d) j i = -telCoeff d i j`. -/
theorem telCoeff_neg_swap {d : k} (hd : d ≠ 0) (i j : ℕ) :
    telCoeff (-d) j i = -telCoeff d i j := by
  induction hn : i + j using Nat.strong_induction_on generalizing i j with
  | _ n ih =>
    have r1 := telCoeff_rec hd i j
    have r2 := telCoeff_rec (neg_ne_zero.mpr hd) j i
    have key : -d * telCoeff (-d) j i = -d * -telCoeff d i j := by
      rcases Nat.eq_zero_or_pos i with hi | hi <;> rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hi hj
        simp only [ite_true] at r1 r2
        linear_combination r2 - r1
      · subst hi
        have e := ih (0 + (j - 1)) (by omega) 0 (j - 1) rfl
        simp only [ite_true, (show j ≠ 0 by omega), ite_false, add_zero] at r1 r2
        linear_combination r2 - r1 - e
      · subst hj
        have e := ih (i - 1 + 0) (by omega) (i - 1) 0 rfl
        simp only [ite_true, (show i ≠ 0 by omega), ite_false, add_zero] at r1 r2
        linear_combination r2 - r1 + e
      · have e1 := ih (i - 1 + j) (by omega) (i - 1) j rfl
        have e2 := ih (i + (j - 1)) (by omega) i (j - 1) rfl
        simp only [(show i ≠ 0 by omega), (show j ≠ 0 by omega), ite_false] at r1 r2
        linear_combination r2 - r1 + e1 - e2
    exact mul_left_cancel₀ (neg_ne_zero.mpr hd) key

end Tel

/-! ## Gaussian elimination, mirrored -/

section Biprod

variable {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts D]

/-- A map `(f, c) : X ⊞ T ⟶ Y` is invertible if its extension
`[[f, g], [fst ≫ c, snd]] : X ⊞ (T ⊞ S) ⟶ Y ⊞ S` is. -/
theorem isIso_desc_of_isIso_ofComponents {X S Y T : D} (f : X ⟶ Y) (c : T ⟶ Y) (g : X ⟶ S)
    (h : IsIso (Biprod.ofComponents f g (biprod.fst ≫ c) (biprod.snd : T ⊞ S ⟶ S))) :
    IsIso (biprod.desc f c) := by
  set Mh := Biprod.ofComponents f g (biprod.fst ≫ c) (biprod.snd : T ⊞ S ⟶ S)
  set K : X ⊞ (T ⊞ S) ⟶ X ⊞ T := biprod.map (𝟙 X) biprod.fst
  set J : X ⊞ T ⟶ X ⊞ (T ⊞ S) := biprod.map (𝟙 X) biprod.inl
  have h1 : Mh ≫ biprod.fst = K ≫ biprod.desc f c := by
    apply biprod.hom_ext' <;> simp [Mh, K, Biprod.ofComponents]
  have h2 : (biprod.inr ≫ biprod.inr : S ⟶ X ⊞ (T ⊞ S)) ≫ Mh = biprod.inr := by
    simp [Mh, Biprod.ofComponents]
  have h3 : biprod.inr ≫ inv Mh = (biprod.inr ≫ biprod.inr : S ⟶ X ⊞ (T ⊞ S)) := by
    rw [← h2, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hJK : J ≫ K = 𝟙 _ := by
    apply biprod.hom_ext' <;> simp [J, K]
  have h0 : (biprod.inr ≫ biprod.inr : S ⟶ X ⊞ (T ⊞ S)) ≫ K = 0 := by simp [K]
  have hJ : J ≫ Mh = biprod.desc f c ≫ biprod.inl + (J ≫ Mh ≫ biprod.snd) ≫ biprod.inr := by
    have e : J ≫ Mh = J ≫ Mh ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) := by
      rw [biprod.total, Category.comp_id]
    rw [e, Preadditive.comp_add, Preadditive.comp_add, reassoc_of% h1, ← Category.assoc J K,
      hJK, Category.id_comp]
    simp only [Category.assoc]
  refine ⟨⟨biprod.inl ≫ inv Mh ≫ K, ?_, ?_⟩⟩
  · have e1 : biprod.desc f c ≫ biprod.inl = J ≫ Mh - (J ≫ Mh ≫ biprod.snd) ≫ biprod.inr := by
      rw [hJ]; abel
    calc biprod.desc f c ≫ biprod.inl ≫ inv Mh ≫ K
        = (biprod.desc f c ≫ biprod.inl) ≫ inv Mh ≫ K := by simp only [Category.assoc]
      _ = (J ≫ Mh - (J ≫ Mh ≫ biprod.snd) ≫ biprod.inr) ≫ inv Mh ≫ K := by rw [e1]
      _ = J ≫ K - (J ≫ Mh ≫ biprod.snd) ≫ (biprod.inr ≫ inv Mh) ≫ K := by
        simp only [Preadditive.sub_comp, Category.assoc, IsIso.hom_inv_id_assoc]
      _ = 𝟙 _ := by rw [h3, h0, Limits.comp_zero, sub_zero, hJK]
  · rw [Category.assoc, Category.assoc, ← h1, IsIso.inv_hom_id_assoc, biprod.inl_fst]

end Biprod

namespace RouqCoproduct

/-! ## The setting -/

section Setting

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [AdditiveWhiskering B]
  {A : Type} [Fintype A] [DecidableEq A] {b : B} {src tgt : A → B}
  {E₁ : ∀ a, src a ⟶ b} {R₁ : ∀ a, b ⟶ src a} {E₂ : ∀ a, b ⟶ tgt a} {R₂ : ∀ a, tgt a ⟶ b}
  {adj₁ : ∀ a, E₁ a ⊣ R₁ a} {adj₂ : ∀ a, E₂ a ⊣ R₂ a}
  {x₁ : ∀ a, E₁ a ⟶ E₁ a} {x₂ : ∀ a, E₂ a ⟶ E₂ a}
  {τ : ∀ a, E₁ a ≫ E₂ a ⟶ E₁ a ≫ E₂ a} {h : A → ℤ}
  (L : ∀ a, RouqLoc (adj₁ a) (adj₂ a) (x₁ a) (x₂ a) (τ a) (h a))
  {k : Type*} [Field k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]

variable (b) in
/-- The binomial coefficients `[yʲ] (u_c + y)ᵗ`, for the cups. -/
def wMatT (u : A → k) (n M : ℕ) : oMat (𝟙 b) (Fin M) ⟶ oMat (𝟙 b) (A × Fin n) :=
  fun t q => (((t : ℕ).choose q.2 : k) * u q.1 ^ ((t : ℕ) - q.2)) • 𝟙 (𝟙 b)

/-- **The cups with shifted dots** `(u_c + y_c)ᵗ`, `t < M`. -/
def rouqCups (u : A → k) (M : ℕ) : oMat (𝟙 b) (Fin M) ⟶ objFE L :=
  fun t c => (adj₂ c).unit ≫ powComp (u c • 𝟙 (E₂ c) + x₂ c) t ▷ R₂ c

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
/-- **The cup with `t` shifted dots**: `η ≫ (s + y)ᵗ ▷ R = ∑ⱼ (t choose j) sᵗ⁻ʲ • η ≫ yʲ ▷ R`. -/
theorem unit_powComp_shift {c d : B} {E : c ⟶ d} {R : d ⟶ c} (adj : E ⊣ R) (s : k) (y : E ⟶ E)
    (t : ℕ) :
    adj.unit ≫ powComp (s • 𝟙 E + y) t ▷ R =
      ∑ j ∈ range (t + 1), ((t.choose j : k) * s ^ (t - j)) • (adj.unit ≫ powComp y j ▷ R) := by
  rw [powComp_add_smul_id,
    show (∑ j ∈ range (t + 1), ((t.choose j : k) * s ^ (t - j)) • powComp y j) ▷ R =
      ∑ j ∈ range (t + 1), (((t.choose j : k) * s ^ (t - j)) • powComp y j) ▷ R from
      map_sum (AdditiveWhiskering.whiskerRightAddHom E E R) _ _, Preadditive.comp_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [smul_whiskerRight', Linear.comp_smul]

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
/-- The cups with shifted dots in terms of the dotted cups, for `M ≤ n`. -/
theorem rouqCups_eq {n M : ℕ} (hM : M ≤ n) (u : A → k) :
    rouqCups L u M = wMatT b u n M ≫ cupAll L n := by
  refine Mat_.hom_ext _ _ fun t c => ?_
  rw [comp_cupAll_apply]
  simp only [wMatT, Linear.smul_comp, Category.id_comp]
  change (adj₂ c).unit ≫ powComp (u c • 𝟙 (E₂ c) + x₂ c) t ▷ R₂ c = _
  rw [unit_powComp_shift, Fin.sum_univ_eq_sum_range
    (fun j => (((t : ℕ).choose j : k) * u c ^ ((t : ℕ) - j)) • (L c).cupD j) n]
  refine Finset.sum_subset (fun j hj => ?_) (fun j _ hj => ?_)
  · simp only [Finset.mem_range] at hj ⊢; omega
  · simp only [Finset.mem_range, not_lt] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_smul]

/-! ### The signed transpose of the partial-fraction matrix -/

section SignedCRT

variable {k : Type*} [Field k] (u : A → k) (hp hn : A → ℕ) (M : ℕ)

/-- The signs `1` on `Fin M` and `-1` on the second block. -/
def signDiag : Matrix (Fin M ⊕ Σ a, Fin (hn a)) (Fin M ⊕ Σ a, Fin (hn a)) k :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))

theorem signDiag_mul_signDiag : signDiag hn M * signDiag (k := k) hn M = 1 := by
  rw [signDiag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext y
  rcases y with t | r <;> simp

/-- The signed transpose `S · crtᵀ` of the partial-fraction matrix. -/
def signedCrt : Matrix (Fin M ⊕ Σ e, Fin (hn e)) (Σ a, Fin (hp a)) k :=
  Matrix.of fun y x => Sum.elim (fun _ => 1) (fun _ => -1) y * crtMatrix u hp hn M x y

theorem signedCrt_eq :
    signedCrt u hp hn M =
      ((signDiag hn M : Matrix (Fin M ⊕ Σ e, Fin (hn e)) (Fin M ⊕ Σ e, Fin (hn e)) k) *
        ((crtMatrix u hp hn M)ᵀ : Matrix (Fin M ⊕ Σ e, Fin (hn e)) (Σ a, Fin (hp a)) k) :
          Matrix (Fin M ⊕ Σ e, Fin (hn e)) (Σ a, Fin (hp a)) k) := by
  ext y x
  rw [signDiag, Matrix.diagonal_mul]
  rfl

/-- The signed transpose of the partial-fraction matrix is invertible. -/
theorem signedCrt_exists_inv (hu : Function.Injective u)
    (hdisj : ∀ a, hp a = 0 ∨ hn a = 0) (hN : ∑ a, hp a = M + ∑ a, hn a) :
    ∃ D : Matrix (Σ a, Fin (hp a)) (Fin M ⊕ Σ e, Fin (hn e)) k,
      signedCrt u hp hn M * D = 1 ∧ D * signedCrt u hp hn M = 1 := by
  obtain ⟨D, hCD, hDC⟩ := crtMatrix_exists_inv (u := u) (hp := hp) (hn := hn) (N := M) hu hdisj hN
  refine ⟨((Matrix.transpose D : Matrix (Σ a, Fin (hp a)) (Fin M ⊕ Σ e, Fin (hn e)) k) *
    (signDiag hn M : Matrix (Fin M ⊕ Σ e, Fin (hn e)) (Fin M ⊕ Σ e, Fin (hn e)) k) :
      Matrix (Σ a, Fin (hp a)) (Fin M ⊕ Σ e, Fin (hn e)) k), ?_, ?_⟩
  · rw [signedCrt_eq, Matrix.mul_assoc, ← Matrix.mul_assoc _ Dᵀ, ← Matrix.transpose_mul, hDC,
      Matrix.transpose_one, Matrix.one_mul, signDiag_mul_signDiag]
  · rw [signedCrt_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (signDiag hn M), signDiag_mul_signDiag,
      Matrix.one_mul, ← Matrix.transpose_mul, hCD, Matrix.transpose_one]

end SignedCRT

/-! ### Elimination -/

section Main

attribute [local instance] endIdCommRing

variable {n : ℕ} (hx₁ : ∀ a, powComp (x₁ a) n = 0) (hx₂ : ∀ a, powComp (x₂ a) n = 0)
  (hn : ∀ a, (h a).natAbs ≤ n)

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- The constant part of the Schur complement is the signed transpose of the partial-fraction
matrix, for the labels of negative weight in the role of those of positive weight. -/
theorem schur_const_neg_eq {M : ℕ} {u : A → k} (hu : Function.Injective u) :
    ((Matrix.fromRows 1 0 : Matrix (Fin M ⊕ Pos h) (Fin M) (End (𝟙 b))) *
        (oMat.toMatrix (wMatT b u n M) * matE0 b hn) -
      ((Matrix.fromRows 1 0 : Matrix (Fin M ⊕ Pos h) (Fin M) (End (𝟙 b))) *
          (oMat.toMatrix (wMatT b u n M) * ((0 : Matrix (A × Fin n) (A × Fin n) (End (𝟙 b))) *
            ((1 : Matrix (A × Fin n) (A × Fin n) (End (𝟙 b))) *
              (oMat.toMatrix (tel b u n) * matE0 b hn)))) +
        (Matrix.fromRows 0 1 : Matrix (Fin M ⊕ Pos h) (Pos h) (End (𝟙 b))) *
          (matB0 b hn * ((1 : Matrix (A × Fin n) (A × Fin n) (End (𝟙 b))) *
            (oMat.toMatrix (tel b u n) * matE0 b hn)))) :
        Matrix (Fin M ⊕ Pos h) (Neg h) (End (𝟙 b))) =
      (signedCrt u (fun a => (-h a).toNat) (fun a => (h a).toNat) M).map
        (algebraMap k (End (𝟙 b))) := by
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, Matrix.fromRows_mul]
  ext y r
  rcases y with t | p
  · simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.fromRows_apply_inl, Matrix.zero_apply,
      add_zero, sub_zero, mul_matE0_apply, Matrix.map_apply, signedCrt,
      Sum.elim_inl, one_mul, crtMatrix, Matrix.of_apply,
      Algebra.algebraMap_eq_smul_one]
    rfl
  · simp only [Matrix.sub_apply, Matrix.fromRows_apply_inr, Matrix.zero_apply,
      zero_add, zero_sub, matB0_mul_apply, mul_matE0_apply, Matrix.map_apply, signedCrt,
      Sum.elim_inr, neg_mul, one_mul, crtMatrix, Matrix.of_apply,
      Algebra.algebraMap_eq_smul_one]
    have hpr : p.1 ≠ r.1 := by
      obtain ⟨a, m⟩ := p
      obtain ⟨c, m'⟩ := r
      rintro (rfl : a = c)
      have := m.2
      have := m'.2
      omega
    have hd : u r.1 - u p.1 ≠ 0 := sub_ne_zero.mpr fun e => hpr (hu e).symm
    change -(if p.1 = r.1 then 0 else _) = _
    rw [ite_eq_right hpr, neg_smul, neg_neg, ← telCoeff_neg_swap hd, neg_sub]
    rfl

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
include hx₁ hx₂ hn in
/-- **Block `(2)`, with teleporters**: for `∑ₐ h a ≤ 0`, the map
`(σ + cap ∘ teleporter ∘ cup, binomials ∘ cup) : ⊞ Eₐ Fₐ ⊕ 1^{⊕ M} → ⊞ Fₐ Eₐ` is invertible. -/
theorem isIso_desc_teleporter {u : A → k} (hu : Function.Injective u) (hN : ∑ a, h a ≤ 0) :
    IsIso (biprod.desc (sigD L + capAll L n ≫ tel b u n ≫ cupAll L n)
      (wMatT b u n (-∑ a, h a).toNat ≫ cupAll L n)) := by
  set M := (-∑ a, h a).toNat with hMdef
  set T := tel b u n
  set W := wMatT b u n M
  refine isIso_desc_of_isIso_ofComponents _ _ (capP L) ?_
  suffices hΨ : IsIso (Biprod.ofComponents (sigD L + capAll L n ≫ T ≫ cupAll L n) (capP L)
      (biprod.fst ≫ W ≫ cupAll L n) (biprod.snd : oMat (𝟙 b) (Fin M) ⊞ oMat (𝟙 b) (Pos h) ⟶ _) ≫
        phiInv L) from IsIso.of_isIso_comp_right _ (phiInv L)
  have e11 : (sigD L + capAll L n ≫ T ≫ cupAll L n) ≫ (-sigLD L) + capP L ≫ cupNP L =
      𝟙 _ + capAll L n ≫ T ≫ cupAll L n ≫ (-sigLD L) := by
    rw [Preadditive.add_comp, add_right_comm, sigD_sigLD L]
    simp only [Category.assoc]
  have e12 : (sigD L + capAll L n ≫ T ≫ cupAll L n) ≫ capNM L +
      capP L ≫ (0 : oMat (𝟙 b) (Pos h) ⟶ oMat (𝟙 b) (Neg h)) = capAll L n ≫ T ≫ gamM L n := by
    rw [Limits.comp_zero, add_zero, Preadditive.add_comp, sigD_capNM, zero_add, gamM]
    simp only [Category.assoc]
  have e21 : (biprod.fst ≫ W ≫ cupAll L n) ≫ (-sigLD L) +
      (biprod.snd : oMat (𝟙 b) (Fin M) ⊞ oMat (𝟙 b) (Pos h) ⟶ _) ≫ cupNP L =
      biprod.fst ≫ W ≫ cupAll L n ≫ (-sigLD L) + biprod.snd ≫ cupNP L := by
    simp only [Category.assoc]
  have e22 : (biprod.fst ≫ W ≫ cupAll L n) ≫ capNM L +
      (biprod.snd : oMat (𝟙 b) (Fin M) ⊞ oMat (𝟙 b) (Pos h) ⟶ _) ≫
        (0 : oMat (𝟙 b) (Pos h) ⟶ oMat (𝟙 b) (Neg h)) =
      biprod.fst ≫ W ≫ gamM L n := by
    rw [Limits.comp_zero, add_zero, gamM]
    simp only [Category.assoc]
  rw [phiInv, Biprod.ofComponents_comp, e11, e12, e21, e22]
  -- the `(1,1)` block is unipotent
  have hgam := matNil_gam L hx₁ hx₂
  have hTgam : IsNilpotent (R := End (oMat (𝟙 b) (A × Fin n))) (T ≫ gam L n) :=
    isNilpotent_of_matNil _ (by
      rw [oMat_comp_toMatrix endId_hcomm]; exact MatNil.mul_left _ hgam)
  have hΨ₁₁ : IsIso (𝟙 (objEF L) + capAll L n ≫ T ≫ cupAll L n ≫ (-sigLD L)) :=
    isIso_id_add_of_isNilpotent _ (isNilpotent_comp_swap (capAll L n) _ (by
      simpa only [gam, Category.assoc] using hTgam))
  have hG : IsIso (𝟙 _ + T ≫ gam L n) := isIso_id_add_of_isNilpotent _ hTgam
  refine isIso_ofComponents_of_isIso_schur _ _ _ _ ?_
  -- push the inverse of the `(1,1)` block through the caps
  have hpush : inv (𝟙 (objEF L) + capAll L n ≫ T ≫ cupAll L n ≫ (-sigLD L)) ≫ capAll L n =
      capAll L n ≫ inv (𝟙 _ + T ≫ gam L n) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.id_comp, Category.comp_id,
      gam, Category.assoc]
  have hS : biprod.fst ≫ W ≫ gamM L n - (biprod.fst ≫ W ≫ cupAll L n ≫ (-sigLD L) +
      (biprod.snd : oMat (𝟙 b) (Fin M) ⊞ oMat (𝟙 b) (Pos h) ⟶ _) ≫ cupNP L) ≫
        inv (𝟙 (objEF L) + capAll L n ≫ T ≫ cupAll L n ≫ (-sigLD L)) ≫
          capAll L n ≫ T ≫ gamM L n =
      biprod.fst ≫ W ≫ gamM L n - (biprod.fst ≫ W ≫ gam L n + biprod.snd ≫ bet L n) ≫
        inv (𝟙 _ + T ≫ gam L n) ≫ T ≫ gamM L n := by
    rw [reassoc_of% hpush]
    simp only [gam, bet, Preadditive.add_comp, Category.assoc]
  rw [hS]
  -- pass to matrices
  rw [← isIso_comp_left_iff (sumIso b (Fin M) (Pos h)).inv]
  -- the inverse of the signed partial-fraction matrix
  have hdisj : ∀ a, (-h a).toNat = 0 ∨ (h a).toNat = 0 := fun a => by omega
  have hM' : ∑ a, (-h a).toNat = M + ∑ a, (h a).toNat := by
    have e : ∀ a, ((-h a).toNat : ℤ) = -h a + ((h a).toNat : ℤ) := fun a => by omega
    zify
    rw [hMdef, Int.toNat_of_nonneg (by omega)]
    simp only [e, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  obtain ⟨Dk, hCD, hDC⟩ := signedCrt_exists_inv u (fun a => (-h a).toNat) (fun a => (h a).toNat)
    M hu hdisj hM'
  let φ := algebraMap k (End (𝟙 b))
  refine isIso_of_nilEq _
    (C := (signedCrt u (fun a => (-h a).toNat) (fun a => (h a).toNat) M).map φ)
    (Dm := Dk.map φ) (by rw [← Matrix.map_mul, hCD, Matrix.map_one _ (map_zero φ) (map_one φ)])
    (by rw [← Matrix.map_mul, hDC, Matrix.map_one _ (map_zero φ) (map_one φ)]) ?_
  rw [← schur_const_neg_eq hn hu]
  simp only [sumIso, Preadditive.add_comp, Preadditive.comp_sub, Preadditive.comp_add,
    Category.assoc, biprod.lift_fst_assoc, biprod.lift_snd_assoc, toMatrix_sub, toMatrix_add,
    oMat_comp_toMatrix endId_hcomm, toMatrix_ofMatrix]
  -- the inverse of the unipotent block is congruent to `1`
  have hGi : NilEq (oMat.toMatrix (inv (𝟙 _ + T ≫ gam L n))) 1 := by
    have h1 := congrArg oMat.toMatrix (IsIso.inv_hom_id (𝟙 _ + T ≫ gam L n))
    rw [oMat_comp_toMatrix endId_hcomm, toMatrix_add, toMatrix_id,
      oMat_comp_toMatrix endId_hcomm] at h1
    rw [Matrix.mul_add, Matrix.mul_one] at h1
    have h2 : oMat.toMatrix (inv (𝟙 _ + T ≫ gam L n)) - 1 =
        -(oMat.toMatrix (inv (𝟙 _ + T ≫ gam L n)) *
          (oMat.toMatrix T * oMat.toMatrix (gam L n))) :=
      eq_neg_of_add_eq_zero_left (by rw [sub_add_eq_add_sub, h1, sub_self])
    unfold NilEq
    rw [h2]
    exact MatNil.neg (MatNil.mul_left _ (MatNil.mul_left _ hgam))
  have hgam0 : NilEq (oMat.toMatrix (gam L n)) 0 := by
    unfold NilEq; rw [sub_zero]; exact hgam
  have hB := nilEq_bet L hx₁ hx₂ hn
  have hE := nilEq_gamM L hx₁ hx₂ hn
  exact NilEq.sub (NilEq.mul (NilEq.refl _) (NilEq.mul (NilEq.refl _) hE))
    (NilEq.add (NilEq.mul (NilEq.refl _) (NilEq.mul (NilEq.refl _) (NilEq.mul hgam0
        (NilEq.mul hGi (NilEq.mul (NilEq.refl _) hE)))))
      (NilEq.mul (NilEq.refl _) (NilEq.mul hB (NilEq.mul hGi (NilEq.mul (NilEq.refl _) hE)))))

end Main

/-! ### The main theorem -/

/-- **The block of Rouquier's map through the identity, `∑ₐ h a ≤ 0`** (the block-`(2)` part of KM3
for the coproduct of `sl₂` data: B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*,
arXiv:1603.06311v3, Theorem `th:coproduct`; J. Brundan, A. Savage, B. Webster, arXiv:1812.03255v3,
§5, Theorem 5.4). Labels `a` carry Rouquier's data `L a` of weight `h a` at a common object `b`, with
nilpotent dots; the dots of label `a` are shifted by `u a`, the `u a` pairwise distinct; `δ a c`
(`a ≠ c`) is any inverse of the dumbbell `(u_c + y_c) - (u_a + x_a)` on `Eₐ E_c` (the
position-preserving component of the summed crossing). Then

  `(rouqSig, rouqCups) : ⊞ₐ Eₐ Fₐ 1_b ⊕ 1_b^{⊕ M} → ⊞ₐ Fₐ Eₐ 1_b`,   `M = -∑ₐ h a`,

is invertible in the additive envelope `Mat_ (b ⟶ b)`. Proved by a matrix argument: Gaussian
elimination against the labelwise inverses reduces it to the signed transpose of the
partial-fraction matrix `crtMatrix` modulo nilpotent closed diagrams. -/
theorem isIso_rouqMap_of_nonpos {n : ℕ} (hx₁ : ∀ a, powComp (x₁ a) n = 0)
    (hx₂ : ∀ a, powComp (x₂ a) n = 0) {u : A → k} (hu : Function.Injective u)
    (δ : ∀ a c, E₁ a ≫ E₂ c ⟶ E₁ a ≫ E₂ c)
    (hδ : ∀ a c, a ≠ c →
      δ a c ≫ ((u c - u a) • 𝟙 _ + E₁ a ◁ x₂ c - x₁ a ▷ E₂ c) = 𝟙 _)
    (hN : ∑ a, h a ≤ 0) :
    IsIso (biprod.desc (rouqSig L δ) (rouqCups L u (-∑ a, h a).toNat)) := by
  set n' := n + ∑ a, (h a).natAbs
  have hx₁' : ∀ a, powComp (x₁ a) n' = 0 := fun a => by
    rw [powComp_add_eq, hx₁ a, Limits.zero_comp]
  have hx₂' : ∀ a, powComp (x₂ a) n' = 0 := fun a => by
    rw [powComp_add_eq, hx₂ a, Limits.zero_comp]
  have hn' : ∀ a, (h a).natAbs ≤ n' := fun a =>
    le_add_left (Finset.single_le_sum (f := fun a => (h a).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ a))
  have hMn : (-∑ a, h a).toNat ≤ n' := by
    have : -∑ a, h a ≤ ∑ a, ((h a).natAbs : ℤ) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun a _ => by have := Int.le_natAbs (a := -h a); rwa [Int.natAbs_neg] at this
    have h2 : ((∑ a, (h a).natAbs : ℕ) : ℤ) = ∑ a, ((h a).natAbs : ℤ) := by push_cast; rfl
    omega
  rw [rouqSig_eq L hx₁' hx₂' hu δ hδ, rouqCups_eq L hMn u]
  exact isIso_desc_teleporter L hx₁' hx₂' hn' hu hN

end Setting

end RouqCoproduct

end Categorification.TwoRep
