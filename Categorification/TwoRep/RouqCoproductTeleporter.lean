/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqSl2
import Categorification.TwoRep.CoproductCRT

/-!
# Teleporters and shifted caps for the `sl₂` coproduct

Bicategorical inputs to the block-`(2)` part of KM3 for a direct sum of `sl₂` data with separated
dots (B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, Theorem
`th:coproduct`; J. Brundan, A. Savage, B. Webster, arXiv:1812.03255v3, §5, Theorem 5.4):

* the rightward crossing `RightwardCrossing.sigma η φ ε` is `k`-linear in `φ` (`sigma_add`,
  `sigma_smul`, `sigma_sum`) and sends `xⁱ ⊗ yʲ` to the cap with `i` dots followed by the cup with
  `j` dots (`sigma_monomial`);
* the **dumbbell** `(u_c + y) - (u_a + x)` on `E₁ ≫ E₂` (a dot `x` on `E₁`, a dot `y` on `E₂`,
  `u_a ≠ u_c`) has, when both dots are nilpotent, the explicit inverse
  `∑ᵢⱼ -telCoeff (u_a - u_c) i j • xⁱ yʲ`, the expansion of `1 / ((u_c - u_a) + y - x)`
  (`dumbbell_mul_inv`); any one-sided inverse equals it (`eq_dumbbellInv`);
* hence the rightward crossing of any inverse of the dumbbell is the **teleporter**
  `∑ᵢⱼ -telCoeff (u_a - u_c) i j • (cap with i dots) ≫ (cup with j dots)`
  (`sigma_eq_teleporter`);
* the cap with `t` shifted dots `(u + x)ᵗ` is `∑ᵢ (t choose i) uᵗ⁻ⁱ • (cap with i dots)`
  (`whiskerLeft_powComp_shift`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory Finset

universe w v u

theorem powComp_eq_pow' {D : Type*} [Category D] {X : D} (f : End X) :
    ∀ n : ℕ, powComp f n = f ^ n
  | 0 => rfl
  | n + 1 => by rw [powComp_succ, powComp_eq_pow' f n, pow_succ']; rfl

/-! ## Shifting indices against a nilpotent element -/

section Ring

variable {k : Type*} [Field k] {R : Type*} [Ring R] [Algebra k R]

/-- Multiplying by `X` shifts coefficients, when `Xⁿ = 0`. -/
theorem sum_smul_pow_succ {X : R} {n : ℕ} (hX : X ^ n = 0) (c : ℕ → k) :
    ∑ i ∈ range n, c i • X ^ (i + 1) =
      ∑ i ∈ range n, (if i = 0 then 0 else c (i - 1)) • X ^ i := by
  cases n with
  | zero => simp
  | succ m =>
    rw [sum_range_succ, hX, smul_zero, add_zero, sum_range_succ']
    simp

/-- The two-variable coefficients `telCoeff e i j`, read as an element of `R`. -/
def dumbbellInv (X Y : R) (n : ℕ) (e : k) : R :=
  ∑ i ∈ range n, ∑ j ∈ range n, (-telCoeff e i j) • (X ^ i * Y ^ j)

/-- **The inverse of the dumbbell**: for commuting nilpotent `X`, `Y` and `e ≠ 0`,
`(-e + Y - X) · ∑ᵢⱼ -telCoeff e i j Xⁱ Yʲ = 1`. -/
theorem dumbbell_mul_inv {X Y : R} (hXY : Commute X Y) {n : ℕ} (hX : X ^ n = 0)
    (hY : Y ^ n = 0) {e : k} (he : e ≠ 0) :
    (algebraMap k R (-e) + Y - X) * dumbbellInv X Y n e = 1 := by
  have hYX : ∀ i j, Y * (X ^ i * Y ^ j) = X ^ i * Y ^ (j + 1) := by
    intro i j
    rw [← mul_assoc, ((hXY.symm).pow_right i).eq, mul_assoc, pow_succ']
  have hXX : ∀ i j, X * (X ^ i * Y ^ j) = X ^ (i + 1) * Y ^ j := by
    intro i j; rw [← mul_assoc, pow_succ']
  -- expand
  have expand : (algebraMap k R (-e) + Y - X) * dumbbellInv X Y n e =
      ∑ i ∈ range n, ∑ j ∈ range n, (e * telCoeff e i j) • (X ^ i * Y ^ j) +
      ∑ i ∈ range n, ∑ j ∈ range n, telCoeff e i j • (X ^ (i + 1) * Y ^ j) -
      ∑ i ∈ range n, ∑ j ∈ range n, telCoeff e i j • (X ^ i * Y ^ (j + 1)) := by
    simp only [dumbbellInv, mul_sum, add_mul, sub_mul, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, mul_smul_comm, hYX, hXX, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    module
  -- shift in `X`
  have shiftX : ∑ i ∈ range n, ∑ j ∈ range n, telCoeff e i j • (X ^ (i + 1) * Y ^ j) =
      ∑ i ∈ range n, ∑ j ∈ range n, (if i = 0 then 0 else telCoeff e (i - 1) j) • (X ^ i * Y ^ j) := by
    rw [sum_comm]
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    simp only [← smul_mul_assoc, ← sum_mul]
    rw [sum_smul_pow_succ hX (fun i => telCoeff e i j)]
  -- shift in `Y`
  have shiftY : ∑ i ∈ range n, ∑ j ∈ range n, telCoeff e i j • (X ^ i * Y ^ (j + 1)) =
      ∑ i ∈ range n, ∑ j ∈ range n, (if j = 0 then 0 else telCoeff e i (j - 1)) • (X ^ i * Y ^ j) := by
    refine sum_congr rfl fun i _ => ?_
    simp only [← mul_smul_comm, ← mul_sum]
    rw [sum_smul_pow_succ hY (fun j => telCoeff e i j)]
  rw [expand, shiftX, shiftY, ← sum_add_distrib, ← sum_sub_distrib]
  simp only [← sum_add_distrib, ← sum_sub_distrib, ← add_smul, ← sub_smul]
  have hrec : ∀ i j, e * telCoeff e i j + (if i = 0 then 0 else telCoeff e (i - 1) j) -
      (if j = 0 then 0 else telCoeff e i (j - 1)) = if i = 0 ∧ j = 0 then 1 else 0 := by
    intro i j
    rw [telCoeff_rec he i j]
    by_cases hj : j = 0 <;> by_cases hi : i = 0 <;> simp [hi, hj]
  simp only [hrec, ite_smul, one_smul, zero_smul]
  cases n with
  | zero =>
    have h1 : (1 : R) = 0 := by simpa using hX
    simp [h1]
  | succ m =>
    rw [sum_eq_single 0, sum_eq_single 0]
    · simp
    · intro j _ hj; simp [hj]
    · simp
    · intro i _ hi
      exact sum_eq_zero fun j _ => by simp [hi]
    · simp

/-- Any one-sided inverse of the dumbbell is `dumbbellInv`. -/
theorem eq_dumbbellInv {X Y : R} (hXY : Commute X Y) {n : ℕ} (hX : X ^ n = 0)
    (hY : Y ^ n = 0) {e : k} (he : e ≠ 0) {δ : R}
    (hδ : (algebraMap k R (-e) + Y - X) * δ = 1) : δ = dumbbellInv X Y n e := by
  set D := algebraMap k R (-e) + Y - X
  have hc : Commute (dumbbellInv X Y n e) D := by
    refine Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ => ?_
    refine Commute.smul_left ?_ _
    have hXD : Commute X D :=
      ((Algebra.commute_algebraMap_right _ X).add_right hXY).sub_right (Commute.refl X)
    have hYD : Commute Y D :=
      ((Algebra.commute_algebraMap_right _ Y).add_right (Commute.refl Y)).sub_right hXY.symm
    exact (hXD.pow_left i).mul_left (hYD.pow_left j)
  calc δ = (dumbbellInv X Y n e * D) * δ := by
        rw [hc.eq, dumbbell_mul_inv hXY hX hY he, one_mul]
    _ = dumbbellInv X Y n e := by rw [mul_assoc, hδ, mul_one]

end Ring

/-! ## The rightward crossing is linear -/

section Sigma

open AdditiveWhiskering

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [AdditiveWhiskering B] {a b c : B} {E₁ : a ⟶ b} {E₂ : b ⟶ c} {R₁ : b ⟶ a} {R₂ : c ⟶ b}

theorem sigma_add (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (φ ψ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) :
    RightwardCrossing.sigma η₂ (φ + ψ) ε₁ =
      RightwardCrossing.sigma η₂ φ ε₁ + RightwardCrossing.sigma η₂ ψ ε₁ := by
  have := RouqSl2Generic.sigma_sub η₂ (φ + ψ) ψ ε₁
  rw [add_sub_cancel_right] at this
  rw [this, sub_add_cancel]

/-- The rightward crossing as an additive map of the upward crossing. -/
def sigmaAddHom (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) :
    (E₁ ≫ E₂ ⟶ E₁ ≫ E₂) →+ (R₁ ≫ E₁ ⟶ E₂ ≫ R₂) :=
  AddMonoidHom.mk' (fun φ => RightwardCrossing.sigma η₂ φ ε₁) fun φ ψ => sigma_add η₂ φ ψ ε₁

theorem sigma_sum {ι : Type*} (s : Finset ι) (η₂ : 𝟙 b ⟶ E₂ ≫ R₂)
    (φ : ι → (E₁ ≫ E₂ ⟶ E₁ ≫ E₂)) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) :
    RightwardCrossing.sigma η₂ (∑ i ∈ s, φ i) ε₁ = ∑ i ∈ s, RightwardCrossing.sigma η₂ (φ i) ε₁ :=
  map_sum (sigmaAddHom η₂ ε₁) φ s

variable {k : Type*} [Field k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
theorem whiskerLeft_smul' (E : a ⟶ b) {f g : b ⟶ c} (s : k) (x : f ⟶ g) :
    E ◁ (s • x) = s • (E ◁ x) :=
  (precomp c E).map_smul s x

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem smul_whiskerRight' {f g : a ⟶ b} (s : k) (x : f ⟶ g) (F : b ⟶ c) :
    (s • x) ▷ F = s • (x ▷ F) :=
  (postcomp a F).map_smul s x

omit [AdditiveWhiskering B] in
theorem sigma_smul (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (s : k) (φ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) :
    RightwardCrossing.sigma η₂ (s • φ) ε₁ = s • RightwardCrossing.sigma η₂ φ ε₁ := by
  simp only [RightwardCrossing.sigma_eq, smul_whiskerRight', whiskerLeft_smul', Linear.smul_comp,
    Linear.comp_smul]

omit [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- The rightward crossing of `x ⊗ y` is the cap with `x` followed by the cup with `y`. -/
theorem sigma_monomial (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) (x : E₁ ⟶ E₁) (y : E₂ ⟶ E₂) :
    RightwardCrossing.sigma η₂ (x ▷ E₂ ≫ E₁ ◁ y) ε₁ = (R₁ ◁ x ≫ ε₁) ≫ η₂ ≫ y ▷ R₂ := by
  rw [RouqSl2Generic.sigma_comp_left, ← Category.id_comp (E₁ ◁ y),
    RouqSl2Generic.sigma_comp_right, RouqSl2Generic.sigma_id]
  simp only [Category.assoc]

/-! ## The teleporter -/

/-- **The teleporter**: the rightward crossing of an inverse `δ` of the dumbbell
`(u_c + y) - (u_a + x)` (with `u_c - u_a = -e ≠ 0` and nilpotent dots) is
`∑ᵢⱼ -telCoeff e i j • (cap with i dots) ≫ (cup with j dots)`. -/
theorem sigma_eq_teleporter (adj₁ : E₁ ⊣ R₁) (adj₂ : E₂ ⊣ R₂) (x : E₁ ⟶ E₁) (y : E₂ ⟶ E₂)
    {n : ℕ} (hx : powComp x n = 0) (hy : powComp y n = 0) {e : k} (he : e ≠ 0)
    (δ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    (hδ : δ ≫ ((-e) • 𝟙 _ + E₁ ◁ y - x ▷ E₂) = 𝟙 _) :
    RightwardCrossing.sigma adj₂.unit δ adj₁.counit =
      ∑ i ∈ range n, ∑ j ∈ range n, (-telCoeff e i j) •
        ((R₁ ◁ powComp x i ≫ adj₁.counit) ≫ adj₂.unit ≫ powComp y j ▷ R₂) := by
  let X : End (E₁ ≫ E₂) := x ▷ E₂
  let Y : End (E₁ ≫ E₂) := E₁ ◁ y
  have hpX : ∀ i, X ^ i = powComp x i ▷ E₂ := fun i => by
    rw [RightwardCrossing.powComp_whiskerRight, powComp_eq_pow']
  have hpY : ∀ j, Y ^ j = E₁ ◁ powComp y j := fun j => by
    rw [RightwardCrossing.whiskerLeft_powComp, powComp_eq_pow']
  have hXY : Commute X Y := whisker_exchange x y
  have hX : X ^ n = 0 := by
    rw [hpX, hx]; exact AdditiveWhiskering.zero_whiskerRight _ _ _
  have hY : Y ^ n = 0 := by
    rw [hpY, hy]; exact AdditiveWhiskering.whiskerLeft_zero _ _ _
  have hδ' : (algebraMap k (End (E₁ ≫ E₂)) (-e) + Y - X) * (show End (E₁ ≫ E₂) from δ) = 1 :=
    hδ
  rw [eq_dumbbellInv hXY hX hY he hδ', dumbbellInv, sigma_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [sigma_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [sigma_smul, hpX, hpY, End.mul_def, whisker_exchange, sigma_monomial]

/-! ## Caps with shifted dots -/

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
theorem powComp_add_smul_id {X : a ⟶ b} (s : k) (x : X ⟶ X) (t : ℕ) :
    powComp (s • 𝟙 X + x) t =
      ∑ i ∈ range (t + 1), ((t.choose i : k) * s ^ (t - i)) • powComp x i := by
  rw [add_comm]
  change powComp ((show End X from x) + algebraMap k (End X) s) t = _
  rw [powComp_eq_pow', (Algebra.commute_algebraMap_right s (show End X from x)).add_pow]
  refine sum_congr rfl fun i _ => ?_
  rw [powComp_eq_pow', ← map_pow, ← map_natCast (algebraMap k (End X)), mul_assoc, ← map_mul,
    ← Algebra.commutes, ← Algebra.smul_def, mul_comm]

omit [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- **The cap with `t` shifted dots**: `R ◁ (s + x)ᵗ ≫ ε = ∑ᵢ (t choose i) sᵗ⁻ⁱ • R ◁ xⁱ ≫ ε`. -/
theorem whiskerLeft_powComp_shift (adj₁ : E₁ ⊣ R₁) (s : k) (x : E₁ ⟶ E₁) (t : ℕ) :
    R₁ ◁ powComp (s • 𝟙 E₁ + x) t ≫ adj₁.counit =
      ∑ i ∈ range (t + 1), ((t.choose i : k) * s ^ (t - i)) • (R₁ ◁ powComp x i ≫ adj₁.counit) := by
  rw [powComp_add_smul_id,
    show R₁ ◁ (∑ i ∈ range (t + 1), ((t.choose i : k) * s ^ (t - i)) • powComp x i) =
      ∑ i ∈ range (t + 1), R₁ ◁ (((t.choose i : k) * s ^ (t - i)) • powComp x i) from
      map_sum (AdditiveWhiskering.whiskerLeftAddHom R₁ E₁ E₁) _ _, Preadditive.sum_comp]
  refine sum_congr rfl fun i _ => ?_
  change R₁ ◁ (_ • _) ≫ _ = _
  rw [whiskerLeft_smul', Linear.smul_comp]

end Sigma

end Categorification.TwoRep
