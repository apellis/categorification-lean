/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Theorem13
import Categorification.Diagrams.KL3.Prop328Tau

/-!
# `K₀(U̇)` as an idempotented algebra, and `γ : _𝒜 U̇ → K₀(U̇)` as an algebra homomorphism

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.6
(TeX `\subsection{$K_0(\dot{\cal{U}})$ and homomorphism $\gamma$}`, label `subsec_KzeroU`).

WIP.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents StringDiagrams
  Categorification.QuantumGroup Categorification.QuantumGroup.UDot Presentation GradedBicat

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [Field k]

/-! ## The ring `K₀(U̇) = ⊕_{λ, ρ} K₀(U̇(λ, ρ))` -/

section Ring

open scoped Classical

/-- **`K₀(U̇) = ⊕_{λ, ρ} K₀(U̇(λ, ρ))`** (KL III §3.6), indexed by pairs `(ρ, λ)` of the left and
right weight (the block `K0Kar RD k ρ λ`). -/
abbrev K0All : Type _ := DirectSum (X × X) fun p => K0Kar RD k p.1 p.2

variable {RD k}

/-- Transport along an equality of left weights. -/
def castK {μ μ' lam : X} (h : μ = μ') : K0Kar RD k μ lam →+ K0Kar RD k μ' lam :=
  h ▸ AddMonoidHom.id _

@[simp] theorem castK_self {μ lam : X} (h : μ = μ) (x : K0Kar RD k μ lam) : castK h x = x := rfl

theorem castK_smul {μ μ' lam : X} (h : μ = μ') (p : LaurentPolynomial ℤ) (x : K0Kar RD k μ lam) :
    castK h (p • x) = p • castK h x := by
  subst h; rfl

/-- The product of two homogeneous blocks: `K₀(U̇(μ, ρ)) × K₀(U̇(λ, μ')) → K₀(U̇(λ, ρ))` if
`μ = μ'`, and `0` otherwise. -/
def blkMul (a b : X × X) : K0Kar RD k a.1 a.2 →+ K0Kar RD k b.1 b.2 →+ K0All RD k :=
  if h : b.1 = a.2 then
    ((K0U.mul (deg := deg RD) (l := wtObj RD k a.1) (m := wtObj RD k a.2)
      (n := wtObj RD k b.2)).compl₂ (castK h)).compr₂
      (DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) (a.1, b.2))
  else 0

theorem blkMul_self (ρ μ lam : X) (x : K0Kar RD k ρ μ) (y : K0Kar RD k μ lam) :
    blkMul (ρ, μ) (μ, lam) x y =
      DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) (ρ, lam) (K0U.mul x y) := by
  unfold blkMul
  split_ifs with h
  · rfl
  · exact absurd rfl h

theorem blkMul_ne {a b : X × X} (h : b.1 ≠ a.2) (x : K0Kar RD k a.1 a.2)
    (y : K0Kar RD k b.1 b.2) : blkMul a b x y = 0 := by
  unfold blkMul
  split_ifs with h'
  · exact absurd h' h
  · rfl

/-- The multiplication of `K₀(U̇)` as a biadditive map. -/
def mulK : K0All RD k →+ K0All RD k →+ K0All RD k :=
  DirectSum.toAddMonoid fun a =>
    (DirectSum.toAddMonoid fun b => (blkMul (RD := RD) (k := k) a b).flip).flip

theorem mulK_of_of (a b : X × X) (x : K0Kar RD k a.1 a.2) (y : K0Kar RD k b.1 b.2) :
    mulK (DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) a x)
      (DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) b y) = blkMul a b x y := by
  rw [mulK, DirectSum.toAddMonoid_of, AddMonoidHom.flip_apply, DirectSum.toAddMonoid_of,
    AddMonoidHom.flip_apply]

instance : Mul (K0All RD k) := ⟨fun x y => mulK x y⟩

theorem mul_def (x y : K0All RD k) : x * y = mulK x y := rfl

theorem of_mul_of (a b : X × X) (x : K0Kar RD k a.1 a.2) (y : K0Kar RD k b.1 b.2) :
    DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) a x *
      DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) b y = blkMul a b x y :=
  mulK_of_of a b x y

theorem of_mul_of_self (ρ μ lam : X) (x : K0Kar RD k ρ μ) (y : K0Kar RD k μ lam) :
    DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) (ρ, μ) x *
        DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) (μ, lam) y =
      DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) (ρ, lam) (K0U.mul x y) := by
  rw [of_mul_of, blkMul_self]

theorem of_mul_of_ne {a b : X × X} (h : b.1 ≠ a.2) (x : K0Kar RD k a.1 a.2)
    (y : K0Kar RD k b.1 b.2) :
    DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) a x *
      DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) b y = 0 := by
  rw [of_mul_of, blkMul_ne h]

theorem mulK_assoc (x y z : K0All RD k) : x * y * z = x * (y * z) := by
  induction x using DirectSum.induction_on with
  | zero => simp [mul_def]
  | add x x' hx hx' => simp only [mul_def, map_add, AddMonoidHom.add_apply] at hx hx' ⊢; rw [hx, hx']
  | of a x =>
    induction y using DirectSum.induction_on with
    | zero => simp [mul_def]
    | add y y' hy hy' =>
      simp only [mul_def, map_add, AddMonoidHom.add_apply] at hy hy' ⊢; rw [hy, hy']
    | of b y =>
      induction z using DirectSum.induction_on with
      | zero => simp [mul_def]
      | add z z' hz hz' => simp only [mul_def, map_add] at hz hz' ⊢; rw [hz, hz']
      | of c z =>
        obtain ⟨a1, a2⟩ := a
        obtain ⟨b1, b2⟩ := b
        obtain ⟨c1, c2⟩ := c
        by_cases h1 : b1 = a2
        · subst h1
          rw [of_mul_of_self]
          by_cases h2 : c1 = b2
          · subst h2
            rw [of_mul_of_self, of_mul_of_self, of_mul_of_self, K0U.mul_assoc]
          · rw [of_mul_of_ne h2, of_mul_of_ne h2, mul_def, map_zero]
        · rw [of_mul_of_ne h1, mul_def, map_zero, AddMonoidHom.zero_apply]
          by_cases h2 : c1 = b2
          · subst h2
            rw [of_mul_of_self, of_mul_of_ne h1]
          · rw [of_mul_of_ne h2, mul_def, map_zero]

/-- **`K₀(U̇)` is a non-unital ring** (KL III §3.6: "we may view `K₀(U̇)` as a non-unital
`ℤ[q, q⁻¹]`-algebra"). -/
instance instNonUnitalRingK0All : NonUnitalRing (K0All RD k) where
  left_distrib x y z := map_add (mulK x) y z
  right_distrib x y z := by rw [mul_def, map_add, AddMonoidHom.add_apply]; rfl
  zero_mul x := by rw [mul_def, map_zero, AddMonoidHom.zero_apply]
  mul_zero x := map_zero (mulK x)
  mul_assoc := mulK_assoc

theorem smul_mulK (p : LaurentPolynomial ℤ) (x y : K0All RD k) : (p • x) * y = p • (x * y) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [smul_add, add_mul, add_mul, hx, hx', smul_add]
  | of a x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [mul_add, mul_add, hy, hy', smul_add]
    | of b y =>
      rw [← DirectSum.of_smul]
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      by_cases h : b1 = a2
      · subst h
        rw [of_mul_of_self, of_mul_of_self, K0U.mul_smul_left, DirectSum.of_smul]
      · rw [of_mul_of_ne h, of_mul_of_ne h, smul_zero]

theorem mulK_smul (p : LaurentPolynomial ℤ) (x y : K0All RD k) : x * (p • y) = p • (x * y) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, add_mul, hx, hx', smul_add]
  | of a x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [smul_add, mul_add, mul_add, hy, hy', smul_add]
    | of b y =>
      rw [← DirectSum.of_smul]
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      by_cases h : b1 = a2
      · subst h
        rw [of_mul_of_self, of_mul_of_self, K0U.mul_smul_right, DirectSum.of_smul]
      · rw [of_mul_of_ne h, of_mul_of_ne h, smul_zero]

instance : IsScalarTower (LaurentPolynomial ℤ) (K0All RD k) (K0All RD k) :=
  ⟨fun p x y => smul_mulK p x y⟩

instance : SMulCommClass (LaurentPolynomial ℤ) (K0All RD k) (K0All RD k) :=
  ⟨fun p x y => (mulK_smul p x y).symm⟩

variable (RD k) in
/-- The idempotent `[1_λ] ∈ K₀(U̇)`. -/
def oneK (lam : X) : K0All RD k :=
  DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) (lam, lam) (K0U.one (wtObj RD k lam))

/-- **The `[1_λ]` are orthogonal idempotents**: `[1_λ][1_μ] = δ_{λμ} [1_λ]`. -/
theorem oneK_mul_oneK (lam mu : X) :
    oneK RD k lam * oneK RD k mu = if lam = mu then oneK RD k lam else 0 := by
  unfold oneK
  split_ifs with h
  · subst h; rw [of_mul_of_self, K0U.one_mul]
  · exact of_mul_of_ne (Ne.symm h) _ _

/-- `[1_ρ] x [1_λ]` is the `(ρ, λ)`-block of `x`. -/
theorem oneK_mul_mul_oneK (ρ lam : X) (x : K0All RD k) :
    oneK RD k ρ * x * oneK RD k lam =
      DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) (ρ, lam) (x (ρ, lam)) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [mul_add, add_mul, hx, hx', DirectSum.add_apply, map_add]
  | of a x =>
    obtain ⟨a1, a2⟩ := a
    unfold oneK
    by_cases h1 : a1 = ρ
    · subst h1
      rw [of_mul_of_self, K0U.one_mul]
      by_cases h2 : a2 = lam
      · subst h2
        rw [of_mul_of_self, K0U.mul_one, DirectSum.of_eq_same]
      · rw [of_mul_of_ne (Ne.symm h2), DirectSum.of_eq_of_ne _ _ _ (by simp [Ne.symm h2]),
          map_zero]
    · rw [of_mul_of_ne h1, zero_mul, DirectSum.of_eq_of_ne _ _ _ (by simp [Ne.symm h1]),
        map_zero]

end Ring

/-! ## `γ : _𝒜 U̇ → K₀(U̇)` -/

section Gamma

attribute [local instance] KLR.KLGamma.vAlgebra

open scoped Classical

variable {RD k} [DecidableEq I]

variable (RD k) in
/-- **Every block `K₀(U̇(λ, ρ))` is torsion free over `ℤ[q, q⁻¹]`** (KL III §3.6: a consequence
of the Krull–Schmidt property; proved in `KrullSchmidtU` under `HomGdim`, in particular for
simply-laced data). -/
def TorsionFreeK0 : Prop :=
  ∀ ρ lam : X, ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ), ∀ x : K0Kar RD k ρ lam,
    p • x = 0 → x = 0

omit [DecidableEq I] in
theorem torsionFreeK0_of_homGdim (hG : HomGdim RD k) : TorsionFreeK0 RD k :=
  fun ρ lam => K0Kar_torsionFree_of_homGdim hG ρ lam

theorem torsionFreeK0_of_simplyLaced [Finite I] (hSL : SimplyLaced C) : TorsionFreeK0 RD k :=
  torsionFreeK0_of_homGdim (homGdim_of_simplyLaced hSL)

variable (RD) in
/-- The index set of the generators `E_d 1_λ` of `_𝒜 U̇`: a block `(ρ, λ)` and a dpss `d` with
right weight `λ` and left weight `ρ`. -/
abbrev Gen : Type _ := Σ p : X × X, DpIdx (RD := RD) p.2 p.1

omit [DecidableEq I] in
theorem wt_eq_add_wdp (lam : X) (d : List (Bool × I × ℕ)) :
    wt RD lam (dpWord d) = lam + wdp RD d := by
  rw [wt_eq_add_wX, ← dpSeq_eq_dpWord, wX_dpSeq, add_comm]

variable (RD) in
/-- `∑_g c_g g ↦ ∑_g c_g E_{d_g} 1_{λ_g} ∈ U̇`. -/
def genU : (Gen RD →₀ LaurentPolynomial ℤ) →+ UD RD vQ :=
  Finsupp.liftAddHom fun g =>
    { toFun := fun c => lpToQ c • E1dp RD vQ g.2.1 g.1.2
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul] }

omit [DecidableEq I] in
theorem genU_single (g : Gen RD) (c : LaurentPolynomial ℤ) :
    genU RD (Finsupp.single g c) = lpToQ c • E1dp RD vQ g.2.1 g.1.2 :=
  Finsupp.liftAddHom_apply_single _ _ _

omit [DecidableEq I] in
theorem genU_smul (p : LaurentPolynomial ℤ) (f : Gen RD →₀ LaurentPolynomial ℤ) :
    genU RD (p • f) = lpToQ p • genU RD f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [smul_add, map_add, hf, hg, map_add, smul_add]
  | single g c => rw [Finsupp.smul_single, genU_single, genU_single, smul_eq_mul, map_mul, mul_smul]

variable (RD k) in
/-- `∑_g c_g g ↦ ∑_g c_g [E_{d_g} 1_{λ_g}] ∈ K₀(U̇)`. -/
def genK : (Gen RD →₀ LaurentPolynomial ℤ) →ₗ[LaurentPolynomial ℤ] K0All RD k :=
  Finsupp.linearCombination _ fun g =>
    DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) g.1 (dpC RD k g.2.1 g.1.2 g.1.1 g.2.2)

theorem genK_single (g : Gen RD) (c : LaurentPolynomial ℤ) :
    genK RD k (Finsupp.single g c) =
      DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) g.1
        (c • dpC RD k g.2.1 g.1.2 g.1.1 g.2.2) := by
  rw [genK, Finsupp.linearCombination_single, DirectSum.of_smul]

/-- Concatenation of generators in adjacent blocks. -/
def genCat (g g' : Gen RD) (h : g'.1.1 = g.1.2) : Gen RD :=
  ⟨(g.1.1, g'.1.2), ⟨g.2.1 ++ g'.2.1, by rw [dpWord_append, wt_append, g'.2.2, h, g.2.2]⟩⟩

open Classical in
/-- The product of two generators (with coefficients). -/
def genMulHom (g g' : Gen RD) :
    LaurentPolynomial ℤ →+ LaurentPolynomial ℤ →+ (Gen RD →₀ LaurentPolynomial ℤ) :=
  if h : g'.1.1 = g.1.2 then
    (AddMonoidHom.mul : LaurentPolynomial ℤ →+ _ →+ _).compr₂ (Finsupp.singleAddHom (genCat g g' h))
  else 0

variable (RD) in
/-- The product of formal combinations of generators (concatenation of dpss). -/
def mulG : (Gen RD →₀ LaurentPolynomial ℤ) →+ (Gen RD →₀ LaurentPolynomial ℤ) →+
    (Gen RD →₀ LaurentPolynomial ℤ) :=
  Finsupp.liftAddHom fun g => (Finsupp.liftAddHom fun g' => (genMulHom g g').flip).flip

omit [DecidableEq I] in
theorem mulG_single_single (g g' : Gen RD) (c c' : LaurentPolynomial ℤ) :
    mulG RD (Finsupp.single g c) (Finsupp.single g' c') = genMulHom g g' c c' := by
  rw [mulG, Finsupp.liftAddHom_apply_single, AddMonoidHom.flip_apply,
    Finsupp.liftAddHom_apply_single, AddMonoidHom.flip_apply]

omit [DecidableEq I] in
/-- `E(f) E(f') = E(f f')` in `U̇`. -/
theorem genU_mulG (f f' : Gen RD →₀ LaurentPolynomial ℤ) :
    genU RD (mulG RD f f') = genU RD f * genU RD f' := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => rw [map_add, AddMonoidHom.add_apply, map_add, h₁, h₂, map_add, add_mul]
  | single g c =>
    induction f' using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, mul_add]
    | single g' c' =>
      rw [mulG_single_single, genU_single, genU_single, smul_mul_assoc, mul_smul_comm,
        E1dp_mul_E1dp, genMulHom]
      have hw : g'.1.2 + wdp RD g'.2.1 = g'.1.1 := by rw [← wt_eq_add_wdp, g'.2.2]
      split_ifs with h h' h'
      · rw [AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply, Finsupp.singleAddHom_apply,
          genU_single, map_mul, mul_smul]
        rfl
      · exact absurd (hw.trans h) h'
      · exact absurd (hw.symm.trans h') h
      · simp

/-- `[E(f)] [E(f')] = [E(f f')]` in `K₀(U̇)`. -/
theorem genK_mulG (f f' : Gen RD →₀ LaurentPolynomial ℤ) :
    genK RD k (mulG RD f f') = genK RD k f * genK RD k f' := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => rw [map_add, AddMonoidHom.add_apply, map_add, h₁, h₂, map_add, add_mul]
  | single g c =>
    induction f' using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, mul_add]
    | single g' c' =>
      obtain ⟨⟨ρ, μ⟩, d, hd⟩ := g
      obtain ⟨⟨μ', lam⟩, d', hd'⟩ := g'
      rw [mulG_single_single, genK_single, genK_single, genMulHom]
      by_cases h : μ' = μ
      · subst h
        rw [dite_eq_left rfl, of_mul_of_self, AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply,
          Finsupp.singleAddHom_apply, genK_single, K0U.mul_smul_left, K0U.mul_smul_right,
          smul_smul]
        exact congrArg (fun z => DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) (ρ, lam)
          ((c * c') • z)) (dpC_append d d' lam μ' ρ hd' hd _)
      · rw [dite_eq_right h, of_mul_of_ne (a := (ρ, μ)) (b := (μ', lam)) h]
        rfl

/-! ### The universal `ℚ(q)`-target of `K₀(U̇)` -/

variable (RD k) in
/-- The global `ℚ(q)`-target `ℚ(q) ⊗_{ℤ[q, q⁻¹]} K₀(U̇)`. -/
def univG : GTarget RD k (TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) (K0All RD k)) where
  φ ρ lam := ((TensorProduct.mk (LaurentPolynomial ℤ) (RatFunc ℚ) (K0All RD k) 1).comp
    (DirectSum.lof (LaurentPolynomial ℤ) (X × X) (fun p => K0Kar RD k p.1 p.2) (ρ, lam))).toAddMonoidHom
  map_T ρ lam n x := by
    change TensorProduct.mk (LaurentPolynomial ℤ) (RatFunc ℚ) (K0All RD k) 1
      (DirectSum.lof (LaurentPolynomial ℤ) (X × X) (fun p => K0Kar RD k p.1 p.2) (ρ, lam) _) = _
    rw [map_smul, map_smul, ← lpToQ_T, lpToQ_eq_laurentEval,
      ← algebraMap_smul (RatFunc ℚ) (LaurentPolynomial.T n : LaurentPolynomial ℤ)]
    rfl

theorem gammaUD_univG_genU (f : Gen RD →₀ LaurentPolynomial ℤ) :
    gammaUD (univG RD k) (genU RD f) =
      TensorProduct.mk (LaurentPolynomial ℤ) (RatFunc ℚ) (K0All RD k) 1 (genK RD k f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]
  | single g c =>
    rw [genU_single, map_smul, gammaUD_E1dp _ g.2.1 g.1.2 g.1.1 g.2.2, genK_single,
      lpToQ_eq_laurentEval]
    change _ = TensorProduct.mk (LaurentPolynomial ℤ) (RatFunc ℚ) (K0All RD k) 1
      (DirectSum.lof (LaurentPolynomial ℤ) (X × X) (fun p => K0Kar RD k p.1 p.2) g.1 (c • _))
    rw [map_smul, map_smul, ← algebraMap_smul (RatFunc ℚ) c]
    rfl

/-- **The relations of `_𝒜 U̇` hold in `K₀(U̇)`**: if `∑_g c_g E_{d_g} 1_{λ_g} = 0` in `U̇`, then
`∑_g c_g [E_{d_g} 1_{λ_g}] = 0` in `K₀(U̇)` (given torsion-freeness). -/
theorem genK_eq_zero (htf : TorsionFreeK0 RD k) {f : Gen RD →₀ LaurentPolynomial ℤ}
    (hf : genU RD f = 0) : genK RD k f = 0 := by
  have h := gammaUD_univG_genU (k := k) f
  rw [hf, map_zero] at h
  have := KLR.KLGamma.isFractionRing_vAlgebra
  have hL : IsLocalizedModule (nonZeroDivisors (LaurentPolynomial ℤ))
      (TensorProduct.mk (LaurentPolynomial ℤ) (RatFunc ℚ) (K0All RD k) 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (LaurentPolynomial ℤ)) (RatFunc ℚ)
      _).2 (TensorProduct.isBaseChange _ _ _)
  obtain ⟨⟨p, hp⟩, hpx⟩ :=
    (IsLocalizedModule.eq_zero_iff (nonZeroDivisors (LaurentPolynomial ℤ))
      (TensorProduct.mk (LaurentPolynomial ℤ) (RatFunc ℚ) (K0All RD k) 1)).1 h.symm
  rw [Submonoid.mk_smul] at hpx
  refine DFinsupp.ext fun a => ?_
  refine htf a.1 a.2 p hp _ ?_
  have := congrArg (fun z : K0All RD k => z a) hpx
  exact this

/-! ### `_𝒜 U̇` is spanned by the generators -/

omit [DecidableEq I] in
theorem lpToQ_smul_E1dp_mem_AUD (c : LaurentPolynomial ℤ) (d : List (Bool × I × ℕ)) (lam : X) :
    lpToQ c • E1dp RD vQ d lam ∈ AUD RD vQ := by
  induction c using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [map_add, add_smul]; exact add_mem hp hp'
  | C_mul_T n a =>
    rw [map_mul, lpToQ_T, lpToQ, LaurentPolynomial.eval₂_C, mul_smul, eq_intCast,
      Int.cast_smul_eq_zsmul]
    exact zsmul_mem (gen_mem_AUD RD vQ n d lam) a

omit [DecidableEq I] in
/-- **`_𝒜 U̇` is the set of `ℤ[q, q⁻¹]`-linear combinations of the `E_d 1_λ`** (KL III §2.1.3). -/
theorem mem_AUD_iff (x : UD RD vQ) : x ∈ AUD RD vQ ↔ ∃ f, genU RD f = x := by
  constructor
  · intro hx
    induction hx using NonUnitalSubring.closure_induction with
    | mem x hx =>
      obtain ⟨n, d, lam, rfl⟩ := hx
      refine ⟨Finsupp.single ⟨(wt RD lam (dpWord d), lam), ⟨d, rfl⟩⟩ (LaurentPolynomial.T n), ?_⟩
      rw [genU_single, lpToQ_T]
      rfl
    | zero => exact ⟨0, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨f, rfl⟩ := hx; obtain ⟨g, rfl⟩ := hy; exact ⟨f + g, map_add _ _ _⟩
    | neg x _ hx => obtain ⟨f, rfl⟩ := hx; exact ⟨-f, map_neg _ _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨f, rfl⟩ := hx; obtain ⟨g, rfl⟩ := hy; exact ⟨mulG RD f g, genU_mulG f g⟩
  · rintro ⟨f, rfl⟩
    induction f using Finsupp.induction_linear with
    | zero => rw [map_zero]; exact zero_mem _
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | single g c => rw [genU_single]; exact lpToQ_smul_E1dp_mem_AUD c _ _

/-! ### `γ` -/

variable (htf : TorsionFreeK0 RD k)

include htf in
theorem genK_congr {f f' : Gen RD →₀ LaurentPolynomial ℤ} (h : genU RD f = genU RD f') :
    genK RD k f = genK RD k f' := by
  rw [← sub_eq_zero, ← map_sub]
  exact genK_eq_zero htf (by rw [map_sub, h, sub_self])

variable (k) in
/-- The underlying function of `γ` on `_𝒜 U̇` (well defined by `gammaFun_eq`). -/
def gammaFun (x : AUD RD vQ) : K0All RD k :=
  genK RD k (Classical.choose ((mem_AUD_iff x.1).1 x.2))

include htf in
theorem gammaFun_eq {x : AUD RD vQ} {f : Gen RD →₀ LaurentPolynomial ℤ} (h : genU RD f = x) :
    gammaFun k x = genK RD k f :=
  genK_congr htf ((Classical.choose_spec ((mem_AUD_iff x.1).1 x.2)).trans h.symm)

variable (k) in
/-- **KL III Proposition 3.27 (integral form, as a homomorphism of idempotented algebras)**:
`γ : _𝒜 U̇ → K₀(U̇)`, `γ(∑ c_d E_d 1_λ) = ∑ c_d [E_d 1_λ]` (`gammaAlg_genU`, `gammaAlg_E1dp`), a
homomorphism of non-unital rings, `ℤ[q, q⁻¹]`-linear (`gammaAlg_smul`), with `γ(1_λ) = [1_λ]`
(`gammaAlg_one`) — given that every block of `K₀(U̇)` is torsion free (true under `HomGdim`, in
particular for simply-laced data: `torsionFreeK0_of_simplyLaced`). -/
def gammaAlg : AUD RD vQ →ₙ+* K0All RD k where
  toFun := gammaFun k
  map_mul' x y := by
    obtain ⟨f, hf⟩ := (mem_AUD_iff x.1).1 x.2
    obtain ⟨g, hg⟩ := (mem_AUD_iff y.1).1 y.2
    rw [gammaFun_eq htf hf, gammaFun_eq htf hg,
      gammaFun_eq htf (f := mulG RD f g) (by rw [genU_mulG, hf, hg]; rfl), genK_mulG]
  map_zero' := (gammaFun_eq htf (f := 0) (map_zero _)).trans (map_zero _)
  map_add' x y := by
    obtain ⟨f, hf⟩ := (mem_AUD_iff x.1).1 x.2
    obtain ⟨g, hg⟩ := (mem_AUD_iff y.1).1 y.2
    rw [gammaFun_eq htf hf, gammaFun_eq htf hg,
      gammaFun_eq htf (f := f + g) (by rw [map_add, hf, hg]; rfl), map_add]

/-- `γ(∑_g c_g E_{d_g} 1_{λ_g}) = ∑_g c_g [E_{d_g} 1_{λ_g}]`. -/
theorem gammaAlg_genU (f : Gen RD →₀ LaurentPolynomial ℤ) :
    gammaAlg k htf ⟨genU RD f, (mem_AUD_iff _).2 ⟨f, rfl⟩⟩ = genK RD k f :=
  gammaFun_eq htf rfl

/-- **`γ(E_d 1_λ) = [E_d 1_λ]`** for every dpss `d` (KL III Proposition 3.27). -/
theorem gammaAlg_E1dp (d : List (Bool × I × ℕ)) (lam ρ : X) (h : wt RD lam (dpWord d) = ρ) :
    gammaAlg k htf ⟨E1dp RD vQ d lam, E1dp_mem_AUD RD vQ d lam⟩ =
      DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) (ρ, lam) (dpC RD k d lam ρ h) := by
  have e := gammaFun_eq (k := k) htf (x := ⟨E1dp RD vQ d lam, E1dp_mem_AUD RD vQ d lam⟩)
    (f := Finsupp.single ⟨(ρ, lam), ⟨d, h⟩⟩ 1) (by rw [genU_single, map_one, one_smul])
  rw [genK_single, one_smul] at e
  exact e

/-- **`γ(1_λ) = [1_λ]`**. -/
theorem gammaAlg_one (lam : X) :
    gammaAlg k htf ⟨one RD vQ lam, one_mem_AUD RD vQ lam⟩ = oneK RD k lam :=
  gammaAlg_E1dp htf [] lam lam rfl

omit [DecidableEq I] in
/-- **`γ` is `ℤ[q, q⁻¹]`-linear**: `_𝒜 U̇` is stable under `ℤ[q, q⁻¹]` and
`γ(c x) = c γ(x)`. -/
theorem lpToQ_smul_mem_AUD (c : LaurentPolynomial ℤ) {x : UD RD vQ} (hx : x ∈ AUD RD vQ) :
    lpToQ c • x ∈ AUD RD vQ := by
  obtain ⟨f, rfl⟩ := (mem_AUD_iff x).1 hx
  exact (mem_AUD_iff _).2 ⟨c • f, genU_smul c f⟩

theorem gammaAlg_smul (c : LaurentPolynomial ℤ) (x : AUD RD vQ) :
    gammaAlg k htf ⟨lpToQ c • x.1, lpToQ_smul_mem_AUD c x.2⟩ = c • gammaAlg k htf x := by
  obtain ⟨f, hf⟩ := (mem_AUD_iff x.1).1 x.2
  change gammaFun k _ = c • gammaFun k x
  rw [gammaFun_eq htf hf, gammaFun_eq htf (f := c • f) (by rw [genU_smul, hf]), map_smul]

end Gamma

/-! ## Blocks -/

section Blocks

attribute [local instance] KLR.KLGamma.vAlgebra

open scoped Classical

variable {RD k} [DecidableEq I]

theorem genK_mapDomain (a : X × X) (f : DpIdx (RD := RD) a.2 a.1 →₀ LaurentPolynomial ℤ) :
    genK RD k (Finsupp.mapDomain (Sigma.mk a) f) =
      DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) a (dpCComb (k := k) a.2 a.1 f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, hf, hg, map_add, map_add]
  | single d c =>
    rw [Finsupp.mapDomain_single, genK_single, dpCComb, Finsupp.linearCombination_single]

omit [DecidableEq I] in
theorem genU_mapDomain (a : X × X) (f : DpIdx (RD := RD) a.2 a.1 →₀ LaurentPolynomial ℤ) :
    genU RD (Finsupp.mapDomain (Sigma.mk a) f) =
      ofB RD vQ a.2 (RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ) (U1 RD vQ a.2)
        (dpComb a.2 a.1 f)) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, hf, hg, map_add, map_add, map_add]
  | single d c =>
    rw [Finsupp.mapDomain_single, genU_single, dpComb, Finsupp.linearCombination_single,
      RestrictScalars.addEquiv_map_smul, lpToQ_eq_laurentEval, AddEquiv.apply_symm_apply,
      map_smul]
    rfl

variable (RD) in
/-- The generator `1_λ`. -/
def genOne (lam : X) : Gen RD := ⟨(lam, lam), ⟨[], rfl⟩⟩

omit [DecidableEq I] in
theorem genU_genOne (lam : X) : genU RD (Finsupp.single (genOne RD lam) 1) = one RD vQ lam := by
  rw [genU_single, map_one, one_smul]
  rfl

theorem genK_genOne (lam : X) :
    genK RD k (Finsupp.single (genOne RD lam) 1) = oneK RD k lam := by
  rw [genK_single, one_smul]
  rfl

omit [DecidableEq I] in
/-- `1_ρ E(f) 1_λ` is a combination of generators in the block `(ρ, λ)`. -/
theorem exists_block (ρ lam : X) (f : Gen RD →₀ LaurentPolynomial ℤ) :
    ∃ f' : DpIdx (RD := RD) lam ρ →₀ LaurentPolynomial ℤ,
      mulG RD (mulG RD (Finsupp.single (genOne RD ρ) 1) f) (Finsupp.single (genOne RD lam) 1) =
        Finsupp.mapDomain (Sigma.mk (ρ, lam)) f' := by
  induction f using Finsupp.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add f g hf hg =>
    obtain ⟨f', hf'⟩ := hf
    obtain ⟨g', hg'⟩ := hg
    exact ⟨f' + g', by rw [map_add, map_add, AddMonoidHom.add_apply, hf', hg',
      Finsupp.mapDomain_add]⟩
  | single g c =>
    obtain ⟨⟨a1, a2⟩, d, hd⟩ := g
    rw [mulG_single_single, genMulHom]
    split_ifs with h1
    · change a1 = ρ at h1
      subst h1
      rw [AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply, Finsupp.singleAddHom_apply,
        mulG_single_single, genMulHom]
      split_ifs with h2
      · change lam = a2 at h2
        subst h2
        rw [AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply, Finsupp.singleAddHom_apply]
        exact ⟨Finsupp.single _ _, (Finsupp.mapDomain_single).symm⟩
      · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩

omit [DecidableEq I] in
theorem one_mul_genU_single_mul_one (a : X × X) (g : Gen RD) (c : LaurentPolynomial ℤ) :
    one RD vQ a.1 * genU RD (Finsupp.single g c) * one RD vQ a.2 =
      if g.1 = a then genU RD (Finsupp.single g c) else 0 := by
  obtain ⟨⟨g1, g2⟩, d, hd⟩ := g
  obtain ⟨a1, a2⟩ := a
  by_cases hga : g1 = a1 ∧ g2 = a2
  · obtain ⟨rfl, rfl⟩ := hga
    rw [ite_eq_left rfl, ← genU_genOne, ← genU_genOne, ← genU_mulG, ← genU_mulG, mulG_single_single,
      genMulHom]
    split_ifs with h1
    · rw [AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply, Finsupp.singleAddHom_apply,
        mulG_single_single, genMulHom]
      split_ifs with h2
      · rw [AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply, Finsupp.singleAddHom_apply,
          genU_single, genU_single, one_mul, mul_one]
        change lpToQ c • E1dp RD vQ (([] ++ d) ++ []) g2 = _
        rw [List.nil_append, List.append_nil]
      · exact absurd rfl h2
    · exact absurd rfl h1
  · rw [ite_eq_right (fun h => hga (Prod.mk.inj h)), ← genU_genOne, ← genU_genOne, ← genU_mulG,
      ← genU_mulG, mulG_single_single, genMulHom]
    split_ifs with h1
    · change g1 = a1 at h1
      subst h1
      rw [AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply, Finsupp.singleAddHom_apply,
        mulG_single_single, genMulHom]
      split_ifs with h2
      · exact absurd ⟨rfl, h2.symm⟩ hga
      · simp
    · simp

omit [DecidableEq I] in
/-- **Block decomposition**: an element `x = E(f)` of `_𝒜 U̇` is the sum of its blocks
`1_ρ x 1_λ`. -/
theorem genU_eq_sum_blocks (f : Gen RD →₀ LaurentPolynomial ℤ) :
    genU RD f = ∑ a ∈ f.support.image Sigma.fst, one RD vQ a.1 * genU RD f * one RD vQ a.2 := by
  have hf : genU RD f = ∑ g ∈ f.support, genU RD (Finsupp.single g (f g)) := by
    conv_lhs => rw [← Finsupp.sum_single f]
    rw [Finsupp.sum, map_sum]
  rw [hf]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g hg => ?_
  simp only [one_mul_genU_single_mul_one]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact absurd (Finset.mem_image_of_mem _ hg) h

end Blocks

/-! ## Surjectivity and injectivity of `γ` (simply-laced) -/

section Bij

attribute [local instance] KLR.KLGamma.vAlgebra

open scoped Classical

variable {RD k} [DecidableEq I] [Finite I]

/-- **KL III Theorem 1.1, as a statement about idempotented algebras** (simply-laced, `I`
finite, `k` a field): `γ : _𝒜 U̇ → K₀(U̇)` is surjective. -/
theorem gammaAlg_surjective (hSL : SimplyLaced C) :
    Function.Surjective (gammaAlg k (torsionFreeK0_of_simplyLaced (RD := RD) hSL)) := by
  intro y
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add y y' hy hy' =>
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨x', rfl⟩ := hy'
    exact ⟨x + x', map_add _ _ _⟩
  | of a y =>
    obtain ⟨⟨_, f, rfl⟩, hz⟩ := gammaUA'_surjective (RD := RD) (k := k) hSL a.2 a.1 y
    rw [gammaUA'_apply] at hz
    refine ⟨⟨genU RD (Finsupp.mapDomain (Sigma.mk a) f), (mem_AUD_iff _).2 ⟨_, rfl⟩⟩, ?_⟩
    rw [gammaAlg_genU, genK_mapDomain, hz]

/-- **KL III Theorem 1.2, as a statement about idempotented algebras** (simply-laced, `I`
finite, `k` a field): if the graphical calculus is nondegenerate, `γ : _𝒜 U̇ → K₀(U̇)` is
injective. -/
theorem gammaAlg_injective (hSL : SimplyLaced C) (hnd : CalculusNondeg RD k) :
    Function.Injective (gammaAlg k (torsionFreeK0_of_simplyLaced (RD := RD) hSL)) := by
  set htf := torsionFreeK0_of_simplyLaced (RD := RD) (k := k) hSL
  refine (injective_iff_map_eq_zero (gammaAlg k htf)).2 fun x hx => ?_
  obtain ⟨f, hf⟩ := (mem_AUD_iff x.1).1 x.2
  have hK : genK RD k f = 0 := by
    rw [← gammaFun_eq htf hf]; exact hx
  have hblk : ∀ a : X × X, one RD vQ a.1 * genU RD f * one RD vQ a.2 = 0 := by
    intro a
    obtain ⟨f', hf'⟩ := exists_block a.1 a.2 f
    have hK' : genK RD k (Finsupp.mapDomain (Sigma.mk a) f') = 0 := by
      rw [← hf', genK_mulG, genK_mulG, hK, mul_zero, zero_mul]
    rw [genK_mapDomain] at hK'
    have h0 : dpCComb (k := k) a.2 a.1 f' = 0 :=
      DirectSum.of_injective (β := fun p : X × X => K0Kar RD k p.1 p.2) a
        (by rw [hK', map_zero])
    have hz : (⟨dpComb a.2 a.1 f', LinearMap.mem_range_self _ _⟩ :
        LinearMap.range (dpComb (RD := RD) a.2 a.1)) = 0 := by
      refine (gammaUA'_bijective_unconditional (k := k) hSL hnd a.2 a.1).1 ?_
      rw [gammaUA'_apply, h0, map_zero]
    have hz' : dpComb (RD := RD) a.2 a.1 f' = 0 := congrArg Subtype.val hz
    rw [← genU_genOne, ← genU_genOne, ← genU_mulG, ← genU_mulG, hf', genU_mapDomain, hz',
      map_zero, map_zero]
  apply Subtype.ext
  rw [← hf, genU_eq_sum_blocks]
  exact Finset.sum_eq_zero fun a _ => hblk a

/-- **`_𝒜 U̇ ≅ K₀(U̇)` as idempotented `ℤ[q, q⁻¹]`-algebras** (KL III Theorems 1.1 and 1.2:
simply-laced, `I` finite, `k` a field, nondegenerate calculus): `γ` is a ring isomorphism
(non-unital rings; `ℤ[q, q⁻¹]`-linear by `gammaAlg_smul`, `γ(1_λ) = [1_λ]` by `gammaAlg_one`). -/
def gammaAlgEquiv (hSL : SimplyLaced C) (hnd : CalculusNondeg RD k) :
    AUD RD vQ ≃+* K0All RD k :=
  RingEquiv.ofBijective (gammaAlg k (torsionFreeK0_of_simplyLaced (RD := RD) hSL))
    ⟨gammaAlg_injective hSL hnd, gammaAlg_surjective hSL⟩

end Bij

/-! ## `sl_n` -/

section SlN

attribute [local instance] KLR.KLGamma.vAlgebra

/-- **KL III, `sl_n`: `_𝒜 U̇(sl_n) ≅ K₀(U̇(sl_n))` as idempotented `ℤ[q, q⁻¹]`-algebras**, over
any field `K` (Theorems 1.1, 1.2 with Theorem 1.3; root datum `slRootDatum m`, `I = Fin m`). -/
def gammaAlgEquiv_sl (K : Type w) [Field K] (m : ℕ) :
    AUD (Categorification.Flag.slRootDatum m) vQ ≃+* K0All (Categorification.Flag.slRootDatum m) K :=
  gammaAlgEquiv (simplyLaced_slCartan m) (theorem_1_3 K m)

end SlN

/-! ## Proposition 3.28 for `σ` and `τ`, exactly -/

section Sym

attribute [local instance] KLR.KLGamma.vAlgebra

open scoped Classical

variable {RD k} [DecidableEq I]

/-- **KL III Proposition 3.28 for `σ`, exactly on the generators** (given torsion-freeness;
e.g. under `HomGdim`, in particular for simply-laced data):
`[σ̃][E_d 1_λ] = [E_{d^rev} 1_{-ρ}]`. -/
theorem sigK0_dpC' (htf : TorsionFreeK0 RD k) (d : List (Bool × I × ℕ)) (lam ρ : X)
    (h : wt RD lam (dpWord d) = ρ) (h' : wt RD (-ρ) (dpWord d.reverse) = -lam) :
    sigK0 (RD := RD) (k := k) (ρ := ρ) (lam := lam) rfl rfl (dpC RD k d lam ρ h) =
      dpC RD k d.reverse (-ρ) (-lam) h' :=
  sigK0_dpC_of_torsionFree d lam ρ h h' (htf (-lam) (-ρ))

/-- **KL III Proposition 3.28 for `τ`, exactly on the generators** (given torsion-freeness):
`[τ̃][E_d 1_λ] = q^{rexp} [E_{ρ̄ d} 1_ρ]`. -/
theorem tauK0_dpC' (htf : TorsionFreeK0 RD k) (d : List (Bool × I × ℕ)) (lam ρ : X)
    (h : wt RD lam (dpWord d) = ρ) (h' : wt RD ρ (dpWord (rhod d)) = lam) :
    tauK0 (dpC RD k d lam ρ h) =
      (LaurentPolynomial.T (rexp RD lam (dpWord d)) : LaurentPolynomial ℤ) •
        dpC RD k (rhod d) ρ lam h' :=
  tauK0_dpC_of_torsionFree d lam ρ h h' (htf lam ρ)

omit [DecidableEq I] in
theorem wt_neg_dpWord_reverse {lam ρ : X} {d : List (Bool × I × ℕ)} (h : wt RD lam (dpWord d) = ρ) :
    wt RD (-ρ) (dpWord d.reverse) = -lam := by
  rw [← h, dpWord_reverse, wt_eq_add_wX, wt_eq_add_wX, wX_reverse]
  abel

variable (RD k) in
/-- **`[σ̃]` on `K₀(U̇)`**: `K₀(U̇(λ, ρ)) → K₀(U̇(-ρ, -λ))` on every block. -/
def sigAll : K0All RD k →+ K0All RD k :=
  DirectSum.toAddMonoid fun a =>
    (DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) (-a.2, -a.1)).comp
      (sigK0 (RD := RD) (k := k) (ρ := a.1) (lam := a.2) rfl rfl).toAddMonoidHom

/-- `σ` on generators. -/
def sigGen (g : Gen RD) : Gen RD :=
  ⟨(-g.1.2, -g.1.1), ⟨g.2.1.reverse, wt_neg_dpWord_reverse g.2.2⟩⟩

omit [DecidableEq I] in
theorem genU_mapDomain_sigGen (f : Gen RD →₀ LaurentPolynomial ℤ) :
    genU RD (Finsupp.mapDomain sigGen f) = sigmaUD RD vQ (genU RD f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, hf, hg, map_add, map_add]
  | single g c =>
    have e : -(g.1.2 + wdp RD g.2.1) = -g.1.1 := by rw [← wt_eq_add_wdp, g.2.2]
    rw [Finsupp.mapDomain_single, genU_single, genU_single, map_smul, sigmaUD_E1dp, e]
    rfl

theorem genK_mapDomain_sigGen (htf : TorsionFreeK0 RD k) (f : Gen RD →₀ LaurentPolynomial ℤ) :
    genK RD k (Finsupp.mapDomain sigGen f) = sigAll RD k (genK RD k f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, hf, hg, map_add, map_add]
  | single g c =>
    rw [Finsupp.mapDomain_single, genK_single, genK_single, sigAll, DirectSum.toAddMonoid_of,
      AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
      map_smul (sigK0 (RD := RD) (k := k) (ρ := g.1.1) (lam := g.1.2) rfl rfl),
      sigK0_dpC' htf g.2.1 g.1.2 g.1.1 g.2.2 (wt_neg_dpWord_reverse g.2.2)]
    rfl

/-- **KL III Proposition 3.28 for `σ`, exactly, on all of `_𝒜 U̇`**: `γ ∘ σ = [σ̃] ∘ γ` (given
torsion-freeness of `K₀(U̇)`; e.g. for simply-laced data). -/
theorem gammaAlg_sigma (htf : TorsionFreeK0 RD k) (x : AUD RD vQ) :
    gammaAlg k htf ⟨sigmaUD RD vQ x.1, sigmaUD_mem_AUD RD vQ x.2⟩ =
      sigAll RD k (gammaAlg k htf x) := by
  obtain ⟨f, hf⟩ := (mem_AUD_iff x.1).1 x.2
  change gammaFun k _ = sigAll RD k (gammaFun k x)
  rw [gammaFun_eq htf hf, gammaFun_eq htf (f := Finsupp.mapDomain sigGen f)
    (by rw [genU_mapDomain_sigGen, hf])]
  exact genK_mapDomain_sigGen htf f

end Sym

end Categorification.KL3.Diagram
