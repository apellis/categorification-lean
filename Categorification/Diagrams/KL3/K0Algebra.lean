/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.KrullSchmidtU
import Categorification.Diagrams.KL3.GammaAUD
import Categorification.Diagrams.KL3.Prop328Tau

/-!
# `K₀(U̇)` as an idempotented algebra, and `γ : _𝒜 U̇ → K₀(U̇)` as an algebra homomorphism

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.6
(TeX `\subsection{$K_0(\dot{\cal{U}})$ and homomorphism $\gamma$}`, label `subsec_KzeroU`):

> Alternatively, we may view `K₀(U̇)` as a non-unital `ℤ[q, q⁻¹]`-algebra
> `⊕_{λ, μ ∈ X} K₀(U̇)(λ, μ)` with a family of idempotents `[1_λ]`. […]
> Both `_𝒜 U̇` and `K₀(U̇)` are idempotented `ℤ[q, q⁻¹]`-algebras, with the idempotents `1_λ` and
> `[1_λ]` labelled by `λ ∈ X`. […]
> **Proposition 3.27.** The assignment `E_𝐢 1_λ ↦ [E_𝐢 1_λ]` extends to a `ℤ[q, q⁻¹]`-algebra
> homomorphism `γ : _𝒜 U̇ → K₀(U̇)`.

Everything is for an arbitrary root datum and a field `k`.

## The algebra `K₀(U̇)`

* `K0All RD k = ⊕_{(ρ, λ)} K₀(U̇(λ, ρ))`, a non-unital ring (`instNonUnitalRingK0All`: the product
  of two blocks is the product induced by composition, `K0U.mul`, if the middle weights agree and
  `0` otherwise) on which `ℤ[q, q⁻¹]` acts compatibly with the product (`IsScalarTower`,
  `SMulCommClass`), with the orthogonal idempotents `oneK λ = [1_λ]` (`oneK_mul_oneK`,
  `oneK_mul_mul_oneK`).
* `K0All_free`: given hom-finiteness (`HomGdim`, the hypothesis of the Krull–Schmidt theorem of
  `Categorification.Diagrams.KL3.KrullSchmidtU`), `K₀(U̇)` is a free `ℤ[q, q⁻¹]`-module;
  `TorsionFreeK0`, `torsionFreeK0_of_homGdim`, `K0All_torsionFree`: it has no
  `ℤ[q, q⁻¹]`-torsion.

## The relations of `_𝒜 U̇` hold exactly in `K₀(U̇)`

Given `TorsionFreeK0 RD k` (in particular given `HomGdim RD k`):

* `genK_eq_zero`: every `ℤ[q, q⁻¹]`-linear relation `∑ c_d E_d 1_λ = 0` among the generators of
  `_𝒜 U̇` (`d` a divided-powers signed sequence) holds for the classes: `∑ c_d [E_d 1_λ] = 0`;
* `dpC_comm_ne`, `dpC_comm_self`: **the `sl₂` relations**
  `[E_a E_i F_j E_b 1_λ] = [E_a F_j E_i E_b 1_λ]` for `i ≠ j` and
  `[E_a E_i F_i E_b 1_λ] = [E_a F_i E_i E_b 1_λ] + [⟨i, λ + b_X⟩]_i [E_a E_b 1_λ]`, in arbitrary
  contexts `a`, `b` of divided powers (for contexts without divided powers these are
  `eC_EF`, `eC_FE`, `eC_ij` of `Categorification.Diagrams.KL3.K0Relations`, which need no
  hypothesis);
* `dpC_serre`: **the quantum Serre relations**
  `∑_{n=0}^{N} (-1)^n [E_a E_{εi}^{(n)} E_{εj} E_{εi}^{(N-n)} E_b 1_λ] = 0`, `N = 1 - ⟨i, j_X⟩`,
  for `ε = ±`, in arbitrary contexts.

All of these come from the 2-isomorphisms of KL III Propositions 3.24–3.26 through the
`ℚ(q)`-linear `γ` (`gammaQ'`); torsion-freeness is what makes them exact for divided powers.

## The homomorphism `γ`

* `mem_AUD_iff`: `_𝒜 U̇` is the set of `ℤ[q, q⁻¹]`-combinations of the `E_d 1_λ`;
* `gammaAlg`: **KL III Proposition 3.27**: the homomorphism of non-unital rings
  `γ : _𝒜 U̇ → K₀(U̇)` with `γ(E_d 1_λ) = [E_d 1_λ]` (`gammaAlg_E1dp`, `gammaAlg_genU`),
  `γ(1_λ) = [1_λ]` (`gammaAlg_one`), `ℤ[q, q⁻¹]`-linear (`gammaAlg_smul`); on the block
  `1_ρ (_𝒜 U̇) 1_λ` it is the map `gammaUA` of `Categorification.Diagrams.KL3.GammaIntegral`
  (`gammaAlg_ofB_dpComb`);
* `gammaAlg_sigma`: `γ ∘ σ = [σ̃] ∘ γ` on all of `_𝒜 U̇` (KL III Proposition 3.28 for `σ`).

Surjectivity and injectivity of `γ` (KL III Theorems 1.1 and 1.2) are in
`Categorification.Diagrams.KL3.GammaAlgebra`.
-/

-- Elaborate direct sums and the scalar restriction through their abbreviations.
set_option backward.isDefEq.respectTransparency false

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

theorem mulK_def (x y : K0All RD k) : x * y = mulK x y := rfl

theorem ofK_mul_ofK (a b : X × X) (x : K0Kar RD k a.1 a.2) (y : K0Kar RD k b.1 b.2) :
    DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) a x *
      DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) b y = blkMul a b x y :=
  mulK_of_of a b x y

theorem ofK_mul_ofK_self (ρ μ lam : X) (x : K0Kar RD k ρ μ) (y : K0Kar RD k μ lam) :
    DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) (ρ, μ) x *
        DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) (μ, lam) y =
      DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) (ρ, lam) (K0U.mul x y) := by
  rw [ofK_mul_ofK, blkMul_self]

theorem ofK_mul_ofK_ne {a b : X × X} (h : b.1 ≠ a.2) (x : K0Kar RD k a.1 a.2)
    (y : K0Kar RD k b.1 b.2) :
    DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) a x *
      DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) b y = 0 := by
  rw [ofK_mul_ofK, blkMul_ne h]

theorem mulK_assoc (x y z : K0All RD k) : x * y * z = x * (y * z) := by
  induction x using DirectSum.induction_on with
  | zero => simp [mulK_def]
  | add x x' hx hx' => simp only [mulK_def, map_add, AddMonoidHom.add_apply] at hx hx' ⊢; rw [hx, hx']
  | of a x =>
    induction y using DirectSum.induction_on with
    | zero => simp [mulK_def]
    | add y y' hy hy' =>
      simp only [mulK_def, map_add, AddMonoidHom.add_apply] at hy hy' ⊢; rw [hy, hy']
    | of b y =>
      induction z using DirectSum.induction_on with
      | zero => simp [mulK_def]
      | add z z' hz hz' => simp only [mulK_def, map_add] at hz hz' ⊢; rw [hz, hz']
      | of c z =>
        obtain ⟨a1, a2⟩ := a
        obtain ⟨b1, b2⟩ := b
        obtain ⟨c1, c2⟩ := c
        by_cases h1 : b1 = a2
        · subst h1
          rw [ofK_mul_ofK_self]
          by_cases h2 : c1 = b2
          · subst h2
            rw [ofK_mul_ofK_self, ofK_mul_ofK_self, ofK_mul_ofK_self, K0U.mul_assoc]
          · rw [ofK_mul_ofK_ne h2, ofK_mul_ofK_ne h2, mulK_def, map_zero]
        · rw [ofK_mul_ofK_ne h1, mulK_def, map_zero, AddMonoidHom.zero_apply]
          by_cases h2 : c1 = b2
          · subst h2
            rw [ofK_mul_ofK_self, ofK_mul_ofK_ne h1]
          · rw [ofK_mul_ofK_ne h2, mulK_def, map_zero]

/-- **`K₀(U̇)` is a non-unital ring** (KL III §3.6: "we may view `K₀(U̇)` as a non-unital
`ℤ[q, q⁻¹]`-algebra"). -/
instance instNonUnitalRingK0All : NonUnitalRing (K0All RD k) where
  left_distrib x y z := map_add (mulK x) y z
  right_distrib x y z := by rw [mulK_def, map_add, AddMonoidHom.add_apply]; rfl
  zero_mul x := by rw [mulK_def, map_zero, AddMonoidHom.zero_apply]
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
        rw [ofK_mul_ofK_self, ofK_mul_ofK_self, K0U.mul_smul_left, DirectSum.of_smul]
      · rw [ofK_mul_ofK_ne h, ofK_mul_ofK_ne h, smul_zero]

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
        rw [ofK_mul_ofK_self, ofK_mul_ofK_self, K0U.mul_smul_right, DirectSum.of_smul]
      · rw [ofK_mul_ofK_ne h, ofK_mul_ofK_ne h, smul_zero]

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
  · subst h; rw [ofK_mul_ofK_self, K0U.one_mul]
  · exact ofK_mul_ofK_ne (Ne.symm h) _ _

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
      rw [ofK_mul_ofK_self, K0U.one_mul]
      by_cases h2 : a2 = lam
      · subst h2
        rw [ofK_mul_ofK_self, K0U.mul_one, DirectSum.of_eq_same]
      · rw [ofK_mul_ofK_ne (Ne.symm h2), DirectSum.of_eq_of_ne _ _ _ (by simp [Ne.symm h2]),
          map_zero]
    · rw [ofK_mul_ofK_ne h1, zero_mul, DirectSum.of_eq_of_ne _ _ _ (by simp [Ne.symm h1]),
        map_zero]

end Ring

/-! ## Freeness and torsion-freeness -/

section Free

open scoped Classical

variable {RD k}

variable (RD k) in
/-- **Every block `K₀(U̇(λ, ρ))` is torsion free over `ℤ[q, q⁻¹]`** (KL III §3.6: a consequence
of the Krull–Schmidt property; proved in `KrullSchmidtU` under `HomGdim`, in particular for
simply-laced data). -/
def TorsionFreeK0 : Prop :=
  ∀ ρ lam : X, ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ), ∀ x : K0Kar RD k ρ lam,
    p • x = 0 → x = 0

theorem torsionFreeK0_of_homGdim (hG : HomGdim RD k) : TorsionFreeK0 RD k :=
  fun ρ lam => K0Kar_torsionFree hG ρ lam

/-- **`K₀(U̇)` is a free `ℤ[q, q⁻¹]`-module** (KL III §3.6), given hom-finiteness: a basis is
given by the classes of the indecomposable 1-morphisms of all `U̇(λ, ρ)` up to isomorphism and
grading shift (`indecBasisU` on each block). -/
theorem K0All_free (hG : HomGdim RD k) : Module.Free (LaurentPolynomial ℤ) (K0All RD k) :=
  Module.Free.of_basis (DFinsupp.basis fun p : X × X => indecBasisU hG p.1 p.2)

/-- `K₀(U̇)` has no `ℤ[q, q⁻¹]`-torsion if its blocks have none. -/
theorem K0All_torsionFree (htf : TorsionFreeK0 RD k) :
    ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ), ∀ x : K0All RD k, p • x = 0 → x = 0 := by
  intro p hp x hx
  refine DFinsupp.ext fun a => ?_
  exact htf a.1 a.2 p hp _ (congrArg (fun z : K0All RD k => z a) hx)

end Free

/-! ## Generators of `_𝒜 U̇` and relations of `U̇` in terms of divided powers -/

section UDotSide

attribute [local instance] KLR.KLGamma.vAlgebra

open scoped Classical

variable {RD}

theorem wt_eq_add_wdp (lam : X) (d : List (Bool × I × ℕ)) :
    wt RD lam (dpWord d) = lam + wdp RD d := by
  rw [wt_eq_add_wX, ← dpSeq_eq_dpWord, wX_dpSeq, add_comm]

variable (RD) in
/-- The index set of the generators `E_d 1_λ` of `_𝒜 U̇`: a block `(ρ, λ)` and a dpss `d` with
right weight `λ` and left weight `ρ`. -/
abbrev DpGen : Type _ := Σ p : X × X, DpIdx (RD := RD) p.2 p.1

variable (RD) in
/-- `∑_g c_g g ↦ ∑_g c_g E_{d_g} 1_{λ_g} ∈ U̇`. -/
def genU : (DpGen RD →₀ LaurentPolynomial ℤ) →+ UD RD vQ :=
  Finsupp.liftAddHom fun g =>
    { toFun := fun c => lpToQ c • E1dp RD vQ g.2.1 g.1.2
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul] }

theorem genU_single (g : DpGen RD) (c : LaurentPolynomial ℤ) :
    genU RD (Finsupp.single g c) = lpToQ c • E1dp RD vQ g.2.1 g.1.2 :=
  Finsupp.liftAddHom_apply_single _ _ _

theorem genU_smul (p : LaurentPolynomial ℤ) (f : DpGen RD →₀ LaurentPolynomial ℤ) :
    genU RD (p • f) = lpToQ p • genU RD f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [smul_add, map_add, hf, hg, map_add, smul_add]
  | single g c => rw [Finsupp.smul_single, genU_single, genU_single, smul_eq_mul, map_mul, mul_smul]

/-- Concatenation of generators in adjacent blocks. -/
def genCat (g g' : DpGen RD) (h : g'.1.1 = g.1.2) : DpGen RD :=
  ⟨(g.1.1, g'.1.2), ⟨g.2.1 ++ g'.2.1, by rw [dpWord_append, wt_append, g'.2.2, h, g.2.2]⟩⟩

/-- The product of two generators (with coefficients). -/
def genMulHom (g g' : DpGen RD) :
    LaurentPolynomial ℤ →+ LaurentPolynomial ℤ →+ (DpGen RD →₀ LaurentPolynomial ℤ) :=
  if h : g'.1.1 = g.1.2 then
    (AddMonoidHom.mul : LaurentPolynomial ℤ →+ _ →+ _).compr₂ (Finsupp.singleAddHom (genCat g g' h))
  else 0

variable (RD) in
/-- The product of formal combinations of generators (concatenation of dpss). -/
def mulG : (DpGen RD →₀ LaurentPolynomial ℤ) →+ (DpGen RD →₀ LaurentPolynomial ℤ) →+
    (DpGen RD →₀ LaurentPolynomial ℤ) :=
  Finsupp.liftAddHom fun g => (Finsupp.liftAddHom fun g' => (genMulHom g g').flip).flip

theorem mulG_single_single (g g' : DpGen RD) (c c' : LaurentPolynomial ℤ) :
    mulG RD (Finsupp.single g c) (Finsupp.single g' c') = genMulHom g g' c c' := by
  rw [mulG, Finsupp.liftAddHom_apply_single, AddMonoidHom.flip_apply,
    Finsupp.liftAddHom_apply_single, AddMonoidHom.flip_apply]

/-- `E(f) E(f') = E(f f')` in `U̇`. -/
theorem genU_mulG (f f' : DpGen RD →₀ LaurentPolynomial ℤ) :
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

/-! ### `_𝒜 U̇` is spanned by the generators -/

theorem lpToQ_smul_E1dp_mem_AUD (c : LaurentPolynomial ℤ) (d : List (Bool × I × ℕ)) (lam : X) :
    lpToQ c • E1dp RD vQ d lam ∈ AUD RD vQ :=
  lpToQ_smul_mem_AUD c (E1dp_mem_AUD RD vQ d lam)

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

/-! ### Blocks -/

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
def genOne (lam : X) : DpGen RD := ⟨(lam, lam), ⟨[], rfl⟩⟩

theorem genU_genOne (lam : X) : genU RD (Finsupp.single (genOne RD lam) 1) = one RD vQ lam := by
  rw [genU_single, map_one, one_smul]
  rfl

/-- `1_ρ E(f) 1_λ` is a combination of generators in the block `(ρ, λ)`. -/
theorem exists_block (ρ lam : X) (f : DpGen RD →₀ LaurentPolynomial ℤ) :
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

theorem one_mul_genU_single_mul_one (a : X × X) (g : DpGen RD) (c : LaurentPolynomial ℤ) :
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

/-- **Block decomposition**: an element `x = E(f)` of `_𝒜 U̇` is the sum of its blocks
`1_ρ x 1_λ`. -/
theorem genU_eq_sum_blocks (f : DpGen RD →₀ LaurentPolynomial ℤ) :
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

/-! ### The defining relations of `U̇` on products of divided powers -/

/-- Scalars in the contexts of a product. -/
theorem smul_mul_mul_smul {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (r s : R)
    (x y z : A) : (r • x) * y * (s • z) = (r * s) • (x * y * z) := by
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- A relator of `U̇ 1_λ` between two words of divided powers vanishes in `U̇ 1_λ`. -/
theorem mk_dpW_mul_mul_eq_zero (a b : List (Bool × I × ℕ)) (lam : X)
    {z : UDot.Free (RatFunc ℚ) I}
    (hz : ew (dpWord a) * z * ew (dpWord b) ∈ Lrel C vQ (RD.ellOf lam)) :
    UDot.mk RD vQ lam (dpW C vQ a * z * dpW C vQ b) = 0 := by
  rw [dpW_eq_smul a, dpW_eq_smul b, smul_mul_mul_smul, map_smul, mk_eq_zero RD vQ lam hz,
    smul_zero]

theorem ew_singleton_pow (l : Bool × I) (n : ℕ) :
    (ew [l] : UDot.Free (RatFunc ℚ) I) ^ n = ew (List.replicate n l) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', ih, List.replicate_succ, ew_cons]

/-- The image of a divided power `θ_i^{(n)}` under an embedding `θ_i ↦ E_{εi}` of `'f`. -/
theorem map_dpow_eq_dpE (ε : Bool)
    (φ : PreF (RatFunc ℚ) I →ₐ[RatFunc ℚ] UDot.Free (RatFunc ℚ) I)
    (hφ : ∀ i, φ (PreF.θ i) = ew [(ε, i)]) (i : I) (n : ℕ) :
    φ (dpow C.dot (vQ : (RatFunc ℚ)ˣ) i n) = dpE C vQ (ε, i, n) := by
  rw [dpow, map_smul, map_pow, hφ, ew_singleton_pow]
  rfl

/-- The image of KL III's Serre element under an embedding `θ_i ↦ E_{εi}` of `'f`, in terms of
divided powers: `∑_{n + m = N} (-1)^n E_{εi}^{(n)} E_{εj} E_{εi}^{(m)}`. -/
theorem map_serreKL (ε : Bool) (φ : PreF (RatFunc ℚ) I →ₐ[RatFunc ℚ] UDot.Free (RatFunc ℚ) I)
    (hφ : ∀ i, φ (PreF.θ i) = ew [(ε, i)]) (i j : I) :
    φ (serreKL C (vQ : (RatFunc ℚ)ˣ) i j) =
      ∑ p ∈ Finset.antidiagonal (C.serreN i j),
        ((-1 : RatFunc ℚ) ^ p.1) • dpW C vQ [(ε, i, p.1), (ε, j, 1), (ε, i, p.2)] := by
  rw [serreKL, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, map_mul, map_mul, map_dpow_eq_dpE ε φ hφ, map_dpow_eq_dpE ε φ hφ, hφ,
    ← dpE_one (C := C) (q := vQ)]
  simp only [dpW, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]

theorem posF_θ (i : I) :
    posF (PreF.θ i : PreF (RatFunc ℚ) I) = ew [(true, i)] :=
  posF_word (FreeMonoid.of i)

theorem negF_θ (i : I) :
    negF (PreF.θ i : PreF (RatFunc ℚ) I) = ew [(false, i)] :=
  negF_word (FreeMonoid.of i)

/-- The Serre relator between two words, for either sign. -/
theorem serre_mem_Lrel (ε : Bool) {i j : I} (hij : i ≠ j) (a b : List (Bool × I)) (ℓ : I → ℤ) :
    ew a * (∑ p ∈ Finset.antidiagonal (C.serreN i j),
        ((-1 : RatFunc ℚ) ^ p.1) • dpW C vQ [(ε, i, p.1), (ε, j, 1), (ε, i, p.2)]) * ew b ∈
      Lrel C vQ ℓ := by
  cases ε with
  | true =>
    rw [← map_serreKL true posF posF_θ]
    exact Submodule.subset_span (Or.inr ⟨a, b, i, j, hij, Or.inl rfl⟩)
  | false =>
    rw [← map_serreKL false negF negF_θ]
    exact Submodule.subset_span (Or.inr ⟨a, b, i, j, hij, Or.inr rfl⟩)

/-- **The quantum Serre relations of `U̇` on products of divided powers** (KL III §2.1.1,
relation (v), for `E` (`ε = +`) and `F` (`ε = -`)): for `i ≠ j`, `N = 1 - ⟨i, j_X⟩` and dpss
`a`, `b`, `∑_{n + m = N} (-1)^n E_a E_{εi}^{(n)} E_{εj} E_{εi}^{(m)} E_b 1_λ = 0`. -/
theorem mk_serre_dpW (ε : Bool) {i j : I} (hij : i ≠ j) (a b : List (Bool × I × ℕ)) (lam : X) :
    ∑ p ∈ Finset.antidiagonal (C.serreN i j), ((-1 : RatFunc ℚ) ^ p.1) •
      UDot.mk RD vQ lam (dpW C vQ (a ++ [(ε, i, p.1), (ε, j, 1), (ε, i, p.2)] ++ b)) = 0 := by
  have h := mk_dpW_mul_mul_eq_zero (RD := RD) a b lam
    (serre_mem_Lrel ε hij (dpWord a) (dpWord b) (RD.ellOf lam))
  rw [Finset.mul_sum, Finset.sum_mul, map_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, map_smul, dpW_append, dpW_append]

theorem dpW_pair (l l' : Bool × I) :
    dpW C (vQ : (RatFunc ℚ)ˣ) [(l.1, l.2, 1), (l'.1, l'.2, 1)] = ew [l, l'] := by
  rw [ew_cons]
  simp only [dpW, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, dpE_one]

/-- **The commutation relations of `U̇` on products of divided powers** (KL III (2.4)): for dpss
`a`, `b`, `E_a E_i F_j E_b 1_λ - E_a F_j E_i E_b 1_λ = δ_{ij} [⟨i, λ + b_X⟩]_i E_a E_b 1_λ`. -/
theorem mk_comm_dpW (i j : I) (a b : List (Bool × I × ℕ)) (lam : X) :
    UDot.mk RD vQ lam (dpW C vQ (a ++ [(true, i, 1), (false, j, 1)] ++ b)) -
        UDot.mk RD vQ lam (dpW C vQ (a ++ [(false, j, 1), (true, i, 1)] ++ b)) -
        (if j = i then qbr (qi C vQ i) (wl C (RD.ellOf lam) (dpWord b) i) else 0) •
          UDot.mk RD vQ lam (dpW C vQ (a ++ b)) = 0 := by
  have h := mk_dpW_mul_mul_eq_zero (RD := RD) a b lam (z := commRel C vQ (RD.ellOf lam) (dpWord b) i j)
    (Submodule.subset_span (Or.inl ⟨dpWord a, dpWord b, i, j, rfl⟩))
  rw [commRel, ← dpW_pair (true, i) (false, j), ← dpW_pair (false, j) (true, i), mul_sub, mul_sub,
    sub_mul, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, map_sub, map_sub, map_smul,
    ← dpW_append, ← dpW_append, ← dpW_append, ← dpW_append, ← dpW_append] at h
  exact h

end UDotSide

/-! ## The classes of the generators, and the relations of `_𝒜 U̇` in `K₀(U̇)` -/

section K0Side

attribute [local instance] KLR.KLGamma.vAlgebra

open scoped Classical

variable {RD k} [DecidableEq I]

variable (RD k) in
/-- `∑_g c_g g ↦ ∑_g c_g [E_{d_g} 1_{λ_g}] ∈ K₀(U̇)`. -/
def genK : (DpGen RD →₀ LaurentPolynomial ℤ) →ₗ[LaurentPolynomial ℤ] K0All RD k :=
  Finsupp.linearCombination _ fun g =>
    DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) g.1 (dpC RD k g.2.1 g.1.2 g.1.1 g.2.2)

theorem genK_single (g : DpGen RD) (c : LaurentPolynomial ℤ) :
    genK RD k (Finsupp.single g c) =
      DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) g.1
        (c • dpC RD k g.2.1 g.1.2 g.1.1 g.2.2) := by
  rw [genK, Finsupp.linearCombination_single, DirectSum.of_smul]

/-- `[E(f)] [E(f')] = [E(f f')]` in `K₀(U̇)`. -/
theorem genK_mulG (f f' : DpGen RD →₀ LaurentPolynomial ℤ) :
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

theorem gammaUD_univG_genU (f : DpGen RD →₀ LaurentPolynomial ℤ) :
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
theorem genK_eq_zero (htf : TorsionFreeK0 RD k) {f : DpGen RD →₀ LaurentPolynomial ℤ}
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

/-! ### `γ` -/

variable (htf : TorsionFreeK0 RD k)

include htf in
theorem genK_congr {f f' : DpGen RD →₀ LaurentPolynomial ℤ} (h : genU RD f = genU RD f') :
    genK RD k f = genK RD k f' := by
  rw [← sub_eq_zero, ← map_sub]
  exact genK_eq_zero htf (by rw [map_sub, h, sub_self])

variable (k) in
/-- The underlying function of `γ` on `_𝒜 U̇` (well defined by `gammaFun_eq`). -/
def gammaFun (x : AUD RD vQ) : K0All RD k :=
  genK RD k (Classical.choose ((mem_AUD_iff x.1).1 x.2))

include htf in
theorem gammaFun_eq {x : AUD RD vQ} {f : DpGen RD →₀ LaurentPolynomial ℤ} (h : genU RD f = x) :
    gammaFun k x = genK RD k f :=
  genK_congr htf ((Classical.choose_spec ((mem_AUD_iff x.1).1 x.2)).trans h.symm)

variable (k) in
/-- **KL III Proposition 3.27 (integral form, as a homomorphism of idempotented algebras)**:
`γ : _𝒜 U̇ → K₀(U̇)`, `γ(∑ c_d E_d 1_λ) = ∑ c_d [E_d 1_λ]` (`gammaAlg_genU`, `gammaAlg_E1dp`), a
homomorphism of non-unital rings, `ℤ[q, q⁻¹]`-linear (`gammaAlg_smul`), with `γ(1_λ) = [1_λ]`
(`gammaAlg_one`) — given that every block of `K₀(U̇)` is torsion free (true under `HomGdim`, in
particular for simply-laced data, `homGdim_of_simplyLaced`). -/
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
theorem gammaAlg_genU (f : DpGen RD →₀ LaurentPolynomial ℤ) :
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

/-- **`γ` is `ℤ[q, q⁻¹]`-linear**: `γ(c x) = c γ(x)` (`_𝒜 U̇` is stable under `ℤ[q, q⁻¹]`,
`lpToQ_smul_mem_AUD`). -/
theorem gammaAlg_smul (c : LaurentPolynomial ℤ) (x : AUD RD vQ) :
    gammaAlg k htf ⟨lpToQ c • x.1, lpToQ_smul_mem_AUD c x.2⟩ = c • gammaAlg k htf x := by
  obtain ⟨f, hf⟩ := (mem_AUD_iff x.1).1 x.2
  change gammaFun k _ = c • gammaFun k x
  rw [gammaFun_eq htf hf, gammaFun_eq htf (f := c • f) (by rw [genU_smul, hf]), map_smul]

/-! ### Blocks -/

theorem genK_mapDomain (a : X × X) (f : DpIdx (RD := RD) a.2 a.1 →₀ LaurentPolynomial ℤ) :
    genK RD k (Finsupp.mapDomain (Sigma.mk a) f) =
      DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) a (dpCComb (k := k) a.2 a.1 f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, hf, hg, map_add, map_add]
  | single d c =>
    rw [Finsupp.mapDomain_single, genK_single, dpCComb, Finsupp.linearCombination_single]

theorem genK_genOne (lam : X) :
    genK RD k (Finsupp.single (genOne RD lam) 1) = oneK RD k lam := by
  rw [genK_single, one_smul]
  rfl

/-- **On the block `1_ρ (_𝒜 U̇) 1_λ`, `γ` is the map `gammaUA` of
`Categorification.Diagrams.KL3.GammaIntegral`**: `γ(∑_d c_d E_d 1_λ) = ∑_d c_d [E_d 1_λ]`, in the
`(ρ, λ)`-block of `K₀(U̇)`. -/
theorem gammaAlg_ofB_dpComb (lam ρ : X) (f : DpIdx (RD := RD) lam ρ →₀ LaurentPolynomial ℤ) :
    gammaAlg k htf ⟨ofB RD vQ lam (RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ)
        (U1 RD vQ lam) (dpComb lam ρ f)), ofB_dpComb_mem_AUD f⟩ =
      DirectSum.of (fun p : X × X => K0Kar RD k p.1 p.2) (ρ, lam) (dpCComb lam ρ f) := by
  have e := gammaFun_eq (k := k) htf
    (x := ⟨ofB RD vQ lam (RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ)
        (U1 RD vQ lam) (dpComb lam ρ f)), ofB_dpComb_mem_AUD f⟩)
    (f := Finsupp.mapDomain (Sigma.mk (ρ, lam)) f) (genU_mapDomain (ρ, lam) f)
  exact e.trans (genK_mapDomain (ρ, lam) f)

/-! ### The `sl₂` and Serre relations in `K₀(U̇)` -/

/-- The quantum integer `[n]` in the variable `q^d`, for an integer `n`:
`[n] = -[-n]` for `n < 0`. -/
def qnZ (d n : ℤ) : LaurentPolynomial ℤ := if 0 ≤ n then qn d n.toNat else -qn d (-n).toNat

omit [DecidableEq I] in
theorem lpToQ_qnZ (i : I) (n : ℤ) : lpToQ (qnZ (di C i) n) = qbr (qi C vQ i) n := by
  have hq : ((qi C vQ i : (RatFunc ℚ)ˣ) : RatFunc ℚ) - (((qi C vQ i)⁻¹ : (RatFunc ℚ)ˣ) :
      RatFunc ℚ) ≠ 0 := vQ_zpow_sub_inv_ne_zero (di_pos C i).ne'
  unfold qnZ
  split_ifs with hn
  · rw [lpToQ_qn]
    conv_rhs => rw [← Int.toNat_of_nonneg hn]
    rw [qbr_eq_qint _ hq]; rfl
  · rw [map_neg, lpToQ_qn, show qint (vQ ^ di C i) (-n).toNat =
      qbr (qi C vQ i) ((-n).toNat : ℤ) from (qbr_eq_qint _ hq _).symm,
      Int.toNat_of_nonneg (by omega), qbr_neg, neg_neg]

include htf in
/-- **The quantum Serre relations hold exactly in `K₀(U̇)`** (KL III Proposition 3.24 in `K₀`,
for divided powers and in arbitrary contexts): for `i ≠ j`, `N = 1 - ⟨i, j_X⟩`, `ε = ±` and dpss
`a`, `b`, `∑_{n=0}^{N} (-1)^n [E_a E_{εi}^{(n)} E_{εj} E_{εi}^{(N-n)} E_b 1_λ] = 0`. -/
theorem dpC_serre (ε : Bool) {i j : I} (hij : i ≠ j) (a b : List (Bool × I × ℕ)) (lam ρ : X)
    (hd : ∀ n : Fin (C.serreN i j + 1), wt RD lam
      (dpWord (a ++ [(ε, i, (n : ℕ)), (ε, j, 1), (ε, i, C.serreN i j - n)] ++ b)) = ρ) :
    ∑ n : Fin (C.serreN i j + 1), ((-1 : LaurentPolynomial ℤ) ^ (n : ℕ)) •
      dpC RD k (a ++ [(ε, i, (n : ℕ)), (ε, j, 1), (ε, i, C.serreN i j - n)] ++ b) lam ρ (hd n) =
        0 := by
  refine dpC_relation_of_torsionFree (htf ρ lam) Finset.univ (fun n => (-1) ^ (n : ℕ))
    (fun n => a ++ [(ε, i, (n : ℕ)), (ε, j, 1), (ε, i, C.serreN i j - n)] ++ b) hd ?_
  have h := mk_serre_dpW (RD := RD) ε hij a b lam
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range] at h
  refine (Finset.sum_congr rfl fun n _ => ?_).trans h
  simp only [map_pow, map_neg, map_one]

include htf in
/-- **The relation `E_i F_j = F_j E_i` (`i ≠ j`) holds exactly in `K₀(U̇)`** in arbitrary
contexts of divided powers (KL III Proposition 3.26 in `K₀`). -/
theorem dpC_comm_ne {i j : I} (hij : i ≠ j) (a b : List (Bool × I × ℕ)) (lam ρ : X)
    (h1 : wt RD lam (dpWord (a ++ [(true, i, 1), (false, j, 1)] ++ b)) = ρ)
    (h2 : wt RD lam (dpWord (a ++ [(false, j, 1), (true, i, 1)] ++ b)) = ρ) :
    dpC RD k (a ++ [(true, i, 1), (false, j, 1)] ++ b) lam ρ h1 =
      dpC RD k (a ++ [(false, j, 1), (true, i, 1)] ++ b) lam ρ h2 := by
  have hrel := mk_comm_dpW (RD := RD) i j a b lam
  rw [if_neg (Ne.symm hij), zero_smul, sub_zero] at hrel
  have h := dpC_relation_of_torsionFree (k := k) (htf ρ lam) (Finset.univ : Finset Bool)
    (fun t => bif t then 1 else -1)
    (fun t => bif t then a ++ [(true, i, 1), (false, j, 1)] ++ b
      else a ++ [(false, j, 1), (true, i, 1)] ++ b)
    (fun t => by cases t; exacts [h2, h1])
    (by rw [Fintype.sum_bool]; simpa [sub_eq_add_neg] using hrel)
  rw [Fintype.sum_bool] at h
  have h' : dpC RD k (a ++ [(true, i, 1), (false, j, 1)] ++ b) lam ρ h1 +
      (-1 : LaurentPolynomial ℤ) • dpC RD k (a ++ [(false, j, 1), (true, i, 1)] ++ b) lam ρ h2 =
        0 := by
    simpa using h
  rw [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h'
  exact h'

include htf in
/-- **The relation `E_i F_i - F_i E_i = [⟨i, λ⟩]_i` holds exactly in `K₀(U̇)`** in arbitrary
contexts of divided powers (KL III Proposition 3.25 in `K₀`):
`[E_a E_i F_i E_b 1_λ] = [E_a F_i E_i E_b 1_λ] + [⟨i, λ + b_X⟩]_i [E_a E_b 1_λ]`, with the
(signed) quantum integer `qnZ`. -/
theorem dpC_comm_self (i : I) (a b : List (Bool × I × ℕ)) (lam ρ : X)
    (h1 : wt RD lam (dpWord (a ++ [(true, i, 1), (false, i, 1)] ++ b)) = ρ)
    (h2 : wt RD lam (dpWord (a ++ [(false, i, 1), (true, i, 1)] ++ b)) = ρ)
    (h3 : wt RD lam (dpWord (a ++ b)) = ρ) :
    dpC RD k (a ++ [(true, i, 1), (false, i, 1)] ++ b) lam ρ h1 =
      dpC RD k (a ++ [(false, i, 1), (true, i, 1)] ++ b) lam ρ h2 +
        qnZ (di C i) (wl C (RD.ellOf lam) (dpWord b) i) • dpC RD k (a ++ b) lam ρ h3 := by
  have hrel := mk_comm_dpW (RD := RD) i i a b lam
  rw [if_pos rfl, ← lpToQ_qnZ] at hrel
  have h := dpC_relation_of_torsionFree (k := k) (htf ρ lam) (Finset.univ : Finset (Option Bool))
    (fun o => match o with
      | none => -qnZ (di C i) (wl C (RD.ellOf lam) (dpWord b) i)
      | some true => 1
      | some false => -1)
    (fun o => match o with
      | none => a ++ b
      | some true => a ++ [(true, i, 1), (false, i, 1)] ++ b
      | some false => a ++ [(false, i, 1), (true, i, 1)] ++ b)
    (fun o => by rcases o with _ | _ | _ <;> assumption)
    (by rw [Fintype.sum_option, Fintype.sum_bool]; simp only [map_neg, map_one, neg_smul, one_smul]
        rw [← hrel]; abel)
  rw [Fintype.sum_option, Fintype.sum_bool] at h
  simp only [neg_smul, one_smul] at h
  rw [← sub_eq_zero, ← h]
  abel

/-! ### Proposition 3.28 for `σ`, exactly -/

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
def sigGen (g : DpGen RD) : DpGen RD :=
  ⟨(-g.1.2, -g.1.1), ⟨g.2.1.reverse, wt_neg_dpWord_reverse g.2.2⟩⟩

omit [DecidableEq I] in
theorem genU_mapDomain_sigGen (f : DpGen RD →₀ LaurentPolynomial ℤ) :
    genU RD (Finsupp.mapDomain sigGen f) = sigmaUD RD vQ (genU RD f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, hf, hg, map_add, map_add]
  | single g c =>
    have e : -(g.1.2 + wdp RD g.2.1) = -g.1.1 := by rw [← wt_eq_add_wdp, g.2.2]
    rw [Finsupp.mapDomain_single, genU_single, genU_single, map_smul, sigmaUD_E1dp, e]
    rfl

theorem genK_mapDomain_sigGen (htf : TorsionFreeK0 RD k) (f : DpGen RD →₀ LaurentPolynomial ℤ) :
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

end K0Side

end Categorification.KL3.Diagram
