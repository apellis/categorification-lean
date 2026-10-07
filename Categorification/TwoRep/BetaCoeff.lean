/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.DecompEF

/-!
# The coefficient `β_n = -1` (CL Lemma 5.4)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §5.3, Lemma 5.4 (`lem_coeff`), with the dots normalized to `r_i = 1`.

By `BBw.decompEF_beta`, at a weight `n = wt (q + 1) ≥ 0` the inverse of CL's `ζ` is
`β σ ⊕ ⊕_k comp_k` for a scalar `β`; Lemma 5.4 says `β = -r_i^{-2}`, i.e. `β = -1` for normalized
dots. CL's argument (eq. `eq_coeffreduction`) for `n > 0`, made explicit:

* close the downward strand of `σ' σ = β⁻¹ 1_{FE1_n}` (relation (A2)) on the left, with the left cup
  of `E 1_n`, `n + 1` dots and the right cap (`rtrace`). On the identity this gives the
  degree-zero clockwise bubble in the region `n + 2`, i.e. `1` (CL (4.1)), so the left side is
  `β⁻¹ 1_{E1_n}`;
* by the zigzag identities of `R_n ⊣ E 1_n` and `E 1_n ⊣ R_n` (`sideL_trace`), the closed diagram
  is the curl `curlG` of `τ (E x^{n+1}) τ` on `E 1_n` (closing `E 1_{n-2}` with the left cup and
  the right cap);
* by the nilHecke relations (`tau_powComp_tau`, `powComp_tau`), this curl is `-1`: curls of `τ`
  with fewer than `n` dots vanish by degrees (Lemma 3.1), and the remaining bubbles are the
  degree-zero bubble `1` in the region `n` and negative-degree bubbles.

Hence `β = -1` (`BBw.beta_eq_neg_one`), and the decompositions of CL §5.3 hold with `β = -1`
(`BBw.decompEF`, `BBw.decompFE_of_nonneg`).

## Main declarations

* generic: `rtrace`, `rtrace_id`, `sideL_trace`, `tau_powComp_tau`, `powComp_tau`;
* `StrongSl2.BBw.curl_powComp`, `StrongSl2.BBw.beta_eq_neg_one` (`n ≥ 1`),
  `StrongSl2.BBw.decompEF_pos`, `StrongSl2.BBw.decompFE_pos`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

/-! ## Generic bicategory lemmas -/

section Generic

variable {C : Type u} [Bicategory.{w, v} C] {a b c : C} {Em : a ⟶ b} {Ep : b ⟶ c}
  {Rm : b ⟶ a} {Rp : c ⟶ b}

/-- **Closing the downward strand of an endomorphism of `F E` on the left**: the left cup of
`Ep` (unit of `Ap : Rp ⊣ Ep`) with `y` on its upward strand, `f`, and the right cap of `Ep`
(counit of `Bp : Ep ⊣ Rp`). -/
def rtrace (Ap : Rp ⊣ Ep) (Bp : Ep ⊣ Rp) (y : Ep ⟶ Ep) (f : Ep ≫ Rp ⟶ Ep ≫ Rp) : Ep ⟶ Ep :=
  (ρ_ Ep).inv ≫ Ep ◁ Ap.unit ≫ Ep ◁ Rp ◁ y ≫ (α_ Ep Rp Ep).inv ≫ f ▷ Ep ≫
    (α_ Ep Rp Ep).hom ≫ Ep ◁ Bp.counit ≫ (ρ_ Ep).hom

theorem rtrace_id (Ap : Rp ⊣ Ep) (Bp : Ep ⊣ Rp) (y : Ep ⟶ Ep) :
    rtrace Ap Bp y (𝟙 _) =
      (ρ_ Ep).inv ≫ Ep ◁ (Ap.unit ≫ Rp ◁ y ≫ Bp.counit) ≫ (ρ_ Ep).hom := by
  simp only [rtrace, id_whiskerRight, Category.id_comp, Iso.inv_hom_id_assoc,
    Bicategory.whiskerLeft_comp, Category.assoc]

/-- The left cup and the leftward sideways crossing: closing the downward strand of
`σ' = (mateEquiv Am Ap).symm τ` with the left cup of `Ep` straightens it (zigzag of `Ap`). -/
theorem sideL_trace_aux (Am : Rm ⊣ Em) (Ap : Rp ⊣ Ep) (τ : Em ≫ Ep ⟶ Em ≫ Ep)
    (y : Ep ⟶ Ep) :
    (ρ_ Ep).inv ≫ Ep ◁ Ap.unit ≫ Ep ◁ Rp ◁ y ≫ (α_ Ep Rp Ep).inv ≫
        (mateEquiv Am Ap).symm τ ▷ Ep =
      (λ_ Ep).inv ≫ Am.unit ▷ Ep ≫ (α_ Rm Em Ep).hom ≫ Rm ◁ (τ ≫ Em ◁ y) ≫
        (α_ Rm Em Ep).inv := by
  calc _ = 𝟙 _ ⊗≫ (𝟙 b ◁ (Ep ◁ Ap.unit ≫ Ep ◁ Rp ◁ y) ≫ Am.unit ▷ (Ep ≫ Rp ≫ Ep)) ⊗≫
          Rm ◁ τ ▷ (Rp ≫ Ep) ⊗≫ Rm ◁ Em ◁ Ap.counit ▷ Ep ⊗≫ 𝟙 _ := by
        rw [mateEquiv_symm_apply']; bicategory
    _ = 𝟙 _ ⊗≫ Am.unit ▷ Ep ⊗≫ Rm ◁ ((Em ≫ Ep) ◁ Ap.unit ⊗≫
          ((Em ≫ Ep) ◁ (Rp ◁ y) ≫ τ ▷ (Rp ≫ Ep)) ⊗≫ Em ◁ Ap.counit ▷ Ep) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ Am.unit ▷ Ep ⊗≫ Rm ◁ (((Em ≫ Ep) ◁ Ap.unit ≫ τ ▷ (Rp ≫ Ep)) ⊗≫
          Em ◁ ((Ep ≫ Rp) ◁ y ≫ Ap.counit ▷ Ep)) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ Am.unit ▷ Ep ⊗≫ Rm ◁ (τ ⊗≫ Em ◁ rightZigzag Ap.unit Ap.counit ⊗≫ Em ◁ y) ⊗≫
          𝟙 _ := by
        rw [whisker_exchange, whisker_exchange, rightZigzag]; bicategory
    _ = _ := by
        rw [Ap.right_triangle]; bicategory

/-- **Closing the downward strand of `σ' σ`** (CL eq. `eq_coeffreduction`, first steps): the
closed diagram is the curl of `τ (E y) τ` on `E₊`, closing `E₋` with the left cup and the right
cap. Only the zigzag identities of `Ap : Rp ⊣ Ep` and `Bp : Ep ⊣ Rp` are used. -/
theorem sideL_trace (Am : Rm ⊣ Em) (Ap : Rp ⊣ Ep) (Bm : Em ⊣ Rm) (Bp : Ep ⊣ Rp)
    (τ : Em ≫ Ep ⟶ Em ≫ Ep) (y : Ep ⟶ Ep) :
    rtrace Ap Bp y ((mateEquiv Am Ap).symm τ ≫ mateEquiv Bm Bp τ) =
      curlG Am.unit Bm.counit (τ ≫ Em ◁ y ≫ τ) := by
  have h1 := sideL_trace_aux Am Ap τ y
  have h2 : mateEquiv Bm Bp τ ▷ Ep ≫ (α_ Ep Rp Ep).hom ≫ Ep ◁ Bp.counit ≫ (ρ_ Ep).hom =
      (α_ Rm Em Ep).hom ≫ Rm ◁ τ ≫ (α_ Rm Em Ep).inv ≫ Bm.counit ▷ Ep ≫ (λ_ Ep).hom := by
    rw [← RightwardCrossing.sigma_eq_mateEquiv]
    have := RightwardCrossing.pitchfork_cap Bp.unit Bp.counit τ Bm.counit Bp.left_triangle
    calc _ = (RightwardCrossing.sigma Bp.unit τ Bm.counit ▷ Ep ⊗≫ Ep ◁ Bp.counit) ≫
          (ρ_ Ep).hom := by bicategory
      _ = _ := by rw [this]; bicategory
  unfold rtrace
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [reassoc_of% h1, h2]
  unfold curlG
  bicategory

/-- Dots on the closed strand of a curl are absorbed into the cup. -/
theorem curlG_whiskerRight_comp {R : b ⟶ a} {E : a ⟶ b} {E' : b ⟶ c} (u : 𝟙 b ⟶ R ≫ E)
    (eps : R ≫ E ⟶ 𝟙 b) (z : E ⟶ E) (w : E ≫ E' ⟶ E ≫ E') :
    curlG u eps (z ▷ E' ≫ w) = curlG (u ≫ R ◁ z) eps w := by
  unfold curlG
  bicategory

/-- The curl of dots on the closed strand is a bubble. -/
theorem curlG_whiskerRight {R : b ⟶ a} {E : a ⟶ b} {E' : b ⟶ c} (u : 𝟙 b ⟶ R ≫ E)
    (eps : R ≫ E ⟶ 𝟙 b) (z : E ⟶ E) :
    curlG u eps (z ▷ E') = (λ_ E').inv ≫ (u ≫ R ◁ z ≫ eps) ▷ E' ≫ (λ_ E').hom := by
  unfold curlG
  bicategory

theorem whiskerLeft_powComp (f : a ⟶ b) {g : b ⟶ c} (x : g ⟶ g) :
    ∀ m : ℕ, f ◁ powComp x m = powComp (f ◁ x) m
  | 0 => by simp
  | m + 1 => by rw [powComp_succ, powComp_succ, Bicategory.whiskerLeft_comp,
      whiskerLeft_powComp f x m]

theorem powComp_whiskerRight {f : a ⟶ b} (x : f ⟶ f) (g : b ⟶ c) :
    ∀ m : ℕ, powComp x m ▷ g = powComp (x ▷ g) m
  | 0 => by simp
  | m + 1 => by rw [powComp_succ, powComp_succ, comp_whiskerRight, powComp_whiskerRight x g m]

end Generic

/-! ## The nilHecke algebra -/

section NilHecke

variable {D : Type*} [Category D] [Preadditive D] {X : D} (t p q : X ⟶ X)

/-- `τ x₂^m = ∑_{a<m} x₁^a x₂^{m-1-a} + x₁^m τ` from `τ x₂ - x₁ τ = 1` (diagrammatic order). -/
theorem tau_powComp (hs : t ≫ q - p ≫ t = 𝟙 X) : ∀ m : ℕ,
    t ≫ powComp q m = ∑ a ∈ Finset.range m, powComp p a ≫ powComp q (m - 1 - a) +
      powComp p m ≫ t
  | 0 => by simp
  | m + 1 => by
    have hs' : t ≫ q = 𝟙 X + p ≫ t := by rw [← hs, sub_add_cancel]
    rw [powComp_succ, ← Category.assoc, tau_powComp hs m, Preadditive.add_comp,
      Finset.sum_range_succ, Category.assoc, hs', Preadditive.comp_add, Category.comp_id,
      Preadditive.sum_comp, powComp_succ p m, Category.assoc, ← add_assoc]
    congr 2
    · refine Finset.sum_congr rfl fun a ha => ?_
      have ha' := Finset.mem_range.1 ha
      rw [Category.assoc, ← powComp_succ, show m - 1 - a + 1 = m + 1 - 1 - a by omega]
    · rw [show m + 1 - 1 - m = 0 by omega, powComp_zero, Category.comp_id]

/-- `x₁^m τ = τ x₂^m - ∑_{a<m} x₁^a x₂^{m-1-a}`. -/
theorem powComp_tau (hs : t ≫ q - p ≫ t = 𝟙 X) (m : ℕ) :
    powComp p m ≫ t = t ≫ powComp q m -
      ∑ a ∈ Finset.range m, powComp p a ≫ powComp q (m - 1 - a) := by
  rw [tau_powComp t p q hs m, add_sub_cancel_left]

/-- `τ x₂^{m+1} τ = ∑_{a ≤ m} x₁^a x₂^{m-a} τ`, from `τ² = 0` and `τ x₂ - x₁ τ = 1`. -/
theorem tau_powComp_tau (htt : t ≫ t = 0) (hs : t ≫ q - p ≫ t = 𝟙 X) (m : ℕ) :
    t ≫ powComp q (m + 1) ≫ t =
      ∑ a ∈ Finset.range (m + 1), powComp p a ≫ powComp q (m - a) ≫ t := by
  rw [← Category.assoc, tau_powComp t p q hs (m + 1), Preadditive.add_comp, Category.assoc, htt,
    comp_zero, add_zero, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Category.assoc, show m + 1 - 1 - a = m - a by omega]

end NilHecke

/-! ## Linearity in the graded-Hom bicategory -/

section GradedHom

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]
  [GradedBicategory.IsLinear B k]

namespace GradedHomBicat

open GradedHomCat

variable {a b c : GradedHomBicat B}

theorem curlG_zero {R : b ⟶ a} {E : a ⟶ b} {E' : b ⟶ c} (u : 𝟙 b ⟶ R ≫ E)
    (eps : R ≫ E ⟶ 𝟙 b) : curlG u eps (0 : E ≫ E' ⟶ E ≫ E') = 0 := by
  simp only [curlG, whiskerLeft_zero, zero_comp, comp_zero]

theorem curlG_sum {R : b ⟶ a} {E : a ⟶ b} {E' : b ⟶ c} (u : 𝟙 b ⟶ R ≫ E)
    (eps : R ≫ E ⟶ 𝟙 b) {ι : Type*} (s : Finset ι) (w : ι → (E ≫ E' ⟶ E ≫ E')) :
    curlG u eps (∑ i ∈ s, w i) = ∑ i ∈ s, curlG u eps (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using curlG_zero u eps
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, StrongSl2.curlG_add, ih]

theorem curlG_sub {R : b ⟶ a} {E : a ⟶ b} {E' : b ⟶ c} (u : 𝟙 b ⟶ R ≫ E)
    (eps : R ≫ E ⟶ 𝟙 b) (w₁ w₂ : E ≫ E' ⟶ E ≫ E') :
    curlG u eps (w₁ - w₂) = curlG u eps w₁ - curlG u eps w₂ := by
  have h := StrongSl2.curlG_add u eps (w₁ - w₂) w₂
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

theorem rtrace_smul {Ep : b ⟶ c} {Rp : c ⟶ b} (Ap : Rp ⊣ Ep) (Bp : Ep ⊣ Rp) (y : Ep ⟶ Ep)
    (t : k) (f : Ep ≫ Rp ⟶ Ep ≫ Rp) : rtrace Ap Bp y (t • f) = t • rtrace Ap Bp y f := by
  simp only [rtrace, smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]

theorem isHomogeneous_curlG {R : b ⟶ a} {E : a ⟶ b} {E' : b ⟶ c} {u : 𝟙 b ⟶ R ≫ E}
    {eps : R ≫ E ⟶ 𝟙 b} {w : E ≫ E' ⟶ E ≫ E'} {du dw de : ℤ} (hu : IsHomogeneous u du)
    (hw : IsHomogeneous w dw) (he : IsHomogeneous eps de) :
    IsHomogeneous (curlG u eps w) (du + dw + de) :=
  ((isHomogeneous_leftUnitor_inv _).comp ((isHomogeneous_whiskerRight hu _).comp
    ((isHomogeneous_associator_hom _ _ _).comp ((isHomogeneous_whiskerLeft _ hw).comp
      ((isHomogeneous_associator_inv _ _ _).comp ((isHomogeneous_whiskerRight he _).comp
        (isHomogeneous_leftUnitor_hom _) rfl) rfl) rfl) rfl) rfl) rfl).of_eq (by ring)

end GradedHomBicat

end GradedHom

/-! ## `β = -1` for `n ≥ 1` -/

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, KrullSchmidtCat.HomFinite k (a ⟶ b)] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]

namespace StrongSl2

open GradedHomBicat GradedHomCat

variable {S : StrongSl2 k B} (hS : S.BBw)

omit [∀ a b : B, KrullSchmidtCat.HomFinite k (a ⟶ b)] [∀ a b : B, IsIdempotentComplete (a ⟶ b)] in
theorem cupD_zero {q : ℤ} (A : S.grR q ⊣ S.grE q) : S.cupD A 0 = A.unit := by
  simp [cupD]

omit [∀ a b : B, KrullSchmidtCat.HomFinite k (a ⟶ b)] [∀ a b : B, IsIdempotentComplete (a ⟶ b)] in
/-- Dots on the two strands of `E E` commute. -/
theorem powComp_whiskerRight_comm {q : ℤ} (i j : ℕ) :
    powComp (S.grDotN q ▷ S.grE (q + 1)) i ≫ powComp (S.grE q ◁ S.grDotN (q + 1)) j =
      powComp (S.grE q ◁ S.grDotN (q + 1)) j ≫ powComp (S.grDotN q ▷ S.grE (q + 1)) i := by
  rw [← powComp_whiskerRight, ← whiskerLeft_powComp, whisker_exchange]

/-- **Curls with fewer than `n` dots vanish** (by degrees, Lemma 3.1): at the weight
`n = wt (q + 1)`, the curl of `τ` on `E 1_n` closing `E 1_{n-2}` with `a < n` dots is `0`. -/
theorem BBw.curlG_cupD_eq_zero {q : ℤ} {a : ℕ} (ha : (a : ℤ) < S.wt (q + 1)) :
    curlG (S.cupD (hS.leftAdjN q) a) (S.grCounit q) (S.grCross q) = 0 :=
  hS.grE_end_eq_zero (isHomogeneous_curlG (S.isHomogeneous_cupD _ (hS.leftAdjN_spec q).1 a)
    (isHomogeneous_of₂ _ _) (isHomogeneous_incl₂ _)) (by omega)

omit [∀ a b : B, KrullSchmidtCat.HomFinite k (a ⟶ b)] [∀ a b : B, IsIdempotentComplete (a ⟶ b)] in
/-- `curl(x₁^a x₂^b τ) = x^b curl(x^a τ)`. -/
theorem curlG_dots_tau {q : ℤ} (A : S.grR q ⊣ S.grE q) (a b : ℕ) :
    curlG A.unit (S.grCounit q) (powComp (S.grDotN q ▷ S.grE (q + 1)) a ≫
        powComp (S.grE q ◁ S.grDotN (q + 1)) b ≫ S.grCross q) =
      powComp (S.grDotN (q + 1)) b ≫ curlG (S.cupD A a) (S.grCounit q) (S.grCross q) := by
  rw [← Category.assoc, powComp_whiskerRight_comm, Category.assoc, ← whiskerLeft_powComp,
    curlG_whiskerLeft_comp, ← powComp_whiskerRight, curlG_whiskerRight_comp]
  rfl

omit [∀ a b : B, KrullSchmidtCat.HomFinite k (a ⟶ b)] [∀ a b : B, IsIdempotentComplete (a ⟶ b)] in
/-- `curl(x₁^a x₂^b) = x^b (bubble with a dots)`. -/
theorem curlG_dots {q : ℤ} (A : S.grR q ⊣ S.grE q) (a b : ℕ) :
    curlG A.unit (S.grCounit q) (powComp (S.grDotN q ▷ S.grE (q + 1)) a ≫
        powComp (S.grE q ◁ S.grDotN (q + 1)) b) =
      powComp (S.grDotN (q + 1)) b ≫
        ((λ_ (S.grE (q + 1))).inv ≫ S.cwBub A a ▷ S.grE (q + 1) ≫ (λ_ (S.grE (q + 1))).hom) := by
  rw [powComp_whiskerRight_comm, ← whiskerLeft_powComp, curlG_whiskerLeft_comp,
    ← powComp_whiskerRight, curlG_whiskerRight]
  rfl

/-- **The curl with `n` dots is `-1`** (CL (4.9) at the weight `n ≥ 1`): moving the dots
through the crossing (nilHecke), the curl of `τ` vanishes and the bubbles are those of degree
`≤ 0` in the region `n`. -/
theorem BBw.curlG_cupD_self {q : ℤ} (hn : 1 ≤ S.wt (q + 1)) :
    curlG (S.cupD (hS.leftAdjN q) (S.wt (q + 1)).toNat) (S.grCounit q) (S.grCross q) =
      -𝟙 _ := by
  set N := (S.wt (q + 1)).toNat with hN
  have hNn : (N : ℤ) = S.wt (q + 1) := Int.toNat_of_nonneg (by omega)
  set A := hS.leftAdjN q
  have hcup : S.cupD A N = A.unit ≫ S.grR q ◁ powComp (S.grDotN q) N := rfl
  have hz : curlG A.unit (S.grCounit q) (S.grCross q) = 0 := by
    rw [← cupD_zero A]
    exact hS.curlG_cupD_eq_zero (by omega)
  rw [hcup, ← curlG_whiskerRight_comp, powComp_whiskerRight,
    powComp_tau _ _ _ (S.grDotN_slide_right q), curlG_sub, curlG_sum, ← whiskerLeft_powComp,
    curlG_comp_whiskerLeft, hz, zero_comp,
    zero_sub, Finset.sum_congr rfl (fun a _ => curlG_dots A a (N - 1 - a)),
    Finset.sum_eq_single_of_mem (N - 1) (Finset.mem_range.2 (by omega))]
  · rw [show N - 1 - (N - 1) = 0 by omega, powComp_zero, Category.id_comp,
      BBw.cwBub_deg_zero hS hn, id_whiskerRight, Category.id_comp, Iso.inv_hom_id]
  · intro a ha hne
    have ha' := Finset.mem_range.1 ha
    rw [hS.cwBub_eq_zero (by omega), zero_whiskerRight, zero_comp, comp_zero, comp_zero]

/-- **The closed diagram of CL eq. `eq_coeffreduction`**: at the weight `n ≥ 1`, the curl of
`τ (E x^{n+1}) τ` on `E 1_n` is `-1`. -/
theorem BBw.curlG_tau_dots_tau {q : ℤ} (hn : 1 ≤ S.wt (q + 1)) :
    curlG (hS.leftAdjN q).unit (S.grCounit q) (S.grCross q ≫
        S.grE q ◁ powComp (S.grDotN (q + 1)) ((S.wt (q + 1)).toNat + 1) ≫ S.grCross q) =
      -𝟙 _ := by
  set N := (S.wt (q + 1)).toNat with hN
  have hNn : (N : ℤ) = S.wt (q + 1) := Int.toNat_of_nonneg (by omega)
  rw [whiskerLeft_powComp, tau_powComp_tau _ _ _ (S.grCross_sq q) (S.grDotN_slide_right q),
    curlG_sum]
  simp only [curlG_dots_tau]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.sub_self, powComp_zero,
    Category.id_comp, hS.curlG_cupD_self hn]
  intro a ha
  rw [hS.curlG_cupD_eq_zero (by have := Finset.mem_range.1 ha; omega), comp_zero]

/-- **CL Lemma 5.4, `β_n = -r_i^{-2}`, for `n ≥ 1`** (with normalized dots, `β = -1`): if
`σ' ≫ β σ = 1_{FE1_n}` and `F E 1_n ≠ 0`, then `β = -1`. -/
theorem BBw.beta_eq_neg_one {q : ℤ} (hn : 1 ≤ S.wt (q + 1)) {β : k}
    (hβ : hS.sideL q ≫ (β • S.grSigma q) = 𝟙 _)
    (hER : ¬ IsZero (S.grE (q + 1) ≫ S.grR (q + 1))) : β = -1 := by
  set N := (S.wt (q + 1)).toNat with hN
  have hNn : (N : ℤ) = S.wt (q + 1) := Int.toNat_of_nonneg (by omega)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_smul, comp_zero] at hβ
    exact hER ((IsZero.iff_id_eq_zero _).2 hβ.symm)
  have h1 : hS.sideL q ≫ S.grSigma q = β⁻¹ • 𝟙 _ := by
    rw [← hβ, Linear.comp_smul, smul_smul, inv_mul_cancel₀ hβ0, one_smul]
  have htr := sideL_trace (hS.leftAdjN q) (hS.leftAdjN (q + 1)) (S.grAdj q) (S.grAdj (q + 1))
    (S.grCross q) (powComp (S.grDotN (q + 1)) (N + 1))
  rw [← grSigma_eq_mateEquiv] at htr
  change rtrace _ _ _ (hS.sideL q ≫ S.grSigma q) = _ at htr
  have hbub : S.cwBub (hS.leftAdjN (q + 1)) (N + 1) = 𝟙 _ := by
    have h := BBw.cwBub_deg_zero hS (q := q + 1) (by rw [S.wt_add_one]; omega)
    rwa [show (S.wt (q + 1 + 1)).toNat - 1 = N + 1 by rw [S.wt_add_one]; omega] at h
  rw [h1, rtrace_smul, rtrace_id, grAdj_counit, grAdj_counit,
    show (hS.leftAdjN (q + 1)).unit ≫ S.grR (q + 1) ◁ powComp (S.grDotN (q + 1)) (N + 1) ≫
      S.grCounit (q + 1) = S.cwBub (hS.leftAdjN (q + 1)) (N + 1) from rfl, hbub,
    Bicategory.whiskerLeft_id, Category.id_comp, Iso.inv_hom_id, hS.curlG_tau_dots_tau hn] at htr
  have hE : 𝟙 (S.grE (q + 1)) ≠ 0 := by
    intro h0
    apply hER
    refine (IsZero.iff_id_eq_zero _).2 ?_
    rw [← Bicategory.id_whiskerRight, h0, zero_whiskerRight]
  have h2 : (β⁻¹ + 1) • 𝟙 (S.grE (q + 1)) = 0 := by rw [add_smul, htr, one_smul, neg_add_cancel]
  have h3 : β⁻¹ = -1 := eq_neg_of_add_eq_zero_left ((smul_eq_zero.1 h2).resolve_right hE)
  rw [← inv_inv β, h3, inv_neg, inv_one]

/-- **CL relations (A2), (A5) with `β = -1`, `n ≥ 1`**: the decompositions of `1_{FE1_n}` and
`1_{EF1_n}` (KL III `eq_ident_decomp` for `n > 0`, with CL's `-r_i^{-2} = -1`). -/
theorem BBw.decompEF_pos {q : ℤ} (hn : 1 ≤ S.wt (q + 1)) :
    hS.sideL q ≫ S.grSigma q = -𝟙 _ ∧
      -(S.grSigma q ≫ hS.sideL q) +
        ∑ j ∈ Finset.range (S.wt (q + 1)).toNat, hS.compK q j ≫ S.cupD (hS.leftAdjN q) j =
          𝟙 _ := by
  obtain ⟨β, h1, h2⟩ := hS.decompEF_beta (q := q) (by omega)
  by_cases hER : IsZero (S.grE (q + 1) ≫ S.grR (q + 1))
  · refine ⟨hER.eq_of_src _ _, ?_⟩
    rw [← h2, hER.eq_of_tgt (S.grSigma q) 0, zero_comp, neg_zero, smul_zero]
  · have hβ := hS.beta_eq_neg_one hn h1 hER
    subst hβ
    refine ⟨?_, ?_⟩
    · rw [← h1, Linear.comp_smul, neg_smul, one_smul, neg_neg]
    · rw [← h2, neg_smul, one_smul]

end StrongSl2

end Categorification.TwoRep
