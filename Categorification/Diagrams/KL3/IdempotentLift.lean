/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Idempotent
import Categorification.Algebra.Graded.ProjectiveCover
import Categorification.Algebra.IdempotentEquiv

/-!
# Idempotents of graded algebras and indecomposable projectives

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.8.1–§3.8.4
("Let `1 = e_1 + ⋯ + e_k` be a decomposition of `1 ∈ A` into a sum of mutually-orthogonal
minimal idempotents, then `A e_s` is an indecomposable projective `A`-module"; Propositions 3.31
and 3.34; and, in §3.8.4, the minimal degree `0` idempotents of `R(ν) ⊗ R(ν')`).

For a `ℤ`-graded algebra `A` over a field `k` with a graded dimension (`HasGdim 𝒜`):

* `GProj.Iso.exists_isEquivPair`: an isomorphism `A e ≅ (A e'){s}` of graded projectives
  (`e`, `e'` idempotents of degree `0`) comes from a pair `x ∈ 𝒜_{-s}`, `y ∈ 𝒜_s` with
  `x y = e`, `y x = e'` (`IsEquivPair`), by right multiplication;
* `exists_indec_decomp`: every idempotent `f` of degree `0` is a finite sum of mutually
  orthogonal idempotents `g_j ≤ f` of degree `0` with `A g_j` indecomposable;
* `isNilpotent_or_isUnit_corner`: if `A f` is indecomposable, every `y ∈ f 𝒜_0 f` is nilpotent
  or invertible in `f 𝒜_0 f` (the corner is local).
-/

noncomputable section

namespace Categorification.Graded

open DirectSum Module

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜]

/-! ## Isomorphisms of `A e` come from equivalent idempotents -/

theorem leftIdeal_self_mem {e : A} (he : IsIdempotentElem e) : e ∈ leftIdeal e := he.eq

/-- Every `A`-linear map `φ : A e → M` is determined by `φ(e)`: `φ(a) = a • φ(e)`. -/
theorem map_leftIdeal_eq {e : A} (he : IsIdempotentElem e) {M : Type*} [AddCommGroup M]
    [Module A M] (φ : leftIdeal e →ₗ[A] M) (a : leftIdeal e) :
    φ a = (a : A) • φ ⟨e, leftIdeal_self_mem he⟩ := by
  rw [← map_smul]
  congr 1
  exact Subtype.ext (by
    show (a : A) = (a : A) * e
    exact a.2.symm)

/-- **Isomorphisms of cyclic graded projectives come from equivalent idempotents.** If
`A e ≅ (A e'){s}` (degree-preserving), then `x = φ(e) ∈ 𝒜_{-s}` and `y = φ⁻¹(e') ∈ 𝒜_s` satisfy
`x y = e`, `y x = e'`, `x y x = x`, `y x y = y`. -/
theorem GProj.Iso.exists_isEquivPair {e e' : A} {he : IsIdempotentElem e}
    {he' : IsIdempotentElem e'} {he0 : e ∈ 𝒜 0} {he0' : e' ∈ 𝒜 0} {s : ℤ}
    (φ : (GProj.ofIdempotent e he he0).Iso ((GProj.ofIdempotent e' he' he0').shift s)) :
    ∃ x y : A, x ∈ 𝒜 (-s) ∧ y ∈ 𝒜 s ∧ IsEquivPair x y e e' := by
  set E : leftIdeal e := ⟨e, leftIdeal_self_mem he⟩
  set E' : leftIdeal e' := ⟨e', leftIdeal_self_mem he'⟩
  let f : leftIdeal e ≃ₗ[A] leftIdeal e' := φ.toLinearEquiv
  have hf : ∀ a : leftIdeal e, f a = (a : A) • f E := fun a =>
    map_leftIdeal_eq he f.toLinearMap a
  have hg : ∀ b : leftIdeal e', f.symm b = (b : A) • f.symm E' := fun b =>
    map_leftIdeal_eq he' f.symm.toLinearMap b
  set x : A := (f E : A)
  set y : A := (f.symm E' : A)
  have hxmem : x ∈ 𝒜 (-s) := by
    have h0 : E ∈ (GProj.ofIdempotent e he he0).grading 0 := he0
    have := φ.map_mem' h0
    change ((f E : leftIdeal e') : A) ∈ 𝒜 (0 - s) at this
    simpa using this
  have hymem : y ∈ 𝒜 s := by
    have h0 : E' ∈ ((GProj.ofIdempotent e' he' he0').shift s).grading s := by
      show (e' : A) ∈ 𝒜 (s - s)
      rw [sub_self]; exact he0'
    exact φ.symm_map_mem' h0
  -- `x ∈ A e'` and `y ∈ A e`
  have hxe' : x * e' = x := (f E).2
  have hye : y * e = y := (f.symm E').2
  -- `x y = e`
  have hxy : x * y = e := by
    have h1 : f.symm (f E) = E := f.symm_apply_apply E
    rw [hg (f E)] at h1
    exact congrArg Subtype.val h1
  -- `y x = e'`
  have hyx : y * x = e' := by
    have h1 : f (f.symm E') = E' := f.apply_symm_apply E'
    rw [hf (f.symm E')] at h1
    exact congrArg Subtype.val h1
  refine ⟨x, y, hxmem, hymem, hxy, hyx, ?_, ?_⟩
  · rw [hxy]
    have : e * x = x := by
      have h1 := hf E
      have h2 : (f E : A) = (E : A) * (f E : A) := congrArg Subtype.val h1
      exact h2.symm
    exact this
  · rw [hyx]
    have h1 := hg E'
    have h2 : (f.symm E' : A) = (E' : A) * (f.symm E' : A) := congrArg Subtype.val h1
    exact h2.symm

/-! ## Right multiplications and the corner `f 𝒜_0 f` -/

/-- Right multiplication by `y ∈ f A f` on `A f`. -/
def rmul {f : A} (y : A) (hy : y * f = y) : leftIdeal f →ₗ[A] leftIdeal f where
  toFun a := ⟨(a : A) * y, by
    show (a : A) * y * f = (a : A) * y
    rw [mul_assoc, hy]⟩
  map_add' a b := Subtype.ext (add_mul _ _ _)
  map_smul' c a := Subtype.ext (by
    show c * (a : A) * y = c * ((a : A) * y)
    rw [mul_assoc])

@[simp] theorem rmul_apply {f : A} (y : A) (hy : y * f = y) (a : leftIdeal f) :
    (rmul y hy a : A) = (a : A) * y := rfl

theorem rmul_preservesGrading {f : A} (he : IsIdempotentElem f) (hf0 : f ∈ 𝒜 0) {y : A}
    (hy : y * f = y) (hy0 : y ∈ 𝒜 0) :
    PreservesGrading (GProj.ofIdempotent f he hf0).grading (GProj.ofIdempotent f he hf0).grading
      (rmul y hy) := fun d a ha => by
  have ha' : ((show leftIdeal f from a) : A) ∈ 𝒜 d := ha
  show ((show leftIdeal f from a) : A) * y ∈ 𝒜 d
  simpa using SetLike.GradedMul.mul_mem ha' hy0

variable [HasGdim 𝒜]

/-- **The corner of an indecomposable is local**: if `A f` is indecomposable (`f` an idempotent of
degree `0`), every `y ∈ f 𝒜_0 f` is nilpotent or invertible in `f 𝒜_0 f`. -/
theorem isNilpotent_or_isUnit_corner {f : A} {he : IsIdempotentElem f} {hf0 : f ∈ 𝒜 0}
    (hind : (GProj.ofIdempotent f he hf0).IsIndec A) {y : A} (hy0 : y ∈ 𝒜 0)
    (hyc : f * y * f = y) :
    IsNilpotent y ∨ ∃ z : A, z ∈ 𝒜 0 ∧ f * z * f = z ∧ y * z = f ∧ z * y = f := by
  have hyr : y * f = y := by rw [← hyc, mul_assoc, he.eq]
  have hyl : f * y = y := by
    calc f * y = f * (f * y * f) := by rw [hyc]
      _ = f * y * f := by rw [← mul_assoc, ← mul_assoc, he.eq]
      _ = y := hyc
  set R := rmul (f := f) y hyr
  set F : leftIdeal f := ⟨f, leftIdeal_self_mem he⟩
  rcases hind.bijective_or_isNilpotent (f := R) (rmul_preservesGrading he hf0 hyr hy0) with
    hb | ⟨n, hn⟩
  · -- a preimage of `f`, made homogeneous of degree `0`
    obtain ⟨a0, ha⟩ := hb.2 F
    set a : leftIdeal f := a0
    have ha' : (a : A) * y = f := congrArg Subtype.val ha
    set a₀ : A := (decompose 𝒜 (a : A) 0 : A)
    have hmul : ∀ b : A, (decompose 𝒜 (b * y) 0 : A) = (decompose 𝒜 b 0 : A) * y := by
      intro b
      have := coe_decompose_mul_add_of_right_mem 𝒜 (a := b) (i := 0) hy0
      simpa using this
    have hmulf : ∀ b : A, (decompose 𝒜 (b * f) 0 : A) = (decompose 𝒜 b 0 : A) * f := by
      intro b
      have := coe_decompose_mul_add_of_right_mem 𝒜 (a := b) (i := 0) hf0
      simpa using this
    have hf00 : (decompose 𝒜 f 0 : A) = f := decompose_of_mem_same 𝒜 hf0
    have ha₀y : a₀ * y = f := by rw [← hmul, ha', hf00]
    have ha₀0 : a₀ ∈ 𝒜 0 := (decompose 𝒜 (a : A) 0).2
    set z := f * a₀
    have hz0 : z ∈ 𝒜 0 := by simpa using SetLike.GradedMul.mul_mem hf0 ha₀0
    have ha₀f : a₀ * f = a₀ := by
      have : (a : A) * f = a := a.2
      rw [← hmulf, this]
    refine Or.inr ⟨z, hz0, by
      show f * (f * a₀) * f = f * a₀
      rw [mul_assoc, mul_assoc, ha₀f, ← mul_assoc, he.eq], ?_, ?_⟩
    · -- `y z = f` by injectivity of right multiplication
      have hzy : z * y = f := by rw [mul_assoc, ha₀y, he.eq]
      have hyz_mem : y * z * f = y * z := by rw [mul_assoc, mul_assoc, ha₀f]
      have hinj := hb.1 (a₁ := ⟨y * z, hyz_mem⟩) (a₂ := F) (Subtype.ext (by
        show y * z * y = f * y
        rw [mul_assoc, hzy, hyr, hyl]))
      exact congrArg Subtype.val hinj
    · rw [mul_assoc, ha₀y, he.eq]
  · -- `R^n = 0`, so `y^n = f y^n = 0`
    left
    refine ⟨n + 1, ?_⟩
    have hpow : ∀ m : ℕ, ((R ^ m) F : A) = f * y ^ m := by
      intro m
      induction m with
      | zero => simp [F]
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, rmul_apply, ih, pow_succ, mul_assoc]
    have hn1 : R ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
    have h0 := hpow (n + 1)
    rw [hn1] at h0
    have hyn : f * y ^ (n + 1) = y ^ (n + 1) := by rw [pow_succ', ← mul_assoc, hyl]
    rw [← hyn, ← h0]
    rfl

/-! ## Decompositions into indecomposable idempotents -/

/-- The degree-zero corner `f 𝒜_0 f`. -/
def cornerZero (f : A) : Submodule k A where
  carrier := {a | a ∈ 𝒜 0 ∧ f * a * f = a}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by rw [mul_add, add_mul, ha.2, hb.2]⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  smul_mem' c a ha := ⟨Submodule.smul_mem _ c ha.1, by rw [mul_smul_comm, smul_mul_assoc, ha.2]⟩

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
theorem cornerZero_le {f g : A} (hgf : f * g = g) (hfg : g * f = g) :
    cornerZero (𝒜 := 𝒜) g ≤ cornerZero (𝒜 := 𝒜) f := by
  rintro a ⟨ha0, ha⟩
  refine ⟨ha0, ?_⟩
  have h1 : f * a = a := by rw [← ha, ← mul_assoc, ← mul_assoc, hgf]
  have h2 : a * f = a := by rw [← ha, mul_assoc, hfg]
  rw [h1, h2]

/-- An idempotent `g ≤ f`: `f g = g f = g`. -/
structure IdemLe (g f : A) : Prop where
  idem : IsIdempotentElem g
  deg0 : g ∈ 𝒜 0
  left : f * g = g
  right : g * f = g

/-- **Decomposition into indecomposable idempotents**: every idempotent `f` of degree `0` is a
finite sum of mutually orthogonal idempotents `g_j ≤ f` of degree `0` with `A g_j`
indecomposable. -/
theorem exists_indec_decomp : ∀ (n : ℕ) (f : A), IsIdempotentElem f → f ∈ 𝒜 0 →
    finrank k (cornerZero (𝒜 := 𝒜) f) < n →
    ∃ (m : ℕ) (g : Fin m → A) (hg : ∀ j, IdemLe (𝒜 := 𝒜) (g j) f),
      (∀ j, (GProj.ofIdempotent (g j) (hg j).idem (hg j).deg0).IsIndec A) ∧
      (∀ j j', j ≠ j' → g j * g j' = 0) ∧ ∑ j, g j = f
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, f, he, hf0, hn => by
    by_cases hf : f = 0
    · exact ⟨0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, by simp [hf]⟩
    by_cases hind : (GProj.ofIdempotent f he hf0).IsIndec A
    · exact ⟨1, fun _ => f, fun _ => ⟨he, hf0, he.eq, he.eq⟩, fun _ => hind,
        fun j j' h => absurd (Subsingleton.elim j j') h, by simp⟩
    -- a nontrivial idempotent endomorphism of `A f`
    have hnt : Nontrivial (leftIdeal f) :=
      ⟨⟨⟨f, leftIdeal_self_mem he⟩, 0, fun h => hf (congrArg Subtype.val h)⟩⟩
    obtain ⟨φ, hφ, hφi, hφ0, hφ1⟩ : ∃ φ ∈ endZero A (GProj.ofIdempotent f he hf0).grading,
        IsIdempotentElem φ ∧ φ ≠ 0 ∧ φ ≠ 1 := by
      by_contra hne
      push_neg at hne
      exact hind ⟨hnt, fun φ hφ hφi => by
        by_cases h0 : φ = 0
        · exact Or.inl h0
        · exact Or.inr (hne φ hφ hφi h0)⟩
    set F : leftIdeal f := ⟨f, leftIdeal_self_mem he⟩
    set φ' : leftIdeal f →ₗ[A] leftIdeal f := φ
    set z : A := (φ' F : A) with hzdef
    have hφa : ∀ a : leftIdeal f, (φ' a : A) = (a : A) * z := fun a => by
      have := map_leftIdeal_eq he φ' a
      exact congrArg Subtype.val this
    have hz0 : z ∈ 𝒜 0 := hφ (d := 0) (x := F) hf0
    have hzf : z * f = z := (φ' F).2
    have hfz : f * z = z := (hφa F).symm
    have hzz : z * z = z := by
      have h1 : ((φ' (φ' F) : leftIdeal f) : A) = (φ' F : A) :=
        congrArg (fun ψ : Module.End A (GProj.ofIdempotent f he hf0).carrier =>
          (((show leftIdeal f →ₗ[A] leftIdeal f from ψ) F : leftIdeal f) : A)) hφi.eq
      rw [hφa (φ' F)] at h1
      exact h1
    have hzne0 : z ≠ 0 := fun h => hφ0 (LinearMap.ext fun a => Subtype.ext (by
      have := hφa a
      rw [h, mul_zero] at this
      exact this))
    have hznef : z ≠ f := fun h => hφ1 (LinearMap.ext fun a => Subtype.ext (by
      have := hφa a
      rw [h] at this
      exact this.trans (show ((show leftIdeal f from a) : A) * f = _ from a.2)))
    -- the two halves
    set z' := f - z
    have hz'z' : IsIdempotentElem z' := by
      show (f - z) * (f - z) = f - z
      rw [sub_mul, mul_sub, mul_sub, he.eq, hfz, hzf, hzz]; abel
    have hz'0 : z' ∈ 𝒜 0 := sub_mem hf0 hz0
    have hfz' : f * z' = z' := by show f * (f - z) = f - z; rw [mul_sub, he.eq, hfz]
    have hz'f : z' * f = z' := by show (f - z) * f = f - z; rw [sub_mul, he.eq, hzf]
    have hzz' : z * z' = 0 := by show z * (f - z) = 0; rw [mul_sub, hzf, hzz, sub_self]
    have hz'z : z' * z = 0 := by show (f - z) * z = 0; rw [sub_mul, hfz, hzz, sub_self]
    -- dimension drops
    have hlt : ∀ g : A, IsIdempotentElem g → f * g = g → g * f = g → g ≠ f →
        finrank k (cornerZero (𝒜 := 𝒜) g) < n := by
      intro g hg hfg hgf hne
      have hle := cornerZero_le (𝒜 := 𝒜) hfg hgf
      have hlt' : cornerZero (𝒜 := 𝒜) g < cornerZero (𝒜 := 𝒜) f := by
        refine lt_of_le_of_ne hle fun heq => hne ?_
        have hmem : f ∈ cornerZero (𝒜 := 𝒜) g := by
          rw [heq]; exact ⟨hf0, by rw [he.eq, he.eq]⟩
        have := hmem.2
        rw [hgf, hg.eq] at this
        exact this
      haveI : FiniteDimensional k (cornerZero (𝒜 := 𝒜) f) :=
        FiniteDimensional.of_injective (V₂ := 𝒜 0)
          ({ toFun := fun a => ⟨a.1, a.2.1⟩, map_add' := fun _ _ => rfl,
             map_smul' := fun _ _ => rfl } : cornerZero (𝒜 := 𝒜) f →ₗ[k] 𝒜 0)
          (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
      have := Submodule.finrank_lt_finrank_of_lt hlt'
      omega
    obtain ⟨m₁, g₁, hg₁, hi₁, ho₁, hs₁⟩ := exists_indec_decomp n z hzz hz0
      (hlt z hzz hfz hzf hznef)
    obtain ⟨m₂, g₂, hg₂, hi₂, ho₂, hs₂⟩ := exists_indec_decomp n z' hz'z' hz'0
      (hlt z' hz'z' hfz' hz'f (fun h => hzne0 (by
        have : f - z = f := h
        exact sub_eq_self.1 this)))
    -- concatenate
    refine ⟨m₁ + m₂, Fin.append g₁ g₂, fun j => ?_, fun j => ?_, fun j j' h => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · rw [Fin.append_left]
        obtain ⟨hi, h0, hl, hr⟩ := hg₁ j
        exact ⟨hi, h0, by rw [← hl, ← mul_assoc, hfz], by rw [← hr, mul_assoc, hzf]⟩
      · rw [Fin.append_right]
        obtain ⟨hi, h0, hl, hr⟩ := hg₂ j
        exact ⟨hi, h0, by rw [← hl, ← mul_assoc, hfz'], by rw [← hr, mul_assoc, hz'f]⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.append_left]; exact hi₁ j
      · simp only [Fin.append_right]; exact hi₂ j
    · -- orthogonality across the two halves
      have cross : ∀ a b, (Fin.append g₁ g₂ (Fin.castAdd m₂ a)) *
          (Fin.append g₁ g₂ (Fin.natAdd m₁ b)) = 0 := fun a b => by
        rw [Fin.append_left, Fin.append_right, ← (hg₁ a).right, ← (hg₂ b).left, mul_assoc,
          ← mul_assoc z, hzz', zero_mul, mul_zero]
      have cross' : ∀ a b, (Fin.append g₁ g₂ (Fin.natAdd m₁ b)) *
          (Fin.append g₁ g₂ (Fin.castAdd m₂ a)) = 0 := fun a b => by
        rw [Fin.append_left, Fin.append_right, ← (hg₂ b).right, ← (hg₁ a).left, mul_assoc,
          ← mul_assoc z', hz'z, zero_mul, mul_zero]
      revert h
      refine Fin.addCases (fun a => ?_) (fun b => ?_) j <;>
        refine Fin.addCases (fun a' => ?_) (fun b' => ?_) j' <;> intro h
      · rw [Fin.append_left, Fin.append_left]
        exact ho₁ a a' (fun h' => h (by rw [h']))
      · exact cross a b'
      · exact cross' a' b
      · rw [Fin.append_right, Fin.append_right]
        exact ho₂ b b' (fun h' => h (by rw [h']))
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hs₁, hs₂]
      show z + (f - z) = f
      abel

end Categorification.Graded
