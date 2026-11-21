/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Finitely generated graded projective modules over a connected graded ring are free

Let `A` be a commutative algebra over a field `k` which is an integral domain, with an
augmentation `ε : A →ₐ[k] k`, and let `M` be an `A`-module with a `ℤ`-grading by `k`-subspaces
`ℳ d`. Call the grading *connected* (`IsConnectedGrading`) if, for a homogeneous `x ∈ ℳ e`, every
homogeneous component of `a • x` is an `A`-multiple of `x`, and the component in the degree of `x`
itself is `ε a • x`. This holds when `A` is a polynomial ring with positive weights, the
augmentation is the constant coefficient, and multiplication by a monomial of weight `w` raises
degrees by `w` (`isConnectedGrading_mvPolynomial`).

**Theorem** (`free_of_projective`). A finitely generated projective `A`-module with a connected
grading is free.

This is the graded form of Nakayama's lemma used in Webster, arXiv:1309.3796v2, proof of
Corollary 3.26, where freeness of a deformed cyclotomic quotient over a polynomial ring is
deduced from its grading. The argument: lift a basis of `M / 𝔪 M` (`𝔪 = ker ε`) to homogeneous
elements; they span `M` because the span `N` is a graded submodule with `M = N + 𝔪 M`, so Nakayama
gives `r ∈ 1 + 𝔪` with `r M ⊆ N`, and the component of `r • x` in the degree of a homogeneous
`x` is `x`. The kernel `K` of the resulting map from a free module is a direct summand with
`K = 𝔪 K`, so it is killed by some `r ∈ 1 + 𝔪`; as `A` is a domain and `r ≠ 0`, `K = 0`.
-/

namespace Categorification.Graded

open Submodule DirectSum

variable {k A M : Type*} [Field k] [CommRing A] [Algebra k A]
  [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  (ε : A →ₐ[k] k) (ℳ : ℤ → Submodule k M) [Decomposition ℳ]

/-- The component of degree `d`, as a `k`-linear map `M → M`. -/
noncomputable def gradedComponent (d : ℤ) : M →ₗ[k] M :=
  (ℳ d).subtype ∘ₗ DirectSum.component k ℤ (fun d => ℳ d) d ∘ₗ
    (decomposeLinearEquiv ℳ).toLinearMap

theorem gradedComponent_apply (d : ℤ) (x : M) :
    gradedComponent ℳ d x = (decompose ℳ x d : M) := rfl

/-- A grading of an `A`-module that is connected relative to the augmentation `ε`: components of
`a • x`, for homogeneous `x`, are multiples of `x`, and the component in the degree of `x` is
`ε a • x`. -/
structure IsConnectedGrading : Prop where
  component_smul_self : ∀ (a : A) (d : ℤ) (x : M), x ∈ ℳ d →
    gradedComponent ℳ d (a • x) = ε a • x
  component_smul : ∀ (a : A) (e d : ℤ) (x : M), x ∈ ℳ e →
    ∃ b : A, gradedComponent ℳ d (a • x) = b • x

variable {ε ℳ}

/-- Every element is the sum of its homogeneous components. -/
theorem exists_sum_homogeneous (x : M) :
    ∃ s : Finset ℤ, ∑ d ∈ s, gradedComponent ℳ d x = x := by
  classical
  refine ⟨(decompose ℳ x).support, ?_⟩
  simp only [gradedComponent_apply]
  exact sum_support_decompose ℳ x

omit [IsScalarTower k A M] in
/-- A span of homogeneous elements contains the homogeneous components of its elements. -/
theorem component_mem_span (h : IsConnectedGrading ε ℳ) {S : Set M}
    (hS : ∀ x ∈ S, ∃ e, x ∈ ℳ e) {y : M} (hy : y ∈ span A S) (d : ℤ) :
    gradedComponent ℳ d y ∈ span A S := by
  induction hy using Submodule.span_induction generalizing d with
  | mem x hx =>
    obtain ⟨e, he⟩ := hS x hx
    obtain ⟨b, hb⟩ := h.component_smul 1 e d x he
    rw [one_smul] at hb
    rw [hb]
    exact smul_mem _ _ (subset_span hx)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem (hx d) (hy d)
  | smul a y _ hy =>
    obtain ⟨s, hs⟩ := exists_sum_homogeneous (ℳ := ℳ) y
    rw [← hs, Finset.smul_sum, map_sum]
    refine sum_mem fun e _ => ?_
    obtain ⟨b, hb⟩ := h.component_smul a e d _ (Submodule.coe_mem (decompose ℳ y e))
    rw [show gradedComponent ℳ e y = (decompose ℳ y e : M) from rfl, hb]
    exact smul_mem _ _ (hy e)

section Free

local notation "𝔪" => RingHom.ker ε

variable (ε) in
theorem sub_algebraMap_mem_ker (a : A) : a - algebraMap k A (ε a) ∈ 𝔪 := by
  simp [RingHom.mem_ker]

variable (ε) in
/-- On `M / 𝔪 M`, every `a ∈ A` acts as the scalar `ε a`. -/
theorem smul_quotient_eq (a : A) (v : M ⧸ (𝔪 • ⊤ : Submodule A M)) : a • v = ε a • v := by
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← sub_eq_zero,
      ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero, ← algebraMap_smul A (ε a) x,
      ← sub_smul]
    exact smul_mem_smul (sub_algebraMap_mem_ker ε a) mem_top

variable (ε) in
theorem finite_quotient [Module.Finite A M] :
    Module.Finite k (M ⧸ (𝔪 • ⊤ : Submodule A M)) := by
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := M ⧸ (𝔪 • ⊤ : Submodule A M))
  refine ⟨⟨S, eq_top_iff.2 fun v hvt => ?_⟩⟩
  clear hvt
  have hv : v ∈ span A (S : Set _) := hS ▸ mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact subset_span hx
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a y _ hy => rw [smul_quotient_eq ε a y]; exact smul_mem _ _ hy

/-- **Graded Nakayama: freeness.** A finitely generated projective module over a commutative
domain `A`, with a connected grading relative to an augmentation `ε : A →ₐ[k] k`, is free. -/
theorem free_of_projective [IsDomain A] (h : IsConnectedGrading ε ℳ) [Module.Finite A M]
    [Module.Projective A M] : Module.Free A M := by
  classical
  set p : Submodule A M := 𝔪 • ⊤
  set V := M ⧸ p
  have : Module.Finite k V := finite_quotient ε
  let mk : M →ₗ[A] V := p.mkQ
  have hmk : ∀ (c : k) (x : M), mk (algebraMap k A c • x) = c • mk x := fun c x => by
    rw [map_smul, algebraMap_smul]
  let H : Set M := {x | ∃ e, x ∈ ℳ e}
  have hspan : span k (mk '' H) = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    obtain ⟨x, rfl⟩ := p.mkQ_surjective v
    obtain ⟨s, hs⟩ := exists_sum_homogeneous (ℳ := ℳ) x
    rw [← hs, map_sum]
    exact sum_mem fun d _ => subset_span ⟨_, ⟨d, Submodule.coe_mem _⟩, rfl⟩
  obtain ⟨b, hbH, hbspan, hbli⟩ := exists_linearIndependent k (mk '' H)
  have : Finite b := hbli.finite_of_isNoetherian
  have : Fintype b := Fintype.ofFinite b
  choose g hgH hg using fun v : b => hbH v.2
  have hgmk : ∀ v : b, mk (g v) = v := hg
  let f : (b →₀ A) →ₗ[A] M := Finsupp.linearCombination A g
  have hrange : LinearMap.range f = span A (Set.range g) := Finsupp.range_linearCombination A
  -- `M = span (range g) + 𝔪 M`
  have hsup : ∀ x : M, ∃ c : b → k, x - ∑ v, algebraMap k A (c v) • g v ∈ p := by
    intro x
    have hx : mk x ∈ span k (Set.range ((↑) : b → V)) := by
      rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hbspan, hspan]; exact mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
    refine ⟨c, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
    change mk x - mk (∑ v, algebraMap k A (c v) • g v) = 0
    rw [map_sum]
    simp only [hmk, hgmk]
    rw [hc, sub_self]
  -- surjectivity
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, hrange]
    set N := span A (Set.range g)
    have hhom : ∀ x ∈ Set.range g, ∃ e, x ∈ ℳ e := by
      rintro _ ⟨v, rfl⟩; exact hgH v
    obtain ⟨r, hr1, hr⟩ := exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪
      (⊤ : Submodule A (M ⧸ N)) (Module.Finite.fg_top) (by
        intro q _
        obtain ⟨x, rfl⟩ := N.mkQ_surjective q
        obtain ⟨c, hc⟩ := hsup x
        have hxe : N.mkQ x = N.mkQ (x - ∑ v, algebraMap k A (c v) • g v) := by
          have h0 : N.mkQ (∑ v, algebraMap k A (c v) • g v) = 0 :=
            (Submodule.Quotient.mk_eq_zero N).2
              (sum_mem fun v _ => smul_mem _ _ (subset_span ⟨v, rfl⟩))
          rw [map_sub, h0, sub_zero]
        rw [hxe]
        have hle : p.map N.mkQ ≤ 𝔪 • ⊤ := by
          rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
        exact hle (Submodule.mem_map_of_mem hc))
    have hεr : ε r = 1 := by
      have := hr1; rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this; exact this
    have hrN : ∀ x : M, r • x ∈ N := fun x => by
      have := hr (N.mkQ x) mem_top
      rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨s, hs⟩ := exists_sum_homogeneous (ℳ := ℳ) x
    rw [← hs]
    refine sum_mem fun d _ => ?_
    have hc := h.component_smul_self r d _ (Submodule.coe_mem (decompose ℳ x d))
    rw [hεr, one_smul] at hc
    rw [← gradedComponent_apply] at hc
    rw [← hc]
    exact component_mem_span h hhom (hrN _) d
  -- injectivity
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hsurj
  have hfs : ∀ x, f (s x) = x := fun x => LinearMap.congr_fun hs x
  have hcoord : ∀ z : b →₀ A, f z ∈ p → ∀ v, z v ∈ 𝔪 := by
    intro z hz
    have hzsum : f z = ∑ v, z v • g v := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
    have h1 : (∑ v, algebraMap k A (ε (z v)) • g v) ∈ p := by
      have h2 : (∑ v, (z v - algebraMap k A (ε (z v))) • g v) ∈ p :=
        sum_mem fun v _ => smul_mem_smul (sub_algebraMap_mem_ker ε (z v)) mem_top
      have h3 := sub_mem (hzsum ▸ hz) h2
      simpa [sub_smul, Finset.sum_sub_distrib] using h3
    have h4 : ∑ v, ε (z v) • (v : V) = 0 := by
      have := (Submodule.Quotient.mk_eq_zero p).2 h1
      change mk _ = 0 at this
      rw [map_sum] at this
      simpa only [hmk, hgmk] using this
    have h5 := (Fintype.linearIndependent_iff.1 hbli) _ h4
    intro v
    have := sub_algebraMap_mem_ker ε (z v)
    rwa [h5 v, map_zero, sub_zero] at this
  set K := LinearMap.ker f
  let π : (b →₀ A) →ₗ[A] (b →₀ A) := LinearMap.id - s ∘ₗ f
  have hπK : ∀ z, π z ∈ K := fun z => by
    simp [π, K, LinearMap.mem_ker, hfs]
  have hπ : ∀ z ∈ K, π z = z := fun z hz => by
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      (LinearMap.mem_ker.1 hz), map_zero, sub_zero]
  have hKfg : K.FG := by
    have : K = LinearMap.range π := le_antisymm
      (fun z hz => ⟨z, hπ z hz⟩) (by rintro _ ⟨z, rfl⟩; exact hπK z)
    rw [this, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map π
  have hKle : K ≤ 𝔪 • K := by
    intro z hz
    have hz0 : f z ∈ p := by rw [LinearMap.mem_ker.1 hz]; exact zero_mem _
    have hc := hcoord z hz0
    have hzs : z = ∑ v, z v • Finsupp.single v (1 : A) := by
      conv_lhs => rw [← Finsupp.sum_single z]
      rw [Finsupp.sum_fintype _ _ (by simp)]
      simp
    rw [← hπ z hz, hzs, map_sum]
    exact sum_mem fun v _ => by rw [map_smul]; exact smul_mem_smul (hc v) (hπK _)
  obtain ⟨r, hr1, hr⟩ := exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 K hKfg hKle
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_sub, RingHom.mem_ker, map_neg, map_one] at hr1
    exact one_ne_zero (neg_eq_zero.1 hr1)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    exact (smul_eq_zero.1 (hr z hz)).resolve_left hr0
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)

end Free

section MvPolynomial

open MvPolynomial

variable {σ : Type*} [Module (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]
  (w : σ → ℕ)

omit [Module A M] [IsScalarTower k A M] in
/-- The components of `a • x`, for `x` homogeneous of degree `e`, when multiplication by a
monomial of weight `n` raises degrees by `n`. -/
theorem gradedComponent_smul_eq
    (hmono : ∀ (s : σ →₀ ℕ) (d : ℤ) (x : M), x ∈ ℳ d →
      (monomial s (1 : k)) • x ∈ ℳ (d + (Finsupp.weight w s : ℤ)))
    (a : MvPolynomial σ k) {e : ℤ} {x : M} (hx : x ∈ ℳ e) (d : ℤ) :
    gradedComponent ℳ d (a • x) =
      (∑ s ∈ a.support, if e + (Finsupp.weight w s : ℤ) = d then monomial s (a.coeff s)
        else 0) • x := by
  classical
  conv_lhs => rw [a.as_sum]
  rw [Finset.sum_smul, Finset.sum_smul, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hm : monomial s (a.coeff s) = a.coeff s • monomial s (1 : k) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, smul_assoc, map_smul, gradedComponent_apply]
  split_ifs with hd
  · rw [decompose_of_mem_same ℳ (hd ▸ hmono s e x hx), smul_assoc]
  · rw [decompose_of_mem_ne ℳ (hmono s e x hx) hd, smul_zero, zero_smul]

omit [Module A M] [IsScalarTower k A M] in
/-- A grading of a module over a polynomial ring with positive weights, on which multiplication by
a monomial of weight `n` raises degrees by `n`, is connected relative to the constant
coefficient. -/
theorem isConnectedGrading_mvPolynomial (hw : ∀ i, 0 < w i)
    (hmono : ∀ (s : σ →₀ ℕ) (d : ℤ) (x : M), x ∈ ℳ d →
      (monomial s (1 : k)) • x ∈ ℳ (d + (Finsupp.weight w s : ℤ))) :
    IsConnectedGrading (MvPolynomial.aeval (0 : σ → k)) ℳ where
  component_smul_self a d x hx := by
    classical
    rw [gradedComponent_smul_eq w hmono a hx d, aeval_zero, Algebra.algebraMap_self,
      RingHom.id_apply, constantCoeff_eq]
    have : Finsupp.NonTorsionWeight ℕ w := Finsupp.nonTorsionWeight_of (R := ℕ) (hw := fun i => (hw i).ne')
    have hz : ∀ s : σ →₀ ℕ, (d + (Finsupp.weight w s : ℤ) = d ↔ s = 0) := fun s => by
      rw [add_eq_left, Nat.cast_eq_zero, Finsupp.weight_eq_zero_iff_eq_zero]
    simp only [hz, Finset.sum_ite_eq', mem_support_iff]
    split_ifs with h0
    · rw [← C_apply, ← algebraMap_eq, algebraMap_smul]
    · rw [not_not] at h0; rw [h0, zero_smul, zero_smul]
  component_smul a e d x hx := ⟨_, gradedComponent_smul_eq w hmono a hx d⟩

end MvPolynomial

end Categorification.Graded
