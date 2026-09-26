/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.FinDimHomUp
import Categorification.Diagrams.KL3.KrullSchmidtCat
import Categorification.Diagrams.KL3.GammaIntegral
import Categorification.Diagrams.KL3.Prop328

/-!
# Krull–Schmidt in `U̇(λ, μ)` and freeness of `K₀(U̇)`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.6
(TeX `\subsection{$K_0(\dot{\cal{U}})$ and homomorphism $\gamma$}`, label `subsec_KzeroU`):

> The space of homs between any two objects in `U̇(λ, μ)` is a finite-dimensional `k`-vector
> space. In particular, the Krull–Schmidt decomposition theorem holds […] Then `{[b]}_b` is a basis
> of `K₀(U̇(λ, μ))`, viewed as a free `ℤ[q, q⁻¹]`-module.

and §3.8.2 (Propositions 3.31, 3.34: freeness of `K₀` of graded (idempotented) algebras with
finite-dimensional weight spaces, bounded below). For simply-laced Cartan data, `I` finite and
`k` a field:

* `hasGdim_obj`: every graded Hom-space `HOM_U(x, y)` between 1-morphisms of `U` has
  finite-dimensional graded pieces, vanishing in low degrees (from `hasGdim_homD`, every
  1-morphism being a normal-form word `obj_eq_ob_endR`);
* `homFinite_UDot`: **the Hom-spaces of `U̇(λ, μ)` are finite-dimensional**;
* `hom_shDot_eq_zero`, `rigid_UDot`: `Hom(A, B{n}) = 0` for `n ≫ 0`, hence no indecomposable
  object of `U̇(λ, μ)` is isomorphic to a nonzero shift of itself;
* `indecBasisU`: **KL III §3.6: `K₀(U̇(λ, μ))` is a free `ℤ[q, q⁻¹]`-module with basis the
  classes of the indecomposable objects up to isomorphism and grading shift** (the generic
  Krull–Schmidt theorem `Categorification.KrullSchmidtCat`); `K0Kar_free`,
  `K0Kar_torsionFree`.

Consequently the torsion-freeness hypothesis `htf` of `Categorification.Diagrams.KL3.GammaIntegral`
and `Categorification.Diagrams.KL3.Prop328` is discharged:

* `gammaUA'`: **KL III Proposition 3.27, integral form**: `γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))`,
  `γ(E_d 1_λ) = [E_d 1_λ]` (`gammaUA'_dpW`), multiplicative (`gammaUA'_mul`);
* `dpC_relation'`: the relations of `_𝒜 U̇` among the generators `E_d 1_λ` hold exactly in
  `K₀(U̇)`;
* `psiK0_dpC'`, `omegaK0_dpC'`: the `ψ`- and `ω`-squares of KL III Proposition 3.28 commute on
  the generators `E_d 1_λ`, exactly.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents StringDiagrams QuantumGroup
  UDot Presentation GradedBicat KrullSchmidtCat

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k]

/-! ## Every 1-morphism is a normal-form word -/

/-- A well-formed word of strands ending in the region `μ` is `E_t 1_μ` for its sequence of
letters `t`. -/
theorem obj_eq_ob_endR (μ : X) (o : Obj (psig RD)) (hwf : o.WF) (h : o.endR = μ) :
    o = ob RD μ (o.word.map Col.l) := by
  obtain ⟨st, w⟩ := o
  induction w generalizing st with
  | nil =>
    change st = μ at h
    subst h; rfl
  | cons c w ih =>
    obtain ⟨h₁, h₂⟩ := hwf
    have e := ih c.r h₂ h
    simp only [ob, Obj.mk.injEq] at e ⊢
    obtain ⟨hr, hw⟩ := e
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, wt_cons, ← hr]; exact h₁.symm
    · rw [List.map_cons, wd_cons, ← hr, ← hw]; rfl

section Finite

variable [DecidableEq I] [Finite I]

/-- **Finite-dimensional graded Hom-spaces between arbitrary 1-morphisms of `U`**
(simply-laced, `I` finite, `k` a field). -/
theorem hasGdim_obj (hSL : SimplyLaced C) {ρ lam : X}
    (x y : Bicat.Hom (wtObj RD k ρ) (wtObj RD k lam)) :
    Graded.HasGdim ((pres RD k).homDeg (deg RD) x.obj y.obj) := by
  have hx : x.obj = ob RD lam (x.obj.word.map Col.l) := obj_eq_ob_endR lam x.obj x.wf x.endR_eq
  have hy : y.obj = ob RD lam (y.obj.word.map Col.l) := obj_eq_ob_endR lam y.obj y.wf y.endR_eq
  rw [hx, hy]
  exact hasGdim_homD hSL lam _ _

/-- The underlying matrix of a morphism of the Karoubi envelope, as a linear map. -/
def karHomL {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞] (A B : Karoubi 𝒞) :
    (A ⟶ B) →ₗ[k] (A.X ⟶ B.X) where
  toFun f := f.f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem karHomL_injective {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
    (A B : Karoubi 𝒞) : Function.Injective (karHomL (k := k) A B) :=
  fun _ _ h => Karoubi.hom_ext _ _ h

/-- **The Hom-spaces of `U̇(λ, μ)` are finite-dimensional** (KL III §3.6). -/
theorem homFinite_UDot (hSL : SimplyLaced C) (ρ lam : X) :
    HomFinite k (UDotHom (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam)) := by
  constructor
  intro A B
  haveI hG : ∀ Xg Yg : GrObj (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam),
      FiniteDimensional k (Xg ⟶ Yg) :=
    fun Xg Yg => (hasGdim_obj (k := k) hSL Xg.x Yg.x).finiteDimensional _
  haveI : ∀ M N : Mat_ (GrObj (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam)),
      FiniteDimensional k (M ⟶ N) :=
    fun M N => by
      change FiniteDimensional k (∀ i j, M.X i ⟶ N.X j)
      infer_instance
  exact FiniteDimensional.of_injective (karHomL (k := k) A B) (karHomL_injective A B)

/-- **`Hom(A, B{n}) = 0` for `n ≫ 0`** in `U̇(λ, μ)` (the Hom-spaces of `U` are bounded
below). -/
theorem hom_shDot_eq_zero (hSL : SimplyLaced C) {ρ lam : X}
    (A B : UDotHom (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam)) :
    ∃ N : ℤ, ∀ n ≥ N, ∀ f : A ⟶ (shDot (deg RD) n).obj B, f = 0 := by
  have hb : ∀ i j, ∃ Nij : ℤ, ∀ d < Nij,
      (pres RD k).homDeg (deg RD) (A.X.X i).x.obj (B.X.X j).x.obj d = ⊥ := by
    intro i j
    obtain ⟨B₀, hB₀⟩ := (hasGdim_obj (k := k) hSL (A.X.X i).x (B.X.X j).x).bddBelow
    refine ⟨B₀, fun d hd => ?_⟩
    by_contra hne
    have := hB₀ hne
    omega
  choose Nf hNf using hb
  obtain ⟨M, hM⟩ := (Set.finite_range fun ij : A.X.ι × B.X.ι =>
    (A.X.X ij.1).t - (B.X.X ij.2).t - Nf ij.1 ij.2 + 1).bddAbove
  refine ⟨M, fun n hn f => Karoubi.hom_ext _ _ ?_⟩
  ext i j
  have hmem := (f.f i j).2
  have hlt : (A.X.X i).t - ((B.X.X j).t + n) < Nf i j := by
    have := hM ⟨(i, j), rfl⟩
    simp only at this
    omega
  have h0 : (f.f i j).1 = 0 := by
    have e := hNf i j _ hlt
    change (f.f i j).1 ∈ (pres RD k).homDeg (deg RD) (A.X.X i).x.obj (B.X.X j).x.obj
      ((A.X.X i).t - ((B.X.X j).t + n)) at hmem
    rw [e] at hmem
    exact (Submodule.mem_bot k).1 hmem
  rw [h0]
  rfl

open SplitK0 SplitK0.K0Shift in
/-- **No indecomposable object of `U̇(λ, μ)` is isomorphic to a nonzero shift of itself** (KL III
§3.8.2, proof of Proposition 3.31: "Boundedness […] ensures that an indecomposable projective is
not isomorphic to itself with a shifted grading"). -/
theorem rigid_UDot (hSL : SimplyLaced C) {ρ lam : X} :
    ∀ (n : ℤ) (A : UDotHom (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam)), IsIndec A →
      Nonempty (SplitK0.K0Shift.sh n A ≅ A) →
      n = 0 := by
  haveI := homFinite_UDot (RD := RD) (k := k) hSL ρ lam
  intro n A hA hn
  by_contra hne
  obtain ⟨p, hp, hpA⟩ : ∃ p : ℤ, 0 < p ∧ Nonempty (SplitK0.K0Shift.sh p A ≅ A) := by
    rcases lt_or_gt_of_ne hne with h | h
    · obtain ⟨e⟩ := hn
      obtain ⟨e₁⟩ := sh_iso (-n) e
      obtain ⟨e₂⟩ := nonempty_sh_neg_sh n A
      exact ⟨-n, by omega, ⟨e₁.symm ≪≫ e₂⟩⟩
    · exact ⟨n, h, hn⟩
  have hk : ∀ j : ℕ, Nonempty (SplitK0.K0Shift.sh ((j : ℤ) * p) A ≅ A) := by
    intro j
    induction j with
    | zero => simpa using sh_zero A
    | succ j ih =>
      obtain ⟨e⟩ := ih
      obtain ⟨φ⟩ := hpA
      obtain ⟨e₁⟩ := sh_add ((j : ℤ) * p) p A
      obtain ⟨e₂⟩ := sh_iso p e
      have : ((j + 1 : ℕ) : ℤ) * p = (j : ℤ) * p + p := by push_cast; ring
      rw [this]
      exact ⟨e₁ ≪≫ e₂ ≪≫ φ⟩
  obtain ⟨N, hN⟩ := hom_shDot_eq_zero (k := k) hSL A A
  obtain ⟨ψ⟩ := hk N.toNat
  have hge : (N.toNat : ℤ) * p ≥ N := by
    have h1 : (N.toNat : ℤ) ≥ N := Int.self_le_toNat N
    have h2 : (0 : ℤ) ≤ N.toNat := by positivity
    nlinarith
  have h0 : ψ.inv = 0 := hN _ hge ψ.inv
  apply hA.1
  rw [IsZero.iff_id_eq_zero, ← ψ.inv_hom_id, h0, Limits.zero_comp]

/-! ## Krull–Schmidt in `U̇(λ, μ)` -/

/-- **Indecomposable 1-morphisms of `U̇(λ, ρ)` have local (degree-zero) endomorphism rings**
(KL III §3.6; simply-laced, `I` finite, `k` a field). -/
theorem isLocalRing_end_UDot (hSL : SimplyLaced C) {ρ lam : X} {Z : UKar RD k ρ lam}
    (hZ : IsIndec Z) : IsLocalRing (End Z) :=
  haveI := homFinite_UDot (RD := RD) (k := k) hSL ρ lam
  hZ.isLocalRing k

/-- **Existence of Krull–Schmidt decompositions in `U̇(λ, ρ)`**: the class of every object is a
sum of classes of indecomposable objects. -/
theorem cl_mem_closure_indec (hSL : SimplyLaced C) {ρ lam : X} (A : UKar RD k ρ lam) :
    K0U.cl A ∈ AddSubmonoid.closure {x | ∃ Z : UKar RD k ρ lam, IsIndec Z ∧ x = K0U.cl Z} :=
  haveI := homFinite_UDot (RD := RD) (k := k) hSL ρ lam
  of_mem_closure_indec k A

open Classical in
/-- **Uniqueness of Krull–Schmidt decompositions in `U̇(λ, ρ)`** (KL III §3.6: "Any object of
`U̇(λ, μ)` has a unique presentation, up to permutation of factors and isomorphisms, as a direct
sum of indecomposables"): two lists of indecomposables with the same class in `K₀` (e.g. with
isomorphic direct sums) contain the same number of objects isomorphic to any given `Z`. -/
theorem countP_iso_eq_UDot (hSL : SimplyLaced C) {ρ lam : X} {Z : UKar RD k ρ lam}
    (hZ : IsIndec Z) {L L' : List (UKar RD k ρ lam)} (hL : ∀ Y ∈ L, IsIndec Y)
    (hL' : ∀ Y ∈ L', IsIndec Y) (h : (L.map K0U.cl).sum = (L'.map K0U.cl).sum) :
    (L.countP fun Y => Nonempty (Y ≅ Z)) = L'.countP fun Y => Nonempty (Y ≅ Z) :=
  haveI := homFinite_UDot (RD := RD) (k := k) hSL ρ lam
  countP_iso_eq_of_sum_eq k hZ hL hL' h

/-! ## `K₀(U̇(λ, μ))` is free -/

/-- **KL III §3.6: `K₀(U̇(λ, μ))` is a free `ℤ[q, q⁻¹]`-module with basis the classes of the
indecomposable objects up to isomorphism and grading shift** (simply-laced, `I` finite, `k` a
field). -/
def indecBasisU (hSL : SimplyLaced C) (ρ lam : X) :
    Basis (IndecClass (UDotHom (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam)))
      (LaurentPolynomial ℤ) (K0Kar RD k ρ lam) :=
  haveI := homFinite_UDot (RD := RD) (k := k) hSL ρ lam
  indecBasis k (rigid_UDot hSL)

theorem indecBasisU_apply (hSL : SimplyLaced C) (ρ lam : X)
    (b : IndecClass (UDotHom (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam))) :
    indecBasisU hSL ρ lam b = K0U.cl b.rep := by
  haveI := homFinite_UDot (RD := RD) (k := k) hSL ρ lam
  exact indecBasis_apply k (rigid_UDot hSL) b

/-- **`K₀(U̇(λ, ρ))` is a free `ℤ[q, q⁻¹]`-module** (KL III §3.6). -/
theorem K0Kar_free (hSL : SimplyLaced C) (ρ lam : X) :
    Module.Free (LaurentPolynomial ℤ) (K0Kar RD k ρ lam) :=
  Module.Free.of_basis (indecBasisU hSL ρ lam)

/-- **`K₀(U̇(λ, ρ))` has no `ℤ[q, q⁻¹]`-torsion** (the hypothesis `htf` of
`Categorification.Diagrams.KL3.GammaIntegral`). -/
theorem K0Kar_torsionFree (hSL : SimplyLaced C) (ρ lam : X) :
    ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ), ∀ x : K0Kar RD k ρ lam, p • x = 0 → x = 0 := by
  haveI := homFinite_UDot (RD := RD) (k := k) hSL ρ lam
  exact fun p hp x h => eq_zero_of_smul_eq_zero k (rigid_UDot hSL) hp h

end Finite

/-! ## Discharging the torsion-freeness hypotheses -/

section Discharge

attribute [local instance] KLR.KLGamma.vAlgebra

variable [DecidableEq I] [Finite I] (hSL : SimplyLaced C)

/-- **KL III Proposition 3.27, integral form** (simply-laced, `I` finite, `k` a field; no
torsion-freeness hypothesis): the `ℤ[q, q⁻¹]`-linear map `γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))`
(on the span of the generators `E_d 1_λ`), `γ(E_d 1_λ) = [E_d 1_λ]`. -/
def gammaUA' (hSL : SimplyLaced C) (lam ρ : X) :
    LinearMap.range (dpComb (RD := RD) lam ρ) →ₗ[LaurentPolynomial ℤ] K0Kar RD k ρ lam :=
  gammaUA lam ρ (K0Kar_torsionFree hSL ρ lam)

/-- `γ(∑_d c_d E_d 1_λ) = ∑_d c_d [E_d 1_λ]`. -/
theorem gammaUA'_apply (lam ρ : X) (f : DpIdx (RD := RD) lam ρ →₀ LaurentPolynomial ℤ) :
    gammaUA' (k := k) hSL lam ρ ⟨dpComb lam ρ f, LinearMap.mem_range_self _ _⟩ =
      dpCComb lam ρ f :=
  gammaUA_apply lam ρ _ f

/-- `γ(E_d 1_λ) = [E_d 1_λ]`. -/
theorem gammaUA'_dpW (lam ρ : X) (d : DpIdx (RD := RD) lam ρ) :
    gammaUA' (k := k) hSL lam ρ ⟨dpComb lam ρ (Finsupp.single d 1), LinearMap.mem_range_self _ _⟩ =
      dpC RD k d.1 lam ρ d.2 :=
  gammaUA_dpW lam ρ _ d

/-- **`γ` is multiplicative** (KL III Proposition 3.27, integrally, unconditionally for
simply-laced data). -/
theorem gammaUA'_mul {lam μ ρ : X} (f : DpIdx (RD := RD) μ ρ →₀ LaurentPolynomial ℤ)
    (g : DpIdx (RD := RD) lam μ →₀ LaurentPolynomial ℤ) :
    gammaUA' (k := k) hSL lam ρ ⟨dpComb lam ρ (dpMul f g), LinearMap.mem_range_self _ _⟩ =
      K0U.mul (gammaUA' (k := k) hSL μ ρ ⟨dpComb μ ρ f, LinearMap.mem_range_self _ _⟩)
        (gammaUA' (k := k) hSL lam μ ⟨dpComb lam μ g, LinearMap.mem_range_self _ _⟩) :=
  (gammaUA_mul (K0Kar_torsionFree hSL ρ μ) (K0Kar_torsionFree hSL μ lam)
    (K0Kar_torsionFree hSL ρ lam) f g).2

include hSL

/-- **The relations of `1_ρ (_𝒜 U̇) 1_λ` among the generators `E_d 1_λ` hold exactly in
`K₀(U̇(λ, ρ))`** (simply-laced). -/
theorem dpC_relation' {lam ρ : X} {ι : Type*} (s : Finset ι) (c : ι → LaurentPolynomial ℤ)
    (d : ι → List (Bool × I × ℕ)) (hd : ∀ j, wt RD lam (dpWord (d j)) = ρ)
    (hrel : ∑ j ∈ s, lpToQ (c j) • UDot.mk RD vQ lam (dpW C vQ (d j)) = 0) :
    ∑ j ∈ s, c j • dpC RD k (d j) lam ρ (hd j) = 0 :=
  dpC_relation_of_torsionFree (K0Kar_torsionFree hSL ρ lam) s c d hd hrel

/-- **KL III Proposition 3.28 for `ψ`, exactly on the generators** (simply-laced):
`[ψ̃][E_d 1_λ] = [E_d 1_λ]`. -/
theorem psiK0_dpC' {lam ρ : X} (d : List (Bool × I × ℕ)) (h : wt RD lam (dpWord d) = ρ) :
    psiK0 (dpC RD k d lam ρ h) = dpC RD k d lam ρ h :=
  psiK0_dpC_of_torsionFree d h (K0Kar_torsionFree hSL ρ lam)

/-- **KL III Proposition 3.28 for `ω`, exactly on the generators** (simply-laced). -/
theorem omegaK0_dpC' (d : List (Bool × I × ℕ)) (lam ρ : X) (h : wt RD lam (dpWord d) = ρ)
    (h' : wt RD (-lam) (dpWord (flipd d)) = -ρ) :
    omegaK0 (RD := RD) (k := k) (lam := ρ) (μ := lam) rfl rfl (dpC RD k d lam ρ h) =
      dpC RD k (flipd d) (-lam) (-ρ) h' :=
  omegaK0_dpC_of_torsionFree d lam ρ h h' (K0Kar_torsionFree hSL (-ρ) (-lam))

end Discharge

end Categorification.KL3.Diagram
