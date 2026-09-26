/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.GammaIntegral
import Categorification.Diagrams.KL3.SymmetryPsi
import Categorification.QuantumGroup.UDotSemilinear

/-!
# `γ` intertwines `ψ`, `ω` with `[ψ̃]`, `[ω̃]` (KL III Proposition 3.28)

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.6,
Proposition 3.28 (TeX label `prop_tilde_lifts`): "Homomorphism `γ` intertwines
(anti)automorphisms `ψ`, `ω`, `σ`, `τ` of `_𝒜 U̇` with (anti) automorphisms `[ψ̃]`, `[ω̃]`, `[σ̃]`,
and `[τ̃]` of `K₀(U̇)`, respectively […]. `[ψ̃]` denotes the induced action of `ψ̃` on the
Grothendieck group, etc. Proof: The proof follows from definitions and our construction of `γ`."

Of the four (anti)automorphisms, the algebraic `ψ` (`UDot.psi`, the `ℚ(q)`-antilinear bar
involution fixing every `E_w 1_λ`) and `ω` (`UDot.omega`, the Chevalley involution
`E_w 1_λ ↦ E_{w*} 1_{-λ}`) of `U̇` are available in the library; the squares for `σ` and `τ` are
in `Categorification.Diagrams.KL3.Prop328Sigma` and `Categorification.Diagrams.KL3.Prop328Tau`
(with `σ`, `τ` on `U̇` in `Categorification.QuantumGroup.UDotSigmaTau`).

## `[ψ̃]` on `K₀(U̇)`

The 2-functor `ψ̃ : U → U^co` (`psiU`, the identity on objects and 1-morphisms, contravariant on
2-morphisms, degree preserving) extends to `U̇(λ, ρ)` (KL III §3.4) as a *contravariant* additive
functor `psiDot : U̇(λ, ρ) ⥤ U̇(λ, ρ)ᵒᵖ`, `(x{t}, e) ↦ (x{-t}, ψ̃(e))` (KL III (3.44):
`E_s 1_λ {t} ↦ E_s 1_λ {-t}`; on formal direct sums the matrices are transposed). A contravariant
additive functor preserves isomorphism classes and direct sums, so it induces
`psiK0 : K₀(U̇(λ, ρ)) → K₀(U̇(λ, ρ))`, which is `ℤ[q, q⁻¹]`-*antilinear*
(`psiK0_smul : [ψ̃](p x) = p̄ [ψ̃](x)`, `q̄ = q⁻¹`) and fixes the classes `[E_w 1_λ]`
(`psiK0_eC`).

## Main results

* `gammaQ'_omega`: **`γ ∘ ω = [ω̃] ∘ γ` over `ℚ(q)`**: for every `ℚ(q)`-target `Φ` of
  `K₀(U̇ 1_{-λ})`, `γ_Φ(ω x) = γ_{Φ ∘ [ω̃]}(x)` for all `x ∈ U̇ 1_λ` (the square of KL III
  Proposition 3.28 for `ω`, after base change to `ℚ(q)`; for the universal target it is the
  commutative square itself).
* `gammaQ'_psi`: **`γ ∘ ψ = [ψ̃] ∘ γ` over `ℚ(q)`** (both sides `ℚ(q)`-antilinear): for every
  `Φ`, `Φ(γ̄(x)) = γ_Φ(ψ x)`, where `γ̄ = γ_{Φ ∘ [ψ̃]}` takes values in `V` with the
  bar-twisted `ℚ(q)`-action (`BarV`).
* Integrally, on the generators `E_d 1_λ` of `_𝒜 U̇` (`dpC`, `Categorification.Diagrams.KL3.GammaIntegral`):
  `omegaK0_dpC : [a]! · [ω̃][E_d 1_λ] = [a]! · [E_{ω d} 1_{-λ}]` and
  `psiK0_dpC : [a]! · [ψ̃][E_d 1_λ] = [a]! · [E_d 1_λ]` exactly in `K₀(U̇)`, where
  `[a]! = dpFac d = ∏_r [a_r]_{i_r}!` is a non-zero-divisor of `ℤ[q, q⁻¹]` (`dpFac_mem`); so the
  squares commute on generators up to `ℤ[q, q⁻¹]`-torsion, and exactly if `K₀(U̇)` is torsion free
  (`omegaK0_dpC_of_torsionFree`, `psiK0_dpC_of_torsionFree`). Since `ψ(E_d 1_λ) = E_d 1_λ` and
  `ω(E_d 1_λ) = E_{ω d} 1_{-λ}` (with `ω d` flipping all signs; `omega_dpW`), and `[ψ̃]`, `[ω̃]` are
  `ℤ[q, q⁻¹]`-antilinear resp. linear, this is the integral content of Proposition 3.28 for `ψ`
  and `ω` on `_𝒜 U̇` (KL III's "follows from definitions" uses the freeness of `K₀(U̇)`).
  For `ω` the torsion caveat is removed in `Categorification.Diagrams.KL3.Prop328Omega`
  (`omegaK0_dpC_exact`, using that `ω̃` is a strict 2-functor with `ω̃² = 1`).

## Generic tools

`matContra`, `karContra`: a contravariant additive functor `𝒞 ⥤ 𝒟ᵒᵖ` extended to formal direct
sums (transposing matrices) and to Karoubi envelopes; `contra_biprod`: a contravariant additive
functor sends binary biproducts to binary biproducts.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits Opposite

/-! ## Contravariant additive functors on matrices and Karoubi envelopes -/

section Contra

variable {𝒞 : Type*} {𝒟 : Type*} [Category 𝒞] [Category 𝒟] [Preadditive 𝒞] [Preadditive 𝒟]

/-- A contravariant additive functor extended to formal direct sums:
`⊕_i X_i ↦ ⊕_i F(X_i)`, with transposed matrices. -/
def matContra (F : 𝒞 ⥤ 𝒟ᵒᵖ) [F.Additive] : Mat_ 𝒞 ⥤ (Mat_ 𝒟)ᵒᵖ where
  obj M := op ({ ι := M.ι, X := fun i => (F.obj (M.X i)).unop } : Mat_ 𝒟)
  map {M N} φ := Quiver.Hom.op (show ({ ι := N.ι, X := fun i => (F.obj (N.X i)).unop } : Mat_ 𝒟) ⟶
      { ι := M.ι, X := fun i => (F.obj (M.X i)).unop } from fun j i => (F.map (φ i j)).unop)
  map_id M := by
    apply Quiver.Hom.unop_inj
    ext j i
    simp only [unop_id, Quiver.Hom.unop_op]
    by_cases h : i = j
    · subst h
      rw [Mat_.id_apply_self M i, F.map_id, unop_id]
      exact (Mat_.id_apply_self _ i).symm
    · rw [Mat_.id_apply_of_ne M i j h, F.map_zero, unop_zero]
      exact (Mat_.id_apply_of_ne _ j i (Ne.symm h)).symm
  map_comp {M N K} φ ψ := by
    apply Quiver.Hom.unop_inj
    ext k i
    simp only [unop_comp, Quiver.Hom.unop_op, Mat_.comp_apply]
    rw [F.map_sum, unop_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [F.map_comp, unop_comp]

instance matContra_additive (F : 𝒞 ⥤ 𝒟ᵒᵖ) [F.Additive] : (matContra F).Additive where
  map_add {M N φ ψ} := by
    apply Quiver.Hom.unop_inj
    ext j i
    show (F.map ((φ + ψ) i j)).unop = (F.map (φ i j)).unop + (F.map (ψ i j)).unop
    rw [Mat_.add_apply, F.map_add, unop_add]

/-- A contravariant functor extended to Karoubi envelopes: `(X, p) ↦ (F X, F p)`. -/
def karContra (G : 𝒞 ⥤ 𝒟ᵒᵖ) : Karoubi 𝒞 ⥤ (Karoubi 𝒟)ᵒᵖ where
  obj P := op ⟨(G.obj P.X).unop, (G.map P.p).unop, by rw [← unop_comp, ← G.map_comp, P.idem]⟩
  map {P Q} f := Quiver.Hom.op ⟨(G.map f.f).unop, by
    nth_rewrite 1 [f.comm]
    simp only [G.map_comp, unop_comp, Category.assoc]⟩
  map_id P := Quiver.Hom.unop_inj (Karoubi.hom_ext _ _ rfl)
  map_comp {P Q R} f g := Quiver.Hom.unop_inj (Karoubi.hom_ext _ _ (by
    show (G.map (f.f ≫ g.f)).unop = (G.map g.f).unop ≫ (G.map f.f).unop
    rw [G.map_comp, unop_comp]))

instance karContra_additive (G : 𝒞 ⥤ 𝒟ᵒᵖ) [G.Additive] : (karContra G).Additive where
  map_add {P Q f g} := Quiver.Hom.unop_inj (Karoubi.hom_ext _ _ (by
    show (G.map (f.f + g.f)).unop = (G.map f.f).unop + (G.map g.f).unop
    rw [G.map_add, unop_add]))

/-- **A contravariant additive functor preserves binary biproducts**:
`F(A ⊕ B) ≅ F(A) ⊕ F(B)`. -/
theorem contra_biprod [HasBinaryBiproducts 𝒞] [HasBinaryBiproducts 𝒟] (F : 𝒞 ⥤ 𝒟ᵒᵖ)
    [F.Additive] (A B : 𝒞) :
    Nonempty ((F.obj (A ⊞ B)).unop ≅ (F.obj A).unop ⊞ (F.obj B).unop) := by
  let b : BinaryBicone (F.obj A).unop (F.obj B).unop :=
    { pt := (F.obj (A ⊞ B)).unop
      fst := (F.map biprod.inl).unop
      snd := (F.map biprod.inr).unop
      inl := (F.map biprod.fst).unop
      inr := (F.map biprod.snd).unop
      inl_fst := by rw [← unop_comp, ← F.map_comp, biprod.inl_fst, F.map_id, unop_id]
      inl_snd := by rw [← unop_comp, ← F.map_comp, biprod.inr_fst, F.map_zero, unop_zero]
      inr_fst := by rw [← unop_comp, ← F.map_comp, biprod.inl_snd, F.map_zero, unop_zero]
      inr_snd := by rw [← unop_comp, ← F.map_comp, biprod.inr_snd, F.map_id, unop_id] }
  refine ⟨biprod.uniqueUpToIso _ _ (isBinaryBilimitOfTotal b ?_)⟩
  show (F.map biprod.inl).unop ≫ (F.map biprod.fst).unop +
    (F.map biprod.inr).unop ≫ (F.map biprod.snd).unop = 𝟙 _
  rw [← unop_comp, ← unop_comp, ← F.map_comp, ← F.map_comp, ← unop_add, ← F.map_add,
    biprod.total, F.map_id, unop_id]

end Contra

end Categorification

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents StringDiagrams QuantumGroup
  UDot Presentation Categorification.GradedBicat LaurentPolynomial Opposite

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## Bar invariance of quantum factorials -/

section Bar

omit [AddCommGroup X] [AddCommGroup Y] in
theorem invert_qfac (d : ℤ) (m : ℕ) : invert (qfac d m) = qfac d m := by
  rw [qfac, map_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  rw [map_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [invert_T]
  congr 1
  rw [show ((n + 1 - 1 - r : ℕ) : ℤ) = (n : ℤ) - r by omega]
  ring

omit [AddCommGroup X] [AddCommGroup Y] in
theorem invert_dpFac (d : List (Bool × I × ℕ)) : invert (dpFac (C := C) d) = dpFac (C := C) d := by
  induction d with
  | nil => simp [dpFac]
  | cons e d ih => rw [dpFac_cons, map_mul, invert_qfac, ih]

omit [AddCommGroup X] [AddCommGroup Y] in
/-- `∏_r [a_r]_{i_r}!` is a non-zero-divisor of `ℤ[q, q⁻¹]`. -/
theorem dpFac_mem (d : List (Bool × I × ℕ)) :
    dpFac (C := C) d ∈ nonZeroDivisors (LaurentPolynomial ℤ) := by
  refine mem_nonZeroDivisors_of_ne_zero ?_
  intro h
  have := lpToQ_dpFac_ne_zero (C := C) d
  rw [h, map_zero] at this
  exact this rfl

end Bar

/-! ## `ω`: the Chevalley involution -/

section Omega

/-- The dpss `ω d`: all signs flipped. -/
def flipd (d : List (Bool × I × ℕ)) : List (Bool × I × ℕ) := d.map fun e => (!e.1, e.2.1, e.2.2)

omit [AddCommGroup X] [AddCommGroup Y] in
theorem dpWord_flipd (d : List (Bool × I × ℕ)) :
    dpWord (flipd d) = (dpWord d).map Letter.dual := by
  induction d with
  | nil => rfl
  | cons e d ih =>
    simp only [flipd, List.map_cons] at ih ⊢
    rw [dpWord_cons, dpWord_cons, ih, List.map_append, dpLetters, dpLetters, List.map_replicate]
    rfl

omit [AddCommGroup X] [AddCommGroup Y] in
theorem dpFac_flipd (d : List (Bool × I × ℕ)) : dpFac (C := C) (flipd d) = dpFac (C := C) d := by
  simp [dpFac, flipd, Function.comp_def]

omit [AddCommGroup X] [AddCommGroup Y] in
/-- `ω(E_d) = E_{ω d}` in the free algebra. -/
theorem omegaF_dpW (d : List (Bool × I × ℕ)) :
    omegaF (dpW C vQ d : UDot.Free (RatFunc ℚ) I) = dpW C vQ (flipd d) := by
  induction d with
  | nil => simp [dpW, flipd]
  | cons e d ih =>
    have hd : ∀ e' d', dpW C vQ (e' :: d') = dpE C vQ e' * dpW C vQ d' := fun e' d' => by
      simp [dpW, List.map_cons, List.prod_cons]
    have hf : flipd (e :: d) = (!e.1, e.2.1, e.2.2) :: flipd d := rfl
    rw [hd, map_mul, ih, hf, hd, dpE, dpE, map_smul, omegaF_ew, List.map_replicate]
    rfl

/-- `ω(E_d 1_λ) = E_{ω d} 1_{-λ}` in `U̇`. -/
theorem omega_dpW (lam : X) (d : List (Bool × I × ℕ)) :
    omega RD vQ lam (UDot.mk RD vQ lam (dpW C vQ d)) =
      UDot.mk RD vQ (-lam) (dpW C vQ (flipd d)) := by
  change UDot.mk RD vQ (-lam) (omegaF _) = _
  rw [omegaF_dpW]

variable [DecidableEq I]

/-- **KL III Proposition 3.28 for `ω`, integrally on generators, up to torsion**:
`[a]! · [ω̃][E_d 1_λ] = [a]! · [E_{ω d} 1_{-λ}]` in `K₀(U̇)`, `[a]! = ∏_r [a_r]_{i_r}!`. -/
theorem omegaK0_dpC (d : List (Bool × I × ℕ)) (lam ρ : X) (h : wt RD lam (dpWord d) = ρ)
    (h' : wt RD (-lam) (dpWord (flipd d)) = -ρ) :
    dpFac (C := C) d • omegaK0 (RD := RD) (k := k) (lam := ρ) (μ := lam) rfl rfl
        (dpC RD k d lam ρ h) =
      dpFac (C := C) d • dpC RD k (flipd d) (-lam) (-ρ) h' := by
  have h'' : wt RD (-lam) ((dpWord d).map Letter.dual) = -ρ := by
    rw [Omega.wt_map_dual, h]
  rw [← map_smul, ← eC_dpWord, omegaK0_eC _ _ _ _ h'', ← dpFac_flipd, ← eC_dpWord]
  exact eC_congr (dpWord_flipd d).symm _ _

/-- `ω`-square on generators, exactly, if `K₀(U̇(-λ, -ρ))` is torsion free. -/
theorem omegaK0_dpC_of_torsionFree (d : List (Bool × I × ℕ)) (lam ρ : X)
    (h : wt RD lam (dpWord d) = ρ) (h' : wt RD (-lam) (dpWord (flipd d)) = -ρ)
    (htf : ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ), ∀ x : K0Kar RD k (-ρ) (-lam),
      p • x = 0 → x = 0) :
    omegaK0 (RD := RD) (k := k) (lam := ρ) (μ := lam) rfl rfl (dpC RD k d lam ρ h) =
      dpC RD k (flipd d) (-lam) (-ρ) h' :=
  sub_eq_zero.1 (htf _ (dpFac_mem d) _ (by rw [smul_sub, omegaK0_dpC, sub_self]))

variable {lam : X} {V : Type*} [AddCommGroup V] [Module (RatFunc ℚ) V]

/-- The pull-back of a `ℚ(q)`-target of `K₀(U̇ 1_{-λ})` along `[ω̃] : K₀(U̇(λ, ρ)) →
K₀(U̇(-λ, -ρ))`. -/
def QTarget.omegaPull (Φ : QTarget RD k (-lam) V) : QTarget RD k lam V where
  φ ρ := (Φ.φ (-ρ)).comp (omegaK0 (RD := RD) (k := k) (lam := ρ) (μ := lam) rfl rfl).toAddMonoidHom
  map_T ρ n x := by
    have := (omegaK0 (RD := RD) (k := k) (lam := ρ) (μ := lam) (lam' := -ρ) (μ' := -lam) rfl
      rfl).map_smul (T n : LaurentPolynomial ℤ) x
    show Φ.φ (-ρ) (omegaK0 rfl rfl ((T n : LaurentPolynomial ℤ) • x)) = _
    rw [this, Φ.map_T]
    rfl

theorem QTarget.omegaPull_φ (Φ : QTarget RD k (-lam) V) (ρ : X) (y : K0Kar RD k ρ lam) :
    Φ.omegaPull.φ ρ y = Φ.φ (-ρ) (omegaK0 (RD := RD) (k := k) (lam := ρ) (μ := lam) rfl rfl y) :=
  rfl

omit [DecidableEq I] in
theorem U1_linExt {W : Type*} [AddCommGroup W] [Module (RatFunc ℚ) W]
    {F G : U1 RD vQ lam →ₗ[RatFunc ℚ] W}
    (h : ∀ t, F (UDot.mk RD vQ lam (ew t)) = G (UDot.mk RD vQ lam (ew t))) : F = G :=
  Submodule.linearMap_qext _ (Free.lhom_ext fun w => h w)

/-- **KL III Proposition 3.28 for `ω`, over `ℚ(q)`**: `γ(ω x) = [ω̃] γ(x)` for `x ∈ U̇ 1_λ`,
i.e. `γ_Φ ∘ ω = γ_{Φ ∘ [ω̃]}` for every `ℚ(q)`-target `Φ` of `K₀(U̇ 1_{-λ})`. -/
theorem gammaQ'_omega (Φ : QTarget RD k (-lam) V) (x : U1 RD vQ lam) :
    gammaQ' Φ (omega RD vQ lam x) = gammaQ' Φ.omegaPull x := by
  have key : (gammaQ' Φ).comp (omega RD vQ lam) = gammaQ' Φ.omegaPull := by
    refine U1_linExt fun t => ?_
    have h'' : wt RD (-lam) (t.map Letter.dual) = -wt RD lam t := Omega.wt_map_dual lam t
    rw [LinearMap.comp_apply, omega_mk_ew, gammaQ'_mk_ew, gammaQ'_mk_ew, QTarget.omegaPull_φ,
      omegaK0_eC rfl rfl t rfl h'']
    exact phi_eC Φ (w := t.map flipL) (w' := t.map Letter.dual)
      (List.map_congr_left fun _ _ => rfl) h''
  exact LinearMap.congr_fun key x

end Omega

/-! ## `ψ̃` on `U̇` and on `K₀(U̇)` -/

section PsiDot

variable (ρ lam : X)

/-- `ψ̃` on shifted 1-morphisms: `x{t} ↦ x{-t}`, contravariant on 2-morphisms (KL III (3.44)). -/
def psiGr : GrObj (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam) ⥤
    (GrObj (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam))ᵒᵖ where
  obj A := op ⟨A.x, -A.t⟩
  map {A B} f := Quiver.Hom.op (show (⟨B.x, -B.t⟩ : GrObj (pres RD k) (deg RD) _ _) ⟶ ⟨A.x, -A.t⟩
    from ⟨((psiU RD k).map f.1).unop, mem_homDeg_of_eq (psiU_homDeg f.2) (by ring)⟩)
  map_id A := Quiver.Hom.unop_inj (GrObj.hom_ext (by
    show ((psiU RD k).map (𝟙 _)).unop = 𝟙 _
    rw [CategoryTheory.Functor.map_id, unop_id]))
  map_comp {A B D} f g := Quiver.Hom.unop_inj (GrObj.hom_ext (by
    show ((psiU RD k).map (f.1 ≫ g.1)).unop = ((psiU RD k).map g.1).unop ≫ ((psiU RD k).map f.1).unop
    rw [CategoryTheory.Functor.map_comp, unop_comp]))

instance psiGr_additive : (psiGr (RD := RD) (k := k) ρ lam).Additive where
  map_add {A B f g} := Quiver.Hom.unop_inj (GrObj.hom_ext (by
    show ((psiU RD k).map (f.1 + g.1)).unop = ((psiU RD k).map f.1).unop + ((psiU RD k).map g.1).unop
    rw [CategoryTheory.Functor.map_add, unop_add]))

/-- **`ψ̃` on `U̇(λ, ρ)`** (KL III §3.4): the contravariant additive functor
`(x{t}, e) ↦ (x{-t}, ψ̃(e))`, `U̇(λ, ρ) ⥤ U̇(λ, ρ)ᵒᵖ`. -/
abbrev psiDot : UKar RD k ρ lam ⥤ (UKar RD k ρ lam)ᵒᵖ :=
  karContra (matContra (psiGr (RD := RD) (k := k) ρ lam))

variable {ρ lam}

/-- `ψ̃(A{n}) ≅ ψ̃(A){-n}`. -/
def psiDotShift (n : ℤ) (A : UKar RD k ρ lam) :
    ((psiDot ρ lam).obj ((shDot (deg RD) n).obj A)).unop ≅
      (shDot (deg RD) (-n)).obj ((psiDot ρ lam).obj A).unop :=
  udIso _ _ (Equiv.refl _) (fun _ => rfl)
    (fun i => by
      show -(A.X.X i).t + -n = -((A.X.X i).t + n)
      ring)
    (fun i j => by
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl)

/-- `ψ̃(x{t}) ≅ x{-t}`, in particular `ψ̃(E_w 1_λ) ≅ E_w 1_λ`. -/
def psiDotObjOf (x : Bicat.Hom (wtObj RD k ρ) (wtObj RD k lam)) (t : ℤ) :
    ((psiDot ρ lam).obj (objOf (P := pres RD k) (deg := deg RD) x t)).unop ≅ objOf x (-t) :=
  udIso _ _ (Equiv.refl _) (fun _ => rfl) (fun _ => rfl)
    (fun i j => by
      cases i; cases j
      simp [Mat_.id_apply_self, karContra, matContra, psiGr])

/-- **`[ψ̃]` on `K₀(U̇(λ, ρ))`**: `[A] ↦ [ψ̃(A)]` (additive, `ℤ[q, q⁻¹]`-antilinear). -/
def psiK0 : K0Kar RD k ρ lam →+ K0Kar RD k ρ lam :=
  SplitK0.lift (fun A => K0U.cl ((psiDot ρ lam).obj A).unop)
    (fun _ _ e => SplitK0.of_iso ((psiDot ρ lam).mapIso e).unop.symm)
    (fun A B => (SplitK0.of_eq_of_nonempty (contra_biprod (psiDot ρ lam) A B)).trans
      (SplitK0.of_biprod _ _))

theorem psiK0_cl (A : UKar RD k ρ lam) :
    psiK0 (K0U.cl A) = K0U.cl ((psiDot ρ lam).obj A).unop :=
  SplitK0.lift_of _ _ _ _

/-- `[ψ̃](q^n x) = q^{-n} [ψ̃](x)`. -/
theorem psiK0_T (n : ℤ) (x : K0Kar RD k ρ lam) :
    psiK0 ((T n : LaurentPolynomial ℤ) • x) = (T (-n) : LaurentPolynomial ℤ) • psiK0 x := by
  rw [SplitK0.T_smul, SplitK0.T_smul]
  induction x using SplitK0.induction_on with
  | of A =>
    rw [SplitK0.shiftHom_of, psiK0_cl, psiK0_cl, SplitK0.shiftHom_of]
    exact SplitK0.of_iso (psiDotShift n A)
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | neg x hx => rw [map_neg, map_neg, hx, map_neg, map_neg]

/-- **`[ψ̃]` is `ℤ[q, q⁻¹]`-antilinear**: `[ψ̃](p x) = p̄ [ψ̃](x)`, `q̄ = q⁻¹`. -/
theorem psiK0_smul (p : LaurentPolynomial ℤ) (x : K0Kar RD k ρ lam) :
    psiK0 (p • x) = invert p • psiK0 x := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [add_smul, map_add, hp, hp', map_add, add_smul]
  | C_mul_T n a =>
    rw [mul_smul, SplitK0.C_smul, map_zsmul, psiK0_T, map_mul, invert_C, invert_T, mul_smul,
      SplitK0.C_smul]

/-- **`[ψ̃][E_w 1_λ] = [E_w 1_λ]`**. -/
theorem psiK0_eC (w : List (Letter I)) (h : wt RD lam w = ρ) :
    psiK0 (eC RD k ρ lam w h) = eC RD k ρ lam w h := by
  rw [eC, psiK0_cl]
  exact SplitK0.of_iso (psiDotObjOf _ 0)

variable [DecidableEq I]

/-- **KL III Proposition 3.28 for `ψ`, integrally on generators, up to torsion**:
`[a]! · [ψ̃][E_d 1_λ] = [a]! · [E_d 1_λ]` in `K₀(U̇)` (`ψ(E_d 1_λ) = E_d 1_λ`,
`[a]! = ∏_r [a_r]_{i_r}!`). -/
theorem psiK0_dpC (d : List (Bool × I × ℕ)) (h : wt RD lam (dpWord d) = ρ) :
    dpFac (C := C) d • psiK0 (dpC RD k d lam ρ h) = dpFac (C := C) d • dpC RD k d lam ρ h := by
  conv_lhs => rw [← invert_dpFac d]
  rw [← psiK0_smul, ← eC_dpWord, psiK0_eC, eC_dpWord]

/-- `ψ`-square on generators, exactly, if `K₀(U̇(λ, ρ))` is torsion free. -/
theorem psiK0_dpC_of_torsionFree (d : List (Bool × I × ℕ)) (h : wt RD lam (dpWord d) = ρ)
    (htf : ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ), ∀ x : K0Kar RD k ρ lam,
      p • x = 0 → x = 0) :
    psiK0 (dpC RD k d lam ρ h) = dpC RD k d lam ρ h :=
  sub_eq_zero.1 (htf _ (dpFac_mem d) _ (by rw [smul_sub, psiK0_dpC, sub_self]))

end PsiDot

/-! ## `γ ∘ ψ = [ψ̃] ∘ γ` over `ℚ(q)` -/

section PsiSquare

/-- `V` with the `ℚ(q)`-action twisted by the bar involution `q ↦ q⁻¹`. -/
def BarV (V : Type*) : Type _ := V

variable {V : Type*} [AddCommGroup V] [Module (RatFunc ℚ) V]

instance : AddCommGroup (BarV V) := inferInstanceAs (AddCommGroup V)

instance : Module (RatFunc ℚ) (BarV V) := Module.compHom V barQ

/-- The identity `V → BarV V`. -/
def toBarV : V ≃+ BarV V := AddEquiv.refl V

theorem toBarV_smul (c : RatFunc ℚ) (v : V) : toBarV (barQ c • v) = c • toBarV v := rfl

variable [DecidableEq I] {lam : X}

/-- The pull-back of a `ℚ(q)`-target `Φ` along `[ψ̃]`, a `ℚ(q)`-target with values in the
bar-twisted `V` (as `[ψ̃]` is antilinear). -/
def QTarget.psiPull (Φ : QTarget RD k lam V) : QTarget RD k lam (BarV V) where
  φ ρ := toBarV.toAddMonoidHom.comp ((Φ.φ ρ).comp psiK0)
  map_T ρ n x := by
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, psiK0_T, Φ.map_T]
    rw [← toBarV_smul, PreF.σ_zpow barQ_vQ]

/-- **KL III Proposition 3.28 for `ψ`, over `ℚ(q)`**: `γ(ψ x) = [ψ̃] γ(x)` for `x ∈ U̇ 1_λ`:
for every `ℚ(q)`-target `Φ`, `γ_{Φ ∘ [ψ̃]}(x) = γ_Φ(ψ x)` (both sides `ℚ(q)`-antilinear in `x`;
the left side is computed in the bar-twisted `V`). -/
theorem gammaQ'_psi (Φ : QTarget RD k lam V) (x : U1 RD vQ lam) :
    toBarV.symm (gammaQ' Φ.psiPull x) = gammaQ' Φ (psi RD vQ barQ barQ_vQ lam x) := by
  obtain ⟨z, rfl⟩ := mk_surjective RD vQ lam x
  induction z using Free.induction with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul_ew t r =>
    have e1 : toBarV.symm (gammaQ' Φ.psiPull (UDot.mk RD vQ lam (r • ew t))) =
        barQ r • toBarV.symm (gammaQ' Φ.psiPull (UDot.mk RD vQ lam (ew t))) := by
      rw [map_smul, map_smul]; rfl
    rw [e1, map_smul, LinearMap.map_smulₛₗ, psi_mk_ew, map_smul, gammaQ'_mk_ew, gammaQ'_mk_ew]
    change barQ r • Φ.φ _ (psiK0 _) = _
    rw [psiK0_eC]

end PsiSquare

end Categorification.KL3.Diagram
