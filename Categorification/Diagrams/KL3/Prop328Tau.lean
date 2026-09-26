/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Prop328Sigma
import Categorification.Diagrams.KL3.SymmetryTau

/-!
# `[τ̃]` on `K₀(U̇)`; KL III Proposition 3.28 for `τ`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.3.1
((3.40)–(3.42), label `eq_almost_biadjoints`), §3.3.2 (paragraph "Rotation by `180°` (taking right
adjoints)", eq. (3.46)), §3.4 (the extension of `τ̃` to `U̇`) and §3.6, Proposition 3.28
(TeX label `prop_tilde_lifts`) for `τ`.

KL III: "`τ̃ : U → U^coop`, `1_μ E_{s_1} ⋯ E_{s_m} 1_λ {t} ↦ 1_λ E_{-s_m} ⋯ E_{-s_1} 1_μ {-t + t'}`,
`ζ ↦ ζ*`, where the degree shift `t'` for the right adjoint […], determined by (3.42), ensures that
`τ̃` is degree preserving."

## The degree shift `t'`

By (3.42) the right adjoint of `E_{+i} 1_λ {t}` is `E_{-i} 1_{λ+i_X} {-c_{+i,λ} - t}`, and right
adjoints of composites are composites of right adjoints. Hence `t'(E_s 1_λ) = rexp λ s`, the
exponent of `q` in the algebraic `τ(E_s 1_λ) = q^{rexp λ s} E_{s*} 1_{λ + s_X}`
(`UDot.rexp`, `UDot.tauUD_E1`; e.g. `rexp λ (+i) = -c_{+i,λ}`). In the library, the rotation
`ζ ↦ ζ*` (`mateL`, `rotU`; the mate for the nested cups and caps) of a 2-morphism
`E_s 1_μ ⟶ E_t 1_μ` of degree `d` has degree `d + deg(cups of s) + deg(caps of t)`
(`rotU_homDeg`), and here:

* `degLs_nCups`, `degLs_nCaps`: the nested cups of `s` have degree `rexp μ s`, the nested caps of
  `t` degree `-rexp μ t`;
* `rexp_of_SChain`: `rexp μ` is constant along diagrams (dots and crossings permute letters;
  cups and caps insert or remove `l l*`), so a non-zero 2-morphism `E_s 1_μ ⟶ E_t 1_μ` has
  `rexp μ s = rexp μ t` (`hom_eq_zero_of_rexp_ne`), and the rotation preserves degrees
  (`rotU_homDeg_same`). Consequently `x{t} ↦ x*{-t + rexp}` is degree preserving
  (`mateL_homDeg`).

## Main results

* `tauDot : U̇(ρ, λ) ⥤ U̇(λ, ρ)ᵒᵖ` (library order: left region to right region): KL III's `τ̃` on
  `U̇`, contravariant on 2-morphisms, `(x{t}, e) ↦ (x*{-t + t'(x)}, e*)`;
  `tauDotObjOf : τ̃(x{t}) ≅ x*{-t + t'(x)}` (for `x = E_w 1_λ`, `t'(x) = rexp λ w`);
* `tauK0 : K₀(U̇(ρ, λ)) → K₀(U̇(λ, ρ))`, additive and `ℤ[q, q⁻¹]`-*antilinear*
  (`tauK0_smul : [τ̃](p x) = p̄ [τ̃](x)`), with
  `tauK0_eC : [τ̃][E_w 1_λ] = q^{rexp λ w} [E_{w*} 1_{λ + w_X}]` — exactly the algebraic
  `τ(E_w 1_λ) = q^{rexp λ w} E_{w*} 1_{λ + w_X}`;
* `gammaUD_tau`: **KL III Proposition 3.28 for `τ` over `ℚ(q)`**: `γ ∘ τ = [τ̃] ∘ γ` on all of
  `U̇` (both sides antilinear; stated with global `ℚ(q)`-targets as for `σ`);
* `tauK0_dpC`: integrally on the generators `E_d 1_λ` of `_𝒜 U̇`, up to torsion:
  `[a]! · [τ̃][E_d 1_λ] = [a]! · q^{rexp} [E_{ρ̄ d} 1_{λ+|d|_X}]`, and exactly if `K₀(U̇)` is
  torsion free (`tauK0_dpC_of_torsionFree`);
* `tauK0_eC_mul`: `[τ̃]` reverses products of the classes `[E_w 1_λ]`.

The anti-multiplicativity of `[τ̃]` on all of `K₀(U̇)` (which needs the compatibility of mates
with horizontal composition in `U̇`) is not formalized.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents StringDiagrams QuantumGroup
  UDot Presentation Categorification.GradedBicat LaurentPolynomial Opposite

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## `rexp` along diagrams and the degrees of nested cups and caps -/

section Rexp

theorem rexp_pair_dual (ν : X) (l : Letter I) : rexp RD ν [l, l.dual] = 0 := by
  obtain ⟨b, i⟩ := l
  simp only [Letter.dual, rexp_cons, rexp_nil, RD.wX_cons, RD.wX_nil, add_zero, sgn_not,
    map_add, map_zsmul, smul_eq_mul, RD.pair_iY_iX_self]
  linear_combination (2 * di C i) * sgn_mul_self b

theorem rexp_dual_pair (ν : X) (l : Letter I) : rexp RD ν [l.dual, l] = 0 := by
  simpa using rexp_pair_dual (RD := RD) ν l.dual

theorem wX_pair_dual (l : Letter I) : RD.wX [l, l.dual] = 0 := by
  obtain ⟨b, i⟩ := l
  simp [RD.wX_cons, Letter.dual, neg_smul]

/-- `rexp` is unchanged by a layer: dots and crossings permute letters, cups and caps insert or
remove a pair `l l*` or `l* l`. -/
theorem rexp_layer (μ : X) (u v : List (Letter I)) (g : Shape I) :
    rexp RD μ (u ++ g.dom ++ v) = rexp RD μ (u ++ g.cod ++ v) := by
  simp only [rexp_append, RD.wX_append]
  cases g with
  | dot l => rfl
  | cross ε i j =>
    have hp : ([(ε, i), (ε, j)] : List (Letter I)).Perm [(ε, j), (ε, i)] := List.Perm.swap _ _ []
    simp only [Shape.dom, Shape.cod, rexp_perm RD _ hp, wX_perm RD hp]
  | cup l =>
    simp only [Shape.dom, Shape.cod, rexp_nil, RD.wX_nil, rexp_pair_dual, wX_pair_dual]
  | cap l =>
    have h0 : RD.wX [l.dual, l] = 0 := by simpa using wX_pair_dual (RD := RD) l.dual
    simp only [Shape.dom, Shape.cod, rexp_nil, RD.wX_nil, rexp_dual_pair, h0]

/-- **`rexp μ` is constant along diagrams.** -/
theorem rexp_of_SChain (μ : X) {s t : List (Letter I)} {ls : List (LayerData I)}
    (h : SChain s ls t) : rexp RD μ s = rexp RD μ t := by
  induction ls generalizing s with
  | nil => cases h; rfl
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    rw [rexp_layer, ih h]

/-- The nested caps of `t` (rightmost region `μ`) have degree `-rexp μ t`. -/
theorem degLs_nCaps (μ : X) (t : List (Letter I)) : degLs RD μ (nCaps t) = -rexp RD μ t := by
  induction t with
  | nil => rfl
  | cons l b ih =>
    obtain ⟨ε, i⟩ := l
    have e : degLs RD μ (nCaps ((ε, i) :: b)) = sdeg RD (wt RD μ b) (.cap (ε, i)) +
        degLs RD μ (nCaps b) := by simp [nCaps, degLs]
    rw [e, ih, rexp_cons, wt_eq_add_wX]
    simp only [sdeg]
    rw [add_comm (RD.wX b) μ]
    ring

/-- The nested cups of `s` (rightmost region `wt μ s`) have degree `rexp μ s`. -/
theorem degLs_nCups (μ : X) (s : List (Letter I)) :
    degLs RD (wt RD μ s) (nCups s) = rexp RD μ s := by
  induction s with
  | nil => rfl
  | cons l a ih =>
    obtain ⟨ε, i⟩ := l
    have e : degLs RD (wt RD μ ((ε, i) :: a)) (nCups ((ε, i) :: a)) =
        sdeg RD (wt RD μ ((ε, i) :: a)) (.cup (ε, i)) +
          degLs RD (wt RD (wt RD μ ((ε, i) :: a)) [Letter.dual (ε, i)]) (nCups a) := by
      simp only [nCups, degLs, List.map_cons, List.sum_cons, wt_nil]
      congr 1
      exact degLs_map_whL (RD := RD) _ _ _ _
    have e2 : wt RD (wt RD μ ((ε, i) :: a)) [Letter.dual (ε, i)] = wt RD μ a := by
      rw [wt_cons, wt_nil, wt_cons, ← add_assoc, sh_dual_add_sh, zero_add]
    rw [e, e2, ih, rexp_cons]
    simp only [sdeg, wt_cons, sh, wt_eq_add_wX, RD.wX_cons, map_add, map_zsmul, smul_eq_mul,
      RD.pair_iY_iX_self]
    linear_combination (-(2 * di C i)) * sgn_mul_self ε

variable (k) in
/-- **A 2-morphism `E_s 1_μ ⟶ E_t 1_μ` with `rexp μ s ≠ rexp μ t` is zero** (there are no
diagrams between these objects). -/
theorem hom_eq_zero_of_rexp_ne (μ : X) {s t : List (Letter I)} (h : rexp RD μ s ≠ rexp RD μ t)
    (f : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) : f = 0 := by
  obtain ⟨g, rfl⟩ := (pres RD k).lin_surjective f
  have he : IsEmpty (ob RD μ s ⟶ ob RD μ t) := ⟨fun D => by
    obtain ⟨ls, hls, -⟩ := exists_mkD RD μ D
    exact h (rexp_of_SChain μ hls)⟩
  rw [show g = 0 from Finsupp.ext (α := ob RD μ s ⟶ ob RD μ t) fun d => (IsEmpty.false d).elim,
    Presentation.lin_zero]

/-- **The rotation `ζ ↦ ζ*` preserves degrees.** -/
theorem rotU_homDeg_same (μ ν : X) {s t : List (Letter I)} (hs : wt RD μ s = ν)
    (ht : wt RD μ t = ν) {f : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)} {d : ℤ}
    (hf : f ∈ (pres RD k).homDeg (deg RD) (ob RD μ s) (ob RD μ t) d) :
    rotU RD k μ ν s t hs ht f ∈ (pres RD k).homDeg (deg RD) (ob RD ν (rd t)) (ob RD ν (rd s)) d := by
  by_cases h : rexp RD μ s = rexp RD μ t
  · have := rotU_homDeg μ ν hs ht hf
    subst hs
    rw [degLs_nCups, degLs_nCaps, h] at this
    simpa using this
  · rw [hom_eq_zero_of_rexp_ne k μ h f, map_zero]
    exact Submodule.zero_mem _

end Rexp

/-! ## The degree shift of `τ̃` on 1-morphisms -/

section Shift

/-- The signed sequence of a 1-morphism of `U`. -/
def lw {a b : U RD k} (x : a ⟶ b) : List (Letter I) := x.obj.word.map Col.l

theorem obj_eq_ob {ρ lam : X} (x : (wtObj RD k ρ : U RD k) ⟶ wtObj RD k lam) :
    x.obj = ob RD lam (lw x) := by
  have h := wf_eq_ob x.obj x.wf
  have he : Sig.eR (RD := RD) x.obj.start x.obj.word = lam := x.endR_eq
  rw [he] at h
  exact h

theorem wt_lw {ρ lam : X} (x : (wtObj RD k ρ : U RD k) ⟶ wtObj RD k lam) :
    wt RD lam (lw x) = ρ := by
  have := congrArg Obj.start (obj_eq_ob x)
  rw [ob_start] at this
  rw [← this]
  exact x.start_eq

/-- Every 1-morphism `λ → ρ` (library: from `ρ` to `λ`) of `U` is some `E_s 1_λ`. -/
theorem hom_eq_obH {ρ lam : X} (x : (wtObj RD k ρ : U RD k) ⟶ wtObj RD k lam) :
    x = obH RD k lam ρ (lw x) (wt_lw x) :=
  Bicat.Hom.ext (obj_eq_ob x)

theorem lw_obH (μ ν : X) (t : List (Letter I)) (h : wt RD μ t = ν) :
    lw (obH RD k μ ν t h) = t :=
  map_l_wd RD μ t

/-- **KL III's degree shift `t'(x)`** for the right adjoint of `x = E_s 1_λ`: `rexp λ s`. -/
def tsh {ρ lam : X} (x : (wtObj RD k ρ : U RD k) ⟶ wtObj RD k lam) : ℤ := rexp RD lam (lw x)

/-- The dual (right adjoint) `x*` of a 1-morphism of `U`. -/
abbrev dualH {a b : U RD k} (x : a ⟶ b) : b ⟶ a :=
  (pres RD k).dualHom (inv RD).toColourDuality.pivotal x

theorem mateL_obH_eq (μ ν : X) (s t : List (Letter I)) (hs : wt RD μ s = ν) (ht : wt RD μ t = ν)
    (f : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :
    mateL RD k (obH RD k μ ν s hs) (obH RD k μ ν t ht) f =
      eqToHom (objEq RD k (dual_obH RD k μ ν t ht)) ≫ rotU RD k μ ν s t hs ht f ≫
        eqToHom (objEq RD k (dual_obH RD k μ ν s hs).symm) := by
  rw [rotU_apply]
  simp

/-- **`τ̃` is degree preserving with the shifts `x{t} ↦ x*{-t + t'(x)}`**: the rotation of a
2-morphism `x ⟶ x'` of degree `d` has degree `d + t'(x') - t'(x)`. -/
theorem mateL_homDeg {ρ lam : X} {x x' : (wtObj RD k ρ : U RD k) ⟶ wtObj RD k lam} {d : ℤ}
    {f : (pres RD k).obj x.obj ⟶ (pres RD k).obj x'.obj}
    (hf : f ∈ (pres RD k).homDeg (deg RD) x.obj x'.obj d) :
    mateL RD k x x' f ∈ (pres RD k).homDeg (deg RD) (dualH x').obj (dualH x).obj
      (d + tsh x' - tsh x) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s hs, x = obH RD k lam ρ s hs := ⟨_, _, hom_eq_obH x⟩
  obtain ⟨t, ht, rfl⟩ : ∃ t ht, x' = obH RD k lam ρ t ht := ⟨_, _, hom_eq_obH x'⟩
  simp only [tsh, lw_obH]
  by_cases h : rexp RD lam s = rexp RD lam t
  · rw [h, add_sub_cancel_right, mateL_obH_eq]
    have h1 := comp_mem_homDeg
      (eqToHom_mem_homDeg (P := pres RD k) (deg := deg RD)
        (congrArg Bicat.Hom.obj (dual_obH RD k lam ρ t ht)))
      (comp_mem_homDeg (rotU_homDeg_same lam ρ hs ht hf)
        (eqToHom_mem_homDeg (P := pres RD k) (deg := deg RD)
          (congrArg Bicat.Hom.obj (dual_obH RD k lam ρ s hs)).symm))
    simpa using h1
  · rw [hom_eq_zero_of_rexp_ne k lam h f, map_zero]
    exact Submodule.zero_mem _

end Shift

/-! ## `τ̃` on `U̇` -/

section Dot

variable (ρ lam : X)

/-- `τ̃` on shifted 1-morphisms: `x{t} ↦ x*{-t + t'(x)}`, contravariant on 2-morphisms
(`ζ ↦ ζ*`, KL III (3.46)). -/
def tauGr : GrObj (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam) ⥤
    (GrObj (pres RD k) (deg RD) (wtObj RD k lam) (wtObj RD k ρ))ᵒᵖ where
  obj A := op ⟨dualH A.x, -A.t + tsh A.x⟩
  map {A B} f := Quiver.Hom.op (show (⟨dualH B.x, -B.t + tsh B.x⟩ :
      GrObj (pres RD k) (deg RD) (wtObj RD k lam) (wtObj RD k ρ)) ⟶ ⟨dualH A.x, -A.t + tsh A.x⟩
    from ⟨mateL RD k A.x B.x f.1, mem_homDeg_of_eq (mateL_homDeg f.2) (by ring)⟩)
  map_id A := Quiver.Hom.unop_inj (GrObj.hom_ext (by
    show mateL RD k A.x A.x (𝟙 _) = 𝟙 _
    exact mateL_id RD k A.x))
  map_comp {A B D} f g := Quiver.Hom.unop_inj (GrObj.hom_ext (by
    show mateL RD k A.x D.x (f.1 ≫ g.1) = mateL RD k B.x D.x g.1 ≫ mateL RD k A.x B.x f.1
    exact mateL_comp RD k A.x B.x D.x f.1 g.1))

instance tauGr_additive : (tauGr (RD := RD) (k := k) ρ lam).Additive where
  map_add {A B f g} := Quiver.Hom.unop_inj (GrObj.hom_ext (by
    show mateL RD k A.x B.x (f.1 + g.1) = mateL RD k A.x B.x f.1 + mateL RD k A.x B.x g.1
    exact map_add _ _ _))

/-- **`τ̃` on `U̇(ρ, λ)`** (KL III §3.4): the contravariant additive functor
`(x{t}, e) ↦ (x*{-t + t'(x)}, e*)`, `U̇(ρ, λ) ⥤ U̇(λ, ρ)ᵒᵖ`. -/
abbrev tauDot : UKar RD k ρ lam ⥤ (UKar RD k lam ρ)ᵒᵖ :=
  karContra (matContra (tauGr (RD := RD) (k := k) ρ lam))

variable {ρ lam}

/-- `τ̃(A{n}) ≅ τ̃(A){-n}`. -/
def tauDotShift (n : ℤ) (A : UKar RD k ρ lam) :
    ((tauDot ρ lam).obj ((shDot (deg RD) n).obj A)).unop ≅
      (shDot (deg RD) (-n)).obj ((tauDot ρ lam).obj A).unop :=
  udIso _ _ (Equiv.refl _) (fun _ => rfl)
    (fun i => by
      show -(A.X.X i).t + tsh (A.X.X i).x + -n = -((A.X.X i).t + n) + tsh (A.X.X i).x
      ring)
    (fun i j => by
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl)

/-- `τ̃(x{t}) ≅ x*{-t + t'(x)}`. -/
def tauDotObjOf (x : (wtObj RD k ρ : U RD k) ⟶ wtObj RD k lam) (t : ℤ) :
    ((tauDot ρ lam).obj (objOf (P := pres RD k) (deg := deg RD) x t)).unop ≅
      objOf (dualH x) (-t + tsh x) :=
  udIso _ _ (Equiv.refl _) (fun _ => rfl) (fun _ => rfl)
    (fun i j => by
      cases i; cases j
      simp [Mat_.id_apply_self, karContra, matContra, tauGr]
      exact (mateL_id RD k x).symm)

end Dot

/-! ## `[τ̃]` on `K₀(U̇)` -/

section K0

variable {ρ lam : X}

/-- **`[τ̃]` on `K₀(U̇(ρ, λ))`**: `[A] ↦ [τ̃(A)] ∈ K₀(U̇(λ, ρ))` (additive,
`ℤ[q, q⁻¹]`-antilinear). -/
def tauK0 : K0Kar RD k ρ lam →+ K0Kar RD k lam ρ :=
  SplitK0.lift (fun A => K0U.cl ((tauDot ρ lam).obj A).unop)
    (fun _ _ e => SplitK0.of_iso ((tauDot ρ lam).mapIso e).unop.symm)
    (fun A B => (SplitK0.of_eq_of_nonempty (contra_biprod (tauDot ρ lam) A B)).trans
      (SplitK0.of_biprod _ _))

theorem tauK0_cl (A : UKar RD k ρ lam) :
    tauK0 (K0U.cl A) = K0U.cl ((tauDot ρ lam).obj A).unop :=
  SplitK0.lift_of _ _ _ _

/-- `[τ̃](q^n x) = q^{-n} [τ̃](x)`. -/
theorem tauK0_T (n : ℤ) (x : K0Kar RD k ρ lam) :
    tauK0 ((T n : LaurentPolynomial ℤ) • x) = (T (-n) : LaurentPolynomial ℤ) • tauK0 x := by
  rw [SplitK0.T_smul, SplitK0.T_smul]
  induction x using SplitK0.induction_on with
  | of A =>
    rw [SplitK0.shiftHom_of, tauK0_cl, tauK0_cl, SplitK0.shiftHom_of]
    exact SplitK0.of_iso (tauDotShift n A)
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | neg x hx => rw [map_neg, map_neg, hx, map_neg, map_neg]

/-- **`[τ̃]` is `ℤ[q, q⁻¹]`-antilinear**: `[τ̃](p x) = p̄ [τ̃](x)`, `q̄ = q⁻¹`. -/
theorem tauK0_smul (p : LaurentPolynomial ℤ) (x : K0Kar RD k ρ lam) :
    tauK0 (p • x) = invert p • tauK0 x := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [add_smul, map_add, hp, hp', map_add, add_smul]
  | C_mul_T n a =>
    rw [mul_smul, SplitK0.C_smul, map_zsmul, tauK0_T, map_mul, invert_C, invert_T, mul_smul,
      SplitK0.C_smul]

/-- **`[τ̃][E_w 1_λ] = q^{rexp λ w} [E_{w*} 1_{λ + w_X}]`**, the categorical counterpart of
`τ(E_w 1_λ) = q^{rexp λ w} E_{w*} 1_{λ + w_X}` (`UDot.tauUD_E1`); e.g.
`[τ̃][E_{+i} 1_λ] = q_i^{-1-⟨i,λ⟩} [E_{-i} 1_{λ+i_X}]`. -/
theorem tauK0_eC (w : List (Letter I)) (h : wt RD lam w = ρ) :
    tauK0 (eC RD k ρ lam w h) =
      (T (rexp RD lam w) : LaurentPolynomial ℤ) • eC RD k lam ρ (rd w) (wt_rd_of RD lam ρ w h) := by
  rw [eC, tauK0_cl]
  refine (SplitK0.of_iso (tauDotObjOf (nfHom RD k ρ lam w h) 0)).trans ?_
  show K0U.cl (objOf (dualH (obH RD k lam ρ w h)) (-0 + tsh (obH RD k lam ρ w h))) = _
  rw [show dualH (obH RD k lam ρ w h) = obH RD k ρ lam (rd w) (wt_rd_of RD lam ρ w h) from
    dual_obH RD k lam ρ w h, tsh, lw_obH, neg_zero, zero_add, K0U.objOf_shift]
  rfl

/-- `[τ̃]` reverses products of the classes `[E_w 1_λ]`:
`[τ̃]([E_s 1_μ] [E_t 1_λ]) = [τ̃][E_t 1_λ] · [τ̃][E_s 1_μ]`. -/
theorem tauK0_eC_mul {μ : X} (s t : List (Letter I)) (hs : wt RD μ s = ρ) (ht : wt RD lam t = μ)
    (h : wt RD lam (s ++ t) = ρ) :
    tauK0 (K0U.mul (eC RD k ρ μ s hs) (eC RD k μ lam t ht)) =
      K0U.mul (tauK0 (eC RD k μ lam t ht)) (tauK0 (eC RD k ρ μ s hs)) := by
  have hμ : lam + RD.wX t = μ := by rw [← ht, wt_eq_add_wX, add_comm]
  have h2 : wt RD ρ (rd t ++ rd s) = lam := by rw [← rd_append]; exact wt_rd_of RD lam ρ _ h
  rw [eC_mul s t hs ht h, tauK0_eC, tauK0_eC, tauK0_eC, K0U.mul_smul_left, K0U.mul_smul_right,
    smul_smul, eC_mul (rd t) (rd s) _ _ h2, rexp_append, hμ, T_add]
  exact congrArg _ (eC_congr (rd_append s t) _ _)

end K0

/-! ## KL III Proposition 3.28 for `τ` over `ℚ(q)` -/

section Gamma

open scoped Classical

variable [DecidableEq I] {V : Type*} [AddCommGroup V] [Module (RatFunc ℚ) V]

/-- The pull-back of a global target along `[τ̃]`, with values in the bar-twisted `V` (as `[τ̃]`
is antilinear). -/
def GTarget.tauPull (Φ : GTarget RD k V) : GTarget RD k (BarV V) where
  φ ρ lam := toBarV.toAddMonoidHom.comp ((Φ.φ lam ρ).comp tauK0)
  map_T ρ lam n x := by
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, tauK0_T, Φ.map_T]
    rw [← toBarV_smul, PreF.σ_zpow barQ_vQ]

omit [DecidableEq I] in
theorem GTarget.tauPull_φ (Φ : GTarget RD k V) (ρ lam : X) (x : K0Kar RD k ρ lam) :
    toBarV.symm (Φ.tauPull.φ ρ lam x) = Φ.φ lam ρ (tauK0 x) := rfl

/-- **KL III Proposition 3.28 for `τ`, over `ℚ(q)`**: `γ(τ x) = [τ̃] γ(x)` for all `x ∈ U̇`, where
`τ = ψρ` is the antilinear anti-automorphism of `U̇` (`UDot.tauUD`): for every global
`ℚ(q)`-target `Φ`, `Φ(γ̄(x)) = γ_Φ(τ x)` with `γ̄ = γ_{Φ ∘ [τ̃]}` computed in the bar-twisted
`V`. -/
theorem gammaUD_tau (Φ : GTarget RD k V) (x : UD RD vQ) :
    toBarV.symm (gammaUD Φ.tauPull x) = gammaUD Φ (tauUD RD vQ barQ barQ_vQ x) := by
  induction x using E1_induction with
  | zero =>
    rw [map_zero, map_zero, show tauUD RD vQ barQ barQ_vQ 0 = 0 by simp [tauUD, Upsi], map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, tauUD_add, map_add]
  | smul_E1 r t lam =>
    have e1 : toBarV.symm (gammaUD Φ.tauPull (r • E1 RD vQ t lam)) =
        barQ r • toBarV.symm (gammaUD Φ.tauPull (E1 RD vQ t lam)) := by
      rw [map_smul]; rfl
    rw [e1, tauUD_smul, map_smul, tauUD_E1, map_smul, gammaUD_E1, gammaUD_E1, GTarget.tauPull_φ,
      tauK0_eC, Φ.map_T]
    congr 2
    exact Φ.phi_eC (by rw [wt_eq_add_wX, wX_ρW]; abel) (by rw [wt_eq_add_wX, add_comm]) rfl _ _

/-- **Proposition 3.28 for `τ` on the generators `E_d 1_λ` of `_𝒜 U̇`, over `ℚ(q)`**:
`γ(τ(E_d 1_λ)) = [τ̃][E_d 1_λ]`. -/
theorem gammaUD_tau_E1dp (Φ : GTarget RD k V) (d : List (Bool × I × ℕ)) (lam ρ : X)
    (h : wt RD lam (dpWord d) = ρ) :
    gammaUD Φ (tauUD RD vQ barQ barQ_vQ (E1dp RD vQ d lam)) =
      Φ.φ lam ρ (tauK0 (dpC RD k d lam ρ h)) := by
  rw [← gammaUD_tau, gammaUD_E1dp _ d lam ρ h]
  rfl

end Gamma

/-! ## KL III Proposition 3.28 for `τ`, integrally on generators (up to torsion) -/

section Dpss

variable [DecidableEq I]

omit [AddCommGroup X] [AddCommGroup Y] [DecidableEq I] in
theorem dpSeq_eq_dpWord (d : List (Bool × I × ℕ)) : dpSeq d = dpWord d := by
  induction d with
  | nil => rfl
  | cons e d ih =>
    simp only [dpSeq, List.map_cons, List.flatten_cons] at ih ⊢
    rw [ih]
    rfl

omit [AddCommGroup X] [AddCommGroup Y] [DecidableEq I] in
theorem dpWord_rhod (d : List (Bool × I × ℕ)) : dpWord (rhod d) = rd (dpWord d) := by
  rw [← dpSeq_eq_dpWord, ← dpSeq_eq_dpWord, dpSeq_rhod]
  rfl

omit [AddCommGroup X] [AddCommGroup Y] [DecidableEq I] in
theorem dpFac_rhod (d : List (Bool × I × ℕ)) : dpFac (C := C) (rhod d) = dpFac (C := C) d := by
  simp [dpFac, rhod, List.map_reverse, List.prod_reverse, Function.comp_def]

/-- **KL III Proposition 3.28 for `τ`, integrally on generators, up to torsion**:
`[a]! · [τ̃][E_d 1_λ] = [a]! · q^{rexp} [E_{ρ̄ d} 1_ρ]` in `K₀(U̇)` (`ρ = λ + |d|_X`,
`ρ̄ d` the reversed dpss with all signs flipped, `rexp = rexp λ (dpWord d)`); on the algebra
side `τ(E_d 1_λ) = q^{rexp} E_{ρ̄ d} 1_ρ` (`UDot.tauUD_E1dp`). -/
theorem tauK0_dpC (d : List (Bool × I × ℕ)) (lam ρ : X) (h : wt RD lam (dpWord d) = ρ)
    (h' : wt RD ρ (dpWord (rhod d)) = lam) :
    dpFac (C := C) d • tauK0 (dpC RD k d lam ρ h) =
      dpFac (C := C) d • ((T (rexp RD lam (dpWord d)) : LaurentPolynomial ℤ) •
        dpC RD k (rhod d) ρ lam h') := by
  conv_lhs => rw [← invert_dpFac d]
  rw [← tauK0_smul, ← eC_dpWord, tauK0_eC, smul_comm, ← dpFac_rhod, ← eC_dpWord]
  exact congrArg _ (eC_congr (dpWord_rhod d).symm _ _)

/-- `τ`-square on generators, exactly, if `K₀(U̇(λ, ρ))` is torsion free. -/
theorem tauK0_dpC_of_torsionFree (d : List (Bool × I × ℕ)) (lam ρ : X)
    (h : wt RD lam (dpWord d) = ρ) (h' : wt RD ρ (dpWord (rhod d)) = lam)
    (htf : ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ), ∀ x : K0Kar RD k lam ρ,
      p • x = 0 → x = 0) :
    tauK0 (dpC RD k d lam ρ h) =
      (T (rexp RD lam (dpWord d)) : LaurentPolynomial ℤ) • dpC RD k (rhod d) ρ lam h' :=
  sub_eq_zero.1 (htf _ (dpFac_mem d) _ (by rw [smul_sub, tauK0_dpC, sub_self]))

end Dpss

end Categorification.KL3.Diagram
