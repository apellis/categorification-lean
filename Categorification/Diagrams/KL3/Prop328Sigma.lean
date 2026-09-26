/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Prop328Omega
import Categorification.Diagrams.KL3.Symmetries
import Categorification.QuantumGroup.UDotSigmaTau

/-!
# `[σ̃]` on `K₀(U̇)`; KL III Proposition 3.28 for `σ`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.3.2
(the symmetry `σ̃ : U → U^op`, "`1_μ E_{s_1} ⋯ E_{s_m} 1_λ {t} ↦ 1_{-λ} E_{s_m} ⋯ E_{s_1} 1_{-μ} {t}`
[…] The square of `σ̃` is the identity"), §3.4 (the remark after Definition 3.21: the 2-functors
`ω̃, σ̃, ψ̃, τ̃` extend to `U̇`) and §3.6, Proposition 3.28 (TeX label `prop_tilde_lifts`) for `σ`.

The 2-functor `σ̃` (`sigU`, `Categorification.Diagrams.KL3.SymmetrySigma`) reverses the order of
1-morphisms, sends `λ ↦ -λ`, is covariant on 2-morphisms and preserves degrees. Hence:

* `sigDot : U̇(ρ, λ) ⥤ U̇(-λ, -ρ)` (library order: from the left region to the right region),
  `(x{t}, e) ↦ (σ̃(x){t}, σ̃(e))`; `sigDot_nfObj`: `σ̃(E_w 1_λ {s}) = E_{w^rev} 1_{-(λ + w_X)} {s}`;
* `sigK0 : K₀(U̇(ρ, λ)) → K₀(U̇(-λ, -ρ))`, `ℤ[q, q⁻¹]`-linear, with
  `sigK0_eC : [σ̃][E_w 1_λ] = [E_{w^rev} 1_{-(λ + w_X)}]`;
* `sigU_hcomp`: **`σ̃` reverses horizontal composition**, `σ̃(f ∘ g) = σ̃(g) ∘ σ̃(f)`; hence
  `sigDotHcomp : σ̃(A B) ≅ σ̃(B) σ̃(A)` and `sigK0_mul : [σ̃](x y) = [σ̃](y) [σ̃](x)`: `[σ̃]` is an
  anti-homomorphism of the ring `K₀(U̇)`;
* `sigDotSigDot : σ̃(σ̃(A)) ≅ A` and `sigK0_sigK0 : [σ̃]² = 1`; `sigK0_one : [σ̃][1_λ] = [1_{-λ}]`.
  So `[σ̃]` is a `ℤ[q, q⁻¹]`-linear anti-involution of `K₀(U̇)`, the counterpart of `σ`.

## KL III Proposition 3.28 for `σ`

The anti-automorphism `σ` does not preserve the blocks `U̇ 1_λ`, so the comparison is stated on the
whole of `U̇` with *global* `ℚ(q)`-targets (`GTarget`: a `ℚ(q)`-vector space `V` with additive maps
`K₀(U̇(ρ, λ)) → V` for all `ρ, λ`, compatible with `q`; the universal one is
`⊕_{ρ, λ} K₀(U̇(ρ, λ)) ⊗_{ℤ[q,q⁻¹]} ℚ(q)`), and `gammaUD Φ : U̇ → V` is `γ` on all blocks.

* `gammaUD_sigma`: **`γ ∘ σ = [σ̃] ∘ γ` over `ℚ(q)`**: `γ_Φ(σ x) = γ_{Φ ∘ [σ̃]}(x)` for all `x ∈ U̇`.
* `sigK0_dpC`: integrally on the generators `E_d 1_λ` of `_𝒜 U̇`, up to torsion:
  `[a]! · [σ̃][E_d 1_λ] = [a]! · [E_{d^rev} 1_{-(λ + |d|_X)}]`, `[a]! = ∏_r [a_r]_{i_r}!`, and
  `sigK0_dpC_of_torsionFree`: exactly if `K₀(U̇)` is torsion free (as for `ψ`); on the algebra
  side `σ(E_d 1_λ) = E_{d^rev} 1_{-(λ + |d|_X)}` (`sigmaUD_E1dp`).

The exact identity `[σ̃][E_{+i^{(a)}} 1_μ] = [E_{+i^{(a)}} 1_{-μ-a i_X}]` would need the
equivalence of the nilHecke idempotent `e_{i,a} = x^δ ψ_{w_0}` with its reflection
`± x^{δ^rev} ψ_{w_0}`; this is not formalized.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents StringDiagrams QuantumGroup
  UDot Presentation Categorification.GradedBicat LaurentPolynomial

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k] [DecidableEq I]

/-! ## `σ̃` on the Hom categories of `U̇` -/

section Dot

/-- `σ̃` on 1-morphisms of `U`: a 1-morphism from `ρ` to `λ` (left to right region) goes to one
from `ρ' = -λ` to `λ' = -ρ`. -/
def sigHom {ρ lam ρ' lam' : X} (hρ : -lam = ρ') (hl : -ρ = lam')
    (x : (wtObj RD k ρ : U RD k) ⟶ wtObj RD k lam) : (wtObj RD k ρ' : U RD k) ⟶ wtObj RD k lam' :=
  ⟨Sig.obj RD x.obj, by
      show -Sig.eR (RD := RD) x.obj.start x.obj.word = ρ'
      rw [← hρ]; exact congrArg (fun r : X => -r) x.endR_eq,
    (Sig.ok_word _ _ x.wf).1, by
      show (psig RD).endR (-Sig.eR (RD := RD) x.obj.start x.obj.word) (Sig.word RD x.obj.word) =
        lam'
      rw [(Sig.ok_word _ _ x.wf).2, ← hl]
      exact congrArg (fun r : X => -r) x.start_eq⟩

omit [DecidableEq I] in
@[simp] theorem sigHom_obj {ρ lam ρ' lam' : X} (hρ : -lam = ρ') (hl : -ρ = lam')
    (x : (wtObj RD k ρ : U RD k) ⟶ wtObj RD k lam) :
    (sigHom hρ hl x).obj = Sig.obj RD x.obj := rfl

omit [DecidableEq I] in
/-- `σ̃(E_w 1_λ) = E_{w^rev} 1_{-(λ + w_X)}`. -/
theorem sigHom_nfHom {ρ lam ρ' lam' : X} (hρ : -lam = ρ') (hl : -ρ = lam')
    (w : List (Letter I)) (h : wt RD lam w = ρ) (h' : wt RD lam' w.reverse = ρ') :
    sigHom hρ hl (nfHom RD k ρ lam w h) = nfHom RD k ρ' lam' w.reverse h' :=
  Bicat.Hom.ext (Sig.trO lam lam' w (by rw [← hl, h]))

variable (ρ lam ρ' lam' : X) (hρ : -lam = ρ') (hl : -ρ = lam')

/-- `σ̃` on shifted 1-morphisms: `x{t} ↦ σ̃(x){t}` (degrees are preserved, `sigU_homDeg`). -/
@[simps]
def sigGr : GrObj (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam) ⥤
    GrObj (pres RD k) (deg RD) (wtObj RD k ρ') (wtObj RD k lam') where
  obj A := ⟨sigHom hρ hl A.x, A.t⟩
  map f := ⟨(sigU RD k).map f.1, sigU_homDeg f.2⟩
  map_id _ := Subtype.ext ((sigU RD k).map_id _)
  map_comp _ _ := Subtype.ext ((sigU RD k).map_comp _ _)

instance : (sigGr (RD := RD) (k := k) ρ lam ρ' lam' hρ hl).Additive where
  map_add {_ _ f g} := by
    apply Subtype.ext
    show (sigU RD k).map (f.1 + g.1) = (sigU RD k).map f.1 + (sigU RD k).map g.1
    exact Functor.map_add _

instance : (sigGr (RD := RD) (k := k) ρ lam ρ' lam' hρ hl).Linear k where
  map_smul {_ _} f r := by
    apply Subtype.ext
    show (sigU RD k).map (r • f.1) = r • (sigU RD k).map f.1
    exact Functor.map_smul _ _ _

/-- **`σ̃` on `U̇`** (KL III §3.4): the functor `U̇(ρ, λ) ⥤ U̇(-λ, -ρ)` induced by `σ̃` on formal
direct sums and on the Karoubi envelope, `(x{t}, e) ↦ (σ̃(x){t}, σ̃(e))`. -/
abbrev sigDot : UKar RD k ρ lam ⥤ UKar RD k ρ' lam' :=
  mapKaroubi (sigGr (RD := RD) (k := k) ρ lam ρ' lam' hρ hl).mapMat_

variable {ρ lam ρ' lam' hρ hl}

/-- `σ̃(x{t}) = σ̃(x){t}`. -/
theorem sigDot_objOf (x : (wtObj RD k ρ : U RD k) ⟶ wtObj RD k lam) (t : ℤ) :
    (sigDot ρ lam ρ' lam' hρ hl).obj (objOf x t) = objOf (sigHom hρ hl x) t := by
  fapply Karoubi.ext
  · rfl
  · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    exact (sigGr ρ lam ρ' lam' hρ hl).mapMat_.map_id _

/-- `σ̃(E_w 1_λ {s}) = E_{w^rev} 1_{-(λ + w_X)} {s}`. -/
theorem sigDot_nfObj (w : List (Letter I)) (h : wt RD lam w = ρ)
    (h' : wt RD lam' w.reverse = ρ') (s : ℤ) :
    (sigDot ρ lam ρ' lam' hρ hl).obj (nfObj RD k ρ lam w h s) =
      nfObj RD k ρ' lam' w.reverse h' s := by
  rw [nfObj, sigDot_objOf, sigHom_nfHom hρ hl w h h']

/-- `σ̃` commutes with the grading shifts: `σ̃(A{n}) ≅ σ̃(A){n}`. -/
def sigDotShift (n : ℤ) (A : UKar RD k ρ lam) :
    (sigDot ρ lam ρ' lam' hρ hl).obj ((shDot (deg RD) n).obj A) ≅
      (shDot (deg RD) n).obj ((sigDot ρ lam ρ' lam' hρ hl).obj A) :=
  udIso _ _ (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) fun i j => by simp

end Dot

/-! ## `σ̃` reverses horizontal composition -/

section Hcomp

omit [DecidableEq I] in
/-- `σ̃(a ⊗ b) = σ̃(b) ⊗ σ̃(a)`. -/
theorem sig_obj_tensor {a b : Obj (psig RD)} (h : a.endR = b.start) :
    Sig.obj RD (a.tensor b) = (Sig.obj RD b).tensor (Sig.obj RD a) := by
  refine Obj.ext ?_ ?_
  · show -Sig.eR (RD := RD) a.start (a.word ++ b.word) = -Sig.eR (RD := RD) b.start b.word
    simp only [Sig.eR, Signature.endR_append]
    rw [show (psig RD).endR a.start a.word = b.start from h]
  · simp [Obj.tensor, Sig.obj, Sig.word_append]

omit [DecidableEq I] in
theorem wRAt_congr_region {r r' : (psig RD).Region} {a a' : Obj (psig RD)} (e : r = r')
    (f : (pres RD k).obj a ⟶ (pres RD k).obj a') (b : Obj (psig RD)) (ha : a.start = r)
    (ha' : a'.start = r) :
    (pres RD k).wRAt r f b ha ha' = (pres RD k).wRAt r' f b (ha.trans e) (ha'.trans e) := by
  subst e; rfl

omit [DecidableEq I] in
theorem sig_whisk_congr {a b u u' : Obj (psig RD)} {v v' : List (psig RD).Colour}
    (f : (pres RD k).obj a ⟶ (pres RD k).obj b) (e : u = u') (e' : v = v') :
    (pres RD k).whisk f u v =
      eqToHom (by rw [e, e']) ≫ (pres RD k).whisk f u' v' ≫ eqToHom (by rw [e, e']) := by
  subst e e'; simp

/-- `σ̃(1_a ⊗ g) = σ̃(g) ⊗ 1_{σ̃ a}`. -/
theorem sigU_wL (a : Obj (psig RD)) {b b' : Obj (psig RD)}
    (g : (pres RD k).obj b ⟶ (pres RD k).obj b') (hb : b.WF) (hab : a.Composable b)
    (hs : b'.start = b.start) (he : b'.endR = b.endR) :
    (sigU RD k).map ((pres RD k).wL a g) =
      eqToHom (congrArg (pres RD k).obj (sig_obj_tensor hab.endR_eq)) ≫
        (pres RD k).wRAt (negR b.endR) ((sigU RD k).map g) (Sig.obj RD a) rfl
          (show negR b'.endR = negR b.endR by rw [he]) ≫
          eqToHom (congrArg (pres RD k).obj (sig_obj_tensor (hab.endR_eq.trans hs.symm))).symm := by
  have hw : b.WhiskerOK a [] := ⟨hab.left_wf, hab.endR_eq, trivial⟩
  simp only [Presentation.wL, Presentation.wRAt, Functor.map_comp, eqToHom_map]
  rw [sigU_whisk g hb hs he hw]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

/-- `σ̃(f ⊗ 1_b) = 1_{σ̃ b} ⊗ σ̃(f)`. -/
theorem sigU_wRAt {r : X} {a a' : Obj (psig RD)} (f : (pres RD k).obj a ⟶ (pres RD k).obj a')
    (b : Obj (psig RD)) (ha : a.start = r) (ha' : a'.start = r) (haw : a.WF)
    (hab : a.Composable b) (he : a'.endR = a.endR) :
    (sigU RD k).map ((pres RD k).wRAt r f b ha ha') =
      eqToHom (congrArg (pres RD k).obj (sig_obj_tensor hab.endR_eq)) ≫
        (pres RD k).wL (Sig.obj RD b) ((sigU RD k).map f) ≫
          eqToHom (congrArg (pres RD k).obj (sig_obj_tensor (he.trans hab.endR_eq))).symm := by
  have hw : a.WhiskerOK (Obj.nil r) b.word := ⟨trivial, ha.symm, hab.ok_endR⟩
  have hu : Sig.sigW a b.word = Sig.obj RD b := by
    refine Obj.ext ?_ rfl
    show -Sig.eR (RD := RD) (Sig.eR (RD := RD) a.start a.word) b.word =
      -Sig.eR (RD := RD) b.start b.word
    rw [show Sig.eR (RD := RD) a.start a.word = b.start from hab.endR_eq]
  simp only [Presentation.wL, Presentation.wRAt, Functor.map_comp, eqToHom_map]
  rw [sigU_whisk f haw (ha'.trans ha.symm) he hw,
    sig_whisk_congr _ hu (show Sig.word RD (Obj.nil r : Obj (psig RD)).word = [] from rfl)]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- **`σ̃` reverses horizontal composition**: `σ̃(f ∘ g) = σ̃(g) ∘ σ̃(f)`. -/
theorem sigU_hcomp {l m n : U RD k} {x x' : Bicat.Hom l m} {y y' : Bicat.Hom m n}
    (f : (pres RD k).obj x.obj ⟶ (pres RD k).obj x'.obj)
    (g : (pres RD k).obj y.obj ⟶ (pres RD k).obj y'.obj) :
    (sigU RD k).map ((pres RD k).hcomp l.region f g x.start_eq x'.start_eq) =
      eqToHom (congrArg (pres RD k).obj (sig_obj_tensor (x.composable y).endR_eq)) ≫
        (pres RD k).hcomp (negR n.region) ((sigU RD k).map g) ((sigU RD k).map f)
          (show negR y.obj.endR = negR n.region by rw [y.endR_eq])
          (show negR y'.obj.endR = negR n.region by rw [y'.endR_eq]) ≫
        eqToHom (congrArg (pres RD k).obj (sig_obj_tensor (x'.composable y').endR_eq)).symm := by
  have hy : y'.obj.endR = y.obj.endR := y'.endR_eq.trans y.endR_eq.symm
  have hys : y'.obj.start = y.obj.start := y'.start_eq.trans y.start_eq.symm
  have hx : x'.obj.endR = x.obj.endR := x'.endR_eq.trans x.endR_eq.symm
  simp only [Presentation.hcomp, Functor.map_comp]
  rw [sigU_wRAt f y.obj x.start_eq x'.start_eq x.wf (x.composable y) hx,
    sigU_wL x'.obj g y.wf (x'.composable y) hys hy,
    wRAt_congr_region (show negR y.obj.endR = negR n.region by rw [y.endR_eq])]
  have e : Sig.eR (RD := RD) x.obj.start x.obj.word = Omega.rX (RD := RD) y.obj.start :=
    (x.composable y).endR_eq
  have hc : (Sig.obj RD y.obj).Composable (Sig.obj RD x.obj) :=
    ⟨(Sig.ok_word _ _ y.wf).1,
      (Sig.ok_word _ _ y.wf).2.trans (congrArg (fun r : X => -r) e.symm),
      (Sig.ok_word _ _ x.wf).1⟩
  have key := (pres RD k).wRAt_comp_wL hc ((sigU RD k).map g) ((sigU RD k).map f)
    (show negR y.obj.endR = negR n.region by rw [y.endR_eq])
    (show negR y'.obj.endR = negR n.region by rw [y'.endR_eq])
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% key]
  rfl

end Hcomp

/-! ## `[σ̃]` on `K₀(U̇)` -/

section K0

variable {ρ lam ρ' lam' : X} (hρ : -lam = ρ') (hl : -ρ = lam')

/-- **`[σ̃]` on `K₀(U̇(ρ, λ))`**: the `ℤ[q, q⁻¹]`-linear map `[A] ↦ [σ̃(A)]` into
`K₀(U̇(-λ, -ρ))` (KL III §3.6: the 2-functors `ω̃, σ̃, ψ̃, τ̃` induce the corresponding
(anti)automorphisms of `K₀(U̇)`). -/
def sigK0 : K0Kar RD k ρ lam →ₗ[LaurentPolynomial ℤ] K0Kar RD k ρ' lam' :=
  SplitK0.linearOfShift (SplitK0.map (sigDot ρ lam ρ' lam' hρ hl)) fun n A => by
    rw [SplitK0.map_of, SplitK0.map_of, SplitK0.shiftHom_of]
    exact SplitK0.of_iso (sigDotShift n A)

theorem sigK0_cl (A : UKar RD k ρ lam) :
    sigK0 hρ hl (K0U.cl A) = K0U.cl ((sigDot ρ lam ρ' lam' hρ hl).obj A) := by
  rw [sigK0, SplitK0.linearOfShift_apply, SplitK0.map_of]

/-- **`[σ̃][E_w 1_λ] = [E_{w^rev} 1_{-(λ + w_X)}]`**. -/
theorem sigK0_eC (w : List (Letter I)) (h : wt RD lam w = ρ) (h' : wt RD lam' w.reverse = ρ') :
    sigK0 hρ hl (eC RD k ρ lam w h) = eC RD k ρ' lam' w.reverse h' := by
  rw [eC, sigK0_cl, sigDot_nfObj _ _ h']

end K0

/-! ## `σ̃` on objects of `U̇`: composition and involutivity -/

section DotProps

variable {ρ μ lam : X}

/-- **`σ̃(A B) ≅ σ̃(B) σ̃(A)`** in `U̇`. -/
def sigDotHcomp (A : UKar RD k ρ μ) (B : UKar RD k μ lam) :
    (sigDot ρ lam (-lam) (-ρ) rfl rfl).obj ((hcompDot (deg RD)).obj (A, B)) ≅
      (hcompDot (deg RD)).obj ((sigDot μ lam (-lam) (-μ) rfl rfl).obj B,
        (sigDot ρ μ (-μ) (-ρ) rfl rfl).obj A) :=
  udIso _ _ (Equiv.prodComm _ _)
    (fun i => Bicat.Hom.ext
      (sig_obj_tensor ((A.X.X i.1).x.composable (B.X.X i.2).x).endR_eq).symm)
    (fun _ => add_comm _ _)
    (fun i j => by
      obtain ⟨a, b⟩ := i
      obtain ⟨a', b'⟩ := j
      show (pres RD k).hcomp (-lam) ((sigU RD k).map (B.p b b').1)
          ((sigU RD k).map (A.p a a').1) _ _ =
        _ ≫ (sigU RD k).map ((pres RD k).hcomp ρ (A.p a a').1 (B.p b b').1 _ _) ≫ _
      rw [sigU_hcomp]
      simp)

/-- **`σ̃(σ̃(A)) ≅ A`** in `U̇` (KL III: "The square of `σ̃` is the identity"). -/
def sigDotSigDot (A : UKar RD k ρ lam) (h3 : -(-ρ) = ρ) (h4 : -(-lam) = lam) :
    (sigDot (-lam) (-ρ) ρ lam h3 h4).obj ((sigDot ρ lam (-lam) (-ρ) rfl rfl).obj A) ≅ A :=
  udIso _ _ (Equiv.refl _) (fun i => Bicat.Hom.ext (Sig.obj_obj _ (A.X.X i).x.wf).symm)
    (fun _ => rfl)
    (fun i j => by
      show (A.p i j).1 = _ ≫ (sigU RD k).map ((sigU RD k).map (A.p i j).1) ≫ _
      rw [sigU_sigU (A.X.X i).x.wf (A.X.X j).x.wf]
      simp [TR])

end DotProps

/-! ## `[σ̃]` is a ring anti-involution of `K₀(U̇)` -/

section K0Props

variable {ρ μ lam : X}

/-- **`[σ̃]` is anti-multiplicative**: `[σ̃](x y) = [σ̃](y) [σ̃](x)`. -/
theorem sigK0_mul {a b c : X} (h1 : -lam = a) (h2 : -μ = b) (h3 : -ρ = c) (x : K0Kar RD k ρ μ)
    (y : K0Kar RD k μ lam) :
    sigK0 h1 h3 (K0U.mul x y) = K0U.mul (sigK0 h1 h2 y) (sigK0 h2 h3 x) := by
  subst h1 h2 h3
  induction x using SplitK0.induction_on generalizing y with
  | of A =>
    induction y using SplitK0.induction_on with
    | of B =>
      rw [K0U.mul_of, sigK0_cl, sigK0_cl, sigK0_cl, K0U.mul_of]
      exact SplitK0.of_iso (sigDotHcomp A B)
    | zero => simp
    | add y y' hy hy' => simp only [map_add, AddMonoidHom.add_apply, hy, hy']
    | neg y hy => simp only [map_neg, AddMonoidHom.neg_apply, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]

/-- `[σ̃][1_λ] = [1_{-λ}]`. -/
theorem sigK0_one (lam : X) :
    sigK0 (RD := RD) (k := k) (ρ := lam) (lam := lam) rfl rfl (K0U.one (deg := deg RD) _) =
      K0U.one (deg := deg RD) (wtObj RD k (-lam)) := by
  rw [K0U.one, sigK0_cl, sigDot_objOf]
  rfl

/-- **`[σ̃]² = 1`** (with the target weights identified with `ρ`, `λ` by any proofs). -/
theorem sigK0_sigK0 {ρ' lam' : X} (hρ : -lam = ρ') (hl : -ρ = lam') (h3 : -lam' = ρ)
    (h4 : -ρ' = lam) (x : K0Kar RD k ρ lam) : sigK0 h3 h4 (sigK0 hρ hl x) = x := by
  subst hρ hl
  induction x using SplitK0.induction_on with
  | of A =>
    rw [sigK0_cl, sigK0_cl]
    exact SplitK0.of_iso (sigDotSigDot A h3 h4)
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | neg x hx => rw [map_neg, map_neg, hx]

end K0Props

/-! ## KL III Proposition 3.28 for `σ`, integrally on generators (up to torsion) -/

section Dpss

omit [AddCommGroup X] [AddCommGroup Y] [DecidableEq I] in
theorem dpWord_reverse (d : List (Bool × I × ℕ)) : dpWord d.reverse = (dpWord d).reverse := by
  induction d with
  | nil => rfl
  | cons e d ih =>
    simp only [List.reverse_cons, dpWord_append, ih, dpWord_cons, dpWord_nil, List.append_nil,
      List.reverse_append, dpLetters, List.reverse_replicate]

omit [AddCommGroup X] [AddCommGroup Y] [DecidableEq I] in
theorem dpFac_reverse (d : List (Bool × I × ℕ)) :
    dpFac (C := C) d.reverse = dpFac (C := C) d := by
  simp [dpFac, List.map_reverse, List.prod_reverse]

/-- **KL III Proposition 3.28 for `σ`, integrally on generators, up to torsion**:
`[a]! · [σ̃][E_d 1_λ] = [a]! · [E_{d^rev} 1_{-ρ}]` in `K₀(U̇)` (`ρ = λ + |d|_X`,
`[a]! = ∏_r [a_r]_{i_r}!`); on the algebra side `σ(E_d 1_λ) = E_{d^rev} 1_{-ρ}`
(`UDot.sigmaUD_E1dp`). -/
theorem sigK0_dpC (d : List (Bool × I × ℕ)) (lam ρ : X) (h : wt RD lam (dpWord d) = ρ)
    (h' : wt RD (-ρ) (dpWord d.reverse) = -lam) :
    dpFac (C := C) d • sigK0 (RD := RD) (k := k) (ρ := ρ) (lam := lam) rfl rfl
        (dpC RD k d lam ρ h) =
      dpFac (C := C) d • dpC RD k d.reverse (-ρ) (-lam) h' := by
  have h'' : wt RD (-ρ) (dpWord d).reverse = -lam := by rwa [← dpWord_reverse]
  rw [← map_smul, ← eC_dpWord, sigK0_eC _ _ _ _ h'', ← dpFac_reverse, ← eC_dpWord]
  exact eC_congr (dpWord_reverse d).symm _ _

/-- `σ`-square on generators, exactly, if `K₀(U̇(-λ, -ρ))` is torsion free. -/
theorem sigK0_dpC_of_torsionFree (d : List (Bool × I × ℕ)) (lam ρ : X)
    (h : wt RD lam (dpWord d) = ρ) (h' : wt RD (-ρ) (dpWord d.reverse) = -lam)
    (htf : ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ), ∀ x : K0Kar RD k (-lam) (-ρ),
      p • x = 0 → x = 0) :
    sigK0 (RD := RD) (k := k) (ρ := ρ) (lam := lam) rfl rfl (dpC RD k d lam ρ h) =
      dpC RD k d.reverse (-ρ) (-lam) h' :=
  sub_eq_zero.1 (htf _ (dpFac_mem d) _ (by rw [smul_sub, sigK0_dpC, sub_self]))

end Dpss

/-! ## Global `ℚ(q)`-targets and `γ` on all of `U̇` -/

section Global

open scoped Classical

variable (V : Type*) [AddCommGroup V] [Module (RatFunc ℚ) V]

variable (RD k) in
/-- A *global* `ℚ(q)`-target of `K₀(U̇)`: a `ℚ(q)`-vector space `V` with additive maps
`φ_{ρ,λ} : K₀(U̇(ρ, λ)) → V` for all `ρ, λ`, compatible with `q` (equivalently, a `ℚ(q)`-linear
map `K₀(U̇) ⊗_{ℤ[q,q⁻¹]} ℚ(q) → V`, `K₀(U̇) = ⊕_{ρ,λ} K₀(U̇(ρ, λ))`). -/
structure GTarget where
  /-- The maps `φ_{ρ,λ}`. -/
  φ : ∀ ρ lam : X, K0Kar RD k ρ lam →+ V
  map_T : ∀ (ρ lam : X) (n : ℤ) (x : K0Kar RD k ρ lam),
    φ ρ lam ((T n : LaurentPolynomial ℤ) • x) = ((vQ ^ n : (RatFunc ℚ)ˣ) : RatFunc ℚ) • φ ρ lam x

variable {V}

/-- The block `K₀(U̇ 1_λ)` of a global target. -/
def GTarget.blk (Φ : GTarget RD k V) (lam : X) : QTarget RD k lam V :=
  ⟨fun ρ => Φ.φ ρ lam, fun ρ => Φ.map_T ρ lam⟩

omit [DecidableEq I] in
theorem GTarget.phi_eC (Φ : GTarget RD k V) {ρ ρ' lam lam' : X} {w w' : List (Letter I)}
    (hρ : ρ = ρ') (hl : lam = lam') (hw : w = w') (h : wt RD lam w = ρ) (h' : wt RD lam' w' = ρ') :
    Φ.φ ρ lam (eC RD k ρ lam w h) = Φ.φ ρ' lam' (eC RD k ρ' lam' w' h') := by
  subst hρ hl hw; rfl

/-- **`γ : U̇ → V`** (KL III Proposition 3.27 over `ℚ(q)`) on all blocks `U̇ 1_λ` at once. -/
def gammaUD (Φ : GTarget RD k V) : UD RD vQ →ₗ[RatFunc ℚ] V :=
  DirectSum.toModule (RatFunc ℚ) X _ fun lam => gammaQ' (Φ.blk lam)

theorem gammaUD_ofB (Φ : GTarget RD k V) (lam : X) (z : U1 RD vQ lam) :
    gammaUD Φ (ofB RD vQ lam z) = gammaQ' (Φ.blk lam) z := by
  rw [gammaUD, ofB, DirectSum.toModule_lof]

/-- `γ(E_w 1_λ) = φ([E_w 1_λ])`. -/
theorem gammaUD_E1 (Φ : GTarget RD k V) (w : List (Letter I)) (lam : X) :
    gammaUD Φ (E1 RD vQ w lam) = Φ.φ (wt RD lam w) lam (eC RD k _ lam w rfl) := by
  rw [E1, gammaUD_ofB, gammaQ'_mk_ew]
  rfl

/-- `γ(E_d 1_λ) = φ([E_d 1_λ])` on the generators of `_𝒜 U̇`. -/
theorem gammaUD_E1dp (Φ : GTarget RD k V) (d : List (Bool × I × ℕ)) (lam ρ : X)
    (h : wt RD lam (dpWord d) = ρ) :
    gammaUD Φ (E1dp RD vQ d lam) = Φ.φ ρ lam (dpC RD k d lam ρ h) := by
  rw [E1dp, gammaUD_ofB]
  exact gammaQ'_dpW (Φ.blk lam) d ρ h

/-- The pull-back of a global target along `[σ̃]`. -/
def GTarget.sigPull (Φ : GTarget RD k V) : GTarget RD k V where
  φ ρ lam := (Φ.φ (-lam) (-ρ)).comp
    (sigK0 (RD := RD) (k := k) (ρ := ρ) (lam := lam) rfl rfl).toAddMonoidHom
  map_T ρ lam n x := by
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearMap.map_smul,
      Φ.map_T]

theorem GTarget.sigPull_φ (Φ : GTarget RD k V) (ρ lam : X) (x : K0Kar RD k ρ lam) :
    Φ.sigPull.φ ρ lam x = Φ.φ (-lam) (-ρ) (sigK0 (ρ := ρ) (lam := lam) rfl rfl x) := rfl

/-- **KL III Proposition 3.28 for `σ`, over `ℚ(q)`**: `γ(σ x) = [σ̃] γ(x)` for all `x ∈ U̇`, i.e.
`γ_Φ ∘ σ = γ_{Φ ∘ [σ̃]}` for every global `ℚ(q)`-target `Φ` of `K₀(U̇)` (for the universal target
`K₀(U̇) ⊗_{ℤ[q,q⁻¹]} ℚ(q)` this is the commutative square itself). -/
theorem gammaUD_sigma (Φ : GTarget RD k V) (x : UD RD vQ) :
    gammaUD Φ (sigmaUD RD vQ x) = gammaUD Φ.sigPull x := by
  have key : (gammaUD Φ).comp (sigmaUD RD vQ) = gammaUD Φ.sigPull := by
    refine UD_lin_ext RD vQ fun t lam => ?_
    have h' : wt RD (-wt RD lam t) t.reverse = -lam := by
      rw [wt_eq_add_wX, wt_eq_add_wX, Sig.wX_reverse]; abel
    rw [LinearMap.comp_apply, sigmaUD_E1, gammaUD_E1, gammaUD_E1, GTarget.sigPull_φ,
      sigK0_eC rfl rfl t rfl h']
    exact Φ.phi_eC (by rw [wt_eq_add_wX, Sig.wX_reverse]; abel)
      (by rw [wt_eq_add_wX, add_comm]) rfl _ _
  exact LinearMap.congr_fun key x

/-- **Proposition 3.28 for `σ` on the generators `E_d 1_λ` of `_𝒜 U̇`, over `ℚ(q)`**:
`γ(σ(E_d 1_λ)) = [σ̃][E_d 1_λ]`. -/
theorem gammaUD_sigma_E1dp (Φ : GTarget RD k V) (d : List (Bool × I × ℕ)) (lam ρ : X)
    (h : wt RD lam (dpWord d) = ρ) :
    gammaUD Φ (sigmaUD RD vQ (E1dp RD vQ d lam)) =
      Φ.φ (-lam) (-ρ) (sigK0 (ρ := ρ) (lam := lam) rfl rfl (dpC RD k d lam ρ h)) := by
  rw [gammaUD_sigma, gammaUD_E1dp _ d lam ρ h]
  rfl

end Global

end Categorification.KL3.Diagram
