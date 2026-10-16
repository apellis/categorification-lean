/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.VacuumLabels
import Categorification.TwoRep.RouqCoproductBubbles
import Categorification.TwoRep.SumInvPointwise

/-!
# Rouquier's data of a highest weight label at the generating object

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`. Let `L` be Rouquier's data (`RouqLoc`, J. Brundan, *On the
definition of Kac–Moody 2-category*, arXiv:1501.00350v1, Definition 1.1) of one label at a
weight `h ≥ 0` in `LinearCat k`, and let `V` be an object with `F E V = 0` (`V` is highest
weight for the label). If the dots are nilpotent and `End V` is reduced, then at `V`

* the caps `yᵐ ≫ κ` (`m < h`) and the `♠`-cups `g_m = η'_m` decompose the identity of `E F V`
  (`sum_capD_cupN_app`);
* `g_m ≫ yᵐ' ≫ κ = δ_{m m'}` for all `m'` (`cupN_app_capD_app`): for `m' < h` by Brundan (3.6),
  and for `m' ≥ h` because the bubble is nilpotent (`RouqLoc.cupN_capD_sub_isNilpotent`), hence
  zero in `End V`;
* so a polynomial dot `p(y)` acts on the cups triangularly (`cupN_app_aeval_sub`), as needed
  by `chainSum_comp_sigma`.
-/

noncomputable section

namespace Categorification.KLR.Unfurling

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits TwoRep Polynomial

universe w v u

variable {k : Type w} [CommRing k] {C₁ C₂ C₃ : LinearCat.{w, v, u} k}
  {E₁ : C₁ ⟶ C₂} {R₁ : C₂ ⟶ C₁} {E₂ : C₂ ⟶ C₃} {R₂ : C₃ ⟶ C₂}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ} (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) (V : (C₂ : Type u))

/-- Evaluation of the 2-endomorphisms of `𝟙 C₂` at an object. -/
def endIdEval : End (𝟙 C₂) →+* End V where
  toFun f := f.hom.app V
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Evaluation of 2-morphisms of endo-1-morphisms of `C₂` at an object. -/
abbrev evalAt : (C₂ ⟶ C₂) ⥤ (C₂ : Type u) :=
  LinearCat.homForget C₂ C₂ ⋙ (evaluation _ _).obj V

/-- The dot on `E F V`. -/
abbrev dotAt : End (E₁.obj.obj (R₁.obj.obj V)) := x₁.hom.app (R₁.obj.obj V)

omit L in
theorem powComp_app (n : ℕ) :
    (powComp x₁ n).hom.app (R₁.obj.obj V) = (dotAt (x₁ := x₁) V ^ n : End _) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [powComp_succ, pow_succ', End.mul_def, ← ih]
    rfl

theorem capD_app (m : ℕ) :
    (L.capD m).hom.app V = (dotAt (x₁ := x₁) V ^ m : End _) ≫ adj₁.counit.hom.app V := by
  rw [← powComp_app]
  rfl

/-- **The caps and `♠`-cups decompose `E F V`** when `F E V = 0` (Brundan (1.8) at `V`). -/
theorem sum_capD_cupN_app (hh : 0 ≤ h) (hY : IsZero (R₂.obj.obj (E₂.obj.obj V))) :
    ∑ m ∈ Finset.range h.toNat, ((dotAt (x₁ := x₁) V ^ m : End _) ≫ adj₁.counit.hom.app V) ≫
      (L.cupN m).hom.app V = 𝟙 (E₁.obj.obj (R₁.obj.obj V)) := by
  have hY' : IsZero ((evalAt V).obj (E₂ ≫ R₂)) := hY
  have t := ((L.ip hh).map (evalAt V)).total
  have h0 : (evalAt V).map L.sig ≫ ((L.ip hh).map (evalAt V)).f' = 0 := by
    rw [hY'.eq_zero_of_src ((L.ip hh).map (evalAt V)).f', Limits.comp_zero]
  rw [h0, zero_add] at t
  refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) t
  show _ = (L.capD m).hom.app V ≫ ((L.ip hh).g' m).hom.app V
  rw [capD_app]
  simp only [RouqLoc.cupN, hh, ↓reduceDIte]
  rfl

/-- **The `♠`-cups against the dotted caps at `V`**: `g_m ≫ yᵐ' ≫ κ = δ_{m m'}` for every `m'`,
if the dots are nilpotent and `End V` is reduced. -/
theorem cupN_app_capD_app {n : ℕ} (hx₁ : powComp x₁ n = 0) (hx₂ : powComp x₂ n = 0)
    [IsReduced (End V)] {m : ℕ} (hm : m < h.toNat) (m' : ℕ) :
    (L.cupN m).hom.app V ≫ (dotAt (x₁ := x₁) V ^ m' : End _) ≫ adj₁.counit.hom.app V =
      if m' = m then 𝟙 V else 0 := by
  have hz := ((L.cupN_capD_sub_isNilpotent hx₁ hx₂ hm m').map (endIdEval V)).eq_zero
  rw [map_sub, sub_eq_zero] at hz
  refine Eq.trans ?_ (hz.trans ?_)
  · show _ = (L.cupN m).hom.app V ≫ (L.capD m').hom.app V
    rw [capD_app]
    rfl
  by_cases hmm : m = m'
  · subst hmm; simp only [↓reduceIte]; rfl
  · simp only [hmm, Ne.symm hmm, ↓reduceIte, map_zero]

/-- **The dot `p(y)` on the `♠`-cups at `V`**: with `F E V = 0`, nilpotent dots and `End V`
reduced, `g_m ≫ (p(y) - p₀) = ∑_{j<m} p_{m-j} g_j` for `m < h`. -/
theorem cupN_app_aeval_sub (hh : 0 ≤ h) (hY : IsZero (R₂.obj.obj (E₂.obj.obj V))) {n : ℕ}
    (hx₁ : powComp x₁ n = 0) (hx₂ : powComp x₂ n = 0) [IsReduced (End V)] (p : k[X]) {m : ℕ}
    (hm : m < h.toNat) :
    (L.cupN m).hom.app V ≫ (aeval (dotAt (x₁ := x₁) V) p -
      algebraMap k (End (E₁.obj.obj (R₁.obj.obj V))) (p.coeff 0) : End _) =
      ∑ j ∈ Finset.range m, p.coeff (m - j) • (L.cupN j).hom.app V :=
  chain_comp_aeval_sub (adj₁.counit.hom.app V) (dotAt V) h.toNat
    (fun m => (L.cupN m).hom.app V) (sum_capD_cupN_app L V hh hY)
    (fun _ m' hm => cupN_app_capD_app L V hx₁ hx₂ hm m') p m hm

end Categorification.KLR.Unfurling
