/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelSl2Rel

/-!
# Dotted bubbles in the `sl₂` model of `U`

The relations of KL III's `U` on dotted bubbles (`cwNeg`, `ccwNeg`, `cwOne`, `ccwOne`; CL §2.5,
`eq_positivity_bubbles`, arXiv:1111.1431v3 p. 8) hold in the `sl₂` model of
`Categorification.TwoRep.ModelSl2`, in every region `λ ≡ n₀ (mod 2)` (the regions reached from a
region of the string): bubbles of negative degree vanish (CL (3.4)) and the bubbles of degree zero
are the identity (CL (4.1) for the normalized left adjunctions, and CL Lemma 5.4 `c_{-1} = 1` for
the counter-clockwise bubble at `λ = -1`).

The image of a bubble diagram is computed from the images of its pieces: a cup, `m` dots on one
strand, a cap (`img_cupUp`, `img_cupDn`, `img_capUp`, `img_capDn`, `img_dotDn_UD`, `img_dotUp_DU`,
`img_dots`). The clockwise bubble carries its dots on the downward strand, i.e. the mates of the
dots under the left adjunction; `bub_mate` moves them to the upward strand, where the bubble is
`StrongSl2.cwBub` (`cwImg_eq`).

## Main results

* `StrongSl2.img_cwReal`, `img_ccwReal`: the images of the bubbles;
* `StrongSl2.cwReal_eq_zero`, `ccwReal_eq_zero`: bubbles of negative degree vanish;
* `StrongSl2.cwReal_deg_zero`, `ccwReal_deg_zero`: bubbles of degree zero are the identity.
-/

noncomputable section

set_option linter.unusedSimpArgs false

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

section Model

open GradedHomBicat GradedHomCat
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]

namespace StrongSl2

variable {S : StrongSl2 k B} (hS : S.BBw)

attribute [local irreducible] KL3.Diagram.sh

omit [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- The objects of the string reached by the model have the expected weight in the regions of the
right parity. -/
theorem wt_qi {lam : ℤ} (h : ∃ q : ℤ, lam = S.n₀ + 2 * q) : S.wt (S.qi lam) = lam := by
  obtain ⟨q, rfl⟩ := h
  unfold qi wt
  omega

theorem powComp_succ' {D : Type*} [Category D] {X : D} (f : X ⟶ X) (n : ℕ) :
    powComp f (n + 1) = f ≫ powComp f n := by
  induction n with
  | zero => simp [powComp]
  | succ n ih =>
    calc powComp f (n + 1 + 1) = powComp f (n + 1) ≫ f := rfl
      _ = (f ≫ powComp f n) ≫ f := by rw [ih]
      _ = f ≫ powComp f (n + 1) := by rw [Category.assoc]; rfl

/-- The mate of a power of an endomorphism of a right adjoint. -/
theorem conjugateEquiv_symm_powComp {C : Type*} [Bicategory C] {a b : C} {l : a ⟶ b} {r : b ⟶ a}
    (adj : l ⊣ r) (x : r ⟶ r) (m : ℕ) :
    (Bicategory.conjugateEquiv adj adj).symm (powComp x m) =
      powComp ((Bicategory.conjugateEquiv adj adj).symm x) m := by
  induction m with
  | zero =>
    simp only [powComp_zero]
    rw [Equiv.symm_apply_eq, Bicategory.conjugateEquiv_id]
  | succ m ih =>
    rw [powComp_succ, powComp_succ' ((Bicategory.conjugateEquiv adj adj).symm x), ← ih,
      Bicategory.conjugateEquiv_symm_comp]

/-- A clockwise bubble with the dots on the left adjoint, as their mate on the right adjoint. -/
theorem bub_mate {C : Type*} [Bicategory C] {a b : C} {R : b ⟶ a} {E : a ⟶ b} (A : R ⊣ E)
    (B : E ⊣ R) (x : E ⟶ E) (m : ℕ) :
    A.unit ≫ powComp ((Bicategory.conjugateEquiv A A).symm x) m ▷ E ≫ B.counit =
      A.unit ≫ R ◁ powComp x m ≫ B.counit := by
  rw [← conjugateEquiv_symm_powComp, ← reassoc_of% unit_whiskerLeft_conjugateEquiv,
    Equiv.apply_symm_apply]

/-- The clockwise bubble of the model (left cup, dots on the downward strand, right cap) is the
clockwise bubble `cwBub` (dots on the upward strand). -/
theorem cwImg_eq (a : ℤ) (m : ℕ) :
    (gAdjL hS a (a + 1) rfl).unit ≫ powComp (gDotR hS a (a + 1) rfl) m ▷ S.gEc a (a + 1) rfl ≫
        (S.gAdjE a (a + 1) rfl).counit = S.cwBub (hS.leftAdjN a) m :=
  (bub_mate (gAdjL hS a (a + 1) rfl) (S.gAdjE a (a + 1) rfl) (S.gDot a (a + 1) rfl) m).trans rfl

/-- The counter-clockwise bubble of the model is `ccwBub`. -/
theorem ccwImg_eq (a : ℤ) (m : ℕ) :
    (S.gAdjE a (a + 1) rfl).unit ≫ powComp (S.gDot a (a + 1) rfl) m ▷ S.gRc a (a + 1) rfl ≫
        (gAdjL hS a (a + 1) rfl).counit = S.ccwBub (hS.leftAdjN a) m := by
  rfl

/-- Clockwise bubbles of negative degree vanish in the model. -/
theorem cwImg_eq_zero (a b : ℤ) (h : a + 1 = b) {m : ℕ} (hm : (m : ℤ) < S.wt b - 1) :
    (gAdjL hS a b h).unit ≫ powComp (gDotR hS a b h) m ▷ S.gEc a b h ≫
        (S.gAdjE a b h).counit = 0 := by
  subst h
  rw [cwImg_eq]
  exact hS.cwBub_eq_zero hm

/-- The clockwise bubble of degree zero is the identity in the model. -/
theorem cwImg_eq_id (a b : ℤ) (h : a + 1 = b) (hb : 1 ≤ S.wt b) :
    (gAdjL hS a b h).unit ≫ powComp (gDotR hS a b h) ((S.wt b).toNat - 1) ▷ S.gEc a b h ≫
        (S.gAdjE a b h).counit = 𝟙 _ := by
  subst h
  rw [cwImg_eq]
  exact hS.cwBub_deg_zero hb

/-- Counter-clockwise bubbles of negative degree vanish in the model. -/
theorem ccwImg_eq_zero (a b : ℤ) (h : a + 1 = b) {m : ℕ} (hm : (m : ℤ) < -S.wt a - 1) :
    (S.gAdjE a b h).unit ≫ powComp (S.gDot a b h) m ▷ S.gRc a b h ≫
        (gAdjL hS a b h).counit = 0 := by
  subst h
  rw [ccwImg_eq]
  exact hS.ccwBub_eq_zero hm

/-- The counter-clockwise bubble of degree zero is the identity in the model (for weight `-1`
this is CL's `c_{-1} = 1`, Lemma 5.4). -/
theorem ccwImg_eq_id (a b : ℤ) (h : a + 1 = b) (ha : S.wt a ≤ -1) :
    (S.gAdjE a b h).unit ≫ powComp (S.gDot a b h) ((-S.wt a).toNat - 1) ▷ S.gRc a b h ≫
        (gAdjL hS a b h).counit = 𝟙 _ := by
  subst h
  rw [ccwImg_eq]
  exact hS.ccwBub_deg_zero' ha

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- Splitting a conjugated composite. -/
theorem conj_comp_conj {D : Type*} [Category D] {X X' Y Y' Z Z' : D} (p : X = X') (q : Y = Y')
    (r : Z = Z') (f : X ⟶ Y) (g : Y ⟶ Z) :
    eqToHom p.symm ≫ (f ≫ g) ≫ eqToHom r =
      (eqToHom p.symm ≫ f ≫ eqToHom q) ≫ (eqToHom q.symm ≫ g ≫ eqToHom r) := by
  simp

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem dots_succ (lam : ℤ) (u : List (Letter Unit)) (l : Letter Unit) (v : List (Letter Unit))
    (m : ℕ) :
    dots sl2RootDatum lam u l v (m + 1) =
      mkD sl2RootDatum lam [(u, .dot l, v)] ⟨rfl, rfl⟩ ≫ dots sl2RootDatum lam u l v m := by
  exact (mkD_comp sl2RootDatum lam [(u, .dot l, v)] (List.replicate m (u, .dot l, v)) _ _).symm

/-- The image of `m` dots is the `m`-th power of the image of one dot. -/
theorem img_dots {s t : ℤ} (lam : ℤ) (u : List (Letter Unit)) (l : Letter Unit)
    (v : List (Letter Unit))
    (h : Cond (S := psig sl2RootDatum) s t (ob sl2RootDatum lam (u ++ [l] ++ v))) (m : ℕ) :
    eqToHom (objI_pos _ _ h).symm ≫
        (interp (genImg hS) s t).functor.map (dots sl2RootDatum lam u l v m) ≫
        eqToHom (objI_pos _ _ h) =
      powComp (eqToHom (objI_pos _ _ h).symm ≫
        (interp (genImg hS) s t).functor.map
          (mkD sl2RootDatum lam [(u, .dot l, v)] ⟨rfl, rfl⟩) ≫ eqToHom (objI_pos _ _ h)) m := by
  induction m with
  | zero =>
    have h0 : dots sl2RootDatum lam u l v 0 = 𝟙 _ := rfl
    set_option backward.isDefEq.respectTransparency false in
    rw [h0, CategoryTheory.Functor.map_id]
    simp
  | succ m ih =>
    set_option backward.isDefEq.respectTransparency false in
    rw [dots_succ, Functor.map_comp, conj_comp_conj (objI_pos _ _ h) (objI_pos _ _ h) (objI_pos _ _ h), ih, powComp_succ']

set_option maxHeartbeats 2000000 in
/-- The image of the cup `1_λ → E F`. -/
theorem img_cupUp (lam : ℤ) (h₀ : Cond (S := psig sl2RootDatum) lam lam (ob sl2RootDatum lam []))
    (h₁ : Cond (S := psig sl2RootDatum) lam lam (ob sl2RootDatum lam [up (), dn ()])) :
    eqToHom (objI_pos _ _ h₀).symm ≫
        (interp (genImg hS) lam lam).functor.map
          (mkD sl2RootDatum lam [([], .cup (up ()), [])] ⟨rfl, rfl⟩) ≫
        eqToHom (objI_pos _ _ h₁) =
      (gAdjL hS (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam)).unit := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_nil, wt_nil, List.nil_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  case c1 => exact ⟨trivial, rfl, rfl⟩
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  try rw [eqToHom_word ?w1 _]
  · unfold coreC core
    refine (chain1_key S.model ((λ_ _) ≪≫ (ρ_ _)) ((λ_ _) ≪≫ (ρ_ _)) _ _ _ _ _ (𝟙 _)
      (eqToHom ?e)).trans ?main
    case main =>
      set_option backward.isDefEq.respectTransparency false in
      rw [layerAt_whole, PrelaxFunctor.map₂_id, Category.id_comp, lift_map₂_eqToHom]
      erw [eqToHom_refl, Category.comp_id]
      exact genImg_cup_true hS () _ _ _ _ _ _ _
    case e =>
      exact fw_eq (by simp [inv_dual, Letter.dual, sh_true_sh_false, ob]) _ _ _ _
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, Letter.dual, sh_true_sh_false, sh_false_sh_true, sig0_dom_dot']

set_option maxHeartbeats 2000000 in
/-- The image of the cup `1_λ → F E`. -/
theorem img_cupDn (lam : ℤ) (h₀ : Cond (S := psig sl2RootDatum) lam lam (ob sl2RootDatum lam []))
    (h₁ : Cond (S := psig sl2RootDatum) lam lam (ob sl2RootDatum lam [dn (), up ()])) :
    eqToHom (objI_pos _ _ h₀).symm ≫
        (interp (genImg hS) lam lam).functor.map
          (mkD sl2RootDatum lam [([], .cup (dn ()), [])] ⟨rfl, rfl⟩) ≫
        eqToHom (objI_pos _ _ h₁) =
      (S.gAdjE (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam)).unit := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_nil, wt_nil, List.nil_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  case c1 => exact ⟨trivial, rfl, rfl⟩
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  try rw [eqToHom_word ?w1 _]
  · unfold coreC core
    refine (chain1_key S.model ((λ_ _) ≪≫ (ρ_ _)) ((λ_ _) ≪≫ (ρ_ _)) _ _ _ _ _ (𝟙 _)
      (eqToHom ?e)).trans ?main
    case main =>
      set_option backward.isDefEq.respectTransparency false in
      rw [layerAt_whole, PrelaxFunctor.map₂_id, Category.id_comp, lift_map₂_eqToHom]
      erw [eqToHom_refl, Category.comp_id]
      exact genImg_cup_false hS () _ _ _ _ _ _ _
    case e =>
      exact fw_eq (by simp [inv_dual, Letter.dual, sh_false_sh_true, ob]) _ _ _ _
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, Letter.dual, sh_true_sh_false, sh_false_sh_true, sig0_dom_dot']

set_option maxHeartbeats 2000000 in
/-- The image of the cap `F E → 1_λ` (the counit of the left adjunction). -/
theorem img_capUp (lam : ℤ)
    (h₀ : Cond (S := psig sl2RootDatum) lam lam (ob sl2RootDatum lam [dn (), up ()]))
    (h₁ : Cond (S := psig sl2RootDatum) lam lam (ob sl2RootDatum lam [])) :
    eqToHom (objI_pos _ _ h₀).symm ≫
        (interp (genImg hS) lam lam).functor.map
          (mkD sl2RootDatum lam [([], .cap (up ()), [])] ⟨rfl, rfl⟩) ≫
        eqToHom (objI_pos _ _ h₁) =
      (gAdjL hS (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam)).counit := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_nil, wt_nil, List.nil_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  case c1 => exact h₀
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  try rw [eqToHom_word ?w1 _]
  · unfold coreC core
    refine (chain1_key S.model ((λ_ _) ≪≫ (ρ_ _)) ((λ_ _) ≪≫ (ρ_ _)) _ _ _ _ _ (eqToHom ?e)
      (𝟙 _)).trans ?main
    case main =>
      set_option backward.isDefEq.respectTransparency false in
      rw [layerAt_whole, PrelaxFunctor.map₂_id, Category.comp_id, lift_map₂_eqToHom]
      erw [eqToHom_refl, Category.id_comp]
      exact genImg_cap_true hS () _ _ _ _ _ _ _
    case e =>
      exact fw_eq (by simp [inv_dual, Letter.dual, ob]) _ _ _ _
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, Letter.dual, sh_true_sh_false, sh_false_sh_true, sig0_dom_dot']

set_option maxHeartbeats 2000000 in
/-- The image of the cap `E F → 1_λ` (the counit of `E ⊣ R`). -/
theorem img_capDn (lam : ℤ)
    (h₀ : Cond (S := psig sl2RootDatum) lam lam (ob sl2RootDatum lam [up (), dn ()]))
    (h₁ : Cond (S := psig sl2RootDatum) lam lam (ob sl2RootDatum lam [])) :
    eqToHom (objI_pos _ _ h₀).symm ≫
        (interp (genImg hS) lam lam).functor.map
          (mkD sl2RootDatum lam [([], .cap (dn ()), [])] ⟨rfl, rfl⟩) ≫
        eqToHom (objI_pos _ _ h₁) =
      (S.gAdjE (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam)).counit := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_nil, wt_nil, List.nil_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  case c1 => exact h₀
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  try rw [eqToHom_word ?w1 _]
  · unfold coreC core
    refine (chain1_key S.model ((λ_ _) ≪≫ (ρ_ _)) ((λ_ _) ≪≫ (ρ_ _)) _ _ _ _ _ (eqToHom ?e)
      (𝟙 _)).trans ?main
    case main =>
      set_option backward.isDefEq.respectTransparency false in
      rw [layerAt_whole, PrelaxFunctor.map₂_id, Category.comp_id, lift_map₂_eqToHom]
      erw [eqToHom_refl, Category.id_comp]
      exact genImg_cap_false hS () _ _ _ _ _ _ _
    case e =>
      exact fw_eq (by simp [inv_dual, Letter.dual, ob]) _ _ _ _
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, Letter.dual, sh_true_sh_false, sh_false_sh_true, sig0_dom_dot']

set_option maxHeartbeats 2000000 in
/-- The image of a dot on the downward strand of `E F`. -/
theorem img_dotDn_UD (lam : ℤ)
    (h₀ : Cond (S := psig sl2RootDatum) lam lam (ob sl2RootDatum lam [up (), dn ()])) :
    eqToHom (objI_pos _ _ h₀).symm ≫
        (interp (genImg hS) lam lam).functor.map
          (mkD sl2RootDatum lam [([up ()], .dot (dn ()), [])] ⟨rfl, rfl⟩) ≫
        eqToHom (objI_pos _ _ h₀) =
      gDotR hS (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam) ▷
        S.gEc (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
          (by have := S.qi_sh_true () (sh sl2RootDatum (dn ()) + lam)
              rwa [sh_true_sh_false] at this) := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  case c1 => exact h₀
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  try rw [eqToHom_word ?w1 _]
  · unfold coreC core
    refine (chain1_key S.model (λ_ _) (λ_ _) _ _ _ _ _ (eqToHom ?e)
      (eqToHom ?e')).trans ?main
    case main =>
      set_option backward.isDefEq.respectTransparency false in
      rw [layerAt_left]
      simp only [lift_map₂_eqToHom, eqToHom_refl, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      erw [genImg_dot_false hS]
      rfl
    case e => rfl
    case e' => rfl
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, Letter.dual, sh_true_sh_false, sh_false_sh_true, sig0_dom_dot']

set_option maxHeartbeats 2000000 in
/-- The image of a dot on the upward strand of `F E`. -/
theorem img_dotUp_DU (lam : ℤ)
    (h₀ : Cond (S := psig sl2RootDatum) lam lam (ob sl2RootDatum lam [dn (), up ()])) :
    eqToHom (objI_pos _ _ h₀).symm ≫
        (interp (genImg hS) lam lam).functor.map
          (mkD sl2RootDatum lam [([dn ()], .dot (up ()), [])] ⟨rfl, rfl⟩) ≫
        eqToHom (objI_pos _ _ h₀) =
      S.gDot (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam) ▷
        S.gRc (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam) := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  case c1 => exact h₀
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  try rw [eqToHom_word ?w1 _]
  · unfold coreC core
    refine (chain1_key S.model (λ_ _) (λ_ _) _ _ _ _ _ (eqToHom ?e)
      (eqToHom ?e')).trans ?main
    case main =>
      set_option backward.isDefEq.respectTransparency false in
      rw [layerAt_left]
      simp only [lift_map₂_eqToHom, eqToHom_refl, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      erw [genImg_dot_true hS]
      rfl
    case e => rfl
    case e' => rfl
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, Letter.dual, sh_true_sh_false, sh_false_sh_true, sig0_dom_dot']

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem cwReal_eq (lam : ℤ) (m : ℕ) :
    cwReal sl2RootDatum lam () m =
      mkD sl2RootDatum lam [([], .cup (up ()), [])] ⟨rfl, rfl⟩ ≫
        dots sl2RootDatum lam [up ()] (dn ()) [] m ≫
          mkD sl2RootDatum lam [([], .cap (dn ()), [])] ⟨rfl, rfl⟩ := by
  unfold cwReal dots
  set_option backward.isDefEq.respectTransparency false in
  rw [mkD_comp, mkD_comp]
  rfl

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem ccwReal_eq (lam : ℤ) (m : ℕ) :
    ccwReal sl2RootDatum lam () m =
      mkD sl2RootDatum lam [([], .cup (dn ()), [])] ⟨rfl, rfl⟩ ≫
        dots sl2RootDatum lam [dn ()] (up ()) [] m ≫
          mkD sl2RootDatum lam [([], .cap (up ()), [])] ⟨rfl, rfl⟩ := by
  unfold ccwReal dots
  set_option backward.isDefEq.respectTransparency false in
  rw [mkD_comp, mkD_comp]
  rfl

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem cond_nil (lam : ℤ) : Cond (S := psig sl2RootDatum) lam lam (ob sl2RootDatum lam []) :=
  ⟨trivial, rfl, rfl⟩

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem cond_up_dn (lam : ℤ) :
    Cond (S := psig sl2RootDatum) lam lam (ob sl2RootDatum lam [up (), dn ()]) := by
  refine ⟨⟨?_, rfl, trivial⟩, rfl, ?_⟩
  · exact sh_true_sh_false () lam
  · exact sh_true_sh_false () lam

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem cond_dn_up (lam : ℤ) :
    Cond (S := psig sl2RootDatum) lam lam (ob sl2RootDatum lam [dn (), up ()]) := by
  refine ⟨⟨?_, rfl, trivial⟩, rfl, ?_⟩
  · exact sh_false_sh_true () lam
  · exact sh_false_sh_true () lam

/-- The image of the clockwise bubble with `m` dots in the region `λ`. -/
theorem img_cwReal (lam : ℤ) (m : ℕ) :
    eqToHom (objI_pos _ _ (cond_nil lam)).symm ≫
        (interp (genImg hS) lam lam).functor.map (cwReal sl2RootDatum lam () m) ≫
        eqToHom (objI_pos _ _ (cond_nil lam)) =
      (gAdjL hS (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam)).unit ≫
        powComp (gDotR hS (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
          (S.qi_sh_false () lam)) m ▷ S.gEc (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
            (S.qi_sh_false () lam) ≫
        (S.gAdjE (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
          (S.qi_sh_false () lam)).counit := by
  set_option backward.isDefEq.respectTransparency false in
  rw [cwReal_eq, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    conj_comp_conj (objI_pos _ _ (cond_nil lam)) (objI_pos _ _ (cond_up_dn lam))
      (objI_pos _ _ (cond_nil lam)),
    conj_comp_conj (objI_pos _ _ (cond_up_dn lam)) (objI_pos _ _ (cond_up_dn lam))
      (objI_pos _ _ (cond_nil lam)),
    img_cupUp hS lam (cond_nil lam) (cond_up_dn lam), 
    img_capDn hS lam (cond_up_dn lam) (cond_nil lam)]
  erw [img_dots hS lam [up ()] (dn ()) [] (cond_up_dn lam) m, img_dotDn_UD hS lam (cond_up_dn lam)]
  rw [← powComp_whiskerRight]

/-- The image of the counter-clockwise bubble with `m` dots in the region `λ`. -/
theorem img_ccwReal (lam : ℤ) (m : ℕ) :
    eqToHom (objI_pos _ _ (cond_nil lam)).symm ≫
        (interp (genImg hS) lam lam).functor.map (ccwReal sl2RootDatum lam () m) ≫
        eqToHom (objI_pos _ _ (cond_nil lam)) =
      (S.gAdjE (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam)).unit ≫
        powComp (S.gDot (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam))
          (S.qi_sh_true () lam)) m ▷ S.gRc (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam))
            (S.qi_sh_true () lam) ≫
        (gAdjL hS (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam))
          (S.qi_sh_true () lam)).counit := by
  set_option backward.isDefEq.respectTransparency false in
  rw [ccwReal_eq, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    conj_comp_conj (objI_pos _ _ (cond_nil lam)) (objI_pos _ _ (cond_dn_up lam))
      (objI_pos _ _ (cond_nil lam)),
    conj_comp_conj (objI_pos _ _ (cond_dn_up lam)) (objI_pos _ _ (cond_dn_up lam))
      (objI_pos _ _ (cond_nil lam)),
    img_cupDn hS lam (cond_nil lam) (cond_dn_up lam), 
    img_capUp hS lam (cond_dn_up lam) (cond_nil lam)]
  erw [img_dots hS lam [dn ()] (up ()) [] (cond_dn_up lam) m, img_dotUp_DU hS lam (cond_dn_up lam)]
  rw [← powComp_whiskerRight]

/-- **Clockwise bubbles of negative degree vanish** in the `sl₂` model (KL III `cwNeg`), in the
regions of the right parity. -/
theorem cwReal_eq_zero {lam : ℤ} (hpar : ∃ q : ℤ, lam = S.n₀ + 2 * q) {m : ℕ}
    (hm : (m : ℤ) < lam - 1) :
    (interp (genImg hS) lam lam).functor.map (cwReal sl2RootDatum lam () m) = 0 := by
  apply (cancel_epi (eqToHom (objI_pos _ _ (cond_nil lam)).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ (cond_nil lam)))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, Limits.comp_zero, Limits.zero_comp]
  rw [img_cwReal]
  exact cwImg_eq_zero hS _ _ _ (by rw [wt_qi hpar]; exact hm)

/-- **The clockwise bubble of degree zero is the identity** in the `sl₂` model (KL III `cwOne`),
in the regions `λ ≥ 1` of the right parity. -/
theorem cwReal_deg_zero {lam : ℤ} (hpar : ∃ q : ℤ, lam = S.n₀ + 2 * q) (hl : 1 ≤ lam) :
    (interp (genImg hS) lam lam).functor.map (cwReal sl2RootDatum lam () (lam - 1).toNat) =
      𝟙 _ := by
  apply (cancel_epi (eqToHom (objI_pos _ _ (cond_nil lam)).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ (cond_nil lam)))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc]
  rw [img_cwReal]
  erw [Category.id_comp, eqToHom_trans, eqToHom_refl]
  have e : (lam - 1).toNat = (S.wt (S.qi lam)).toNat - 1 := by rw [wt_qi hpar]; omega
  rw [e]
  exact cwImg_eq_id hS _ _ (S.qi_sh_false () lam) (by rw [wt_qi hpar]; exact hl)

/-- **The counter-clockwise bubble of degree zero is the identity** in the `sl₂` model (KL III
`ccwOne`), in the regions `λ ≤ -1` of the right parity (for `λ = -1` this is CL's `c_{-1} = 1`,
Lemma 5.4). -/
theorem ccwReal_deg_zero {lam : ℤ} (hpar : ∃ q : ℤ, lam = S.n₀ + 2 * q) (hl : lam ≤ -1) :
    (interp (genImg hS) lam lam).functor.map (ccwReal sl2RootDatum lam () (-lam - 1).toNat) =
      𝟙 _ := by
  apply (cancel_epi (eqToHom (objI_pos _ _ (cond_nil lam)).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ (cond_nil lam)))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc]
  rw [img_ccwReal]
  erw [Category.id_comp, eqToHom_trans, eqToHom_refl]
  have e : (-lam - 1).toNat = (-S.wt (S.qi lam)).toNat - 1 := by rw [wt_qi hpar]; omega
  rw [e]
  exact ccwImg_eq_id hS _ _ (S.qi_sh_true () lam) (by rw [wt_qi hpar]; exact hl)

/-- **Counter-clockwise bubbles of negative degree vanish** in the `sl₂` model (KL III
`ccwNeg`), in the regions of the right parity. -/
theorem ccwReal_eq_zero {lam : ℤ} (hpar : ∃ q : ℤ, lam = S.n₀ + 2 * q) {m : ℕ}
    (hm : (m : ℤ) < -lam - 1) :
    (interp (genImg hS) lam lam).functor.map (ccwReal sl2RootDatum lam () m) = 0 := by
  apply (cancel_epi (eqToHom (objI_pos _ _ (cond_nil lam)).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ (cond_nil lam)))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, Limits.comp_zero, Limits.zero_comp]
  rw [img_ccwReal]
  exact ccwImg_eq_zero hS _ _ _ (by rw [wt_qi hpar]; exact hm)

end StrongSl2

end Model

end Categorification.TwoRep
