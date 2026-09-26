/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.BubbleSlidesEq

/-!
# The infinite Grassmannian relation in all degrees

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1,
Definition 3.1 (TeX label `eq_infinite_Grass`): "The above equation, called the infinite
Grassmannian relation, remains valid even in high degree when most of the bubbles involved are
not fake bubbles. See [Lau1] for more details." In the presentation `pres RD k` the fake bubbles
are *defined* by the Grassmannian relation in low degrees (`grassInv`); here we prove the
relation in all degrees, following A. Lauda, *A categorification of quantum sl(2)*,
arXiv:0803.3652v3, Proposition 5.5: the figure-eight diagram (the crossing of `E_i E_i` with
both strands closed) is reduced in two ways, with the left and with the right curl relations.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Placement of single diagrams -/

theorem plcL_diag (μ : X) (u v s t : List (Letter I))
    (d : ob RD (wt RD μ v) s ⟶ ob RD (wt RD μ v) t) :
    plcL RD k μ u v s t ((pres RD k).diag d) =
      (pres RD k).diag (Diagram.cast (Diagram.whisker d (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v)
        (whiskerOK_ob RD μ u v s)) (ob_whisker RD μ u v s s rfl)
        (ob_whisker RD μ u v s t (Diagram.chain d).start_eq)) := by
  have hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s := (Diagram.chain d).start_eq
  simp only [plcL]
  rw [dif_pos hst]
  simp only [plc, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Presentation.whisk_diag _ _ _ _ (whiskerOK_ob RD μ u v s), Presentation.diag_cast]

/-- Transport an equality of classes of diagrams along equalities of boundary objects and of
lists of layers. -/
theorem diag_transfer {a b a' b' : Obj (psig RD)} (A B : a ⟶ b) (A' B' : a' ⟶ b') (e₁ : a = a')
    (e₂ : b = b') (hA : Diagram.layers A = Diagram.layers A')
    (hB : Diagram.layers B = Diagram.layers B') (h : (pres RD k).diag A' = (pres RD k).diag B') :
    (pres RD k).diag A = (pres RD k).diag B := by
  subst e₁ e₂
  rw [(pres RD k).diag_eq_of_layers_eq hA, (pres RD k).diag_eq_of_layers_eq hB, h]

/-- Linear maps on `Hom` spaces of `U` agree if they agree on classes of diagrams. -/
theorem hom_ext_diag {a b : Obj (psig RD)} {M : Type*} [AddCommGroup M] [Module k M]
    (φ ψ : ((pres RD k).obj a ⟶ (pres RD k).obj b) →ₗ[k] M)
    (h : ∀ d : a ⟶ b, φ ((pres RD k).diag d) = ψ ((pres RD k).diag d)) : φ = ψ := by
  ext f
  obtain ⟨F, rfl⟩ := (pres RD k).lin_surjective f
  induction F using Finsupp.induction_linear with
  | zero => simp only [Presentation.lin_zero, map_zero]
  | add F₁ F₂ h₁ h₂ => rw [Presentation.lin_add, map_add, map_add, h₁, h₂]
  | single d r => rw [Presentation.lin_single, map_smul, map_smul, h d]

/-- Reduction of a statement `Φ β = nhCross β` (with `Φ`, `nhCross` built from linear maps, after unfolding
the given abbreviations) to classes of diagrams `β`. -/
syntax "diag_induction " ident " [" Lean.Parser.Tactic.simpLemma,* "]" " => " tacticSeq : tactic

macro_rules
  | `(tactic| diag_induction $β [$ids,*] => $tac) => `(tactic| (
    obtain ⟨F, hF⟩ := (pres _ _).lin_surjective $β
    subst hF
    induction F using Finsupp.induction_linear with
    | zero => rw [Presentation.lin_zero]; simp only [$ids,*, map_zero]
    | add F₁ F₂ h₁ h₂ =>
      rw [Presentation.lin_add]; simp only [$ids,*, map_add] at h₁ h₂ ⊢; rw [h₁, h₂]
    | single d r =>
      rw [Presentation.lin_single]; simp only [$ids,*, map_smul]
      congr 1
      ($tac)))

/-! ## Nested placements -/

section Nested

variable (ρ : X) (i : I)

theorem plcL_bubLU_dn (β : End ((pres RD k).obj (ob RD (wt RD (wt RD ρ [dn i]) [up i]) []))) :
    plcL RD k ρ [] [dn i] [up i] [up i] (bubLU RD k (wt RD ρ [dn i]) (up i) β) =
      plcL RD k ρ [] [up i, dn i] [] [] β := by
  diag_induction β [bubLU] =>
    rw [plcL_diag, plcL_diag, plcL_diag]
    exact (pres RD k).diag_eq_of_layers_eq (by
      simp only [Diagram.layers_cast, Diagram.layers_whisker, List.map_map, Function.comp_def,
        Layer.whisker_whisker]
      rfl)

theorem plcL_bubRU_dn (γ : End ((pres RD k).obj (ob RD ρ []))) :
    plcL RD k ρ [dn i] [] [up i] [up i] (bubRU RD k ρ (up i) γ) =
      plcL RD k ρ [dn i, up i] [] [] [] γ := by
  diag_induction γ [bubRU] =>
    rw [plcL_diag, plcL_diag, plcL_diag]
    exact (pres RD k).diag_eq_of_layers_eq (by
      simp only [Diagram.layers_cast, Diagram.layers_whisker, List.map_map, Function.comp_def,
        Layer.whisker_whisker]
      rfl)

theorem plcL_plcL_dnL (f : End ((pres RD k).obj (ob RD (wt RD ρ [dn i]) [up i, up i]))) :
    plcL RD k ρ [] [dn i] [dn i, up i, up i] [dn i, up i, up i]
        (plcL RD k (wt RD ρ [dn i]) [dn i] [] [up i, up i] [up i, up i] f) =
      plcL RD k ρ [dn i] [dn i] [up i, up i] [up i, up i] f := by
  diag_induction f [plcL_diag] =>
    exact (pres RD k).diag_eq_of_layers_eq (by
      simp only [Diagram.layers_cast, Diagram.layers_whisker, List.map_map, Function.comp_def,
        Layer.whisker_whisker]
      rfl)

theorem plcL_plcL_dnR (f : End ((pres RD k).obj (ob RD (wt RD ρ [dn i]) [up i, up i]))) :
    plcL RD k ρ [dn i] [] [up i, up i, dn i] [up i, up i, dn i]
        (plcL RD k ρ [] [dn i] [up i, up i] [up i, up i] f) =
      plcL RD k ρ [dn i] [dn i] [up i, up i] [up i, up i] f := by
  diag_induction f [plcL_diag] =>
    exact (pres RD k).diag_eq_of_layers_eq (by
      simp only [Diagram.layers_cast, Diagram.layers_whisker, List.map_map, Function.comp_def,
        Layer.whisker_whisker]
      rfl)

end Nested

/-! ## Endomorphisms of `1_ρ` -/

section Closed

variable (ρ : X) (i : I)

/-- **`END(1_ρ)` is commutative** (interchange law). -/
theorem endEmpty_comm (β γ : End ((pres RD k).obj (ob RD ρ []))) : β ≫ γ = γ ≫ β := by
  diag_induction β [Preadditive.add_comp, Preadditive.comp_add, Linear.smul_comp, Linear.comp_smul,
      Limits.zero_comp, Limits.comp_zero] =>
    rename_i d _
    diag_induction γ [Preadditive.add_comp, Preadditive.comp_add, Linear.smul_comp,
        Linear.comp_smul, Limits.zero_comp, Limits.comp_zero] =>
      rename_i e _
      rw [← Presentation.diag_comp, ← Presentation.diag_comp]
      have hc : (ob RD ρ []).Composable (ob RD ρ []) := ⟨ob_wf RD _ _, rfl, ob_wf RD _ _⟩
      have key := (pres RD k).diag_interchange_of_composable (a := ob RD ρ []) (b := ob RD ρ [])
        (a' := ob RD ρ []) (b' := ob RD ρ []) d e hc
      rw [sign_even, one_smul] at key
      have he : Chain (ob RD ρ []) (Diagram.layers e) (ob RD ρ []) := Diagram.chain e
      have e₁ : ∀ L ∈ Diagram.layers d, L.wr (ob RD ρ []).word = L := by
        intro L _; simp [Layer.wr]
      have e₂ : ∀ L ∈ Diagram.layers e, L.wl (ob RD ρ []) = L := by
        intro L hL
        have := he.start_of_mem hL
        simp only [ob_start, wt_nil] at this
        simp only [Layer.wl, ob_start, ob_word, wt_nil, wd_nil, List.nil_append, ← this]
      refine ((pres RD k).diag_eq_of_layers_eq ?_).trans (key.trans
        ((pres RD k).diag_eq_of_layers_eq ?_))
      · simp only [Diagram.layers_comp, Diagram.layers_rwhisker, Diagram.layers_lwhisker,
          List.map_congr_left e₁, List.map_congr_left e₂, List.map_id']
      · simp only [Diagram.layers_comp, Diagram.layers_rwhisker, Diagram.layers_lwhisker,
          List.map_congr_left e₁, List.map_congr_left e₂, List.map_id']

/-- Transport of an endomorphism of `1_x` along an equality of weights `x = y`. -/
def wtTransport {x y : X} (h : x = y) (β : (pres RD k).obj (ob RD x []) ⟶ (pres RD k).obj (ob RD x [])) :
    (pres RD k).obj (ob RD y []) ⟶ (pres RD k).obj (ob RD y []) :=
  eqToHom (by rw [h]) ≫ β ≫ eqToHom (by rw [h])

theorem wtTransport_diag {x y : X} (h : x = y) (d : ob RD x [] ⟶ ob RD x []) :
    wtTransport RD k h ((pres RD k).diag d) =
      (pres RD k).diag (Diagram.cast d (by rw [h]) (by rw [h])) := by
  subst h; simp [wtTransport]

theorem wtTransport_ccwU {x y : X} (h : x = y) (i : I) (m : ℤ) :
    wtTransport RD k h (ccwU RD k x i m) = ccwU RD k y i m := by
  subst h; simp [wtTransport]

theorem wtTransport_add {x y : X} (h : x = y)
    (β γ : (pres RD k).obj (ob RD x []) ⟶ (pres RD k).obj (ob RD x [])) :
    wtTransport RD k h (β + γ) = wtTransport RD k h β + wtTransport RD k h γ := by
  subst h; simp [wtTransport]

theorem wtTransport_smul {x y : X} (h : x = y) (r : k)
    (β : (pres RD k).obj (ob RD x []) ⟶ (pres RD k).obj (ob RD x [])) :
    wtTransport RD k h (r • β) = r • wtTransport RD k h β := by
  subst h; simp [wtTransport]

theorem wtTransport_zero {x y : X} (h : x = y) :
    wtTransport RD k h (0 : (pres RD k).obj (ob RD x []) ⟶ (pres RD k).obj (ob RD x [])) = 0 := by
  subst h; simp [wtTransport]

/-- An endomorphism of `1` placed to the left of the strands of the cup `1 ⟶ E F` can be moved
below the cup. -/
theorem cupUp_plcL (β : End ((pres RD k).obj (ob RD (wt RD (wt RD ρ [dn i]) [up i]) []))) :
    dg RD k ρ [] [up i, dn i] [([], .cup (up i), [])] ≫ plcL RD k ρ [] [up i, dn i] [] [] β =
      wtTransport RD k (by simp : wt RD (wt RD ρ [dn i]) [up i] = ρ) β ≫
        dg RD k ρ [] [up i, dn i] [([], .cup (up i), [])] := by
  diag_induction β [wtTransport_add, wtTransport_smul, wtTransport_zero, Preadditive.add_comp, Preadditive.comp_add,
      Linear.smul_comp, Linear.comp_smul, Limits.zero_comp, Limits.comp_zero] =>
    rename_i d _
    rw [plcL_diag, wtTransport_diag, dg_of (by schain), ← Presentation.diag_comp, ← Presentation.diag_comp]
    have hc : (ob RD ρ []).Composable (ob RD ρ []) := ⟨ob_wf RD _ _, rfl, ob_wf RD _ _⟩
    have hρ : ob RD (wt RD (wt RD ρ [dn i]) [up i]) [] = ob RD ρ [] := by simp [ob]
    have key := (pres RD k).diag_interchange_of_composable (a := ob RD ρ []) (b := ob RD ρ [])
      (a' := ob RD ρ []) (b' := ob RD ρ [up i, dn i])
      (Diagram.cast (d : ob RD (wt RD (wt RD ρ [dn i]) [up i]) [] ⟶ _) hρ hρ)
      (mkD RD ρ [([], .cup (up i), [])] ⟨rfl, rfl⟩) hc
    rw [sign_even, one_smul] at key
    have hd : Chain (ob RD (wt RD (wt RD ρ [dn i]) [up i]) []) (Diagram.layers d)
        (ob RD (wt RD (wt RD ρ [dn i]) [up i]) []) := Diagram.chain d
    have e₁ : ∀ L ∈ Diagram.layers d, L.whisker (ob RD (wt RD (wt RD ρ [up i, dn i]) []) [])
        (wd RD ρ [up i, dn i]) = L.wr (ob RD ρ [up i, dn i]).word := by
      intro L hL
      have := hd.start_of_mem hL
      simp only [ob_start, wt_nil] at this
      simp only [Layer.whisker, Layer.wr, ob_start, ob_word, wt_nil, wd_nil, List.nil_append]
      rw [this]; rfl
    have e₂ : ∀ L ∈ Diagram.layers d, L.wr (ob RD ρ []).word = L := by
      intro L _; simp [Layer.wr]
    refine diag_transfer RD k (a' := (ob RD ρ []).tensor (ob RD ρ []))
      (b' := (ob RD ρ []).tensor (ob RD ρ [up i, dn i])) _ _ _ _ (Obj.ext rfl rfl)
      (Obj.ext (by simp [ob]) rfl) ?_ ?_ key.symm
    · simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_whisker,
        Diagram.layers_rwhisker, Diagram.layers_lwhisker, layers_mkD, List.map_congr_left e₁]
      rfl
    · simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_rwhisker,
        Diagram.layers_lwhisker, layers_mkD, List.map_congr_left e₂, List.map_id']
      rfl

/-- An endomorphism of `1_ρ` placed to the right of the strands of the cup `1 ⟶ F E` can be
moved below the cup. -/
theorem cupDn_plcL (γ : End ((pres RD k).obj (ob RD ρ []))) :
    dg RD k ρ [] [dn i, up i] [([], .cup (dn i), [])] ≫ plcL RD k ρ [dn i, up i] [] [] [] γ =
      γ ≫ dg RD k ρ [] [dn i, up i] [([], .cup (dn i), [])] := by
  diag_induction γ [Preadditive.add_comp, Preadditive.comp_add,
      Linear.smul_comp, Linear.comp_smul, Limits.zero_comp, Limits.comp_zero] =>
    rename_i d _
    rw [plcL_diag, dg_of (by schain), ← Presentation.diag_comp, ← Presentation.diag_comp]
    have hc : (ob RD ρ []).Composable (ob RD ρ []) := ⟨ob_wf RD _ _, rfl, ob_wf RD _ _⟩
    have key := (pres RD k).diag_interchange_of_composable (a := ob RD ρ [])
      (a' := ob RD ρ [dn i, up i]) (b := ob RD ρ []) (b' := ob RD ρ [])
      (mkD RD ρ [([], .cup (dn i), [])] ⟨rfl, rfl⟩) d hc
    rw [sign_even, one_smul] at key
    have hd : Chain (ob RD ρ []) (Diagram.layers d) (ob RD ρ []) := Diagram.chain d
    have e₁ : ∀ L ∈ Diagram.layers d, L.whisker (ob RD (wt RD (wt RD ρ []) []) [dn i, up i])
        (wd RD ρ []) = L.wl (ob RD ρ [dn i, up i]) := by
      intro L _
      simp [Layer.whisker, Layer.wl]
    have e₂ : ∀ L ∈ Diagram.layers d, L.wl (ob RD ρ []) = L := by
      intro L hL
      have := hd.start_of_mem hL
      simp only [ob_start, wt_nil] at this
      simp only [Layer.wl, ob_start, ob_word, wt_nil, wd_nil, List.nil_append, ← this]
    refine diag_transfer RD k (a' := (ob RD ρ []).tensor (ob RD ρ []))
      (b' := (ob RD ρ [dn i, up i]).tensor (ob RD ρ [])) _ _ _ _ (Obj.ext rfl rfl)
      (Obj.ext (by simp [ob]) (by simp [ob])) ?_ ?_ key
    · simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_whisker,
        Diagram.layers_rwhisker, Diagram.layers_lwhisker, layers_mkD, List.map_congr_left e₁]
      rfl
    · simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_rwhisker,
        Diagram.layers_lwhisker, layers_mkD, List.map_congr_left e₂, List.map_id']
      rfl

end Closed

/-! ## Closing a single strand -/

section Close

variable (ρ : X) (i : I)

/-- Closing an upward strand `E_i` (with the region `ρ - i_X` on its right) to the right: a
clockwise loop in the region `ρ`. -/
def closeRight : End ((pres RD k).obj (ob RD (wt RD ρ [dn i]) [up i])) →ₗ[k]
    End ((pres RD k).obj (ob RD ρ [])) where
  toFun g := dg RD k ρ [] [up i, dn i] [([], .cup (up i), [])] ≫
    plcL RD k ρ [] [dn i] [up i] [up i] g ≫ dg RD k ρ [up i, dn i] [] [([], .cap (dn i), [])]
  map_add' f g := by rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

/-- Closing an upward strand `E_i` (with the region `ρ` on its right) to the left: a
counterclockwise loop in the region `ρ`. -/
def closeLeft : End ((pres RD k).obj (ob RD ρ [up i])) →ₗ[k] End ((pres RD k).obj (ob RD ρ [])) where
  toFun g := dg RD k ρ [] [dn i, up i] [([], .cup (dn i), [])] ≫
    plcL RD k ρ [dn i] [] [up i] [up i] g ≫ dg RD k ρ [dn i, up i] [] [([], .cap (up i), [])]
  map_add' f g := by rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

theorem closeRight_apply (g : End ((pres RD k).obj (ob RD (wt RD ρ [dn i]) [up i]))) :
    closeRight RD k ρ i g = dg RD k ρ [] [up i, dn i] [([], .cup (up i), [])] ≫
      plcL RD k ρ [] [dn i] [up i] [up i] g ≫ dg RD k ρ [up i, dn i] [] [([], .cap (dn i), [])] :=
  rfl

theorem closeLeft_apply (g : End ((pres RD k).obj (ob RD ρ [up i]))) :
    closeLeft RD k ρ i g = dg RD k ρ [] [dn i, up i] [([], .cup (dn i), [])] ≫
      plcL RD k ρ [dn i] [] [up i] [up i] g ≫ dg RD k ρ [dn i, up i] [] [([], .cap (up i), [])] :=
  rfl

/-- The right closure of dots is a clockwise bubble. -/
theorem closeRight_dots (n : ℕ) : closeRight RD k ρ i (dotsU RD k (wt RD ρ [dn i]) (up i) n) = cwU RD k ρ i n := by
  rw [closeRight_apply, dotsU, plcL_dg, cwU_of_nonneg, cwLs, dg_cw_dots]
  show dg RD k ρ [] [up i, dn i] _ ≫ dg RD k ρ [up i, dn i] [up i, dn i] _ ≫
    dg RD k ρ [up i, dn i] [] _ = _
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  congr 1; lnf

/-- The left closure of dots is a counterclockwise bubble. -/
theorem closeLeft_dots (n : ℕ) : closeLeft RD k ρ i (dotsU RD k ρ (up i) n) = ccwU RD k ρ i n := by
  rw [closeLeft_apply, dotsU, plcL_dg_nil, ccwU_of_nonneg, ccwLs]
  show dg RD k ρ [] [dn i, up i] _ ≫ dg RD k ρ [dn i, up i] [dn i, up i] _ ≫
    dg RD k ρ [dn i, up i] [] _ = _
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  congr 1; lnf

/-- Closing to the right a strand with bubbles on its left: the bubbles come out (transported to
the region `ρ`). -/
theorem closeRight_bubLU (β : End ((pres RD k).obj (ob RD (wt RD (wt RD ρ [dn i]) [up i]) [])))
    (n : ℕ) :
    closeRight RD k ρ i (bubLU RD k (wt RD ρ [dn i]) (up i) β ≫ dotsU RD k (wt RD ρ [dn i]) (up i) n) =
      wtTransport RD k (by simp : wt RD (wt RD ρ [dn i]) [up i] = ρ) β ≫ cwU RD k ρ i n := by
  rw [closeRight_apply, ← plcL_comp RD k ρ [] [dn i] rfl rfl, plcL_bubLU_dn]
  simp only [← Category.assoc]
  rw [cupUp_plcL]
  simp only [Category.assoc]
  rw [← closeRight_dots, closeRight_apply]

/-- Closing to the left a strand with bubbles on its right: the bubbles come out. -/
theorem closeLeft_bubRU (γ : End ((pres RD k).obj (ob RD ρ []))) (n : ℕ) :
    closeLeft RD k ρ i (bubRU RD k ρ (up i) γ ≫ dotsU RD k ρ (up i) n) = γ ≫ ccwU RD k ρ i n := by
  rw [closeLeft_apply, ← plcL_comp RD k ρ [dn i] [] rfl rfl, plcL_bubRU_dn]
  simp only [← Category.assoc]
  rw [cupDn_plcL]
  simp only [Category.assoc]
  rw [← closeLeft_dots, closeLeft_apply]

/-- **The two closures of the figure eight agree** (interchange law): closing the left strand of
`f ∈ END(E_i E_i 1_{ρ-i_X})` and then the remaining strand to the right equals closing the right
strand and then the remaining strand to the left. -/
theorem closeRight_ptrL (f : End ((pres RD k).obj (ob RD (wt RD ρ [dn i]) [up i, up i]))) :
    closeRight RD k ρ i (ptrL RD k (wt RD ρ [dn i]) i f) = closeLeft RD k ρ i (ptrR RD k ρ i f) := by
  have h₁ : wt RD (wt RD ρ [dn i]) [dn i, up i, up i] = wt RD (wt RD ρ [dn i]) [up i] := by simp
  have h₂ : wt RD (wt RD ρ []) [up i, up i, dn i] = wt RD (wt RD ρ []) [up i] := by simp
  rw [closeRight_apply, ptrL_apply, ← plcL_comp RD k ρ [] [dn i] h₁ h₁.symm,
    ← plcL_comp RD k ρ [] [dn i] rfl h₁.symm, plcL_dg, plcL_plcL_dnL, plcL_dg,
    closeLeft_apply, ptrR_apply, ← plcL_comp RD k ρ [dn i] [] h₂ h₂.symm,
    ← plcL_comp RD k ρ [dn i] [] rfl h₂.symm, plcL_dg_nil, plcL_plcL_dnR, plcL_dg_nil]
  show dg RD k ρ [] [up i, dn i] _ ≫
      (dg RD k ρ [up i, dn i] [dn i, up i, up i, dn i] _ ≫
        plcL RD k ρ [dn i] [dn i] [up i, up i] [up i, up i] f ≫
          dg RD k ρ [dn i, up i, up i, dn i] [up i, dn i] _) ≫
      dg RD k ρ [up i, dn i] [] _ =
    dg RD k ρ [] [dn i, up i] _ ≫
      (dg RD k ρ [dn i, up i] [dn i, up i, up i, dn i] _ ≫
        plcL RD k ρ [dn i] [dn i] [up i, up i] [up i, up i] f ≫
          dg RD k ρ [dn i, up i, up i, dn i] [dn i, up i] _) ≫
      dg RD k ρ [dn i, up i] [] _
  simp only [Category.assoc]
  rw [← Category.assoc (dg RD k ρ [] [up i, dn i] _), dg_comp (by schain) (by schain),
    dg_comp (by schain) (by schain), ← Category.assoc (dg RD k ρ [] [dn i, up i] _),
    dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  have hcup : dg RD k ρ [] [dn i, up i, up i, dn i]
      [([], .cup (dn i), []), ([dn i, up i], .cup (up i), [])] =
      dg RD k ρ [] [dn i, up i, up i, dn i]
      [([], .cup (up i), []), ([], .cup (dn i), [up i, dn i])] :=
    dg_swap' RD k ρ [] [] [] (.cup (dn i)) (.cup (up i))
  have hcap : dg RD k ρ [dn i, up i, up i, dn i] []
      [([], .cap (up i), [up i, dn i]), ([], .cap (dn i), [])] =
      dg RD k ρ [dn i, up i, up i, dn i] []
      [([dn i, up i], .cap (dn i), []), ([], .cap (up i), [])] :=
    dg_swap' RD k ρ [] [] [] (.cap (up i)) (.cap (dn i))
  lnf
  rw [← hcup, hcap]

end Close

/-! ## Vanishing of bubbles of negative degree -/

theorem ccwU_eq_zero (ν : X) (i : I) (m : ℤ) (h : m + 1 + ip RD i ν < 0) : ccwU RD k ν i m = 0 := by
  by_cases hm : 0 ≤ m
  · obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [ccwU_of_nonneg, dg_ccwNeg RD k ν i m' (by omega)]
  · rw [ccwU, ccwL, if_neg hm, if_neg (by omega), Presentation.lin_zero]

theorem cwU_eq_zero (ν : X) (i : I) (m : ℤ) (h : m + 1 - ip RD i ν < 0) : cwU RD k ν i m = 0 := by
  by_cases hm : 0 ≤ m
  · obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [cwU_of_nonneg, dg_cwNeg RD k ν i m' (by omega)]
  · rw [cwU, cwL, if_neg hm, if_neg (by omega), Presentation.lin_zero]

/-! ## A reindexing identity -/

theorem sum_split_reflect {M : Type*} [AddCommMonoid M] (G : ℤ → M) (d : ℕ)
    (hG : ∀ j : ℤ, j < 0 ∨ (d : ℤ) < j → G j = 0) (c : ℤ) :
    ∑ j ∈ Finset.range c.toNat, G j + ∑ ℓ ∈ Finset.range ((d : ℤ) + 1 - c).toNat, G (d - ℓ) =
      ∑ j ∈ Finset.range (d + 1), G j := by
  set S : ℤ → M := fun c => ∑ j ∈ Finset.range c.toNat, G j +
    ∑ ℓ ∈ Finset.range ((d : ℤ) + 1 - c).toNat, G (d - ℓ) with hS
  have step : ∀ c : ℤ, S (c + 1) = S c := by
    intro c
    simp only [hS]
    by_cases hc : 0 ≤ c
    · rw [show (c + 1).toNat = c.toNat + 1 by omega, Finset.sum_range_succ,
        show ((c.toNat : ℕ) : ℤ) = c by omega]
      by_cases hcd : c ≤ d
      · rw [show ((d : ℤ) + 1 - c).toNat = ((d : ℤ) + 1 - (c + 1)).toNat + 1 by omega,
          Finset.sum_range_succ (fun ℓ => G (d - ℓ)),
          show ((d : ℤ) - (((d : ℤ) + 1 - (c + 1)).toNat : ℕ)) = c by omega]
        abel
      · rw [hG c (Or.inr (by omega)), add_zero,
          show ((d : ℤ) + 1 - c).toNat = ((d : ℤ) + 1 - (c + 1)).toNat by omega]
    · rw [show (c + 1).toNat = c.toNat by omega,
        show ((d : ℤ) + 1 - c).toNat = ((d : ℤ) + 1 - (c + 1)).toNat + 1 by omega,
        Finset.sum_range_succ (fun ℓ => G (d - ℓ)),
        show ((d : ℤ) - (((d : ℤ) + 1 - (c + 1)).toNat : ℕ)) = c by omega,
        hG c (Or.inl (by omega)), add_zero]
  have hconst : ∀ c : ℤ, S c = S 0 := by
    intro c
    induction c using Int.induction_on with
    | hz => rfl
    | hp n ih => rw [step, ih]
    | hn n ih => rw [← ih, ← step]; ring_nf
  show S c = _
  rw [hconst c]
  simp only [hS, Int.toNat_zero, Finset.range_zero, Finset.sum_empty, zero_add, sub_zero]
  rw [show ((d : ℤ) + 1).toNat = d + 1 by omega]
  rw [← Finset.sum_range_reflect (fun j : ℕ => G j) (d + 1)]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have := Finset.mem_range.1 hℓ
  congr 1
  omega

/-! ## The infinite Grassmannian relation -/

/-- **The infinite Grassmannian relation in all degrees** (KL III Definition 3.1,
`eq_infinite_Grass`, "remains valid even in high degree"; Lauda, Proposition 5.5): for every
region `ρ` (with `n = ⟨i, ρ⟩`) and every degree `d ≥ 1`,
`∑_{j=0}^{d} ccw_{-n-1+j} cw_{n-1+d-j} = 0`, where the bubbles are real or fake (`ccwL`, `cwL`).
For `d ≤ n` resp. `d ≤ -n` this is the definition of the fake bubbles; for larger `d` it is a
consequence of the defining relations of `U`, proved here by evaluating the figure-eight diagram
(the crossing of `E_i E_i` with both strands closed, `d - 1` dots on one loop) with the left and
with the right curl relation. -/
theorem grassmannian (ρ : X) (i : I) (d : ℕ) (hd : 1 ≤ d) :
    ∑ j ∈ Finset.range (d + 1),
      ccwU RD k ρ i (-ip RD i ρ - 1 + j) ≫ cwU RD k ρ i (ip RD i ρ - 1 + (d - j)) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have key := closeRight_ptrL RD k ρ i (nhDotR RD k (wt RD ρ [dn i]) i m ≫ nhCross RD k (wt RD ρ [dn i]) i)
  rw [ptrL_nhDotR_comp, ptrL_nhCross, ptrR_nhDotR_nhCross, Preadditive.comp_sum, map_sum, map_neg, map_sum] at key
  have hN : ip RD i (wt RD (wt RD ρ [dn i]) [up i]) = ip RD i ρ := by simp
  have hA : ∀ g ∈ Finset.range (ip RD i (wt RD (wt RD ρ [dn i]) [up i]) + 1).toNat,
      closeRight RD k ρ i (dotsU RD k (wt RD ρ [dn i]) (up i) m ≫
        bubLU RD k (wt RD ρ [dn i]) (up i) (ccwU RD k (wt RD (wt RD ρ [dn i]) [up i]) i
          (-ip RD i (wt RD (wt RD ρ [dn i]) [up i]) - 1 + g)) ≫
        dotsU RD k (wt RD ρ [dn i]) (up i) (ip RD i (wt RD (wt RD ρ [dn i]) [up i]) - g).toNat) =
      ccwU RD k ρ i (-ip RD i ρ - 1 + g) ≫ cwU RD k ρ i (ip RD i ρ - 1 + ((↑(m + 1) : ℤ) - g)) := by
    intro g hg
    have hg' := Finset.mem_range.1 hg
    rw [← Category.assoc, ← bubLU_comm, Category.assoc, dotsU_add, closeRight_bubLU, wtTransport_ccwU, hN]
    congr 2
    rw [hN] at hg'
    push_cast; omega
  have hB : ∀ ℓ ∈ Finset.range ((m : ℤ) + -ip RD i ρ + 1).toNat,
      closeLeft RD k ρ i (bubRU RD k ρ (up i) (cwU RD k ρ i (ip RD i ρ - 1 + ℓ)) ≫
        dotsU RD k ρ (up i) ((m : ℤ) + -ip RD i ρ - ℓ).toNat) =
      ccwU RD k ρ i (-ip RD i ρ - 1 + ((↑(m + 1) : ℤ) - ℓ)) ≫
        cwU RD k ρ i (ip RD i ρ - 1 + ((↑(m + 1) : ℤ) - ((↑(m + 1) : ℤ) - ℓ))) := by
    intro ℓ hℓ
    have hℓ' := Finset.mem_range.1 hℓ
    rw [closeLeft_bubRU, endEmpty_comm]
    congr 2
    · push_cast; omega
    · ring
  rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB, hN, eq_neg_iff_add_eq_zero] at key
  have := sum_split_reflect (fun j : ℤ => ccwU RD k ρ i (-ip RD i ρ - 1 + j) ≫
    cwU RD k ρ i (ip RD i ρ - 1 + ((↑(m + 1) : ℤ) - j))) (m + 1) ?_ (ip RD i ρ + 1)
  · rw [show ((↑(m + 1) : ℤ) + 1 - (ip RD i ρ + 1)).toNat = ((m : ℤ) + -ip RD i ρ + 1).toNat by
      push_cast; omega, key] at this
    exact this.symm
  · intro j hj
    dsimp only
    rcases hj with hj | hj
    · rw [ccwU_eq_zero RD k ρ i _ (by omega), Limits.zero_comp]
    · rw [cwU_eq_zero RD k ρ i _ (by push_cast at hj ⊢; omega), Limits.comp_zero]

end Categorification.KL3.Diagram
