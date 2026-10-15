/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqFakeBubbles
import Categorification.TwoRep.RouqMixedDownup
import Categorification.TwoRep.RouqCurl

/-!
# Actual CL decomposition relations from ungraded Rouquier data

The original `genImg` sends both actual CL EF and FE decompositions to zero when the local
unit parameter satisfies `r_i = 1`. The finite triangular sum is compared term by
term with Brundan's inverse-component expansion; its empty cases are included.

Sources: Cautis–Lauda, arXiv:1111.1431v3, the extended sl₂ double-crossing
decomposition displays; Brundan, arXiv:1501.00350v1, Corollary 3.4, (3.16)–(3.17).
The bubble orientation dictionary reverses the local names `cw` and `ccw`.
No grading, Hom-finiteness, scalar endomorphism ring, or presentation relation is
assumed. This verifies the two decomposition constructors, not all upward KLR
constructors or the horizontally generated presentation ideal. Normalized `presNM`
soundness/descent and arbitrary-scalar rescaling remain separate.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
universe w v u u₁
variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [AdditiveWhiskering B]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y}
namespace RouqFamily
variable (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)
attribute [local irreducible] KL3.Diagram.sh

private theorem decomp_dotUp (i : I) (μ : X) :
    (S.interp Sc μ μ).map
      (ObjectProperty.homMk (X := bubbleUD i μ) (Y := bubbleUD i μ)
        (mkD RD μ [([], .dot (up i), [dn i])] ⟨rfl, rfl⟩)) =
      S.F i (cross_dn_reg i μ) ◁ S.dot i (cross_dn_reg i μ) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, bubbleUD, mkD, Diagram.layers_mk,
    layList_cons, layList_nil, lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil,
    List.nil_append, List.cons_append, Shape.dom]
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  erw [eqToHom_word ?w0 _]
  · unfold coreC core
    refine (chain1_key S.model (whiskerLeftIso _ (ρ_ _)) (whiskerLeftIso _ (ρ_ _))
      _ _ _ _ _ (eqToHom ?e) (eqToHom ?e')).trans ?main
    case main =>
      erw [layerAt_right, lift_map₂_eqToHom,
        eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    case e => rfl
    case e' => rfl
  case w0 => rfl

private theorem decomp_dotDn (i : I) (μ : X) :
    (S.interp Sc μ μ).map
      (ObjectProperty.homMk (X := bubbleDU i μ) (Y := bubbleDU i μ)
        (mkD RD μ [([], .dot (dn i), [up i])] ⟨rfl, rfl⟩)) =
      S.E i (cross_up_reg i μ) ◁ S.dotDn i (cross_up_reg i μ) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, bubbleDU, mkD, Diagram.layers_mk,
    layList_cons, layList_nil, lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil,
    List.nil_append, List.cons_append, Shape.dom]
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  erw [eqToHom_word ?w0 _]
  · unfold coreC core
    refine (chain1_key S.model (whiskerLeftIso _ (ρ_ _)) (whiskerLeftIso _ (ρ_ _))
      _ _ _ _ _ (eqToHom ?e) (eqToHom ?e')).trans ?main
    case main =>
      erw [layerAt_right, lift_map₂_eqToHom,
        eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    case e => rfl
    case e' => rfl
  case w0 => rfl

private theorem decomp_dotCapEF (i : I) (μ : X) (n : ℕ) :
    (S.interp Sc μ μ).map
      (ObjectProperty.homMk (X := bubbleUD i μ) (Y := bubbleNil μ)
        (dotCapEF RD μ i n)) =
      (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).capD n := by
  have hd : dotCapEF RD μ i n = dots RD μ [] (up i) [dn i] n ≫
      mkD RD μ [([], .cap (dn i), [])] ⟨rfl, rfl⟩ := by
    unfold dotCapEF dots
    erw [mkD_comp]
    rfl
  rw [hd]
  change (S.interp Sc μ μ).map
    ((ObjectProperty.homMk (X := bubbleUD i μ) (Y := bubbleUD i μ)
      (dots RD μ [] (up i) [dn i] n)) ≫
      ObjectProperty.homMk (X := bubbleUD i μ) (Y := bubbleNil μ)
        (mkD RD μ [([], .cap (dn i), [])] ⟨rfl, rfl⟩)) = _
  erw [Functor.map_comp, bubble_dots, decomp_dotUp, bubble_capDn,
    ← whiskerLeft_powComp]
  rfl

private theorem decomp_cupDotFE (i : I) (μ : X) (n : ℕ) :
    (S.interp Sc μ μ).map
      (ObjectProperty.homMk (X := bubbleNil μ) (Y := bubbleDU i μ)
        (cupDotFE RD μ i n)) =
      (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).cupD n := by
  have hd : cupDotFE RD μ i n =
      mkD RD μ [([], .cup (dn i), [])] ⟨rfl, rfl⟩ ≫ dots RD μ [dn i] (up i) [] n := by
    unfold cupDotFE dots
    erw [mkD_comp]
    rfl
  rw [hd]
  change (S.interp Sc μ μ).map
    ((ObjectProperty.homMk (X := bubbleNil μ) (Y := bubbleDU i μ)
      (mkD RD μ [([], .cup (dn i), [])] ⟨rfl, rfl⟩)) ≫
      ObjectProperty.homMk (X := bubbleDU i μ) (Y := bubbleDU i μ)
        (dots RD μ [dn i] (up i) [] n)) = _
  erw [Functor.map_comp, bubble_dots, bubble_dotUp, bubble_cupDn,
    ← powComp_whiskerRight]
  rfl

private theorem decomp_cupDotEF (i : I) (μ : X) (n : ℕ) :
    (S.interp Sc μ μ).map
      (ObjectProperty.homMk (X := bubbleNil μ) (Y := bubbleUD i μ)
        (cupDotEF RD μ i n)) =
      (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).cupL ≫
        S.F i (cross_dn_reg i μ) ◁ powComp (S.dot i (cross_dn_reg i μ)) n := by
  have hd : cupDotEF RD μ i n =
      mkD RD μ [([], .cup (up i), [])] ⟨rfl, rfl⟩ ≫ dots RD μ [up i] (dn i) [] n := by
    unfold cupDotEF dots
    erw [mkD_comp]
    rfl
  rw [hd]
  change (S.interp Sc μ μ).map
    ((ObjectProperty.homMk (X := bubbleNil μ) (Y := bubbleUD i μ)
      (mkD RD μ [([], .cup (up i), [])] ⟨rfl, rfl⟩)) ≫
      ObjectProperty.homMk (X := bubbleUD i μ) (Y := bubbleUD i μ)
        (dots RD μ [up i] (dn i) [] n)) = _
  erw [Functor.map_comp, bubble_dots, bubble_dotDn, bubble_cupUp,
    ← powComp_whiskerRight]
  erw [dotDn, ← StrongSl2.conjugateEquiv_symm_powComp,
    ← unit_whiskerLeft_conjugateEquiv, Equiv.apply_symm_apply]
  rw [S.adjL_unit i (cross_dn_reg i μ) (cross_up_reg i μ)]

private theorem decomp_dotCapFE (i : I) (μ : X) (n : ℕ) :
    (S.interp Sc μ μ).map
      (ObjectProperty.homMk (X := bubbleDU i μ) (Y := bubbleNil μ)
        (dotCapFE RD μ i n)) =
      powComp (S.dot i (cross_up_reg i μ)) n ▷ S.F i (cross_up_reg i μ) ≫
        (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).capL := by
  have hd : dotCapFE RD μ i n = dots RD μ [] (dn i) [up i] n ≫
      mkD RD μ [([], .cap (up i), [])] ⟨rfl, rfl⟩ := by
    unfold dotCapFE dots
    erw [mkD_comp]
    rfl
  rw [hd]
  change (S.interp Sc μ μ).map
    ((ObjectProperty.homMk (X := bubbleDU i μ) (Y := bubbleDU i μ)
      (dots RD μ [] (dn i) [up i] n)) ≫
      ObjectProperty.homMk (X := bubbleDU i μ) (Y := bubbleNil μ)
        (mkD RD μ [([], .cap (up i), [])] ⟨rfl, rfl⟩)) = _
  erw [Functor.map_comp, bubble_dots, decomp_dotDn, bubble_capUp,
    ← whiskerLeft_powComp]
  erw [dotDn, ← StrongSl2.conjugateEquiv_symm_powComp,
    ← conjugateEquiv_whiskerRight_counit, Equiv.apply_symm_apply]
  rw [S.adjL_counit i (cross_dn_reg i μ) (cross_up_reg i μ)]

/-- The inverse sideways crossing is the partial mate under the derived left adjunctions. -/
theorem mate_sigL (i : I) {a b c : X} (h₁ : a + RD.iX i = b)
    (h₂ : b + RD.iX i = c) :
    (mateEquiv (S.adjL i h₁) (S.adjL i h₂)).symm (S.cross i i h₁ h₂ h₁ h₂) =
      (S.loc i h₁ h₂).sigL := by
  apply (mateEquiv (S.adjL i h₁) (S.adjL i h₂)).injective
  rw [Equiv.apply_symm_apply]
  symm
  rw [S.adjL_eq i (sub_add_cancel a (RD.iX i)) h₁ h₂,
    S.adjL_eq i h₁ h₂ (rfl : c + RD.iX i = c + RD.iX i)]
  exact (S.loc i (sub_add_cancel a (RD.iX i)) h₁).mate_sigL
    (S.loc i h₁ h₂) (S.loc i h₂ rfl) (pair_step i h₁) (pair_step i h₂)
    (S.square i _ h₁) (S.square i h₁ h₂) (S.square i h₂ rfl)
    (S.braid i _ h₁ h₂) (S.braid i h₁ h₂ rfl)

private theorem decomp_crossl_at (i : I) (μ : X) {ν : X}
    (e : sh RD (up i) + (sh RD (dn i) + μ) = ν)
    (ha : Cond (S := psig RD) ν μ (ob RD μ [up i, dn i]))
    (hb : Cond (S := psig RD) ν μ (ob RD μ [dn i, up i])) :
    (S.interp Sc ν μ).map (ObjectProperty.homMk (X := ⟨_, ha⟩)
      (Y := ⟨_, hb⟩) (crossl RD i i μ)) =
      S.mixedSigma i i ((cross_up_reg i (sh RD (dn i) + μ)).trans e)
        (by rw [← e, sh_up, sh_dn]; abel) (cross_dn_reg i μ) (cross_up_reg i μ) := by
  subst ν
  exact S.mixed_crossl Sc i i μ

private theorem decomp_crossr_at (i : I) (μ : X) {ν : X}
    (e : sh RD (up i) + (sh RD (dn i) + μ) = ν)
    (ha : Cond (S := psig RD) ν μ (ob RD μ [dn i, up i]))
    (hb : Cond (S := psig RD) ν μ (ob RD μ [up i, dn i])) :
    (S.interp Sc ν μ).map (ObjectProperty.homMk (X := ⟨_, ha⟩)
      (Y := ⟨_, hb⟩) (crossr RD i i μ)) =
      (mateEquiv (S.adjL i (cross_dn_reg i μ))
        (S.adjL i (by rw [← e, sh_up, sh_dn]; abel))).symm
        (S.cross i i (cross_dn_reg i μ) (cross_up_reg i μ)
          ((cross_up_reg i (sh RD (dn i) + μ)).trans e)
          (by rw [← e, sh_up, sh_dn]; abel)) := by
  subst ν
  exact S.mixed_crossr_mate Sc i i μ

private theorem decomp_crossl (i : I) (μ : X) :
    (S.interp Sc μ μ).map (ObjectProperty.homMk
      (X := bubbleUD i μ) (Y := bubbleDU i μ) (crossl RD i i μ)) =
      (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).sig := by
  exact (S.decomp_crossl_at Sc i μ (sh_up_add_sh_dn i μ) _ _).trans
    (S.mixedSigma_self i _ _)

private theorem decomp_crossr (i : I) (μ : X) :
    (S.interp Sc μ μ).map (ObjectProperty.homMk
      (X := bubbleDU i μ) (Y := bubbleUD i μ) (crossr RD i i μ)) =
      (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).sigL := by
  exact (S.decomp_crossr_at Sc i μ (sh_up_add_sh_dn i μ) _ _).trans (S.mate_sigL i _ _)

private theorem decompEFSum_map (i : I) (μ : X) :
    admissibleMap (S.genImg Sc) (bubbleUD i μ).property (bubbleUD i μ).property
      (decompEFSum RD k i μ) =
      ∑ f ∈ Finset.range (ip RD i μ).toNat, ∑ g ∈ Finset.range (f + 1),
        (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).capD (f - g) ≫
          (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).cw (-ip RD i μ - 1 + g) ≫
          ((S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).cupL ≫
            S.F i (cross_dn_reg i μ) ◁
              powComp (S.dot i (cross_dn_reg i μ)) ((ip RD i μ).toNat - 1 - f)) := by
  unfold decompEFSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g _
  erw [admissibleMap_comp (S.genImg Sc) (bubbleUD i μ).property
      (bubbleNil μ).property (bubbleUD i μ).property,
    admissibleMap_comp (S.genImg Sc) (bubbleNil μ).property
      (bubbleNil μ).property (bubbleUD i μ).property,
    admissibleMap_of, admissibleMap_of]
  change (S.interp Sc μ μ).map (ObjectProperty.homMk (X := bubbleUD i μ)
      (Y := bubbleNil μ) (dotCapEF RD μ i (f - g))) ≫
      S.bubbleHom Sc μ (ccwL RD k μ i (-ip RD i μ - 1 + g)) ≫
      (S.interp Sc μ μ).map (ObjectProperty.homMk (X := bubbleNil μ)
        (Y := bubbleUD i μ) (cupDotEF RD μ i ((ip RD i μ).toNat - 1 - f))) = _
  erw [decomp_dotCapEF, decomp_cupDotEF,
    S.bubble_ccwL Sc i (cross_dn_reg i μ) (cross_up_reg i μ)]
  rfl

private theorem decomp_triangle {A : Type*} [AddCommMonoid A] (N : ℕ) (F : ℕ → ℕ → ℕ → A) :
    (∑ f ∈ Finset.range N, ∑ g ∈ Finset.range (f + 1), F (f - g) (N - 1 - f) g) =
      ∑ n ∈ Finset.range N, ∑ r ∈ Finset.range (N - n), F n r (N - 1 - n - r) := by
  rw [← Finset.sum_range_reflect]
  calc
    _ = ∑ r ∈ Finset.range N, ∑ n ∈ Finset.range (N - r), F n r (N - 1 - n - r) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_range] at hr
      rw [show N - 1 - r + 1 = N - r by omega,
        show N - 1 - (N - 1 - r) = r by omega, ← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_range] at hn
      congr 1 <;> omega
    _ = _ := Finset.sum_comm' (fun r n => by simp only [Finset.mem_range]; omega)

private theorem decompEF_local (i : I) (μ : X) :
    𝟙 (S.F i (cross_dn_reg i μ) ≫ S.E i (cross_dn_reg i μ)) +
      (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).sig ≫
        (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).sigL -
      ∑ f ∈ Finset.range (ip RD i μ).toNat, ∑ g ∈ Finset.range (f + 1),
        (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).capD (f - g) ≫
          (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).cw (-ip RD i μ - 1 + g) ≫
          ((S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).cupL ≫
            S.F i (cross_dn_reg i μ) ◁
              powComp (S.dot i (cross_dn_reg i μ)) ((ip RD i μ).toNat - 1 - f)) = 0 := by
  let L := S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)
  have hs : ∑ f ∈ Finset.range (ip RD i μ).toNat, ∑ g ∈ Finset.range (f + 1),
      L.capD (f - g) ≫ L.cw (-ip RD i μ - 1 + g) ≫
        (L.cupL ≫ S.F i (cross_dn_reg i μ) ◁
          powComp (S.dot i (cross_dn_reg i μ)) ((ip RD i μ).toNat - 1 - f)) =
      ∑ n ∈ Finset.range (ip RD i μ).toNat, ∑ r ∈ Finset.range ((ip RD i μ).toNat - n),
        L.capD n ≫ L.cw (-(n : ℤ) - r - 2) ≫
          L.cupL ≫ S.F i (cross_dn_reg i μ) ◁ powComp (S.dot i (cross_dn_reg i μ)) r := by
    rw [decomp_triangle (ip RD i μ).toNat (fun n r g =>
      L.capD n ≫ L.cw (-ip RD i μ - 1 + g) ≫ L.cupL ≫
        S.F i (cross_dn_reg i μ) ◁ powComp (S.dot i (cross_dn_reg i μ)) r)]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro r hr
    have hn' := Finset.mem_range.mp hn
    have hr' := Finset.mem_range.mp hr
    rw [show -ip RD i μ - 1 + (((ip RD i μ).toNat - 1 - n - r : ℕ) : ℤ) =
      -(n : ℤ) - r - 2 by omega]
  change 𝟙 _ + L.sig ≫ L.sigL - _ = 0
  rw [hs, L.decompEF]
  abel

/-- The actual CL EF decomposition relation vanishes at every weight for `r_i = 1`. -/
theorem decompEF_rel (i : I) (μ : X) (hr : Sc.r i = 1) :
    admissibleMap (S.genImg Sc) (bubbleUD i μ).property (bubbleUD i μ).property
      (CL.relationCL RD k Sc (.decompEF i μ)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _
    (LinDiagram.of (𝟙 (ob RD μ [up i, dn i])) +
      (((Sc.r i)⁻¹ : kˣ) : k) ^ 2 • LinDiagram.of (crossl RD i i μ ≫ crossr RD i i μ) -
        decompEFSum RD k i μ) = 0
  rw [map_sub, map_add, map_smul, hr]
  simp only [inv_one, Units.val_one, one_pow, one_smul]
  have hid : admissibleMap (S.genImg Sc) (bubbleUD i μ).property (bubbleUD i μ).property
      (LinDiagram.of (𝟙 _) : LinDiagram k _ _) = 𝟙 _ := by
    erw [admissibleMap_of]
    exact (S.interp Sc μ μ).map_id _
  have hc : admissibleMap (S.genImg Sc) (bubbleUD i μ).property (bubbleUD i μ).property
      (LinDiagram.of (crossl RD i i μ ≫ crossr RD i i μ) : LinDiagram k _ _) =
      (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).sig ≫
        (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).sigL := by
    erw [admissibleMap_of]
    change (S.interp Sc μ μ).map
      ((ObjectProperty.homMk (X := bubbleUD i μ) (Y := bubbleDU i μ) (crossl RD i i μ)) ≫
        ObjectProperty.homMk (X := bubbleDU i μ) (Y := bubbleUD i μ) (crossr RD i i μ)) = _
    erw [Functor.map_comp, decomp_crossl, decomp_crossr]
    rfl
  rw [hid, decompEFSum_map, hc]
  exact S.decompEF_local i μ

private theorem decompFESum_map (i : I) (μ : X) :
    admissibleMap (S.genImg Sc) (bubbleDU i μ).property (bubbleDU i μ).property
      (decompFESum RD k i μ) =
      ∑ f ∈ Finset.range (-ip RD i μ).toNat, ∑ g ∈ Finset.range (f + 1),
        (powComp (S.dot i (cross_up_reg i μ)) (f - g) ▷ S.F i (cross_up_reg i μ) ≫
          (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).capL) ≫
          (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).ccw (ip RD i μ - 1 + g) ≫
          (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).cupD ((-ip RD i μ).toNat - 1 - f) := by
  unfold decompFESum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g _
  erw [admissibleMap_comp (S.genImg Sc) (bubbleDU i μ).property
      (bubbleNil μ).property (bubbleDU i μ).property,
    admissibleMap_comp (S.genImg Sc) (bubbleNil μ).property
      (bubbleNil μ).property (bubbleDU i μ).property,
    admissibleMap_of, admissibleMap_of]
  change (S.interp Sc μ μ).map (ObjectProperty.homMk (X := bubbleDU i μ)
      (Y := bubbleNil μ) (dotCapFE RD μ i (f - g))) ≫
      S.bubbleHom Sc μ (cwL RD k μ i (ip RD i μ - 1 + g)) ≫
      (S.interp Sc μ μ).map (ObjectProperty.homMk (X := bubbleNil μ)
        (Y := bubbleDU i μ) (cupDotFE RD μ i ((-ip RD i μ).toNat - 1 - f))) = _
  erw [decomp_dotCapFE, decomp_cupDotFE,
    S.bubble_cwL Sc i (cross_dn_reg i μ) (cross_up_reg i μ)]
  rfl

private theorem decompFE_local (i : I) (μ : X) :
    𝟙 (S.E i (cross_up_reg i μ) ≫ S.F i (cross_up_reg i μ)) +
      (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).sigL ≫
        (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).sig -
      ∑ f ∈ Finset.range (-ip RD i μ).toNat, ∑ g ∈ Finset.range (f + 1),
        (powComp (S.dot i (cross_up_reg i μ)) (f - g) ▷ S.F i (cross_up_reg i μ) ≫
          (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).capL) ≫
          (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).ccw (ip RD i μ - 1 + g) ≫
          (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).cupD ((-ip RD i μ).toNat - 1 - f) = 0 := by
  let L := S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)
  have hs : ∑ f ∈ Finset.range (-ip RD i μ).toNat, ∑ g ∈ Finset.range (f + 1),
      (powComp (S.dot i (cross_up_reg i μ)) (f - g) ▷ S.F i (cross_up_reg i μ) ≫ L.capL) ≫
        L.ccw (ip RD i μ - 1 + g) ≫ L.cupD ((-ip RD i μ).toNat - 1 - f) =
      ∑ n ∈ Finset.range (-ip RD i μ).toNat, ∑ r ∈ Finset.range ((-ip RD i μ).toNat - n),
        powComp (S.dot i (cross_up_reg i μ)) r ▷ S.F i (cross_up_reg i μ) ≫
          L.capL ≫ L.ccw (-(n : ℤ) - r - 2) ≫ L.cupD n := by
    rw [decomp_triangle (-ip RD i μ).toNat (fun r n g =>
      (powComp (S.dot i (cross_up_reg i μ)) r ▷ S.F i (cross_up_reg i μ) ≫ L.capL) ≫
        L.ccw (ip RD i μ - 1 + g) ≫ L.cupD n)]
    rw [Finset.sum_comm' (s := Finset.range (-ip RD i μ).toNat)
      (t' := Finset.range (-ip RD i μ).toNat)
      (s' := fun n => Finset.range ((-ip RD i μ).toNat - n))
      (fun r n => by simp only [Finset.mem_range]; omega)]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro r hr
    have hn' := Finset.mem_range.mp hn
    have hr' := Finset.mem_range.mp hr
    rw [show ip RD i μ - 1 + (((-ip RD i μ).toNat - 1 - r - n : ℕ) : ℤ) =
      -(n : ℤ) - r - 2 by omega, Category.assoc]
  change 𝟙 _ + L.sigL ≫ L.sig - _ = 0
  rw [hs, L.decompFE]
  abel

/-- The actual CL FE decomposition relation vanishes at every weight for `r_i = 1`. -/
theorem decompFE_rel (i : I) (μ : X) (hr : Sc.r i = 1) :
    admissibleMap (S.genImg Sc) (bubbleDU i μ).property (bubbleDU i μ).property
      (CL.relationCL RD k Sc (.decompFE i μ)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _
    (LinDiagram.of (𝟙 (ob RD μ [dn i, up i])) +
      (((Sc.r i)⁻¹ : kˣ) : k) ^ 2 • LinDiagram.of (crossr RD i i μ ≫ crossl RD i i μ) -
        decompFESum RD k i μ) = 0
  rw [map_sub, map_add, map_smul, hr]
  simp only [inv_one, Units.val_one, one_pow, one_smul]
  have hid : admissibleMap (S.genImg Sc) (bubbleDU i μ).property (bubbleDU i μ).property
      (LinDiagram.of (𝟙 _) : LinDiagram k _ _) = 𝟙 _ := by
    erw [admissibleMap_of]
    exact (S.interp Sc μ μ).map_id _
  have hc : admissibleMap (S.genImg Sc) (bubbleDU i μ).property (bubbleDU i μ).property
      (LinDiagram.of (crossr RD i i μ ≫ crossl RD i i μ) : LinDiagram k _ _) =
      (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).sigL ≫
        (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).sig := by
    erw [admissibleMap_of]
    change (S.interp Sc μ μ).map
      ((ObjectProperty.homMk (X := bubbleDU i μ) (Y := bubbleUD i μ) (crossr RD i i μ)) ≫
        ObjectProperty.homMk (X := bubbleUD i μ) (Y := bubbleDU i μ) (crossl RD i i μ)) = _
    erw [Functor.map_comp, decomp_crossr, decomp_crossl]
    rfl
  rw [hid, decompFESum_map, hc]
  exact S.decompFE_local i μ

end RouqFamily
end Categorification.TwoRep
