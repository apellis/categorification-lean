/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftRelDecompEF
import Categorification.Diagrams.KL3.SidewaysDotSlide

/-!
# The right curl closed by a cap, under the weight shift of `U′`

Part of the proof that the weight shift of `U′` respects the decomposition relation of
`F_i E_i` (Webster arXiv:1309.3796v2, Proposition 3.30). This mirrors
`LocalizationShiftCurlCap`, with `crossr` and the downward cap.

## Main results

* `dg_crossr_capDn`: `crossr_{ii} ≫ cap` in `U`, from the right curl relation of KL III.
* `dg_crossr_dotE`: an upward dot below `crossr_{ii}` slides through it up to `cap ≫ cup`.
* `KLzR_eq`: `crossr ≫ (F-dot)^c ≫ cap` in `U′` is the image of the explicit sum
  `curlCapFE c`, for every `c ∈ ℤ`.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

variable (ρ : X) (i : I)


theorem plcL_capUp_right (γ : End ((pres RD k).obj (ob RD ρ []))) :
    plcL RD k ρ [dn i, up i] [] [] [] γ ≫ dg RD k ρ [dn i, up i] [] [([], .cap (up i), [])] =
      dg RD k ρ [dn i, up i] [] [([], .cap (up i), [])] ≫ γ := by
  diag_induction γ [Preadditive.add_comp, Preadditive.comp_add, Linear.smul_comp,
      Linear.comp_smul, Limits.zero_comp, Limits.comp_zero] =>
    rename_i d _
    rw [plcL_diag, dg_of (by schain), ← Presentation.diag_comp, ← Presentation.diag_comp]
    have hc : (ob RD ρ [dn i, up i]).Composable (ob RD ρ []) :=
      ⟨ob_wf RD _ _, rfl, ob_wf RD _ _⟩
    have key := (pres RD k).diag_interchange_of_composable
      (a := ob RD ρ [dn i, up i]) (a' := ob RD ρ [])
      (b := ob RD ρ []) (b' := ob RD ρ [])
      (mkD RD ρ [([], .cap (up i), [])] ⟨rfl, rfl⟩) d hc
    rw [sign_even, one_smul] at key
    refine diag_transfer RD k
      (a' := (ob RD ρ [dn i, up i]).tensor (ob RD ρ []))
      (b' := (ob RD ρ []).tensor (ob RD ρ [])) _ _ _ _ (Obj.ext ?_ ?_)
      (Obj.ext ?_ ?_) ?_ ?_ key.symm
    · rfl
    · simp [ob, Obj.tensor]
    · rfl
    · simp [ob, Obj.tensor]
    · have e₁ : ∀ L ∈ Diagram.layers d,
          L.whisker (ob RD (wt RD (wt RD ρ []) []) [dn i, up i]) (wd RD ρ []) =
            Layer.wl (ob RD ρ [dn i, up i]) L := by
        intro L _; simp [Layer.whisker, Layer.wl]
      simp only [Diagram.layers_comp, Diagram.layers_rwhisker, Diagram.layers_lwhisker,
        layers_mkD, Diagram.layers_cast, Diagram.layers_whisker, List.map_congr_left e₁]
      simp [Layer.wr]
    · have hd : Chain (ob RD ρ []) (Diagram.layers d) (ob RD ρ []) := Diagram.chain d
      have e₂ : ∀ L ∈ Diagram.layers d, Layer.wl (ob RD ρ []) L = L := by
        intro L hL
        have := hd.start_of_mem hL
        simp only [ob_start, wt_nil] at this
        obtain ⟨st, le, g, ri⟩ := L
        simp only at this
        subst this
        simp [Layer.wl]
      simp only [Diagram.layers_comp, Diagram.layers_rwhisker, Diagram.layers_lwhisker,
        layers_mkD, List.map_congr_left e₂, List.map_id']
      simp [Layer.wr]

theorem ctxL_curlRTerm (γ : End ((pres RD k).obj (ob RD ρ []))) (p : ℕ) :
    ctxL RD k ρ [dn i, up i] [] [] [dn i] [] [([], .cap (up i), [])] [up i] [up i]
        (bubRU RD k ρ (up i) γ ≫ dotsU RD k ρ (up i) p) =
      dg RD k ρ [dn i, up i] [] (dotCapFELs i p) ≫ γ := by
  rw [bubRU_comm]
  show dg RD k ρ [dn i, up i] ([dn i] ++ [up i] ++ []) [] ≫
    plcL RD k ρ [dn i] [] [up i] [up i] _ ≫ dg RD k ρ ([dn i] ++ [up i] ++ []) [] _ = _
  rw [← plcL_comp RD k ρ [dn i] [] rfl rfl, plcL_bubRU_dn, dotsU]
  erw [plcL_dg]
  erw [dg_nil, Category.id_comp, Category.assoc, plcL_capUp_right]
  rw [← Category.assoc]
  erw [dg_comp (by schain) (by schain)]
  simp only [dotCapFELs, List.map_replicate, whL, List.append_nil]
  rw [dg_dots_cap_up]
  rfl

theorem dg_crossr_capDn (lam : X) :
    dg RD k lam [dn i, up i] [] (crossrL i i ++ [([], .cap (dn i), [])]) =
      -∑ g ∈ Finset.range (-ip RD i lam + 1).toNat,
        dg RD k lam [dn i, up i] [] (dotCapFELs i (-ip RD i lam - g).toNat) ≫
          cwU RD k lam i (ip RD i lam - 1 + g) := by
  simp only [crossrL, List.cons_append, List.nil_append]
  dswap 2
  rw [dg_stepL_at _ 0 [dn i] [] (dg_curlR RD k i lam) (by (try dnorm); schain)
    (by (try dnorm); schain) (by dnorm)]
  simp only [List.take_zero, List.length_cons, List.length_nil, zero_add, List.drop_succ_cons,
    List.drop_zero]
  rw [map_neg, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [ctxL_curlRTerm]

theorem dg_crossr_dotE (ν : X) :
    dg RD k ν [dn i, up i] [up i, dn i] (crossrL i i ++ [([], .dot (up i), [dn i])]) =
      dg RD k ν [dn i, up i] [up i, dn i] (([dn i], .dot (up i), []) :: crossrL i i) -
        dg RD k ν [dn i, up i] [up i, dn i] [([], .cap (up i), []), ([], .cup (up i), [])] := by
  simp only [crossrL, List.cons_append, List.nil_append]
  dswap 2
  rw [dg_stepL_at _ 1 [dn i] [dn i] (dg_slideREq' RD k _ i) (by (try dnorm); schain)
    (by (try dnorm); schain) (by dnorm)]
  rw [map_sub, ctxL_dg RD k ν (by (try dnorm); schain) (by (try dnorm); schain),
    ctxL_dg RD k ν (by (try dnorm); schain) (by (try dnorm); schain)]
  dnorm
  congr 1
  · dswap 0
  · dswap 0

/-- The closed form of `crossr ≫ (F-dot)^c ≫ cap` in `U`, for `c ∈ ℤ`. -/
def curlCapFE (lam : X) (c : ℤ) :
    (pres RD k).obj (ob RD lam [dn i, up i]) ⟶ (pres RD k).obj (ob RD lam []) :=
  -∑ g ∈ Finset.range (-ip RD i lam + 1 + c).toNat,
    dg RD k lam [dn i, up i] [] (dotCapFELs i (-ip RD i lam + c - g).toNat) ≫
      cwU RD k lam i (ip RD i lam - 1 + g)

theorem dotCapFE_succ (lam : X) (m : ℕ) :
    dg RD k lam [dn i, up i] [] (dotCapFELs i (1 + m)) =
      dg RD k lam [dn i, up i] [dn i, up i] [([dn i], .dot (up i), [])] ≫
        dg RD k lam [dn i, up i] [] (dotCapFELs i m) := by
  simp only [dotCapFELs]
  rw [dg_dots_cap_up, dg_dots_cap_up, dg_comp (by schain) (by schain)]
  simp only [List.replicate_add, List.replicate_one, List.cons_append, List.nil_append]

theorem curlCapFE_succ (lam : X) (c : ℤ) :
    curlCapFE RD k i lam (c + 1) =
      dg RD k lam [dn i, up i] [dn i, up i] [([dn i], .dot (up i), [])] ≫
          curlCapFE RD k i lam c -
        dg RD k lam [dn i, up i] [] [([], .cap (up i), [])] ≫ cwU RD k lam i c := by
  unfold curlCapFE
  rcases lt_or_ge (-ip RD i lam + 1 + c) 0 with h | h
  · have h1 : (-ip RD i lam + 1 + (c + 1)).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    have h2 : (-ip RD i lam + 1 + c).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    rw [h1, h2, cwU_eq_zero RD k _ i c (by omega)]
    simp
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, -ip RD i lam + 1 + c = n :=
      ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    have h1 : (-ip RD i lam + 1 + (c + 1)).toNat = n + 1 := by omega
    have h2 : (-ip RD i lam + 1 + c).toNat = n := by omega
    rw [h1, h2, Finset.sum_range_succ, Preadditive.comp_neg, Preadditive.comp_sum, neg_add,
      sub_eq_add_neg]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun f hf => ?_
      have hf' := Finset.mem_range.mp hf
      have e : (-ip RD i lam + (c + 1) - f).toNat = 1 + (-ip RD i lam + c - f).toNat := by omega
      rw [e, dotCapFE_succ, Category.assoc]
    · have e1 : ip RD i lam + -1 + (n : ℤ) = c := by omega
      have e2 : (-ip RD i lam + (c + 1) - n).toNat = 0 := by omega
      rw [e1, e2]
      rfl

section KLR

variable (lam : X)

/-- `crossr_{ii}`, then `c` dots on the downward strand, then the cap `E_i F_i ⟶ 1`, in `U′`. -/
abbrev KLzR (c : ℤ) : lob RD k lam [dn i, up i] ⟶ lob RD k lam [] :=
  ldg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) ≫ Yz RD k lam i c ≫
    ldg RD k lam [up i, dn i] [] [([], .cap (dn i), [])]

/-- An upward dot on `E_i` in `F_i E_i`, in `U′`. -/
abbrev XFE : lob RD k lam [dn i, up i] ⟶ lob RD k lam [dn i, up i] :=
  ldg RD k lam [dn i, up i] [dn i, up i] [([dn i], .dot (up i), [])]

theorem KLzR_succ (c : ℤ) :
    KLzR RD k i lam (c + 1) = XFE RD k i lam ≫ KLzR RD k i lam c -
      ldg RD k lam [dn i, up i] [] [([], .cap (up i), [])] ≫
        zcw (RD := RD) (k := k) lam i c := by
  have F1 : Yz RD k lam i 1 ≫ ldg RD k lam [up i, dn i] [] [([], .cap (dn i), [])] =
      ldg RD k lam [up i, dn i] [up i, dn i] [([], .dot (up i), [dn i])] ≫
        ldg RD k lam [up i, dn i] [] [([], .cap (dn i), [])] := by
    rw [Yz_one]
    exact (ldg_comp RD k (A := [([up i], .dot (dn i), [])])
      (B := [([], .cap (dn i), [])]) (by schain) (by schain)).trans
      ((congrArg (toLoc RD k).map (dg_dot_cap_dn RD k lam i)).trans
        (ldg_comp RD k (A := [([], .dot (up i), [dn i])])
          (B := [([], .cap (dn i), [])]) (by schain) (by schain)).symm)
  have F2 := Yz_comm_Edots RD k lam i 1 c
  simp only [List.replicate_one] at F2
  have F3 : ldg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) ≫
      ldg RD k lam [up i, dn i] [up i, dn i] [([], .dot (up i), [dn i])] =
      XFE RD k i lam ≫ ldg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) -
        ldg RD k lam [dn i, up i] [] [([], .cap (up i), [])] ≫
          ldg RD k lam [] [up i, dn i] [([], .cup (up i), [])] := by
    rw [ldg_comp RD k (by schain) (by schain), ldg_comp RD k (by schain) (by schain),
      ldg_comp RD k (by schain) (by schain), ldg, ldg, ← Functor.map_sub]
    exact congrArg (toLoc RD k).map (dg_crossr_dotE RD k i lam)
  simp only [KLzR, XFE, zcw]
  rw [Yz, add_comm, zdot_add, ← Yz, ← Yz, Category.assoc, F1, ← Category.assoc (Yz _ _ _ _ c),
    F2]
  simp only [Category.assoc]
  rw [← Category.assoc (ldg RD k lam [dn i, up i] [up i, dn i] (crossrL i i)), F3]
  simp only [Preadditive.sub_comp, Category.assoc]

/-- `crossr ≫ (F-dot)^c ≫ cap` in `U′` is the image of `curlCapFE c`, for every `c ∈ ℤ`. -/
theorem KLzR_eq (c : ℤ) :
    KLzR RD k i lam c = (toLoc RD k).map (curlCapFE RD k i lam c) := by
  have hX : (toLoc RD k).map (dg RD k lam [dn i, up i] [dn i, up i] [([dn i], .dot (up i), [])]) =
      XFE RD k i lam := rfl
  have hC : (toLoc RD k).map (dg RD k lam [dn i, up i] [] [([], .cap (up i), [])]) =
      ldg RD k lam [dn i, up i] [] [([], .cap (up i), [])] := rfl
  induction c using Int.induction_on with
  | zero =>
    rw [KLzR, Yz, zdot_zero]
    erw [Category.id_comp]
    rw [ldg_comp RD k (A := crossrL i i) (B := [([], .cap (dn i), [])]) (by schain) (by schain)]
    refine congrArg (toLoc RD k).map ((dg_crossr_capDn RD k i lam).trans ?_)
    simp only [curlCapFE, add_zero]
  | succ n ih =>
    rw [KLzR_succ, ih, zcw_eq, curlCapFE_succ, (toLoc RD k).map_sub, (toLoc RD k).map_comp,
      (toLoc RD k).map_comp, hX, hC]
  | pred n ih =>
    have e1 := KLzR_succ RD k i lam (-(n : ℤ) - 1)
    have e2 := congrArg (toLoc RD k).map (curlCapFE_succ RD k i lam (-(n : ℤ) - 1))
    rw [(toLoc RD k).map_sub, (toLoc RD k).map_comp, (toLoc RD k).map_comp, hX, hC] at e2
    rw [show -(n : ℤ) - 1 + 1 = -n by ring, ih, zcw_eq] at e1
    rw [show -(n : ℤ) - 1 + 1 = -n by ring] at e2
    have e3 := sub_left_inj.mp (e1.symm.trans e2)
    have hE : Epi (XFE RD k i lam) := by
      unfold XFE ldg
      exact @IsIso.epi_of_iso _ _ _ _ _ (isIso_toLoc_dg_dot RD k lam [dn i] (up i) [])
    exact (cancel_epi (XFE RD k i lam)).mp e3

end KLR

end Categorification.KL3.Diagram
