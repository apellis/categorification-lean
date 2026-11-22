/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftDecompCurl
import Categorification.Diagrams.KL3.Grassmannian
import Categorification.Diagrams.KL3.LocalizationShiftCurlL

/-!
# The left curl closed by a cap, under the weight shift of `U′`

Part of the proof that the weight shift of `U′` respects the decomposition relation of
`E_i F_i` (Webster arXiv:1309.3796v2, Proposition 3.30).

## Main results

* `plcL_capDn`: an endomorphism of `1` to the left of the cap `E F ⟶ 1` moves above it.
* `dg_crossl_capUp'`: `crossl_{ii} ≫ cap` in `U`, from the left curl relation of KL III.
* `KLz_eq`: `crossl ≫ (F-dot)^c ≫ cap` in `U′` is the image of the explicit sum `curlCapU c`,
  for every `c ∈ ℤ`.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

variable (ρ : X) (i : I)

/-- An endomorphism of `1` placed to the left of the strands of the cap `E F ⟶ 1` can be moved
above the cap. -/
theorem plcL_capDn (β : End ((pres RD k).obj (ob RD (wt RD (wt RD ρ [dn i]) [up i]) []))) :
    plcL RD k ρ [] [up i, dn i] [] [] β ≫ dg RD k ρ [up i, dn i] [] [([], .cap (dn i), [])] =
      dg RD k ρ [up i, dn i] [] [([], .cap (dn i), [])] ≫
        wtTransport RD k (by simp : wt RD (wt RD ρ [dn i]) [up i] = ρ) β := by
  diag_induction β [wtTransport_add, wtTransport_smul, wtTransport_zero, Preadditive.add_comp,
      Preadditive.comp_add, Linear.smul_comp, Linear.comp_smul, Limits.zero_comp,
      Limits.comp_zero] =>
    rename_i d _
    rw [plcL_diag, wtTransport_diag, dg_of (by schain), ← Presentation.diag_comp,
      ← Presentation.diag_comp]
    have hc : (ob RD (wt RD ρ [up i, dn i]) []).Composable (ob RD ρ [up i, dn i]) :=
      ⟨ob_wf RD _ _, rfl, ob_wf RD _ _⟩
    have key := (pres RD k).diag_interchange_of_composable
      (a := ob RD (wt RD ρ [up i, dn i]) []) (a' := ob RD (wt RD ρ [up i, dn i]) [])
      (b := ob RD ρ [up i, dn i]) (b' := ob RD ρ []) d
      (mkD RD ρ [([], .cap (dn i), [])] ⟨rfl, rfl⟩) hc
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
    refine diag_transfer RD k
      (a' := (ob RD (wt RD ρ [up i, dn i]) []).tensor (ob RD ρ [up i, dn i]))
      (b' := (ob RD (wt RD ρ [up i, dn i]) []).tensor (ob RD ρ [])) _ _ _ _ (Obj.ext ?_ ?_)
      (Obj.ext ?_ ?_) ?_ ?_ key
    · rfl
    · rfl
    · simp [ob, Obj.tensor]
    · rfl
    · simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_whisker,
        Diagram.layers_rwhisker, Diagram.layers_lwhisker, layers_mkD, List.map_congr_left e₁]
      congr 1
    · simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_rwhisker,
        Diagram.layers_lwhisker, layers_mkD, List.map_congr_left e₂, List.map_id']
      congr 1

/-- A term of the left curl relation, whiskered on the right by `F_i` and closed by the cap. -/
theorem ctxL_curlTerm (β : End ((pres RD k).obj (ob RD (wt RD (wt RD ρ [dn i]) [up i]) [])))
    (p : ℕ) :
    ctxL RD k ρ [up i, dn i] [] [] [] [dn i] [([], .cap (dn i), [])] [up i] [up i]
        (bubLU RD k (wt RD ρ [dn i]) (up i) β ≫ dotsU RD k (wt RD ρ [dn i]) (up i) p) =
      dg RD k ρ [up i, dn i] [] (dotCapEFLs i p) ≫
        wtTransport RD k (by simp : wt RD (wt RD ρ [dn i]) [up i] = ρ) β := by
  rw [bubLU_comm]
  show dg RD k ρ [up i, dn i] ([] ++ [up i] ++ [dn i]) [] ≫
    plcL RD k ρ [] [dn i] [up i] [up i] _ ≫ dg RD k ρ ([] ++ [up i] ++ [dn i]) [] _ = _
  rw [← plcL_comp RD k ρ [] [dn i] rfl rfl, plcL_bubLU_dn, dotsU, plcL_dg]
  erw [dg_nil, Category.id_comp, Category.assoc, plcL_capDn]
  rw [← Category.assoc]
  erw [dg_comp (by schain) (by schain)]
  simp only [dotCapEFLs, List.map_replicate, whL, List.append_nil, List.nil_append]
  rfl

/-- The sideways crossing `crossl_{ii}` closed by the cap `F_i E_i ⟶ 1`: the left curl relation
whiskered by `F_i`. -/
theorem dg_crossl_capUp (lam : X) :
    dg RD k lam [up i, dn i] [] (crosslL i i ++ [([], .cap (up i), [])]) =
      ∑ g ∈ Finset.range (ip RD i (wt RD (wt RD lam [dn i]) [up i]) + 1).toNat,
        dg RD k lam [up i, dn i] []
            (dotCapEFLs i (ip RD i (wt RD (wt RD lam [dn i]) [up i]) - g).toNat) ≫
          ccwU RD k lam i (-ip RD i (wt RD (wt RD lam [dn i]) [up i]) - 1 + g) := by
  simp only [crosslL, List.cons_append, List.nil_append]
  dswap 2
  rw [dg_stepL_at _ 0 [] [dn i] (dg_curlL RD k i (wt RD lam [dn i])) (by (try dnorm); schain)
    (by (try dnorm); schain) (by dnorm)]
  simp only [List.take_zero, List.length_cons, List.length_nil, zero_add, List.drop_succ_cons,
    List.drop_zero]
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [ctxL_curlTerm, wtTransport_ccwU]

theorem dg_crossl_capUp' (lam : X) :
    dg RD k lam [up i, dn i] [] (crosslL i i ++ [([], .cap (up i), [])]) =
      ∑ g ∈ Finset.range (ip RD i lam + 1).toNat,
        dg RD k lam [up i, dn i] [] (dotCapEFLs i (ip RD i lam - g).toNat) ≫
          ccwU RD k lam i (-ip RD i lam - 1 + g) := by
  have hw : wt RD (wt RD lam [dn i]) [up i] = lam := by simp
  rw [dg_crossl_capUp, hw]

/-- The closed form of `crossl ≫ (F-dot)^c ≫ cap` in `U`, for `c ∈ ℤ`. -/
def curlCapU (lam : X) (c : ℤ) :
    (pres RD k).obj (ob RD lam [up i, dn i]) ⟶ (pres RD k).obj (ob RD lam []) :=
  ∑ g ∈ Finset.range (ip RD i lam + 1 + c).toNat,
    dg RD k lam [up i, dn i] [] (dotCapEFLs i (ip RD i lam + c - g).toNat) ≫
      ccwU RD k lam i (-ip RD i lam - 1 + g)

theorem dotCapEF_succ (lam : X) (m : ℕ) :
    dg RD k lam [up i, dn i] [] (dotCapEFLs i (1 + m)) =
      dg RD k lam [up i, dn i] [up i, dn i] [([], .dot (up i), [dn i])] ≫
        dg RD k lam [up i, dn i] [] (dotCapEFLs i m) := by
  rw [dg_comp (by schain) (by schain)]
  simp only [dotCapEFLs, List.replicate_add, List.replicate_one, List.cons_append,
    List.nil_append]

theorem curlCapU_succ (lam : X) (c : ℤ) :
    curlCapU RD k i lam (c + 1) =
      dg RD k lam [up i, dn i] [up i, dn i] [([], .dot (up i), [dn i])] ≫ curlCapU RD k i lam c +
        dg RD k lam [up i, dn i] [] [([], .cap (dn i), [])] ≫ ccwU RD k lam i c := by
  unfold curlCapU
  rcases lt_or_ge (ip RD i lam + 1 + c) 0 with h | h
  · have h1 : (ip RD i lam + 1 + (c + 1)).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    have h2 : (ip RD i lam + 1 + c).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    rw [h1, h2, ccwU_eq_zero RD k _ i c (by omega)]
    simp
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, ip RD i lam + 1 + c = n :=
      ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    have h1 : (ip RD i lam + 1 + (c + 1)).toNat = n + 1 := by omega
    have h2 : (ip RD i lam + 1 + c).toNat = n := by omega
    rw [h1, h2, Finset.sum_range_succ, Preadditive.comp_sum]
    congr 1
    · refine Finset.sum_congr rfl fun f hf => ?_
      have hf' := Finset.mem_range.mp hf
      have e : (ip RD i lam + (c + 1) - f).toNat = 1 + (ip RD i lam + c - f).toNat := by omega
      rw [e, dotCapEF_succ, Category.assoc]
    · have e1 : -ip RD i lam - 1 + (n : ℤ) = c := by omega
      have e2 : (ip RD i lam + (c + 1) - n).toNat = 0 := by omega
      rw [e1, e2]
      rfl

/-- `crossl ≫ (F-dot)^c ≫ cap` in `U′` is the image of `curlCapU c`, for every `c ∈ ℤ`. -/
theorem KLz_eq (lam : X) (c : ℤ) :
    KLz RD k lam i c = (toLoc RD k).map (curlCapU RD k i lam c) := by
  have hX : (toLoc RD k).map (dg RD k lam [up i, dn i] [up i, dn i] [([], .dot (up i), [dn i])]) =
      XEF RD k lam i := rfl
  have hC : (toLoc RD k).map (dg RD k lam [up i, dn i] [] [([], .cap (dn i), [])]) =
      ldg RD k lam [up i, dn i] [] [([], .cap (dn i), [])] := rfl
  induction c using Int.induction_on with
  | zero =>
    rw [KLz, zdot_zero]
    erw [Category.id_comp]
    rw [ldg_comp RD k (A := crosslL i i) (B := [([], .cap (up i), [])]) (by schain) (by schain)]
    refine congrArg (toLoc RD k).map ((dg_crossl_capUp' RD k i lam).trans ?_)
    simp only [curlCapU, add_zero]
  | succ n ih =>
    rw [KLz_succ, ih, zccw_eq, curlCapU_succ, (toLoc RD k).map_add, (toLoc RD k).map_comp,
      (toLoc RD k).map_comp, hX, hC]
  | pred n ih =>
    have e1 := KLz_succ RD k lam i (-(n : ℤ) - 1)
    have e2 := congrArg (toLoc RD k).map (curlCapU_succ RD k i lam (-(n : ℤ) - 1))
    rw [(toLoc RD k).map_add, (toLoc RD k).map_comp, (toLoc RD k).map_comp, hX, hC] at e2
    rw [show -(n : ℤ) - 1 + 1 = -n by ring, ih, zccw_eq] at e1
    rw [show -(n : ℤ) - 1 + 1 = -n by ring] at e2
    have e3 := add_left_inj _ |>.mp (e1.symm.trans e2)
    have hE : Epi (XEF RD k lam i) := by
      unfold XEF ldg
      exact @IsIso.epi_of_iso _ _ _ _ _ (isIso_toLoc_dg_dot RD k lam [] (up i) [dn i])
    exact (cancel_epi (XEF RD k lam i)).mp e3

end Categorification.KL3.Diagram
