/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaIndep
import Categorification.Flag.GammaN
import Categorification.Diagrams.KL3.SlnEmbedU

/-!
# `Γ_N`-like functors for `U(sl_{m₀+1})`: `Γ_N` of `sl_{m₀+2}` after the embedding

Khovanov–Lauda III (arXiv:0807.3250v1), §6.4 (TeX `sln-2008-ArXiv.tex` l. 9598–9790). We
construct, for every bound `B`, the data `Categorification.Flag.Indep.Rep` of the abstract
independence theorem `Categorification.Flag.Indep.linearIndependent_vB`:

* the functor `Fsl K m₀ N = Γ_N ∘ Σ ∘ embedU` from `U(sl_{m₀+1})` to `K`-modules, where
  `embedU` is the 2-functor `U(sl_{m₀+1}) → U(sl_{m₀+2})`
  (`Categorification.KL3.Diagram.SlnEmbed.embedU`), `Σ` the rescaling isomorphism of KL III
  §4.2.1 with the erratum's cups and caps (`sigmaF`, built from `CL.Sln.sigmaDatum`), and `Γ_N`
  the 2-representation of `U_Q(sl_{m₀+2})` on the flag 2-category (`Categorification.Flag.GammaN`);
* `gammaLike_Fsl`: it is `Γ_N`-like for the relabelling `ιF` of diagrams and the units of `Σ`;
* `upCompat_sln`: upward dots and crossings go to upward dots and crossings, with colours
  `Fin.castSucc` (never the last colour of `sl_{m₀+2}`);
* the choice of `N` (`Nbd`): all regions of the relabelled paths `E_{+i} 1_λ`, `i ∈ Seq(ν)`, are
  realized compositions of `N` with all blocks larger than `B` (`wok_path`, `regionsBig_path`);
* `hbub_sln`: the generators of `Π_λ` act on the rightmost region by their `Γ_N`-values
  `bubVal`, up to the units of `Σ` (`ωsl`).

The extra last block of `sl_{m₀+2}` is what makes the bubbles independent in every
characteristic (see `Categorification.Flag.Indep.chernData`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Flag.Indep

open Categorification.Flag Categorification.KL3.Diagram StringDiagrams CategoryTheory
  Categorification.KL3.Diagram.SlnEmbed

universe u

variable {K : Type u} [Field K] {m₀ : ℕ}

/-! ## `Σ` on KL III's presentation -/

section Sigma

variable (K) (M : ℕ)

theorem sigma_rel (i : (pres (slRootDatum M) K).Rel) :
    (CL.presCL (slRootDatum M) K (CL.Sln.slnScalars K M)).lin
      (CL.Rescale.scL (CL.Sln.sigmaDatum K M).chi ((pres (slRootDatum M) K).rel i)) = 0 := by
  revert i
  rw [← CL.presCL_kl]
  exact (CL.Sln.sigmaDatum K M).lin_scL_rel' CL.CLScalars.kl CL.Sln.sigmaDatum_mapScalars

/-- **`Σ : U(sl_{M+1}) → U_Q(sl_{M+1})`** (KL III §4.2.1, with the erratum's cups and caps) as a
rescaling functor out of KL III's presentation `pres`. -/
def sigmaF : (pres (slRootDatum M) K).Presented ⥤
    (CL.presCL (slRootDatum M) K (CL.Sln.slnScalars K M)).Presented :=
  CL.Rescale.functor (CL.Sln.sigmaDatum K M).chi (sigma_rel K M)

theorem sigmaF_diag {a b : Obj (psig (slRootDatum M))} (d : a ⟶ b) :
    (sigmaF K M).map ((pres (slRootDatum M) K).diag d) =
      ((CL.Rescale.weight (CL.Sln.sigmaDatum K M).chi (Diagram.layers d) : Kˣ) : K) •
        (CL.presCL (slRootDatum M) K (CL.Sln.slnScalars K M)).diag d :=
  CL.Rescale.functor_diag _ d

instance : (sigmaF K M).Additive := by unfold sigmaF; infer_instance

instance : (sigmaF K M).Linear K := by unfold sigmaF; infer_instance

end Sigma

/-! ## The functor -/

instance (M N : ℕ) : (GammaN K M N).Additive := by unfold GammaN gammaLift; infer_instance

instance (M N : ℕ) : (GammaN K M N).Linear K := by unfold GammaN gammaLift; infer_instance

variable (K m₀) in
/-- **The `Γ_N`-like functor** `Γ_N ∘ Σ ∘ embedU : U(sl_{m₀+1}) → K-mod`. -/
def Fsl (N : ℕ) : (pres (slRootDatum m₀) K).Presented ⥤ ModuleCat.{u} K :=
  embedU K m₀ ⋙ sigmaF K (m₀ + 1) ⋙ GammaN K (m₀ + 1) N

instance (N : ℕ) : (Fsl K m₀ N).Additive := by unfold Fsl; infer_instance

instance (N : ℕ) : (Fsl K m₀ N).Linear K := by unfold Fsl; infer_instance

/-- `Fsl` is `Γ_N`-like for the relabelling `ιF` and the units of `Σ`. -/
theorem gammaLike_Fsl (N : ℕ) :
    GammaLike (Fsl K m₀ N) (SlnEmbed.ιF m₀) N (gammaDn K (m₀ + 1))
      (CL.Sln.sigmaDatum K (m₀ + 1)).chi where
  obj _ := rfl
  map f := by
    show (GammaN K (m₀ + 1) N).map ((sigmaF K (m₀ + 1)).map
      ((embedU K m₀).map ((pres (slRootDatum m₀) K).diag f))) = 𝟙 _ ≫ _ ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, embedU_diag, sigmaF_diag, Functor.map_smul]
    unfold GammaN gammaLift
    rw [Presentation.lift_diag]
    rfl

/-! ## Upward dots and crossings -/

theorem length_wd {n : ℕ} (μ : Fin n → ℤ) (t : List (Letter (Fin n))) :
    (wd (slRootDatum n) μ t).length = t.length := by
  induction t with
  | nil => rfl
  | cons l t ih => simp [ih]

/-- **Upward dots and crossings go to single upward dots and crossings** of the colours
`Fin.castSucc c`. -/
theorem upCompat_sln (μ : Wt m₀) (ν : Multiset (Fin m₀)) :
    UpCompat (SlnEmbed.ιF m₀) Fin.castSucc μ ν where
  dot s a := by
    refine ⟨_, rfl, ?_, _, rfl⟩
    simp only [ιL, upLay, lay, List.length_map, length_wd, KLR.Diagram.lay_left, ups,
      List.length_take, KLR.Diagram.length_word]
    exact min_eq_left a.isLt.le
  cross s j h := by
    refine ⟨_, rfl, ?_, _, rfl⟩
    simp only [ιL, upLay, lay, List.length_map, length_wd, KLR.Diagram.lay_left, ups,
      List.length_take, KLR.Diagram.length_word]
    omega

/-! ## Regions -/

section Regions

variable {M : ℕ}

/-- `∑_{k ≥ j} v_k`: block `j` of the composition of weight `v` minus the last block. -/
def tailSum (v : Fin M → ℤ) (j : Fin (M + 1)) : ℤ := ∑ k : Fin M, if (j : ℕ) ≤ k then v k else 0

/-- The `ℓ¹`-norm of a weight. -/
def l1 (v : Fin M → ℤ) : ℤ := ∑ k, |v k|

theorem abs_tailSum_le (v : Fin M → ℤ) (j : Fin (M + 1)) : |tailSum v j| ≤ l1 v := by
  unfold tailSum l1
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  split_ifs <;> simp

theorem l1_add (v w : Fin M → ℤ) : l1 (v + w) ≤ l1 v + l1 w := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => abs_add_le _ _

theorem tailSum_castSucc_sub_succ (v : Fin M → ℤ) (a : Fin M) :
    tailSum v a.castSucc - tailSum v a.succ = v a := by
  unfold tailSum
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
  · simp
  · intro k _ hk
    have hk' : (k : ℕ) ≠ a := fun e => hk (Fin.ext e)
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases h1 : (a : ℕ) ≤ k <;> by_cases h2 : (a : ℕ) + 1 ≤ k <;> simp only [h1, h2,
      ↓reduceIte, sub_self, sub_zero, zero_sub] <;> omega
  · simp

theorem sum_tailSum (v : Fin M → ℤ) : ∑ j, tailSum v j = SlnEmbed.sW v := by
  unfold tailSum SlnEmbed.sW
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have : (Finset.univ.filter fun j : Fin (M + 1) => (j : ℕ) ≤ k) = Finset.Iic k.castSucc := by
    ext j; simp [Fin.le_def]
  rw [this, Fin.card_Iic]
  simp

/-- **Weights from tail sums**: if `T + tailSum v j ≥ 0` for all `j`, the weight `v` is realized
by a composition of `(M + 1) T + s(v)` with blocks `T + tailSum v j`. -/
theorem realized_tail (T : ℤ) (v : Fin M → ℤ) (hT : ∀ j, 0 ≤ T + tailSum v j) :
    Realized ((((M : ℤ) + 1) * T + SlnEmbed.sW v).toNat) v ∧
      ∀ j, (compOf ((((M : ℤ) + 1) * T + SlnEmbed.sW v).toNat) v j : ℤ) = T + tailSum v j := by
  set d : Comp M := fun j => (T + tailSum v j).toNat with hd_def
  have hd : ∀ j, (d j : ℤ) = T + tailSum v j := fun j => Int.toNat_of_nonneg (hT j)
  have hX : ((M : ℤ) + 1) * T + SlnEmbed.sW v = ∑ j, (d j : ℤ) := by
    simp only [hd, Finset.sum_add_distrib, sum_tailSum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hsum : ∑ j, d j = (((M : ℤ) + 1) * T + SlnEmbed.sW v).toNat := by
    rw [hX, ← Nat.cast_sum, Int.toNat_natCast]
  have hw : compWeight d = v := funext fun a => by
    simp only [compWeight, hd]
    linarith [tailSum_castSucc_sub_succ v a]
  exact ⟨⟨d, hsum, hw⟩, fun j => by rw [compOf_eq hsum hw, hd]⟩

theorem sW_smul (c : ℤ) (v : Fin M → ℤ) : SlnEmbed.sW (c • v) = c * SlnEmbed.sW v := by
  simp only [SlnEmbed.sW, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem sW_sh_ιl (l : Letter (Fin m₀)) : SlnEmbed.sW (sh (slRootDatum (m₀ + 1)) (ιl l)) = 0 := by
  rw [sh, sW_smul, sW_iX]
  have := l.2.isLt
  simp only [ιl, Fin.val_castSucc]
  simp only [show ¬ ((l.2 : ℕ) + 1 = m₀ + 1) by omega, ↓reduceIte, mul_zero]

theorem l1_sh_le (l : Letter (Fin M)) : l1 (sh (slRootDatum M) l) ≤ 2 * M := by
  unfold l1
  calc ∑ k, |sh (slRootDatum M) l k| ≤ ∑ _k : Fin M, (2 : ℤ) := Finset.sum_le_sum fun k _ => by
        simp only [sh, Pi.smul_apply, smul_eq_mul, slRootDatum_iX_apply, slCartan_dot_val]
        rcases l with ⟨b, i⟩
        cases b <;> simp only [QuantumGroup.UDot.sgn_true, QuantumGroup.UDot.sgn_false] <;>
          split_ifs <;> norm_num
    _ = 2 * M := by simp [mul_comm]

theorem phiW_wt_cons (μ : Wt m₀) (l : Letter (Fin m₀)) (t : List (Letter (Fin m₀))) :
    phiW (wt (slRootDatum m₀) μ (l :: t)) =
      sh (slRootDatum (m₀ + 1)) (ιl l) + phiW (wt (slRootDatum m₀) μ t) :=
  (sh_ιl l _).symm

theorem sW_phiW_wt (μ : Wt m₀) (t : List (Letter (Fin m₀))) :
    SlnEmbed.sW (phiW (wt (slRootDatum m₀) μ t)) = SlnEmbed.sW (phiW μ) := by
  induction t with
  | nil => rfl
  | cons l t ih => rw [phiW_wt_cons, SlnEmbed.sW_add, sW_sh_ιl, zero_add, ih]

theorem l1_phiW_wt (μ : Wt m₀) (t : List (Letter (Fin m₀))) :
    l1 (phiW (wt (slRootDatum m₀) μ t)) ≤ l1 (phiW μ) + 2 * ((m₀ : ℤ) + 1) * t.length := by
  induction t with
  | nil => simp
  | cons l t ih =>
    rw [phiW_wt_cons]
    have h1 := l1_add (sh (slRootDatum (m₀ + 1)) (ιl l)) (phiW (wt (slRootDatum m₀) μ t))
    have h2 := l1_sh_le (M := m₀ + 1) (ιl l)
    simp only [List.length_cons]
    push_cast at h2 ⊢
    nlinarith

variable (μ : Wt m₀) (L B : ℕ)

/-- The bound on the tail sums of all regions of paths of length `≤ L` from `φ(μ)`. -/
def Cbd : ℤ := l1 (phiW μ) + 2 * ((m₀ : ℤ) + 1) * L

/-- The last block of the regions. -/
def Tbd : ℤ := B + 1 + Cbd μ L

/-- **The size of the flag varieties**: `(m₀ + 2) T + s(φ μ)`. -/
def Nbd : ℕ := ((((m₀ + 1 : ℕ) : ℤ) + 1) * Tbd μ L B + SlnEmbed.sW (phiW μ)).toNat

/-- **Every region of a path of length `≤ L` from `φ(μ)` is realized by a composition of `Nbd`
with all blocks larger than `B`.** -/
theorem region_good (t : List (Letter (Fin m₀))) (ht : t.length ≤ L) :
    Realized (Nbd μ L B) (phiW (wt (slRootDatum m₀) μ t)) ∧
      ∀ j, B < compOf (Nbd μ L B) (phiW (wt (slRootDatum m₀) μ t)) j := by
  set v := phiW (wt (slRootDatum m₀) μ t)
  have h1 : ∀ j, (B : ℤ) + 1 ≤ Tbd μ L B + tailSum v j := fun j => by
    have e1 := abs_tailSum_le v j
    have e2 := l1_phiW_wt μ t
    have e3 : (t.length : ℤ) ≤ L := by exact_mod_cast ht
    have e4 := neg_abs_le (tailSum v j)
    unfold Tbd Cbd
    nlinarith
  obtain ⟨hr, hc⟩ := realized_tail (M := m₀ + 1) (Tbd μ L B) v (fun j => by linarith [h1 j])
  rw [sW_phiW_wt] at hr hc
  refine ⟨hr, fun j => ?_⟩
  have e1 := hc j
  have e2 := h1 j
  unfold Nbd
  omega

theorem wok_path (t : List (Letter (Fin m₀))) (ht : t.length ≤ L) :
    WOK (Nbd μ L B) (ιO (ob (slRootDatum m₀) μ t)).start (ιO (ob (slRootDatum m₀) μ t)).word := by
  induction t with
  | nil => exact (region_good μ L B [] (by simp)).1
  | cons l t ih =>
    refine ⟨(region_good μ L B (l :: t) ht).1, sh_ιl l _, ih ?_⟩
    simp only [List.length_cons] at ht; omega

theorem regionsBig_path (w : List (Fin m₀)) (hw : w.length ≤ L) :
    RegionsBig (Nbd μ L B) B (ιO (ob (slRootDatum m₀) μ (ups w))).start
      (ιO (ob (slRootDatum m₀) μ (ups w))).word := by
  induction w with
  | nil => exact (region_good μ L B [] (by simp)).2
  | cons c w ih =>
    refine ⟨rfl, (region_good μ L B (ups (c :: w)) (by simpa using hw)).2, ih ?_⟩
    simp only [List.length_cons] at hw; omega

theorem lastR_path (t : List (Letter (Fin m₀))) :
    lastR (ιO (ob (slRootDatum m₀) μ t)).start (ιO (ob (slRootDatum m₀) μ t)).word = phiW μ := by
  exact (lastR_eq_endR _ _).trans ((ιO_endR _).trans (congrArg phiW (ob_endR _ μ t)))

end Regions

end Categorification.Flag.Indep

end
