/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.GdimBound
import Categorification.Diagrams.KL3.GammaU

/-!
# Nondegeneracy only needs positive sequences

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.3,
Remark after the definition of nondegeneracy (TeX l. 4632): "Nondegeneracy holds if the above
condition is true for all `λ ∈ X` and all pairs of positive sequences `𝐢, 𝐣`."

We prove (`calculusNondeg_of_positive`): if
`gdim HOM_U(E_𝐢 1_λ, E_𝐣 1_λ) = π ⟨E_𝐢 1_λ, E_𝐣 1_λ⟩` for all `λ` and all **positive** `𝐢, 𝐣`,
then it holds for all signed sequences, i.e. `CalculusNondeg RD k` (simply-laced, `I` finite,
`𝕜` a field). The proof:

* **bending** (`finrank_homD_bend`, biadjointness, KL III (3.1)–(3.2)):
  `HOM_U(E_𝐢 1_λ, E_𝐣 1_λ)_d ≅ HOM_U(1_λ, E_{𝐢* 𝐣} 1_λ)_{d + c}` with `c` the degree of the nested
  cups, `c = -rcx` the exponent in `ρ̄(E_𝐢) = q^{rcx} …` (`sdegSum_cupA_rd`), matching
  `(E_𝐢 1_λ, E_𝐣 1_λ) = q^{rcx} (1_λ, E_{𝐢* 𝐣} 1_λ)` on the algebraic side;
* **the commutation relations** (KL III Propositions 3.25, 3.26, in `K₀` as `eC_EF`, `eC_FE`,
  `eC_ij`): the functional `[B] ↦ dim U̇(1_λ{t}, B)` (`homDim`) factors through `K₀(U̇)`, so the
  graded dimensions of `HOM_U(1_λ, E_u 1_λ)` satisfy the same recursion as `(1_λ, E_u 1_λ)`
  (`UDot.φ_comm`);
* **normal ordering** (`UDot.normal_induction`): the normally ordered words `F_c E_b` bend to
  pairs of positive sequences `(c^{rev}, b)`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Module Finset

universe w u v

/-! ## Graded maps with graded inverses -/

section Linear

variable {k : Type w} [Field k]

/-- Mutually inverse linear maps shifting gradings by `c` and `c'` identify the graded pieces
`ℳ_d ≅ 𝒩_{d + c}` (both vanish if `c + c' ≠ 0`). -/
theorem finrank_eq_of_graded_inverse {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (ℳ : ℤ → Submodule k V) (𝒩 : ℤ → Submodule k W) (hM : DirectSum.IsInternal ℳ)
    (hN : DirectSum.IsInternal 𝒩) (F : V →ₗ[k] W) (G : W →ₗ[k] V) (c c' : ℤ)
    (hF : ∀ d, (ℳ d).map F ≤ 𝒩 (d + c)) (hG : ∀ e, (𝒩 e).map G ≤ ℳ (e + c'))
    (hGF : ∀ x, G (F x) = x) (hFG : ∀ y, F (G y) = y) (d : ℤ) :
    finrank k (ℳ d) = finrank k (𝒩 (d + c)) := by
  have mF : ∀ {d x}, x ∈ ℳ d → F x ∈ 𝒩 (d + c) := fun hx => hF _ ⟨_, hx, rfl⟩
  have mG : ∀ {e y}, y ∈ 𝒩 e → G y ∈ ℳ (e + c') := fun hy => hG _ ⟨_, hy, rfl⟩
  by_cases hcc : c + c' = 0
  · have e : d + c + c' = d := by omega
    let E : ℳ d ≃ₗ[k] 𝒩 (d + c) :=
      { toFun := fun x => ⟨F x, mF x.2⟩
        invFun := fun y => ⟨G y, by have := mG y.2; rwa [e] at this⟩
        map_add' := fun x y => Subtype.ext (map_add F _ _)
        map_smul' := fun r x => Subtype.ext (map_smul F _ _)
        left_inv := fun x => Subtype.ext (hGF x)
        right_inv := fun y => Subtype.ext (hFG y) }
    exact E.finrank_eq
  · have dM := hM.submodule_iSupIndep.pairwiseDisjoint
    have dN := hN.submodule_iSupIndep.pairwiseDisjoint
    have h1 : ℳ d = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      have hx' : x ∈ ℳ (d + c + c') := by rw [← hGF x]; exact mG (mF hx)
      exact (Submodule.disjoint_def.1 (dM (show d ≠ d + c + c' by omega)) x hx hx')
    have h2 : 𝒩 (d + c) = ⊥ := by
      refine eq_bot_iff.2 fun y hy => ?_
      have hy' : y ∈ 𝒩 (d + c + c' + c) := by rw [← hFG y]; exact mF (mG hy)
      exact (Submodule.disjoint_def.1 (dN (show d + c ≠ d + c + c' + c by omega)) y hy hy')
    rw [h1, h2, finrank_bot, finrank_bot]

end Linear

/-! ## Bending -/

section Bend

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k]

/-- **Bending the source up on the left** (biadjointness): `HOM_U(E_s 1_μ, E_t 1_μ)_d ≅
HOM_U(1_μ, E_{s* t} 1_μ)_{d + c}` with `c` the degree of the nested cups `1 → s* s`. -/
theorem finrank_homD_bend (μ : X) (s t : List (Letter I)) (d : ℤ) :
    finrank k (HomD RD k μ s t d) =
      finrank k (HomD RD k μ [] (rd s ++ t) (d + (sdegSum RD μ (cupA (rd s)) + sdegSum RD μ []))) := by
  have hpre : SChain [] (cupA (rd s)) (rd s ++ s ++ []) := by simpa using sChain_cupA (rd s)
  have hpostF : SChain (rd s ++ t ++ []) [] (rd s ++ t) := by simp
  have hpreG : SChain s [] (s ++ [] ++ []) := by simp
  have hpostG : SChain (s ++ (rd s ++ t) ++ []) ((capA (rd s)).map (whL [] t)) t := by
    simpa using (sChain_capA (rd s)).whisk [] t
  let F := ctxL RD k μ [] (rd s ++ t) (cupA (rd s)) (rd s) [] [] s t
  let G := ctxL RD k μ s t [] s [] ((capA (rd s)).map (whL [] t)) [] (rd s ++ t)
  have keyGF : G.comp F = LinearMap.id := by
    refine hom_ext_dg RD k μ _ _ (fun A hA => ?_)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, F, G]
    erw [ctxL_dg_nil RD k μ hpre hpostF, ctxL_dg_nil RD k μ hpreG hpostG]
    have e := dg_unbend_flat (RD := RD) (k := k) (rd s) [] [] t (M := A) (by simpa using hA) μ
    rw [rd_rd, rd_nil] at e
    repeat rw [List.append_nil] at e
    refine Eq.trans (dg_list_eq ?_) e
    simp [flatL]
  have keyFG : F.comp G = LinearMap.id := by
    refine hom_ext_dg RD k μ _ _ (fun M hM => ?_)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, F, G]
    erw [ctxL_dg_nil RD k μ hpreG hpostG, ctxL_dg_nil RD k μ hpre hpostF]
    have e := dg_unbend_sharp (RD := RD) (k := k) (rd s) [] [] t (M := M) (by simpa using hM) μ
    refine Eq.trans (dg_list_eq ?_) e
    simp [sharpL, rd_rd, List.map_map, Function.comp_def, whL_def]
  exact finrank_eq_of_graded_inverse (HomD RD k μ s t) (HomD RD k μ [] (rd s ++ t))
    (isInternal_homDeg (RD := RD) (k := k) _ _) (isInternal_homDeg (RD := RD) (k := k) _ _) F G _ _
    (fun d => map_ctxL_le μ hpre hpostF d) (fun e => map_ctxL_le μ hpreG hpostG e)
    (fun x => LinearMap.congr_fun keyGF x) (fun y => LinearMap.congr_fun keyFG y) d

omit [Field k] in
/-- **The degree of the nested cups `1 → s* s`** is `-rcx`, the negative of the exponent of
`ρ̄(E_s)` (so that bending matches `(E_s 1_λ, E_t 1_λ) = q^{rcx} (1_λ, E_{s* t} 1_λ)`). -/
theorem sdegSum_cupA_rd (μ : X) (s : List (Letter I)) :
    sdegSum RD μ (cupA (rd s)) = -rcx C (fun i => ip RD i (wt RD μ s)) s := by
  induction s using List.reverseRecOn generalizing μ with
  | nil => simp [sdegSum, rcx]
  | append_singleton s' x ih =>
    have hrd : rd (s' ++ [x]) = x.dual :: rd s' := by simp [rd_singleton]
    rw [hrd, cupA, sdegSum, List.map_cons, List.sum_cons, ← sdegSum, sdegSum_map_whL,
      Letter.dual_dual, ih, rcx_append]
    have hm : (fun k => ip RD k (wt RD μ (s' ++ [x])) - aS C k s') =
        fun k => ip RD k (wt RD μ [x]) := by
      funext k
      rw [wt_append, wt_eq_add_wX RD (wt RD μ [x]) s', ip, map_add, RD.pair_wX]
      ring
    have hm' : (fun i => ip RD i (wt RD (wt RD μ [x]) s')) = fun i => ip RD i (wt RD μ (s' ++ [x])) :=
      by funext i; rw [wt_append]
    rw [hm, hm']
    simp only [rcx, wt_cons, wt_nil, sdeg, Letter.dual, ip, pair_sh, A_self, sgn_not]
    obtain ⟨b, i⟩ := x
    cases b <;> simp <;> ring

end Bend

/-! ## Words and weights -/

section Words

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y}

theorem rd_eq_ρW (s : List (Letter I)) : rd s = ρW s := rfl

theorem rd_posW_reverse (c : List I) : rd (posW c.reverse) = negW c := by
  rw [rd_eq_ρW, ρW_posW, List.reverse_reverse]

theorem wl_ellOf_eq' (lam : X) (b : List (Letter I)) :
    wl C (RD.ellOf lam) b = fun i => ip RD i (wt RD lam b) := by
  funext i; rw [RD.wl_ellOf, wt_eq_add_wX, add_comm]

end Words

/-! ## `HOM_U(1_λ, E_u 1_λ)` -/

section OneSided

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k] [DecidableEq I] [Finite I] (hSL : SimplyLaced C)

/-- `dim HOM_U(1_μ, E_u 1_μ)_t` as the value of the functional `homDim` on `[E_u 1_μ]`. -/
theorem finrank_eq_homDim {μ : X} (u : List (Letter I)) (hu : wt RD μ u = μ) (t : ℤ) :
    (finrank k (HomD RD k μ [] u t) : ℤ) =
      homDim hSL (nfObj RD k μ μ [] rfl t) (eC RD k μ μ u hu) := by
  have := homDim_T_eC (k := k) hSL [] u rfl hu t 0
  rw [sub_zero, LaurentPolynomial.T_zero, one_smul] at this
  exact this.symm

variable (RD k) in
/-- The statement "`gdim HOM_U(1_μ, E_u 1_μ) = π (1_μ, E_u 1_μ)`" for one word `u`. -/
def OneSidedEq (u : List (Letter I)) : Prop :=
  ∀ μ : X, wt RD μ u = μ → ∀ t : ℤ,
    ((finrank k (HomD RD k μ [] u t) : ℤ) : ℚ) =
      (piLS C * toLS (φ C KL3.qK (KL3.cK C) (RD.ellOf μ) (ew u))).coeff t

/-- The values of `homDim` on `h • [E_u 1_μ]` in terms of the graded dimensions. -/
theorem homDim_smul_eq {μ : X} (u : List (Letter I)) (hu : wt RD μ u = μ) (t : ℤ)
    (h : LaurentPolynomial ℤ) :
    homDim hSL (nfObj RD k μ μ [] rfl t) (h • eC RD k μ μ u hu) =
      h.sum fun n c => c * (finrank k (HomD RD k μ [] u (t - n)) : ℤ) :=
  homDim_smul_eC hSL [] u rfl hu t h

include hSL in
/-- **The commutation step**: `OneSidedEq` passes from `a (-j)(+i) b` and `a b` to
`a (+i)(-j) b` (KL III Propositions 3.25, 3.26 in `K₀`, and the relation (2.4) for the form). -/
theorem oneSidedEq_comm (a b : List (Letter I)) (i j : I)
    (h1 : OneSidedEq RD k (a ++ (false, j) :: (true, i) :: b)) (h2 : OneSidedEq RD k (a ++ b)) :
    OneSidedEq RD k (a ++ (true, i) :: (false, j) :: b) := by
  intro μ hμ t
  rw [φ_comm]
  set ν := wt RD μ b with hν
  have hsplit : ∀ w, wt RD μ (a ++ w ++ b) = wt RD (wt RD ν w) a := fun w => by
    rw [wt_append, wt_append]
  have e1 : a ++ (true, i) :: (false, j) :: b = a ++ [up i, dn j] ++ b := by simp
  have e2 : a ++ (false, j) :: (true, i) :: b = a ++ [dn j, up i] ++ b := by simp
  have e3 : a ++ b = a ++ [] ++ b := by simp
  rw [e1] at hμ ⊢
  rw [e2] at h1 ⊢
  rw [e3] at h2 ⊢
  have hw1 : wt RD μ (a ++ [up i, dn j] ++ b) = μ := hμ
  have hw2 : wt RD μ (a ++ [dn j, up i] ++ b) = μ := by
    rw [hsplit, wt_dn_up_eq, ← hsplit]; exact hw1
  have fr : ∀ (u : List (Letter I)) (hu : wt RD μ u = μ) (t : ℤ),
      ((finrank k (HomD RD k μ [] u t) : ℤ) : ℚ) =
        ((homDim hSL (nfObj RD k μ μ [] rfl t) (eC RD k μ μ u hu) : ℤ) : ℚ) :=
    fun u hu t => by rw [finrank_eq_homDim hSL u hu t]
  rw [fr _ hw1]
  by_cases hji : j = i
  · subst hji
    have ha' : wt RD ν a = μ := by
      rw [← wt_up_dn RD j ν, ← hsplit]; exact hw1
    have hw3 : wt RD μ (a ++ [] ++ b) = μ := by rw [hsplit]; exact ha'
    rw [if_pos rfl]
    have hq : ((qi C KL3.qK j : (RatFunc ℚ)ˣ) : RatFunc ℚ) - (((qi C KL3.qK j)⁻¹ : (RatFunc ℚ)ˣ) :
        RatFunc ℚ) ≠ 0 := vQ_zpow_sub_inv_ne_zero (di_pos C j).ne'
    have hwl : wl C (RD.ellOf μ) b j = ip RD j ν := by rw [wl_ellOf_eq']
    rw [hwl, map_add, mul_add, HahnSeries.coeff_add, map_mul, mul_left_comm]
    have hB : ∀ t, (piLS C * toLS (φ C KL3.qK (KL3.cK C) (RD.ellOf μ) (ew (a ++ [] ++ b)))).coeff t
        = ((finrank k (HomD RD k μ [] (a ++ [] ++ b) t) : ℤ) : ℚ) := fun t => (h2 μ hw3 t).symm
    have hA := h1 μ hw2 t
    by_cases hn : 0 ≤ ip RD j ν
    · have hK := eC_EF (k := k) a b ha' rfl j hn hw1 hw2 hw3
      have hqn : qbr (qi C KL3.qK j) (ip RD j ν) = lpToQ (qn (di C j) (ip RD j ν).toNat) := by
        rw [lpToQ_qn]
        conv_lhs => rw [← Int.toNat_of_nonneg hn]
        rw [qbr_eq_qint _ hq]; rfl
      rw [hqn, coeff_toLS_lpToQ_mul, hK, map_add, homDim_smul_eq hSL, Finsupp.sum, Finsupp.sum]
      push_cast
      rw [← fr _ hw2 t, hA]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hB]; push_cast; ring
    · have hn' : ip RD j ν ≤ 0 := by omega
      have hK := eC_FE (k := k) a b ha' rfl j hn' hw1 hw2 hw3
      have hqn : qbr (qi C KL3.qK j) (ip RD j ν) = -lpToQ (qn (di C j) (-ip RD j ν).toNat) := by
        rw [lpToQ_qn, show qint (vQ ^ di C j) (-ip RD j ν).toNat =
          qbr (qi C KL3.qK j) ((-ip RD j ν).toNat : ℤ) from (qbr_eq_qint _ hq _).symm,
          Int.toNat_of_nonneg (by omega), qbr_neg, neg_neg]
      have hK' : eC RD k μ μ (a ++ [up j, dn j] ++ b) hw1 =
          eC RD k μ μ (a ++ [dn j, up j] ++ b) hw2 -
            qn (di C j) (-ip RD j ν).toNat • eC RD k μ μ (a ++ [] ++ b) hw3 := by
        rw [hK]; abel
      rw [hqn, map_neg, neg_mul, HahnSeries.coeff_neg, coeff_toLS_lpToQ_mul, hK',
        map_sub, homDim_smul_eq hSL, Finsupp.sum, Finsupp.sum]
      push_cast
      rw [← fr _ hw2 t, hA, sub_eq_add_neg]
      congr 1
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hB]; push_cast; ring
  · rw [if_neg hji, add_zero]
    have hK := eC_ij (k := k) a b i j (Ne.symm hji) (by rw [← hsplit]; exact hw1) rfl rfl hw1 hw2
    rw [hK, ← fr _ hw2]
    exact h1 μ hw2 t

/-! ## Bending, numerically -/

omit [DecidableEq I] [Finite I] in
/-- `(E_s 1_μ, E_w 1_μ) = q^{rcx} (1_μ, E_{s* w} 1_μ)`, as coefficients of `π ⟨ , ⟩`. -/
theorem coeff_sform_eq (μ : X) (s w : List (Letter I)) (t : ℤ) :
    (piLS C * toLS (UDot.KL3.sform RD (E1 RD vQ s μ) (E1 RD vQ w μ))).coeff t =
      (piLS C * toLS (φ C KL3.qK (KL3.cK C) (RD.ellOf μ) (ew (rd s ++ w)))).coeff
        (t - rcx C (wl C (RD.ellOf μ) w) s) := by
  rw [← (UDot.KL3.thm_2_7 C RD s w μ μ).1, UDot.KL3.form, formUD_E1_E1, if_pos rfl, B_ew_ew,
    map_mul, qp, toLS_vQ_zpow, mul_left_comm, ← rd_eq_ρW]
  have := HahnSeries.coeff_single_mul_add (r := (1 : ℚ))
    (x := piLS C * toLS (φ C KL3.qK (KL3.cK C) (RD.ellOf μ) (ew (rd s ++ w))))
    (a := t - rcx C (wl C (RD.ellOf μ) w) s) (b := rcx C (wl C (RD.ellOf μ) w) s)
  rw [sub_add_cancel, one_mul] at this
  exact this

omit [DecidableEq I] [Finite I] in
/-- **Bending, numerically**: `dim HOM(E_s 1_μ, E_w 1_μ)_t = dim HOM(1_μ, E_{s* w} 1_μ)_{t - rcx}`
when the left weights agree. -/
theorem finrank_bend_rcx (μ : X) (s w : List (Letter I)) (hsw : wt RD μ s = wt RD μ w) (t : ℤ) :
    finrank k (HomD RD k μ s w t) =
      finrank k (HomD RD k μ [] (rd s ++ w) (t - rcx C (wl C (RD.ellOf μ) w) s)) := by
  rw [finrank_homD_bend μ s w t, sdegSum_cupA_rd, wl_ellOf_eq', ← hsw]
  have e : t + (-rcx C (fun i => ip RD i (wt RD μ s)) s + sdegSum RD μ []) =
      t - rcx C (fun i => ip RD i (wt RD μ s)) s := by simp [sdegSum]; ring
  rw [e]

omit [DecidableEq I] [Finite I] in
theorem wt_rd_append_eq {μ : X} {s w : List (Letter I)} (hsw : wt RD μ s = wt RD μ w) :
    wt RD μ (rd s ++ w) = μ := by
  rw [wt_append, ← hsw, wt_rd]

variable (RD k) in
/-- **The nondegeneracy condition for positive sequences** (KL III, Remark after the definition
of nondegeneracy): `gdim HOM_U(E_𝐢 1_λ, E_𝐣 1_λ) = π ⟨E_𝐢 1_λ, E_𝐣 1_λ⟩` for all `λ` and all
positive sequences `𝐢 = +c`, `𝐣 = +b`. -/
def PositiveNondeg : Prop :=
  ∀ (μ : X) (c b : List I) (t : ℤ),
    ((finrank k (HomD RD k μ (posW c) (posW b) t) : ℤ) : ℚ) =
      (piLS C * toLS (UDot.KL3.sform RD (E1 RD vQ (posW c) μ) (E1 RD vQ (posW b) μ))).coeff t

omit [DecidableEq I] [Finite I] in
/-- The normally ordered words `F_c E_b = (+c^{rev})* (+b)` bend to pairs of positive sequences. -/
theorem oneSidedEq_normal (hpos : PositiveNondeg RD k) (c b : List I) :
    OneSidedEq RD k (negW c ++ posW b) := by
  intro μ hμ t
  have hrd := rd_posW_reverse c
  have hsw : wt RD μ (posW c.reverse) = wt RD μ (posW b) := by
    have h1 : wt RD (wt RD μ (posW b)) (rd (posW c.reverse)) = μ := by
      rw [hrd, ← wt_append]; exact hμ
    have h2 : wt RD (wt RD μ (posW c.reverse)) (rd (posW c.reverse)) = μ := wt_rd RD μ _
    rw [wt_eq_add_wX] at h1 h2
    exact add_left_cancel (h2.trans h1.symm)
  set r := rcx C (wl C (RD.ellOf μ) (posW b)) (posW c.reverse)
  have e1 := finrank_bend_rcx (k := k) μ (posW c.reverse) (posW b) hsw (t + r)
  rw [add_sub_cancel_right, hrd] at e1
  have e2 := hpos μ c.reverse b (t + r)
  rw [coeff_sform_eq, add_sub_cancel_right, hrd] at e2
  rw [← e1]
  exact e2

include hSL in
/-- `gdim HOM_U(1_μ, E_u 1_μ) = π (1_μ, E_u 1_μ)` for all signed sequences `u`, given the
positive case. -/
theorem oneSidedEq_all (hpos : PositiveNondeg RD k) (u : List (Letter I)) : OneSidedEq RD k u := by
  induction u using normal_induction with
  | hN c b => exact oneSidedEq_normal hpos c b
  | hS a i j b h1 h2 => exact oneSidedEq_comm hSL a b i j h1 h2

include hSL in
/-- **KL III, Remark after the definition of nondegeneracy** (TeX l. 4632): "Nondegeneracy holds
if the above condition is true for all `λ ∈ X` and all pairs of positive sequences `𝐢, 𝐣`"
(simply-laced, `I` finite, `𝕜` a field). -/
theorem calculusNondeg_of_positive (hpos : PositiveNondeg RD k) : CalculusNondeg RD k := by
  intro μ s w t
  by_cases hsw : wt RD μ s = wt RD μ w
  · rw [finrank_bend_rcx μ s w hsw t, coeff_sform_eq]
    exact oneSidedEq_all hSL hpos (rd s ++ w) μ (wt_rd_append_eq hsw) _
  · exact calculusNondeg_cond_of_wt_ne hsw t

omit [DecidableEq I] [Finite I] in
/-- The converse: `CalculusNondeg` contains the positive case. -/
theorem positive_of_calculusNondeg (h : CalculusNondeg RD k) : PositiveNondeg RD k :=
  fun μ c b t => h μ (posW c) (posW b) t

include hSL in
/-- **KL III Theorem 1.2 / Proposition 1.4, reduced to positive sequences**: if
`gdim HOM_U(E_𝐢 1_λ, E_𝐣 1_λ) = π ⟨E_𝐢 1_λ, E_𝐣 1_λ⟩` for all `λ` and all positive `𝐢, 𝐣`, and
Proposition 2.5 holds, then `γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))` is bijective (simply-laced,
`I` finite, `𝕜` a field). -/
theorem gammaUA'_bijective_of_positive (hpos : PositiveNondeg RD k)
    (h25 : UDot.KL3.FormNondeg RD) (lam ρ : X) :
    Function.Bijective (gammaUA' (RD := RD) (k := k) hSL lam ρ) :=
  gammaUA'_bijective hSL (calculusNondeg_of_positive hSL hpos) h25 lam ρ

end OneSided

end Categorification.KL3.Diagram
