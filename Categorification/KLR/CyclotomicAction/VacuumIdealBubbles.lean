/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumIdeal

/-!
# Clockwise bubbles and right curls at the vacuum lie in the ideal `I`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 3.25. The ideal `I` (`vacIdeal`) is spanned by the 2-morphisms out of the region of
`P_∅` that factor through a composite whose first strand, adjacent to the region of `P_∅`, is
downward (Webster's `F_𝐣 E_j 1_λ`). A diagram whose middle slice ends with a downward strand next
to that region therefore lies in `I` (`dg_mem_vacIdeal`). This applies to

* every clockwise bubble at the vacuum, whose middle slice is `E_i F_i 1_λ`
  (`cwReal_mem_vacIdeal`): these bubbles generate the kernel of the map from the bubble algebra
  to the coefficient ring of `Ř^λ`;
* the right curl on an upward strand next to the vacuum, whose middle slice is
  `E_i E_i F_i 1_λ` (`curlR_mem_vacIdeal`), and hence, by Cautis–Lauda's curl relation, to the
  sum `-∑_{f=0}^{λ^i} x^{λ^i - f} cw_{f - λ^i - 1}` of dotted strands times (fake) clockwise
  bubbles
  (`curlRHS_mem_vacIdeal`): this is the cyclotomic relation of `Ř^λ` on the strand next to the
  vacuum.

The 1-morphisms out of the region of `P_∅` given by a word are `vacHom`.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory TwoRep QuantumGroup StringDiagrams
open KL3.Diagram

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k]
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)

/-- The weight of the region of `P_∅`. -/
abbrev vacWt : X := (blockWeight RD Λ 0 : X)

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq I] [Nontrivial k] in
/-- Cautis–Lauda's right curl relation solved for its right-hand side:
`-∑_f x^{-n-f} cw_{n-1+f} = r_i⁻¹ · curl` in the presented 2-category (`n = ⟨i, λ⟩`). -/
theorem presCL_lin_curlRHS (S : CL.CLScalars C k) (i : I) (lam : X) :
    (CL.presCL RD k S).lin (curlRHS RD k i lam) =
      (((S.r i)⁻¹ : kˣ) : k) • (CL.presCL RD k S).diag (curlR RD i lam) := by
  have h := (CL.presCL RD k S).lin_rel_self (.inr (.curlR i lam))
  change (CL.presCL RD k S).lin (LinDiagram.of (curlR RD i lam) -
    (S.r i : k) • curlRHS RD k i lam) = 0 at h
  rw [Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of, sub_eq_zero] at h
  rw [h, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/-- The 1-morphism out of the region of `P_∅` given by the word `t` (rightmost region that of
`P_∅`), with target the region `c` on its left. -/
def vacHom (t : List (Letter I)) {c : X} (hc : KL3.Diagram.wt RD (vacWt RD Λ) t = c) :
    vacRegion hQ RD Λ ⟶ (⟨⟨c⟩⟩ : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat) :=
  (⟨ob RD (vacWt RD Λ) t, hc, ob_wf RD _ t, ob_endR RD _ t⟩ :
    StringDiagrams.Presentation.Bicat.Hom _ _)

@[simp] theorem vacHom_obj (t : List (Letter I)) {c : X}
    (hc : KL3.Diagram.wt RD (vacWt RD Λ) t = c) :
    (LinearCat.revHom (vacHom hQ RD Λ t hc)).obj = ob RD (vacWt RD Λ) t := rfl

/-- **A diagram through a downward strand next to the vacuum lies in `I`.** The class of a
normal-form diagram `E_s 1_λ ⟶ E_{s'} 1_λ` (`λ` the region of `P_∅`) whose layers pass through
the word `t ++ [F_i]` lies in `vacIdeal`. -/
theorem dg_mem_vacIdeal {s s' t : List (Letter I)} (i : I) {c : X}
    (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c) (hs' : KL3.Diagram.wt RD (vacWt RD Λ) s' = c)
    (ls ms : List (LayerData I)) (h₁ : SChain s ls (t ++ [dn i]))
    (h₂ : SChain (t ++ [dn i]) ms s') :
    (show vacHom (k := k) hQ RD Λ s hs ⟶ vacHom hQ RD Λ s' hs' from
      (CL.presCL RD k (univScalars hQ RD)).diag (mkD RD (vacWt RD Λ) (ls ++ ms)
        (h₁.append h₂))) ∈ vacIdeal hQ RD Λ _ _ := by
  set P := CL.presCL RD k (univScalars hQ RD)
  set μ := vacWt RD Λ
  have hc : KL3.Diagram.wt RD (KL3.Diagram.wt RD μ [dn i]) t = c := by
    rw [← wt_append]
    exact (h₁.wt_eq RD μ).trans hs
  let e : vacRegion hQ RD Λ ⟶ (⟨⟨(KL3.Diagram.wt RD μ [dn i] : X)⟩⟩ : RevBicat P.Bicat) :=
    vacHom hQ RD Λ [dn i] rfl
  let w' : (⟨⟨(KL3.Diagram.wt RD μ [dn i] : X)⟩⟩ : RevBicat P.Bicat) ⟶
      (⟨⟨c⟩⟩ : RevBicat P.Bicat) :=
    (⟨ob RD (KL3.Diagram.wt RD μ [dn i]) t, hc, ob_wf RD _ t, ob_endR RD _ t⟩ :
      StringDiagrams.Presentation.Bicat.Hom _ _)
  have hE : (LinearCat.revHom (e ≫ w')).obj = ob RD μ (t ++ [dn i]) := by
    refine Obj.ext ?_ ?_
    · exact (wt_append RD μ t [dn i]).symm
    · exact (wd_append RD μ t [dn i]).symm
  have hd : P.diag (mkD RD μ (ls ++ ms) (h₁.append h₂)) =
      P.diag (mkD RD μ ls h₁) ≫ P.diag (mkD RD μ ms h₂) := by
    rw [← Presentation.diag_comp, mkD_comp]
  refine Submodule.subset_span ⟨_, e, w',
    (P.diag (mkD RD μ ls h₁) ≫ eqToHom (congrArg P.obj hE.symm) :),
    (eqToHom (congrArg P.obj hE) ≫ P.diag (mkD RD μ ms h₂) :), ⟨i, μ, rfl⟩, ?_⟩
  change (P.diag (mkD RD μ ls h₁) ≫ eqToHom (congrArg P.obj hE.symm)) ≫
    (eqToHom (congrArg P.obj hE) ≫ P.diag (mkD RD μ ms h₂)) = _
  refine Eq.trans ?_ hd.symm
  rw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

omit [DecidableEq I] in
theorem mkD_congr_layers (μ : X) {t t' : List (Letter I)} {ls ls' : List (LayerData I)}
    (h : ls = ls') (h₁ : SChain t ls t') (h₂ : SChain t ls' t') :
    mkD RD μ ls h₁ = mkD RD μ ls' h₂ := by
  subst h; rfl

/-- **Clockwise bubbles at the vacuum lie in `I`**: the middle slice of `cw_m` is `E_i F_i 1_λ`,
whose strand next to the region of `P_∅` is downward. -/
theorem cwReal_mem_vacIdeal (i : I) (m : ℕ) :
    (show vacHom (k := k) hQ RD Λ [] rfl ⟶ vacHom hQ RD Λ [] rfl from
      (CL.presCL RD k (univScalars hQ RD)).diag (cwReal RD (vacWt RD Λ) i m)) ∈
        vacIdeal hQ RD Λ _ _ := by
  have h₂ : SChain ([up i] ++ [dn i])
      (List.replicate m ([up i], .dot (dn i), []) ++ [([], .cap (dn i), [])]) [] :=
    SChain.append (SChain.replicate m [up i] (dn i) []) ⟨rfl, rfl⟩
  have := dg_mem_vacIdeal hQ RD Λ (s := []) (s' := []) (t := [up i]) i rfl rfl
    [([], .cup (up i), [])] _ ⟨rfl, rfl⟩ h₂
  have e : cwReal RD (vacWt RD Λ) i m = mkD RD (vacWt RD Λ)
      ([([], .cup (up i), [])] ++
        (List.replicate m ([up i], .dot (dn i), []) ++ [([], .cap (dn i), [])]))
      ((show SChain [] [([], .cup (up i), [])] ([up i] ++ [dn i]) from ⟨rfl, rfl⟩).append h₂) :=
    mkD_congr_layers RD _ (List.append_assoc _ _ _) _ _
  change (CL.presCL RD k (univScalars hQ RD)).diag (cwReal RD (vacWt RD Λ) i m) ∈ _
  rw [e]
  exact this

/-- **The right curl on the strand next to the vacuum lies in `I`**: its middle slice is
`E_i E_i F_i 1_λ`. -/
theorem curlR_mem_vacIdeal (i : I) :
    (show vacHom (k := k) hQ RD Λ [up i] rfl ⟶ vacHom hQ RD Λ [up i] rfl from
      (CL.presCL RD k (univScalars hQ RD)).diag (curlR RD i (vacWt RD Λ))) ∈
        vacIdeal hQ RD Λ _ _ :=
  dg_mem_vacIdeal hQ RD Λ (s := [up i]) (s' := [up i]) (t := [up i, up i]) i rfl rfl
    [([up i], .cup (up i), [])] [([], .cross true i i, [dn i]), ([up i], .cap (dn i), [])]
    ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩

/-- **The cyclotomic relation at the vacuum lies in `I`**: by Cautis–Lauda's right curl
relation, `-∑_{f=0}^{λ^i} x^{λ^i - f} cw_{f - λ^i - 1}` (dots on the strand next to the vacuum
times clockwise and fake clockwise bubbles) is `r_i⁻¹` times the right curl. -/
theorem curlRHS_mem_vacIdeal (i : I) :
    (show vacHom (k := k) hQ RD Λ [up i] rfl ⟶ vacHom hQ RD Λ [up i] rfl from
      (CL.presCL RD k (univScalars hQ RD)).lin (curlRHS RD k i (vacWt RD Λ))) ∈
        vacIdeal hQ RD Λ _ _ := by
  set P := CL.presCL RD k (univScalars hQ RD)
  have h := presCL_lin_curlRHS RD (univScalars hQ RD) i (vacWt RD Λ)
  change P.lin (curlRHS RD k i (vacWt RD Λ)) ∈ _
  rw [h]
  exact Submodule.smul_mem _ _ (curlR_mem_vacIdeal hQ RD Λ i)

end

end Categorification.KLR.CyclotomicAction
