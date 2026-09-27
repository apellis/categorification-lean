/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftCyc

/-!
# `Γ_N` respects the relation `cycCrossR`

Cautis–Lauda arXiv:1111.1431v3, §2 (`eq_almost_cyclic`, p. 6), the relation
`cycCrossR j i μ : t_{ij}^{-1} · rotCrossR j i - downCross j i = 0` of `CL.presCL` for the `sl_n`
scalars. The right rotation is evaluated on canonical data (`canon_rotCrossR`); its normal-form
data differ from the canonical ones by relabellings of regions of the boundary objects, absorbed
by the downward crossing (`crossDn_relabel`); on the path model the rotation is `±(6.9)`
(`rotCrossRW_eq_crossDn`, `rotCrossRW_same_eq`), and `t_{ij}^{-1} (±1) = t_{ji}^{-1}`.
-/

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

set_option maxHeartbeats 2000000 in
/-- **`Γ_N` respects `cycCrossR j i μ`** (Cautis–Lauda `eq_almost_cyclic`, `sl_n` scalars):
`t_{ij}^{-1} · Γ(rotCrossR j i) = Γ(downCross j i)`, where `Γ(downCross j i) = t_{ji}^{-1} · (6.9)`. -/
theorem evalB_cycCrossR (j i : Fin m) (μ s : Wt m) (hs : s = (ob RD μ [dn j, dn i]).start)
    (v : List (psig RD).Colour) (ha : WOK N s ((ob RD μ [dn j, dn i]).word ++ v))
    (hb : WOK N s ((ob RD μ [dn i, dn j]).word ++ v)) :
    evalB K N (gammaDn K m) s v ha hb
      ((((((CL.Sln.slnScalars K m).t i j)⁻¹ : Kˣ) : K) • LinDiagram.of (rotCrossR RD j i μ) -
        LinDiagram.of (downCross RD j i μ))) = 0 := by
  have hμ : μ = sh RD (up j) + (sh RD (up i) + s) := by
    rw [hs]
    show μ = sh RD (up j) + (sh RD (up i) + (sh RD (dn j) + (sh RD (dn i) + μ)))
    rw [sh_dn', sh_dn']
    abel
  subst hμ
  rw [map_sub, map_smul, evalB_downCross (gammaDn K m) j i _ s v ha hb, evalB_of]
  have e₁ : (ob RD (sh RD (up j) + (sh RD (up i) + s)) [dn j, dn i]).word ++ v =
      (⟨dn j, sh RD (up j) + s⟩ :: ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩ :: v :
        List (WCol m)) := by
    simp only [ob_word, wd, wt, List.cons_append, List.nil_append, sh_dn']
    abel_nf
  have e₂ : (ob RD (sh RD (up j) + (sh RD (up i) + s)) [dn i, dn j]).word ++ v =
      (⟨dn i, sh RD (up i) + s⟩ :: ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v :
        List (WCol m)) := by
    simp only [ob_word, wd, wt, List.cons_append, List.nil_append, sh_dn']
    abel_nf
  have ha' := e₁ ▸ ha
  have hb' := e₂ ▸ hb
  have el : (Diagram.layers (rotCrossR RD j i (sh RD (up j) + (sh RD (up i) + s)))).map
      (dataV v) = ([([⟨dn j, sh RD (up j) + s⟩, ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩],
         .cup ⟨up j, sh RD (up i) + s⟩, v),
       ([⟨dn j, sh RD (up j) + s⟩, ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩,
          ⟨up j, sh RD (up i) + s⟩],
         .cup ⟨up i, s⟩, ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v),
       ([⟨dn j, sh RD (up j) + s⟩, ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩],
         .gen (.cross true j i s),
         ⟨dn i, sh RD (up i) + s⟩ :: ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v),
       ([⟨dn j, sh RD (up j) + s⟩], .cap ⟨up i, sh RD (up j) + s⟩,
         ⟨up j, s⟩ :: ⟨dn i, sh RD (up i) + s⟩ :: ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v),
       ([], .cap ⟨up j, s⟩,
         ⟨dn i, sh RD (up i) + s⟩ :: ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v)] : List (LData m)) := by
    simp only [rotCrossR, layers_mkD, layList, List.map_cons, List.map_nil, dataV, lay, wd, wt,
      Shape.gen, Shape.dom, Shape.cod, List.nil_append, List.cons_append, List.append_nil,
      List.singleton_append, Letter.dual_mk]
    simp only [Bool.not_true, Bool.not_false, sh_dn']
    abel_nf
    simp only [neg_one_zsmul, neg_add_cancel_left]
  have hch : ChainW (⟨dn j, sh RD (up j) + s⟩ :: ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩ :: v)
      ([([⟨dn j, sh RD (up j) + s⟩, ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩],
         .cup ⟨up j, sh RD (up i) + s⟩, v),
       ([⟨dn j, sh RD (up j) + s⟩, ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩,
          ⟨up j, sh RD (up i) + s⟩],
         .cup ⟨up i, s⟩, ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v),
       ([⟨dn j, sh RD (up j) + s⟩, ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩],
         .gen (.cross true j i s),
         ⟨dn i, sh RD (up i) + s⟩ :: ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v),
       ([⟨dn j, sh RD (up j) + s⟩], .cap ⟨up i, sh RD (up j) + s⟩,
         ⟨up j, s⟩ :: ⟨dn i, sh RD (up i) + s⟩ :: ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v),
       ([], .cap ⟨up j, s⟩,
         ⟨dn i, sh RD (up i) + s⟩ :: ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v)] : List (LData m)) (⟨dn i, sh RD (up i) + s⟩ :: ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v) :=
    ⟨rfl, rfl, rfl, by
      show (_ :: _ :: _ : List (WCol m)) = _
      rw [add_left_comm (sh RD (up j))]
      rfl, rfl, rfl⟩
  rw [chainBD_congr (gammaDn K m) s e₁ e₂ el _ hch ha ha' hb hb', canon_rotCrossR]
  have hA : sh RD (up j) + s = wt RD (sh RD (up j) + (sh RD (up i) + s)) [dn i] := by
    simp only [wt_cons, wt_nil, sh_dn']; abel
  have hB : sh RD (up i) + s = wt RD (sh RD (up j) + (sh RD (up i) + s)) [dn j] := by
    simp only [wt_cons, wt_nil, sh_dn']; abel
  have hrel := crossDn_relabel (K := K) (N := N) j i v hA (rfl : (sh RD (up j) + (sh RD (up i) + s)) = wt RD (sh RD (up j) + (sh RD (up i) + s)) []) hB
    e₁ e₂.symm ha' ha hb' hb
  by_cases hij : i = j
  · subst hij
    rw [rotCrossRW_same_eq]
    erw [hrel]
    exact sub_self _
  · rw [rotCrossRW_eq_crossDn i j _ _ _ _ _ hij]
    split_ifs with hadj
    · rw [BHom.neg_comp', BHom.comp_neg']
      erw [hrel]
      rw [smul_neg, ← neg_smul, slnT_inv_adj ((slCartan_dot_eq_neg_one_iff i j).2 hadj)]
      exact sub_self _
    · erw [hrel]
      rw [slnT_inv_not_adj (fun h => hadj ((slCartan_dot_eq_neg_one_iff i j).1 h))]
      exact sub_self _
end Categorification.Flag

end
