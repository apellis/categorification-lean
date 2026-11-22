/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftDecompFE
import Categorification.Diagrams.KL3.LocalizationShiftRelDecompEF

/-!
# The relation `decompFE` under the weight shift of `U′` (Webster Prop. 3.30)

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. Under Webster's condition `a i - b i = -⟨i, δ⟩`, the image of the
decomposition relation of `1_{F_i E_i 1_λ}` (KL III Definition 3.1) under the weight shift is
`Wz (a i) ≫ (Wz (b i - a i) - Sz (b i - a i)) ≫ Wz (-b i)`, which vanishes by `Wz_eq_Sz`.

* `shift_decompTermFE`, `shift_decompSumFE`, `shift_crossRL`, `shift_idFE`: the images of the
  pieces;
* `shift_rel_decompFE`: the relation holds for the images.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

section ImgFE

variable (a b : I → ℤ) (lam : X) (i : I)

theorem Wz_comm_Edots (p : ℕ) (n : ℤ) :
    Wz RD k lam i n ≫ ldg RD k lam [dn i, up i] [dn i, up i]
        (List.replicate p ([dn i], .dot (up i), [])) =
      ldg RD k lam [dn i, up i] [dn i, up i] (List.replicate p ([dn i], .dot (up i), [])) ≫
        Wz RD k lam i n := by
  refine zdot_comp_of_one (RD := RD) (k := k) (A := []) (B := [up i]) (A' := [])
    (B' := [up i]) lam _ ?_ n
  have h := Wz_one RD k lam i
  simp only [Wz] at h
  rw [h, ldg_comp RD k (by schain) (by schain), ldg_comp RD k (by schain) (by schain)]
  refine congrArg (toLoc RD k).map ?_
  simpa using (dg_swap_dots RD k lam [] [] [] (dn i) (up i) p 1).symm

theorem ldg_FdotsFE (q : ℕ) :
    ldg RD k lam [dn i, up i] [dn i, up i] (List.replicate q ([], .dot (dn i), [up i])) =
      Wz RD k lam i q := by
  induction q with
  | zero => simp [ldg_nil]
  | succ q ih =>
    rw [List.replicate_succ', ← ldg_comp RD k (t := [dn i, up i])
      (A := List.replicate q ([], .dot (dn i), [up i])) (B := [([], .dot (dn i), [up i])])
      (by schain) (by schain), ih, ← Wz_one, Wz, Wz, Wz, ← zdot_add]
    push_cast; rw [add_comm]

theorem flat_dotCapFE (p : ℕ) :
    (dotCapFELs i p).flatMap (layStep a b) =
      (List.replicate p ([], .dot (dn i), [up i])).map DStep.lay ++
        [.dot [] i [up i] (a i), .lay ([], .cap (up i), [])] := by
  rw [dotCapFELs, List.flatMap_append, flat_rep_dot a b _ rfl]
  rfl

theorem flat_cupDotFE (q : ℕ) :
    (cupDotFELs i q).flatMap (layStep a b) =
      [.lay ([], .cup (dn i), []), .dot [] i [up i] (-b i)] ++
        (List.replicate q ([dn i], .dot (up i), [])).map DStep.lay := by
  rw [cupDotFELs, List.flatMap_append, flat_rep_dot a b _ rfl]
  rfl

theorem zg_img_dotCapFE (p : ℕ) :
    zg RD k lam [dn i, up i] [] ((dotCapFELs i p).flatMap (layStep a b)) =
      Wz RD k lam i (a i) ≫ ldg RD k lam [dn i, up i] [] (dotCapFELs i p) := by
  have hr : SChain [dn i, up i] (List.replicate p ([], .dot (dn i), [up i])) [dn i, up i] := by
    schain
  rw [flat_dotCapFE, zg_append lam _ _ (dChain_lays hr), zg_lays lam hr]
  erw [zg_dot_cons lam [] [] i [up i] (a i), zg_cons_self lam [] (.lay ([], .cap (up i), [])),
    zg_nil, Category.comp_id]
  rw [ldg_FdotsFE, ← Category.assoc, Wz, zdot_comm, Category.assoc]
  congr 1
  show Wz RD k lam i p ≫ ldg RD k lam [dn i, up i] [] [([], .cap (up i), [])] = _
  rw [← ldg_FdotsFE]
  exact ldg_comp RD k hr (by schain)

theorem zg_img_cupDotFE (q : ℕ) :
    zg RD k lam [] [dn i, up i] ((cupDotFELs i q).flatMap (layStep a b)) =
      ldg RD k lam [] [dn i, up i] (cupDotFELs i q) ≫ Wz RD k lam i (-b i) := by
  have hr : SChain [dn i, up i] (List.replicate q ([dn i], .dot (up i), [])) [dn i, up i] := by
    schain
  rw [flat_cupDotFE, zg_append lam (r := [dn i, up i]) _ _ (by dchain), zg_lays lam hr]
  erw [zg_cons_self lam _ (.lay ([], .cup (dn i), [])), zg_dot_cons lam [dn i, up i] [] i [up i],
    zg_nil, Category.comp_id]
  show (ldg RD k lam [] [dn i, up i] [([], .cup (dn i), [])] ≫ Wz RD k lam i (-b i)) ≫
    ldg RD k lam [dn i, up i] [dn i, up i] (List.replicate q ([dn i], .dot (up i), [])) = _
  rw [Category.assoc, Wz_comm_Edots, ← Category.assoc, ldg_comp RD k (by schain) hr]
  rfl

end ImgFE

section ShiftFE

variable (δ : X) (a b : I → ℤ)

theorem shift_cwL_map (hab : ∀ i, a i - b i = -ip RD i δ) (lam : X) (i : I) (m : ℤ) :
    (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k (cwL RD k lam i m)) =
      eqToHom (shiftFree_obj_ob RD k δ a b lam []) ≫
        (toLoc RD k).map (cwU RD k (lam + δ) i (m + ip RD i δ)) ≫
          eqToHom (shiftFree_obj_ob RD k δ a b lam []).symm := by
  rw [← shiftEnd_cwL RD k δ a b hab, shiftEnd_apply]
  simp

theorem shift_decompTermFE (hab : ∀ i, a i - b i = -ip RD i δ) (lam : X) (i : I) (p q : ℕ)
    (m : ℤ) :
    eqToHom (shiftFree_obj_ob RD k δ a b lam [dn i, up i]).symm ≫
        (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k
          (LinDiagram.of (dotCapFE RD lam i p) ≫ cwL RD k lam i m ≫
            LinDiagram.of (cupDotFE RD lam i q))) ≫
        eqToHom (shiftFree_obj_ob RD k δ a b lam [dn i, up i]) =
      Wz RD k (lam + δ) i (a i) ≫
        (toLoc RD k).map (dg RD k (lam + δ) [dn i, up i] [] (dotCapFELs i p) ≫
          cwU RD k (lam + δ) i (m + ip RD i δ) ≫
            dg RD k (lam + δ) [] [dn i, up i] (cupDotFELs i q)) ≫
        Wz RD k (lam + δ) i (-b i) := by
  rw [freeLift_shiftFree_inclLin, (freeLift k (shiftU RD k δ a b)).map_comp,
    (freeLift k (shiftU RD k δ a b)).map_comp, ← freeLift_shiftFree_inclLin,
    ← freeLift_shiftFree_inclLin, ← freeLift_shiftFree_inclLin, shift_cwL_map RD k δ a b hab,
    inclLin_of, inclLin_of, freeLift_map_of, freeLift_map_of, dotCapFE, cupDotFE,
    shiftFree_map_mkD, shiftFree_map_mkD, imgList_eq_zg, imgList_eq_zg]
  erw [zg_img_dotCapFE, zg_img_cupDotFE]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    eqToHom_trans, Category.comp_id, (toLoc RD k).map_comp]

theorem shift_decompSumFE (hab : ∀ i, a i - b i = -ip RD i δ) (lam : X) (i : I) :
    eqToHom (shiftFree_obj_ob RD k δ a b lam [dn i, up i]).symm ≫
        (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k (decompFESum RD k i lam)) ≫
        eqToHom (shiftFree_obj_ob RD k δ a b lam [dn i, up i]) =
      Wz RD k (lam + δ) i (a i) ≫
        (toLoc RD k).map (decompSumFE RD k (lam + δ) i (b i - a i)) ≫
        Wz RD k (lam + δ) i (-b i) := by
  have hn : -ip RD i (lam + δ) + (b i - a i) = -ip RD i lam := by
    rw [ip_add_shift]; have := hab i; omega
  rw [decompFESum, decompSumFE, hn, map_sum, Functor.map_sum, conj_sum, (toLoc RD k).map_sum,
    Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [map_sum, Functor.map_sum, conj_sum, (toLoc RD k).map_sum, Preadditive.sum_comp,
    Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [shift_decompTermFE RD k δ a b hab]
  have e : ip RD i lam - 1 + (g : ℤ) + ip RD i δ = ip RD i (lam + δ) - 1 + g := by
    rw [ip_add_shift]; ring
  rw [e]

theorem shift_crossRL (lam : X) (i : I) :
    eqToHom (shiftFree_obj_ob RD k δ a b lam [dn i, up i]).symm ≫
        (freeLift k (shiftFree RD k δ a b)).map
          (inclLin RD k (LinDiagram.of (crossr RD i i lam ≫ crossl RD i i lam))) ≫
        eqToHom (shiftFree_obj_ob RD k δ a b lam [dn i, up i]) =
      Wz RD k (lam + δ) i (a i) ≫
        (ldg RD k (lam + δ) [dn i, up i] [up i, dn i] (crossrL i i) ≫
          Yz RD k (lam + δ) i (b i - a i) ≫
            ldg RD k (lam + δ) [up i, dn i] [dn i, up i] (crosslL i i)) ≫
        Wz RD k (lam + δ) i (-b i) := by
  have e1 : crossr RD i i lam ≫ crossl RD i i lam =
      mkD RD lam (crossrL i i ++ crosslL i i) (by schain) := mkD_comp RD lam _ _ _ _
  rw [e1, inclLin_of, freeLift_map_of, shiftFree_map_mkD, imgList_eq_zg, List.flatMap_append,
    zg_append (lam + δ) (r := [up i, dn i]) _ _ (by dchain), zg_img_crossr, zg_img_crossl]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    eqToHom_trans, Category.comp_id]
  rw [← Category.assoc (zdot RD k (lam + δ) [up i] i [] (-a i)), ← zdot_add, sub_eq_add_neg]

theorem shift_idFE (lam : X) (i : I) :
    eqToHom (shiftFree_obj_ob RD k δ a b lam [dn i, up i]).symm ≫
        (freeLift k (shiftFree RD k δ a b)).map
          (inclLin RD k (LinDiagram.of (𝟙 (ob RD lam [dn i, up i])))) ≫
        eqToHom (shiftFree_obj_ob RD k δ a b lam [dn i, up i]) = 𝟙 _ := by
  have e2 : 𝟙 (ob RD lam [dn i, up i]) = mkD RD lam ([] : List (LayerData I)) rfl := by
    ext; simp
  rw [e2, inclLin_of, freeLift_map_of, shiftFree_map_mkD, imgList_eq_zg, List.flatMap_nil,
    zg_nil]
  simp

theorem shift_decompFE_eq (hab : ∀ i, a i - b i = -ip RD i δ) (i : I) (lam : X) :
    (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k
      (LinDiagram.of (𝟙 (ob RD lam [dn i, up i])) +
        LinDiagram.of (crossr RD i i lam ≫ crossl RD i i lam))) =
      (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k (decompFESum RD k i lam)) := by
  apply (cancel_epi (eqToHom (shiftFree_obj_ob RD k δ a b lam [dn i, up i]).symm)).mp
  apply (cancel_mono (eqToHom (shiftFree_obj_ob RD k δ a b lam [dn i, up i]))).mp
  simp only [Category.assoc]
  rw [shift_decompSumFE RD k δ a b hab, map_add, Functor.map_add, Preadditive.add_comp,
    Preadditive.comp_add, shift_idFE, shift_crossRL]
  have hW := Wz_eq_Sz RD k (lam + δ) i (b i - a i)
  simp only [Sz] at hW
  have h1 : 𝟙 _ = Wz RD k (lam + δ) i (a i) ≫ Wz RD k (lam + δ) i (b i - a i) ≫
      Wz RD k (lam + δ) i (-b i) := by
    rw [Wz, Wz, Wz, ← zdot_add, ← zdot_add,
      show -b i + (b i - a i) + a i = 0 by ring, zdot_zero]
    rfl
  rw [h1, hW]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.neg_comp,
    Preadditive.comp_neg, Category.assoc]
  abel

/-- **The decomposition relation `decompFE`** (KL III Definition 3.1, `eq_ident_decomp`) holds
for the images of the weight shift (Webster arXiv:1309.3796v2, Proposition 3.30). -/
theorem shift_rel_decompFE (hab : ∀ i, a i - b i = -ip RD i δ) (i : I) (lam : X) :
    (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.decompFE i lam)))) = 0 := by
  show (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k
    (LinDiagram.of (𝟙 _) + LinDiagram.of (crossr RD i i lam ≫ crossl RD i i lam) -
      decompFESum RD k i lam)) = 0
  rw [map_sub, Functor.map_sub, sub_eq_zero]
  exact shift_decompFE_eq RD k δ a b hab i lam

end ShiftFE

end Categorification.KL3.Diagram
