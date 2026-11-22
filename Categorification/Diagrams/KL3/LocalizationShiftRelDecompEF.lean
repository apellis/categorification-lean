/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftDecompEF
import Categorification.Diagrams.KL3.LocalizationShiftDownup
import Categorification.Diagrams.KL3.LocalizationShiftFakeBubbles

/-!
# The relation `decompEF` under the weight shift of `U′` (Webster Prop. 3.30)

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. Under Webster's condition `a i - b i = -⟨i, δ⟩`, the image of the
decomposition relation of `1_{E_i F_i 1_λ}` (KL III Definition 3.1) under the weight shift is
`Yz (b i) ≫ (Yz (a i - b i) - Rz (a i - b i)) ≫ Yz (-a i)`, which vanishes by `Yz_eq_Rz`.

* `shift_decompTerm`, `shift_decompSum`, `shift_crossLR`, `shift_idEF`: the images of the pieces;
* `shift_rel_decompEF`: the relation holds for the images.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

section Img

variable (a b : I → ℤ) (lam : X) (i : I)

theorem Yz_comm_Edots (p : ℕ) (n : ℤ) :
    Yz RD k lam i n ≫ ldg RD k lam [up i, dn i] [up i, dn i]
        (List.replicate p ([], .dot (up i), [dn i])) =
      ldg RD k lam [up i, dn i] [up i, dn i] (List.replicate p ([], .dot (up i), [dn i])) ≫
        Yz RD k lam i n := by
  refine zdot_comp_of_one (RD := RD) (k := k) (A := [up i]) (B := []) (A' := [up i])
    (B' := []) lam _ ?_ n
  have h := Yz_one RD k lam i
  simp only [Yz] at h
  rw [h, ldg_comp RD k (by schain) (by schain), ldg_comp RD k (by schain) (by schain)]
  refine congrArg (toLoc RD k).map ?_
  simpa using dg_swap_dots RD k lam [] [] [] (up i) (dn i) 1 p

theorem ldg_Fdots (q : ℕ) :
    ldg RD k lam [up i, dn i] [up i, dn i] (List.replicate q ([up i], .dot (dn i), [])) =
      Yz RD k lam i q := by
  induction q with
  | zero => simp [ldg_nil]
  | succ q ih =>
    rw [List.replicate_succ', ← ldg_comp RD k (t := [up i, dn i])
      (A := List.replicate q ([up i], .dot (dn i), [])) (B := [([up i], .dot (dn i), [])])
      (by schain) (by schain), ih, ← Yz_one, Yz, Yz, Yz, ← zdot_add]
    push_cast; rw [add_comm]

theorem flat_rep_dot (x : LayerData I) (hx : layStep a b x = [.lay x]) (p : ℕ) :
    (List.replicate p x).flatMap (layStep a b) = (List.replicate p x).map DStep.lay := by
  induction p with
  | zero => rfl
  | succ p ih => simp only [List.replicate_succ, List.flatMap_cons, List.map_cons, hx, ih,
      List.singleton_append]

theorem flat_dotCap (p : ℕ) :
    (dotCapEFLs i p).flatMap (layStep a b) =
      (List.replicate p ([], .dot (up i), [dn i])).map DStep.lay ++
        [.dot [up i] i [] (b i), .lay ([], .cap (dn i), [])] := by
  rw [dotCapEFLs, List.flatMap_append, flat_rep_dot a b _ rfl]
  rfl

theorem flat_cupDot (q : ℕ) :
    (cupDotEFLs i q).flatMap (layStep a b) =
      [.lay ([], .cup (up i), []), .dot [up i] i [] (-a i)] ++
        (List.replicate q ([up i], .dot (dn i), [])).map DStep.lay := by
  rw [cupDotEFLs, List.flatMap_append, flat_rep_dot a b _ rfl]
  rfl

theorem zg_img_dotCap (p : ℕ) :
    zg RD k lam [up i, dn i] [] ((dotCapEFLs i p).flatMap (layStep a b)) =
      Yz RD k lam i (b i) ≫ ldg RD k lam [up i, dn i] [] (dotCapEFLs i p) := by
  have hr : SChain [up i, dn i] (List.replicate p ([], .dot (up i), [dn i])) [up i, dn i] := by
    schain
  rw [flat_dotCap, zg_append lam _ _ (dChain_lays hr), zg_lays lam hr]
  erw [zg_dot_cons lam [] [up i] i [] (b i), zg_cons_self lam [] (.lay ([], .cap (dn i), [])),
    zg_nil, Category.comp_id]
  rw [← Category.assoc, ← Yz_comm_Edots, Category.assoc]
  erw [ldg_comp RD k hr (by schain)]
  rfl

theorem zg_img_cupDot (q : ℕ) :
    zg RD k lam [] [up i, dn i] ((cupDotEFLs i q).flatMap (layStep a b)) =
      ldg RD k lam [] [up i, dn i] (cupDotEFLs i q) ≫ Yz RD k lam i (-a i) := by
  have hr : SChain [up i, dn i] (List.replicate q ([up i], .dot (dn i), [])) [up i, dn i] := by
    schain
  rw [flat_cupDot, zg_append lam (r := [up i, dn i]) _ _ (by dchain), zg_lays lam hr]
  erw [zg_cons_self lam _ (.lay ([], .cup (up i), [])), zg_dot_cons lam [up i, dn i] [up i] i [],
    zg_nil, Category.comp_id]
  rw [ldg_Fdots, cupDotEFLs, ← ldg_comp RD k (t := [up i, dn i]) (by schain) hr, ldg_Fdots]
  simp only [Category.assoc]
  rw [Yz, Yz, zdot_comm]
  rfl

end Img

section ShiftEF

variable (δ : X) (a b : I → ℤ)

theorem shift_ccwL_map (hab : ∀ i, a i - b i = -ip RD i δ) (lam : X) (i : I) (m : ℤ) :
    (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k (ccwL RD k lam i m)) =
      eqToHom (shiftFree_obj_ob RD k δ a b lam []) ≫
        (toLoc RD k).map (ccwU RD k (lam + δ) i (m - ip RD i δ)) ≫
          eqToHom (shiftFree_obj_ob RD k δ a b lam []).symm := by
  rw [← shiftEnd_ccwL RD k δ a b hab, shiftEnd_apply]
  simp

theorem shift_decompTerm (hab : ∀ i, a i - b i = -ip RD i δ) (lam : X) (i : I) (p q : ℕ)
    (m : ℤ) :
    eqToHom (shiftFree_obj_ob RD k δ a b lam [up i, dn i]).symm ≫
        (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k
          (LinDiagram.of (dotCapEF RD lam i p) ≫ ccwL RD k lam i m ≫
            LinDiagram.of (cupDotEF RD lam i q))) ≫
        eqToHom (shiftFree_obj_ob RD k δ a b lam [up i, dn i]) =
      Yz RD k (lam + δ) i (b i) ≫
        (toLoc RD k).map (dg RD k (lam + δ) [up i, dn i] [] (dotCapEFLs i p) ≫
          ccwU RD k (lam + δ) i (m - ip RD i δ) ≫
            dg RD k (lam + δ) [] [up i, dn i] (cupDotEFLs i q)) ≫
        Yz RD k (lam + δ) i (-a i) := by
  rw [freeLift_shiftFree_inclLin, (freeLift k (shiftU RD k δ a b)).map_comp,
    (freeLift k (shiftU RD k δ a b)).map_comp, ← freeLift_shiftFree_inclLin,
    ← freeLift_shiftFree_inclLin, ← freeLift_shiftFree_inclLin, shift_ccwL_map RD k δ a b hab,
    inclLin_of, inclLin_of, freeLift_map_of, freeLift_map_of, dotCapEF, cupDotEF,
    shiftFree_map_mkD, shiftFree_map_mkD, imgList_eq_zg, imgList_eq_zg]
  erw [zg_img_dotCap, zg_img_cupDot]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    eqToHom_trans, Category.comp_id, (toLoc RD k).map_comp]

theorem shift_decompSum (hab : ∀ i, a i - b i = -ip RD i δ) (lam : X) (i : I) :
    eqToHom (shiftFree_obj_ob RD k δ a b lam [up i, dn i]).symm ≫
        (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k (decompEFSum RD k i lam)) ≫
        eqToHom (shiftFree_obj_ob RD k δ a b lam [up i, dn i]) =
      Yz RD k (lam + δ) i (b i) ≫
        (toLoc RD k).map (decompSumEF RD k (lam + δ) i (a i - b i)) ≫
        Yz RD k (lam + δ) i (-a i) := by
  have hn : ip RD i (lam + δ) + (a i - b i) = ip RD i lam := by
    rw [ip_add_shift]; have := hab i; omega
  rw [decompEFSum, decompSumEF, hn, map_sum, Functor.map_sum, conj_sum, (toLoc RD k).map_sum,
    Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [map_sum, Functor.map_sum, conj_sum, (toLoc RD k).map_sum, Preadditive.sum_comp,
    Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [shift_decompTerm RD k δ a b hab]
  have e : -ip RD i lam - 1 + (g : ℤ) - ip RD i δ = -ip RD i (lam + δ) - 1 + g := by
    rw [ip_add_shift]; ring
  rw [e]

theorem shift_crossLR (lam : X) (i : I) :
    eqToHom (shiftFree_obj_ob RD k δ a b lam [up i, dn i]).symm ≫
        (freeLift k (shiftFree RD k δ a b)).map
          (inclLin RD k (LinDiagram.of (crossl RD i i lam ≫ crossr RD i i lam))) ≫
        eqToHom (shiftFree_obj_ob RD k δ a b lam [up i, dn i]) =
      Yz RD k (lam + δ) i (b i) ≫
        (ldg RD k (lam + δ) [up i, dn i] [dn i, up i] (crosslL i i) ≫
          zdot RD k (lam + δ) [] i [up i] (a i - b i) ≫
            ldg RD k (lam + δ) [dn i, up i] [up i, dn i] (crossrL i i)) ≫
        Yz RD k (lam + δ) i (-a i) := by
  have e1 : crossl RD i i lam ≫ crossr RD i i lam =
      mkD RD lam (crosslL i i ++ crossrL i i) (by schain) := mkD_comp RD lam _ _ _ _
  rw [e1, inclLin_of, freeLift_map_of, shiftFree_map_mkD, imgList_eq_zg, List.flatMap_append,
    zg_append (lam + δ) (r := [dn i, up i]) _ _ (by dchain), zg_img_crossl, zg_img_crossr]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    eqToHom_trans, Category.comp_id]
  rw [← Category.assoc (zdot RD k (lam + δ) [] i [up i] (-b i)), ← zdot_add, sub_eq_add_neg]

theorem shift_idEF (lam : X) (i : I) :
    eqToHom (shiftFree_obj_ob RD k δ a b lam [up i, dn i]).symm ≫
        (freeLift k (shiftFree RD k δ a b)).map
          (inclLin RD k (LinDiagram.of (𝟙 (ob RD lam [up i, dn i])))) ≫
        eqToHom (shiftFree_obj_ob RD k δ a b lam [up i, dn i]) = 𝟙 _ := by
  have e2 : 𝟙 (ob RD lam [up i, dn i]) = mkD RD lam ([] : List (LayerData I)) rfl := by
    ext; simp
  rw [e2, inclLin_of, freeLift_map_of, shiftFree_map_mkD, imgList_eq_zg, List.flatMap_nil,
    zg_nil]
  simp

theorem shift_decompEF_eq (hab : ∀ i, a i - b i = -ip RD i δ) (i : I) (lam : X) :
    (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k
      (LinDiagram.of (𝟙 (ob RD lam [up i, dn i])) +
        LinDiagram.of (crossl RD i i lam ≫ crossr RD i i lam))) =
      (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k (decompEFSum RD k i lam)) := by
  apply (cancel_epi (eqToHom (shiftFree_obj_ob RD k δ a b lam [up i, dn i]).symm)).mp
  apply (cancel_mono (eqToHom (shiftFree_obj_ob RD k δ a b lam [up i, dn i]))).mp
  simp only [Category.assoc]
  rw [shift_decompSum RD k δ a b hab, map_add, Functor.map_add, Preadditive.add_comp,
    Preadditive.comp_add, shift_idEF, shift_crossLR]
  have hY := Yz_eq_Rz RD k (lam + δ) i (a i - b i)
  simp only [Rz] at hY
  have h1 : 𝟙 _ = Yz RD k (lam + δ) i (b i) ≫ Yz RD k (lam + δ) i (a i - b i) ≫
      Yz RD k (lam + δ) i (-a i) := by
    rw [Yz, Yz, Yz, ← zdot_add, ← zdot_add,
      show -a i + (a i - b i) + b i = 0 by ring, zdot_zero]
    rfl
  rw [h1, hY]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.neg_comp,
    Preadditive.comp_neg, Category.assoc]
  abel

/-- **The decomposition relation `decompEF`** (KL III Definition 3.1, `eq_ident_decomp`) holds
for the images of the weight shift (Webster arXiv:1309.3796v2, Proposition 3.30). -/
theorem shift_rel_decompEF (hab : ∀ i, a i - b i = -ip RD i δ) (i : I) (lam : X) :
    (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.decompEF i lam)))) = 0 := by
  show (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k
    (LinDiagram.of (𝟙 _) + LinDiagram.of (crossl RD i i lam ≫ crossr RD i i lam) -
      decompEFSum RD k i lam)) = 0
  rw [map_sub, Functor.map_sub, sub_eq_zero]
  exact shift_decompEF_eq RD k δ a b hab i lam

end ShiftEF

end Categorification.KL3.Diagram
