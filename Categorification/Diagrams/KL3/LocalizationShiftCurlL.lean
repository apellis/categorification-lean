/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftCurlR
import Categorification.Diagrams.KL3.LocalizationDots

/-!
# The left curl relation under the weight shift of `U′`

Part of the proof that the weight shift of the localized 2-category `U′` respects its defining
relations (Webster arXiv:1309.3796v2, Proposition 3.30), under Webster's hypothesis
`a i - b i = -⟨i, δ⟩`.

## Main results

* `CzL_eq`: the image of a left curl with `z` dots on its downward strand, computed by induction
  on `z ∈ ℤ` from the left curl relation of `U` and invertibility of the upward dot in `U′`.
* `shift_bubL`: the image of a bubble to the left of an upward strand.
* `shift_rel_curlL`: the left curl relation holds for the images of the weight shift.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

section CurlL

variable (ν : X) (i : I)

/-- The image of the left curl with `z` dots, before identification with the right side. -/
abbrev CzL (z : ℤ) : lob RD k ν [up i] ⟶ lob RD k ν [up i] :=
  ldg RD k ν [up i] [dn i, up i, up i] [([], .cup (dn i), [up i])] ≫
    ldg RD k ν [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] ≫
      zdot RD k ν [] i [up i, up i] z ≫
        ldg RD k ν [dn i, up i, up i] [up i] [([], .cap (up i), [up i])]

/-- A whiskered counterclockwise bubble with `z` dots in `U′`. -/
abbrev BLz (z : ℤ) : lob RD k ν [up i] ⟶ lob RD k ν [up i] :=
  ldg RD k ν [up i] [dn i, up i, up i] [([], .cup (dn i), [up i])] ≫
      zdot RD k ν [] i [up i, up i] z ≫
        ldg RD k ν [dn i, up i, up i] [up i] [([], .cap (up i), [up i])]

theorem CzL_succ (z : ℤ) :
    CzL RD k ν i (z + 1) = Xu RD k ν i ≫ CzL RD k ν i z + BLz RD k ν i z := by
  have F1 : zdot RD k ν [] i [up i, up i] 1 ≫
      ldg RD k ν [dn i, up i, up i] [up i] [([], .cap (up i), [up i])] =
      ldg RD k ν [dn i, up i, up i] [dn i, up i, up i] [([dn i], .dot (up i), [up i])] ≫
        ldg RD k ν [dn i, up i, up i] [up i] [([], .cap (up i), [up i])] := by
    rw [zdot_one, ldot, ← ldg_of]
    exact (ldg_comp RD k (A := [([], .dot (dn i), [up i, up i])])
      (B := [([], .cap (up i), [up i])]) (by schain) (by schain)).trans
      ((congrArg (toLoc RD k).map (dg_step RD k ν [] [] [] [up i] (s := [dn i, up i]) (t := [])
        (dg_dot_cap_up RD k (wt RD ν [up i]) i) (by schain) (by schain) (by simp [whL])
        (by simp [whL]))).trans
        (ldg_comp RD k (A := [([dn i], .dot (up i), [up i])])
          (B := [([], .cap (up i), [up i])]) (by schain) (by schain)).symm)
  have F2 : zdot RD k ν [] i [up i, up i] z ≫
      ldg RD k ν [dn i, up i, up i] [dn i, up i, up i] [([dn i], .dot (up i), [up i])] =
      ldg RD k ν [dn i, up i, up i] [dn i, up i, up i] [([dn i], .dot (up i), [up i])] ≫
        zdot RD k ν [] i [up i, up i] z := by
    refine zdot_comp_of_one (RD := RD) (k := k) (A := []) (B := [up i, up i])
      (A' := []) (B' := [up i, up i]) ν _ ?_ z
    rw [zdot_one, ldot, ← ldg_of]
    exact (ldg_comp RD k (A := [([], .dot (dn i), [up i, up i])])
      (B := [([dn i], .dot (up i), [up i])]) (by schain) (by schain)).trans
      ((congrArg (toLoc RD k).map
        (dg_swap RD k ν _ _ [] [] [up i] (.dot (dn i)) (.dot (up i)))).trans
        (ldg_comp RD k (A := [([dn i], .dot (up i), [up i])])
          (B := [([], .dot (dn i), [up i, up i])]) (by schain) (by schain)).symm)
  have F3 : ldg RD k ν [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] ≫
      ldg RD k ν [dn i, up i, up i] [dn i, up i, up i] [([dn i], .dot (up i), [up i])] =
      ldg RD k ν [dn i, up i, up i] [dn i, up i, up i] [([dn i, up i], .dot (up i), [])] ≫
        ldg RD k ν [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] +
      𝟙 _ := by
    have key := dg_stepL RD k ν (s₀ := [dn i, up i, up i]) (t₀ := [dn i, up i, up i]) [] []
      [dn i] [] (L := [([dn i], .cross true i i, []), ([dn i], .dot (up i), [up i])])
      (dg_slideLEq RD k (wt RD ν []) i) (by schain) (by schain) (by simp [whL])
    rw [ldg_comp RD k (by schain) (by schain), ldg_comp RD k (by schain) (by schain), ldg,
      ← ldg_nil RD k ν, ldg, ← Functor.map_add]
    refine congrArg (toLoc RD k).map (key.trans ?_)
    rw [map_add, ctxL_dg RD k ν (by schain) (by schain),
      ctxL_dg RD k ν (by schain) (by schain)]
    simp [whL]
  have F4 : ldg RD k ν [up i] [dn i, up i, up i] [([], .cup (dn i), [up i])] ≫
      ldg RD k ν [dn i, up i, up i] [dn i, up i, up i] [([dn i, up i], .dot (up i), [])] =
      Xu RD k ν i ≫ ldg RD k ν [up i] [dn i, up i, up i] [([], .cup (dn i), [up i])] := by
    rw [ldg_comp RD k (by schain) (by schain), ldg_comp RD k (by schain) (by schain)]
    exact congrArg (toLoc RD k).map
      (by simpa using (dg_swap RD k ν [up i] [dn i, up i, up i] [] [] [] (.cup (dn i))
        (.dot (up i))))
  simp only [CzL, BLz]
  rw [add_comm, zdot_add, Category.assoc, F1, ← Category.assoc (zdot _ _ _ _ _ _ z), F2,
    Category.assoc, ← Category.assoc _ (ldg _ _ _ _ _ [([dn i], .dot (up i), [up i])]), F3,
    Preadditive.add_comp, Category.id_comp, Preadditive.comp_add, Category.assoc,
    ← Category.assoc _ (ldg _ _ _ _ _ [([dn i, up i], .dot (up i), [])]), F4]
  simp only [Category.assoc]

/-- The whiskered counterclockwise bubble of `U′` is the image of the whiskered bubble of `U`. -/
theorem BLz_eq (z : ℤ) :
    BLz RD k ν i z =
      (toLoc RD k).map (bubLU RD k ν (up i) (ccwU RD k (wt RD ν [up i]) i z)) := by
  have hc : SChain [] [([], .cup (dn i), [])] [dn i, up i] := ⟨rfl, rfl⟩
  have hk : SChain [dn i, up i] [([], .cap (up i), [])] [] := ⟨rfl, rfl⟩
  have e : lU RD ν [] [up i] [] = lU RD ν [] [up i] [dn i, up i] :=
    congrArg (fun w => (incl RD).obj (ob RD w [])) (hc.wt_eq RD _).symm
  rw [bubLU, toLoc_plcL_whisk RD k ν [] [up i] [] [] rfl, ← zccw_eq, zccw, Presentation.whisk_comp,
    Presentation.whisk_comp, ldg, ldg,
    whisk_toLoc RD k ν [] [up i] [] [dn i, up i] (hc.wt_eq RD _) _ _ rfl,
    whisk_toLoc RD k ν [] [up i] [dn i, up i] [] (hk.wt_eq RD _) _ _ e]
  erw [plcL_dg RD k ν [] [up i] [] [dn i, up i] [([], .cup (dn i), [])],
    plcL_dg RD k ν [] [up i] [dn i, up i] [] [([], .cap (up i), [])]]
  rw [whisk_zdot RD k (wt RD ν [up i]) [] i [up i] z _ _
      (by rw [e]; exact lwhiskerOK RD ν [] [up i] [dn i, up i])
      ν [] [up i, up i] (by rw [e]; exact lob_whisker RD ν [] [up i] [dn i, up i])
      (by rw [e]; rfl)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Category.comp_id, List.map, whL, List.append_nil, List.nil_append]
  rfl

/-- The right side of the left curl relation with `z` extra dots, in `U`. -/
def curlLU (z : ℤ) : (pres RD k).obj (ob RD ν [up i]) ⟶ (pres RD k).obj (ob RD ν [up i]) :=
  ∑ g ∈ Finset.range (ip RD i (wt RD ν [up i]) + 1 + z).toNat,
    bubLU RD k ν (up i) (ccwU RD k (wt RD ν [up i]) i (-ip RD i (wt RD ν [up i]) - 1 + g)) ≫
      dotsU RD k ν (up i) (ip RD i (wt RD ν [up i]) + z - g).toNat

theorem curlLU_succ (z : ℤ) :
    curlLU RD k ν i (z + 1) =
      dotsU RD k ν (up i) 1 ≫ curlLU RD k ν i z +
        (show (pres RD k).obj (ob RD ν [up i]) ⟶ (pres RD k).obj (ob RD ν [up i]) from
          bubLU RD k ν (up i) (ccwU RD k (wt RD ν [up i]) i z)) := by
  unfold curlLU
  rcases lt_or_ge (ip RD i (wt RD ν [up i]) + 1 + z) 0 with h | h
  · have h1 : (ip RD i (wt RD ν [up i]) + 1 + (z + 1)).toNat = 0 :=
      Int.toNat_eq_zero.mpr (by omega)
    have h2 : (ip RD i (wt RD ν [up i]) + 1 + z).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    rw [h1, h2, ccwU_eq_zero RD k _ i z (by omega)]
    simp
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, ip RD i (wt RD ν [up i]) + 1 + z = n :=
      ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    have h1 : (ip RD i (wt RD ν [up i]) + 1 + (z + 1)).toNat = n + 1 := by omega
    have h2 : (ip RD i (wt RD ν [up i]) + 1 + z).toNat = n := by omega
    rw [h1, h2, Finset.sum_range_succ, Preadditive.comp_sum]
    congr 1
    · refine Finset.sum_congr rfl fun f hf => ?_
      have hf' := Finset.mem_range.mp hf
      have e : (ip RD i (wt RD ν [up i]) + (z + 1) - f).toNat =
          1 + (ip RD i (wt RD ν [up i]) + z - f).toNat := by omega
      rw [e, ← dotsU_add, ← Category.assoc, bubLU_comm, Category.assoc]
    · have e1 : -ip RD i (wt RD ν [up i]) - 1 + (n : ℤ) = z := by omega
      have e2 : (ip RD i (wt RD ν [up i]) + (z + 1) - n).toNat = 0 := by omega
      show _ = bubLU RD k ν (up i) (ccwU RD k (wt RD ν [up i]) i z)
      rw [e1, e2, dotsU_zero, Category.comp_id]

/-- The image of a left curl with `z` dots on its downward strand is the right side of the left
curl relation with `z` extra dots. -/
theorem CzL_eq (z : ℤ) : CzL RD k ν i z = (toLoc RD k).map (curlLU RD k ν i z) := by
  have hX : (toLoc RD k).map (dotsU RD k ν (up i) 1) = Xu RD k ν i := rfl
  induction z using Int.induction_on with
  | zero =>
    rw [CzL, zdot_zero]
    erw [Category.id_comp]
    rw [ldg_comp RD k (A := [([dn i], .cross true i i, [])]) (B := [([], .cap (up i), [up i])])
        (by schain) (by schain)]
    refine (ldg_comp RD k (A := [([], .cup (dn i), [up i])])
        (B := [([dn i], .cross true i i, []), ([], .cap (up i), [up i])]) (by schain)
        (by schain)).trans ?_
    refine congrArg (toLoc RD k).map ((dg_curlL RD k i ν).trans ?_)
    simp only [curlLU, add_zero]
  | succ n ih =>
    rw [CzL_succ, ih, BLz_eq, curlLU_succ, (toLoc RD k).map_add, (toLoc RD k).map_comp, hX]
  | pred n ih =>
    have e1 := CzL_succ RD k ν i (-(n : ℤ) - 1)
    have e2 := congrArg (toLoc RD k).map (curlLU_succ RD k ν i (-(n : ℤ) - 1))
    rw [(toLoc RD k).map_add, (toLoc RD k).map_comp, hX] at e2
    rw [show -(n : ℤ) - 1 + 1 = -n by ring, ih, BLz_eq] at e1
    rw [show -(n : ℤ) - 1 + 1 = -n by ring] at e2
    have e3 := add_left_inj _ |>.mp (e1.symm.trans e2)
    have hE : Epi (Xu RD k ν i) := by unfold Xu ldg; infer_instance
    exact (cancel_epi (Xu RD k ν i)).mp e3

end CurlL


section Shift

variable (δ : X) (a b : I → ℤ)

theorem whisk_cast {x x' : Obj (lsig RD)} (h : x' = x)
    (p : (presLoc RD k).obj x' = (presLoc RD k).obj x)
    (q : (presLoc RD k).obj x = (presLoc RD k).obj x')
    (f : (presLoc RD k).obj x ⟶ (presLoc RD k).obj x) {U U' : Obj (lsig RD)}
    {V V' : List (lsig RD).Colour} (hU : U = U') (hV : V = V') :
    (presLoc RD k).whisk (eqToHom p ≫ f ≫ eqToHom q) U V =
      eqToHom (by subst h hU hV; rfl) ≫ (presLoc RD k).whisk f U' V' ≫
        eqToHom (by subst h hU hV; rfl) := by
  subst h hU hV; simp

theorem shiftMap_word_wd (μ : X) (t : List (Letter I)) :
    (shiftMap RD δ).word ((incl RD).word (wd RD μ t)) = (incl RD).word (wd RD (μ + δ) t) := by
  have := congrArg Obj.word (shiftMap_ob RD δ μ t)
  simpa using this

/-- The image of a bubble to the left of an upward strand. -/
theorem shift_bubL (lam : X) (i : I) (β : LEnd RD k (ob RD (wt RD lam [up i]) []))
    (g : End ((pres RD k).obj (ob RD (wt RD (lam + δ) [up i]) [])))
    (hw : (incl RD).obj (ob RD (wt RD lam [up i] + δ) []) =
      (incl RD).obj (ob RD (wt RD (lam + δ) [up i]) []))
    (hβ : shiftEnd RD k δ a b (wt RD lam [up i]) β =
      eqToHom (congrArg (presLoc RD k).obj hw) ≫ (toLoc RD k).map g ≫
        eqToHom (congrArg (presLoc RD k).obj hw).symm) :
    eqToHom (shiftFree_obj_ob RD k δ a b lam [up i]).symm ≫
        (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k (bubL RD k lam [up i] β)) ≫
          eqToHom (shiftFree_obj_ob RD k δ a b lam [up i]) =
      (toLoc RD k).map (bubLU RD k (lam + δ) (up i) g) := by
  rw [freeLift_shiftFree_inclLin, bubL, freeLift_cast, freeLift_shiftU_whisker,
    freeLift_shiftU_eq_shiftEnd, hβ]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rw [whisk_cast RD k ((shiftMap_ob RD δ _ []).trans hw) _ _ _
    (show (shiftMap RD δ).obj ((incl RD).obj (ob RD (wt RD lam [up i]) [])) =
      lU RD (lam + δ) [] [up i] [] from (shiftMap_ob RD δ _ []).trans hw)
    (shiftMap_word_wd RD δ lam [up i])]
  rw [bubLU, toLoc_plcL_whisk RD k (lam + δ) [] [up i] [] [] rfl]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl


theorem toLoc_ccwU_cast {ν ν' : X} (h : ν = ν') (i : I) (m : ℤ) :
    (toLoc RD k).map (ccwU RD k ν i m) =
      eqToHom (congrArg (presLoc RD k).obj (congrArg (fun w => (incl RD).obj (ob RD w [])) h)) ≫
        (toLoc RD k).map (ccwU RD k ν' i m) ≫
          eqToHom (congrArg (presLoc RD k).obj
            (congrArg (fun w => (incl RD).obj (ob RD w [])) h)).symm := by
  subst h; simp

theorem zg_img_curlL (ν : X) (i : I) :
    zg RD k ν [up i] [up i]
        ([([], .cup (dn i), [up i]), ([dn i], .cross true i i, []), ([], .cap (up i), [up i])]
          |>.flatMap (layStep a b)) = CzL RD k ν i (a i + -b i) := by
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil]
  erw [zg_cons_self ν _ (DStep.lay ([], .cup (dn i), [up i])),
    zg_cons_self ν _ (DStep.dot [] i [up i, up i] (-b i)),
    zg_cons_self ν _ (DStep.lay ([dn i], .cross true i i, [])),
    zg_cons_self ν _ (DStep.dot [] i [up i, up i] (a i)),
    zg_cons_self ν _ (DStep.lay ([], .cap (up i), [up i])), zg_nil, Category.comp_id]
  have hc : zdot RD k ν [] i [up i, up i] (-b i) ≫
      ldg RD k ν [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] =
      ldg RD k ν [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] ≫
        zdot RD k ν [] i [up i, up i] (-b i) := by
    refine zdot_comp_of_one (RD := RD) (k := k) (A := []) (B := [up i, up i])
      (A' := []) (B' := [up i, up i]) ν _ ?_ _
    rw [zdot_one, ldot, ← ldg_of]
    exact (ldg_comp RD k (A := [([], .dot (dn i), [up i, up i])])
      (B := [([dn i], .cross true i i, [])]) (by schain) (by schain)).trans
      ((congrArg (toLoc RD k).map
        (dg_swap RD k ν _ _ [] [] [] (.dot (dn i)) (.cross true i i))).trans
        (ldg_comp RD k (A := [([dn i], .cross true i i, [])])
          (B := [([], .dot (dn i), [up i, up i])]) (by schain) (by schain)).symm)
  show ldg RD k ν [up i] [dn i, up i, up i] [([], .cup (dn i), [up i])] ≫
    zdot RD k ν [] i [up i, up i] (-b i) ≫
    ldg RD k ν [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] ≫
    zdot RD k ν [] i [up i, up i] (a i) ≫
    ldg RD k ν [dn i, up i, up i] [up i] [([], .cap (up i), [up i])] = _
  rw [reassoc_of% hc, ← Category.assoc (zdot RD k ν [] i [up i, up i] (-b i)), ← zdot_add]

theorem shift_curlL_img (lam : X) (i : I) :
    eqToHom (shiftFree_obj_ob RD k δ a b lam [up i]).symm ≫
        (freeLift k (shiftFree RD k δ a b)).map
          (inclLin RD k (LinDiagram.of (curlL RD i lam))) ≫
          eqToHom (shiftFree_obj_ob RD k δ a b lam [up i]) =
      CzL RD k (lam + δ) i (a i + -b i) := by
  rw [inclLin_of, freeLift_map_of, curlL]
  show _ ≫ (shiftFree RD k δ a b).map (inclD RD (mkD RD lam _ _)) ≫ _ = _
  rw [shiftFree_map_mkD, imgList_eq_zg, zg_img_curlL]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  erw [Category.comp_id]

theorem conj_sum {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {x y : 𝒞} (h : x = y)
    {ι : Type*} (s : Finset ι) (A : ι → (x ⟶ x)) :
    eqToHom h.symm ≫ (∑ j ∈ s, A j) ≫ eqToHom h =
      ∑ j ∈ s, (eqToHom h.symm ≫ A j ≫ eqToHom h) := by
  subst h; simp

theorem shift_curlL_eq (hab : ∀ i, a i - b i = -ip RD i δ) (i : I) (lam : X) :
    (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k (LinDiagram.of (curlL RD i lam))) =
      (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k (curlLHS RD k i lam)) := by
  apply (cancel_epi (eqToHom (shiftFree_obj_ob RD k δ a b lam [up i]).symm)).mp
  apply (cancel_mono (eqToHom (shiftFree_obj_ob RD k δ a b lam [up i]))).mp
  simp only [Category.assoc]
  rw [shift_curlL_img, CzL_eq, curlLHS, map_sum, Functor.map_sum, conj_sum]
  have hn : ip RD i (wt RD (lam + δ) [up i]) = ip RD i (wt RD lam [up i]) + ip RD i δ := by
    rw [wt_add_shift, ip_add_shift]
  have hz := hab i
  have hr : ip RD i (wt RD (lam + δ) [up i]) + 1 + (a i + -b i) =
      ip RD i (wt RD lam [up i]) + 1 := by omega
  unfold curlLU
  rw [hr, (toLoc RD k).map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  symm
  have hw : (incl RD).obj (ob RD (wt RD lam [up i] + δ) []) =
      (incl RD).obj (ob RD (wt RD (lam + δ) [up i]) []) :=
    congrArg (fun w => (incl RD).obj (ob RD w [])) (wt_add_shift RD δ lam [up i]).symm
  have hβ : shiftEnd RD k δ a b (wt RD lam [up i])
      (ccwL RD k (wt RD lam [up i]) i (-ip RD i (wt RD lam [up i]) - 1 + f)) =
      eqToHom (congrArg (presLoc RD k).obj hw) ≫
        (toLoc RD k).map (ccwU RD k (wt RD (lam + δ) [up i]) i
          (-ip RD i (wt RD (lam + δ) [up i]) - 1 + f)) ≫
        eqToHom (congrArg (presLoc RD k).obj hw).symm := by
    rw [shiftEnd_ccwL RD k δ a b hab]
    have e : -ip RD i (wt RD lam [up i]) - 1 + (f : ℤ) - ip RD i δ =
        -ip RD i (wt RD (lam + δ) [up i]) - 1 + f := by omega
    rw [e]
    exact toLoc_ccwU_cast RD k (wt_add_shift RD δ lam [up i]).symm i _
  rw [freeLift_shiftFree_inclLin, (freeLift k (shiftU RD k δ a b)).map_comp,
    ← freeLift_shiftFree_inclLin, ← freeLift_shiftFree_inclLin, conj_comp]
  erw [shift_bubL RD k δ a b lam i _ _ hw hβ, shift_dots]
  have e : ip RD i (wt RD (lam + δ) [up i]) + (a i + -b i) - f =
      ip RD i (wt RD lam [up i]) - f := by omega
  rw [e, (toLoc RD k).map_comp]

/-- **The left curl relation** (KL III, item iv)) holds for the images of the weight shift. -/
theorem shift_rel_curlL (hab : ∀ i, a i - b i = -ip RD i δ) (i : I) (lam : X) :
    (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.curlL i lam)))) = 0 := by
  show (freeLift k (shiftFree RD k δ a b)).map
    (inclLin RD k (LinDiagram.of (curlL RD i lam) - curlLHS RD k i lam)) = 0
  rw [map_sub, Functor.map_sub, sub_eq_zero]
  exact shift_curlL_eq RD k δ a b hab i lam

end Shift

end Categorification.KL3.Diagram
