/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftCurls
import Categorification.Diagrams.KL3.LocalizationDots

/-!
# The right curl relation under the weight shift of `U′`

Part of the proof that the weight shift of the localized 2-category `U′` respects its defining
relations (Webster arXiv:1309.3796v2, Proposition 3.30), under Webster's hypothesis
`a i - b i = -⟨i, δ⟩`.

## Main results

* `shift_bubR`: the image of a bubble to the right of an upward strand.
* `Cz_eq`: the image of a right curl with `z` dots on its downward strand, computed by induction
  on `z ∈ ℤ` from the curl relation of `U` and invertibility of the upward dot in `U′`.
* `shift_rel_curlR`: the right curl relation holds for the images of the weight shift.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (δ : X) (a b : I → ℤ)

theorem shiftObj_whisker (A u : Obj (psig RD)) (v : List (psig RD).Colour) :
    (shiftMap RD δ).obj ((incl RD).obj (A.whisker u v)) =
      ((shiftMap RD δ).obj ((incl RD).obj A)).whisker ((shiftMap RD δ).obj ((incl RD).obj u))
        ((shiftMap RD δ).word ((incl RD).word v)) := by
  rw [(incl RD).obj_whisker, (shiftMap RD δ).obj_whisker]

theorem shiftU_map_whisker {A B : Obj (psig RD)} (d : A ⟶ B) (u : Obj (psig RD))
    (v : List (psig RD).Colour) (hw : A.WhiskerOK u v) :
    (shiftU RD k δ a b).map (Diagram.whisker d u v hw) =
      eqToHom (congrArg (presLoc RD k).obj (shiftObj_whisker RD δ A u v)) ≫
        (presLoc RD k).whisk ((shiftU RD k δ a b).map d)
          ((shiftMap RD δ).obj ((incl RD).obj u)) ((shiftMap RD δ).word ((incl RD).word v)) ≫
        eqToHom (congrArg (presLoc RD k).obj (shiftObj_whisker RD δ B u v)).symm := by
  show (shiftFree RD k δ a b).map ((incl RD).toLayerMap.map (Diagram.whisker d u v hw)) = _
  rw [(incl RD).whiskerData.map_whisker (i := ()) d u v trivial hw, Diagram.cast_eq,
    Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
    (LocalMap.ofGen_whiskerData (shiftMap RD δ) (shiftImg RD k δ a b)).functor_map_whisker
      (i := ()) _ _ _ trivial]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

theorem freeLift_shiftU_whisker {A B : Obj (psig RD)} (f : LinDiagram k A B) (u : Obj (psig RD))
    (v : List (psig RD).Colour) (hw : A.WhiskerOK u v) :
    (freeLift k (shiftU RD k δ a b)).map (LinDiagram.whisker f u v hw) =
      eqToHom (congrArg (presLoc RD k).obj (shiftObj_whisker RD δ A u v)) ≫
        (presLoc RD k).whisk ((freeLift k (shiftU RD k δ a b)).map f)
          ((shiftMap RD δ).obj ((incl RD).obj u)) ((shiftMap RD δ).word ((incl RD).word v)) ≫
        eqToHom (congrArg (presLoc RD k).obj (shiftObj_whisker RD δ B u v)).symm := by
  let T : ((presLoc RD k).obj ((shiftMap RD δ).obj ((incl RD).obj A)) ⟶
        (presLoc RD k).obj ((shiftMap RD δ).obj ((incl RD).obj B))) →ₗ[k]
      ((presLoc RD k).obj ((shiftMap RD δ).obj ((incl RD).obj (A.whisker u v))) ⟶
        (presLoc RD k).obj ((shiftMap RD δ).obj ((incl RD).obj (B.whisker u v)))) :=
    { toFun := fun x => eqToHom (congrArg (presLoc RD k).obj (shiftObj_whisker RD δ A u v)) ≫
        (presLoc RD k).whisk x ((shiftMap RD δ).obj ((incl RD).obj u))
          ((shiftMap RD δ).word ((incl RD).word v)) ≫
        eqToHom (congrArg (presLoc RD k).obj (shiftObj_whisker RD δ B u v)).symm
      map_add' := fun x y => by
        simp only [(presLoc RD k).whisk_add, Preadditive.add_comp, Preadditive.comp_add]
      map_smul' := fun r x => by
        simp only [(presLoc RD k).whisk_smul, Linear.smul_comp, Linear.comp_smul,
          RingHom.id_apply] }
  exact freeLift_map_mapDomain (F := shiftU RD k δ a b) (G := shiftU RD k δ a b)
    (fun d => Diagram.whisker d u v hw) T
    (fun d => shiftU_map_whisker RD k δ a b d u v hw) f

theorem freeLift_cast {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟] [Linear k 𝒟]
    (F : Obj (psig RD) ⥤ 𝒟) {A B A' B' : Obj (psig RD)} (f : LinDiagram k A B)
    (hA : A = A') (hB : B = B') :
    (freeLift k F).map (LinDiagram.cast f hA hB) =
      eqToHom (congrArg F.obj hA).symm ≫ (freeLift k F).map f ≫ eqToHom (congrArg F.obj hB) := by
  subst hA hB; simp

theorem freeLift_shiftU_eq_shiftEnd (lam : X) (β : LEnd RD k (ob RD lam [])) :
    (freeLift k (shiftU RD k δ a b)).map β =
      eqToHom (congrArg (presLoc RD k).obj (shiftMap_ob RD δ lam [])) ≫
        shiftEnd RD k δ a b lam β ≫
          eqToHom (congrArg (presLoc RD k).obj (shiftMap_ob RD δ lam [])).symm := by
  rw [shiftEnd_apply, freeLift_shiftFree_inclLin]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp]
  erw [Category.comp_id]

/-- The image of a bubble to the right of an upward strand. -/
theorem shift_bubR (lam : X) (i : I) (β : LEnd RD k (ob RD lam []))
    (g : End ((pres RD k).obj (ob RD (lam + δ) [])))
    (hβ : shiftEnd RD k δ a b lam β = (toLoc RD k).map g) :
    eqToHom (shiftFree_obj_ob RD k δ a b lam [up i]).symm ≫
        (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k (bubR RD k lam [up i] β)) ≫
          eqToHom (shiftFree_obj_ob RD k δ a b lam [up i]) =
      (toLoc RD k).map (bubRU RD k (lam + δ) (up i) g) := by
  have ok0 := (shiftMap RD δ).whiskerOK ((incl RD).whiskerOK (whiskerOK_right RD lam [up i]))
  rw [freeLift_shiftFree_inclLin, bubR, freeLift_cast, freeLift_shiftU_whisker,
    freeLift_shiftU_eq_shiftEnd, hβ, (presLoc RD k).whisk_comp, (presLoc RD k).whisk_comp,
    (presLoc RD k).whisk_eqToHom _ _ _ ok0]
  erw [whisk_toLoc RD k (lam + δ) [up i] [] [] [] rfl g _ (shiftMap_ob RD δ lam [up i])]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rw [eqToHom_refl, Category.id_comp]
  exact Category.comp_id _
  exact shiftMap_ob RD δ lam []

theorem zg_img_curlR (ν : X) (i : I) :
    zg RD k ν [up i] [up i]
        ([([up i], .cup (up i), []), ([], .cross true i i, [dn i]), ([up i], .cap (dn i), [])]
          |>.flatMap (layStep a b)) = Cz RD k ν i (b i + -a i) := by
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil]
  erw [zg_cons_self ν _ (DStep.lay ([up i], .cup (up i), [])),
    zg_cons_self ν _ (DStep.dot [up i, up i] i [] (-a i)),
    zg_cons_self ν _ (DStep.lay ([], .cross true i i, [dn i])),
    zg_cons_self ν _ (DStep.dot [up i, up i] i [] (b i)),
    zg_cons_self ν _ (DStep.lay ([up i], .cap (dn i), [])), zg_nil, Category.comp_id]
  have hc : zdot RD k ν [up i, up i] i [] (-a i) ≫
      ldg RD k ν [up i, up i, dn i] [up i, up i, dn i] [([], .cross true i i, [dn i])] =
      ldg RD k ν [up i, up i, dn i] [up i, up i, dn i] [([], .cross true i i, [dn i])] ≫
        zdot RD k ν [up i, up i] i [] (-a i) := by
    refine zdot_comp_of_one (RD := RD) (k := k) (A := [up i, up i]) (B := [])
      (A' := [up i, up i]) (B' := []) ν _ ?_ _
    rw [zdot_one, ldot, ← ldg_of]
    exact (ldg_comp RD k (A := [([up i, up i], .dot (dn i), [])])
      (B := [([], .cross true i i, [dn i])]) (by schain) (by schain)).trans
      ((congrArg (toLoc RD k).map
        (dg_swap RD k ν _ _ [] [] [] (.cross true i i) (.dot (dn i))).symm).trans
        (ldg_comp RD k (A := [([], .cross true i i, [dn i])])
          (B := [([up i, up i], .dot (dn i), [])]) (by schain) (by schain)).symm)
  show ldg RD k ν [up i] [up i, up i, dn i] [([up i], .cup (up i), [])] ≫
    zdot RD k ν [up i, up i] i [] (-a i) ≫
    ldg RD k ν [up i, up i, dn i] [up i, up i, dn i] [([], .cross true i i, [dn i])] ≫
    zdot RD k ν [up i, up i] i [] (b i) ≫
    ldg RD k ν [up i, up i, dn i] [up i] [([up i], .cap (dn i), [])] = _
  rw [reassoc_of% hc, ← Category.assoc (zdot RD k ν [up i, up i] i [] (-a i)), ← zdot_add]

/-- The right side of the right curl relation with `z` extra dots, in `U`. -/
def curlRU (ν : X) (i : I) (z : ℤ) :
    (pres RD k).obj (ob RD ν [up i]) ⟶ (pres RD k).obj (ob RD ν [up i]) :=
  -∑ f ∈ Finset.range (z - ip RD i ν + 1).toNat,
    bubRU RD k ν (up i) (cwU RD k ν i (ip RD i ν - 1 + f)) ≫
      dotsU RD k ν (up i) (z - ip RD i ν - f).toNat

theorem curlRU_succ (ν : X) (i : I) (z : ℤ) :
    curlRU RD k ν i (z + 1) =
      dotsU RD k ν (up i) 1 ≫ curlRU RD k ν i z -
        (show (pres RD k).obj (ob RD ν [up i]) ⟶ (pres RD k).obj (ob RD ν [up i]) from
          bubRU RD k ν (up i) (cwU RD k ν i z)) := by
  unfold curlRU
  rcases lt_or_ge (z + 1 - ip RD i ν) 0 with h | h
  · have h1 : (z + 1 - ip RD i ν + 1).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    have h2 : (z - ip RD i ν + 1).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    rw [h1, h2, cwU_eq_zero RD k ν i z (by omega)]
    simp
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, z - ip RD i ν + 1 = n :=
      ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    have h1 : (z + 1 - ip RD i ν + 1).toNat = n + 1 := by omega
    have h2 : (z - ip RD i ν + 1).toNat = n := by omega
    rw [h1, h2, Finset.sum_range_succ, Preadditive.comp_neg, Preadditive.comp_sum, neg_add']
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun f hf => ?_
      have hf' := Finset.mem_range.mp hf
      have e : (z + 1 - ip RD i ν - f).toNat = 1 + (z - ip RD i ν - f).toNat := by omega
      rw [e, ← dotsU_add, ← Category.assoc, bubRU_comm, Category.assoc]
    · have e1 : ip RD i ν - 1 + (n : ℤ) = z := by omega
      have e2 : (z + 1 - ip RD i ν - n).toNat = 0 := by omega
      show _ = bubRU RD k ν (up i) (cwU RD k ν i z)
      rw [e1, e2, dotsU_zero, Category.comp_id]

/-- The image of a right curl with `z` dots on its downward strand is the right side of the right
curl relation with `z` extra dots. -/
theorem Cz_eq (ν : X) (i : I) (z : ℤ) :
    Cz RD k ν i z = (toLoc RD k).map (curlRU RD k ν i z) := by
  have hX : (toLoc RD k).map (dotsU RD k ν (up i) 1) = Xu RD k ν i := rfl
  induction z using Int.induction_on with
  | zero =>
    rw [Cz, zdot_zero]
    erw [Category.id_comp]
    rw [ldg_comp RD k (A := [([], .cross true i i, [dn i])]) (B := [([up i], .cap (dn i), [])])
        (by schain) (by schain)]
    refine (ldg_comp RD k (A := [([up i], .cup (up i), [])])
        (B := [([], .cross true i i, [dn i]), ([up i], .cap (dn i), [])]) (by schain)
        (by schain)).trans ?_
    refine congrArg (toLoc RD k).map ((dg_curlR RD k i ν).trans ?_)
    simp only [curlRU, zero_sub]
  | succ n ih =>
    rw [Cz_succ, ih, Bz_eq, curlRU_succ, (toLoc RD k).map_sub, (toLoc RD k).map_comp, hX]
  | pred n ih =>
    have e1 := Cz_succ RD k ν i (-(n : ℤ) - 1)
    have e2 := congrArg (toLoc RD k).map (curlRU_succ RD k ν i (-(n : ℤ) - 1))
    rw [(toLoc RD k).map_sub, (toLoc RD k).map_comp, hX] at e2
    rw [show -(n : ℤ) - 1 + 1 = -n by ring, ih, Bz_eq] at e1
    rw [show -(n : ℤ) - 1 + 1 = -n by ring] at e2
    have e3 := sub_left_inj.mp (e1.symm.trans e2)
    have hE : Epi (Xu RD k ν i) := by unfold Xu ldg; infer_instance
    exact (cancel_epi (Xu RD k ν i)).mp e3


theorem conj_comp {𝒞 : Type*} [Category 𝒞] {x y : 𝒞} (h : x = y) (A B : x ⟶ x) :
    eqToHom h.symm ≫ (A ≫ B) ≫ eqToHom h =
      (eqToHom h.symm ≫ A ≫ eqToHom h) ≫ (eqToHom h.symm ≫ B ≫ eqToHom h) := by
  subst h; simp

theorem conj_neg_sum {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {x y : 𝒞} (h : x = y)
    {ι : Type*} (s : Finset ι) (A : ι → (x ⟶ x)) :
    eqToHom h.symm ≫ (-∑ j ∈ s, A j) ≫ eqToHom h =
      -∑ j ∈ s, (eqToHom h.symm ≫ A j ≫ eqToHom h) := by
  subst h; simp

theorem shift_dots (lam : X) (i : I) (n : ℕ) :
    eqToHom (shiftFree_obj_ob RD k δ a b lam [up i]).symm ≫
        (freeLift k (shiftFree RD k δ a b)).map
          (inclLin RD k (LinDiagram.of (dots RD lam [] (up i) [] n))) ≫
          eqToHom (shiftFree_obj_ob RD k δ a b lam [up i]) =
      (toLoc RD k).map (dotsU RD k (lam + δ) (up i) n) := by
  rw [inclLin_of, freeLift_map_of]
  show _ ≫ (shiftFree RD k δ a b).map
    (inclD RD (mkD RD lam _ (SChain.replicate n [] (up i) []))) ≫ _ = _
  rw [shiftFree_map_mkD, imgList_eq_zg, flatMap_layStep_dots,
    zg_lays (lam + δ) (SChain.replicate n [] (up i) [])]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  erw [Category.comp_id]
  rfl

theorem shift_curlR_img (lam : X) (i : I) :
    eqToHom (shiftFree_obj_ob RD k δ a b lam [up i]).symm ≫
        (freeLift k (shiftFree RD k δ a b)).map
          (inclLin RD k (LinDiagram.of (curlR RD i lam))) ≫
          eqToHom (shiftFree_obj_ob RD k δ a b lam [up i]) =
      Cz RD k (lam + δ) i (b i + -a i) := by
  rw [inclLin_of, freeLift_map_of, curlR]
  show _ ≫ (shiftFree RD k δ a b).map (inclD RD (mkD RD lam _ _)) ≫ _ = _
  rw [shiftFree_map_mkD, imgList_eq_zg, zg_img_curlR]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  erw [Category.comp_id]

theorem shift_curlR_eq (hab : ∀ i, a i - b i = -ip RD i δ) (i : I) (lam : X) :
    (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k (LinDiagram.of (curlR RD i lam))) =
      (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k (curlRHS RD k i lam)) := by
  apply (cancel_epi (eqToHom (shiftFree_obj_ob RD k δ a b lam [up i]).symm)).mp
  apply (cancel_mono (eqToHom (shiftFree_obj_ob RD k δ a b lam [up i]))).mp
  simp only [Category.assoc]
  rw [shift_curlR_img, Cz_eq, curlRHS, map_neg, map_sum, Functor.map_neg, Functor.map_sum,
    conj_neg_sum]
  have hz : b i + -a i - ip RD i (lam + δ) = -ip RD i lam := by
    rw [ip_add_shift]; have := hab i; omega
  unfold curlRU
  rw [hz, (toLoc RD k).map_neg, (toLoc RD k).map_sum]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  symm
  rw [freeLift_shiftFree_inclLin, (freeLift k (shiftU RD k δ a b)).map_comp,
    ← freeLift_shiftFree_inclLin, ← freeLift_shiftFree_inclLin, conj_comp, shift_dots,
    shift_bubR RD k δ a b lam i _ _ (shiftEnd_cwL RD k δ a b hab lam i _)]
  have e : ip RD i lam - 1 + (f : ℤ) + ip RD i δ = ip RD i (lam + δ) - 1 + f := by
    rw [ip_add_shift]; ring
  rw [e, (toLoc RD k).map_comp]

/-- **The right curl relation** (KL III, item iv)) holds for the images of the weight shift. -/
theorem shift_rel_curlR (hab : ∀ i, a i - b i = -ip RD i δ) (i : I) (lam : X) :
    (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.curlR i lam)))) = 0 := by
  show (freeLift k (shiftFree RD k δ a b)).map
    (inclLin RD k (LinDiagram.of (curlR RD i lam) - curlRHS RD k i lam)) = 0
  rw [map_sub, Functor.map_sub, sub_eq_zero]
  exact shift_curlR_eq RD k δ a b hab i lam

end Categorification.KL3.Diagram
