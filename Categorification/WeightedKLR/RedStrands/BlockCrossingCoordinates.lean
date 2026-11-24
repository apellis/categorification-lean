/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingSeam
import Categorification.WeightedKLR.RedStrands.BlockShuffleLoading
import Categorification.KLR.Crystal.IndDecomp
import Categorification.KLR.Examples.Small

/-!
# Reading the block coefficients of a diagram

Webster, arXiv:1309.3796v2, §6.1, ordinary comparison of Lemma 6.8. Use the left
parabolic basis (Khovanov–Lauda I, Proposition 2.16) successively. Its coordinates
respect multiplication by juxtaposed upper diagrams. After forgetting red dots they
reconstruct the entire juxtaposed-top column. No freeness of the standard quotient is
needed.
-/
noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra TypeA BraidedStendhalAlgebra
open scoped TensorProduct
variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "S" => stendhalQ Q Λ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ)
local notation "X" => diagrams Q Λ

private def omitRedDots (B : RedBlock I ℓ) : R B.weight →ₐ[k] diagramAlgebra Q Λ B :=
  (ofKLR k Q (Λ ∘ B.label) B.black).comp
    (relabelEquiv (redSubfamilyRelabel Q Λ B.label B.label.injective B.black)).symm.toAlgHom

private theorem omitRedDots_top_red (B : RedBlock I ℓ) (t : Seq B.weight) (a : Fin B.weight.card)
    (ha : (t.lbl a).isRight) :
    (ofKLR k Q (Λ ∘ B.label) B.black)
      ((relabelEquiv (redSubfamilyRelabel Q Λ B.label B.label.injective B.black)).symm (x a * e t)) = 0 := by
  obtain ⟨s, rfl⟩ := (Seq.map_bijective (Sum.map_injective.mpr ⟨Function.injective_id, B.label.injective⟩) B.localWeight).surjective t
  let d := redSubfamilyRelabel Q Λ B.label B.label.injective B.black
  let b := Fin.cast (Multiset.card_map B.colour B.localWeight) a
  have hb : (s.lbl b).isRight := by simpa only [Seq.map_lbl, Sum.isRight_map] using ha
  have hx : relabelEquiv d (x b) = x a := relabelHom_x d b
  have E : relabelEquiv d (e s) = e (Seq.map B.colour s) := relabelHom_e _ _
  rw [← hx, ← E, ← map_mul (relabelEquiv d), AlgEquiv.symm_apply_apply]
  exact ofKLR_x_mul_e_of_red b s hb
private theorem concat_top_red {a b : Multiset (I ⊕ Fin ℓ)}
    {D E : Type*} [Ring D] [Algebra k D] [AddCommGroup E] [Module k E]
    (v : R a →ₐ[k] D) (t : R b →ₗ[k] E)
    (hv : ∀ s j, (s.lbl j).isRight → v (x j * e s) = 0)
    (ht : ∀ s j, (s.lbl j).isRight → ∀ y, t (x j * e s * y) = 0)
    (g : R (a+b) →ₗ[k] (R a ⊗[k] R b))
    (gm : ∀ z y, g (concat S a b z * y) = z * g y) :
    ∀ (s : Seq (a+b)) j, (s.lbl j).isRight → ∀ y,
      TensorProduct.map v.toLinearMap t (g (x j * e s * y)) = 0 := by
  classical
  intro s
  by_cases hs : s ∈ concatSet a b
  · obtain ⟨p,q,rfl⟩ := mem_concatSet.1 hs
    rw [Seq.forall_pos]
    constructor
    · intro j hj y
      have hc : concat S a b ((x j * e p) ⊗ₜ e q) = x (Seq.posL b j) * e (p.append q) := by
        simpa [ψw, shiftWord, pol_X] using concat_pol_ψw_e (Q := S) (MvPolynomial.X j) 1
          (α := []) (α' := []) (by simp) (by simp) p q
      rw [← hc, gm]
      have hr := hv p j (by simpa only [Seq.lbl, Seq.append_posL] using hj)
      generalize g y = z
      induction z using TensorProduct.inductionOn with
      | tmul l r => simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul,
          AlgHom.toLinearMap_apply, map_mul v (x j * e p) l, hr, zero_mul, TensorProduct.zero_tmul]
      | add x y hx hy => rw [mul_add, map_add, hx, hy, add_zero]
    · intro j hj y
      have hc : concat S a b (e p ⊗ₜ (x j * e q)) = x (Seq.posR a j) * e (p.append q) := by
        simpa [ψw, shiftWord, pol_X] using concat_pol_ψw_e (Q := S) 1 (MvPolynomial.X j)
          (α := []) (α' := []) (by simp) (by simp) p q
      rw [← hc, gm]
      have hr := ht q j (by simpa only [Seq.lbl, Seq.append_posR] using hj)
      generalize g y = z
      induction z using TensorProduct.inductionOn with
      | tmul l r => simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul, hr, TensorProduct.tmul_zero]
      | add x y hx hy => rw [mul_add, map_add, hx, hy, add_zero]
  · intro j _ y
    have fix (z) : g (oneConcat S a b * z) = g z := by simpa only [concat_one, one_mul] using gm 1 z
    rw [← fix, x_mul_e, ← mul_assoc, ← mul_assoc, oneConcat, eSum_mul_e, ite_eq_right_iff.mpr (fun hc => (hs hc).elim), zero_mul, zero_mul, map_zero, map_zero]

private theorem omit_read (B : RedBlock I ℓ) (hQ : KLRSymm Q) (u : diagramAlgebra Q Λ B) :
    omitRedDots Q Λ B (readBlock Q Λ B u) = u := by
  let bs := BraidedStendhalAlgebra.basis (Λ := Λ ∘ B.label) (ν := B.black) hQ (canWord _)
    (fun w => ⟨isReduced_canWord _ w,wordProd_canWord _ w⟩)
  apply LinearMap.congr_fun (f := ((omitRedDots Q Λ B).comp (readBlock Q Λ B)).toLinearMap)
    (g := LinearMap.id) _ u
  apply bs.ext; intro b
  simp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, LinearMap.id_apply, omitRedDots, readBlock,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
  rw [show bs b = _ from BraidedStendhalAlgebra.basis_apply hQ _ _ b, toKLR_ofKLR_std _ _ _ b.2]

private abbrev KillsRed {w : Multiset (I ⊕ Fin ℓ)} {D : Type*} [Ring D] [Algebra k D]
    (H : R w →ₙₐ[k] D) := ∀ (i : Seq w) (a : Fin w.card), (i.lbl a).isRight → H (x a * e i) = 0

private theorem read_omit {w : RedBlock I ℓ} {D : Type*} [Ring D] [Algebra k D]
    (H : R w.weight →ₙₐ[k] D) (hH : KillsRed Q Λ H) (z : R w.weight) :
    H (readBlock Q Λ w (omitRedDots Q Λ w z)) = H z := by
  let r := relabelEquiv (redSubfamilyRelabel Q Λ w.label w.label.injective w.black)
  let F := H.comp r.toAlgHom.toNonUnitalAlgHom
  let B := (toKLR k Q (Λ ∘ w.label) w.black).comp (ofKLR k Q (Λ ∘ w.label) w.black)
  have eqB : LinearMap.ofClass (F.comp B.toNonUnitalAlgHom) = LinearMap.ofClass F := by
    apply ext_of_mul _ _ (map_mul (F.comp B.toNonUnitalAlgHom)) (map_mul F)
    · change F (B 1) = F 1; rw [map_one]
    · intro i; exact congrArg F (toKLR_ofKLR_e i)
    · intro a
      change F (B (x a)) = F (x a)
      rw [show B (x a) = _ from toKLR_ofKLR_x a]
      have sep (u : KLRAlgebra k (stendhalQ Q (Λ ∘ w.label)) w.localWeight) :
          F u = ∑ i : Seq w.localWeight, F (u * e i) := by rw [← map_sum, ← Finset.mul_sum, sum_e, mul_one]
      rw [sep (KLRAlgebra.blackDot a), sep (x a)]
      apply Finset.sum_congr rfl; intro i _
      rw [KLRAlgebra.blackDot, mul_assoc, KLRAlgebra.blackIdem_mul_e]
      cases he : i.lbl a with
      | inl j => simp
      | inr j =>
        have hv : ((Seq.map w.colour i).lbl (Fin.cast (Multiset.card_map w.colour w.localWeight).symm a)).isRight := by
          simp only [Seq.map_lbl, Fin.cast_cast, Fin.cast_eq_self, he]; rfl
        have hz := hH _ _ hv
        simp only [Sum.isLeft_inr, Bool.false_eq_true, ite_false, mul_zero, map_zero]
        change 0 = H (r (x a * e i))
        rw [map_mul, show r (x a) = _ from relabelHom_x _ _, show r (e i) = _ from relabelHom_e _ _]
        exact hz.symm
    · intro j _; exact congrArg F (toKLR_ofKLR_ψ j)
  obtain ⟨z,rfl⟩ := r.surjective z
  change H (r (B (r.symm (r z)))) = H (r z)
  rw [AlgEquiv.symm_apply_apply]; exact LinearMap.congr_fun eqB z

private def join {a b : Multiset (I ⊕ Fin ℓ)} : R a ⊗[k] R b →ₙₐ[k] R (a+b) where
  toFun := concat S a b
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := LinearMap.map_smul _
  map_mul' := concat_mul

private abbrev leftIn (a b : Multiset (I ⊕ Fin ℓ)) :=
  (join Q Λ (a := a) (b := b)).comp Algebra.TensorProduct.includeLeft.toNonUnitalAlgHom
private abbrev rightIn (a b : Multiset (I ⊕ Fin ℓ)) :=
  (join Q Λ (a := a) (b := b)).comp Algebra.TensorProduct.includeRight.toNonUnitalAlgHom

private theorem join_pure {a b : Multiset (I ⊕ Fin ℓ)} (u : R a) (v : R b) :
    concat S a b (u ⊗ₜ v) = leftIn Q Λ a b u * rightIn Q Λ a b v := by
  change concat S a b _ = concat S a b (u ⊗ₜ 1) * concat S a b (1 ⊗ₜ v)
  rw [← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem right_mul_pure {a b : Multiset (I ⊕ Fin ℓ)} (z : R b) (u : R a) (v : R b) :
    rightIn Q Λ a b z * concat S a b (u ⊗ₜ[k] v) = leftIn Q Λ a b u * rightIn Q Λ a b (z*v) := by
  change concat S a b (1 ⊗ₜ[k] z) * concat S a b (u ⊗ₜ[k] v) = _
  rw [← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, join_pure]

private theorem kills_left_right {a b : Multiset (I ⊕ Fin ℓ)} {D : Type*} [Ring D] [Algebra k D]
    (H : R (a+b) →ₙₐ[k] D) (hh : KillsRed Q Λ H) :
    KillsRed Q Λ (H.comp (leftIn Q Λ a b)) ∧ KillsRed Q Λ (H.comp (rightIn Q Λ a b)) := by
  constructor <;> intro i j hj
  · change H (concat S a b ((x j * e i) ⊗ₜ 1)) = 0
    rw [← sum_e (Q := S) (ν := b), TensorProduct.tmul_sum, map_sum, map_sum]
    apply Finset.sum_eq_zero; intro t _
    have hc : concat S a b ((x j * e i) ⊗ₜ e t) = x (Seq.posL b j) * e (i.append t) := by
      simpa [ψw, shiftWord, pol_X] using concat_pol_ψw_e (Q := S) (MvPolynomial.X j) 1
        (α := []) (α' := []) (by simp) (by simp) i t
    rw [hc]; apply hh; simpa only [Seq.lbl, Seq.append_posL] using hj
  · change H (concat S a b (1 ⊗ₜ (x j * e i))) = 0
    rw [← sum_e (Q := S) (ν := a), TensorProduct.sum_tmul, map_sum, map_sum]
    apply Finset.sum_eq_zero; intro t _
    have hc : concat S a b (e t ⊗ₜ (x j * e i)) = x (Seq.posR a j) * e (t.append i) := by
      simpa [ψw, shiftWord, pol_X] using concat_pol_ψw_e (Q := S) 1 (MvPolynomial.X j)
        (α := []) (α' := []) (by simp) (by simp) t i
    rw [hc]; apply hh; simpa only [Seq.lbl, Seq.append_posR] using hj

private theorem binaryCoordinates (a b : Multiset (I ⊕ Fin ℓ)) (hQ : KLRSymm Q) :
    let U := Shuffle (Seq.card_add' a b)
    ∃ (g : U → R (a+b) →ₗ[k] (R a ⊗[k] R b)) (w : U → R (a+b)),
      (∀ i x y, g i (concat S a b x * y) = x * g i y) ∧
      (∀ i y s, g i (y * e s) = g i y * concatIdem (i.1 • s)) ∧
      ∀ y, oneConcat S a b * y = ∑ i, concat S a b (g i y) * w i := by
  classical
  let B := freeBasis (ν := a) (ν' := b) (stendhalQ_symm Q Λ hQ) (canWord _) (canWord _)
    (fun i => canWord _ i.1) (fun i => ⟨isReduced_canWord _ i,wordProd_canWord _ i⟩)
    (fun i => ⟨isReduced_canWord _ i,wordProd_canWord _ i⟩)
    (fun i => ⟨isReduced_canWord _ i.1,wordProd_canWord _ i.1⟩)
  let col := (LinearMap.mulLeft k (oneConcat S a b)).codRestrict (oneConcatSub S) fun y =>
    mem_oneConcatSub.2 (by change _ * (oneConcat S a b * y) = _; rw [← mul_assoc, oneConcat_idem.eq]; rfl)
  refine ⟨fun i => ((B.coord i).restrictScalars k).comp col, fun i => (B i).1, ?_, ?_, ?_⟩
  · intro i x y
    have he : col (concat S a b x * y) = x • col y := Subtype.ext (by
      change oneConcat S a b * (concat S a b x * y) = concat S a b x * (oneConcat S a b * y)
      rw [← mul_assoc, oneConcat_mul_concat, ← mul_assoc, concat_mul_oneConcat])
    change B.coord i (col _) = x * B.coord i (col y)
    rw [he, map_smul, smul_eq_mul]
  · intro i y s
    have he : col (y * e s) = ⟨(col y).1 * e s,
        mem_oneConcatSub.2 (by rw [← mul_assoc, mem_oneConcatSub.1 (col y).2])⟩ :=
      Subtype.ext (mul_assoc _ _ _).symm
    change B.coord i (col (y * e s)) = B.coord i (col y) * _
    rw [he]
    exact freeBasis_coord_mul_e (stendhalQ_symm Q Λ hQ) (canWord _) (canWord _)
      (fun i => canWord _ i.1) (fun i => ⟨isReduced_canWord _ i, wordProd_canWord _ i⟩)
      (fun i => ⟨isReduced_canWord _ i, wordProd_canWord _ i⟩)
      (fun i => ⟨isReduced_canWord _ i.1, wordProd_canWord _ i.1⟩) s i (col y)
  · intro y
    have he := congrArg Subtype.val (B.sum_repr (col y))
    change (col y).1 = ∑ i, concat S a b (B.repr (col y) i) * (B i).1
    simpa only [AddSubmonoidClass.coe_finsetSum, coe_tensor_smul] using he.symm

/-- The external product of the quotient maps kills a loading idempotent
as soon as any one of its blocks is violated. -/
private theorem projection_loadingIdem_eq_zero : ∀ Bs (s : Loadings Bs), Violated Bs s →
    projection Q Λ Bs (loadingIdem Q Λ Bs s) = 0
  | [], _, hs => False.elim hs
  | B :: Bs, s, hs => by
    change (Algebra.TensorProduct.map (violMk k Q (Λ ∘ B.label) B.black)
      (projection Q Λ Bs)) (_ ⊗ₜ[k] _) = 0
    rw [Algebra.TensorProduct.map_tmul]
    rcases hs with h | h
    · rw [violMk_e h, TensorProduct.zero_tmul]
    · rw [projection_loadingIdem_eq_zero Bs s.2 h, TensorProduct.tmul_zero]

private structure Coefficients (row : List (RedBlock I ℓ)) (D : Type*) [Ring D] [Algebra k D] where
  ι : Type
  fintype : Fintype ι
  coeff : ι → R (weightSum row) →ₗ[k] X row
  word : ι → R (weightSum row)
  bottom : ι → Seq (weightSum row) → X row
  coeff_e : ∀ j y s, coeff j (y * e s) = coeff j y * bottom j s
  bottom_spec : ∀ j s, bottom j s = 0 ∨
    ∃ v : Loadings row, ShuffleLoading row s v ∧ bottom j s = loadingIdem Q Λ row v
  coeff_mul : ∀ j x y, coeff j (juxtapose Q Λ row x * y) = x * coeff j y
  coeff_top_red : ∀ j (t : Seq (weightSum row)) a, (t.lbl a).isRight → ∀ y,
    coeff j ((x a * e t) * y) = 0
  expand : ∀ (H : R (weightSum row) →ₙₐ[k] D), KillsRed Q Λ H → ∀ y,
    H (juxtapose Q Λ row 1 * y) = ∑ j, H (juxtapose Q Λ row (coeff j y) * word j)

private def emptyCoefficients (D : Type*) [Ring D] [Algebra k D] : Coefficients Q Λ [] D := by
  let z := zeroEquiv (I ⊕ Fin ℓ) k S
  let ev := ULift.algEquiv.symm.toLinearMap.comp z.toLinearMap
  refine ⟨Unit, inferInstance, fun _ => ev, fun _ => 1, fun _ _ => 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ y s
    rw [e_eq_one, mul_one, mul_one]
  · intro _ _
    exact Or.inr ⟨PUnit.unit, trivial, rfl⟩
  · intro _ a y
    change ULift.up (z (algebraMap k _ a.down * y)) = _
    rw [map_mul, AlgEquiv.commutes]; rfl
  · intro _ _ a
    exact Fin.elim0 a
  · intro H _ y
    rw [Fintype.sum_unique]
    change H (z.symm 1 * y) = H (z.symm (z y) * 1)
    rw [map_one, AlgEquiv.symm_apply_apply, one_mul, mul_one]

private theorem univ_eq (A : Type*) (i j : Fintype A) : @Finset.univ A i = @Finset.univ A j :=
  congrArg (@Finset.univ A) (Subsingleton.elim i j)

private def consCoefficients (B : RedBlock I ℓ) (row : List (RedBlock I ℓ)) (hQ : KLRSymm Q)
    {D : Type*} [Ring D] [Algebra k D] (T : Coefficients Q Λ row D) : Coefficients Q Λ (B::row) D := by
  classical
  let a := B.weight
  let b := weightSum row
  let U := Shuffle (Seq.card_add' a b)
  letI : Fintype U := Fintype.ofFinite (Shuffle (Seq.card_add' a b))
  letI : Fintype T.ι := T.fintype
  let prodfin : Fintype (U × T.ι) := @instFintypeProd U T.ι ‹Fintype U› T.fintype
  let g := (binaryCoordinates Q Λ a b hQ).choose
  let w := (binaryCoordinates Q Λ a b hQ).choose_spec.choose
  obtain ⟨gm,ge,gw⟩ := (binaryCoordinates Q Λ a b hQ).choose_spec.choose_spec
  let v := omitRedDots Q Λ B
  let c j := TensorProduct.map v.toLinearMap (T.coeff j)
  let hcoeff (u : X (B::row)) (s) (j) : c j (TensorProduct.map (readBlock Q Λ B).toLinearMap
      (juxtapose Q Λ row) u * s) = u * c j s := by
    induction u using TensorProduct.inductionOn with
    | add u u' hu hu' => rw [map_add, add_mul, map_add, add_mul, hu, hu']
    | tmul l r =>
      induction s using TensorProduct.inductionOn with
      | add s s' hs hs' => rw [mul_add, map_add, hs, hs', map_add, mul_add]
      | tmul x y =>
        simp only [c, TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, AlgHom.toLinearMap_apply,
          map_mul, v, omit_read Q Λ B hQ, T.coeff_mul]
  have project_tmul (j : T.ι) (s : KLR.Seq B.weight) (t : KLR.Seq (weightSum row))
      (u : R B.weight ⊗[k] R (weightSum row)) :
      c j (u * ((KLRAlgebra.e s : R B.weight) ⊗ₜ[k] (KLRAlgebra.e t : R (weightSum row)))) =
        c j u * (v (e s) ⊗ₜ[k] T.bottom j t) := by
    induction u using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [c, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, T.coeff_e]
      exact congrArg (· ⊗ₜ[k] ((T.coeff j) y * T.bottom j t)) (v.map_mul x (e s))
    | add x y hx hy => simp only [add_mul, map_add, hx, hy]
  let split (s : KLR.Seq (a + b)) (hs : s ∈ concatSet a b) : KLR.Seq a × KLR.Seq b :=
    let ex := mem_concatSet.1 hs
    (ex.choose, ex.choose_spec.choose)
  have split_spec (s : KLR.Seq (a + b)) (hs : s ∈ concatSet a b) :
      (split s hs).1.append (split s hs).2 = s := (mem_concatSet.1 hs).choose_spec.choose_spec
  let bottom (ij : U × T.ι) (s : KLR.Seq (weightSum (B :: row))) : X (B :: row) :=
    if hs : ij.1.1 • s ∈ concatSet a b then
      v (e (split _ hs).1) ⊗ₜ[k] T.bottom ij.2 (split _ hs).2
    else 0
  refine ⟨U × T.ι, prodfin, fun ij => (c ij.2).comp (g ij.1),
    fun ij => rightIn Q Λ a b (T.word ij.2) * w ij.1, bottom, ?_, ?_, ?_, ?_, ?_⟩
  · intro ij y s
    change c ij.2 (g ij.1 (y * e s)) = c ij.2 (g ij.1 y) * bottom ij s
    rw [ge]
    by_cases hs : ij.1.1 • s ∈ concatSet a b
    · let p := (split (ij.1.1 • s) hs).1
      let q := (split (ij.1.1 • s) hs).2
      have hpq : p.append q = ij.1.1 • s := split_spec (ij.1.1 • s) hs
      have hcut := (congrArg (concatIdem (ν := a) (ν' := b) (Q := S)) hpq.symm).trans
        (concatIdem_append (Q := S) p q)
      rw [hcut]
      simp only [bottom, dite_eq_left hs]
      exact project_tmul ij.2 p q (g ij.1 y)
    · rw [concatIdem_of_not_mem hs, mul_zero, map_zero]
      simp only [bottom, dite_eq_right hs, mul_zero]
  · intro ij s
    by_cases hs : ij.1.1 • s ∈ concatSet a b
    · let p := (split (ij.1.1 • s) hs).1
      let q := (split (ij.1.1 • s) hs).2
      have hb : bottom ij s = v (e p) ⊗ₜ[k] T.bottom ij.2 q := by
        simp only [bottom, dite_eq_left hs, p, q]
      rcases T.bottom_spec ij.2 q with hzero | ⟨t, ht, he⟩
      · exact Or.inl (by rw [hb, hzero, TensorProduct.tmul_zero])
      · let equiv := redSubfamilyRelabel Q Λ B.label B.label.injective B.black
        let p' := equiv.equiv.symm p
        have hmap : Seq.map B.colour p' = p := equiv.equiv.apply_symm_apply p
        have hproj : v (e p) = ofKLR k Q (Λ ∘ B.label) B.black (e p') := by
          change ofKLR k Q (Λ ∘ B.label) B.black ((relabelEquiv equiv).symm (e p)) = _
          rw [relabelEquiv_symm_apply, relabelHom_e, SeqRelabel.symm_equiv]
        refine Or.inr ⟨(p', t), ⟨ij.1, q, ?_, ht⟩, ?_⟩
        · exact (split_spec _ hs).symm.trans (congrArg (·.append q) hmap.symm)
        · rw [hb, he, hproj]
          rfl
    · exact Or.inl (by simp only [bottom, dite_eq_right hs])
  · intro ij u y
    change c ij.2 (g ij.1 (concat S a b _ * y)) = _
    rw [gm]; exact hcoeff u _ _
  · intro ij s d hd y
    exact concat_top_red Q Λ v (T.coeff ij.2) (omitRedDots_top_red Q Λ B)
      (T.coeff_top_red ij.2) (g ij.1) (gm ij.1) s d hd y
  · intro H hh y
    let l := leftIn Q Λ a b
    let r := rightIn Q Λ a b
    let m := concat S a b
    let U₀ := juxtapose Q Λ row 1
    have hE : juxtapose Q Λ (B::row) 1 = r U₀ := by
      change juxtapose Q Λ (B::row) ((1 : diagramAlgebra Q Λ B) ⊗ₜ[k] (1 : X row)) = r U₀
      rw [juxtapose_tmul, map_one]; rfl
    have step (s) : H (r U₀ * m s) =
        ∑ j, H (juxtapose Q Λ (B::row) (c j s) * r (T.word j)) := by
      induction s using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, mul_add, add_mul, Finset.sum_add_distrib, hx, hy]
      | tmul x y =>
        obtain ⟨hl,hr⟩ := kills_left_right Q Λ H hh
        have hl' : H (l (readBlock Q Λ B (v x))) = H (l x) := read_omit Q Λ (H.comp l) hl x
        have hr' : H (r (U₀ * y)) = ∑ j, H (r (juxtapose Q Λ row (T.coeff j y) * T.word j)) :=
          T.expand (H.comp r) hr y
        rw [right_mul_pure Q Λ U₀ x y, map_mul, hr', Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        change _ = H (juxtapose Q Λ (B::row) (v x ⊗ₜ T.coeff j y) * r (T.word j))
        rw [juxtapose_tmul, join_pure Q Λ]
        simp only [map_mul r, map_mul H, mul_assoc]
        exact congrArg (fun t => t * (H (r (juxtapose Q Λ row (T.coeff j y))) * H (r (T.word j)))) hl'.symm
    have topFix : r U₀ * oneConcat S a b = r U₀ := concat_mul_oneConcat _
    change H (juxtapose Q Λ (B::row) 1 * y) = _
    rw [hE, ← topFix, mul_assoc, gw, Finset.mul_sum, map_sum]
    refine Eq.trans ?_ (@Fintype.sum_prod_type D U T.ι ‹Fintype U› T.fintype _ _).symm
    apply Finset.sum_congr (univ_eq U _ _); intro i _
    rw [← mul_assoc, map_mul, step, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by simp only [map_mul, mul_assoc, LinearMap.comp_apply]; rfl

private def rowCoefficients (D : Type*) [Ring D] [Algebra k D] (hQ : KLRSymm Q) :
    (row : List (RedBlock I ℓ)) → Coefficients Q Λ row D
  | [] => emptyCoefficients Q Λ D
  | B :: row => consCoefficients Q Λ B row hQ (rowCoefficients D hQ row)

section SectionCoefficient
open MvPolynomial
variable {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "A" => R μ
local notation "E" => AlgHom.comp (toKLR k Q Λ ν) (ofKLR k Q Λ ν)

private theorem coefficient_of_section {M : Type*} [AddCommGroup M] [Module k M]
    (hQ : KLRSymm Q) (F : A →ₗ[k] M)
    (hF : ∀ (s : Seq μ) (a : Fin (Multiset.card μ)), (s.lbl a).isRight → ∀ z : A, F (x a * e s * z) = 0) (y : A) :
    F (E y) = F y := by
  let ρ := canWord (Multiset.card μ)
  have hρ : ∀ w, IsReduced (Multiset.card μ) (ρ w) ∧ wordProd (Multiset.card μ) (ρ w) = w :=
    fun w => ⟨isReduced_canWord _ w,wordProd_canWord _ w⟩
  let B := lbasis (stendhalQ_symm Q Λ hQ) ρ hρ
  suffices H : F.comp (E).toLinearMap = F from LinearMap.congr_fun H y
  apply B.ext
  rintro ⟨s,w,d⟩
  rw [show B _ = _ from lbasis_apply (stendhalQ_symm Q Λ hQ) ρ hρ (s,w,d), LinearMap.comp_apply]
  let t := wordProd (Multiset.card μ) (ρ w) • s
  let u : A := ψw (ρ w) * e s
  have support : e t * u = u := by
    dsimp [t,u]; rw [← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  have clean : E u = u := by simp only [u,map_mul,AlgHom.comp_apply,toKLR_ofKLR_ψw,toKLR_ofKLR_e]
  have changeTop : pol (monomial d 1) * ψw (ρ w) * e s = (pol (monomial d 1) * e t : A) * u := by
    rw [mul_assoc,mul_assoc _ (e t),support]
  rw [changeTop]; change F (E ((pol (monomial d 1) * e t : A) * u)) = _
  rw [map_mul,clean]
  by_cases good : ∀ a, (t.lbl a).isRight → d a = 0
  · have H := toKLR_ofKLR_std (k := k) (Q := Q) (Λ := Λ) [] d t good
    simp only [ψw_nil,one_mul] at H
    rw [show E (pol (monomial d 1) * e t) = _ from H]
  · push Not at good
    obtain ⟨a,ha,hd⟩ := good
    have H := ofKLR_std_eq_zero (k := k) (Q := Q) (Λ := Λ) [] d t a ha hd
    simp only [ψw_nil,one_mul] at H
    rw [AlgHom.comp_apply,H,map_zero,zero_mul,map_zero]
    have hle : Finsupp.single a 1 ≤ d := by rw [Finsupp.single_le_iff]; omega
    have split : (monomial d 1 : MvPolynomial (Fin (Multiset.card μ)) k) = MvPolynomial.X a * monomial (d-Finsupp.single a 1) 1 := by
      rw [MvPolynomial.X,monomial_mul_monomial,one_mul,add_comm,tsub_add_cancel_of_le hle]
    rw [split,map_mul pol,pol_X,mul_assoc _ _ (e t),(e_commute_pol t _).eq.symm,← mul_assoc (x a),mul_assoc _ _ u,hF t a ha]
end SectionCoefficient

/-- Parabolic coordinates of the juxtaposed-top column (Webster, arXiv:1309.3796v2,
Proposition 6.4 and proof of Lemma 6.8; Khovanov–Lauda I, Proposition 2.16). Multiplying
above the seam multiplies each coefficient. A bottom loading acts on each
coefficient through the split projector for its shuffle. Restacking the coefficients recovers the
whole column after imposing red dots, before either kind of violation. -/
theorem exists_blockStack_coordinates_with_bottom (hQ : KLRSymm Q) (L M : List (Fin ℓ × Multiset I))
    (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν) :
    let row := adjacentRow L M f β
    let μ := stendhalWeight ℓ ν
    let G := affineStackBlocks Q Λ L M f β h
    let π := ofKLR k Q Λ ν
    let bad := fun s : KLR.Seq μ => IsViolated s ∨
      (redWord s = L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst ∧
        (fun r i => boundaryCount (cut (f 0) (f 1) r) i row) < adjacentBlockRoot (f 0) (f 1) s)
    ∃ n, ∃ (g : Fin n → R μ →ₗ[k] X row) (w : Fin n → R μ)
      (bottom : Fin n → Seq μ → X row),
      (∀ j x y, g j (G x * y) = x * g j y) ∧
      (∀ j y s, g j (y * e s) = g j y * bottom j s) ∧
      (∀ j y, g j (toKLR k Q Λ ν (π y)) = g j y) ∧
      (∀ j s, bottom j s = 0 ∨ ∃ v : Loadings row,
        ShuffleLoading row (Seq.cast h.symm s) v ∧ bottom j s = loadingIdem Q Λ row v) ∧
      (∀ j y s z, bad s → projection Q Λ row (g j (y * e s * z)) = 0) ∧
      ∀ y, π (G 1 * y) = ∑ j, π (G (g j y) * w j) := by
  classical
  intro row μ G π bad
  let T := rowCoefficients Q Λ (BraidedStendhalAlgebra k Q Λ ν) hQ row
  let : Fintype T.ι := T.fintype
  let e := Fintype.equivFin T.ι
  let b := castKLR S h
  let H := (π.comp b.toAlgHom).toNonUnitalAlgHom
  have hh : KillsRed Q Λ H := by
    intro i a ha
    change π (b (x a * KLRAlgebra.e i)) = 0
    rw [map_mul, show b (x a) = _ from castKLR_x h a, show b (KLRAlgebra.e i) = _ from castKLR_e h i]
    apply ofKLR_x_mul_e_of_red
    have castLabel {u v : Multiset (I ⊕ Fin ℓ)} (he : u = v) (s : Seq u) (t : Fin u.card) :
        (Seq.cast he s).lbl (Fin.cast (congrArg Multiset.card he) t) = s.lbl t := by subst v; rfl
    rwa [castLabel]
  have cast_back (s : Seq μ) : Seq.cast h (Seq.cast h.symm s) = s :=
    (show ∀ {w w' : Multiset (I ⊕ Fin ℓ)} (hw : w = w') (t : Seq w'),
      Seq.cast hw (Seq.cast hw.symm t) = t from fun {w w'} hw t => by subst w'; rfl) h s
  have cast_e (s : Seq μ) : b.symm (KLRAlgebra.e s) = KLRAlgebra.e (Seq.cast h.symm s) := by
    apply b.injective
    rw [AlgEquiv.apply_symm_apply, show b (KLRAlgebra.e (Seq.cast h.symm s)) = _ from
      castKLR_e h (Seq.cast h.symm s), cast_back]
  let g (j : Fin (Fintype.card T.ι)) := (T.coeff (e.symm j)).comp b.symm.toLinearMap
  let w (j : Fin (Fintype.card T.ι)) := b (T.word (e.symm j))
  let bottom (j : Fin (Fintype.card T.ι)) (s : KLR.Seq μ) :=
    T.bottom (e.symm j) (Seq.cast h.symm s)
  have g_mul (j : Fin (Fintype.card T.ι)) (x : X row) (y : R μ) :
      g j (G x * y) = x * g j y := by
    change T.coeff _ (b.symm (b (juxtapose Q Λ row x)*y)) = _
    rw [map_mul, AlgEquiv.symm_apply_apply]; exact T.coeff_mul _ _ _
  have g_e (j : Fin (Fintype.card T.ι)) (y : R μ) (s : KLR.Seq μ) :
      g j (y * KLRAlgebra.e s) = g j y * bottom j s := by
    change T.coeff _ (b.symm (y * KLRAlgebra.e s)) = _
    rw [map_mul]
    rw [cast_e, T.coeff_e]
    rfl
  have g_section (j : Fin (Fintype.card T.ι)) (y : R μ) :
      g j (toKLR k Q Λ ν (π y)) = g j y := by
    apply coefficient_of_section Q Λ hQ (g j) _ y
    intro s a ha z
    let a' := Fin.cast (congrArg Multiset.card h.symm) a
    have cast_x : b.symm (KLRAlgebra.x a) = KLRAlgebra.x a' := by
      apply b.injective
      rw [AlgEquiv.apply_symm_apply,
        show b (KLRAlgebra.x a') = _ from castKLR_x h a', Fin.cast_cast, Fin.cast_eq_self]
    have red' : ((Seq.cast h.symm s).lbl a').isRight := by
      have cast_label {w w' : Multiset (I ⊕ Fin ℓ)} (hw : w = w')
          (t : KLR.Seq w) (a : Fin w.card) :
          ((Seq.cast hw t).lbl (Fin.cast (congrArg Multiset.card hw) a)) = t.lbl a := by
        subst w'
        rfl
      exact (cast_label h.symm s a).symm ▸ ha
    change T.coeff _ (b.symm ((KLRAlgebra.x a * KLRAlgebra.e s) * z)) = 0
    rw [map_mul b.symm, map_mul b.symm, cast_x, cast_e]
    exact T.coeff_top_red _ _ _ red' _
  have zero_at_loading (j : Fin (Fintype.card T.ι)) (y : R μ) (s : KLR.Seq μ)
      (hviol : bad s) : projection Q Λ row (g j (y * KLRAlgebra.e s)) = 0 := by
    let u := Seq.cast h.symm s
    have hv (v : Loadings row) (hs : ShuffleLoading row u v) : Violated row v := by
      rcases hviol with hglobal | ⟨ho, hhigh⟩
      · apply violated_of_shuffleLoading_global row u v hs
        have cast_violated {w w' : Multiset (I ⊕ Fin ℓ)} (hww : w = w') (t : Seq w)
            (ht : IsViolated t) : IsViolated (Seq.cast hww t) := by
          subst w'
          simpa using ht
        exact cast_violated h.symm s hglobal
      · have hu : redWord (Seq.cast h u) = L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst := by
          rw [cast_back, ho]
        apply violated_of_adjacent_shuffleLoading L M f β h u v hs hu
        exact Or.inr (by rwa [cast_back])
    change projection Q Λ row (T.coeff _ (b.symm (y * KLRAlgebra.e s))) = 0
    rw [map_mul b.symm, cast_e, T.coeff_e]
    rcases T.bottom_spec (e.symm j) u with hzero | ⟨v, hsh, he⟩
    · rw [hzero, mul_zero, map_zero]
    · rw [he, map_mul, projection_loadingIdem_eq_zero Q Λ row v (hv v hsh), mul_zero]
  have rebuild (y : R μ) : π (G 1 * y) = ∑ j, π (G (g j y) * w j) := by
    obtain ⟨v,rfl⟩ := b.surjective y
    have he := T.expand H hh v
    change π (b (juxtapose Q Λ row 1) * b v) = _
    rw [← map_mul]
    refine he.trans ((e.symm.sum_comp _).symm.trans ?_)
    apply Finset.sum_congr rfl; intro j _
    change π (b (juxtapose Q Λ row (T.coeff _ v) * _)) = π (b (juxtapose Q Λ row (T.coeff _ (b.symm (b v)))) * _)
    rw [map_mul b, AlgEquiv.symm_apply_apply]
  refine ⟨_, g, w, bottom, g_mul, g_e, g_section, ?_, ?_, rebuild⟩
  · intro j s
    exact T.bottom_spec (e.symm j) (Seq.cast h.symm s)
  · intro j y s z hs
    let d := y * KLRAlgebra.e s
    let P := projection Q Λ row
    let expanded : R μ := ∑ i, G (g i d) * (w i * z)
    have rawEq : π (G 1 * (d * z)) = π expanded := by
      calc
        _ = π (G 1 * d) * π z := by rw [← mul_assoc, map_mul]
        _ = _ := by
          rw [rebuild, Finset.sum_mul]
          simp only [expanded, map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [← mul_assoc, map_mul π (G (g i d) * w i) z]
    have same : g j (G 1 * (d * z)) = g j expanded :=
      (g_section j _).symm.trans
        ((congrArg (g j ∘ toKLR k Q Λ ν) rawEq).trans (g_section j expanded))
    change P (g j (d * z)) = 0
    calc
      _ = P (g j (G 1 * (d * z))) := by rw [g_mul, one_mul]
      _ = P (g j expanded) := congrArg P same
      _ = 0 := by
        simp only [expanded, map_sum]
        apply Finset.sum_eq_zero
        intro i _
        rw [g_mul, map_mul, zero_at_loading i y s hs, zero_mul]

/-- Parabolic coordinates that are linear under multiplication above the seam and
reconstruct the juxtaposed-top column after forgetting red dots. -/
theorem exists_blockStack_coordinates (hQ : KLRSymm Q) (L M : List (Fin ℓ × Multiset I))
    (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν) :
    let row := adjacentRow L M f β
    let μ := stendhalWeight ℓ ν
    let G := affineStackBlocks Q Λ L M f β h
    let π := ofKLR k Q Λ ν
    ∃ n, ∃ (g : Fin n → R μ →ₗ[k] X row) (w : Fin n → R μ),
      (∀ j x y, g j (G x * y) = x * g j y) ∧
      ∀ y, π (G 1 * y) = ∑ j, π (G (g j y) * w j) := by
  obtain ⟨n, g, w, _, hmul, _, _, _, _, hexpand⟩ :=
    exists_blockStack_coordinates_with_bottom Q Λ hQ L M f β h
  exact ⟨n, g, w, hmul, hexpand⟩

end Categorification.Stendhal.RedBlock
