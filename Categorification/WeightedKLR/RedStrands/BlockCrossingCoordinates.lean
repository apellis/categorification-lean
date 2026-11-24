/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingSeam
import Categorification.KLR.InductionFree
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
      ∀ y, oneConcat S a b * y = ∑ i, concat S a b (g i y) * w i := by
  classical
  let B := freeBasis (ν := a) (ν' := b) (stendhalQ_symm Q Λ hQ) (canWord _) (canWord _)
    (fun i => canWord _ i.1) (fun i => ⟨isReduced_canWord _ i,wordProd_canWord _ i⟩)
    (fun i => ⟨isReduced_canWord _ i,wordProd_canWord _ i⟩)
    (fun i => ⟨isReduced_canWord _ i.1,wordProd_canWord _ i.1⟩)
  let col := (LinearMap.mulLeft k (oneConcat S a b)).codRestrict (oneConcatSub S) fun y =>
    mem_oneConcatSub.2 (by change _ * (oneConcat S a b * y) = _; rw [← mul_assoc, oneConcat_idem.eq]; rfl)
  refine ⟨fun i => ((B.coord i).restrictScalars k).comp col, fun i => (B i).1, ?_, ?_⟩
  · intro i x y
    have he : col (concat S a b x * y) = x • col y := Subtype.ext (by
      change oneConcat S a b * (concat S a b x * y) = concat S a b x * (oneConcat S a b * y)
      rw [← mul_assoc, oneConcat_mul_concat, ← mul_assoc, concat_mul_oneConcat])
    change B.coord i (col _) = x * B.coord i (col y)
    rw [he, map_smul, smul_eq_mul]
  · intro y
    have he := congrArg Subtype.val (B.sum_repr (col y))
    change (col y).1 = ∑ i, concat S a b (B.repr (col y) i) * (B i).1
    simpa only [AddSubmonoidClass.coe_finsetSum, coe_tensor_smul] using he.symm

private structure Coefficients (row : List (RedBlock I ℓ)) (D : Type*) [Ring D] [Algebra k D] where
  ι : Type
  fintype : Fintype ι
  coeff : ι → R (weightSum row) →ₗ[k] X row
  word : ι → R (weightSum row)
  coeff_mul : ∀ j x y, coeff j (juxtapose Q Λ row x * y) = x * coeff j y
  expand : ∀ (H : R (weightSum row) →ₙₐ[k] D), KillsRed Q Λ H → ∀ y,
    H (juxtapose Q Λ row 1 * y) = ∑ j, H (juxtapose Q Λ row (coeff j y) * word j)

private def emptyCoefficients (D : Type*) [Ring D] [Algebra k D] : Coefficients Q Λ [] D := by
  let z := zeroEquiv (I ⊕ Fin ℓ) k S
  let ev := ULift.algEquiv.symm.toLinearMap.comp z.toLinearMap
  refine ⟨Unit, inferInstance, fun _ => ev, fun _ => 1, ?_, ?_⟩
  · intro _ a y
    change ULift.up (z (algebraMap k _ a.down * y)) = _
    rw [map_mul, AlgEquiv.commutes]; rfl
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
  obtain ⟨gm,gw⟩ := (binaryCoordinates Q Λ a b hQ).choose_spec.choose_spec
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
  refine ⟨U × T.ι, prodfin, fun ij => (c ij.2).comp (g ij.1),
    fun ij => rightIn Q Λ a b (T.word ij.2) * w ij.1, ?_, ?_⟩
  · intro ij u y
    change c ij.2 (g ij.1 (concat S a b _ * y)) = _
    rw [gm]; exact hcoeff u _ _
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

/-- Parabolic coordinates of the juxtaposed-top column (Webster, arXiv:1309.3796v2,
Proposition 6.4 and proof of Lemma 6.8; Khovanov–Lauda I, Proposition 2.16). Multiplying
above the seam multiplies each coefficient. Restacking the coefficients recovers the
whole column after imposing red dots, before either kind of violation. -/
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
  classical
  intro row μ G π
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
  refine ⟨_, fun j => (T.coeff (e.symm j)).comp b.symm.toLinearMap, fun j => b (T.word (e.symm j)), ?_, ?_⟩
  · intro j x y
    change T.coeff _ (b.symm (b (juxtapose Q Λ row x)*y)) = _
    rw [map_mul, AlgEquiv.symm_apply_apply]; exact T.coeff_mul _ _ _
  · intro y
    obtain ⟨v,rfl⟩ := b.surjective y
    have he := T.expand H hh v
    change π (b (juxtapose Q Λ row 1) * b v) = _
    rw [← map_mul]
    refine he.trans ((e.symm.sum_comp _).symm.trans ?_)
    apply Finset.sum_congr rfl; intro j _
    change π (b (juxtapose Q Λ row (T.coeff _ v) * _)) = π (b (juxtapose Q Λ row (T.coeff _ (b.symm (b v)))) * _)
    rw [map_mul b, AlgEquiv.symm_apply_apply]

end Categorification.Stendhal.RedBlock
