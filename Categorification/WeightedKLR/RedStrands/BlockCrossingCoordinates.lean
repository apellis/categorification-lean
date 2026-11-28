/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingSeam
import Categorification.WeightedKLR.RedStrands.BlockShuffleLoading
import Categorification.WeightedKLR.RedStrands.BlockShuffleCrossing
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

/-- A shuffle of a row separates its first block from the tail, then shuffles the tail. -/
def ShuffleIndex : List (RedBlock I ℓ) → Type
  | [] => Unit
  | B :: row => Shuffle (Seq.card_add' B.weight (weightSum row)) × ShuffleIndex row

instance shuffleIndexFintype : (row : List (RedBlock I ℓ)) → Fintype (ShuffleIndex row)
  | [] => inferInstanceAs (Fintype Unit)
  | B :: row => @instFintypeProd _ _ (Fintype.ofFinite (Shuffle (Seq.card_add' B.weight (weightSum row))))
      (shuffleIndexFintype row)

/-- The chosen crossing word reads the tail in its shifted positions and then applies
the minimal representative separating the first block. -/
def shuffleWord : (row : List (RedBlock I ℓ)) → ShuffleIndex row → List ℕ
  | [], _ => []
  | B :: row, u => shiftWord B.weight.card (shuffleWord row u.2) ++ canWord _ u.1.1

omit [DecidableEq I] in
/-- Each word chosen by the recursion is reduced. -/
theorem isReduced_shuffleWord : ∀ (row : List (RedBlock I ℓ)) (u : ShuffleIndex row),
    IsReduced (weightSum row).card (shuffleWord row u)
  | [], _ => by simp [shuffleWord, TypeA.IsReduced]
  | B :: row, u => by
    let h := Seq.card_add' B.weight (weightSum row)
    have empty : IsReduced B.weight.card [] := by simp [TypeA.IsReduced]
    have sh : IsShuffle h (wordProd _ (canWord _ u.1.1)) := by
      rw [wordProd_canWord]; exact u.1.2
    simpa only [shuffleWord, List.nil_append] using
      (IsReduced.parabolic h empty (isReduced_shuffleWord row u.2) (isReduced_canWord _ u.1.1) sh).1

/-- Tensor crossing filtration on the external block diagrams. A pure tensor of
block diagrams can use its crossing budget in either factor. -/
def blockCrossingFilt : (row : List (RedBlock I ℓ)) → ℕ → Submodule k (X row)
  | [], _ => ⊤
  | B :: row, n => Submodule.span k {z | ∃ (p q : ℕ) (x : R B.weight) (y : X row),
      p + q ≤ n ∧ x ∈ filt k S B.weight p ∧ y ∈ blockCrossingFilt row q ∧
        omitRedDots Q Λ B x ⊗ₜ[k] y = z}

/-- The available internal crossing budget after fixing the exiting shuffle. -/
def blockShuffleFilt (row : List (RedBlock I ℓ)) (index : ShuffleIndex row) (n : ℕ) :
    Submodule k (X row) :=
  if (shuffleWord row index).length ≤ n then blockCrossingFilt Q Λ row (n - (shuffleWord row index).length) else ⊥

/-- A shuffle longer than the source diagram has zero coefficient. -/
theorem blockShuffleFilt_eq_bot (row : List (RedBlock I ℓ)) (index : ShuffleIndex row)
    {n : ℕ} (hn : n < (shuffleWord row index).length) : blockShuffleFilt Q Λ row index n = ⊥ :=
  ite_eq_right (Nat.not_le.mpr hn)

private theorem filtered_cons_coordinate (B : RedBlock I ℓ) (row : List (RedBlock I ℓ))
    (u : Shuffle (Seq.card_add' B.weight (weightSum row))) (v : ShuffleIndex row)
    (tail : R (weightSum row) →ₗ[k] X row)
    (htail : ∀ y n, y ∈ filt k S (weightSum row) n → tail y ∈ blockShuffleFilt Q Λ row v n)
    {z : R B.weight ⊗[k] R (weightSum row)} {n : ℕ}
    (hz : z ∈ tensorCrossingFilt S B.weight (weightSum row) (length _ u.1) n) :
    TensorProduct.map (omitRedDots Q Λ B).toLinearMap tail z ∈ blockShuffleFilt Q Λ (B :: row) (u, v) n := by
  let F := TensorProduct.map (omitRedDots Q Λ B).toLinearMap tail
  let M := blockShuffleFilt Q Λ (B :: row) (u, v) n
  change z ∈ M.comap F
  apply (Submodule.span_le.2 ?_ hz)
  rintro _ ⟨p, q, x, y, hpq, hx, hy, rfl⟩
  change F (x ⊗ₜ[k] y) ∈ M
  rw [show F (x ⊗ₜ[k] y) = omitRedDots Q Λ B x ⊗ₜ[k] tail y from TensorProduct.map_tmul _ _ x y]
  have h := htail y q hy
  by_cases good : (shuffleWord row v).length ≤ q
  · rw [blockShuffleFilt, ite_eq_left good] at h
    have budget : (shuffleWord (B :: row) (u, v)).length = (shuffleWord row v).length + length _ u.1 := by
      simp only [shuffleWord, List.length_append, length_shiftWord, length_canWord]
    have enough : (shuffleWord (B :: row) (u, v)).length ≤ n := by omega
    rw [show M = blockCrossingFilt Q Λ (B :: row) (n - (shuffleWord (B :: row) (u, v)).length) from
      ite_eq_left enough]
    apply Submodule.subset_span
    exact ⟨p, q - (shuffleWord row v).length, x, tail y, by omega, hx, h, rfl⟩
  · rw [blockShuffleFilt, ite_eq_right good, Submodule.mem_bot] at h
    rw [h, TensorProduct.tmul_zero]
    exact M.zero_mem

private theorem rightIn_word {a b : Multiset (I ⊕ Fin ℓ)} (z : R b) (d c : List ℕ)
    (hd : ValidWord b.card d) :
    rightIn Q Λ a b (z * ψw d) * (oneConcat S a b * ψw c) =
      rightIn Q Λ a b z * ψw (shiftWord a.card d ++ c) := by
  let r := rightIn Q Λ a b
  have fix (y : R b) : r y * oneConcat S a b = r y := concat_mul_oneConcat _
  have shift : r (ψw d) = oneConcat S a b * ψw (shiftWord a.card d) := by
    change concat S a b (1 ⊗ₜ[k] ψw d) = _
    rw [← ψw_nil (Q := S) (ν := a), concat_ψw_tmul_ψw (validWord_nil _) hd,
      ← oneConcat_mul_ψw (validWord_nil _) hd, List.nil_append]
  change r (z * ψw d) * _ = r z * _
  rw [← mul_assoc, fix, map_mul r, shift, ← mul_assoc (r z), fix, ψw_append, mul_assoc]

private theorem binaryCoordinates (a b : Multiset (I ⊕ Fin ℓ)) (hQ : KLRSymm Q) :
    let U := Shuffle (Seq.card_add' a b)
    ∃ (g : U → R (a+b) →ₗ[k] (R a ⊗[k] R b)) (w : U → R (a+b)),
      (∀ i y n, y ∈ filt k S (a+b) n → g i y ∈ tensorCrossingFilt S a b (length _ i.1) n) ∧
      (∀ i, w i = oneConcat S a b * ψw (canWord _ i.1)) ∧
      (∀ i x y, g i (concat S a b x * y) = x * g i y) ∧
      (∀ i y s, g i (y * e s) = g i y * concatIdem (i.1 • s)) ∧
      (∀ i, g i (w i) = 1) ∧ (∀ i j, i ≠ j → g i (w j) = 0) ∧
      ∀ y, oneConcat S a b * y = ∑ i, concat S a b (g i y) * w i := by
  classical
  let B := freeBasis (ν := a) (ν' := b) (stendhalQ_symm Q Λ hQ) (canWord _) (canWord _)
    (fun i => canWord _ i.1) (fun i => ⟨isReduced_canWord _ i,wordProd_canWord _ i⟩)
    (fun i => ⟨isReduced_canWord _ i,wordProd_canWord _ i⟩)
    (fun i => ⟨isReduced_canWord _ i.1,wordProd_canWord _ i.1⟩)
  let col := (LinearMap.mulLeft k (oneConcat S a b)).codRestrict (oneConcatSub S) fun y =>
    mem_oneConcatSub.2 (by change _ * (oneConcat S a b * y) = _; rw [← mul_assoc, oneConcat_idem.eq]; rfl)
  have hcol (i : Shuffle (Seq.card_add' a b)) : col (B i).1 = B i :=
    Subtype.ext (mem_oneConcatSub.1 (B i).2)
  refine ⟨fun i => ((B.coord i).restrictScalars k).comp col, fun i => (B i).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i y n hy
    exact freeBasis_coord_mem_tensorCrossingFilt (stendhalQ_symm Q Λ hQ) _ _ _ _ _ _ hy i
  · intro i
    exact freeBasis_apply _ _ _ _ _ _ _ i
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
  · intro i
    change B.coord i (col (B i).1) = 1
    simp [hcol, Module.Basis.coord_apply, Module.Basis.repr_self]
  · intro i j hij
    change B.coord i (col (B j).1) = 0
    simp [hcol, Module.Basis.coord_apply, Module.Basis.repr_self, hij]
  · intro y
    have he := congrArg Subtype.val (B.sum_repr (col y))
    change (col y).1 = ∑ i, concat S a b (B.repr (col y) i) * (B i).1
    simpa only [AddSubmonoidClass.coe_finsetSum, coe_tensor_smul] using he.symm

/-- The external product of the quotient maps kills a loading idempotent
as soon as any one of its blocks is violated. -/
theorem projection_loadingIdem_eq_zero : ∀ Bs (s : Loadings Bs), Violated Bs s →
    projection Q Λ Bs (loadingIdem Q Λ Bs s) = 0
  | [], _, hs => False.elim hs
  | B :: Bs, s, hs => by
    change (Algebra.TensorProduct.map (violMk k Q (Λ ∘ B.label) B.black)
      (projection Q Λ Bs)) (_ ⊗ₜ[k] _) = 0
    rw [Algebra.TensorProduct.map_tmul]
    rcases hs with h | h
    · rw [violMk_e h, TensorProduct.zero_tmul]
    · rw [projection_loadingIdem_eq_zero Bs s.2 h, TensorProduct.tmul_zero]

/-- The actual parabolic shuffle selects a unique placed bottom loading whenever
the split exists. A matching loading gives precisely its idempotent, including in
the case where that idempotent vanishes. -/
structure IndexedLoadingProjector (row : List (RedBlock I ℓ)) (i : ShuffleIndex row)
    (s : Seq (weightSum row)) (z : X row) : Prop where
  support : z = 0 ∨ ∃ v : Loadings row, ShuffleLoading row s v ∧
    wordProd (weightSum row).card (shuffleWord row i) • s = place row v ∧ z = loadingIdem Q Λ row v
  matched : ∀ v : Loadings row, wordProd (weightSum row).card (shuffleWord row i) • s = place row v →
    z = loadingIdem Q Λ row v

theorem IndexedLoadingProjector.loading {row : List (RedBlock I ℓ)} {i : ShuffleIndex row}
    {s : Seq (weightSum row)} {z : X row} (p : IndexedLoadingProjector Q Λ row i s z) :
    z = 0 ∨ ∃ v : Loadings row, ShuffleLoading row s v ∧ z = loadingIdem Q Λ row v := by
  rcases p.support with hz | ⟨v, hsh, _, he⟩
  · exact Or.inl hz
  · exact Or.inr ⟨v, hsh, he⟩

/-- Projectors at equal shuffled top loadings coincide, also when the loading has no
block split. -/
theorem IndexedLoadingProjector.eq_of_same_top {row : List (RedBlock I ℓ)} {i j : ShuffleIndex row}
    {s t : Seq (weightSum row)} {x y : X row} (p : IndexedLoadingProjector Q Λ row i s x)
    (q : IndexedLoadingProjector Q Λ row j t y)
    (he : wordProd (weightSum row).card (shuffleWord row i) • s = wordProd (weightSum row).card (shuffleWord row j) • t) : x = y := by
  rcases p.support with hx | ⟨v, _, hv, hx⟩
  · rcases q.support with hy | ⟨v, _, hv, hy⟩
    · exact hx.trans hy.symm
    · exact (p.matched v (he.trans hv)).trans hy.symm
  · exact hx.trans (q.matched v (he.symm.trans hv)).symm

omit [DecidableEq I] in
private theorem shuffleWord_place_cons (B : RedBlock I ℓ) (row : List (RedBlock I ℓ))
    (i : ShuffleIndex (B :: row)) (s : Seq (weightSum (B :: row))) (v : Loadings (B :: row)) :
    wordProd (weightSum (B :: row)).card (shuffleWord (B :: row) i) • s = place (B :: row) v ↔
    i.1.1 • s = (Seq.map B.colour v.1).append ((wordProd (weightSum row).card (shuffleWord row i.2))⁻¹ • place row v.2) := by
  let d := wordProd (weightSum row).card (shuffleWord row i.2)
  let b := blockPerm (Seq.card_add' B.weight (weightSum row)) 1 d
  have word : wordProd (weightSum (B :: row)).card (shuffleWord (B :: row) i) = b * i.1.1 := by
    change wordProd _ (shiftWord _ _ ++ canWord _ _) = _
    rw [wordProd_append, wordProd_canWord, wordProd_shiftWord (Seq.card_add' B.weight (weightSum row))
      (isReduced_shuffleWord row _).1]
  rw [word, mul_smul]
  constructor
  · intro he
    have hc := congrArg (fun x : Seq (weightSum (B :: row)) => b⁻¹ • x) he
    change b⁻¹ • (b • (i.1.1 • s)) = b⁻¹ • place (B :: row) v at hc
    rw [inv_smul_smul] at hc
    simpa only [place, b, blockPerm_inv, inv_one, Seq.blockPerm_smul_append, one_smul] using hc
  · intro he
    rw [he]
    change blockPerm _ 1 d • _ = _
    rw [Seq.blockPerm_smul_append, one_smul, smul_inv_smul]
    rfl

private structure Coefficients (row : List (RedBlock I ℓ)) (D : Type*) [Ring D] [Algebra k D] where
  coeff : ShuffleIndex row → R (weightSum row) →ₗ[k] X row
  word : ShuffleIndex row → R (weightSum row)
  coeff_filt : ∀ i y n, y ∈ filt k S (weightSum row) n → coeff i y ∈ blockShuffleFilt Q Λ row i n
  word_spec : ∀ i, word i = juxtapose Q Λ row 1 * ψw (shuffleWord row i)
  bottom : ShuffleIndex row → Seq (weightSum row) → X row
  coeff_e : ∀ j y s, coeff j (y * e s) = coeff j y * bottom j s
  bottom_spec : ∀ j s, IndexedLoadingProjector Q Λ row j s (bottom j s)
  coeff_mul : ∀ j x y, coeff j (juxtapose Q Λ row x * y) = x * coeff j y
  coeff_word_self : ∀ j, coeff j (word j) = 1
  coeff_word_ne : ∀ i j, i ≠ j → coeff i (word j) = 0
  coeff_top_red : ∀ j (t : Seq (weightSum row)) a, (t.lbl a).isRight → ∀ y,
    coeff j ((x a * e t) * y) = 0
  expand : ∀ (H : R (weightSum row) →ₙₐ[k] D), KillsRed Q Λ H → ∀ y,
    H (juxtapose Q Λ row 1 * y) = ∑ j, H (juxtapose Q Λ row (coeff j y) * word j)

private def emptyCoefficients (D : Type*) [Ring D] [Algebra k D] : Coefficients Q Λ [] D := by
  letI : Unique (ShuffleIndex ([] : List (RedBlock I ℓ))) := inferInstanceAs (Unique Unit)
  let z := zeroEquiv (I ⊕ Fin ℓ) k S
  let ev := ULift.algEquiv.symm.toLinearMap.comp z.toLinearMap
  refine ⟨fun _ => ev, fun _ => 1, ?_, ?_, fun _ _ => 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i y n _
    simp only [blockShuffleFilt, shuffleWord, List.length_nil, Nat.zero_le, ite_true, blockCrossingFilt, Submodule.mem_top]
  · intro _
    change (1 : R 0) = algebraMap k _ 1 * ψw []
    rw [map_one, ψw_nil, mul_one]
  · intro _ y s
    rw [e_eq_one, mul_one, mul_one]
  · intro _ _
    exact ⟨Or.inr ⟨PUnit.unit, trivial, Subsingleton.elim _ _, rfl⟩, fun _ _ => rfl⟩
  · intro _ a y
    change ULift.up (z (algebraMap k _ a.down * y)) = _
    rw [map_mul, AlgEquiv.commutes]; rfl
  · intro _
    change ULift.up (z 1) = 1
    rw [map_one]
    rfl
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
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
  let g := (binaryCoordinates Q Λ a b hQ).choose
  let w := (binaryCoordinates Q Λ a b hQ).choose_spec.choose
  obtain ⟨g_filt, w_spec, gm, ge, gs, gn, gw⟩ := (binaryCoordinates Q Λ a b hQ).choose_spec.choose_spec
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
  have project_tmul (j : ShuffleIndex row) (s : KLR.Seq B.weight) (t : KLR.Seq (weightSum row))
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
  have gRight (u : U) (z : R (weightSum row)) (r : R (a + b)) :
      g u (rightIn Q Λ a b z * r) = ((1 : R B.weight) ⊗ₜ[k] z) * g u r :=
    gm u _ r
  let bottom (ij : U × ShuffleIndex row) (s : KLR.Seq (weightSum (B :: row))) : X (B :: row) :=
    if hs : ij.1.1 • s ∈ concatSet a b then
      v (e (split _ hs).1) ⊗ₜ[k] T.bottom ij.2 (split _ hs).2
    else 0
  have unit : juxtapose Q Λ (B :: row) 1 = rightIn Q Λ a b (juxtapose Q Λ row 1) := by
    change juxtapose Q Λ (B::row) ((1 : diagramAlgebra Q Λ B) ⊗ₜ[k] (1 : X row)) = _
    rw [juxtapose_tmul, map_one]; rfl
  refine ⟨fun ij => (c ij.2).comp (g ij.1),
    fun ij => rightIn Q Λ a b (T.word ij.2) * w ij.1, ?_, ?_, bottom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ij y n hy
    exact filtered_cons_coordinate Q Λ B row ij.1 ij.2 (T.coeff ij.2) (T.coeff_filt ij.2) (g_filt ij.1 y n hy)
  · intro ij
    have hw : w ij.1 = oneConcat S a b * ψw (canWord _ ij.1.1) := w_spec ij.1
    rw [T.word_spec, hw, unit]
    exact rightIn_word Q Λ _ _ _ (isReduced_shuffleWord row _).1
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
    constructor
    · by_cases hs : ij.1.1 • s ∈ concatSet a b
      · let p := (split (ij.1.1 • s) hs).1
        let q := (split (ij.1.1 • s) hs).2
        have hb : bottom ij s = v (e p) ⊗ₜ[k] T.bottom ij.2 q := by
          simp only [bottom, dite_eq_left hs, p, q]
        rcases (T.bottom_spec ij.2 q).support with hzero | ⟨t, ht, hplace, he⟩
        · exact Or.inl (by rw [hb, hzero, TensorProduct.tmul_zero])
        · let equiv := redSubfamilyRelabel Q Λ B.label B.label.injective B.black
          let p' := equiv.equiv.symm p
          have hmap : Seq.map B.colour p' = p := equiv.equiv.apply_symm_apply p
          have hproj : v (e p) = ofKLR k Q (Λ ∘ B.label) B.black (e p') := by
            change ofKLR k Q (Λ ∘ B.label) B.black ((relabelEquiv equiv).symm (e p)) = _
            rw [relabelEquiv_symm_apply, relabelHom_e, SeqRelabel.symm_equiv]
          refine Or.inr ⟨(p', t), ⟨ij.1, q, ?_, ht⟩, ?_, ?_⟩
          · exact (split_spec _ hs).symm.trans (congrArg (·.append q) hmap.symm)
          · apply (shuffleWord_place_cons B row ij s _).2
            have htq : q = (wordProd (weightSum row).card (shuffleWord row ij.2))⁻¹ • place row t := by rw [← hplace, inv_smul_smul]
            exact (split_spec _ hs).symm.trans (congrArg₂ Seq.append hmap.symm htq)
          · rw [hb, he, hproj]
            rfl
      · exact Or.inl (by simp only [bottom, dite_eq_right hs])
    · intro x hx
      let t := (wordProd (weightSum row).card (shuffleWord row ij.2))⁻¹ • place row x.2
      have he : ij.1.1 • s = (Seq.map B.colour x.1).append t := (shuffleWord_place_cons B row ij s x).1 hx
      have hs : ij.1.1 • s ∈ concatSet a b := mem_concatSet.2 ⟨_, _, he.symm⟩
      obtain ⟨hp, hq⟩ := Seq.append_inj.1 ((split_spec _ hs).trans he)
      have ht : wordProd (weightSum row).card (shuffleWord row ij.2) • t = place row x.2 := smul_inv_smul _ _
      have hx' : v (e (Seq.map B.colour x.1)) = ofKLR k Q (Λ ∘ B.label) B.black (e x.1) := by
        let r := redSubfamilyRelabel Q Λ B.label B.label.injective B.black
        change ofKLR k Q (Λ ∘ B.label) B.black ((relabelEquiv r).symm _) = _
        rw [← show (relabelEquiv r) (e x.1) = e (Seq.map B.colour x.1) from relabelHom_e _ _,
          AlgEquiv.symm_apply_apply]
      rw [show bottom ij s = _ from dite_eq_left hs, hp, hq, hx', (T.bottom_spec ij.2 t).matched x.2 ht]
      rfl
  · intro ij u y
    change c ij.2 (g ij.1 (concat S a b _ * y)) = _
    rw [gm]; exact hcoeff u _ _
  · intro ij
    change c ij.2 (g ij.1 (rightIn Q Λ a b (T.word ij.2) * w ij.1)) = 1
    rw [gRight, gs, mul_one]
    simp only [c, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, T.coeff_word_self]
    exact Algebra.TensorProduct.one_def.symm
  · intro ij uv hne
    change c ij.2 (g ij.1 (rightIn Q Λ a b (T.word uv.2) * w uv.1)) = 0
    rw [gRight]
    by_cases hu : ij.1 = uv.1
    · have hv : ij.2 ≠ uv.2 := fun h => hne (Prod.ext hu h)
      rw [← hu, gs, mul_one]
      simp only [c, TensorProduct.map_tmul, T.coeff_word_ne _ _ hv, TensorProduct.tmul_zero]
    · rw [gn _ _ hu, mul_zero, map_zero]
  · intro ij s d hd y
    exact concat_top_red Q Λ v (T.coeff ij.2) (omitRedDots_top_red Q Λ B)
      (T.coeff_top_red ij.2) (g ij.1) (gm ij.1) s d hd y
  · intro H hh y
    let l := leftIn Q Λ a b
    let r := rightIn Q Λ a b
    let m := concat S a b
    let U₀ := juxtapose Q Λ row 1
    have hE : juxtapose Q Λ (B::row) 1 = r U₀ := unit
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
    refine Eq.trans ?_ (@Fintype.sum_prod_type D U (ShuffleIndex row) ‹Fintype U› (shuffleIndexFintype row) _ _).symm
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

/-- Juxtaposition of the blocks of a row in the affine algebra of the ambient weight. -/
def rowStack (Bs : List (RedBlock I ℓ)) {ν : Multiset I} (h : weightSum Bs = stendhalWeight ℓ ν) :
    X Bs →ₙₐ[k] R (stendhalWeight ℓ ν) where
  toFun x := castKLR S h (juxtapose Q Λ Bs x)
  map_zero' := by simp only [map_zero]
  map_add' _ _ := by simp only [map_add]
  map_smul' _ _ := by simp only [map_smul, MonoidHom.id_apply]
  map_mul' _ _ := by simp only [juxtapose_mul, map_mul]

/-- **Parabolic coordinates of a juxtaposed-top column, for any row** (Webster,
arXiv:1309.3796v2, Proposition 6.4 and proof of Lemma 6.8; Khovanov–Lauda I,
Proposition 2.16). The same as `exists_blockStack_coordinates_with_indexed_projectors`, for an
arbitrary row of red blocks and an arbitrary class `bad` of source loadings all of whose
compatible shuffles have a violated block. For the row of an adjacent pair this is the partial
standard; for a row of singleton blocks with `bad` the singleton cuts it is the full standard. -/
theorem exists_rowStack_coordinates_with_indexed_projectors (hQ : KLRSymm Q)
    (row : List (RedBlock I ℓ)) {ν : Multiset I} (h : weightSum row = stendhalWeight ℓ ν)
    (bad : KLR.Seq (stendhalWeight ℓ ν) → Prop)
    (hbad : ∀ s, bad s → ∀ v : Loadings row, ShuffleLoading row (Seq.cast h.symm s) v →
      Violated row v) :
    let μ := stendhalWeight ℓ ν
    let G := rowStack Q Λ row h
    let π := ofKLR k Q Λ ν
    ∃ n, ∃ (index : Fin n ≃ ShuffleIndex row) (g : Fin n → R μ →ₗ[k] X row) (w : Fin n → R μ)
      (bottom : Fin n → Seq μ → X row),
      (∀ j y n, y ∈ filt k S μ n → g j y ∈ blockShuffleFilt Q Λ row (index j) n) ∧
      (∀ j, w j = G 1 * ψw (shuffleWord row (index j))) ∧
      (∀ j x y, g j (G x * y) = x * g j y) ∧
      (∀ j y s, g j (y * e s) = g j y * bottom j s) ∧
      (∀ j y, g j (toKLR k Q Λ ν (π y)) = g j y) ∧
      (∀ j, g j (w j) = 1) ∧ (∀ i j, i ≠ j → g i (w j) = 0) ∧
      (∀ j s, IndexedLoadingProjector Q Λ row (index j) (Seq.cast h.symm s) (bottom j s)) ∧
      (∀ j y s z, bad s → projection Q Λ row (g j (y * e s * z)) = 0) ∧
      ∀ y, π (G 1 * y) = ∑ j, π (G (g j y) * w j) := by
  classical
  intro μ G π
  let T := rowCoefficients Q Λ (BraidedStendhalAlgebra k Q Λ ν) hQ row
  let e := Fintype.equivFin (ShuffleIndex row)
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
  let g (j : Fin (Fintype.card (ShuffleIndex row))) := (T.coeff (e.symm j)).comp b.symm.toLinearMap
  let w (j : Fin (Fintype.card (ShuffleIndex row))) := b (T.word (e.symm j))
  let bottom (j : Fin (Fintype.card (ShuffleIndex row))) (s : KLR.Seq μ) :=
    T.bottom (e.symm j) (Seq.cast h.symm s)
  have g_mul (j : Fin (Fintype.card (ShuffleIndex row))) (x : X row) (y : R μ) :
      g j (G x * y) = x * g j y := by
    change T.coeff _ (b.symm (b (juxtapose Q Λ row x)*y)) = _
    rw [map_mul, AlgEquiv.symm_apply_apply]; exact T.coeff_mul _ _ _
  have g_e (j : Fin (Fintype.card (ShuffleIndex row))) (y : R μ) (s : KLR.Seq μ) :
      g j (y * KLRAlgebra.e s) = g j y * bottom j s := by
    change T.coeff _ (b.symm (y * KLRAlgebra.e s)) = _
    rw [map_mul]
    rw [cast_e, T.coeff_e]
    rfl
  have g_section (j : Fin (Fintype.card (ShuffleIndex row))) (y : R μ) :
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
  have zero_at_loading (j : Fin (Fintype.card (ShuffleIndex row))) (y : R μ) (s : KLR.Seq μ)
      (hviol : bad s) : projection Q Λ row (g j (y * KLRAlgebra.e s)) = 0 := by
    let u := Seq.cast h.symm s
    have hv (v : Loadings row) (hs : ShuffleLoading row u v) : Violated row v :=
      hbad s hviol v hs
    change projection Q Λ row (T.coeff _ (b.symm (y * KLRAlgebra.e s))) = 0
    rw [map_mul b.symm, cast_e, T.coeff_e]
    rcases (T.bottom_spec (e.symm j) u).loading Q Λ with hzero | ⟨v, hsh, he⟩
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
  refine ⟨_, e.symm, g, w, bottom, ?_, ?_, g_mul, g_e, g_section, ?_, ?_, ?_, ?_, rebuild⟩
  · intro j y n hy
    have castFilt {u v : Multiset (I ⊕ Fin ℓ)} (e : u = v) (z : R v) (hz : z ∈ filt k S v n) :
        (castKLR S e).symm z ∈ filt k S u n := by subst v; exact hz
    exact T.coeff_filt _ (b.symm y) n (castFilt h y hy)
  · intro j
    change b (T.word _) = b (juxtapose Q Λ row 1) * ψw _
    rw [T.word_spec, map_mul, show ∀ d, b (ψw d) = ψw d from castKLR_ψw h]
  · intro j
    change T.coeff (e.symm j) (b.symm (b (T.word (e.symm j)))) = 1
    rw [AlgEquiv.symm_apply_apply, T.coeff_word_self]
  · intro i j hij
    change T.coeff (e.symm i) (b.symm (b (T.word (e.symm j)))) = 0
    rw [AlgEquiv.symm_apply_apply]
    exact T.coeff_word_ne _ _ (fun h => hij (e.symm.injective h))
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


/-- Parabolic coordinates of the juxtaposed-top column (Webster, arXiv:1309.3796v2,
Proposition 6.4 and proof of Lemma 6.8; Khovanov–Lauda I, Proposition 2.16). Multiplying
above the seam multiplies each coefficient. A bottom loading acts on each
coefficient through the split projector for its shuffle. Restacking the coefficients recovers the
whole column after imposing red dots, before either kind of violation. -/
theorem exists_blockStack_coordinates_with_indexed_projectors (hQ : KLRSymm Q) (L M : List (Fin ℓ × Multiset I))
    (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν) :
    let row := adjacentRow L M f β
    let μ := stendhalWeight ℓ ν
    let G := affineStackBlocks Q Λ L M f β h
    let π := ofKLR k Q Λ ν
    let bad := fun s : KLR.Seq μ => IsViolated s ∨
      (redWord s = L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst ∧
        (fun r i => boundaryCount (cut (f 0) (f 1) r) i row) < adjacentBlockRoot (f 0) (f 1) s)
    ∃ n, ∃ (index : Fin n ≃ ShuffleIndex row) (g : Fin n → R μ →ₗ[k] X row) (w : Fin n → R μ)
      (bottom : Fin n → Seq μ → X row),
      (∀ j y n, y ∈ filt k S μ n → g j y ∈ blockShuffleFilt Q Λ row (index j) n) ∧
      (∀ j, w j = G 1 * ψw (shuffleWord row (index j))) ∧
      (∀ j x y, g j (G x * y) = x * g j y) ∧
      (∀ j y s, g j (y * e s) = g j y * bottom j s) ∧
      (∀ j y, g j (toKLR k Q Λ ν (π y)) = g j y) ∧
      (∀ j, g j (w j) = 1) ∧ (∀ i j, i ≠ j → g i (w j) = 0) ∧
      (∀ j s, IndexedLoadingProjector Q Λ row (index j) (Seq.cast h.symm s) (bottom j s)) ∧
      (∀ j y s z, bad s → projection Q Λ row (g j (y * e s * z)) = 0) ∧
      ∀ y, π (G 1 * y) = ∑ j, π (G (g j y) * w j) := by
  intro row μ G π bad
  refine exists_rowStack_coordinates_with_indexed_projectors Q Λ hQ row h bad ?_
  intro s hs v hsv
  have cast_back : Seq.cast h (Seq.cast h.symm s) = s :=
    (show ∀ {w w' : Multiset (I ⊕ Fin ℓ)} (hw : w = w') (t : Seq w'),
      Seq.cast hw (Seq.cast hw.symm t) = t from fun {w w'} hw t => by subst w'; rfl) h s
  rcases hs with hglobal | ⟨ho, hhigh⟩
  · apply violated_of_shuffleLoading_global row _ v hsv
    have cast_violated {w w' : Multiset (I ⊕ Fin ℓ)} (hww : w = w') (t : Seq w)
        (ht : IsViolated t) : IsViolated (Seq.cast hww t) := by
      subst w'
      simpa using ht
    exact cast_violated h.symm s hglobal
  · exact violated_of_adjacent_shuffleLoading L M f β h _ v hsv (by rw [cast_back, ho])
      (Or.inr (by rwa [cast_back]))
/-- Filtered coordinates with the support of each bottom projector. -/
theorem exists_blockStack_coordinates_with_filtered_shuffle_words (hQ : KLRSymm Q) (L M : List (Fin ℓ × Multiset I))
    (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν) :
    let row := adjacentRow L M f β
    let μ := stendhalWeight ℓ ν
    let G := affineStackBlocks Q Λ L M f β h
    let π := ofKLR k Q Λ ν
    let bad := fun s : KLR.Seq μ => IsViolated s ∨
      (redWord s = L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst ∧
        (fun r i => boundaryCount (cut (f 0) (f 1) r) i row) < adjacentBlockRoot (f 0) (f 1) s)
    ∃ n, ∃ (index : Fin n ≃ ShuffleIndex row) (g : Fin n → R μ →ₗ[k] X row) (w : Fin n → R μ)
      (bottom : Fin n → Seq μ → X row),
      (∀ j y n, y ∈ filt k S μ n → g j y ∈ blockShuffleFilt Q Λ row (index j) n) ∧
      (∀ j, w j = G 1 * ψw (shuffleWord row (index j))) ∧
      (∀ j x y, g j (G x * y) = x * g j y) ∧
      (∀ j y s, g j (y * e s) = g j y * bottom j s) ∧
      (∀ j y, g j (toKLR k Q Λ ν (π y)) = g j y) ∧
      (∀ j, g j (w j) = 1) ∧ (∀ i j, i ≠ j → g i (w j) = 0) ∧
      (∀ j s, bottom j s = 0 ∨ ∃ v : Loadings row,
        ShuffleLoading row (Seq.cast h.symm s) v ∧ bottom j s = loadingIdem Q Λ row v) ∧
      (∀ j y s z, bad s → projection Q Λ row (g j (y * e s * z)) = 0) ∧
      ∀ y, π (G 1 * y) = ∑ j, π (G (g j y) * w j) := by
  obtain ⟨n, index, g, w, b, hf, hw, hm, he, hs, h1, h0, hp, hbad, hr⟩ :=
    exists_blockStack_coordinates_with_indexed_projectors Q Λ hQ L M f β h
  exact ⟨n, index, g, w, b, hf, hw, hm, he, hs, h1, h0, fun j s => (hp j s).loading Q Λ, hbad, hr⟩

/-- Coordinates indexed by chosen reduced shuffle words. -/
theorem exists_blockStack_coordinates_with_shuffle_words (hQ : KLRSymm Q) (L M : List (Fin ℓ × Multiset I))
    (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν) :
    let row := adjacentRow L M f β
    let μ := stendhalWeight ℓ ν
    let G := affineStackBlocks Q Λ L M f β h
    let π := ofKLR k Q Λ ν
    let bad := fun s : KLR.Seq μ => IsViolated s ∨
      (redWord s = L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst ∧
        (fun r i => boundaryCount (cut (f 0) (f 1) r) i row) < adjacentBlockRoot (f 0) (f 1) s)
    ∃ n, ∃ (index : Fin n ≃ ShuffleIndex row) (g : Fin n → R μ →ₗ[k] X row) (w : Fin n → R μ)
      (bottom : Fin n → Seq μ → X row),
      (∀ j, w j = G 1 * ψw (shuffleWord row (index j))) ∧
      (∀ j x y, g j (G x * y) = x * g j y) ∧
      (∀ j y s, g j (y * e s) = g j y * bottom j s) ∧
      (∀ j y, g j (toKLR k Q Λ ν (π y)) = g j y) ∧
      (∀ j, g j (w j) = 1) ∧ (∀ i j, i ≠ j → g i (w j) = 0) ∧
      (∀ j s, bottom j s = 0 ∨ ∃ v : Loadings row,
        ShuffleLoading row (Seq.cast h.symm s) v ∧ bottom j s = loadingIdem Q Λ row v) ∧
      (∀ j y s z, bad s → projection Q Λ row (g j (y * e s * z)) = 0) ∧
      ∀ y, π (G 1 * y) = ∑ j, π (G (g j y) * w j) := by
  obtain ⟨n, e, g, w, bottom, _, h⟩ := exists_blockStack_coordinates_with_filtered_shuffle_words Q Λ hQ L M f β h
  exact ⟨n, e, g, w, bottom, h⟩

/-- Finite coordinates without a choice of presentation of their shuffle indices. -/
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
      (∀ j, g j (w j) = 1) ∧ (∀ i j, i ≠ j → g i (w j) = 0) ∧
      (∀ j s, bottom j s = 0 ∨ ∃ v : Loadings row,
        ShuffleLoading row (Seq.cast h.symm s) v ∧ bottom j s = loadingIdem Q Λ row v) ∧
      (∀ j y s z, bad s → projection Q Λ row (g j (y * e s * z)) = 0) ∧
      ∀ y, π (G 1 * y) = ∑ j, π (G (g j y) * w j) := by
  obtain ⟨n, _, g, w, bottom, _, h⟩ := exists_blockStack_coordinates_with_shuffle_words Q Λ hQ L M f β h
  exact ⟨n, g, w, bottom, h⟩

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
  obtain ⟨n, g, w, _, hmul, _, _, _, _, _, _, hexpand⟩ :=
    exists_blockStack_coordinates_with_bottom Q Λ hQ L M f β h
  exact ⟨n, g, w, hmul, hexpand⟩

end Categorification.Stendhal.RedBlock
