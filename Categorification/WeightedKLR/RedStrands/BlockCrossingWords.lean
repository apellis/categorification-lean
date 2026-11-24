/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OrderedBlockAction
import Categorification.TypeA.GapSort

/-!
# A reduced upper factor with uncrossed lower boundary

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 (ordinary diagrams).
Order the strands of each top block by their positions at the bottom of a reduced
permutation diagram. The resulting block permutations introduce only inversions of that
diagram. Their juxtaposition is thus a reduced upper factor, with uncrossed red order
at its lower boundary. No basis theorem for a quotient is used here.
-/
noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra TypeA Equiv BraidedStendhalAlgebra
open scoped TensorProduct
variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "S" => stendhalQ Q Λ
local notation "botOrd" => (fun (_ : RedBlock I ℓ) => 1)

/-- `key` records the bottom position of each strand at the top. -/
def OrderedBy {μ : Multiset (I ⊕ Fin ℓ)} (t : Seq μ) (key : Fin μ.card → ℕ)
    (R : Fin ℓ → Fin ℓ → Prop) : Prop :=
  ∀ a b r r', key a < key b → t.lbl a = .inr r → t.lbl b = .inr r' → R r r'

private def BelowKey {n : ℕ} (A : List ℕ) (key : Fin n → ℕ) : Prop :=
  ∀ i j : Fin n, i < j → (wordProd n A)⁻¹ j < (wordProd n A)⁻¹ i → key j < key i

private theorem belowKey_append {n d m : ℕ} (h : n+d=m) {A B : List ℕ} {key : Fin m → ℕ}
    (hA : ValidWord n A) (hB : ValidWord d B)
    (h₁ : BelowKey A (fun i => key (blockEquiv h (.inl i))))
    (h₂ : BelowKey B (fun i => key (blockEquiv h (.inr i)))) : BelowKey (A ++ shiftWord n B) key := by
  intro i j hij hv
  rw [wordProd_append_shiftWord h hA hB, blockPerm_inv] at hv
  obtain ⟨i | i,rfl⟩ := (blockEquiv h).surjective i <;> obtain ⟨j | j,rfl⟩ := (blockEquiv h).surjective j
  · exact h₁ _ _ hij (by simpa only [blockPerm_inl, blockEquiv_inl_lt_inl] using hv)
  · simp only [blockPerm_inr, blockPerm_inl, not_blockEquiv_inr_lt_inl] at hv
  · exact (not_blockEquiv_inr_lt_inl h j i hij).elim
  · exact h₂ _ _ ((blockEquiv_inr_lt_inr h).1 hij) (by simpa only [blockPerm_inr, blockEquiv_inr_lt_inr] using hv)

private theorem cast_below {n m : ℕ} (h : n = m) {A : List ℕ} {key : Fin m → ℕ}
    (ha : BelowKey A (key ∘ Fin.cast h)) : BelowKey A key := by subst m; exact ha

private theorem read_word (B : RedBlock I ℓ) (A : List ℕ) :
    readBlock Q Λ B (ofKLR k Q (Λ ∘ B.label) B.black (ψw A)) = ψw A := by
  induction A with
  | nil => simp only [ψw_nil, map_one]
  | cons j A ih =>
    rw [ψw_cons, map_mul, map_mul, ih, ψw_cons]
    congr 1
    change relabelEquiv _ (toKLR _ _ _ _ (ofKLR _ _ _ _ (ψ j))) = _
    rw [toKLR_ofKLR_ψ]; exact relabelHom_ψ _ _

private theorem oneBlock (B : RedBlock I ℓ) (s : Seq B.localWeight) (key : Fin B.weight.card → ℕ)
    (hk : Function.Injective key) (R : Fin ℓ → Fin ℓ → Prop)
    (ho : OrderedBy (Seq.map B.colour s) key R) (hr : ∀ r r', R (B.label r) (B.label r') → r < r') :
    ∃ A, IsReduced B.weight.card A ∧ BelowKey A key ∧ ∃ x : diagramAlgebra Q Λ B,
      x * redProj k Q (Λ ∘ B.label) B.black (List.finRange B.size) = x ∧
      readBlock Q Λ B x = e (Seq.map B.colour s) * ψw A := by
  let h := (Multiset.card_map B.colour B.localWeight).symm
  let K := key ∘ Fin.cast h
  obtain ⟨v,hv⟩ := exists_perm_lt_iff K (hk.comp (finCongr h).injective)
  let A := canWord B.localWeight.card v⁻¹
  have ha := isReduced_canWord B.localWeight.card v⁻¹
  have hw : (wordProd B.localWeight.card A)⁻¹ = v := by simp [A]
  refine ⟨A,h ▸ ha,cast_below h (fun i j _ hij => (hv j i).1 (by rwa [hw] at hij)),
    ofKLR _ _ _ _ (e s * ψw A), ?_, ?_⟩
  · have hs : IsRedOrdered (v • s) := by
      intro a b r r' hab har hbr
      apply hr
      apply ho (Fin.cast h (v⁻¹ a)) (Fin.cast h (v⁻¹ b)) _ _ ((hv _ _).1 (by simpa using hab))
      · simp only [Seq.map_lbl, Fin.cast_cast, Fin.cast_eq_self, show s.lbl (v⁻¹ a) = .inr r from har]; rfl
      · simp only [Seq.map_lbl, Fin.cast_cast, Fin.cast_eq_self, show s.lbl (v⁻¹ b) = .inr r' from hbr]; rfl
    change _ * ofKLR _ _ _ _ (redIdem _ _ _ _) = _
    rw [← map_mul, e_mul_ψw, hw, mul_assoc, e_mul_redIdem, ite_eq_left ((redWord_eq_finRange_iff _).2 hs)]
  · rw [map_mul, map_mul, readBlock_idem, read_word]

private theorem concat_top {a b : Multiset (I ⊕ Fin ℓ)} {A B : List ℕ}
    (hA : ValidWord a.card A) (hB : ValidWord b.card B) (s : Seq a) (t : Seq b) :
    concat S a b ((e s * ψw A) ⊗ₜ (e t * ψw B)) = e (s.append t) * ψw (A ++ shiftWord a.card B) := by
  simp only [e_mul_ψw, wordProd_append_shiftWord (Seq.card_add' a b) hA hB, blockPerm_inv,
    Seq.blockPerm_smul_append]
  simpa only [map_one, one_mul] using (concat_pol_ψw_e (Q := S) 1 1 hA hB
    ((wordProd _ A)⁻¹ • s) ((wordProd _ B)⁻¹ • t))

/-- The upper part of an adapted reduced word is a juxtaposition with the ordered lower
projector. Its inversions (viewed from the top) are all required by the specified bottom
positions. This is before killing either local violations or higher standard loadings. -/
theorem exists_orderedBlock_word (R : Fin ℓ → Fin ℓ → Prop) : ∀ (Bs : List (RedBlock I ℓ))
    (t : Loadings Bs) (key : Fin (weightSum Bs).card → ℕ), Function.Injective key →
    OrderedBy (place Bs t) key R → (∀ B ∈ Bs, ∀ r r', R (B.label r) (B.label r') → r < r') →
    ∃ A, IsReduced (weightSum Bs).card A ∧
      (∀ i j : Fin (weightSum Bs).card, i < j → (wordProd _ A)⁻¹ j < (wordProd _ A)⁻¹ i → key j < key i) ∧
      ∃ x : diagrams Q Λ Bs, x * orderedIdem Q Λ botOrd Bs = x ∧ juxtapose Q Λ Bs x = e (place Bs t) * ψw A
  | [], t, _, _, _, _ => by
    refine ⟨[], ⟨validWord_nil _,by simp⟩, fun i => Fin.elim0 i, 1, mul_one _, ?_⟩
    rw [ψw_nil, mul_one]; exact juxtapose_loadingIdem Q Λ [] t
  | B :: Bs, t, key, hk, ho, hr => by
    let h := Seq.card_add' B.weight (weightSum Bs)
    let l := fun i : Fin B.weight.card => blockEquiv h (.inl i)
    let r := fun i : Fin (weightSum Bs).card => blockEquiv h (.inr i)
    have hl : Function.Injective l := (blockEquiv h).injective.comp Sum.inl_injective
    have hr' : Function.Injective r := (blockEquiv h).injective.comp Sum.inr_injective
    have atL (i) : (place (B :: Bs) t).lbl (l i) = (Seq.map B.colour t.1).lbl i := Seq.append_posL _ _ _
    have atR (i) : (place (B :: Bs) t).lbl (r i) = (place Bs t.2).lbl i := Seq.append_posR _ _ _
    have hoL : OrderedBy (Seq.map B.colour t.1) (key ∘ l) R := fun i j a b hij hi hj =>
      ho (l i) (l j) a b hij ((atL i).trans hi) ((atL j).trans hj)
    have hoR : OrderedBy (place Bs t.2) (key ∘ r) R := fun i j a b hij hi hj =>
      ho (r i) (r j) a b hij ((atR i).trans hi) ((atR j).trans hj)
    obtain ⟨A,hA,ha,x,hx,hX⟩ := oneBlock Q Λ B t.1 (key ∘ l) (hk.comp hl) R hoL (hr B (.head _))
    obtain ⟨D,hD,hd,y,hy,hY⟩ := exists_orderedBlock_word R Bs t.2 (key ∘ r) (hk.comp hr') hoR
      (fun B' hB => hr B' (.tail _ hB))
    exact ⟨A ++ shiftWord _ D, hA.append_shiftWord h hD, belowKey_append h hA.1 hD.1 ha hd,
      x ⊗ₜ y, by simp only [orderedIdem, Algebra.TensorProduct.tmul_mul_tmul, Equiv.Perm.coe_one, List.map_id_fun, id_eq, hx, hy],
      by rw [juxtapose_tmul, hX, hY]; exact concat_top Q Λ hA.1 hD.1 _ _⟩

/-- Transport the reduced upper factor to the alphabet and weight of the global column. -/
theorem exists_orderedBlock_word_cast (Bs : List (RedBlock I ℓ)) {μ : Multiset (I ⊕ Fin ℓ)}
    (h : weightSum Bs = μ) (s : Loadings Bs) (τ : Perm (Fin μ.card)) (R : Fin ℓ → Fin ℓ → Prop)
    (ho : OrderedBy (Seq.cast h (place Bs s)) (fun j => (τ⁻¹ j).val) R)
    (hr : ∀ B ∈ Bs, ∀ r r', R (B.label r) (B.label r') → r < r') :
    ∃ A, IsReduced μ.card A ∧ invSet μ.card (wordProd μ.card A)⁻¹ ⊆ invSet μ.card τ⁻¹ ∧
      ∃ x : diagrams Q Λ Bs, x * orderedIdem Q Λ botOrd Bs = x ∧
        castKLR S h (juxtapose Q Λ Bs x) = e (Seq.cast h (place Bs s)) * ψw A := by
  subst μ
  obtain ⟨A,hA,hv,x,hx,hX⟩ := exists_orderedBlock_word Q Λ R Bs s _
    (Fin.val_injective.comp τ⁻¹.injective) ho hr
  refine ⟨A,hA,?_,x,hx,hX⟩
  rintro ⟨i,j⟩ hij
  rw [mem_invSet_pair] at hij ⊢
  exact ⟨hij.1,hv i j hij.1 hij.2⟩

variable (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
local notation "Bs" => adjacentRow L M f β
local notation "κ₀" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "F" => stackBlocks Q Λ L M f β h
local notation "E₀" => orderedIdem Q Λ botOrd Bs

omit [DecidableEq I] in
private theorem localRedOrder (i : Seq μ) (hi : redWord i = κ₀) : ∀ B ∈ Bs, ∀ a b : Fin B.size,
    (∃ p q, i.lbl p = .inr (B.label a) ∧ i.lbl q = .inr (B.label b) ∧ p < q) → a < b := by
  intro B hB a b ⟨p,q,hp,hq,hpq⟩
  have hne : a ≠ b := by rintro rfl; exact hpq.ne (lbl_inj_of_inr i _ hp hq)
  rcases List.mem_append.1 hB with hB | hB
  · obtain ⟨s,_,rfl⟩ := List.mem_map.1 hB; exact (hne (Subsingleton.elim ..)).elim
  rcases List.mem_cons.1 hB with rfl | hB
  · by_contra! hab
    have hba : b < a := lt_of_le_of_ne hab hne.symm
    have ha2 : a.val < 2 := a.isLt
    have hb2 : b.val < 2 := b.isLt
    have ha : a = 1 := Fin.ext (by change (a : ℕ) = 1; omega)
    have hb : b = 0 := Fin.ext (by change (b : ℕ) = 0; omega)
    subst a; subst b
    exact hpq.not_gt (lt_of_redWord_eq_append hi hq hp)
  · obtain ⟨s,_,rfl⟩ := List.mem_map.1 hB; exact (hne (Subsingleton.elim ..)).elim

/-- Reduced representatives whose upper word is an ordered local diagram whenever the
end loadings match (Webster, arXiv:1309.3796v2, proof of Lemma 6.8). -/
theorem exists_reduced_crossing_cut_affine (s : Loadings Bs) (i : Seq μ) (hi : redWord i = κ₀) (w : Perm (Fin m)) :
    ∃ A D, (IsReduced m (A ++ D) ∧ wordProd m (A ++ D) = w) ∧
      (w • i = Seq.cast h (place Bs s) → ∃ x : diagrams Q Λ Bs, x * E₀ = x ∧
        castKLR S h (juxtapose Q Λ Bs x) = e (Seq.cast h (place Bs s)) * ψw A) := by
  by_cases hw : w • i = Seq.cast h (place Bs s)
  swap
  · exact ⟨[],canWord m w,⟨isReduced_canWord _ _,wordProd_canWord _ _⟩,fun he => (hw he).elim⟩
  let rel := fun a b : Fin ℓ => ∃ p q, i.lbl p = .inr a ∧ i.lbl q = .inr b ∧ p < q
  have ho : OrderedBy (Seq.cast h (place Bs s)) (fun j => (w⁻¹ j).val) rel := by
    rw [← hw]; intro a b r r' hab ha hb
    exact ⟨_,_,ha,hb,hab⟩
  obtain ⟨A,hA,hv,x,hx,hX⟩ := exists_orderedBlock_word_cast Q Λ Bs h s w rel ho
    (localRedOrder L M f β i hi)
  let u := wordProd m A
  have hl : length m (u⁻¹ * w) + length m u = length m w := by
    have H := length_add_of_invSet_subset hv
    rw [inv_inv, ← length_inv (w⁻¹ * wordProd m A), mul_inv_rev, inv_inv, length_inv, length_inv] at H
    exact H
  let D := canWord m (u⁻¹ * w)
  have hD : wordProd m D = u⁻¹ * w := wordProd_canWord _ _
  have hprod : wordProd m (A ++ D) = w := by rw [wordProd_append,hD]; exact mul_inv_cancel_left u w
  refine ⟨A,D,⟨⟨validWord_append.2 ⟨hA.1, validWord_canWord _ _⟩,?_⟩,hprod⟩,
    fun _ => ⟨x,hx,hX⟩⟩
  rw [List.length_append, hprod, show D.length = length m (u⁻¹ * w) from length_canWord _ _, hA.2, Nat.add_comm]
  exact hl

/-- The same reduced representatives after projection to the violated quotient. -/
theorem exists_reduced_crossing_cut (s : Loadings Bs) (i : Seq μ) (hi : redWord i = κ₀) (w : Perm (Fin m)) :
    ∃ A D, (IsReduced m (A ++ D) ∧ wordProd m (A ++ D) = w) ∧
      (w • i = Seq.cast h (place Bs s) → ∃ x : diagrams Q Λ Bs, x * E₀ = x ∧
        F x = π (e (Seq.cast h (place Bs s)) * ψw A)) := by
  obtain ⟨A,D,hw,hx⟩ := exists_reduced_crossing_cut_affine Q Λ L M f β h s i hi w
  refine ⟨A,D,hw,fun he => ?_⟩
  obtain ⟨x,h₀,hX⟩ := hx he
  exact ⟨x,h₀,congrArg π hX⟩

end Categorification.Stendhal.RedBlock
