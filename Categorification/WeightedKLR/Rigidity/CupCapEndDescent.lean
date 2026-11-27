/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapEndBlock

/-!
# The diagrams of `λ` left of a cap at the right end, on `T̃`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, in the case `j = ℓ`: the action of `T̃^λ`
"above the maximum of the cap" on the model of `K̃^{λ⁺}_λ`. A multiplicative linear map out of
the KLR algebra of `λ` which kills the dots on red strands and the crossings of two red strands
factors through the algebra of Stendhal diagrams in all orders (`CupCap.allOrdersLift`), and
hence restricts to `T̃^λ` (`CupCap.stendhalLift`). Applied to the block of the first `m` strands
of `λ⁺` (`CupCap.prefixMapKLR`) this gives the map `T̃^λ → T̃^{λ⁺}` placing a diagram of `λ` left of
the strands at the maximum (`CupCap.prefixStendhal`).

## Main definitions

* `CupCap.allOrdersLift`, `CupCap.stendhalLift`: the factorization through Stendhal diagrams.
* `CupCap.prefixStendhal`: the diagrams of `λ` on the first `m` strands of `λ⁺`, on `T̃`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

section PrefixKLR

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "μL" => Multiset.map (oldColour (I := I) ℓ le_rfl) (stendhalWeight ℓ ν)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (stendhalWeight (ℓ + 2) (ν + ν₀))

theorem insertSet_subset_endSet (s : Seq (stendhalWeight ℓ ν)) :
    insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s m le_rfl ⊆ endSet ν ν₀ := by
  intro u hu
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hu
  exact insertSeq_mem_endSet s t

omit [DecidableEq I] in
theorem isRedOrdered_of_insertSeq {s : Seq (stendhalWeight ℓ ν)}
    {t : Seq (Multiset.map (cupColour (I := I) ℓ le_rfl) (stendhalWeight 2 ν₀))}
    (h : IsRedOrdered (insertSeq (j := ℓ) (hj := le_rfl) s m le_rfl t)) : IsRedOrdered s := by
  intro a b r r' hab ha hb
  have hM : m ≤ M := by have := m_add_N (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega
  have h1 := insertSeq_lbl_lt s le_rfl t (c := ⟨a.val, by omega⟩) a a.2 rfl
  have h2 := insertSeq_lbl_lt s le_rfl t (c := ⟨b.val, by omega⟩) b b.2 rfl
  rw [ha] at h1
  rw [hb] at h2
  have := h _ _ _ _ (show (⟨a.val, by omega⟩ : Fin M) < ⟨b.val, by omega⟩ from hab) h1 h2
  rw [Fin.lt_def] at this ⊢
  simpa [oldRed, insertPos, r.2, r'.2] using this

theorem insertSeq_mem_insertSet {s s' : Seq (stendhalWeight ℓ ν)}
    {t : Seq (Multiset.map (cupColour (I := I) ℓ le_rfl) (stendhalWeight 2 ν₀))} :
    insertSeq (j := ℓ) (hj := le_rfl) s m le_rfl t ∈
      insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s' m le_rfl ↔ s' = s := by
  constructor
  · intro hu
    obtain ⟨t', -, ht⟩ := Finset.mem_image.1 hu
    apply Subtype.ext
    funext b
    have hM : m ≤ M := by have := m_add_N (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega
    have h1 := insertSeq_lbl_lt s' le_rfl t' (c := ⟨b.val, by omega⟩) b b.2 rfl
    have h2 := insertSeq_lbl_lt s le_rfl t (c := ⟨b.val, by omega⟩) b b.2 rfl
    rw [ht, h2] at h1
    exact (oldColour_injective ℓ le_rfl h1).symm
  · rintro rfl
    exact Finset.mem_image_of_mem _ (Finset.mem_univ t)

theorem prefixMapKLR_x (a : Fin m) :
    prefixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.x a) =
      KLRAlgebra.x (⟨a.val, by have := m_add_N (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega⟩ :
        Fin M) * KLRAlgebra.eSum _ (endSet ν ν₀) := by
  rw [prefixMapKLR, relabelHom_x, BlockEmb.hom_x, val_polCorner, pol_X]
  congr 2
  exact Fin.ext (by simp [prefixWindow, BlockEmb.window, windowPos])

theorem prefixMapKLR_ψ {p : ℕ} (hp : p + 1 < m) :
    prefixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.ψ p) =
      KLRAlgebra.ψ p * KLRAlgebra.eSum _ (endSet ν ν₀) := by
  rw [prefixMapKLR, relabelHom_ψ, BlockEmb.hom_ψ,
    BlockEmb.val_gψ _ (by rw [card_μL]; exact hp)]
  simp [prefixWindow, BlockEmb.window]

theorem prefixMapKLR_smul (c : k) (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    prefixMapKLR Q Λ Λc ν ν₀ (c • a) = c • prefixMapKLR Q Λ Λc ν ν₀ a := by
  unfold prefixMapKLR
  rw [map_smul, AlgHom.map_smul_of_tower, KLR.Corner.val_smul]

end PrefixKLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Lift

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {C : Type*} [Ring C] [Algebra k C]
  (G : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν) →ₙₐ[k] C)

/-- The relations of Stendhal diagrams beyond the KLR relations (arXiv:1309.3796v3,
Definition 4.5), on a map out of the KLR algebra: red strands carry no dots and do not cross. -/
structure RedRelations : Prop where
  red_dot : ∀ (a : Fin (Multiset.card (stendhalWeight ℓ ν))) (s : Seq (stendhalWeight ℓ ν)),
    (s.lbl a).isRight → G (KLRAlgebra.x a * KLRAlgebra.e s) = 0
  red_cross : ∀ (j : ℕ) (h : j + 1 < Multiset.card (stendhalWeight ℓ ν))
    (s : Seq (stendhalWeight ℓ ν)), (s.lbl ⟨j, by omega⟩).isRight →
    (s.lbl ⟨j + 1, h⟩).isRight → G (KLRAlgebra.ψ j * KLRAlgebra.e s) = 0

theorem isIdempotentElem_map_one : IsIdempotentElem (G 1) := by
  unfold IsIdempotentElem; rw [← map_mul, one_mul]

/-- `G` as a unital map into the corner of `G 1`. -/
def liftCorner :
    KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν) →ₐ[k] (isIdempotentElem_map_one G).Corner where
  toFun a := KLR.Corner.mk (G a) (by rw [← map_mul, ← map_mul, one_mul, mul_one])
  map_zero' := Subtype.ext (map_zero G)
  map_add' a b := Subtype.ext (map_add G a b)
  map_mul' a b := Subtype.ext (map_mul G a b)
  map_one' := rfl
  commutes' r := Subtype.ext (by
    change G (algebraMap k _ r) = r • G 1
    rw [← map_smul, Algebra.smul_def, mul_one])

theorem liftCorner_val (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    (liftCorner G a).val = G a := rfl

variable {G}

/-- The factorization through Stendhal diagrams in all orders, into the corner of `G 1`. -/
def allOrdersLiftCorner (hG : RedRelations G) :
    StendhalAlgebraAllOrders k Q Λ ν →ₐ[k] (isIdempotentElem_map_one G).Corner :=
  RingQuot.liftAlgHom k
    ⟨(liftCorner G).comp (KLRAlgebra.mk k (stendhalQ Q Λ) (stendhalWeight ℓ ν)), fun x y h => by
      cases h with
      | klr h => exact congrArg (liftCorner G) (RingQuot.mkAlgHom_rel k h)
      | red_dot a s ha =>
        apply KLR.Corner.ext
        simp only [AlgHom.comp_apply, map_mul, map_zero]
        rw [← map_mul (liftCorner G), liftCorner_val]
        exact hG.red_dot a s ha
      | red_cross j hj s ha hb =>
        apply KLR.Corner.ext
        simp only [AlgHom.comp_apply, map_mul, map_zero]
        rw [← map_mul (liftCorner G), liftCorner_val]
        exact hG.red_cross j hj s ha hb⟩

/-- The inclusion of a corner, as a multiplicative `k`-linear map. -/
def cornerValAlg {A : Type*} [Ring A] [Algebra k A] {E : A} (idem : IsIdempotentElem E) :
    idem.Corner →ₙₐ[k] A where
  toFun a := a.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The factorization of `G` through Stendhal diagrams in all orders.** -/
def allOrdersLift (hG : RedRelations G) : StendhalAlgebraAllOrders k Q Λ ν →ₙₐ[k] C where
  toFun z := (allOrdersLiftCorner hG z).val
  map_zero' := by rw [map_zero]; rfl
  map_add' x y := by rw [map_add]; rfl
  map_mul' x y := by rw [map_mul]; rfl
  map_smul' c z := by rw [AlgHom.map_smul_of_tower]; rfl

theorem allOrdersLift_ofKLR (hG : RedRelations G)
    (z : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    allOrdersLift hG (StendhalAlgebraAllOrders.ofKLR k Q Λ ν z) = G z := by
  obtain ⟨w, rfl⟩ := KLRAlgebra.mk_surjective z
  rw [StendhalAlgebraAllOrders.ofKLR_mk]
  have h : allOrdersLiftCorner hG (RingQuot.mkAlgHom k _ w) =
      liftCorner G (KLRAlgebra.mk k _ _ w) := RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _
  change (allOrdersLiftCorner hG (RingQuot.mkAlgHom k _ w)).val = _
  rw [h]
  rfl

/-- **The restriction of `G` to `T̃^λ`.** -/
def stendhalLift (hG : RedRelations G) : StendhalAlgebra k Q Λ ν →ₙₐ[k] C :=
  (allOrdersLift hG).comp
    (cornerValAlg (StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem (k := k) (Q := Q)
      (Λ := Λ) (ν := ν)))

theorem stendhalLift_apply (hG : RedRelations G) (z : StendhalAlgebra k Q Λ ν) :
    stendhalLift hG z = allOrdersLift hG z.val := rfl

/-- On the image of a KLR diagram, `stendhalLift` is `G` cut by the red-ordered idempotents. -/
theorem stendhalLift_topMap (hG : RedRelations G)
    (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    stendhalLift hG (topMap k Q Λ ν a) =
      G a * allOrdersLift hG (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) := by
  rw [stendhalLift_apply]
  change allOrdersLift hG (StendhalAlgebraAllOrders.ofKLR k Q Λ ν a *
    StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) = _
  rw [map_mul, allOrdersLift_ofKLR]

end Lift

section Prefix

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (stendhalWeight (ℓ + 2) (ν + ν₀))


variable (ν ν₀) in
/-- The diagrams of `λ` on the first `m` strands of `λ⁺`, in `T̃^{λ⁺}`, before descending. -/
def prefixBot :
    KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν) →ₙₐ[k]
      StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀) where
  toFun a := botMap k Q Λ Λc ℓ le_rfl ν ν₀ (prefixMapKLR Q Λ Λc ν ν₀ a)
  map_zero' := by unfold prefixMapKLR; rw [map_zero, map_zero]; exact map_zero _
  map_add' a b := by unfold prefixMapKLR; rw [map_add, map_add]; exact map_add _ _ _
  map_mul' a b := by rw [prefixMapKLR_mul, map_mul]
  map_smul' c a := by
    change botMap k Q Λ Λc ℓ le_rfl ν ν₀ (prefixMapKLR Q Λ Λc ν ν₀ (c • a)) =
      c • botMap k Q Λ Λc ℓ le_rfl ν ν₀ (prefixMapKLR Q Λ Λc ν ν₀ a)
    rw [prefixMapKLR_smul, map_smul]

theorem prefixBot_apply (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    prefixBot Q Λ Λc ν ν₀ a = botMap k Q Λ Λc ℓ le_rfl ν ν₀ (prefixMapKLR Q Λ Λc ν ν₀ a) := rfl

theorem prefixBot_eSum (s : Seq (stendhalWeight ℓ ν))
    (y : Rp) :
    botMap k Q Λ Λc ℓ le_rfl ν ν₀ (y * KLRAlgebra.eSum _ (endSet ν ν₀) *
      prefixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e s)) =
      ∑ t, botMap k Q Λ Λc ℓ le_rfl ν ν₀ (y * KLRAlgebra.e (insertSeq (j := ℓ) (hj := le_rfl) s m
        le_rfl t)) := by
  rw [prefixMapKLR_e, mul_assoc, KLRAlgebra.eSum_mul_eSum,
    Finset.inter_eq_right.2 (insertSet_subset_endSet s), KLRAlgebra.eSum, Finset.mul_sum,
    map_sum, insertSet, Finset.sum_image (fun t _ t' _ h => insertSeq_injective s le_rfl h)]

theorem redRelations_prefixBot : RedRelations (prefixBot Q Λ Λc ν ν₀) where
  red_dot a s ha := by
    rw [prefixBot_apply, prefixMapKLR_mul, prefixMapKLR_x, prefixBot_eSum]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [botMap, AlgHom.comp_apply, map_mul]
    change orderProjection _ _ _ (StendhalAlgebraAllOrders.x _ * StendhalAlgebraAllOrders.e _) = 0
    rw [StendhalAlgebraAllOrders.x_mul_e_of_red, map_zero]
    rw [insertSeq_lbl_lt s le_rfl t a a.2 rfl]
    cases h : s.lbl a with
    | inl i => rw [h] at ha; exact absurd ha (by simp)
    | inr r => rfl
  red_cross p hp s ha hb := by
    rw [prefixBot_apply, prefixMapKLR_mul, prefixMapKLR_ψ _ _ _ hp, prefixBot_eSum]
    refine Finset.sum_eq_zero fun t _ => ?_
    have hp' : p + 1 < M := by have := m_add_N (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega
    rw [botMap, AlgHom.comp_apply, ofKLR_ψ_mul_e_of_red p hp' _ ?_ ?_, map_zero]
    · rw [insertSeq_lbl_lt s le_rfl t ⟨p, by omega⟩ (by simp; omega) rfl]
      cases h : s.lbl ⟨p, by omega⟩ with
      | inl i => rw [h] at ha; exact absurd ha (by simp)
      | inr r => rfl
    · rw [insertSeq_lbl_lt s le_rfl t ⟨p + 1, hp⟩ (by simp; omega) rfl]
      cases h : s.lbl ⟨p + 1, hp⟩ with
      | inl i => rw [h] at hb; exact absurd hb (by simp)
      | inr r => rfl

variable (ν ν₀) in
/-- **The diagrams of `λ` left of a cap at the right end**: the map `T̃^λ → T̃^{λ⁺}` placing a
diagram of `λ` on the first `m` strands, beside the identity on the strands at the maximum. -/
def prefixStendhal :
    StendhalAlgebra k Q Λ ν →ₙₐ[k] StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀) :=
  stendhalLift (redRelations_prefixBot Q Λ Λc)

theorem prefixStendhal_eq (z : StendhalAlgebra k Q Λ ν) :
    ∃ a, prefixStendhal Q Λ Λc ν ν₀ z = prefixBot Q Λ Λc ν ν₀ a := by
  obtain ⟨a, ha⟩ := StendhalAlgebraAllOrders.ofKLR_surjective z.val
  refine ⟨a, ?_⟩
  rw [prefixStendhal, stendhalLift_apply, ← ha, allOrdersLift_ofKLR]

open Classical in
theorem prefixStendhal_one :
    prefixStendhal Q Λ Λc ν ν₀ 1 =
      ∑ s ∈ Finset.univ.filter (fun s : Seq (stendhalWeight ℓ ν) => IsRedOrdered s),
        botMap k Q Λ Λc ℓ le_rfl ν ν₀
          (KLRAlgebra.eSum _ (insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s m le_rfl)) := by
  classical
  rw [prefixStendhal, stendhalLift_apply, KLR.Corner.val_one]
  have hE : allOrdersLift (redRelations_prefixBot Q Λ Λc (ν := ν) (ν₀ := ν₀))
      (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) =
      allOrdersLift (redRelations_prefixBot Q Λ Λc (ν := ν) (ν₀ := ν₀))
        (∑ s ∈ Finset.univ.filter (fun s : Seq (stendhalWeight ℓ ν) => IsRedOrdered s),
          StendhalAlgebraAllOrders.e s) := rfl
  rw [hE, map_sum]
  refine Finset.sum_congr (by congr) fun s _ => ?_
  rw [StendhalAlgebraAllOrders.e, allOrdersLift_ofKLR, prefixBot_apply, prefixMapKLR_e]

theorem prefixStendhal_one_mul_e (s : Seq (stendhalWeight ℓ ν))
    (t : Seq (Multiset.map (cupColour (I := I) ℓ le_rfl) (stendhalWeight 2 ν₀))) :
    prefixStendhal Q Λ Λc ν ν₀ 1 *
      botMap k Q Λ Λc ℓ le_rfl ν ν₀ (KLRAlgebra.e (insertSeq (j := ℓ) (hj := le_rfl) s m le_rfl t)) =
      botMap k Q Λ Λc ℓ le_rfl ν ν₀ (KLRAlgebra.e (insertSeq (j := ℓ) (hj := le_rfl) s m le_rfl t)) := by
  classical
  by_cases hs : IsRedOrdered s
  · rw [prefixStendhal_one, Finset.sum_mul, Finset.sum_eq_single_of_mem s
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩)]
    · rw [← map_mul, KLRAlgebra.eSum_mul_e, ite_eq_left (insertSeq_mem_insertSet.2 rfl)]
    · intro s' _ hs'
      rw [← map_mul, KLRAlgebra.eSum_mul_e, ite_eq_right (fun h => hs' (insertSeq_mem_insertSet.1 h)),
        map_zero]
  · have h0 : botMap k Q Λ Λc ℓ le_rfl ν ν₀
        (KLRAlgebra.e (insertSeq (j := ℓ) (hj := le_rfl) s m le_rfl t)) = 0 :=
      orderProjection_e_of_not (fun h => hs (isRedOrdered_of_insertSeq h))
    rw [h0, mul_zero]

/-- `T̃^λ` acts unitally on the diagrams whose bottom is cut by the loadings `insertSeq s m t`. -/
theorem prefixStendhal_one_mul_endIdem :
    prefixStendhal Q Λ Λc ν ν₀ 1 * botMap k Q Λ Λc ℓ le_rfl ν ν₀ (KLRAlgebra.eSum _ (endSet ν ν₀)) =
      botMap k Q Λ Λc ℓ le_rfl ν ν₀ (KLRAlgebra.eSum _ (endSet ν ν₀)) := by
  rw [KLRAlgebra.eSum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  obtain ⟨s, t, rfl⟩ := mem_endSet.1 hu
  exact prefixStendhal_one_mul_e Q Λ Λc s t

theorem endIdem_mul_prefixBot (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    botMap k Q Λ Λc ℓ le_rfl ν ν₀ (KLRAlgebra.eSum _ (endSet ν ν₀)) * prefixBot Q Λ Λc ν ν₀ a =
      prefixBot Q Λ Λc ν ν₀ a := by
  rw [prefixBot_apply, ← map_mul, prefixMapKLR]
  exact congrArg _ (KLR.Corner.E_mul_val _)

theorem prefixBot_mul_endIdem (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    prefixBot Q Λ Λc ν ν₀ a * botMap k Q Λ Λc ℓ le_rfl ν ν₀ (KLRAlgebra.eSum _ (endSet ν ν₀)) =
      prefixBot Q Λ Λc ν ν₀ a := by
  rw [prefixBot_apply, ← map_mul, prefixMapKLR]
  exact congrArg _ (KLR.Corner.val_mul_E _)

theorem commute_prefixBot_endMapKLR (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν))
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    Commute (prefixBot Q Λ Λc ν ν₀ a) (botMap k Q Λ Λc ℓ le_rfl ν ν₀ (endMapKLR Q Λ Λc ν ν₀ x)) :=
  (commute_prefixMapKLR_endMapKLR Q Λ Λc ν ν₀ a x).map (botMap k Q Λ Λc ℓ le_rfl ν ν₀)

end Prefix

end Categorification.Stendhal.CupCap
