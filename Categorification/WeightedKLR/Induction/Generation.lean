/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Induction.Monoidal
import Categorification.WeightedKLR.KLR.SpacedCrossing

/-!
# Generation clause of Webster's Proposition 2.18

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4, Proposition
2.18, last clause: the monoidal category of `⊕_ν W^ϑ_ν`-modules is generated under induction by
the rank-one algebras `W_{α_i}`, in the sense that the projectives coming from `R_ν` are iterated
inductions of the regular modules `W_{α_i}`.

**Reading of `R_ν`.** The symbol `R_ν` is not defined in v4 of the source. Following the
maintainer's decision, it is read as the ordinary (unweighted) KLR algebra, realized inside
`W^ϑ_ν` as the corner `e(B_s) W^ϑ_ν e(B_s)` of the loadings whose strands are evenly spaced, at
distance `s = WeightedGraph.spacing Γ > ∑_e |ϑ_e|`; Proposition 2.14 (`spacedEquiv`) identifies
this corner with `R(ν)`. The literal reading with `R_ν = W^ϑ_ν` is false in general: it fails
for a weighted Kronecker quiver, and Corollary 2.16 relates `W^ϑ_ν` to the KLR algebra (by a
Morita equivalence) only for forests.

For a sequence `i = (i₁, …, iₙ)` of colours, `e(B_s(i))` is the idempotent of the full chamber of
the configuration with the strand of `iₘ` at position `s m` (`spacedW`). The results:

* `castChamber_chamber_spacedFull`: juxtaposing the evenly spaced chambers of `i` and `j` gives
  the evenly spaced chamber of the concatenation `ij` (`Seq.append`).
* `inductionMap_spacedW`: hence `ι_{ν₁;ν₂}(e(B_s(i)) ⊗ e(B_s(j))) = e(B_s(ij))`.
* `juxtUnits_eq_spacedW`: the iterated juxtaposition `e_{i₁} ∘ ⋯ ∘ e_{iₙ}` of the units of the
  one-strand algebras `W_{α_{iₘ}}` is `e(B_s(i₁ ⋯ iₙ))`.
* `InductionAlong.indLIdealEquiv`: induction along a ring map `φ` takes the left ideal `A f` of an
  idempotent `f` to `B φ(f)`; `ExtTensor.lIdealEquiv`: `A₁ e₁ ⊠ A₂ e₂ ≅ (A₁ ⊗ A₂)(e₁ ⊗ e₂)`.
* `indSpacedEquiv`: `Ind(W_{ν₁} e(B_s(i)) ⊠ W_{ν₂} e(B_s(j))) ≅ W_{ν₁+ν₂} e(B_s(ij))`. With
  `one_eq_spacedW_single` (`W_{α_c} e(B_s(c)) = W_{α_c}`) this exhibits `W_ν e(B_s(i₁ ⋯ iₙ))`
  as the iterated induction of the regular modules `W_{α_{iₘ}}`.

The weight of a concatenation is read through `Seq.toFinsupp_add` and `castW`.
-/

namespace Categorification.KLR.Seq

open Categorification.WeightedKLR

variable {I : Type*} {ν₁ ν₂ : Multiset I}

/-- The concatenation of two sequences. -/
def append (i : Seq ν₁) (j : Seq ν₂) : Seq (ν₁ + ν₂) :=
  ⟨fun a => Fin.append i.1 j.1 (Fin.cast (Multiset.card_add ν₁ ν₂) a), by
    have hi := i.2
    have hj := j.2
    rw [Fin.univ_val_map] at hi hj ⊢
    rw [← List.ofFn_congr (Multiset.card_add ν₁ ν₂).symm, List.ofFn_fin_append,
      ← Multiset.coe_add, hi, hj]⟩

/-- The position of `a` in the first part of a concatenation. -/
def inlPos (a : Fin (Multiset.card ν₁)) : Fin (Multiset.card (ν₁ + ν₂)) :=
  Fin.cast (Multiset.card_add ν₁ ν₂).symm (Fin.castAdd _ a)

/-- The position of `b` in the second part of a concatenation. -/
def inrPos (b : Fin (Multiset.card ν₂)) : Fin (Multiset.card (ν₁ + ν₂)) :=
  Fin.cast (Multiset.card_add ν₁ ν₂).symm (Fin.natAdd _ b)

@[simp] theorem append_inlPos (i : Seq ν₁) (j : Seq ν₂) (a : Fin (Multiset.card ν₁)) :
    (i.append j).1 (inlPos a) = i.1 a := by
  simp [append, inlPos]

@[simp] theorem append_inrPos (i : Seq ν₁) (j : Seq ν₂) (b : Fin (Multiset.card ν₂)) :
    (i.append j).1 (inrPos b) = j.1 b := by
  simp [append, inrPos]

theorem card_filter_cast {m n : ℕ} (h : m = n) (p : Fin n → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = (Finset.univ.filter fun a : Fin m => p (Fin.cast h a)).card := by
  subst h
  simp


theorem inlPos_lt_inlPos {a c : Fin (Multiset.card ν₁)} :
    (inlPos (ν₂ := ν₂) c < inlPos a) ↔ c < a := by
  rw [Fin.lt_def, Fin.lt_def]; simp [inlPos]

theorem inrPos_lt_inrPos {b c : Fin (Multiset.card ν₂)} :
    (inrPos (ν₁ := ν₁) c < inrPos b) ↔ c < b := by
  rw [Fin.lt_def, Fin.lt_def]; simp [inrPos]

theorem inlPos_lt_inrPos (a : Fin (Multiset.card ν₁)) (b : Fin (Multiset.card ν₂)) :
    inlPos a < inrPos b := by
  simp only [inlPos, inrPos, Fin.lt_def, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
  omega

variable [DecidableEq I]

theorem rank_append_inlPos (i : Seq ν₁) (j : Seq ν₂) (a : Fin (Multiset.card ν₁)) :
    (i.append j).rank (inlPos a) = i.rank a := by
  rw [rank, card_filter_cast (Multiset.card_add ν₁ ν₂).symm, Finset.card_filter,
    Fin.sum_univ_add, rank, Finset.card_filter]
  have h1 : ∀ c, Fin.cast (Multiset.card_add ν₁ ν₂).symm (Fin.castAdd _ c) = inlPos (ν₂ := ν₂) c :=
    fun _ => rfl
  have h2 : ∀ c, Fin.cast (Multiset.card_add ν₁ ν₂).symm (Fin.natAdd _ c) = inrPos (ν₁ := ν₁) c :=
    fun _ => rfl
  simp only [h1, h2, append_inlPos, append_inrPos, inlPos_lt_inlPos,
    (inlPos_lt_inrPos a _).not_gt, false_and, ite_false, Finset.sum_const_zero, add_zero]

theorem rank_append_inrPos (i : Seq ν₁) (j : Seq ν₂) (b : Fin (Multiset.card ν₂)) :
    (i.append j).rank (inrPos b) = ν₁.count (j.1 b) + j.rank b := by
  rw [rank, card_filter_cast (Multiset.card_add ν₁ ν₂).symm, Finset.card_filter,
    Fin.sum_univ_add, rank, Finset.card_filter, count_eq_card i, Finset.card_filter]
  have h1 : ∀ c, Fin.cast (Multiset.card_add ν₁ ν₂).symm (Fin.castAdd _ c) = inlPos (ν₂ := ν₂) c :=
    fun _ => rfl
  have h2 : ∀ c, Fin.cast (Multiset.card_add ν₁ ν₂).symm (Fin.natAdd _ c) = inrPos (ν₁ := ν₁) c :=
    fun _ => rfl
  simp only [h1, h2, append_inlPos, append_inrPos, inrPos_lt_inrPos, inlPos_lt_inrPos, true_and]


theorem toFinsupp_add (ν₁ ν₂ : Multiset I) :
    Multiset.toFinsupp ν₁ + Multiset.toFinsupp ν₂ = Multiset.toFinsupp (ν₁ + ν₂) :=
  (map_add Multiset.toFinsupp ν₁ ν₂).symm

open Juxtapose in
theorem strandAt_append_inlPos (i : Seq ν₁) (j : Seq ν₂) (a : Fin (Multiset.card ν₁)) :
    (i.append j).strandAt (inlPos a) =
      castStrand (toFinsupp_add ν₁ ν₂) (inlStrand _ _ (i.strandAt a)) := by
  refine strand_ext (Subtype.ext ?_) ?_
  · rw [castStrand_colour]
    exact append_inlPos i j a
  · rw [castStrand_rank]
    exact rank_append_inlPos i j a

open Juxtapose in
theorem strandAt_append_inrPos (i : Seq ν₁) (j : Seq ν₂) (b : Fin (Multiset.card ν₂)) :
    (i.append j).strandAt (inrPos b) =
      castStrand (toFinsupp_add ν₁ ν₂) (inrStrand _ _ (j.strandAt b)) := by
  refine strand_ext (Subtype.ext ?_) ?_
  · rw [castStrand_colour]
    exact append_inrPos i j b
  · rw [castStrand_rank]
    show (i.append j).rank (inrPos b) = Multiset.toFinsupp ν₁ (j.1 b) + j.rank b
    rw [rank_append_inrPos, Multiset.toFinsupp_apply]

open Juxtapose in
theorem posOf_append_inl (i : Seq ν₁) (j : Seq ν₂) (s : Strand (Multiset.toFinsupp ν₁)) :
    (i.append j).posOf (castStrand (toFinsupp_add ν₁ ν₂) (inlStrand _ _ s)) =
      inlPos (i.posOf s) := by
  conv_lhs => rw [← i.strandAt_posOf s, ← strandAt_append_inlPos i j]
  exact posOf_strandAt _ _

open Juxtapose in
theorem posOf_append_inr (i : Seq ν₁) (j : Seq ν₂) (s : Strand (Multiset.toFinsupp ν₂)) :
    (i.append j).posOf (castStrand (toFinsupp_add ν₁ ν₂) (inrStrand _ _ s)) =
      inrPos (j.posOf s) := by
  conv_lhs => rw [← j.strandAt_posOf s, ← strandAt_append_inrPos i j]
  exact posOf_strandAt _ _


omit [DecidableEq I] in
/-- The sequence of a list of colours. -/
def ofList (l : List I) : Seq (l : Multiset I) :=
  ⟨fun a => l.get (Fin.cast (Multiset.coe_card l) a), by
    rw [Fin.univ_val_map, ← List.ofFn_congr (Multiset.coe_card l).symm, List.ofFn_get]⟩

omit [DecidableEq I] in
theorem append_ofList (c : I) (l : List I) :
    (ofList [c]).append (ofList l) = (ofList (c :: l) : Seq ((↑[c] : Multiset I) + ↑l)) := by
  apply Subtype.ext
  funext a
  obtain ⟨n, hn⟩ := a
  cases n with
  | zero => rfl
  | succ n =>
    have hn' : n < Multiset.card (l : Multiset I) := by
      simp only [Multiset.card_add, Multiset.coe_card, List.length_singleton] at hn ⊢
      omega
    have hc : Fin.cast (Multiset.card_add _ _) ⟨n + 1, hn⟩ =
        Fin.natAdd (Multiset.card ((↑[c] : Multiset I))) ⟨n, hn'⟩ :=
      Fin.ext (by
        rw [Fin.val_natAdd]
        show n + 1 = Multiset.card ((↑[c] : Multiset I)) + n
        simp [Nat.add_comm])
    show Fin.append (ofList [c]).1 (ofList l).1 (Fin.cast (Multiset.card_add _ _) ⟨n + 1, hn⟩) = _
    rw [hc, Fin.append_right]
    rfl

end Categorification.KLR.Seq

namespace Categorification.InductionAlong

open MulOpposite

universe u v

variable {A : Type u} [Ring A] {B : Type u} [Ring B] {φ : A →ₙ+* B} {f : A}

theorem mul_mem_lIdeal_map (z : Corner φ) (a : lIdeal f) :
    z.1 * φ a.1 ∈ lIdeal (φ f) := by
  rw [mem_lIdeal, mul_assoc, ← map_mul, a.2]

theorem mem_corner_of_mem_lIdeal_map {w : B} (hw : w ∈ lIdeal (φ f)) : w ∈ lIdeal (φ 1) := by
  rw [mem_lIdeal] at hw ⊢
  rw [← hw, mul_assoc, ← map_mul, mul_one]

variable (φ f) in
/-- The map `B φ(1) ⊗_A A f → B φ(f)`, `z ⊗ a ↦ z φ(a)`. -/
noncomputable def indLIdealMap : Ind (lIdeal f) φ →ₗ[B] lIdeal (φ f) :=
  Ind.lift (fun z a => ⟨z.1 * φ a.1, mul_mem_lIdeal_map z a⟩)
    (fun _ _ _ => Subtype.ext (add_mul _ _ _))
    (fun z a a' => Subtype.ext (by
      change z.1 * φ (a.1 + a'.1) = z.1 * φ a.1 + z.1 * φ a'.1
      rw [map_add, mul_add]))
    (fun z a n => Subtype.ext (by
      change z.1 * φ a * φ n.1 = z.1 * φ (a * n.1)
      rw [map_mul, mul_assoc]))
    (fun _ _ _ => Subtype.ext (mul_assoc _ _ _))

/-- The class `w ⊗ f` of an element `w` of `B φ(f)`. -/
def cornerOfLIdeal (w : lIdeal (φ f)) : Corner φ := ⟨w.1, mem_corner_of_mem_lIdeal_map w.2⟩

theorem cornerOfLIdeal_add (w w' : lIdeal (φ f)) :
    cornerOfLIdeal (w + w') = cornerOfLIdeal w + cornerOfLIdeal w' := rfl

theorem cornerOfLIdeal_smul (b : B) (w : lIdeal (φ f)) :
    cornerOfLIdeal (b • w) = b • cornerOfLIdeal w := rfl

variable (φ) in
/-- The inverse map `B φ(f) → B φ(1) ⊗_A A f`, `w ↦ w ⊗ f`. -/
noncomputable def indLIdealInv (hf : IsIdempotentElem f) : lIdeal (φ f) →ₗ[B] Ind (lIdeal f) φ where
  toFun w := Ind.tmul (cornerOfLIdeal w) ⟨f, hf.eq⟩
  map_add' w w' := by rw [cornerOfLIdeal_add, Ind.add_tmul]
  map_smul' b w := by rw [cornerOfLIdeal_smul, RingHom.id_apply, Ind.smul_tmul]

variable (φ) in
/-- **Induction of a cyclic projective module**: for an idempotent `f` of `A`, induction along
`φ` takes the left ideal `A f` to the left ideal `B φ(f)`, by `z ⊗ a ↦ z φ(a)`. -/
noncomputable def indLIdealEquiv (hf : IsIdempotentElem f) :
    Ind (lIdeal f) φ ≃ₗ[B] lIdeal (φ f) :=
  LinearEquiv.ofLinearMap (indLIdealMap φ f) (indLIdealInv φ hf)
    (LinearMap.ext fun w => Subtype.ext w.2)
    (Ind.ext fun z a => by
      change Ind.tmul (cornerOfLIdeal (indLIdealMap φ f (Ind.tmul z a))) ⟨f, hf.eq⟩ = Ind.tmul z a
      have h1 : cornerOfLIdeal (indLIdealMap φ f (Ind.tmul z a)) = op a.1 • z := rfl
      rw [h1, Ind.op_smul_tmul]
      congr 1
      exact Subtype.ext a.2)

@[simp] theorem indLIdealEquiv_tmul (hf : IsIdempotentElem f) (z : Corner φ) (a : lIdeal f) :
    (indLIdealEquiv φ hf (Ind.tmul z a)).1 = z.1 * φ a.1 := rfl

theorem Ind.map_map {N N' : Type v} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (g : N →ₗ[A] N') (g' : N' →ₗ[A] N) (h : g'.comp g = LinearMap.id) :
    (Ind.map (φ := φ) g').comp (Ind.map g) = LinearMap.id := by
  rw [← Ind.map_comp, h, Ind.map_id]

/-- Induction along `φ` of an isomorphism of `A`-modules. -/
noncomputable def Ind.congr {N N' : Type v} [AddCommGroup N] [Module A N] [AddCommGroup N']
    [Module A N'] (g : N ≃ₗ[A] N') : Ind N φ ≃ₗ[B] Ind N' φ :=
  LinearEquiv.ofLinearMap (Ind.map g.toLinearMap) (Ind.map g.symm.toLinearMap)
    (Ind.map_map _ _ (LinearMap.ext g.apply_symm_apply))
    (Ind.map_map _ _ (LinearMap.ext g.symm_apply_apply))

end Categorification.InductionAlong

namespace Categorification.ExtTensor

open scoped TensorProduct

variable {k : Type*} [CommRing k] {A₁ A₂ : Type*} [Ring A₁] [Algebra k A₁] [Ring A₂]
  [Algebra k A₂] {e₁ : A₁} {e₂ : A₂}

/-- Right multiplication by an idempotent, onto the left ideal it generates. -/
def rMulIdem (he : IsIdempotentElem e₁) : A₁ →ₗ[k] lIdeal e₁ where
  toFun a := ⟨a * e₁, by rw [mem_lIdeal, mul_assoc, he.eq]⟩
  map_add' a b := Subtype.ext (add_mul _ _ _)
  map_smul' c a := Subtype.ext (smul_mul_assoc _ _ _)

theorem rMulIdem_val (he : IsIdempotentElem e₁) (y : lIdeal e₁) : rMulIdem (k := k) he y.1 = y :=
  Subtype.ext y.2

/-- The inclusion `A e₁ ⊠ A e₂ → A₁ ⊗ A₂`. -/
noncomputable def lIdealIncl :
    ExtTensor k (lIdeal e₁) (lIdeal e₂) →ₗ[A₁ ⊗[k] A₂] A₁ ⊗[k] A₂ :=
  (selfEquiv k A₁ A₂).toLinearMap.comp (map (lIdeal e₁).subtype (lIdeal e₂).subtype)

theorem lIdealIncl_tmul (y₁ : lIdeal e₁) (y₂ : lIdeal e₂) :
    lIdealIncl (k := k) (tmul y₁ y₂) = y₁.1 ⊗ₜ y₂.1 := rfl

theorem lIdealIncl_mem (x : ExtTensor k (lIdeal e₁) (lIdeal e₂)) :
    lIdealIncl x ∈ lIdeal (e₁ ⊗ₜ[k] e₂) := by
  induction x using induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul y₁ y₂ =>
    rw [lIdealIncl_tmul, mem_lIdeal, Algebra.TensorProduct.tmul_mul_tmul, y₁.2, y₂.2]
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- Right multiplication by `e₁ ⊗ e₂`, with values in `A e₁ ⊠ A e₂`. -/
noncomputable def lIdealProj (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) :
    A₁ ⊗[k] A₂ →ₗ[k] ExtTensor k (lIdeal e₁) (lIdeal e₂) :=
  (equivTensor (k := k) (P := lIdeal e₁) (Q := lIdeal e₂)).symm.toLinearMap.comp
    (TensorProduct.map (rMulIdem he₁) (rMulIdem he₂))

theorem lIdealProj_tmul (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) (a : A₁)
    (b : A₂) : lIdealProj (k := k) he₁ he₂ (a ⊗ₜ b) =
      tmul (rMulIdem (k := k) he₁ a) (rMulIdem (k := k) he₂ b) :=
  rfl

theorem lIdealProj_mul (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    (t x : A₁ ⊗[k] A₂) : lIdealProj (k := k) he₁ he₂ (t * x) = t • lIdealProj he₁ he₂ x := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => rw [add_mul, map_add, hs, ht, add_smul]
  | tmul a b =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, smul_add]
    | tmul a' b' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, lIdealProj_tmul, lIdealProj_tmul, smul_tmul]
      congr 1 <;> exact Subtype.ext (mul_assoc _ _ _)

theorem lIdealIncl_lIdealProj (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    (x : A₁ ⊗[k] A₂) : lIdealIncl (lIdealProj (k := k) he₁ he₂ x) = x * (e₁ ⊗ₜ e₂) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_mul]
  | tmul a b => rw [lIdealProj_tmul, lIdealIncl_tmul, Algebra.TensorProduct.tmul_mul_tmul]; rfl

variable (k) in
/-- **External tensor product of cyclic projectives**: `A₁ e₁ ⊠ A₂ e₂ ≅ (A₁ ⊗ A₂)(e₁ ⊗ e₂)`. -/
noncomputable def lIdealEquiv (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) :
    ExtTensor k (lIdeal e₁) (lIdeal e₂) ≃ₗ[A₁ ⊗[k] A₂] lIdeal (e₁ ⊗ₜ[k] e₂) :=
  LinearEquiv.ofLinearMap (LinearMap.codRestrict _ lIdealIncl lIdealIncl_mem)
    { toFun := fun x => lIdealProj he₁ he₂ x.1
      map_add' := fun x y => map_add _ x.1 y.1
      map_smul' := fun t x => lIdealProj_mul he₁ he₂ t x.1 }
    (LinearMap.ext fun x => Subtype.ext (by
      change lIdealIncl (lIdealProj he₁ he₂ x.1) = x.1
      rw [lIdealIncl_lIdealProj]
      exact x.2))
    (LinearMap.ext fun x => by
      change lIdealProj he₁ he₂ (lIdealIncl x) = x
      induction x using induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul y₁ y₂ => rw [lIdealIncl_tmul, lIdealProj_tmul, rMulIdem_val, rMulIdem_val]
      | add x y hx hy => rw [map_add, map_add, hx, hy])

end Categorification.ExtTensor

namespace Categorification.WeightedKLR

open KLR Juxtapose GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν₁ ν₂ : Multiset I}

omit [DecidableEq I] in
theorem castStrand_castStrand {ν μ : I →₀ ℕ} (h : ν = μ) (t : Strand μ) :
    castStrand h (castStrand h.symm t) = t := by
  subst h
  rfl

theorem isGeneric_spacedPos {ν : Multiset I} (i : Seq ν) :
    IsGeneric Γ (i.spacedPos Γ.spacing) :=
  isGeneric_spacedConfig WeightedGraph.spacing_pos WeightedGraph.abs_weight_lt_spacing
    (injective_posOf_val i)

theorem ofPoint_spacedPos {ν : Multiset I} (i : Seq ν) :
    FullChamber.ofPoint (i.spacedPos Γ.spacing) (isGeneric_spacedPos i) = spacedFull Γ i :=
  Subtype.ext (fullSigns_spacedPos i)

/-- Juxtaposing the chambers of the evenly spaced loadings `B_s(i)` and `B_s(j)` gives the
chamber of `B_s(ij)`, `ij` the concatenation. -/
theorem castChamber_chamber_spacedFull (i : Seq ν₁) (j : Seq ν₂) :
    castChamber (Seq.toFinsupp_add ν₁ ν₂) (chamber (spacedFull Γ i) (spacedFull Γ j)) =
      spacedFull Γ (i.append j) := by
  set h := Seq.toFinsupp_add ν₁ ν₂
  set P := (i.append j).spacedPos Γ.spacing
  have hP : IsGeneric Γ P := isGeneric_spacedPos _
  set q := P ∘ castStrand h
  have hq : IsGeneric Γ q := isGeneric_comp_castStrand h.symm hP
  have hl : q ∘ inlStrand _ _ = i.spacedPos Γ.spacing := by
    funext s
    simp only [q, P, Function.comp_apply, Seq.spacedPos, Seq.posOf_append_inl, Seq.inlPos,
      Fin.val_cast, Fin.val_castAdd]
  have hr : q ∘ inrStrand _ _ =
      fun s => j.spacedPos Γ.spacing s + Γ.spacing * (Multiset.card ν₁ : 𝕜) := by
    funext s
    simp only [q, P, Function.comp_apply, Seq.spacedPos, Seq.posOf_append_inr, Seq.inrPos,
      Fin.val_cast, Fin.val_natAdd]
    push_cast
    ring
  have hs' : fullSigns (Γ := Γ) (q ∘ inlStrand _ _) = (spacedFull Γ i).1 := by
    rw [hl, fullSigns_spacedPos]
  have hs'' : fullSigns (Γ := Γ) (q ∘ inrStrand _ _) = (spacedFull Γ j).1 := by
    rw [hr, fullSigns_add_const, fullSigns_spacedPos]
  have hsep : ∀ a b, q (inlStrand _ _ a) + ∑ e, |Γ.weight e| < q (inrStrand _ _ b) := by
    intro a b
    have ha := congrFun hl a
    have hb := congrFun hr b
    simp only [Function.comp_apply] at ha hb
    rw [ha, hb]
    simp only [Seq.spacedPos]
    have h1 : ((i.posOf a : ℕ) : 𝕜) + 1 ≤ (Multiset.card ν₁ : 𝕜) := by
      exact_mod_cast (i.posOf a).2
    have h2 : (0 : 𝕜) ≤ ((j.posOf b : ℕ) : 𝕜) := Nat.cast_nonneg _
    have hs := WeightedGraph.spacing_pos (Γ := Γ)
    have h3 : Γ.spacing = 1 + ∑ e, |Γ.weight e| := rfl
    nlinarith
  rw [← ofPoint_eq_chamber_of_separated q hq hs' hs'' hsep, castChamber_ofPoint,
    ← ofPoint_spacedPos]
  apply Subtype.ext
  show fullSigns (q ∘ castStrand h.symm) = fullSigns P
  congr 1
  funext t
  simp only [q, Function.comp_apply, castStrand_castStrand]


/-! ### Single strands -/

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem isEmpty_hyp_of_subsingleton {ν : I →₀ ℕ} [Subsingleton (Strand ν)] :
    IsEmpty (Hyp Γ ν) := by
  refine ⟨fun h => ?_⟩
  rcases h with w | d
  · exact w.2.2.2 (Subsingleton.elim _ _)
  · have h := d.2.2
    rw [Subsingleton.elim d.1.1 d.1.2] at h
    exact lt_irrefl _ h

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem subsingleton_fullChamber {ν : I →₀ ℕ} [Subsingleton (Strand ν)] :
    Subsingleton (FullChamber Γ ν) :=
  ⟨fun _ _ => Subtype.ext (funext fun h =>
    ((isEmpty_hyp_of_subsingleton (Γ := Γ)).false h).elim)⟩

omit [DecidableEq I] in
instance subsingleton_strand_single (c : I) :
    Subsingleton (Strand (Multiset.toFinsupp ((↑[c] : Multiset I)))) := by
  rw [← Fintype.card_le_one_iff_subsingleton, Seq.card_strand]
  simp

omit [DecidableEq I] in
instance subsingleton_strand_nil :
    Subsingleton (Strand (Multiset.toFinsupp ((↑([] : List I)) : Multiset I))) := by
  rw [← Fintype.card_le_one_iff_subsingleton, Seq.card_strand]
  simp

/-- When a dimension vector has at most one full chamber, Webster's idempotent is the idempotent
of any rank-ordered one. -/
theorem rankIdem_eq_e {ν : I →₀ ℕ} [Subsingleton (FullChamber Γ ν)] (C : FullChamber Γ ν)
    (hC : C.IsRankOrdered) : rankIdem k Γ ν = e C := by
  rw [rankIdem, Finset.sum_eq_single_of_mem C (Finset.mem_filter.2 ⟨Finset.mem_univ _, hC⟩)]
  intro D _ hD
  exact absurd (Subsingleton.elim D C) hD

/-! ### The idempotents of the evenly spaced loadings in `W` -/

theorem castGallery_e {ν μ : I →₀ ℕ} (h : ν = μ) (C : FullChamber Γ ν) :
    castGallery k Γ h (e C) = e (castChamber h C) := by
  subst h
  rfl

variable (k Γ) in
/-- The idempotent `e(B_s(i))` of the evenly spaced loading, as an element of `W_ν`. -/
noncomputable def spacedW {ν : Multiset I} (i : Seq ν) :
    WeightedKLRAlgebra k Γ (Multiset.toFinsupp ν) :=
  ⟨e (spacedFull Γ i), (Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem).2
    ⟨by rw [rankIdem_mul_e, ite_eq_left (Chamber.toFull_isRankOrdered _)],
      by rw [e_mul_rankIdem, ite_eq_left (Chamber.toFull_isRankOrdered _)]⟩⟩

theorem spacedW_val {ν : Multiset I} (i : Seq ν) : (spacedW k Γ i).1 = e (spacedFull Γ i) := rfl

/-- Juxtaposition sends `e(B_s(i)) ⊗ e(B_s(j))` to `e(B_s(ij))` in the gallery algebras. -/
theorem castGallery_galleryTensorHom_spacedFull (i : Seq ν₁) (j : Seq ν₂) :
    castGallery k Γ (Seq.toFinsupp_add ν₁ ν₂)
        (galleryTensorHom k Γ _ _ (e (spacedFull Γ i) ⊗ₜ e (spacedFull Γ j))).1 =
      e (spacedFull Γ (i.append j)) := by
  rw [galleryTensorHom_e_tmul_e, castGallery_e, castChamber_chamber_spacedFull]

/-- Webster's map `ι` sends `e(B_s(i)) ⊗ e(B_s(j))` to `e(B_s(ij))`. -/
theorem inductionMap_spacedW (i : Seq ν₁) (j : Seq ν₂) :
    castW k Γ (Seq.toFinsupp_add ν₁ ν₂)
        (inductionMap k Γ _ _ (spacedW k Γ i ⊗ₜ spacedW k Γ j)) = spacedW k Γ (i.append j) := by
  apply Subtype.ext
  rw [castW_val, inductionMap_tmul]
  exact castGallery_galleryTensorHom_spacedFull i j

/-- The unit of `W_{α_c}` (one strand of colour `c`) is `e(B_s(c))`. -/
theorem one_eq_spacedW_single (c : I) :
    (1 : WeightedKLRAlgebra k Γ (Multiset.toFinsupp ((↑[c] : Multiset I)))) =
      spacedW k Γ (Seq.ofList [c]) := by
  have := subsingleton_fullChamber (Γ := Γ) (ν := Multiset.toFinsupp ((↑[c] : Multiset I)))
  exact Subtype.ext (rankIdem_eq_e _ (Chamber.toFull_isRankOrdered _))

theorem one_eq_spacedW_nil :
    (1 : WeightedKLRAlgebra k Γ (Multiset.toFinsupp ((↑([] : List I)) : Multiset I))) =
      spacedW k Γ (Seq.ofList []) := by
  have := subsingleton_fullChamber (Γ := Γ)
    (ν := Multiset.toFinsupp ((↑([] : List I)) : Multiset I))
  exact Subtype.ext (rankIdem_eq_e _ (Chamber.toFull_isRankOrdered _))

variable (k Γ) in
/-- The iterated juxtaposition `ι(1_{α_{c₁}} ⊗ ι(1_{α_{c₂}} ⊗ ⋯))` of the units of the
one-strand algebras `W_{α_c}`, for a list `(c₁, …, cₙ)` of colours. -/
noncomputable def juxtUnits :
    (l : List I) → WeightedKLRAlgebra k Γ (Multiset.toFinsupp (l : Multiset I))
  | [] => 1
  | c :: l => castW k Γ (Seq.toFinsupp_add (↑[c]) (↑l)) (inductionMap k Γ _ _ (1 ⊗ₜ juxtUnits l))

/-- **Generation clause of Webster's Proposition 2.18** (arXiv:1209.2463v4, §2.4), on
idempotents: the iterated juxtaposition of the units of the one-strand algebras
`W_{α_{c₁}}, …, W_{α_{cₙ}}` is the idempotent `e(B_s(c₁ ⋯ cₙ))` of the evenly spaced loading. -/
theorem juxtUnits_eq_spacedW (l : List I) : juxtUnits k Γ l = spacedW k Γ (Seq.ofList l) := by
  induction l with
  | nil => exact one_eq_spacedW_nil
  | cons c l ih =>
    rw [juxtUnits, ih, one_eq_spacedW_single, inductionMap_spacedW]
    exact congrArg (spacedW k Γ) (Seq.append_ofList c l)

/-! ### Induction of the projectives `W e(B_s(i))` -/

theorem isIdempotentElem_spacedW {ν : Multiset I} (i : Seq ν) :
    IsIdempotentElem (spacedW k Γ i) :=
  Subtype.ext (by
    change e (spacedFull Γ i) * e (spacedFull Γ i) = e (spacedFull Γ i)
    simp [e_mul_e])

theorem isIdempotentElem_tmul {A₁ A₂ : Type*} [Ring A₁] [Algebra k A₁] [Ring A₂] [Algebra k A₂]
    {e₁ : A₁} {e₂ : A₂} (h₁ : IsIdempotentElem e₁) (h₂ : IsIdempotentElem e₂) :
    IsIdempotentElem (e₁ ⊗ₜ[k] e₂) := by
  rw [IsIdempotentElem, Algebra.TensorProduct.tmul_mul_tmul, h₁.eq, h₂.eq]

theorem inductionRingHom_spacedW (i : Seq ν₁) (j : Seq ν₂) :
    inductionRingHom k Γ _ _ (spacedW k Γ i ⊗ₜ spacedW k Γ j) =
      (castW k Γ (Seq.toFinsupp_add ν₁ ν₂)).symm (spacedW k Γ (i.append j)) := by
  rw [← inductionMap_spacedW, AlgEquiv.symm_apply_apply]
  rfl

variable (k Γ) in
/-- First step of `indSpacedEquiv`: the external tensor product of the two cyclic projectives
is the cyclic projective of `e(B_s(i)) ⊗ e(B_s(j))`. -/
noncomputable def indSpacedEquivAux₁ (i : Seq ν₁) (j : Seq ν₂) :
    InductionAlong.Ind
        (A := TensorProduct k (WeightedKLRAlgebra k Γ (Multiset.toFinsupp ν₁))
          (WeightedKLRAlgebra k Γ (Multiset.toFinsupp ν₂)))
        (B := WeightedKLRAlgebra k Γ (Multiset.toFinsupp ν₁ + Multiset.toFinsupp ν₂))
        (ExtTensor k (lIdeal (spacedW k Γ i)) (lIdeal (spacedW k Γ j)))
        (inductionRingHom k Γ (Multiset.toFinsupp ν₁) (Multiset.toFinsupp ν₂)) ≃ₗ[
          WeightedKLRAlgebra k Γ (Multiset.toFinsupp ν₁ + Multiset.toFinsupp ν₂)]
      InductionAlong.Ind
        (A := TensorProduct k (WeightedKLRAlgebra k Γ (Multiset.toFinsupp ν₁))
          (WeightedKLRAlgebra k Γ (Multiset.toFinsupp ν₂)))
        (B := WeightedKLRAlgebra k Γ (Multiset.toFinsupp ν₁ + Multiset.toFinsupp ν₂))
        (lIdeal (spacedW k Γ i ⊗ₜ[k] spacedW k Γ j))
        (inductionRingHom k Γ (Multiset.toFinsupp ν₁) (Multiset.toFinsupp ν₂)) :=
  InductionAlong.Ind.congr
    (ExtTensor.lIdealEquiv k (isIdempotentElem_spacedW i) (isIdempotentElem_spacedW j))

variable (k Γ) in
/-- Second step of `indSpacedEquiv`: induction of the cyclic projective of
`e(B_s(i)) ⊗ e(B_s(j))`. -/
noncomputable def indSpacedEquivAux₂ (i : Seq ν₁) (j : Seq ν₂) :
    InductionAlong.Ind
        (A := TensorProduct k (WeightedKLRAlgebra k Γ (Multiset.toFinsupp ν₁))
          (WeightedKLRAlgebra k Γ (Multiset.toFinsupp ν₂)))
        (B := WeightedKLRAlgebra k Γ (Multiset.toFinsupp ν₁ + Multiset.toFinsupp ν₂))
        (lIdeal (spacedW k Γ i ⊗ₜ[k] spacedW k Γ j))
        (inductionRingHom k Γ (Multiset.toFinsupp ν₁) (Multiset.toFinsupp ν₂)) ≃ₗ[
          WeightedKLRAlgebra k Γ (Multiset.toFinsupp ν₁ + Multiset.toFinsupp ν₂)]
      lIdeal (inductionRingHom k Γ (Multiset.toFinsupp ν₁) (Multiset.toFinsupp ν₂)
        (spacedW k Γ i ⊗ₜ[k] spacedW k Γ j)) :=
  InductionAlong.indLIdealEquiv _
    (isIdempotentElem_tmul (isIdempotentElem_spacedW i) (isIdempotentElem_spacedW j))

variable (k Γ) in
/-- **Generation clause of Webster's Proposition 2.18** (arXiv:1209.2463v4, §2.4), for one
juxtaposition: induction takes `W_{ν₁} e(B_s(i)) ⊠ W_{ν₂} e(B_s(j))` to `W_{ν₁+ν₂} e(B_s(ij))`.
Iterating with `i` a single colour (`one_eq_spacedW_single`: `W_{α_c} e(B_s(c)) = W_{α_c}`)
exhibits `W_ν e(B_s(c₁ ⋯ cₙ))` as the iterated induction of the regular modules `W_{α_{cₘ}}`.
The weight `ν₁ + ν₂` of the target is read
through `Seq.toFinsupp_add`. -/
noncomputable def indSpacedEquiv (i : Seq ν₁) (j : Seq ν₂) :
    ind k Γ (Multiset.toFinsupp ν₁) (Multiset.toFinsupp ν₂) (lIdeal (spacedW k Γ i))
        (lIdeal (spacedW k Γ j)) ≃ₗ[
          WeightedKLRAlgebra k Γ (Multiset.toFinsupp ν₁ + Multiset.toFinsupp ν₂)]
      lIdeal ((castW k Γ (Seq.toFinsupp_add ν₁ ν₂)).symm (spacedW k Γ (i.append j))) :=
  ((indSpacedEquivAux₁ k Γ i j).trans (indSpacedEquivAux₂ k Γ i j)).trans
    (LinearEquiv.ofEq _ _ (congrArg lIdeal (inductionRingHom_spacedW i j)))

end Categorification.WeightedKLR
