/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingRowStandard
import Categorification.WeightedKLR.RedStrands.BlockQuotientCoordinates
import Categorification.WeightedKLR.RedStrands.BlockStackedCounts

/-!
# Partial standardization of the local standard module is the global standard module

Webster, arXiv:1309.3796v2, §6.1, proof of Proposition 6.9 (v3: Proposition 6.10), the
reduction to two red strands. Let a row carry spectator loadings and, in its distinguished
pair `λ_a λ_b`, a loading `t₀` with no black strand left of a red strand (the uncrossed
Figure 5 loading `λ_a λ_b w`). Write `s'` for the row loading. The standard relations at `s'`
(Definition 5.1) are exactly the corner elements whose class modulo the diagrams through
higher cuts lies in the local two-red standard relations at `t₀`, stacked on the uncrossed
column (`stackedStandard_setPairLoading`). Webster states this without proof; this file
supplies one, so `StackedStandard` is no longer a hypothesis of Proposition 6.9.

* A stacked local relation is a standard relation (`mem_violStandardUpper_of_stacked`): a local
  relation passes through a pair loading with a black strand left of `λ_b`, and juxtaposing it
  with the spectators gives a loading which is not below `s'`, so every diagram through it
  factors through loadings strictly above `s'` (`e_mul_mul_e_mem_commonUpperSpan`); the higher
  cuts are standard relations (`mul_mem_stendhalUpperIdeal_of_mem_blockUpperIdeal`).
* A standard relation is a stacked local relation (`e_mul_e_mul_mem_stackedRelations`): modulo the
  higher cuts, a diagram from `s'` to a loading `v` strictly above `s'` with the same cuts is,
  by the parabolic coordinates (`exists_blockStack_quotient_coordinates_with_indexed_projectors`),
  a sum of juxtaposed block diagrams ending at nonviolated splits of `v`. Such a split has a black
  strand left of `λ_b` in the pair (`blockBlackCount_le_of_shuffleLoading`), so its pair factor
  is a local standard relation at `t₀`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Categorification.Stendhal

namespace BraidedStendhalAlgebra

open KLR

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "V" => ViolQuotient k Q Λ ν
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation:max "E" j:arg => π (KLRAlgebra.e j)

/-- A diagram from `t` through a loading `u` of the same red order which is not below `t` is a
standard relation at `t`: it factors through loadings above `t` and `u` (Webster,
arXiv:1309.3796v2, §5.1), which are strictly above `t`. -/
theorem e_mul_mul_e_mem_stendhalUpperIdeal {t u : Seq μ} (hu : redWord u = redWord t)
    (hnot : ¬ StendhalLE u t) (c : V) :
    E t * c * E u ∈ stendhalUpperIdeal k Q Λ ν t (redWord t) := by
  obtain ⟨z, rfl⟩ := (violMk_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν)).comp
    ofKLR_surjective c
  change π (KLRAlgebra.e t) * π z * π (KLRAlgebra.e u) ∈ _
  rw [← map_mul, ← map_mul]
  suffices H : ∀ y ∈ commonUpperSpan Q Λ u t,
      π y ∈ stendhalUpperIdeal k Q Λ ν t (redWord t) from
    H _ (e_mul_mul_e_mem_commonUpperSpan Q Λ u t hu.symm z)
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, a', b', huv, htv, hv, rfl⟩ := hx
    have hlt : StendhalLT t v :=
      ⟨htv, fun hvt => hnot fun r i => (huv r i).trans (hvt r i)⟩
    have hgen : E v ∈ stendhalUpperIdeal k Q Λ ν t (redWord t) :=
      TwoSidedIdeal.subset_span ⟨v, hv.trans hu, hlt, rfl⟩
    rw [map_mul, map_mul]
    exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ hgen)
  | zero => rw [map_zero]; exact TwoSidedIdeal.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact TwoSidedIdeal.add_mem _ hx hy
  | smul r x _ hx =>
    rw [map_smul, Algebra.smul_def]
    exact TwoSidedIdeal.mul_mem_left _ _ _ hx

end BraidedStendhalAlgebra

namespace RedBlock

open KLR BraidedStendhalAlgebra MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Juxtaposition

variable {k : Type*} [CommRing k] {I : Type} [DecidableEq I] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

/-- A diagram of the first block juxtaposed with a diagram of the remaining blocks. -/
private abbrev qtmul (B : RedBlock I ℓ) (Bs : List (RedBlock I ℓ)) (a : quotientAlgebra Q Λ B)
    (b : quotients Q Λ Bs) : quotients Q Λ (B :: Bs) := a ⊗ₜ b

variable {B : RedBlock I ℓ} {Bs : List (RedBlock I ℓ)}

private theorem qtmul_mul (a a' : quotientAlgebra Q Λ B) (b b' : quotients Q Λ Bs) :
    qtmul B Bs a b * qtmul B Bs a' b' = qtmul B Bs (a * a') (b * b') :=
  Algebra.TensorProduct.tmul_mul_tmul a a' b b'

private theorem sum_qtmul {ι : Type*} (s : Finset ι) (a : ι → quotientAlgebra Q Λ B)
    (b : quotients Q Λ Bs) : qtmul B Bs (∑ i ∈ s, a i) b = ∑ i ∈ s, qtmul B Bs (a i) b :=
  TensorProduct.sum_tmul s a b

private theorem zero_qtmul (b : quotients Q Λ Bs) : qtmul B Bs 0 b = 0 :=
  TensorProduct.zero_tmul _ b

private theorem add_qtmul (a a' : quotientAlgebra Q Λ B) (b : quotients Q Λ Bs) :
    qtmul B Bs (a + a') b = qtmul B Bs a b + qtmul B Bs a' b :=
  TensorProduct.add_tmul a a' b

private theorem neg_qtmul (a : quotientAlgebra Q Λ B) (b : quotients Q Λ Bs) :
    qtmul B Bs (-a) b = -qtmul B Bs a b :=
  TensorProduct.neg_tmul a b

private theorem qtmul_zero (a : quotientAlgebra Q Λ B) :
    qtmul B Bs a (0 : quotients Q Λ Bs) = 0 :=
  TensorProduct.tmul_zero _ a

private theorem qtmul_add (a : quotientAlgebra Q Λ B) (b b' : quotients Q Λ Bs) :
    qtmul B Bs a (b + b') = qtmul B Bs a b + qtmul B Bs a b' :=
  TensorProduct.tmul_add a b b'

private theorem qtmul_smul (r : k) (a : quotientAlgebra Q Λ B) (b : quotients Q Λ Bs) :
    qtmul B Bs a (r • b) = r • qtmul B Bs a b :=
  TensorProduct.tmul_smul r a b

/-- An ordered local diagram of the first block juxtaposed with ordered diagrams of the
remaining blocks. -/
private abbrev otmul (σ : (B : RedBlock I ℓ) → Equiv.Perm (Fin B.size)) (B : RedBlock I ℓ)
    (Bs : List (RedBlock I ℓ)) (a : TensorProductAlgebra k Q ((Λ ∘ B.label) ∘ σ B) B.black)
    (b : orderedProduct Q Λ σ Bs) : orderedProduct Q Λ σ (B :: Bs) := a ⊗ₜ b

private theorem otmul_mul (σ : (B : RedBlock I ℓ) → Equiv.Perm (Fin B.size))
    (a a' : TensorProductAlgebra k Q ((Λ ∘ B.label) ∘ σ B) B.black)
    (b b' : orderedProduct Q Λ σ Bs) :
    otmul σ B Bs a b * otmul σ B Bs a' b' = otmul σ B Bs (a * a') (b * b') :=
  Algebra.TensorProduct.tmul_mul_tmul a a' b b'

end Juxtaposition

section Retraction

variable {k : Type*} [CommRing k] {I : Type} [DecidableEq I] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (σ : (B : RedBlock I ℓ) → Equiv.Perm (Fin B.size))

/-- Cut every tensor factor down to its ordered diagonal algebra. -/
def rowRetraction : (Bs : List (RedBlock I ℓ)) →
    quotients Q Λ Bs →ₗ[k] orderedProduct Q Λ σ Bs
  | [] => LinearMap.id
  | B :: Bs => TensorProduct.map (orderedRetraction Q Λ hQ σ B) (rowRetraction Bs)

/-- The row retraction followed by the ordered inclusion multiplies by the ordered projectors
on both sides. -/
theorem orderedInclusion_rowRetraction : ∀ (Bs : List (RedBlock I ℓ)) (x : quotients Q Λ Bs),
    orderedInclusion Q Λ hQ σ Bs (rowRetraction Q Λ hQ σ Bs x) =
      orderedInclusion Q Λ hQ σ Bs 1 * x * orderedInclusion Q Λ hQ σ Bs 1
  | [], x => by
    change x = 1 * x * 1
    rw [one_mul, mul_one]
  | B :: Bs, x => by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, mul_add, add_mul, hx, hy]
    | tmul a b =>
      change qtmul B Bs (orderedValue Q Λ hQ σ B (orderedRetraction Q Λ hQ σ B a))
          (orderedInclusion Q Λ hQ σ Bs (rowRetraction Q Λ hQ σ Bs b)) =
        qtmul B Bs (orderedValue Q Λ hQ σ B 1) (orderedInclusion Q Λ hQ σ Bs 1) *
          qtmul B Bs a b *
          qtmul B Bs (orderedValue Q Λ hQ σ B 1) (orderedInclusion Q Λ hQ σ Bs 1)
      rw [qtmul_mul, qtmul_mul, orderedValue_retraction, orderedInclusion_rowRetraction Bs]

end Retraction

section Stacked

universe v
variable {k : Type v} [CommRing k]
variable {I : Type} [DecidableEq I] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)
local notation "botOrd" => (fun (_ : RedBlock I ℓ) => 1)
local notation "B₂" => (RedBlock.mk 2 f β : RedBlock I ℓ)
local notation "ov" => orderedValue Q Λ hQ botOrd B₂

/-- **Sandwiches by row loading idempotents are row relations.** If every local diagram from
`τp` to `τp'` is a local relation, every diagram of the row from the row idempotent of `τp` to
that of `τp'` is a row relation. -/
theorem rowTau_mul_mul_rowTau_mem_rowRelations (τp τp' : TensorProductAlgebra k Q (Λ ∘ f) β)
    (Hp : Submodule k (TensorProductAlgebra k Q (Λ ∘ f) β))
    (hHp : ∀ a, τp * a * τp' ∈ Hp) :
    ∀ (L : List (Fin ℓ × Multiset I)) (s v : Loadings (adjacentRow L M f β))
      (d : orderedProduct Q Λ botOrd (adjacentRow L M f β)),
      rowTau Q Λ hQ M f β τp L s * d * rowTau Q Λ hQ M f β τp' L v ∈
        rowRelations Q Λ hQ M f β τp Hp L s
  | [], s, v, d => by
    induction d using TensorProduct.inductionOn with
    | add x y hx hy => rw [mul_add, add_mul]; exact add_mem hx hy
    | tmul a b =>
      change otmul botOrd B₂ (M.map spectator) τp (spectatorsIdem Q Λ hQ M s.2) *
          otmul botOrd B₂ (M.map spectator) a b *
          otmul botOrd B₂ (M.map spectator) τp' (spectatorsIdem Q Λ hQ M v.2) ∈
        BlockCut.tensorRelations τp (spectatorsIdem Q Λ hQ M s.2) Hp
          (spectatorsRelations Q Λ hQ M s.2)
      rw [otmul_mul, otmul_mul]
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨_, hHp a, _,
        ⟨b * spectatorsIdem Q Λ hQ M v.2, (mul_assoc _ _ _).symm⟩, rfl⟩)
  | x :: L, s, v, d => by
    induction d using TensorProduct.inductionOn with
    | add y z hy hz => rw [mul_add, add_mul]; exact add_mem hy hz
    | tmul a b =>
      change otmul botOrd (spectator x) (adjacentRow L M f β) (spectatorIdem Q Λ hQ x s.1)
            (rowTau Q Λ hQ M f β τp L s.2) *
          otmul botOrd (spectator x) (adjacentRow L M f β) a b *
          otmul botOrd (spectator x) (adjacentRow L M f β) (spectatorIdem Q Λ hQ x v.1)
            (rowTau Q Λ hQ M f β τp' L v.2) ∈
        BlockCut.tensorRelations (spectatorIdem Q Λ hQ x s.1) (rowTau Q Λ hQ M f β τp L s.2) ⊥
          (rowRelations Q Λ hQ M f β τp Hp L s.2)
      rw [otmul_mul, otmul_mul]
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨_,
        ⟨a * spectatorIdem Q Λ hQ x v.1, (mul_assoc _ _ _).symm⟩, _,
        rowTau_mul_mul_rowTau_mem_rowRelations τp τp' Hp hHp L s.2 v.2 b, rfl⟩)

end Stacked

section Loadings

variable {I : Type} {ℓ : ℕ} (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ)
    (β : Multiset I)
local notation "B₂" => (RedBlock.mk 2 f β : RedBlock I ℓ)

/-- Inserting the pair loading of a row loading gives it back. -/
theorem setPairLoading_pairLoading :
    ∀ (L : List (Fin ℓ × Multiset I)) (s : Loadings (adjacentRow L M f β)),
      setPairLoading M f β (pairLoading M f β L s) L s = s
  | [], _ => rfl
  | _ :: L, s => Prod.ext rfl (setPairLoading_pairLoading L s.2)

/-- A violated pair loading violates the row loading. -/
theorem violated_of_isViolated_pairLoading :
    ∀ (L : List (Fin ℓ × Multiset I)) (s : Loadings (adjacentRow L M f β)),
      IsViolated (pairLoading M f β L s) → Violated _ s
  | [], _, h => .inl h
  | _ :: L, s, h => .inr (violated_of_isViolated_pairLoading L s.2 h)

/-- Changing a nonviolated pair loading of a nonviolated row loading gives a nonviolated row
loading. -/
theorem not_violated_setPairLoading (σ τ : Seq (B₂).localWeight) (hτ : ¬ IsViolated τ) :
    ∀ (L : List (Fin ℓ × Multiset I)) (s : Loadings (adjacentRow L M f β)),
      ¬ Violated _ (setPairLoading M f β σ L s) → ¬ Violated _ (setPairLoading M f β τ L s)
  | [], s, h => by
    rintro (h' | h')
    · exact hτ h'
    · exact h (.inr h')
  | _ :: L, s, h => by
    rintro (h' | h')
    · exact h (.inl h')
    · exact not_violated_setPairLoading σ τ hτ L s.2 (fun h'' => h (.inr h'')) h'

private theorem redWord_spectator (x : Fin ℓ × Multiset I) (σ : Seq (spectator x).localWeight) :
    redWord σ = List.finRange (spectator x).size :=
  List.perm_singleton.1 ((List.perm_ext_iff_of_nodup (redWord_nodup _)
    (List.nodup_finRange _)).2 fun r => by simp [mem_redWord])

/-- A row loading whose pair loading has the identity red order is uncrossed. -/
theorem uncrossedLoading_setPairLoading (σ : Seq (B₂).localWeight)
    (hσ : redWord σ = List.finRange 2) :
    ∀ (L : List (Fin ℓ × Multiset I)) (s : Loadings (adjacentRow L M f β)),
      UncrossedLoading _ (setPairLoading M f β σ L s)
  | [], s => ⟨hσ, spectators_uncrossed M s.2⟩
  | x :: L, s => ⟨redWord_spectator x s.1, uncrossedLoading_setPairLoading σ hσ L s.2⟩
where
  spectators_uncrossed : ∀ (M : List (Fin ℓ × Multiset I)) (s : Loadings (M.map spectator)),
      UncrossedLoading (M.map spectator) s
    | [], _ => trivial
    | x :: xs, s => ⟨redWord_spectator x s.1, spectators_uncrossed xs s.2⟩

end Loadings

section GoodSpan

variable {k : Type*} [CommRing k] {I : Type} [DecidableEq I] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)
    (t₀ : Seq (stendhalWeight 2 β))

/-- The span of the block diagrams through an uncrossed row loading whose pair loading lies
strictly above `t₀`. -/
def upperPairSpan (L : List (Fin ℓ × Multiset I)) :
    Submodule k (quotients Q Λ (adjacentRow L M f β)) :=
  Submodule.span k {X | ∃ (a b : quotients Q Λ (adjacentRow L M f β))
    (u : Loadings (adjacentRow L M f β)), UncrossedLoading _ u ∧
      StendhalLT t₀ (pairLoading M f β L u) ∧
      X = a * projection Q Λ _ (loadingIdem Q Λ _ u) * b}

variable {Q Λ M f β t₀}

theorem mul_mem_upperPairSpan {L : List (Fin ℓ × Multiset I)}
    {X : quotients Q Λ (adjacentRow L M f β)} (hX : X ∈ upperPairSpan Q Λ M f β t₀ L)
    (c d : quotients Q Λ (adjacentRow L M f β)) :
    c * X * d ∈ upperPairSpan Q Λ M f β t₀ L := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨a, b, u, hu, hlt, rfl⟩ := hX
    exact Submodule.subset_span ⟨c * a, b * d, u, hu, hlt, by simp only [mul_assoc]⟩
  | zero => simp only [mul_zero, zero_mul]; exact zero_mem _
  | add X Y _ _ hX hY => rw [mul_add, add_mul]; exact add_mem hX hY
  | smul r X _ hX => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ r hX

/-- Tensoring with a spectator factor on the left preserves the upper pair span. -/
theorem tmul_mem_upperPairSpan (x : Fin ℓ × Multiset I) {L : List (Fin ℓ × Multiset I)}
    (Y : quotientAlgebra Q Λ (spectator x)) {X : quotients Q Λ (adjacentRow L M f β)}
    (hX : X ∈ upperPairSpan Q Λ M f β t₀ L) :
    (Y ⊗ₜ X : quotients Q Λ (adjacentRow (x :: L) M f β)) ∈
      upperPairSpan Q Λ M f β t₀ (x :: L) := by
  show qtmul (spectator x) (adjacentRow L M f β) Y X ∈ _
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨a, b, u, hu, hlt, rfl⟩ := hX
    have h1 : (1 : quotientAlgebra Q Λ (spectator x)) = ∑ σ : Seq (spectator x).localWeight,
        violMk k Q (Λ ∘ (spectator x).label) x.2 (ofKLR k Q (Λ ∘ (spectator x).label) x.2
          (KLRAlgebra.e σ)) := by
      rw [← map_sum, ← map_sum, KLRAlgebra.sum_e, map_one, map_one]
    have hσ : ∀ σ : Seq (spectator x).localWeight,
        projection Q Λ (adjacentRow (x :: L) M f β) (loadingIdem Q Λ _ (σ, u)) =
          qtmul (spectator x) (adjacentRow L M f β)
            (violMk k Q (Λ ∘ (spectator x).label) x.2 (ofKLR k Q (Λ ∘ (spectator x).label) x.2
              (KLRAlgebra.e σ))) (projection Q Λ _ (loadingIdem Q Λ _ u)) := fun _ => rfl
    have he : qtmul (spectator x) (adjacentRow L M f β) Y
        (a * projection Q Λ _ (loadingIdem Q Λ _ u) * b) =
        ∑ σ : Seq (spectator x).localWeight, qtmul (spectator x) (adjacentRow L M f β) Y a *
          qtmul (spectator x) (adjacentRow L M f β)
            (violMk k Q (Λ ∘ (spectator x).label) x.2 (ofKLR k Q (Λ ∘ (spectator x).label) x.2
              (KLRAlgebra.e σ))) (projection Q Λ _ (loadingIdem Q Λ _ u)) *
            qtmul (spectator x) (adjacentRow L M f β) 1 b := by
      have hterm : ∀ σ : Seq (spectator x).localWeight,
          qtmul (spectator x) (adjacentRow L M f β) Y a *
            qtmul (spectator x) (adjacentRow L M f β)
              (violMk k Q (Λ ∘ (spectator x).label) x.2
                (ofKLR k Q (Λ ∘ (spectator x).label) x.2 (KLRAlgebra.e σ)))
                (projection Q Λ _ (loadingIdem Q Λ _ u)) *
              qtmul (spectator x) (adjacentRow L M f β) 1 b =
          qtmul (spectator x) (adjacentRow L M f β)
            (Y * violMk k Q (Λ ∘ (spectator x).label) x.2
              (ofKLR k Q (Λ ∘ (spectator x).label) x.2 (KLRAlgebra.e σ)))
              (a * projection Q Λ _ (loadingIdem Q Λ _ u) * b) := fun σ => by
        rw [qtmul_mul, qtmul_mul, mul_one]
      rw [Finset.sum_congr rfl fun σ _ => hterm σ, ← sum_qtmul, ← Finset.mul_sum, ← h1,
        mul_one]
    rw [he]
    exact Submodule.sum_mem _ fun σ _ => Submodule.subset_span
      ⟨_, _, (σ, u), ⟨redWord_spectator x σ, hu⟩, hlt, by rw [hσ]⟩
  | zero => rw [qtmul_zero]; exact zero_mem _
  | add X Z _ _ hX hZ => rw [qtmul_add]; exact add_mem hX hZ
  | smul r X _ hX => rw [qtmul_smul]; exact Submodule.smul_mem _ r hX

/-- A local standard relation at `t₀` tensored with the spectators of `M` lies in the upper pair
span. -/
theorem tmul_mem_upperPairSpan_nil {Y : quotientAlgebra Q Λ (RedBlock.mk 2 f β)}
    (hY : Y ∈ stendhalUpperIdeal k Q (Λ ∘ f) β t₀ [0, 1])
    (Z : quotients Q Λ (M.map spectator)) :
    (Y ⊗ₜ Z : quotients Q Λ (adjacentRow [] M f β)) ∈
      upperPairSpan Q Λ M f β t₀ [] := by
  show qtmul (RedBlock.mk 2 f β) (M.map spectator) Y Z ∈ _
  induction hY using TwoSidedIdeal.span_induction generalizing Z with
  | mem Y hY =>
    obtain ⟨w, hw, hlt, rfl⟩ := hY
    have hw' : redWord w = List.finRange 2 := hw.trans (by decide)
    have hspan : ∀ Z' ∈ Submodule.span k (Set.range (loadingIdem Q Λ (M.map spectator))),
        qtmul (RedBlock.mk 2 f β) (M.map spectator)
          (violMk k Q (Λ ∘ f) β (ofKLR k Q (Λ ∘ f) β (KLRAlgebra.e w)))
          (projection Q Λ (M.map spectator) Z') ∈ upperPairSpan Q Λ M f β t₀ [] := by
      intro Z' hZ'
      induction hZ' using Submodule.span_induction with
      | mem Z' hZ' =>
        obtain ⟨σ, rfl⟩ := hZ'
        refine Submodule.subset_span ⟨1, 1, (w, σ),
          ⟨hw', uncrossedLoading_setPairLoading.spectators_uncrossed M σ⟩, hlt, ?_⟩
        rw [one_mul, mul_one]
        rfl
      | zero => rw [map_zero, qtmul_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [map_add, qtmul_add]; exact add_mem ha hb
      | smul r a _ ha => rw [map_smul, qtmul_smul]; exact Submodule.smul_mem _ r ha
    have hone := hspan 1 (unit_mem_loadingSpan Q Λ (M.map spectator))
    rw [map_one] at hone
    have := mul_mem_upperPairSpan hone 1 (qtmul (RedBlock.mk 2 f β) (M.map spectator) 1 Z)
    rwa [one_mul, qtmul_mul, mul_one, one_mul] at this
  | zero => rw [zero_qtmul]; exact zero_mem _
  | add Y Y' _ _ hY hY' => rw [add_qtmul]; exact add_mem (hY Z) (hY' Z)
  | neg Y _ hY => rw [neg_qtmul]; exact neg_mem (hY Z)
  | left_absorb c Y _ hY =>
    have := mul_mem_upperPairSpan (hY Z) (qtmul (RedBlock.mk 2 f β) (M.map spectator) c 1) 1
    rwa [mul_one, qtmul_mul, one_mul] at this
  | right_absorb c Y _ hY =>
    have := mul_mem_upperPairSpan (hY Z) 1 (qtmul (RedBlock.mk 2 f β) (M.map spectator) c 1)
    rwa [one_mul, qtmul_mul, mul_one] at this

end GoodSpan

section RowRelations

variable {k : Type*} [CommRing k] {I : Type} [DecidableEq I] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
local notation "botOrd" => (fun (_ : RedBlock I ℓ) => 1)

/-- The spectators carry no relations. -/
theorem spectatorsRelations_eq_bot : ∀ (N : List (Fin ℓ × Multiset I))
    (s : Loadings (N.map spectator)), spectatorsRelations Q Λ hQ N s = ⊥
  | [], _ => rfl
  | x :: xs, s => by
    rw [spectatorsRelations, spectatorsRelations_eq_bot xs, eq_bot_iff, BlockCut.tensorRelations]
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨a, ha, b, -, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_bot] at ha
      simp only [ha, TensorProduct.zero_tmul, SetLike.mem_coe, zero_mem]
    · rintro _ ⟨a, -, b, hb, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_bot] at hb
      simp only [hb, TensorProduct.tmul_zero, SetLike.mem_coe, zero_mem]

variable (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)

/-- **Row relations are spanned by diagrams through higher pair loadings.** The ordered
inclusion of a row relation built from the local standard relations at `t₀` lies in the span of
the diagrams through uncrossed row loadings whose pair loading is strictly above `t₀`. -/
theorem rowRelations_le_comap (τp : TensorProductAlgebra k Q (Λ ∘ f) β)
    (t₀ : Seq (stendhalWeight 2 β)) :
    ∀ (L : List (Fin ℓ × Multiset I)) (s : Loadings (adjacentRow L M f β)),
      rowRelations Q Λ hQ M f β τp (pairRelations Q Λ hQ f β t₀) L s ≤
        (upperPairSpan Q Λ M f β t₀ L).comap
          (LinearMap.ofClass (orderedInclusion Q Λ hQ botOrd (adjacentRow L M f β)))
  | [], s => by
    rw [rowRelations, BlockCut.tensorRelations]
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨Y, hY, Z, -, rfl⟩
      exact tmul_mem_upperPairSpan_nil ((mem_pairRelations Q Λ hQ f β).1 hY)
        (orderedInclusion Q Λ hQ botOrd (M.map spectator) Z)
    · rintro _ ⟨Y, -, Z, hZ, rfl⟩
      rw [spectatorsRelations_eq_bot, SetLike.mem_coe, Submodule.mem_bot] at hZ
      simp only [hZ, TensorProduct.tmul_zero, SetLike.mem_coe, zero_mem]
  | x :: L, s => by
    rw [rowRelations, BlockCut.tensorRelations]
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨Y, hY, Z, -, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_bot] at hY
      simp only [hY, TensorProduct.zero_tmul, SetLike.mem_coe, zero_mem]
    · rintro _ ⟨Y, -, Z, hZ, rfl⟩
      exact tmul_mem_upperPairSpan x (orderedValue Q Λ hQ botOrd (spectator x) Y)
        (rowRelations_le_comap τp t₀ L s.2 hZ)

end RowRelations

section Main

universe w
variable {k : Type w} [CommRing k]
variable {I : Type} [DecidableEq I] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
local notation "Bs" => adjacentRow L M f β
local notation "botOrd" => (fun (_ : RedBlock I ℓ) => 1)
local notation "B₂" => (RedBlock.mk 2 f β : RedBlock I ℓ)
local notation "D₀" => orderedProduct Q Λ botOrd Bs
local notation "ι₀" => orderedInclusion Q Λ hQ botOrd Bs
local notation "S₀" => orderedColumn Q Λ hQ botOrd L M f β h
local notation "act" => blockProductAction Q Λ L M f β h
local notation "Col" => blockColumn Q Λ L M f β h
local notation "V" => ViolQuotient k Q Λ ν
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "κ₀" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "α" => fun r i => boundaryCount (cut (f 0) (f 1) r) i Bs
local notation "J" => blockUpperIdeal k Q Λ ν (f 0) (f 1) α κ₀
local notation "q" => RingCon.mkₐ k (TwoSidedIdeal.ringCon J)
local notation "p" => violMk k Q Λ ν (redProj k Q Λ ν κ₀)
local notation "F" => stackBlocks Q Λ L M f β h
local notation "G" => affineStackBlocks Q Λ L M f β h
local notation "P" => projection Q Λ Bs
local notation "pl" s => Seq.cast h (place Bs s)
local notation "ov" => orderedValue Q Λ hQ botOrd B₂
local notation "mk" => violMk k Q Λ ν
local notation "raw" => ofKLR k Q Λ ν

private abbrev columnGroup' (σ : (B : RedBlock I ℓ) → Equiv.Perm (Fin B.size)) :
    AddCommGroup (orderedColumn Q Λ hQ σ L M f β h) := Submodule.addCommGroup _
attribute [local instance] columnGroup'

omit [DecidableEq I] in
private theorem blockBlackCount_cast {w w' : Multiset (I ⊕ Fin ℓ)} [DecidableEq I]
    (e : w = w') (z : Seq w) (C : Finset (Fin ℓ)) (i : I) :
    blockBlackCount (Seq.cast e z) C i = blockBlackCount z C i := by subst w'; rfl

variable {Q Λ hQ L M f β h}

private theorem q_eq_zero (z : V) : q z = 0 ↔ z ∈ J := by
  change (J).ringCon.mk' z = 0 ↔ _
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

omit [DecidableEq I] in
private theorem nodup_of_redWord {s : Seq (stendhalWeight ℓ ν)} (hs : redWord s = κ₀) :
    (κ₀).Nodup := hs ▸ redWord_nodup s

omit [DecidableEq I] in
private theorem ne_of_mem_left (hn : (κ₀).Nodup) (j : Fin 2) :
    ∀ x ∈ L, x.1 ≠ f j := by
  intro x hx he
  have hd := (List.nodup_append.1 hn).2.2 _ (List.mem_map_of_mem hx) (f j)
    (by fin_cases j <;> simp)
  exact hd he

/-- The black strands left of `λ_{f 1}` at a placed row loading. -/
private theorem blackCount_place_one (hn : (κ₀).Nodup) (u : Loadings Bs) (i : I) :
    blackCount (pl u) (f 1) i =
      boundaryCount {f 1} i Bs + blackCount (pairLoading M f β L u) 1 i := by
  rw [← blockBlackCount_singleton, blockBlackCount_cast,
    blockBlackCount_place_pair M f β 1 i L u (ne_of_mem_left hn 1)]

/-- The retained root of a nonviolated uncrossed placed loading is the boundary count of the
row. -/
theorem adjacentBlockRoot_place_of_uncrossed {s : Loadings Bs} (hs : ¬ Violated Bs s)
    (ht : redWord (pl s) = κ₀) : adjacentBlockRoot (f 0) (f 1) (pl s) = α := by
  funext r i
  change blockBlackCount (pl s) (cut (f 0) (f 1) r) i = _
  rw [blockBlackCount_cast]
  exact count_place_of_not_violated r i s (aligned_adjacent L M f β (nodup_of_redWord ht)) hs

/-- **Juxtaposed local relations are standard relations.** Let `s'` be a nonviolated
uncrossed row loading whose pair loading has no black strand left of a red strand, and `u` an
uncrossed row loading whose pair loading lies strictly above it. Every diagram from `s'`
through `u` is a standard relation at `s'`. -/
theorem e_mul_mul_place_mem_stendhalUpperIdeal {s' u : Loadings Bs} (hs : ¬ Violated Bs s')
    (ht : redWord (pl s') = κ₀)
    (h0 : ∀ r i, blackCount (pairLoading M f β L s') r i = 0) (hu : UncrossedLoading Bs u)
    (hlt : StendhalLT (pairLoading M f β L s') (pairLoading M f β L u)) (c : V) :
    π (KLRAlgebra.e (pl s')) * c * π (KLRAlgebra.e (pl u)) ∈
      stendhalUpperIdeal k Q Λ ν (pl s') (redWord (pl s')) := by
  have hut : redWord (pl u) = κ₀ := (uncrossedLoading_iff L M f β h u).1 hu
  have hn := nodup_of_redWord ht
  by_cases hv : Violated Bs u
  · have hlt' := root_lt_of_violated h (aligned_adjacent L M f β hn) u hv
    rw [← adjacentBlockRoot_place_of_uncrossed hs ht] at hlt'
    exact mul_mem_stendhalUpperIdeal_of_mem_blockUpperIdeal (L := L.map Prod.fst)
      (M := M.map Prod.fst) ht
      (TwoSidedIdeal.subset_span ⟨pl u, hut.trans ht.symm, hlt', rfl⟩) c
  · have hvp : ¬ IsViolated (pairLoading M f β L u) :=
      fun h' => hv (violated_of_isViolated_pairLoading M f β L u h')
    obtain ⟨i, hi⟩ := exists_blackCount_one_pos h0
      ((redWord_pairLoading M f β L u hu).trans (show List.finRange 2 = [0, 1] by decide)) hvp hlt
    refine e_mul_mul_e_mem_stendhalUpperIdeal (hut.trans ht.symm) (fun hle => ?_) c
    have := hle (f 1) i
    rw [blackCount_place_one hn, blackCount_place_one hn, h0] at this
    omega

private theorem cast_cast_symm' {X : Type*} {w w' : Multiset X} (e : w = w') (v : Seq w') :
    Seq.cast e (Seq.cast e.symm v) = v := by subst e; rfl

private theorem mem_violStandardUpper_iff' {t : Seq (stendhalWeight ℓ ν)} {κ : List (Fin ℓ)}
    (hκ : redWord t = κ) (x : violCorner k Q Λ ν t κ) :
    x ∈ violStandardUpper t κ ↔ x.1 ∈ stendhalUpperIdeal k Q Λ ν t κ := by
  subst hκ; exact mem_violStandardUpper_iff x

/-- A diagram from a nonviolated uncrossed row loading through the higher cuts is a standard
relation. -/
private theorem e_mul_mem_of_mem_J {s' : Loadings Bs} (hs : ¬ Violated Bs s')
    (ht : redWord (pl s') = κ₀) {y : V} (hy : y ∈ J) (c : V) :
    π (KLRAlgebra.e (pl s')) * c * y ∈ stendhalUpperIdeal k Q Λ ν (pl s') κ₀ := by
  have hroot := adjacentBlockRoot_place_of_uncrossed hs ht
  have := mul_mem_stendhalUpperIdeal_of_mem_blockUpperIdeal (L := L.map Prod.fst)
    (M := M.map Prod.fst) ht (y := y) (by rw [hroot, ht]; exact hy) c
  rwa [ht] at this

variable (Q Λ L M f β) in
/-- Classes modulo the higher cuts with a representative which is a standard relation at `t`
after multiplying by `e(t)`. -/
private def goodQuot (t : Seq (stendhalWeight ℓ ν)) : Submodule k (J).ringCon.Quotient :=
  (((stendhalUpperIdeal k Q Λ ν t κ₀).asIdeal.restrictScalars k).comap
    (LinearMap.mulLeft k (π (KLRAlgebra.e t)))).map (q).toLinearMap

private theorem q_mem_goodQuot {t : Seq (stendhalWeight ℓ ν)} {y : V}
    (hy : π (KLRAlgebra.e t) * y ∈ stendhalUpperIdeal k Q Λ ν t κ₀) :
    q y ∈ goodQuot Q Λ L M f β t := by
  refine Submodule.mem_map_of_mem ?_
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem, TwoSidedIdeal.mem_asIdeal]
  exact hy

private theorem mem_of_q_mem_goodQuot {s' : Loadings Bs} (hs : ¬ Violated Bs s')
    (ht : redWord (pl s') = κ₀) {y : V} (hy : q y ∈ goodQuot Q Λ L M f β (pl s')) :
    π (KLRAlgebra.e (pl s')) * y ∈ stendhalUpperIdeal k Q Λ ν (pl s') κ₀ := by
  obtain ⟨y', hy', he⟩ := hy
  rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.restrictScalars_mem,
    TwoSidedIdeal.mem_asIdeal] at hy'
  change π (KLRAlgebra.e (pl s')) * y' ∈ _ at hy'
  have hJ : y - y' ∈ J := by
    rw [← q_eq_zero, map_sub]
    exact sub_eq_zero.2 he.symm
  have h1 := e_mul_mem_of_mem_J hs ht hJ 1
  rw [mul_one, mul_sub] at h1
  have h2 := TwoSidedIdeal.add_mem _ h1 hy'
  rwa [sub_add_cancel] at h2

/-- The action of the upper pair span on the block column lands in the good classes. -/
private theorem act_mem_goodQuot {s' : Loadings Bs} (hs : ¬ Violated Bs s')
    (ht : redWord (pl s') = κ₀) (h0 : ∀ r i, blackCount (pairLoading M f β L s') r i = 0)
    {X : quotients Q Λ Bs} (hX : X ∈ upperPairSpan Q Λ M f β (pairLoading M f β L s') L)
    (z : Col) : (act X z).1 ∈ goodQuot Q Λ L M f β (pl s') := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨a, b, u, hu, hlt, rfl⟩ := hX
    obtain ⟨a', rfl⟩ := projection_surjective Q Λ Bs a
    obtain ⟨b', rfl⟩ := projection_surjective Q Λ Bs b
    obtain ⟨z₀, hz₀⟩ := RingCon.mkₐ_surjective («α» := k) (TwoSidedIdeal.ringCon J) z.1
    have e1 : (act (P a' * P (loadingIdem Q Λ Bs u) * P b') z).1 =
        q (F a' * π (KLRAlgebra.e (pl u)) * (F b' * z₀)) := by
      rw [← map_mul, ← map_mul, blockProductAction_projection, ← hz₀, map_mul F, map_mul F,
        stackBlocks_loadingIdem, ← map_mul q]
      simp only [mul_assoc]
    rw [e1]
    refine q_mem_goodQuot ?_
    have h1 := e_mul_mul_place_mem_stendhalUpperIdeal hs ht h0 hu hlt (F a')
    rw [ht] at h1
    have h2 := TwoSidedIdeal.mul_mem_right _ _ (F b' * z₀) h1
    simpa only [mul_assoc] using h2
  | zero =>
    rw [map_zero (blockProductAction Q Λ L M f β h), LinearMap.zero_apply, Submodule.coe_zero]
    exact zero_mem _
  | add X Y _ _ hX hY =>
    rw [map_add (blockProductAction Q Λ L M f β h), LinearMap.add_apply, Submodule.coe_add]
    exact add_mem hX hY
  | smul r X _ hX =>
    rw [map_smul (blockProductAction Q Λ L M f β h), LinearMap.smul_apply, Submodule.coe_smul]
    exact Submodule.smul_mem _ r hX

/-- **Stacked local relations are standard relations.** -/
theorem mem_violStandardUpper_of_stacked {s' : Loadings Bs} (hs : ¬ Violated Bs s')
    (ht : redWord (pl s') = κ₀) (h0 : ∀ r i, blackCount (pairLoading M f β L s') r i = 0)
    {H : Submodule k D₀}
    (hH : ∀ a ∈ H, ι₀ a ∈ upperPairSpan Q Λ M f β (pairLoading M f β L s') L)
    (x : violCorner k Q Λ ν (pl s') κ₀)
    (hx : q x.1 ∈ stackedRelations Q Λ hQ L M f β h H) :
    x ∈ violStandardUpper (pl s') κ₀ := by
  have hle : stackedRelations Q Λ hQ L M f β h H ≤ goodQuot Q Λ L M f β (pl s') := by
    rw [stackedRelations, Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, z, rfl⟩
    exact act_mem_goodQuot hs ht h0 (hH a ha) z.1
  rw [mem_violStandardUpper_iff' ht]
  have := mem_of_q_mem_goodQuot hs ht (hle hx)
  have hc : π (KLRAlgebra.e (pl s')) * x.1 = x.1 := (mem_violCorner_iff.1 x.2).1
  rwa [hc] at this

/-- A juxtaposed diagram of `H` acting on the block column is a stacked relation. -/
private theorem act_mem_stackedRelations {H : Submodule k D₀} {a : D₀} (ha : a ∈ H)
    (z : Col) :
    (act (ι₀ a) z).1 ∈ stackedRelations Q Λ hQ L M f β h H := by
  refine ⟨a • (⟨act (ι₀ 1) z, z, rfl⟩ : S₀),
    Submodule.subset_span ⟨a, ha, _, rfl⟩, ?_⟩
  change (act (ι₀ a) (act (ι₀ 1) z)).1 = _
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_one]


local notation "spl" => setPairLoading M f β
local notation "τe" t => tensorOfKLR Q (Λ ∘ f) β (KLRAlgebra.e t)
local notation "rowRel" t:max L':max s:max =>
  rowRelations Q Λ hQ M f β (tensorOfKLR Q (Λ ∘ f) β (KLRAlgebra.e t))
    (pairRelations Q Λ hQ f β t) L' s

/-- **Standard relations are stacked local relations**, for a generator of the standard
relations: a diagram from `s'` through a loading `v` strictly above `s'`. -/
private theorem e_mul_e_mul_mem_stackedRelations (s : Loadings Bs)
    (t₀ : Seq (B₂).localWeight) (ht₀ : redWord t₀ = List.finRange 2)
    (h0 : ∀ r i, blackCount t₀ r i = 0) (hs : ¬ Violated Bs (spl t₀ L s))
    {v : Seq (stendhalWeight ℓ ν)} (hvκ : redWord v = κ₀)
    (hlt : StendhalLT (pl (spl t₀ L s)) v)
    (c d : V) :
    q (π (KLRAlgebra.e (pl (spl t₀ L s))) * c * π (KLRAlgebra.e v) * d * p) ∈
      stackedRelations Q Λ hQ L M f β h (rowRel t₀ L s) := by
  have ht : redWord (pl (spl t₀ L s)) = κ₀ :=
    (uncrossedLoading_iff L M f β h _).1 (uncrossedLoading_setPairLoading M f β t₀ ht₀ L s)
  have hn := nodup_of_redWord ht
  have hroot₀ := adjacentBlockRoot_place_of_uncrossed hs ht
  by_cases hroot : α < adjacentBlockRoot (f 0) (f 1) v
  · have hJ : π (KLRAlgebra.e v) ∈ J := TwoSidedIdeal.subset_span ⟨v, hvκ, hroot, rfl⟩
    have hJ' : π (KLRAlgebra.e (pl (spl t₀ L s))) * c * π (KLRAlgebra.e v) * d * p ∈ J :=
      TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_right _ _ _
        (TwoSidedIdeal.mul_mem_left _ _ _ hJ))
    rw [(q_eq_zero _).2 hJ']
    exact zero_mem _
  have hrootEq :
      adjacentBlockRoot (f 0) (f 1) v = adjacentBlockRoot (f 0) (f 1) (pl (spl t₀ L s)) := by
    have hle := adjacentBlockRoot_mono (L' := L.map Prod.fst) (M' := M.map Prod.fst) ht hvκ hlt.1
    rw [hroot₀] at hle ⊢
    by_contra hne
    exact hroot (lt_of_le_of_ne hle (Ne.symm hne))
  obtain ⟨i, hi⟩ := exists_blackCount_lt_of_adjacentBlockRoot_eq ht hvκ hlt hrootEq
  obtain ⟨c', rfl⟩ := ((violMk_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν)).comp
    ofKLR_surjective) c
  obtain ⟨d', rfl⟩ := ((violMk_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν)).comp
    ofKLR_surjective) d
  obtain ⟨n, index, g, w, G', bottom, hG, -, -, hmul, hbottom, hloading, -, -, -, rebuild⟩ :=
    exists_blockStack_quotient_coordinates_with_indexed_projectors Q Λ L M f β hQ h
  have hload : ∀ u : Loadings Bs, G (loadingIdem Q Λ Bs u) = KLRAlgebra.e (pl u) := fun u => by
    change KLRAlgebra.castKLR _ h _ = _
    rw [juxtapose_loadingIdem, KLRAlgebra.castKLR_e]
  obtain ⟨y₀, hy₀⟩ :
      ∃ y₀, y₀ = KLRAlgebra.e (pl (spl t₀ L s)) * c' * KLRAlgebra.e v := ⟨_, rfl⟩
  have hleft : G (loadingIdem Q Λ Bs (spl t₀ L s)) * y₀ = y₀ := by
    rw [hload, hy₀, ← mul_assoc, ← mul_assoc, KLRAlgebra.e_mul_e,
      ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  have hS1 : G 1 * y₀ = y₀ := by
    rw [← hleft, ← mul_assoc, ← map_mul, one_mul]
  have hright : y₀ * KLRAlgebra.e v = y₀ := by
    rw [hy₀, mul_assoc _ (KLRAlgebra.e v), KLRAlgebra.e_mul_e,
      ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  have hx : π (KLRAlgebra.e (pl (spl t₀ L s))) * π c' * π (KLRAlgebra.e v) * π d' * p =
      mk (raw (G 1 * y₀)) * (π d' * p) := by
    rw [hS1, hy₀]
    simp only [map_mul, mul_assoc, AlgHom.comp_apply]
  change q (π (KLRAlgebra.e (pl (spl t₀ L s))) * π c' * π (KLRAlgebra.e v) *
    π d' * p) ∈ _
  rw [hx, map_mul, rebuild, Finset.sum_mul]
  refine Submodule.sum_mem _ fun j _ => ?_
  -- the column element carrying the rest of the diagram
  let zc : Col := ⟨q (F 1 * (mk (raw (w j)) * π d' * p)), mk (raw (w j)) * π d', rfl⟩
  have hT : q (mk (raw (G (g j y₀) * w j))) * q (π d' * p) =
      (act (G' j (q (mk (raw y₀)))) zc).1 := by
    rw [hG, blockProductAction_projection]
    change _ = q (F (g j y₀)) * q (F 1 * (mk (raw (w j)) * π d' * p))
    rw [← map_mul q, ← map_mul q, ← mul_assoc (F (g j y₀)), ← map_mul F, mul_one]
    simp only [map_mul, mul_assoc, AlgHom.comp_apply]
    rfl
  rw [hT]
  set X := G' j (q (mk (raw y₀))) with hXdef
  have hX1 : P (loadingIdem Q Λ Bs (spl t₀ L s)) * X = X := by
    rw [hXdef, ← hmul, hleft]
  have hX2 : X * P (bottom j v) = X := by
    rw [hXdef, ← hbottom, hright]
  rcases (hloading j v).loading with hb | ⟨vj, hsh, hb⟩
  · rw [hb, map_zero (projection Q Λ Bs), mul_zero] at hX2
    rw [← hX2, map_zero (blockProductAction Q Λ L M f β h), LinearMap.zero_apply,
      Submodule.coe_zero]
    exact zero_mem _
  rw [hb] at hX2
  by_cases hvj : Violated Bs vj
  · rw [projection_loadingIdem_eq_zero Q Λ Bs vj hvj, mul_zero] at hX2
    rw [← hX2, map_zero (blockProductAction Q Λ L M f β h), LinearMap.zero_apply,
      Submodule.coe_zero]
    exact zero_mem _
  -- the combinatorics of the shuffle
  have ho : redWord (Seq.cast h (Seq.cast h.symm v)) = κ₀ := by
    rw [cast_cast_symm']; exact hvκ
  have hred := redWord_place_eq_of_shuffleLoading L M f β h _ vj hsh ho
  have hvjU : UncrossedLoading Bs vj := (uncrossedLoading_iff L M f β h vj).2 (hred.symm.trans ho)
  have hσ : redWord (pairLoading M f β L vj) = List.finRange 2 :=
    redWord_pairLoading M f β L vj hvjU
  have hcount := blockBlackCount_le_of_shuffleLoading h _ vj hsh hred hvj {f 1} i
  rw [cast_cast_symm', blockBlackCount_singleton, ← blockBlackCount_cast h (place Bs vj) {f 1} i,
    blockBlackCount_singleton, blackCount_place_one hn vj i] at hcount
  have hs1 := blackCount_place_one (h := h) hn (spl t₀ L s) i
  rw [pairLoading_setPairLoading M f β t₀ L s, h0] at hs1
  have hpos : 0 < blackCount (pairLoading M f β L vj) 1 i := by omega
  have hlt₀ : StendhalLT t₀ (pairLoading M f β L vj) := stendhalLT_of_blackCount_pos h0 hpos
  -- the local relation
  let τσ := tensorOfKLR Q (Λ ∘ f) β (KLRAlgebra.e (pairLoading M f β L vj))
  have hHp : ∀ a, (τe t₀) * a * τσ ∈ pairRelations Q Λ hQ f β t₀ := fun a => by
    rw [mem_pairRelations, map_mul, map_mul, orderedValue_identity_e Q Λ hQ B₂ t₀ ht₀,
      orderedValue_identity_e Q Λ hQ B₂ _ hσ]
    exact TwoSidedIdeal.mul_mem_left _ _ _
      (TwoSidedIdeal.subset_span
        ⟨_, hσ.trans (show List.finRange 2 = [0, 1] by decide), hlt₀, rfl⟩)
  have hmem := rowTau_mul_mul_rowTau_mem_rowRelations Q Λ hQ M f β (τe t₀) τσ _ hHp L s vj
    (rowRetraction Q Λ hQ botOrd Bs X)
  have hA : ι₀ (rowTau Q Λ hQ M f β (τe t₀) L s) * ι₀ 1 =
      ι₀ (rowTau Q Λ hQ M f β (τe t₀) L s) := by
    rw [← map_mul, mul_one]
  have hB : ι₀ 1 * ι₀ (rowTau Q Λ hQ M f β τσ L vj) =
      ι₀ (rowTau Q Λ hQ M f β τσ L vj) := by
    rw [← map_mul, one_mul]
  have hι : ι₀ (rowTau Q Λ hQ M f β (τe t₀) L s * rowRetraction Q Λ hQ botOrd Bs X *
      rowTau Q Λ hQ M f β τσ L vj) = X := by
    rw [map_mul, map_mul, orderedInclusion_rowRetraction]
    calc _ = (ι₀ (rowTau Q Λ hQ M f β (τe t₀) L s) * ι₀ 1) * X *
          (ι₀ 1 * ι₀ (rowTau Q Λ hQ M f β τσ L vj)) := by simp only [mul_assoc]
      _ = X := by
        rw [hA, hB, orderedInclusion_rowTau Q Λ hQ M f β t₀ ht₀ L s,
          orderedInclusion_rowTau Q Λ hQ M f β _ hσ L vj, setPairLoading_pairLoading, hX1, hX2]
  rw [← hι]
  exact act_mem_stackedRelations hmem zc

/-- **Partial standardization of the local standard module is the global standard module**
(Webster, arXiv:1309.3796v2, §6.1, proof of Proposition 6.9; v3: Proposition 6.10). Let `t₀` be
a two-red loading of identity red order with no black strand left of a red strand, and let `s'`
be a nonviolated row loading with pair loading `t₀`. A corner element at `s'` is a standard
relation exactly when its class modulo the higher cuts is a stacked local standard relation. -/
theorem stackedStandard_setPairLoading (s : Loadings Bs) (t₀ : Seq (B₂).localWeight)
    (ht₀ : redWord t₀ = List.finRange 2)
    (h0 : ∀ r i, blackCount t₀ r i = 0) (hs : ¬ Violated Bs (spl t₀ L s)) :
    StackedStandard hQ h (rowRel t₀ L s) (spl t₀ L s) := by
  have ht : redWord (pl (spl t₀ L s)) = κ₀ :=
    (uncrossedLoading_iff L M f β h _).1 (uncrossedLoading_setPairLoading M f β t₀ ht₀ L s)
  have h0' : ∀ r i, blackCount (pairLoading M f β L (spl t₀ L s)) r i = 0 := by
    rw [pairLoading_setPairLoading]; exact h0
  intro x
  constructor
  · intro hx
    have hx' := (mem_violStandardUpper_iff' ht x).1 hx
    suffices H : ∀ y ∈ stendhalUpperIdeal k Q Λ ν (pl (spl t₀ L s)) κ₀, ∀ c d : V,
        q (π (KLRAlgebra.e (pl (spl t₀ L s))) * c * y * d * p) ∈
          stackedRelations Q Λ hQ L M f β h (rowRel t₀ L s) by
      have := H _ hx' 1 1
      have hc : π (KLRAlgebra.e (pl (spl t₀ L s))) * x.1 = x.1 := (mem_violCorner_iff.1 x.2).1
      have hc' : x.1 * p = x.1 := (mem_violCorner_iff.1 x.2).2
      rwa [mul_one, mul_one, hc, hc'] at this
    intro y hy
    induction hy using TwoSidedIdeal.span_induction with
    | mem z hz =>
      obtain ⟨v, hvκ, hlt, rfl⟩ := hz
      exact e_mul_e_mul_mem_stackedRelations s t₀ ht₀ h0 hs hvκ hlt
    | zero =>
      intro c d
      simp only [mul_zero, zero_mul, map_zero]
      exact zero_mem _
    | add a b _ _ ha hb =>
      intro c d
      rw [mul_add, add_mul, add_mul, map_add]
      exact add_mem (ha c d) (hb c d)
    | neg a _ ha =>
      intro c d
      rw [mul_neg, neg_mul, neg_mul, map_neg]
      exact neg_mem (ha c d)
    | left_absorb a b _ hb =>
      intro c d
      simpa only [mul_assoc] using hb (c * a) d
    | right_absorb a b _ hb =>
      intro c d
      simpa only [mul_assoc] using hb c (a * d)
  · intro hx
    refine mem_violStandardUpper_of_stacked hs ht h0' (fun a ha => ?_) x hx
    have := rowRelations_le_comap Q Λ hQ M f β (τe t₀) t₀ L s ha
    rwa [pairLoading_setPairLoading]


end Main

end RedBlock

end Categorification.Stendhal
