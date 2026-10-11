import Categorification.KLR.MackeyInj

/-!
# Distinct-colour affine Mackey corner

Specialize KL I Proposition 2.18 to the unique single-crossing stratum.
The noncrossing piece vanishes by distinct colours, and the one-crossing piece
is the full rectangular corner. This is the affine step used before the ideal
calculation in Kang–Kashiwara, arXiv:1102.4677v4, Theorem 5.1.

The four-block source is reduced to the actual lower-rank tensor in
`CyclotomicMixedInversionTensor`. No cyclotomic descent is asserted here.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.MixedAffine
open TypeA MvPolynomial
open scoped TensorProduct
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}
variable (γ : Multiset I) (i j : I)

omit [DecidableEq I] in
/-- The rectangular weight square. -/
theorem weightSquare : (γ + {i}) + {j} = (γ + {j}) + {i} := by
  ac_rfl

/-- The unique crossing matrix for distinct last colours. -/
def crossingQuad : MackeyQuad (γ + {j}) {i} (γ + {i}) {j} where
  α := γ
  β := {j}
  γ := {i}
  δ := 0
  h₁ := rfl
  h₂ := add_zero _
  h₃ := rfl
  h₄ := add_zero _

variable {γ i j}
omit [DecidableEq I] in
theorem quad_unique (hij : i ≠ j)
    (q : MackeyQuad (γ + {j}) {i} (γ + {i}) {j}) : q = crossingQuad γ i j := by
  have hδi : q.δ ≤ ({i} : Multiset I) := (Multiset.le_add_left _ _).trans_eq q.h₂
  have hδj : q.δ ≤ ({j} : Multiset I) := (Multiset.le_add_left _ _).trans_eq q.h₄
  have hδ : q.δ = 0 := by
    rcases Multiset.le_singleton.1 hδi with h | h
    · exact h
    · rw [h] at hδj
      have : i = j := by simpa using hδj
      exact (hij this).elim
  apply MackeyQuad.ext_of_β
  simpa only [hδ, add_zero, crossingQuad] using q.h₄

variable (γ i j)
/-- The noncrossing filtration piece is genuinely zero, not a zero-object assumption. -/
theorem zero_stratum (hij : i ≠ j) :
    mackeyBimodFilt (k := k) Q (weightSquare γ i j) 0 = ⊥ := by
  have htop := mackeyImage_eq_top (Q := Q) (weightSquare γ i j) 0
  have him : mackeyImage Q (weightSquare γ i j) 0 = ⊥ := by
    apply eq_bot_iff.2
    refine iSup₂_le fun q hq => ?_
    rw [quad_unique hij q] at hq
    simp [crossingQuad] at hq
  rw [him] at htop
  apply eq_bot_iff.2
  intro r hr
  have hz : subquotOf (weightSquare γ i j) r hr = 0 := by
    have : subquotOf (weightSquare γ i j) r hr ∈
        (⊥ : Submodule k (MackeySubquot Q (weightSquare γ i j) 0)) := by
      rw [htop]; trivial
    exact this
  have := (subquotOf_eq_zero_iff (weightSquare γ i j) hr).1 hz
  simpa only [mackeyLowerBimod_zero, Submodule.mem_bot] using this

/-- Every rectangular diagram has at most one strand from the last bottom block. -/
theorem one_stratum :
    mackeyBimodFilt (k := k) Q (weightSquare γ i j) 1 =
      bimod Q (weightSquare γ i j) := by
  refine le_antisymm inf_le_left fun r hr => ⟨hr, ?_⟩
  have htop : mackeyFilt k Q ((γ + {j}) + {i})
      (Multiset.card (γ + {j})) (Multiset.card (γ + {i})) 1 = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    refine Submodule.span_mono ?_ (mem_span_gen (Q := Q) a)
    rintro _ ⟨α, p, s, hα, rfl⟩
    refine ⟨α, p, s, hα, fun v _ => ?_, rfl⟩
    have := crossCount_le_right (Multiset.card (γ + {j}))
      (show Multiset.card (γ + {i}) ≤ Multiset.card ((γ + {j}) + {i}) by simp) v
    simp only [Multiset.card_add, Multiset.card_singleton] at this ⊢
    omega
  rw [htop]; trivial

/-- The quotient projection from the full, ungraded corner. -/
def cornerClass : bimod (k := k) Q (weightSquare γ i j) →ₗ[k]
    MackeySubquot Q (weightSquare γ i j) 1 where
  toFun z := subquotOf (weightSquare γ i j) z ((one_stratum (Q := Q) γ i j).symm ▸ z.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cornerClass_bijective (hij : i ≠ j) :
    Function.Bijective (cornerClass (Q := Q) γ i j) := by
  constructor
  · intro x y h
    have hm := (subquotOf_eq_iff (weightSquare γ i j) _ _).1 h
    rw [mackeyLowerBimod_succ, zero_stratum γ i j hij, Submodule.mem_bot,
      sub_eq_zero] at hm
    exact Subtype.ext hm
  · intro z
    obtain ⟨r, hr, rfl⟩ := subquotOf_surjective (weightSquare γ i j) z
    exact ⟨⟨r, one_stratum (Q := Q) γ i j ▸ hr⟩, rfl⟩

/-- Removing the zero noncrossing piece identifies the subquotient with the full corner. -/
def cornerClassEquiv (hij : i ≠ j) :
    bimod (k := k) Q (weightSquare γ i j) ≃ₗ[k]
      MackeySubquot Q (weightSquare γ i j) 1 :=
  LinearEquiv.ofBijective (cornerClass γ i j) (cornerClass_bijective γ i j hij)

theorem crossingMap_surjective (hij : i ≠ j) : Function.Surjective
    (mackeyMap (Q := Q) (weightSquare γ i j) (crossingQuad γ i j)
      (show Multiset.card (crossingQuad γ i j).β = 1 by simp [crossingQuad])) := by
  apply LinearMap.range_eq_top.1
  apply top_unique
  rw [← mackeyImage_eq_top (Q := Q) (weightSquare γ i j) 1]
  refine iSup₂_le fun q hq => ?_
  have he := quad_unique hij q
  subst q
  exact le_rfl

omit [DecidableEq I] in
theorem crossingPerm : quadPerm (weightSquare γ i j) (crossingQuad γ i j) =
    sadj (Multiset.card ((γ + {j}) + {i})) (Multiset.card γ) := by
  ext p
  rw [quadPerm_val, sadj_val_of_lt (by simp)]
  simp only [crossingQuad, Multiset.card_add, Multiset.card_singleton, swapNat]
  have hp := p.2
  simp only [Multiset.card_add, Multiset.card_singleton] at hp
  split_ifs <;> omega

omit [DecidableEq I] in
theorem crossingWord : canWord (Multiset.card ((γ + {j}) + {i}))
    (quadPerm (weightSquare γ i j) (crossingQuad γ i j)) = [Multiset.card γ] := by
  rw [crossingPerm]
  have hl := length_canWord (Multiset.card ((γ + {j}) + {i}))
    (sadj (Multiset.card ((γ + {j}) + {i})) (Multiset.card γ))
  rw [length_sadj (by simp)] at hl
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hl
  have hw := wordProd_canWord (Multiset.card ((γ + {j}) + {i}))
    (sadj (Multiset.card ((γ + {j}) + {i})) (Multiset.card γ))
  rw [ha, wordProd_cons, wordProd_nil, mul_one] at hw
  have hv := validWord_canWord (Multiset.card ((γ + {j}) + {i}))
    (sadj (Multiset.card ((γ + {j}) + {i})) (Multiset.card γ))
  rw [ha] at hv
  have hab : a + 1 < Multiset.card ((γ + {j}) + {i}) := hv a (by simp)
  have he := congrArg (fun w => (w ⟨a, by omega⟩).val) hw
  rw [sadj_apply_left hab, sadj_val_of_lt (by simp)] at he
  simp only [swapNat] at he
  have heq : a = Multiset.card γ := by split_ifs at he <;> omega
  simpa only [heq] using ha

/-- Last-colour projector even when the removed colour does not occur. -/
def lastColourProjector (β : Multiset I) (added target : I) : KLRAlgebra k Q (β + {added}) :=
  eSum Q (Finset.univ.filter fun s : Seq (β + {added}) =>
    s.1 ⟨Multiset.card β, by simp⟩ = target)

/-- The absent-colour block is zero in the actual affine algebra. -/
theorem lastColourProjector_of_absent (β : Multiset I) (added target : I)
    (habs : target ∉ β) (hne : target ≠ added) :
    (lastColourProjector β added target : KLRAlgebra k Q (β + {added})) = 0 := by
  have hf : (Finset.univ.filter fun s : Seq (β + {added}) =>
      s.1 ⟨Multiset.card β, by simp⟩ = target) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro s _ hs
    have hm := Seq.mem s ⟨Multiset.card β, by simp⟩
    rw [hs] at hm
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hm
    exact hm.elim habs hne
  simp only [lastColourProjector, eSum, hf, Finset.sum_empty]

/-- In particular the whole off-diagonal corner vanishes when removal is impossible. -/
theorem absent_corner (β : Multiset I) (added target : I)
    (habs : target ∉ β) (hne : target ≠ added) (r : KLRAlgebra k Q (β + {added})) :
    lastColourProjector β added target * r * oneConcat Q β {added} = 0 := by
  rw [lastColourProjector_of_absent β added target habs hne, zero_mul, zero_mul]

/-- The degree-zero weight boundary uses the same actual colour idempotent. -/
theorem zero_weight_corner (added target : I) (hne : target ≠ added)
    (r : KLRAlgebra k Q (0 + {added})) :
    lastColourProjector 0 added target * r * oneConcat Q 0 {added} = 0 :=
  absent_corner 0 added target (by simp) hne r

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

/-- Actual rectangular affine crossing equivalence into the full corner.
The source here is the balanced four-block Mackey tensor. -/
def crossingEquiv (hij : i ≠ j) : MackeyX Q (crossingQuad γ i j) ≃ₗ[k]
    bimod Q (weightSquare γ i j) :=
  (LinearEquiv.ofBijective
    (mackeyMap (weightSquare γ i j) (crossingQuad γ i j) (by simp [crossingQuad]))
    ⟨mackeyMap_injective (weightSquare γ i j) hPQ hP _ _,
      crossingMap_surjective γ i j hij⟩).trans (cornerClassEquiv γ i j hij).symm

theorem cornerClass_crossingEquiv (hij : i ≠ j) (z : MackeyX Q (crossingQuad γ i j)) :
    cornerClass γ i j (crossingEquiv γ i j hPQ hP hij z) =
      mackeyMap (weightSquare γ i j) (crossingQuad γ i j)
        (by simp [crossingQuad]) z :=
  (cornerClassEquiv γ i j hij).apply_symm_apply _

/-- The forward map is the single actual crossing, in the ambient algebra. -/
theorem crossingEquiv_tmul (hij : i ≠ j)
    (t : MackeyTop Q (crossingQuad γ i j)) (b : MackeyBot Q (crossingQuad γ i j)) :
    (crossingEquiv γ i j hPQ hP hij (BalancedTensor.tmul t b) :
      KLRAlgebra k Q ((γ + {j}) + {i})) =
      concat Q (γ + {j}) {i} t * ψ (Multiset.card γ) *
        botConcat Q (weightSquare γ i j) b := by
  have hc := cornerClass_crossingEquiv γ i j hPQ hP hij (BalancedTensor.tmul t b)
  rw [mackeyMap_tmul] at hc
  have he := (subquotOf_eq_iff (weightSquare γ i j) _ _).1 hc
  rw [mackeyLowerBimod_succ, zero_stratum γ i j hij, Submodule.mem_bot,
    sub_eq_zero] at he
  simpa only [crossingWord, ψw_cons, ψw_nil, mul_one] using he

/-- Left coefficient linearity on the full rectangular corner. -/
theorem crossingEquiv_left (hij : i ≠ j) (a : TensorKLR Q (γ + {j}) {i})
    (z : MackeyX Q (crossingQuad γ i j)) :
    (crossingEquiv γ i j hPQ hP hij (a • z) : KLRAlgebra k Q ((γ + {j}) + {i})) =
      concat Q (γ + {j}) {i} a * crossingEquiv γ i j hPQ hP hij z := by
  have hc := cornerClass_crossingEquiv γ i j hPQ hP hij (a • z)
  rw [mackeyMap_left, ← cornerClass_crossingEquiv γ i j hPQ hP hij z] at hc
  change subquotOf _ _ _ = subquotLeft _ _ a (subquotOf _ _ _) at hc
  rw [subquotLeft_of] at hc
  have he := (subquotOf_eq_iff (weightSquare γ i j) _ _).1 hc
  simpa only [mackeyLowerBimod_succ, zero_stratum γ i j hij, Submodule.mem_bot,
    sub_eq_zero] using he

/-- Right coefficient linearity on the full rectangular corner. -/
theorem crossingEquiv_right (hij : i ≠ j) (a : TensorKLR Q (γ + {i}) {j})
    (z : MackeyX Q (crossingQuad γ i j)) :
    (crossingEquiv γ i j hPQ hP hij (MackeyX.rightAct (q := crossingQuad γ i j) a z) :
      KLRAlgebra k Q ((γ + {j}) + {i})) =
      crossingEquiv γ i j hPQ hP hij z * botConcat Q (weightSquare γ i j) a := by
  have hc := cornerClass_crossingEquiv γ i j hPQ hP hij
    (MackeyX.rightAct (q := crossingQuad γ i j) a z)
  rw [mackeyMap_right, ← cornerClass_crossingEquiv γ i j hPQ hP hij z] at hc
  change subquotOf _ _ _ = subquotRight _ _ a (subquotOf _ _ _) at hc
  rw [subquotRight_of] at hc
  have he := (subquotOf_eq_iff (weightSquare γ i j) _ _).1 hc
  simpa only [mackeyLowerBimod_succ, zero_stratum γ i j hij, Submodule.mem_bot,
    sub_eq_zero] using he

end Categorification.KLR.KLRAlgebra.MixedAffine
