/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicRestrictionProjective
import Categorification.KLR.IndLastStrandQuot

/-!
# Cyclotomic KLR algebras are projective over the base ring

For a commutative ring `k`, parameters `Q` with `KLRSymm Q` and unit constant leading
coefficients, and monic cyclotomic polynomials `a_i`, the cyclotomic quotient `R^Λ(ν)` is a
projective `k`-module (`CycKLR.projective_base`).

This is the input for the flatness half of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v2, **Corollary 3.26**: applied over the polynomial
ring `Ř^λ_λ` of universal cyclotomic coefficients, it says that `Ř^λ` is a projective, hence
flat, `Ř^λ_λ`-module.

The proof is the induction of Kang–Kashiwara, arXiv:1102.4677v4, §4: `R^Λ(ν)` is the sum of
the right ideals `R^Λ(ν) e(s)` over the sequences `s` of `ν`; if `s` ends with the colour `i`
and `ν = {i} + β` with `β ≠ 0`, then `R^Λ(ν) e(s)` is a direct summand of the corner
`R^Λ(ν) e(β, i)`, which is a projective right `R^Λ(β)`-module (Kang–Kashiwara, Theorem 4.5,
`projective_indCorner`), and `R^Λ(β)` is `k`-projective by induction. The cases `ν = 0` and
`ν = {i}` are `R^Λ(0) ≅ k` and `R^Λ({i}) ≅ k[x]/(a_i)`.
-/

noncomputable section

namespace Categorification.KLR

open KLRAlgebra KLRAlgebra.AbsentColour MulOpposite

/-- Projectivity is transitive along a scalar tower `k → A → P`. -/
theorem Module.projective_of_tower {k A P : Type*} [CommRing k] [Ring A] [Algebra k A]
    [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
    [Module.Projective k A] [hP : Module.Projective A P] : Module.Projective k P := by
  classical
  obtain ⟨s, hs⟩ := hP.out
  have : Module.Projective k (P →₀ A) :=
    Module.Projective.of_equiv (finsuppLequivDFinsupp k).symm
  exact Module.Projective.of_split (s.restrictScalars k)
    ((Finsupp.linearCombination A id).restrictScalars k) (LinearMap.ext hs)

namespace CycKLR

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (a : I → Polynomial k)

/-- The right ideal `R^Λ(ν) e(s)` of a sequence `s`. -/
def seqPiece {ν : Multiset I} (s : Seq ν) : Submodule k (CycKLR k Q a ν) :=
  LinearMap.range (LinearMap.mulRight k (CycKLR.mk k Q a ν (e s)))

theorem mk_e_mul_self {ν : Multiset I} (s : Seq ν) :
    CycKLR.mk k Q a ν (e s) * CycKLR.mk k Q a ν (e s) = CycKLR.mk k Q a ν (e s) := by
  rw [← map_mul, e_mul_self]

/-- `R^Λ(ν)` is projective over `k` once every right ideal `R^Λ(ν) e(s)` is. -/
theorem projective_of_seqPiece {ν : Multiset I}
    (h : ∀ s : Seq ν, Module.Projective k (seqPiece (Q := Q) a s)) :
    Module.Projective k (CycKLR k Q a ν) := by
  have : Module.Projective k (∀ s : Seq ν, seqPiece (Q := Q) a s) :=
    Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := k))
  let i : CycKLR k Q a ν →ₗ[k] ∀ s : Seq ν, seqPiece (Q := Q) a s :=
    LinearMap.pi fun s => (LinearMap.mulRight k (CycKLR.mk k Q a ν (e s))).rangeRestrict
  let p : (∀ s : Seq ν, seqPiece (Q := Q) a s) →ₗ[k] CycKLR k Q a ν :=
    ∑ s : Seq ν, (seqPiece (Q := Q) a s).subtype.comp (LinearMap.proj s)
  refine Module.Projective.of_split i p (LinearMap.ext fun r => ?_)
  rw [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.sum_apply]
  change ∑ s : Seq ν, r * CycKLR.mk k Q a ν (e s) = r
  rw [← Finset.mul_sum, ← map_sum, sum_e, map_one, mul_one]

variable (hsym : KLRSymm Q)
  (hQ : ∀ s t : I, s ≠ t → ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)

/-- The sequence `s i` of `{i} + β`. -/
abbrev lastSeq (i : I) {β : Multiset I} (s : Seq β) : Seq (({i} : Multiset I) + β) :=
  Seq.cast (add_comm β ({i} : Multiset I)) (s.append (default : Seq ({i} : Multiset I)))

theorem lastSeq_mul_lastIdem (i : I) {β : Multiset I} (s : Seq β) :
    CycKLR.mk k Q a (({i} : Multiset I) + β) (e (lastSeq i s)) * lastIdem Q i a β =
      CycKLR.mk k Q a (({i} : Multiset I) + β) (e (lastSeq i s)) := by
  have hs : cyclotomicLast Q i a β (CycKLR.mk k Q a β (e s)) =
      CycKLR.mk k Q a (({i} : Multiset I) + β) (e (lastSeq i s)) := by
    rw [cyclotomicLast_mk, cL_e]
  rw [lastIdem, ← hs, ← map_mul, mul_one]

include hsym hQ in
/-- The right ideal `R^Λ({i} + β) e(s i)` is a projective `k`-module when `R^Λ(β)` is, for
`β ≠ 0`. -/
theorem projective_seqPiece_lastSeq (i : I) {β : Multiset I} (ha : (a i).Monic)
    (hβ : 0 < Multiset.card β) [Module.Projective k (CycKLR k Q a β)] (s : Seq β) :
    Module.Projective k (seqPiece (Q := Q) a (lastSeq i s)) := by
  have : Module.Projective k (CycKLR k Q a β)ᵐᵒᵖ :=
    Module.Projective.of_equiv (MulOpposite.opLinearEquiv k)
  have : Module.Projective (CycKLR k Q a β)ᵐᵒᵖ (IndCorner Q i a β) :=
    projective_indCorner a β i hsym hQ ha hβ
  have : Module.Projective k (IndCorner Q i a β) :=
    Module.projective_of_tower (A := (CycKLR k Q a β)ᵐᵒᵖ)
  set E := CycKLR.mk k Q a (({i} : Multiset I) + β) (e (lastSeq i s))
  let incl : seqPiece (Q := Q) a (lastSeq i s) →ₗ[k] IndCorner Q i a β :=
    { toFun := fun y => ⟨y.1, by
        obtain ⟨r, hr⟩ := y.2
        change y.1 * lastIdem Q i a β = y.1
        rw [← hr]
        change r * E * lastIdem Q i a β = r * E
        rw [mul_assoc, lastSeq_mul_lastIdem]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let proj : IndCorner Q i a β →ₗ[k] seqPiece (Q := Q) a (lastSeq i s) :=
    { toFun := fun z => ⟨z.1 * E, z.1, rfl⟩
      map_add' := fun z w => Subtype.ext (add_mul _ _ _)
      map_smul' := fun c z => Subtype.ext (smul_mul_assoc _ _ _) }
  refine Module.Projective.of_split incl proj (LinearMap.ext fun y => Subtype.ext ?_)
  obtain ⟨r, hr⟩ := y.2
  change y.1 * E = y.1
  rw [← hr]
  change r * E * E = r * E
  rw [mul_assoc, mk_e_mul_self]

include hsym hQ in
/-- `projective_seqPiece_lastSeq` along a transport of weights. -/
theorem projective_seqPiece_cast_lastSeq (i : I) {β μ : Multiset I} (ha : (a i).Monic)
    (hβ : 0 < Multiset.card β) [Module.Projective k (CycKLR k Q a β)] (h : {i} + β = μ)
    (s : Seq β) : Module.Projective k (seqPiece (Q := Q) a (Seq.cast h (lastSeq i s))) := by
  subst h
  exact projective_seqPiece_lastSeq a hsym hQ i ha hβ s

omit [DecidableEq I] in
private theorem map_univ_eq_add {X Y : Multiset I} (f : Fin (Multiset.card (X + Y)) → I) :
    Finset.univ.val.map f =
      Finset.univ.val.map (f ∘ Seq.posL Y) + Finset.univ.val.map (f ∘ Seq.posR X) := by
  conv_lhs => rw [← Multiset.map_univ_val_equiv (TypeA.blockEquiv (Seq.card_add' X Y))]
  rw [Multiset.map_map, ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.disjSum,
    Multiset.map_add, Multiset.map_map, Multiset.map_map]
  rfl

omit [DecidableEq I] in
private theorem cast_cast {μ μ' μ'' : Multiset I} (h₁ : μ = μ') (h₂ : μ' = μ'') (x : Seq μ) :
    Seq.cast h₂ (Seq.cast h₁ x) = Seq.cast (h₁.trans h₂) x := by
  subst h₁ h₂; rfl

/-- Every sequence of a nonempty weight `ν` ends with some colour `j`: it is the transport of
`s j` for a sequence `s` of `ν - {j}`. -/
theorem exists_eq_cast_lastSeq {ν : Multiset I} (t : Seq ν) (hν : 0 < Multiset.card ν) :
    ∃ (j : I) (β : Multiset I) (h : {j} + β = ν) (s : Seq β), t = Seq.cast h (lastSeq j s) := by
  let j := t.1 ⟨Multiset.card ν - 1, by omega⟩
  have hj : j ∈ ν := by
    rw [← t.2]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
  have h : {j} + ν.erase j = ν := by rw [Multiset.singleton_add, Multiset.cons_erase hj]
  have h' : ν = ν.erase j + {j} := by rw [add_comm]; exact h.symm
  let u : Seq (ν.erase j + {j}) := Seq.cast h' t
  have hlast : Finset.univ.val.map (u.1 ∘ Seq.posR (ν.erase j)) = {j} := by
    have : (Finset.univ : Finset (Fin (Multiset.card ({j} : Multiset I)))).val =
        {⟨0, by simp⟩} := by
      have : (Finset.univ : Finset (Fin (Multiset.card ({j} : Multiset I)))) =
          {⟨0, by simp⟩} :=
        Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_univ _, fun y _ =>
          Fin.ext (by have := y.isLt; simp only [Multiset.card_singleton] at this; simp; omega)⟩
      rw [this]; rfl
    rw [this, Multiset.map_singleton]
    congr 1
    simp only [Function.comp_apply, u, Seq.cast_apply, j]
    refine congrArg t.1 (Fin.ext ?_)
    simp only [Fin.val_cast, Seq.posR_val]
    rw [Multiset.card_erase_of_mem hj, Nat.pred_eq_sub_one]; omega
  have hX : Finset.univ.val.map (u.1 ∘ Seq.posL {j}) = ν.erase j := by
    have := map_univ_eq_add u.1
    rw [u.2, hlast] at this
    exact (add_right_cancel this).symm
  obtain ⟨s, b, hsb, -⟩ := Seq.exists_append_eq_of_map u hX
  refine ⟨j, ν.erase j, h, s, ?_⟩
  rw [lastSeq, Subsingleton.elim (default : Seq ({j} : Multiset I)) b, hsb, cast_cast,
    cast_cast]
  rfl

include hsym hQ in
/-- **`R^Λ(ν)` is a projective `k`-module** (Kang–Kashiwara, arXiv:1102.4677v4, §4; the input
for B. Webster, arXiv:1309.3796v2, Corollary 3.26): for `k` commutative, `Q` with `KLRSymm Q`
and unit constant leading coefficients, and every `a_i` monic. -/
theorem projective_base (ha : ∀ i, (a i).Monic) (ν : Multiset I) :
    Module.Projective k (CycKLR k Q a ν) := by
  suffices H : ∀ n (ν : Multiset I), Multiset.card ν = n → Module.Projective k (CycKLR k Q a ν)
    from H _ ν rfl
  intro n
  induction n with
  | zero =>
    intro ν hν
    rw [Multiset.card_eq_zero.1 hν]
    exact Module.Projective.of_equiv (cyclotomicZeroEquiv Q a).symm.toLinearEquiv
  | succ n ih =>
    intro ν hν
    rcases n with _ | n
    · obtain ⟨i, rfl⟩ := Multiset.card_eq_one.1 hν
      exact Module.Projective.of_equiv (cyclotomicSingleFinEquiv Q i a (ha i))
    refine projective_of_seqPiece a fun t => ?_
    obtain ⟨j, β, h, s, rfl⟩ := exists_eq_cast_lastSeq t (by omega)
    have hβ : Multiset.card β = n + 1 := by
      have := congrArg Multiset.card h
      rw [Multiset.card_add, Multiset.card_singleton] at this
      omega
    have := ih β hβ
    exact projective_seqPiece_cast_lastSeq a hsym hQ j (ha j) (by omega) h s

end CycKLR

end Categorification.KLR
