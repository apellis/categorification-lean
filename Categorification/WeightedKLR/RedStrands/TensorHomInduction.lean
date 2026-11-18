/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorHomGeneration
import Categorification.WeightedKLR.RedStrands.TensorWordInduction
import Categorification.WeightedKLR.RedStrands.TensorHomBoundary
import Categorification.WeightedKLR.RedStrands.TensorRestrictionAdjoint
import Categorification.WeightedKLR.RedStrands.VacuumRestrictionClass

/-!
# The boundary induction for the corrected tensor Hom form

Webster, arXiv:1309.3796v2, §4.7, Lemmas 4.36–4.37.
Removing a terminal strand from either boundary reduces the Hom comparison.
A terminal black strand uses restriction and its adjoint, and two terminal
red strands use the earlier tensor factors.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra Categorification.Graded TypeA
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section LastBoundary

variable {I : Type} {ℓ : ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν

private theorem cardinal_weight : Multiset.card μ = ν.card + ℓ := by
  simp [stendhalWeight]

private def terminalPos (h : 0 < ℓ + ν.card) : Fin (Multiset.card μ) :=
  ⟨Multiset.card μ - 1, by rw [cardinal_weight]; omega⟩

private theorem exists_append_singleton {J : Type*} {δ : Multiset J} (c : J)
    (s : KLR.Seq (δ + ({c} : Multiset J)))
    (h : ∀ j : Fin (Multiset.card ({c} : Multiset J)), s.lbl (KLR.Seq.posR δ j) = c) :
    ∃ u : KLR.Seq δ, u.append (default : KLR.Seq ({c} : Multiset J)) = s := by
  let lbl := s.lbl ∘ KLR.Seq.posL ({c} : Multiset J)
  have hright : Finset.univ.val.map (s.lbl ∘ KLR.Seq.posR δ) = ({c} : Multiset J) := by
    rw [show s.lbl ∘ KLR.Seq.posR δ = fun _ => c from funext h]
    simp
  have hsplit : Finset.univ.val.map s.lbl =
      Finset.univ.val.map lbl + Finset.univ.val.map (s.lbl ∘ KLR.Seq.posR δ) := by
    conv_lhs => rw [← Multiset.map_univ_val_equiv (blockEquiv (KLR.Seq.card_add' δ ({c} : Multiset J)))]
    rw [Multiset.map_map, ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.disjSum,
      Multiset.map_add, Multiset.map_map, Multiset.map_map]
    rfl
  rw [show Finset.univ.val.map s.lbl = _ from s.2, hright] at hsplit
  refine ⟨⟨lbl, (add_right_cancel hsplit).symm⟩, ?_⟩
  apply Subtype.ext
  funext a
  obtain ⟨a, rfl⟩ := (blockEquiv (KLR.Seq.card_add' δ ({c} : Multiset J))).surjective a
  cases a with
  | inl a => exact KLR.Seq.append_posL _ _ a
  | inr a =>
    exact (KLR.Seq.append_posR _ _ a).trans ((Multiset.mem_singleton.mp ((default :
      KLR.Seq ({c} : Multiset J)).mem a)).trans (h a).symm)

private theorem exists_appendBlack_terminal {i : I} {β : Multiset I}
    (s : KLR.Seq (stendhalWeight ℓ (({i} : Multiset I) + β)))
    (h : s.lbl (terminalPos (ν := ({i} : Multiset I) + β) (ℓ := ℓ)
      (by simp)) = .inl i) (hs : IsRedOrdered s) :
    ∃ u : KLR.Seq (stendhalWeight ℓ β), IsRedOrdered u ∧ appendBlackLoading i β u = s := by
  let δ := stendhalWeight ℓ β
  let σ : Multiset (I ⊕ Fin ℓ) := {.inl i}
  let w : δ + σ = stendhalWeight ℓ (({i} : Multiset I) + β) :=
    (add_comm δ σ).trans (stendhalWeight_black_cons i β)
  let t := KLR.Seq.cast w.symm s
  have ht (j : Fin (Multiset.card σ)) : t.lbl (KLR.Seq.posR δ j) = Sum.inl i := by
    change s.lbl (Fin.cast _ (KLR.Seq.posR δ j)) = _
    have hj : j.val = 0 := by have := j.isLt; simp [σ] at this; omega
    rw [show Fin.cast (congrArg Multiset.card w) (KLR.Seq.posR δ j) =
      terminalPos (ν := ({i} : Multiset I) + β) (ℓ := ℓ) (by simp) from Fin.ext (by
        change δ.card + j.val = (stendhalWeight ℓ (({i} : Multiset I) + β)).card - 1
        rw [hj, cardinal_weight, cardinal_weight]; simp)]
    exact h
  obtain ⟨u, hu⟩ := exists_append_singleton (Sum.inl i : I ⊕ Fin ℓ) t ht
  have he : appendBlackLoading i β u = s := by
    change KLR.Seq.cast w (u.append (default : KLR.Seq σ)) = s
    rw [hu]
    apply Subtype.ext
    funext a
    change (KLR.Seq.cast w (KLR.Seq.cast w.symm s)).1 a = s.1 a
    rw [KLR.Seq.cast_apply, KLR.Seq.cast_apply, Fin.cast_cast, Fin.cast_eq_self]
  exact ⟨u, (appendBlackLoading_ordered_iff i β u).mp (he ▸ hs), he⟩

private theorem terminal_red_last {n : ℕ} (s : KLR.Seq (stendhalWeight (n + 1) ν)) (hs : IsRedOrdered s)
    (r : Fin (n + 1)) (hr : s.lbl (lastRedPosition n ν) = .inr r) :
    HasLastRed s := by
  have hm : (Sum.inr (Fin.last n) : I ⊕ Fin (n + 1)) ∈ stendhalWeight (n + 1) ν :=
    Multiset.mem_add.mpr (Or.inr (Multiset.mem_map.mpr ⟨Fin.last n, Finset.mem_univ_val _, rfl⟩))
  rw [← s.2] at hm
  obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hm
  have he : j = lastRedPosition n ν := by
    by_contra hn
    have hj' : j < lastRedPosition n ν := by
      have hm : j.val < ν.card + (n + 1) := Nat.lt_of_lt_of_eq j.isLt cardinal_weight
      have hn' : j.val ≠ ν.card + n := fun h => hn (Fin.ext h)
      change j.val < ν.card + n
      omega
    exact (not_lt_of_ge (Fin.le_last r)) (hs j _ (Fin.last n) r hj' hj hr)
  change s.lbl (lastRedPosition n ν) = _
  rw [← he]
  exact hj

end LastBoundary

open KLGamma QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped RatFunc

local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local instance : NeZero (RatFunc.X : L) := ⟨RatFunc.X_ne_zero⟩

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular)

private abbrev inductionGrading {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) :=
  stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)


omit [DecidableEq I] [Finite I] in
private theorem zero_boundary_eq (s t : KLR.Seq (stendhalWeight 0 (0 : Multiset I))) : s = t := by
  apply Subtype.ext
  funext j
  have := j.isLt
  simp [stendhalWeight] at this

private theorem agrees_empty_boundary
    (Λ : Fin 0 → I →₀ ℕ) (wt : Fin 0 → Dom R)
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    (s t : KLR.Seq (stendhalWeight 0 (0 : Multiset I))) (hs : IsRedOrdered s) (ht : IsRedOrdered t) :
    tensorHomAgrees C hQ hR Λ wt hwt 0 (K0.of (sequenceProj (inductionGrading C hQ Λ) s hs))
      (K0.of (sequenceProj (inductionGrading C hQ Λ) t ht)) := by
  let G := inductionGrading C hQ Λ
  let K := tensorProjectiveGroup C hQ Λ
  let 𝒜 := tensorProductGrade G (0 : Multiset I)
  let reg := GProj.regular 𝒜
  let u : TensorWord I 0 := .empty
  have regular_class (s : KLR.Seq (stendhalWeight 0 (0 : Multiset I))) (hs : IsRedOrdered s) :
      K0.of (sequenceProj G s hs) = K0.of reg := by
    have he : TensorProductAlgebra.mk Q Λ (0 : Multiset I) (StendhalAlgebra.e s hs) = 1 := by
      have h := zero_boundary_eq s (vacuumSeq (I := I) (ℓ := 0))
      subst s
      exact vacuumSeq_mk_e Q Λ
    exact (K0.of_ofIdempotent_congr (𝒜 := 𝒜) he (isIdempotentElem_mk_e s hs) _
      (mk_e_mem_tensorProductGrade G 0 s hs) _).trans (K0.of_eq_of_iso GProj.ofIdempotentOneIso)
  have hword : K0.of (tensorWordProjective Λ C hQ u) = K0.of reg := by
    have hf := tensorWordProjective_factorial Λ C hQ u
    change _ = (KL2.divQFact2 C ([] : List (I × ℕ))) • K0.of (tensorWordProjective Λ C hQ u) at hf
    simp only [KL2.divQFact2, List.map_nil, List.prod_nil, one_smul] at hf
    exact hf.symm.trans (regular_class u.loading u.blocks_redOrdered)
  have hvec := congrArg Subtype.val (tensorModuleEquiv_word C hQ hR Λ wt hwt u)
  change (tensorModuleEquiv C hQ hR Λ wt hwt
    (DirectSum.lof LP _ K 0 (K0.of (tensorWordProjective Λ C hQ u)))).val =
      tensorWordVector u wt at hvec
  have hregvec : (tensorModuleEquiv C hQ hR Λ wt hwt
    (DirectSum.lof LP _ K 0 (K0.of reg))).val = tensorWordVector u wt :=
    (congrArg (fun a : K 0 =>
      (tensorModuleEquiv C hQ hR Λ wt hwt (DirectSum.lof LP _ K 0 a)).val) hword).symm.trans hvec
  let := tensorProductAlgebra_finite Λ (0 : Multiset I) hQ
  let := HasGdim.of_finiteDimensional 𝒜
  rw [tensorHomAgrees_iff, regular_class s hs, regular_class t ht, hregvec,
    vacuum_homForm_regular G, TensorPairing.orderedForm_empty]
  simp [u, tensorWordVector, PiTensorProduct.isEmptyEquiv_apply_tprod]

private def homAgreementAtSize (n : ℕ) : Prop :=
  ∀ (ℓ : ℕ) (ν : Multiset I), ℓ + ν.card = n →
    ∀ (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R)
      (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
      (x y : tensorProjectiveGroup C hQ Λ ν),
        tensorHomAgrees C hQ hR Λ wt hwt ν x y

private theorem agrees_at_size (n : ℕ) : homAgreementAtSize C hQ hR n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ℓ ν hn Λ wt hwt x y
    apply tensorHomAgrees_of_sequenceProj C hQ hR Λ wt hwt ν _ x y
    intro s t hs ht
    by_cases hpos : 0 < ℓ + ν.card
    · have black_case (a b : KLR.Seq (stendhalWeight ℓ ν))
          (ha : IsRedOrdered a) (hb : IsRedOrdered b) (i : I)
          (hblack : a.lbl (terminalPos hpos) = .inl i) :
          tensorHomAgrees C hQ hR Λ wt hwt ν (K0.of (sequenceProj (inductionGrading C hQ Λ) a ha))
            (K0.of (sequenceProj (inductionGrading C hQ Λ) b hb)) := by
        have hmem := a.mem (terminalPos hpos)
        change a.lbl (terminalPos hpos) ∈ stendhalWeight ℓ ν at hmem
        rw [hblack] at hmem
        have hi : i ∈ ν := by simpa [stendhalWeight] using hmem
        obtain ⟨β, hβ⟩ := Multiset.exists_cons_of_mem hi
        rw [← Multiset.singleton_add] at hβ
        subst ν
        obtain ⟨u, hu, he⟩ := exists_appendBlack_terminal a hblack ha
        subst a
        rw [← blackIndK0_sequenceProj (inductionGrading C hQ Λ) i u hu]
        have hsmall : ℓ + β.card < n := by
          simp only [Multiset.card_add, Multiset.card_singleton] at hn
          omega
        exact tensorHomAgrees_blackInd C hQ hR Λ wt hwt i β
          (ih _ hsmall ℓ β rfl Λ wt hwt) _ _
      cases hsEnd : s.lbl (terminalPos hpos) with
      | inl i => exact black_case s t hs ht i hsEnd
      | inr r =>
        cases htEnd : t.lbl (terminalPos hpos) with
        | inl i =>
          exact (tensorHomAgrees_sequenceProj_comm C hQ hR Λ wt hwt ν s t hs ht).mpr
            (black_case t s ht hs i htEnd)
        | inr r' =>
          cases ℓ with
          | zero => exact r.elim0
          | succ ℓ =>
            have hp : terminalPos hpos = lastRedPosition ℓ ν := by
              apply Fin.ext
              change (stendhalWeight (ℓ + 1) ν).card - 1 = ν.card + ℓ
              rw [cardinal_weight]
              omega
            have hsr := terminal_red_last s hs r (by simpa only [hp] using hsEnd)
            have htr := terminal_red_last t ht r' (by simpa only [hp] using htEnd)
            obtain ⟨⟨u, hu⟩, he⟩ := (appendRedOrderedEquiv (ℓ := ℓ) (ν := ν)).surjective ⟨s, hs, hsr⟩
            obtain ⟨⟨v, hv⟩, hf⟩ := (appendRedOrderedEquiv (ℓ := ℓ) (ν := ν)).surjective ⟨t, ht, htr⟩
            have hes : appendRedLoading u = s := congrArg Subtype.val he
            have het : appendRedLoading v = t := congrArg Subtype.val hf
            subst s
            subst t
            apply (tensorHomAgrees_appendRed C hQ hR Λ wt hwt ν u v hu hv).mpr
            exact ih (ℓ + ν.card) (by omega) ℓ ν rfl _ _ _ _ _
    · have hℓ : ℓ = 0 := by omega
      have hν : ν = 0 := Multiset.card_eq_zero.mp (by omega)
      subst ℓ
      subst ν
      exact agrees_empty_boundary C hQ hR Λ wt hwt s t hs ht

/-- The corrected tensor form agrees with the graded Hom form on all virtual
projectives at each fixed black content (Webster, arXiv:1309.3796v2,
§4.7, Lemma 4.36, with the second-argument repair to Proposition 4.33). -/
theorem tensorHomAgrees_all {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R)
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (ν : Multiset I)
    (x y : tensorProjectiveGroup C hQ Λ ν) :
    tensorHomAgrees C hQ hR Λ wt hwt ν x y :=
  agrees_at_size C hQ hR (ℓ + ν.card) ℓ ν rfl Λ wt hwt x y

end Categorification.Stendhal.FirstWeight
