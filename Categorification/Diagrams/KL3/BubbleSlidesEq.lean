/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.BubbleSlides

/-!
# Bubble slides in `U`: the case `i = j`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.2,
Proposition 3.3 (`prop_bubble_slide1`), case `i = j`. KL III refer to A. Lauda,
*A categorification of quantum sl(2)*, arXiv:0803.3652v3, Proposition 5.6, whose proof is
"the reduction to bubbles and the identity decomposition". We give that argument in full.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## A summation identity -/

theorem sum_range_sum_range_succ {M : Type*} [AddCommMonoid M] (G : ℕ → M) (n : ℕ) :
    ∑ f ∈ Finset.range n, ∑ g ∈ Finset.range (f + 1), G g = ∑ j ∈ Finset.range n, (n - j) • G j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun j => (n + 1 - j) • G j),
      Nat.add_sub_cancel_left, one_smul, Finset.sum_range_succ, ← add_assoc,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.1 hj
    rw [show n + 1 - j = (n - j) + 1 by omega, add_smul, one_smul]

/-- The counting identity behind the coefficients `α + 1 - ℓ` of the bubble slide:
`∑_{a<m} ∑_{j ≤ a+N} G_j + ∑_{f<N} ∑_{g ≤ f} G_g = ∑_{j < m+N} (m+N-j) G_j`. -/
theorem sum_slide_identity {M : Type*} [AddCommMonoid M] (G : ℕ → M) (m : ℕ) (N : ℤ) :
    ∑ a ∈ Finset.range m, ∑ j ∈ Finset.range ((a : ℤ) + N + 1).toNat, G j +
        ∑ f ∈ Finset.range N.toNat, ∑ g ∈ Finset.range (f + 1), G g =
      ∑ j ∈ Finset.range ((m : ℤ) + N).toNat, ((m : ℤ) + N - j).toNat • G j := by
  induction m with
  | zero =>
    rw [Finset.sum_range_zero, zero_add, sum_range_sum_range_succ]
    simp only [Nat.cast_zero, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.1 hj
    congr 1
    omega
  | succ m ih =>
    rw [Finset.sum_range_succ, add_right_comm, ih]
    by_cases h : 0 ≤ (m : ℤ) + N
    · have e₁ : ((↑(m + 1) : ℤ) + N).toNat = ((m : ℤ) + N).toNat + 1 := by push_cast; omega
      have e₂ : ((m : ℤ) + N + 1).toNat = ((m : ℤ) + N).toNat + 1 := by omega
      rw [e₁, e₂, Finset.sum_range_succ, Finset.sum_range_succ, ← add_assoc,
        ← Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        have := Finset.mem_range.1 hj
        rw [show ((↑(m + 1) : ℤ) + N - j).toNat = ((m : ℤ) + N - j).toNat + 1 by push_cast; omega,
          add_smul, one_smul]
      · rw [show ((↑(m + 1) : ℤ) + N - (((m : ℤ) + N).toNat : ℕ)).toNat = 1 by push_cast; omega,
          one_smul]
    · have e₁ : ((↑(m + 1) : ℤ) + N).toNat = 0 := by push_cast; omega
      have e₂ : ((m : ℤ) + N + 1).toNat = 0 := by omega
      have e₃ : ((m : ℤ) + N).toNat = 0 := by omega
      rw [e₁, e₂, e₃]
      simp

/-! ## Dots around caps and cups -/

/-- A downward dot on the left strand of the cap `F_i E_i ⟶ 1` equals an upward dot on its
right strand (KL III (3.3) and a zigzag relation). -/
theorem dg_dot_cap_up (ν : X) (i : I) :
    dg RD k ν [dn i, up i] [] [([], .dot (dn i), [up i]), ([], .cap (up i), [])] =
      dg RD k ν [dn i, up i] [] [([dn i], .dot (up i), []), ([], .cap (up i), [])] := by
  dstep [] [([], .cap (up i), [])] [] [up i] (dg_cycDotR RD k i (wt RD ν [up i]))
  dstep [([dn i], .cup (up i), [up i]), ([dn i], .dot (up i), [dn i, up i])] [] [] []
    (dg_swap' RD k ν [] [] [] (.cap (up i)) (.cap (up i)))
  dstep [([dn i], .cup (up i), [up i])] [([], .cap (up i), [])] [] []
    (dg_swap' RD k ν [dn i] [] [] (.dot (up i)) (.cap (up i)))
  dstep [] [([dn i], .dot (up i), []), ([], .cap (up i), [])] [dn i] []
    (dg_zigL' RD k ν (up i))
  lnf

/-- `m` downward dots on the left strand of the cap `F_i E_i ⟶ 1` equal `m` upward dots on its
right strand. -/
theorem dg_dots_cap_up (ν : X) (i : I) (m : ℕ) :
    dg RD k ν [dn i, up i] [] (List.replicate m ([], .dot (dn i), [up i]) ++ [([], .cap (up i), [])]) =
      dg RD k ν [dn i, up i] [] (List.replicate m ([dn i], .dot (up i), []) ++ [([], .cap (up i), [])]) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    dstep [([], .dot (dn i), [up i])] [] [] [] ih
    dstep [] [([], .cap (up i), [])] [] []
      (dg_swap_rep RD k ν [] [] [] (.dot (dn i)) (.dot (up i)) rfl m).symm
    lnf
    dstep (List.replicate m ([dn i], .dot (up i), [])) [] [] [] (dg_dot_cap_up RD k ν i)
    simp [whL, List.replicate_succ']

/-! ## The nilHecke algebra on `E_i E_i` -/

section NilHecke

variable (ν : X) (i : I)

/-- `n` dots on the left strand of `E_i E_i 1_ν`. -/
abbrev nhDotL (n : ℕ) : End ((pres RD k).obj (ob RD ν [up i, up i])) :=
  dg RD k ν [up i, up i] [up i, up i] (List.replicate n ([], .dot (up i), [up i]))

/-- `n` dots on the right strand of `E_i E_i 1_ν`. -/
abbrev nhDotR (n : ℕ) : End ((pres RD k).obj (ob RD ν [up i, up i])) :=
  dg RD k ν [up i, up i] [up i, up i] (List.replicate n ([up i], .dot (up i), []))

/-- The crossing of `E_i E_i 1_ν`. -/
abbrev nhCross : End ((pres RD k).obj (ob RD ν [up i, up i])) :=
  dg RD k ν [up i, up i] [up i, up i] [([], .cross true i i, [])]

theorem nhDotL_add (a b : ℕ) : nhDotL RD k ν i a ≫ nhDotL RD k ν i b = nhDotL RD k ν i (a + b) := by
  simp only [nhDotL]; rw [dg_comp (by schain) (by schain), List.replicate_add]

theorem nhDotR_add (a b : ℕ) : nhDotR RD k ν i a ≫ nhDotR RD k ν i b = nhDotR RD k ν i (a + b) := by
  simp only [nhDotR]; rw [dg_comp (by schain) (by schain), List.replicate_add]

theorem nhDotL_zero : nhDotL RD k ν i 0 = 𝟙 _ := by simp only [nhDotL]; rw [List.replicate_zero, dg_nil]

theorem nhDotR_zero : nhDotR RD k ν i 0 = 𝟙 _ := by simp only [nhDotR]; rw [List.replicate_zero, dg_nil]

theorem nhDotR_nhDotL_one (n : ℕ) : nhDotR RD k ν i n ≫ nhDotL RD k ν i 1 = nhDotL RD k ν i 1 ≫ nhDotR RD k ν i n := by
  simp only [nhDotR, nhDotL]
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  exact dg_swap_rep RD k ν [] [] [] (.dot (up i)) (.dot (up i)) rfl n

theorem nhDotR_nhDotL (a b : ℕ) : nhDotR RD k ν i b ≫ nhDotL RD k ν i a = nhDotL RD k ν i a ≫ nhDotR RD k ν i b := by
  induction a with
  | zero => rw [nhDotL_zero, Category.comp_id, Category.id_comp]
  | succ a ih =>
    rw [← nhDotL_add RD k ν i a 1, ← Category.assoc, ih, Category.assoc, nhDotR_nhDotL_one,
      ← Category.assoc]

/-- `eq_nil_dotslide`: `x₁ ψ = ψ x₂ + 1`. -/
theorem nhDotL_nhCross : nhDotL RD k ν i 1 ≫ nhCross RD k ν i = nhCross RD k ν i ≫ nhDotR RD k ν i 1 + 𝟙 _ := by
  simp only [nhDotL, nhCross, nhDotR]
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain), ← dg_nil]
  exact dg_slideREq RD k ν i

/-- `eq_nil_rels`: `ψ² = 0`. -/
theorem nhCross_nhCross : nhCross RD k ν i ≫ nhCross RD k ν i = 0 := by
  simp only [nhCross]; rw [dg_comp (by schain) (by schain)]
  exact dg_sqEq RD k ν i

/-- **Induction formula** (Lauda, Proposition 5.2): `ψ x₂^m = x₁^m ψ - ∑_{a<m} x₁^a x₂^{m-1-a}`. -/
theorem nhCross_nhDotR (m : ℕ) :
    nhCross RD k ν i ≫ nhDotR RD k ν i m =
      nhDotL RD k ν i m ≫ nhCross RD k ν i - ∑ a ∈ Finset.range m, nhDotL RD k ν i a ≫ nhDotR RD k ν i (m - 1 - a) := by
  induction m with
  | zero => rw [nhDotR_zero, nhDotL_zero, Category.comp_id, Category.id_comp, Finset.sum_range_zero,
      sub_zero]
  | succ m ih =>
    rw [← nhDotR_add RD k ν i m 1, ← Category.assoc, ih, Preadditive.sub_comp, Preadditive.sum_comp,
      Category.assoc, eq_sub_of_add_eq (nhDotL_nhCross RD k ν i).symm, Preadditive.comp_sub,
      Category.comp_id, ← Category.assoc, nhDotL_add, Finset.sum_range_succ, Nat.add_sub_cancel,
      Nat.sub_self, nhDotR_zero, Category.comp_id]
    have : ∀ a ∈ Finset.range m, (nhDotL RD k ν i a ≫ nhDotR RD k ν i (m - 1 - a)) ≫ nhDotR RD k ν i 1 =
        nhDotL RD k ν i a ≫ nhDotR RD k ν i (m - a) := by
      intro a ha
      rw [Category.assoc, nhDotR_add]
      congr 2
      have := Finset.mem_range.1 ha
      omega
    rw [Finset.sum_congr rfl this, sub_sub, add_comm (nhDotL RD k ν i m)]

/-- `ψ x₂^m ψ = -∑_{a<m} x₁^a x₂^{m-1-a} ψ`. -/
theorem nhCross_nhDotR_nhCross (m : ℕ) :
    nhCross RD k ν i ≫ nhDotR RD k ν i m ≫ nhCross RD k ν i =
      -∑ a ∈ Finset.range m, nhDotL RD k ν i a ≫ nhDotR RD k ν i (m - 1 - a) ≫ nhCross RD k ν i := by
  rw [← Category.assoc, nhCross_nhDotR, Preadditive.sub_comp, Category.assoc, nhCross_nhCross, Limits.comp_zero,
    zero_sub, Preadditive.sum_comp]
  simp only [Category.assoc]

/-- `eq_nil_dotslide`: `ψ x₁ = x₂ ψ + 1`. -/
theorem nhCross_nhDotL : nhCross RD k ν i ≫ nhDotL RD k ν i 1 = nhDotR RD k ν i 1 ≫ nhCross RD k ν i + 𝟙 _ := by
  simp only [nhDotL, nhCross, nhDotR]
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain), ← dg_nil]
  exact dg_slideLEq RD k ν i

/-- **Induction formula**, mirror form: `ψ x₁^m = x₂^m ψ + ∑_{a<m} x₂^a x₁^{m-1-a}`. -/
theorem nhCross_nhDotL_pow (m : ℕ) :
    nhCross RD k ν i ≫ nhDotL RD k ν i m =
      nhDotR RD k ν i m ≫ nhCross RD k ν i + ∑ a ∈ Finset.range m, nhDotR RD k ν i a ≫ nhDotL RD k ν i (m - 1 - a) := by
  induction m with
  | zero => rw [nhDotR_zero, nhDotL_zero, Category.comp_id, Category.id_comp, Finset.sum_range_zero,
      add_zero]
  | succ m ih =>
    rw [← nhDotL_add RD k ν i m 1, ← Category.assoc, ih, Preadditive.add_comp, Preadditive.sum_comp,
      Category.assoc, nhCross_nhDotL, Preadditive.comp_add, Category.comp_id, ← Category.assoc, nhDotR_add,
      Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, nhDotL_zero, Category.comp_id]
    have : ∀ a ∈ Finset.range m, (nhDotR RD k ν i a ≫ nhDotL RD k ν i (m - 1 - a)) ≫ nhDotL RD k ν i 1 =
        nhDotR RD k ν i a ≫ nhDotL RD k ν i (m - a) := by
      intro a ha
      rw [Category.assoc, nhDotL_add]
      congr 2
      have := Finset.mem_range.1 ha
      omega
    rw [Finset.sum_congr rfl this, add_assoc, add_comm (nhDotR RD k ν i m)]

/-- `ψ x₁^m ψ = ∑_{a<m} x₂^a x₁^{m-1-a} ψ`. -/
theorem nhCross_nhDotL_nhCross (m : ℕ) :
    nhCross RD k ν i ≫ nhDotL RD k ν i m ≫ nhCross RD k ν i =
      ∑ a ∈ Finset.range m, nhDotR RD k ν i a ≫ nhDotL RD k ν i (m - 1 - a) ≫ nhCross RD k ν i := by
  rw [← Category.assoc, nhCross_nhDotL_pow, Preadditive.add_comp, Category.assoc, nhCross_nhCross, Limits.comp_zero,
    zero_add, Preadditive.sum_comp]
  simp only [Category.assoc]

end NilHecke

/-! ## Closing the left strand of `E_i E_i` -/

section ClosureL

variable (ν : X) (i : I)

/-- Closing the left strand of `E_i E_i 1_ν` to the left (a counterclockwise loop). -/
def ptrL : End ((pres RD k).obj (ob RD ν [up i, up i])) →ₗ[k] End ((pres RD k).obj (ob RD ν [up i])) where
  toFun f := dg RD k ν [up i] [dn i, up i, up i] [([], .cup (dn i), [up i])] ≫
    plcL RD k ν [dn i] [] [up i, up i] [up i, up i] f ≫
      dg RD k ν [dn i, up i, up i] [up i] [([], .cap (up i), [up i])]
  map_add' f g := by rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

theorem ptrL_apply (f : End ((pres RD k).obj (ob RD ν [up i, up i]))) :
    ptrL RD k ν i f = dg RD k ν [up i] [dn i, up i, up i] [([], .cup (dn i), [up i])] ≫
      plcL RD k ν [dn i] [] [up i, up i] [up i, up i] f ≫
        dg RD k ν [dn i, up i, up i] [up i] [([], .cap (up i), [up i])] := rfl

theorem ptrL_dg (A : List (LayerData I)) :
    ptrL RD k ν i (dg RD k ν [up i, up i] [up i, up i] A) =
      dg RD k ν [up i] [up i] ([([], .cup (dn i), [up i])] ++ A.map (whL [dn i] []) ++
        [([], .cap (up i), [up i])]) := by
  rw [ptrL_apply, plcL_dg_nil]
  show dg RD k ν [up i] [dn i, up i, up i] _ ≫ dg RD k ν [dn i, up i, up i] [dn i, up i, up i] _ ≫
    dg RD k ν [dn i, up i, up i] [up i] _ = _
  by_cases hA : SChain [up i, up i] A [up i, up i]
  · have hA' : SChain [dn i, up i, up i] (A.map (whL [dn i] [])) [dn i, up i, up i] :=
      hA.whisk [dn i] []
    rw [dg_comp hA' (by schain), dg_comp (by schain) (hA'.append (by schain))]
    simp only [List.append_assoc]
  · have h0 : ¬ SChain [dn i, up i, up i] (A.map (whL [dn i] [])) [dn i, up i, up i] :=
      fun h => hA (SChain.of_whisk (u := [dn i]) (v := []) (s := [up i, up i])
        (t := [up i, up i]) h)
    rw [dg_of_not h0, Limits.zero_comp, Limits.comp_zero, dg_of_not]
    intro h
    obtain ⟨a, h₁, h₂⟩ := SChain.split h
    obtain ⟨b, h₃, h₄⟩ := SChain.split h₁
    obtain rfl : b = [dn i, up i, up i] := h₃.eq_target (by schain)
    obtain rfl : a = [dn i, up i, up i] := h₂.eq_source (by schain)
    exact hA (SChain.of_whisk (u := [dn i]) (v := []) (by simpa using h₄))

theorem plcL_nhDotR (b : ℕ) :
    plcL RD k ν [dn i] [] [up i, up i] [up i, up i] (nhDotR RD k ν i b) =
      dg RD k ν [dn i, up i, up i] [dn i, up i, up i]
        (List.replicate b ([dn i, up i], .dot (up i), [])) := by
  simp only [nhDotR]; rw [plcL_dg_nil]; lnf

/-- Dots on the right (unclosed) strand below the left closure come out of it. -/
theorem ptrL_nhDotR_comp (b : ℕ) (f : End ((pres RD k).obj (ob RD ν [up i, up i]))) :
    ptrL RD k ν i (nhDotR RD k ν i b ≫ f) = dotsU RD k ν (up i) b ≫ ptrL RD k ν i f := by
  have E : dg RD k ν [up i] [dn i, up i, up i] [([], .cup (dn i), [up i])] ≫
      dg RD k ν [dn i, up i, up i] [dn i, up i, up i]
        (List.replicate b ([dn i, up i], .dot (up i), [])) =
      dotsU RD k ν (up i) b ≫ dg RD k ν [up i] [dn i, up i, up i] [([], .cup (dn i), [up i])] := by
    rw [dotsU, dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
    exact (dg_swap_rep RD k ν [] [] [] (.cup (dn i)) (.dot (up i)) rfl b).symm
  rw [ptrL_apply, ptrL_apply, ← plcL_comp RD k ν [dn i] [] rfl rfl, plcL_nhDotR]
  simp only [Category.assoc]
  rw [← Category.assoc (dg RD k ν [up i] [dn i, up i, up i] _), E, Category.assoc]

/-- Dots on the right (unclosed) strand above the left closure come out of it. -/
theorem ptrL_comp_nhDotR (b : ℕ) (f : End ((pres RD k).obj (ob RD ν [up i, up i]))) :
    ptrL RD k ν i (f ≫ nhDotR RD k ν i b) = ptrL RD k ν i f ≫ dotsU RD k ν (up i) b := by
  have E : dg RD k ν [dn i, up i, up i] [dn i, up i, up i]
        (List.replicate b ([dn i, up i], .dot (up i), [])) ≫
      dg RD k ν [dn i, up i, up i] [up i] [([], .cap (up i), [up i])] =
      dg RD k ν [dn i, up i, up i] [up i] [([], .cap (up i), [up i])] ≫ dotsU RD k ν (up i) b := by
    rw [dotsU, dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
    exact dg_swap_rep RD k ν [] [] [] (.cap (up i)) (.dot (up i)) rfl b
  rw [ptrL_apply, ptrL_apply, ← plcL_comp RD k ν [dn i] [] rfl rfl, plcL_nhDotR]
  simp only [Category.assoc]
  rw [E]

/-- The left closure of `x₁^a` is a counterclockwise bubble to the left of the strand. -/
theorem ptrL_nhDotL (a : ℕ) :
    ptrL RD k ν i (nhDotL RD k ν i a) = bubLU RD k ν (up i) (ccwU RD k (wt RD ν [up i]) i a) := by
  simp only [nhDotL]
  rw [ptrL_dg, ccwU_of_nonneg, bubLU, plcL_dg]
  show _ = dg RD k ν [up i] [up i] _
  congr 1; simp only [ccwLs]; lnf

/-- The left closure of the crossing is the left curl (KL III, curl relation). -/
theorem ptrL_nhCross :
    ptrL RD k ν i (nhCross RD k ν i) =
      ∑ g ∈ Finset.range (ip RD i (wt RD ν [up i]) + 1).toNat,
        bubLU RD k ν (up i) (ccwU RD k (wt RD ν [up i]) i (-ip RD i (wt RD ν [up i]) - 1 + g)) ≫
          dotsU RD k ν (up i) (ip RD i (wt RD ν [up i]) - g).toNat := by
  simp only [nhCross]
  rw [ptrL_dg, ← dg_curlL]
  congr 1

/-- **More reduction to bubbles** (Lauda, Proposition 5.4, second equation): the left curl with
`a` dots on its loop is `∑_{j=0}^{a+N} ccw_{-N-1+j} x^{a+N-j}` (bubbles to the left of the
strand, `N = ⟨i, ν + i_X⟩`; fake bubbles occur for `j ≤ N`). -/
theorem ptrL_nhDotL_nhCross (a : ℕ) :
    ptrL RD k ν i (nhDotL RD k ν i a ≫ nhCross RD k ν i) =
      ∑ j ∈ Finset.range (a + ip RD i (wt RD ν [up i]) + 1).toNat,
        bubLU RD k ν (up i) (ccwU RD k (wt RD ν [up i]) i (-ip RD i (wt RD ν [up i]) - 1 + j)) ≫
          dotsU RD k ν (up i) (a + ip RD i (wt RD ν [up i]) - j).toNat := by
  induction a with
  | zero =>
    rw [nhDotL_zero, Category.id_comp, ptrL_nhCross]
    simp only [Nat.cast_zero, zero_add]
  | succ a ih =>
    rw [← nhDotL_add, Category.assoc, nhDotL_nhCross, Preadditive.comp_add, Category.comp_id, map_add,
      ← Category.assoc, ptrL_comp_nhDotR, ih, ptrL_nhDotL, Preadditive.sum_comp]
    by_cases ha : 0 ≤ (a : ℤ) + ip RD i (wt RD ν [up i]) + 1
    · have hr : ((↑(a + 1) : ℤ) + ip RD i (wt RD ν [up i]) + 1).toNat =
          ((a : ℤ) + ip RD i (wt RD ν [up i]) + 1).toNat + 1 := by
        push_cast; omega
      rw [hr, Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [Category.assoc, dotsU_add]
        have := Finset.mem_range.1 hj
        congr 2
        push_cast; omega
      · have hj : (-ip RD i (wt RD ν [up i]) - 1 +
            ((((a : ℤ) + ip RD i (wt RD ν [up i]) + 1).toNat : ℕ) : ℤ)) = (a : ℤ) := by
          rw [Int.toNat_of_nonneg ha]; ring
        rw [hj]
        have h0 : ((↑(a + 1) : ℤ) + ip RD i (wt RD ν [up i]) -
            ((((a : ℤ) + ip RD i (wt RD ν [up i]) + 1).toNat : ℕ) : ℤ)).toNat = 0 := by
          rw [Int.toNat_of_nonneg ha]; push_cast; omega
        rw [h0, dotsU_zero, Category.comp_id]
    · have h₁ : ((a : ℤ) + ip RD i (wt RD ν [up i]) + 1).toNat = 0 := by omega
      have h₂ : ((↑(a + 1) : ℤ) + ip RD i (wt RD ν [up i]) + 1).toNat = 0 := by push_cast; omega
      rw [h₁, h₂, Finset.sum_range_zero, Finset.sum_range_zero, zero_add, ccwU_of_nonneg,
        dg_ccwNeg RD k _ i a (by omega)]
      exact map_zero _
end ClosureL

/-! ## The terms of the decomposition of `1_{E F}` inside a bubble -/

section DecompTerms

variable (lam : X) (i : I)

/-- A counterclockwise bubble with `m` dots to the right of `E_i`, whose left strand is closed
off by the cap with `p` dots of the `E F` decomposition: `p + m` dots on the strand. -/
theorem dg_bubble_dotCap (m p : ℕ) :
    dg RD k lam [up i] [up i]
        ([([up i], .cup (dn i), [])] ++ List.replicate m ([up i, dn i], .dot (up i), []) ++
          (dotCapEFLs i p).map (whL [] [up i])) = dotsU RD k lam (up i) (p + m) := by
  simp only [dotCapEFLs]
  dstep [([up i], .cup (dn i), [])] [([], .cap (dn i), [up i])] [] []
    (dg_swap_dots RD k lam [] [dn i] [] (up i) (up i) m p)
  dstep [] (List.replicate m ([up i, dn i], .dot (up i), []) ++ [([], .cap (dn i), [up i])]) [] []
    (dg_swap_rep' RD k lam [] [] [] (.cup (dn i)) (.dot (up i)) rfl p).symm
  dstep (List.replicate p ([], .dot (up i), []) ++ [([up i], .cup (dn i), [])]) [] [] []
    (dg_swap_rep RD k lam [] [] [] (.cap (dn i)) (.dot (up i)) rfl m)
  dstep (List.replicate p ([], .dot (up i), [])) (List.replicate m ([], .dot (up i), [])) [] []
    (dg_zigR' RD k lam (dn i))
  rw [dotsU, List.replicate_add]
  lnf

/-- The cup with `q` dots of the `E F` decomposition, closed off by the cap of a
counterclockwise bubble to the right of `E_i`: `q` dots on the strand. -/
theorem dg_cupDot_bubble (q : ℕ) :
    dg RD k lam [up i] [up i]
        ((cupDotEFLs i q).map (whL [] [up i]) ++ [([up i], .cap (up i), [])]) =
      dotsU RD k lam (up i) q := by
  simp only [cupDotEFLs]
  dstep [([], .cup (up i), [up i])] [] [up i] [] (dg_dots_cap_up RD k lam i q)
  dstep [] [([up i], .cap (up i), [])] [] []
    (dg_swap_rep RD k lam [] [] [] (.cup (up i)) (.dot (up i)) rfl q).symm
  dstep (List.replicate q ([], .dot (up i), [])) [] [] [] (dg_zigL' RD k lam (up i))
  rw [dotsU]
  lnf

/-- A term `(cap with p dots) β (cup with q dots)` of the decomposition of `1_{E F}`, inserted
between the strand `E_i` and the left strand of a counterclockwise bubble with `m` dots on its
right, equals `β` to the left of the strand with `p + m + q` dots on the strand. -/
theorem ctxL_decompTerm (m p q : ℕ) (β : End ((pres RD k).obj (ob RD (wt RD lam [up i]) []))) :
    ctxL RD k lam [up i] [up i]
        ([([up i], .cup (dn i), [])] ++ List.replicate m ([up i, dn i], .dot (up i), [])) [] [up i]
        [([up i], .cap (up i), [])] [up i, dn i] [up i, dn i]
        (dg RD k (wt RD lam [up i]) [up i, dn i] [] (dotCapEFLs i p) ≫ β ≫
          dg RD k (wt RD lam [up i]) [] [up i, dn i] (cupDotEFLs i q)) =
      bubLU RD k lam (up i) β ≫ dotsU RD k lam (up i) (p + m + q) := by
  have hw : wt RD (wt RD lam [up i]) [up i, dn i] = wt RD (wt RD lam [up i]) [] := by simp
  show dg RD k lam [up i] ([] ++ [up i, dn i] ++ [up i]) _ ≫ plcL RD k lam [] [up i] _ _ _ ≫
    dg RD k lam ([] ++ [up i, dn i] ++ [up i]) [up i] _ = _
  rw [← plcL_comp RD k lam [] [up i] hw.symm hw, ← plcL_comp RD k lam [] [up i] rfl hw,
    plcL_dg, plcL_dg]
  have E1 : dg RD k lam [up i] ([] ++ [] ++ [up i])
      ([([up i], .cup (dn i), [])] ++ List.replicate m ([up i, dn i], .dot (up i), []) ++
        (dotCapEFLs i p).map (whL [] [up i])) = dotsU RD k lam (up i) (p + m) :=
    dg_bubble_dotCap RD k lam i m p
  have E2 : dg RD k lam ([] ++ [] ++ [up i]) [up i]
      ((cupDotEFLs i q).map (whL [] [up i]) ++ [([up i], .cap (up i), [])]) =
      dotsU RD k lam (up i) q := dg_cupDot_bubble RD k lam i q
  simp only [Category.assoc]
  rw [← Category.assoc (dg RD k lam [up i] _ _), dg_comp (by schain) (by schain),
    dg_comp (by schain) (by schain), E1, E2,
    ← Category.assoc, ← bubLU_comm, Category.assoc, dotsU_add]

end DecompTerms

/-! ## The bubble slide for `i = j` -/

set_option maxHeartbeats 1000000 in
/-- **Bubble slide, counterclockwise, `i = j`** (KL III Proposition 3.3, first display, case
`i = j`; Lauda, Proposition 5.6, (5.26)), for a real bubble with `m ≥ 0` dots: with
`λ' = λ + i_X` the region to the left of the strand and `N = ⟨i, λ'⟩`,
`ccw_m ⊗ 1 = ∑_{j=0}^{m+N-1} (m+N-j) (1 ⊗ ccw_{-N-1+j}) x^{m+N-1-j}`,
the bubbles on the right being in the region `λ` and those on the left in `λ'` (they may be fake
bubbles). With the printed label `m = -⟨i,λ⟩-1+α` one has `m + N - 1 = α` (as `N = ⟨i,λ⟩+2`),
so the right-hand side is `∑_{ℓ=0}^{α} (α+1-ℓ) ccw_{-⟨i,λ+i_X⟩-1+ℓ} x^{α-ℓ}`. -/
theorem dg_ccw_slide_eq (lam : X) (i : I) (m : ℕ) :
    dg RD k lam [up i] [up i]
        ([([up i], .cup (dn i), [])] ++ List.replicate m ([up i, dn i], .dot (up i), []) ++
          [([up i], .cap (up i), [])]) =
      ∑ j ∈ Finset.range ((m : ℤ) + ip RD i (wt RD lam [up i])).toNat,
        ((m : ℤ) + ip RD i (wt RD lam [up i]) - j).toNat •
          (bubLU RD k lam (up i)
              (ccwU RD k (wt RD lam [up i]) i (-ip RD i (wt RD lam [up i]) - 1 + j)) ≫
            dotsU RD k lam (up i) ((m : ℤ) + ip RD i (wt RD lam [up i]) - 1 - j).toNat) := by
  -- the identity decomposition of `1_{E F}` (eq_ident_decomp) between the strand and the bubble
  refine (dg_stepL RD k lam ([([up i], .cup (dn i), [])] ++
      List.replicate m ([up i, dn i], .dot (up i), [])) [([up i], .cap (up i), [])] [] [up i]
    (dg_decompEF RD k i (wt RD lam [up i])) (by schain) (by schain) (by lnf)).trans ?_
  rw [map_add, map_neg, ctxL_dg RD k lam (by schain) (by schain), dg_pull_ccw, map_sum]
  simp only [map_sum, ctxL_decompTerm]
  -- the crossing term: the left closure of `ψ x₂^m ψ`
  have hS : dg RD k lam [up i] [up i]
      ([([], .cup (dn i), [up i]), ([dn i], .cross true i i, [])] ++
        List.replicate m ([dn i, up i], .dot (up i), []) ++
        [([dn i], .cross true i i, []), ([], .cap (up i), [up i])]) =
      ptrL RD k lam i (nhCross RD k lam i ≫ nhDotR RD k lam i m ≫ nhCross RD k lam i) := by
    simp only [nhCross, nhDotR]
    rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain), ptrL_dg]
    congr 1; lnf
  rw [hS, nhCross_nhDotR_nhCross, map_neg, neg_neg, map_sum]
  have hT : ∀ a ∈ Finset.range m, ptrL RD k lam i (nhDotL RD k lam i a ≫ nhDotR RD k lam i (m - 1 - a) ≫
      nhCross RD k lam i) = ∑ j ∈ Finset.range ((a : ℤ) + ip RD i (wt RD lam [up i]) + 1).toNat,
        bubLU RD k lam (up i)
            (ccwU RD k (wt RD lam [up i]) i (-ip RD i (wt RD lam [up i]) - 1 + j)) ≫
          dotsU RD k lam (up i) ((m : ℤ) + ip RD i (wt RD lam [up i]) - 1 - j).toNat := by
    intro a ha
    have ha' := Finset.mem_range.1 ha
    rw [← Category.assoc, ← nhDotR_nhDotL, Category.assoc, ptrL_nhDotR_comp, ptrL_nhDotL_nhCross,
      Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [← Category.assoc, ← bubLU_comm, Category.assoc, dotsU_add]
    congr 2
    omega
  rw [Finset.sum_congr rfl hT]
  have hD : ∀ f ∈ Finset.range (ip RD i (wt RD lam [up i])).toNat, ∀ g ∈ Finset.range (f + 1),
      bubLU RD k lam (up i)
          (ccwU RD k (wt RD lam [up i]) i (-ip RD i (wt RD lam [up i]) - 1 + g)) ≫
        dotsU RD k lam (up i) (f - g + m + ((ip RD i (wt RD lam [up i])).toNat - 1 - f)) =
      bubLU RD k lam (up i)
          (ccwU RD k (wt RD lam [up i]) i (-ip RD i (wt RD lam [up i]) - 1 + g)) ≫
        dotsU RD k lam (up i) ((m : ℤ) + ip RD i (wt RD lam [up i]) - 1 - g).toNat := by
    intro f hf g hg
    have hf' := Finset.mem_range.1 hf
    have hg' := Finset.mem_range.1 hg
    congr 2
    omega
  rw [Finset.sum_congr rfl fun f hf => Finset.sum_congr rfl (hD f hf)]
  exact sum_slide_identity (fun j => bubLU RD k lam (up i)
      (ccwU RD k (wt RD lam [up i]) i (-ip RD i (wt RD lam [up i]) - 1 + j)) ≫
        dotsU RD k lam (up i) ((m : ℤ) + ip RD i (wt RD lam [up i]) - 1 - j).toNat) m _

/-! ## Closing the right strand of `E_i E_i` -/

section ClosureR

variable (lam : X) (i : I)

/-- Closing the right strand of `E_i E_i 1_{λ - i_X}` to the right (a clockwise loop); the
result is an endomorphism of `E_i 1_λ`. -/
def ptrR : End ((pres RD k).obj (ob RD (wt RD lam [dn i]) [up i, up i])) →ₗ[k]
    End ((pres RD k).obj (ob RD lam [up i])) where
  toFun f := dg RD k lam [up i] [up i, up i, dn i] [([up i], .cup (up i), [])] ≫
    plcL RD k lam [] [dn i] [up i, up i] [up i, up i] f ≫
      dg RD k lam [up i, up i, dn i] [up i] [([up i], .cap (dn i), [])]
  map_add' f g := by rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

theorem ptrR_apply (f : End ((pres RD k).obj (ob RD (wt RD lam [dn i]) [up i, up i]))) :
    ptrR RD k lam i f = dg RD k lam [up i] [up i, up i, dn i] [([up i], .cup (up i), [])] ≫
      plcL RD k lam [] [dn i] [up i, up i] [up i, up i] f ≫
        dg RD k lam [up i, up i, dn i] [up i] [([up i], .cap (dn i), [])] := rfl

theorem ptrR_dg (A : List (LayerData I)) :
    ptrR RD k lam i (dg RD k (wt RD lam [dn i]) [up i, up i] [up i, up i] A) =
      dg RD k lam [up i] [up i] ([([up i], .cup (up i), [])] ++ A.map (whL [] [dn i]) ++
        [([up i], .cap (dn i), [])]) := by
  rw [ptrR_apply, plcL_dg]
  show dg RD k lam [up i] [up i, up i, dn i] _ ≫ dg RD k lam [up i, up i, dn i] [up i, up i, dn i] _ ≫
    dg RD k lam [up i, up i, dn i] [up i] _ = _
  by_cases hA : SChain [up i, up i] A [up i, up i]
  · have hA' : SChain [up i, up i, dn i] (A.map (whL [] [dn i])) [up i, up i, dn i] :=
      hA.whisk [] [dn i]
    rw [dg_comp hA' (by schain), dg_comp (by schain) (hA'.append (by schain))]
    simp only [List.append_assoc]
  · have h0 : ¬ SChain [up i, up i, dn i] (A.map (whL [] [dn i])) [up i, up i, dn i] :=
      fun h => hA (SChain.of_whisk (u := []) (v := [dn i]) (s := [up i, up i])
        (t := [up i, up i]) h)
    rw [dg_of_not h0, Limits.zero_comp, Limits.comp_zero, dg_of_not]
    intro h
    obtain ⟨a, h₁, h₂⟩ := SChain.split h
    obtain ⟨b, h₃, h₄⟩ := SChain.split h₁
    obtain rfl : b = [up i, up i, dn i] := h₃.eq_target (by schain)
    obtain rfl : a = [up i, up i, dn i] := h₂.eq_source (by schain)
    exact hA (SChain.of_whisk (u := []) (v := [dn i]) (by simpa using h₄))

theorem plcL_nhDotL (b : ℕ) :
    plcL RD k lam [] [dn i] [up i, up i] [up i, up i] (nhDotL RD k (wt RD lam [dn i]) i b) =
      dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
        (List.replicate b ([], .dot (up i), [up i, dn i])) := by
  simp only [nhDotL]; rw [plcL_dg]; lnf

/-- Dots on the left (unclosed) strand below the right closure come out of it. -/
theorem ptrR_nhDotL_comp (b : ℕ) (f : End ((pres RD k).obj (ob RD (wt RD lam [dn i]) [up i, up i]))) :
    ptrR RD k lam i (nhDotL RD k (wt RD lam [dn i]) i b ≫ f) =
      dotsU RD k lam (up i) b ≫ ptrR RD k lam i f := by
  have E : dg RD k lam [up i] [up i, up i, dn i] [([up i], .cup (up i), [])] ≫
      dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
        (List.replicate b ([], .dot (up i), [up i, dn i])) =
      dotsU RD k lam (up i) b ≫ dg RD k lam [up i] [up i, up i, dn i] [([up i], .cup (up i), [])] := by
    rw [dotsU, dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
    exact (dg_swap_rep' RD k lam [] [] [] (.cup (up i)) (.dot (up i)) rfl b).symm
  rw [ptrR_apply, ptrR_apply, ← plcL_comp RD k lam [] [dn i] rfl rfl, plcL_nhDotL]
  simp only [Category.assoc]
  rw [← Category.assoc (dg RD k lam [up i] [up i, up i, dn i] _), E, Category.assoc]

/-- Dots on the left (unclosed) strand above the right closure come out of it. -/
theorem ptrR_comp_nhDotL (b : ℕ) (f : End ((pres RD k).obj (ob RD (wt RD lam [dn i]) [up i, up i]))) :
    ptrR RD k lam i (f ≫ nhDotL RD k (wt RD lam [dn i]) i b) =
      ptrR RD k lam i f ≫ dotsU RD k lam (up i) b := by
  have E : dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
        (List.replicate b ([], .dot (up i), [up i, dn i])) ≫
      dg RD k lam [up i, up i, dn i] [up i] [([up i], .cap (dn i), [])] =
      dg RD k lam [up i, up i, dn i] [up i] [([up i], .cap (dn i), [])] ≫ dotsU RD k lam (up i) b := by
    rw [dotsU, dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
    exact dg_swap_rep' RD k lam [] [] [] (.cap (dn i)) (.dot (up i)) rfl b
  rw [ptrR_apply, ptrR_apply, ← plcL_comp RD k lam [] [dn i] rfl rfl, plcL_nhDotL]
  simp only [Category.assoc]
  rw [E]

/-- The right closure of `x₂^a` is a clockwise bubble to the right of the strand. -/
theorem ptrR_nhDotR (a : ℕ) :
    ptrR RD k lam i (nhDotR RD k (wt RD lam [dn i]) i a) = bubRU RD k lam (up i) (cwU RD k lam i a) := by
  simp only [nhDotR]
  rw [ptrR_dg, cwU_of_nonneg, bubRU, cwLs, dg_cw_dots, plcL_dg_nil]
  show _ = dg RD k lam [up i] [up i] _
  congr 1; lnf

/-- The right closure of the crossing is the right curl (KL III, curl relation). -/
theorem ptrR_nhCross :
    ptrR RD k lam i (nhCross RD k (wt RD lam [dn i]) i) =
      -∑ f ∈ Finset.range (-ip RD i lam + 1).toNat,
        bubRU RD k lam (up i) (cwU RD k lam i (ip RD i lam - 1 + f)) ≫
          dotsU RD k lam (up i) (-ip RD i lam - f).toNat := by
  simp only [nhCross]
  rw [ptrR_dg, ← dg_curlR]
  congr 1

/-- **More reduction to bubbles** (Lauda, Proposition 5.4, first equation): the right curl with
`a` dots on its loop is `-∑_{ℓ=0}^{a-n} cw_{n-1+ℓ} x^{a-n-ℓ}` (bubbles to the right of the
strand, `n = ⟨i, λ⟩`; fake bubbles occur for `ℓ ≤ -n`). -/
theorem ptrR_nhDotR_nhCross (a : ℕ) :
    ptrR RD k lam i (nhDotR RD k (wt RD lam [dn i]) i a ≫ nhCross RD k (wt RD lam [dn i]) i) =
      -∑ ℓ ∈ Finset.range (a + -ip RD i lam + 1).toNat,
        bubRU RD k lam (up i) (cwU RD k lam i (ip RD i lam - 1 + ℓ)) ≫
          dotsU RD k lam (up i) (a + -ip RD i lam - ℓ).toNat := by
  induction a with
  | zero =>
    rw [nhDotR_zero, Category.id_comp, ptrR_nhCross]
    simp only [Nat.cast_zero, zero_add]
  | succ a ih =>
    rw [← nhDotR_add, Category.assoc, eq_sub_of_add_eq (nhCross_nhDotL RD k _ i).symm, Preadditive.comp_sub,
      Category.comp_id, map_sub, ← Category.assoc, ptrR_comp_nhDotL, ih, ptrR_nhDotR,
      Preadditive.neg_comp, Preadditive.sum_comp, sub_eq_neg_add, ← neg_add, neg_inj]
    by_cases ha : 0 ≤ (a : ℤ) + -ip RD i lam + 1
    · have hr : ((↑(a + 1) : ℤ) + -ip RD i lam + 1).toNat =
          ((a : ℤ) + -ip RD i lam + 1).toNat + 1 := by
        push_cast; omega
      rw [hr, Finset.sum_range_succ, add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [Category.assoc, dotsU_add]
        have := Finset.mem_range.1 hj
        congr 2
        push_cast; omega
      · have hj : (ip RD i lam - 1 + ((((a : ℤ) + -ip RD i lam + 1).toNat : ℕ) : ℤ)) = (a : ℤ) := by
          rw [Int.toNat_of_nonneg ha]; ring
        rw [hj]
        have h0 : ((↑(a + 1) : ℤ) + -ip RD i lam -
            ((((a : ℤ) + -ip RD i lam + 1).toNat : ℕ) : ℤ)).toNat = 0 := by
          rw [Int.toNat_of_nonneg ha]; push_cast; omega
        rw [h0, dotsU_zero, Category.comp_id]
    · have h₁ : ((a : ℤ) + -ip RD i lam + 1).toNat = 0 := by omega
      have h₂ : ((↑(a + 1) : ℤ) + -ip RD i lam + 1).toNat = 0 := by push_cast; omega
      rw [h₁, h₂, Finset.sum_range_zero, Finset.sum_range_zero, add_zero, cwU_of_nonneg,
        dg_cwNeg RD k _ i a (by omega)]
      exact map_zero _

/-- A clockwise bubble with `m` dots (on its upward strand) to the left of `E_i`, whose right
strand is closed off by the cap with `p` dots of the `F E` decomposition: `p + m` dots on the
strand. -/
theorem dg_bubble_dotCapFE (m p : ℕ) :
    dg RD k lam [up i] [up i]
        ([([], .cup (up i), [up i])] ++ List.replicate m ([], .dot (up i), [dn i, up i]) ++
          (dotCapFELs i p).map (whL [up i] [])) = dotsU RD k lam (up i) (p + m) := by
  simp only [dotCapFELs]
  dstep ([([], .cup (up i), [up i])] ++ List.replicate m ([], .dot (up i), [dn i, up i])) [] [up i] []
    (dg_dots_cap_up RD k lam i p)
  dstep [([], .cup (up i), [up i])] [([up i], .cap (up i), [])] [] []
    (dg_swap_dots RD k lam [] [dn i] [] (up i) (up i) p m).symm
  dstep [] (List.replicate m ([], .dot (up i), [dn i, up i]) ++ [([up i], .cap (up i), [])]) [] []
    (dg_swap_rep RD k lam [] [] [] (.cup (up i)) (.dot (up i)) rfl p).symm
  dstep (List.replicate p ([], .dot (up i), []) ++ [([], .cup (up i), [up i])]) [] [] []
    (dg_swap_rep' RD k lam [] [] [] (.cap (up i)) (.dot (up i)) rfl m)
  dstep (List.replicate p ([], .dot (up i), [])) (List.replicate m ([], .dot (up i), [])) [] []
    (dg_zigL' RD k lam (up i))
  rw [dotsU, List.replicate_add]
  lnf

/-- The cup with `q` dots of the `F E` decomposition, closed off by the cap of a clockwise bubble
to the left of `E_i`: `q` dots on the strand. -/
theorem dg_cupDotFE_bubble (q : ℕ) :
    dg RD k lam [up i] [up i]
        ((cupDotFELs i q).map (whL [up i] []) ++ [([], .cap (dn i), [up i])]) =
      dotsU RD k lam (up i) q := by
  simp only [cupDotFELs]
  dstep [([up i], .cup (dn i), [])] [] [] []
    (dg_swap_rep RD k lam [] [] [] (.cap (dn i)) (.dot (up i)) rfl q)
  dstep [] (List.replicate q ([], .dot (up i), [])) [] [] (dg_zigR' RD k lam (dn i))
  rw [dotsU]
  lnf

/-- A term `(cap with p dots) β (cup with q dots)` of the decomposition of `1_{F E}`, inserted
between the right strand of a clockwise bubble with `m` dots and the strand `E_i` on its right,
equals `β` to the right of the strand with `p + m + q` dots on the strand. -/
theorem ctxL_decompTermFE (m p q : ℕ) (β : End ((pres RD k).obj (ob RD lam []))) :
    ctxL RD k lam [up i] [up i]
        ([([], .cup (up i), [up i])] ++ List.replicate m ([], .dot (up i), [dn i, up i])) [up i] []
        [([], .cap (dn i), [up i])] [dn i, up i] [dn i, up i]
        (dg RD k lam [dn i, up i] [] (dotCapFELs i p) ≫ β ≫
          dg RD k lam [] [dn i, up i] (cupDotFELs i q)) =
      bubRU RD k lam (up i) β ≫ dotsU RD k lam (up i) (p + m + q) := by
  have hw : wt RD (wt RD lam []) [dn i, up i] = wt RD (wt RD lam []) [] := by simp
  show dg RD k lam [up i] ([up i] ++ [dn i, up i] ++ []) _ ≫ plcL RD k lam [up i] [] _ _ _ ≫
    dg RD k lam ([up i] ++ [dn i, up i] ++ []) [up i] _ = _
  rw [← plcL_comp RD k lam [up i] [] hw.symm hw, ← plcL_comp RD k lam [up i] [] rfl hw,
    plcL_dg_nil, plcL_dg_nil]
  have E1 : dg RD k lam [up i] ([up i] ++ [] ++ [])
      ([([], .cup (up i), [up i])] ++ List.replicate m ([], .dot (up i), [dn i, up i]) ++
        (dotCapFELs i p).map (whL [up i] [])) = dotsU RD k lam (up i) (p + m) :=
    dg_bubble_dotCapFE RD k lam i m p
  have E2 : dg RD k lam ([up i] ++ [] ++ []) [up i]
      ((cupDotFELs i q).map (whL [up i] []) ++ [([], .cap (dn i), [up i])]) =
      dotsU RD k lam (up i) q := dg_cupDotFE_bubble RD k lam i q
  simp only [Category.assoc]
  rw [← Category.assoc (dg RD k lam [up i] _ _), dg_comp (by schain) (by schain),
    dg_comp (by schain) (by schain), E1, E2,
    ← Category.assoc, ← bubRU_comm, Category.assoc, dotsU_add]

end ClosureR

set_option maxHeartbeats 1000000 in
/-- **Bubble slide, clockwise, `i = j`** (KL III Proposition 3.3, second display, case `i = j`;
Lauda, Proposition 5.6, (5.27)), for a real bubble with `m ≥ 0` dots: with `n = ⟨i, λ⟩` (`λ`
the region to the right of the strand, `λ + i_X` the region of the bubble on the left),
`1 ⊗ cw_m = ∑_{ℓ=0}^{m-n-1} (m-n-ℓ) (cw_{n-1+ℓ} ⊗ 1) x^{m-n-1-ℓ}`
(the bubbles on the right may be fake). With the printed label `m = ⟨i,λ+i_X⟩-1+α = n+1+α`
this is `∑_{ℓ=0}^{α} (α+1-ℓ) x^{α-ℓ} cw_{n-1+ℓ}`. -/
theorem dg_cw_slide_eq (lam : X) (i : I) (m : ℕ) :
    dg RD k lam [up i] [up i]
        ([([], .cup (up i), [up i])] ++ List.replicate m ([up i], .dot (dn i), [up i]) ++
          [([], .cap (dn i), [up i])]) =
      ∑ ℓ ∈ Finset.range ((m : ℤ) + -ip RD i lam).toNat,
        ((m : ℤ) + -ip RD i lam - ℓ).toNat •
          (bubRU RD k lam (up i) (cwU RD k lam i (ip RD i lam - 1 + ℓ)) ≫
            dotsU RD k lam (up i) ((m : ℤ) + -ip RD i lam - 1 - ℓ).toNat) := by
  -- move the dots of the bubble to its upward strand
  dstep [] [] [] [up i] (dg_cw_dots RD k (wt RD lam [up i]) i m)
  -- the identity decomposition of `1_{F E}` (eq_ident_decomp) between the bubble and the strand
  refine (dg_stepL RD k lam ([([], .cup (up i), [up i])] ++
      List.replicate m ([], .dot (up i), [dn i, up i])) [([], .cap (dn i), [up i])] [up i] []
    (dg_decompFE RD k i lam) (by schain) (by schain) (by lnf)).trans ?_
  rw [map_add, map_neg, ctxL_dg_nil RD k lam (by schain) (by schain), dg_pull_cw, map_sum]
  simp only [map_sum, ctxL_decompTermFE]
  -- the crossing term: the right closure of `ψ x₁^m ψ`
  have hS : dg RD k lam [up i] [up i]
      ([([up i], .cup (up i), []), ([], .cross true i i, [dn i])] ++
        List.replicate m ([], .dot (up i), [up i, dn i]) ++
        [([], .cross true i i, [dn i]), ([up i], .cap (dn i), [])]) =
      ptrR RD k lam i (nhCross RD k (wt RD lam [dn i]) i ≫ nhDotL RD k (wt RD lam [dn i]) i m ≫
        nhCross RD k (wt RD lam [dn i]) i) := by
    simp only [nhCross, nhDotL]
    rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain), ptrR_dg]
    congr 1; lnf
  rw [hS, nhCross_nhDotL_nhCross, map_sum]
  have hT : ∀ a ∈ Finset.range m, ptrR RD k lam i (nhDotR RD k (wt RD lam [dn i]) i a ≫
      nhDotL RD k (wt RD lam [dn i]) i (m - 1 - a) ≫ nhCross RD k (wt RD lam [dn i]) i) =
      -∑ ℓ ∈ Finset.range ((a : ℤ) + -ip RD i lam + 1).toNat,
        bubRU RD k lam (up i) (cwU RD k lam i (ip RD i lam - 1 + ℓ)) ≫
          dotsU RD k lam (up i) ((m : ℤ) + -ip RD i lam - 1 - ℓ).toNat := by
    intro a ha
    have ha' := Finset.mem_range.1 ha
    rw [← Category.assoc, nhDotR_nhDotL, Category.assoc, ptrR_nhDotL_comp, ptrR_nhDotR_nhCross,
      Preadditive.comp_neg, Preadditive.comp_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [← Category.assoc, ← bubRU_comm, Category.assoc, dotsU_add]
    congr 2
    omega
  rw [Finset.sum_congr rfl hT, Finset.sum_neg_distrib, neg_neg]
  have hD : ∀ f ∈ Finset.range (-ip RD i lam).toNat, ∀ g ∈ Finset.range (f + 1),
      bubRU RD k lam (up i) (cwU RD k lam i (ip RD i lam - 1 + g)) ≫
        dotsU RD k lam (up i) (f - g + m + ((-ip RD i lam).toNat - 1 - f)) =
      bubRU RD k lam (up i) (cwU RD k lam i (ip RD i lam - 1 + g)) ≫
        dotsU RD k lam (up i) ((m : ℤ) + -ip RD i lam - 1 - g).toNat := by
    intro f hf g hg
    have hf' := Finset.mem_range.1 hf
    have hg' := Finset.mem_range.1 hg
    congr 2
    omega
  rw [Finset.sum_congr rfl fun f hf => Finset.sum_congr rfl (hD f hf)]
  exact sum_slide_identity (fun ℓ => bubRU RD k lam (up i) (cwU RD k lam i (ip RD i lam - 1 + ℓ)) ≫
    dotsU RD k lam (up i) ((m : ℤ) + -ip RD i lam - 1 - ℓ).toNat) m _

end Categorification.KL3.Diagram
