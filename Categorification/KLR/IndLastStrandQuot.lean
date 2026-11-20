/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.IndLastStrand
import Categorification.KLR.MackeyMap

/-!
# The last strand of an induced module: the quotient

Khovanov–Lauda I (arXiv:0803.4121v2), Proposition 2.18, in the case where one strand coloured
`i` is restricted off the right of an induced module; the KLR input of B. Webster,
*Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5.
-/

namespace Categorification.TypeA

open Equiv

/-- A minimal double coset representative for `(S_{m₀} × S_1) \ S_m / (S_n × S_{n'})` with
fewer than `n'` strands crossing from the second bottom block to the first top block is the
identity. -/
theorem IsDoubleShuffle.eq_one_of_crossCount_lt {m m₀ o n n' : ℕ} (hJ : m₀ + o = m) (ho : o = 1)
    (hK : n + n' = m) {d : Perm (Fin m)} (hd : IsDoubleShuffle hJ hK d)
    (hc : crossCount m₀ n d + 1 ≤ n') : d = 1 := by
  have hle := le_crossCount (n := m₀) (n'' := n) d (by omega) (by omega)
  refine Equiv.ext fun p => Fin.ext ?_
  obtain ⟨h1, h2, h3, h4⟩ := hd.val_eq hJ hK p
  have hp := p.isLt
  have hdp := (d p).isLt
  simp only [Perm.coe_one, id_eq]
  by_cases hpn : p.val < n
  · by_cases hdpm : (d p).val < m₀
    · exact h1 hpn hdpm
    · have := h2 hpn (by omega); omega
  · by_cases hdpm : (d p).val < m₀
    · have := h4 (by omega) hdpm; omega
    · exact h3 (by omega) (by omega)

end Categorification.TypeA

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*}

namespace Seq

variable {X Y Z : Multiset I}

/-- A sequence of `X + Y` whose first block has content `X` is a concatenation. -/
theorem exists_append_eq_of_map (u : Seq (X + Y))
    (hX : Finset.univ.val.map (u.1 ∘ posL Y) = X) :
    ∃ (a : Seq X) (b : Seq Y), a.append b = u ∧ a.1 = u.1 ∘ posL Y := by
  have key : ∀ f : Fin (Multiset.card (X + Y)) → I, Finset.univ.val.map f =
      Finset.univ.val.map (f ∘ posL Y) + Finset.univ.val.map (f ∘ posR X) := by
    intro f
    conv_lhs => rw [← Multiset.map_univ_val_equiv (blockEquiv (card_add' X Y))]
    rw [Multiset.map_map, ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.disjSum,
      Multiset.map_add, Multiset.map_map, Multiset.map_map]
    rfl
  have hmap := key u.1
  rw [u.2, hX] at hmap
  refine ⟨⟨u.1 ∘ posL Y, hX⟩, ⟨u.1 ∘ posR X, (add_left_cancel hmap).symm⟩, ?_, rfl⟩
  apply Subtype.ext; funext a
  obtain ⟨c, rfl⟩ := (blockEquiv (card_add' X Y)).surjective a
  cases c with
  | inl x => exact append_posL _ _ x
  | inr y => exact append_posR _ _ y

theorem cast_cast_symm {μ μ' : Multiset I} (h : μ = μ') (v : Seq μ') :
    cast h (cast h.symm v) = v := by
  subst h; rfl

theorem cast_symm_cast {μ μ' : Multiset I} (h : μ = μ') (v : Seq μ) :
    cast h.symm (cast h v) = v := by
  subst h; rfl

/-- `s (w)` is a concatenation `(u)(c)` with `u ∈ Seq (X + Y)`, `c ∈ Seq Z`, iff `w` is a
concatenation `(t)(c)`. -/
theorem cast_append_mem_concatSet_iff [DecidableEq I] (s : Seq X) (w : Seq (Y + Z)) :
    cast (add_assoc X Y Z).symm (s.append w) ∈ KLRAlgebra.concatSet (X + Y) Z ↔
      w ∈ KLRAlgebra.concatSet Y Z := by
  open KLRAlgebra in
  constructor
  · intro hm
    obtain ⟨u, c, huc⟩ := mem_concatSet.1 hm
    have hu : u.1 ∘ posL Y = s.1 := by
      funext x
      have h1 := congrArg (fun v : Seq (X + Y + Z) => v.1 (posL Z (posL Y x))) huc
      simp only [append_posL, cast_apply] at h1
      rw [Function.comp_apply, h1, append_apply_lt _ _ _ (by simp)]
      exact apply_congr s rfl
    obtain ⟨a, b, rfl, ha⟩ := exists_append_eq_of_map u (by rw [hu]; exact s.2)
    have has : a = s := Subtype.ext (ha.trans hu)
    subst has
    have h2 := congrArg (cast (add_assoc X Y Z)) huc
    rw [append_assoc, cast_cast_symm, append_inj] at h2
    exact mem_concatSet.2 ⟨b, c, h2.2⟩
  · intro hm
    obtain ⟨t, c, rfl⟩ := mem_concatSet.1 hm
    rw [← append_assoc, cast_symm_cast]
    exact append_mem_concatSet _ _

end Seq

variable [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

variable {X Y Z : Multiset I}

theorem sum_ite_mem_concatSet (f : Seq (Y + Z) → KLRAlgebra k Q (X + (Y + Z))) :
    (∑ w : Seq (Y + Z), if w ∈ concatSet Y Z then f w else 0) =
      ∑ t : Seq Y, ∑ c : Seq Z, f (t.append c) := by
  rw [Finset.sum_ite_mem, Finset.univ_inter, concatSet, Finset.sum_image, ← Finset.univ_product_univ,
    Finset.sum_product]
  rintro ⟨t, c⟩ - ⟨t', c'⟩ - h
  obtain ⟨rfl, rfl⟩ := Seq.append_inj.1 h
  rfl

/-- `1_{ν+ν',ν''} 1_{ν,ν'+ν''} = 1_{ν,ν',ν''}` (after reassociating). -/
theorem castKLR_oneConcat_mul_oneConcat :
    castKLR Q (add_assoc X Y Z) (oneConcat Q (X + Y) Z) * oneConcat Q X (Y + Z) =
      concatR X Y Z 1 1 1 := by
  rw [oneConcat_eq' (ν := X) (ν' := Y + Z), Finset.mul_sum, concatR_one]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum, ← sum_ite_mem_concatSet (fun w => e (s.append w))]
  refine Finset.sum_congr rfl fun w _ => ?_
  have he : (e (s.append w) : KLRAlgebra k Q (X + (Y + Z))) =
      castKLR Q (add_assoc X Y Z) (e (Seq.cast (add_assoc X Y Z).symm (s.append w))) := by
    rw [castKLR_e, Seq.cast_cast_symm]
  rw [he, ← map_mul, oneConcat, eSum_mul_e]
  by_cases hw : w ∈ concatSet Y Z
  · rw [ite_eq_left ((Seq.cast_append_mem_concatSet_iff s w).2 hw), ite_eq_left hw]
  · rw [ite_eq_right (mt (Seq.cast_append_mem_concatSet_iff s w).1 hw), ite_eq_right hw, map_zero]

/-- `ι_{ν+ν',ν''}(1 ⊗ b) 1_{ν,ν'+ν''} = ι_{ν,ν'+ν''}(1 ⊗ ι_{ν',ν''}(1 ⊗ b))` (after
reassociating). -/
theorem castKLR_concat_one_tmul_mul_oneConcat (b : KLRAlgebra k Q Z) :
    castKLR Q (add_assoc X Y Z) (concat Q (X + Y) Z (1 ⊗ₜ b)) * oneConcat Q X (Y + Z) =
      concat Q X (Y + Z) (1 ⊗ₜ concat Q Y Z (1 ⊗ₜ b)) := by
  rw [← concat_mul_oneConcat (1 ⊗ₜ b), map_mul, mul_assoc, castKLR_oneConcat_mul_oneConcat,
    ← castKLR_concatL_one, ← map_mul, concatL_one_eq, ← concat_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, ← concat_one_tmul_one,
    concat_assoc]

theorem castAlg_eq_castKLR {μ μ' : Multiset I} (h : μ = μ') (a : KLRAlgebra k Q μ) :
    castAlg Q h a = castKLR Q h a := by
  subst h; rfl

end KLRAlgebra

namespace KLRAlgebra

local notation "Si" i:max => (Singleton.singleton i : Multiset I)

/-! ### The terms of `Ind_{ν,ν'} N` lying in the image of `Φ` -/

section ImageTerms

variable {ν ν₀' : Multiset I} {i : I}
variable {N : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N]
  [IsScalarTower k (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N]

theorem castKLR_appendR_mul_oneConcat (y : KLRAlgebra k Q (ν + ν₀')) :
    castKLR Q (add_assoc ν ν₀' (Si i)) (appendR Q (ν + ν₀') i y) * oneConcat Q ν (ν₀' + Si i) =
      castKLR Q (add_assoc ν ν₀' (Si i)) (appendR Q (ν + ν₀') i (y * oneConcat Q ν ν₀')) := by
  have hy : appendR Q (ν + ν₀') i y = appendR Q (ν + ν₀') i y * appendR Q (ν + ν₀') i 1 := by
    rw [← map_mul, mul_one]
  have hK := castKLR_concat_one_tmul_mul_oneConcat (Q := Q) (X := ν) (Y := ν₀') (Z := Si i)
    (1 : KLRAlgebra k Q (Si i))
  rw [← Algebra.TensorProduct.one_def, concat_one, ← Algebra.TensorProduct.one_def,
    concat_one] at hK
  rw [hy, appendR_one, map_mul, mul_assoc, hK, map_mul, map_mul,
    ← concat_one (Q := Q) (ν := ν) (ν' := ν₀'), castKLR_appendR_concat, tensorAppendR_one]

/-- A term `ι(y ⊗ 1_i) ι_{ν,ν'}(T) ⊗ n` of `Ind_{ν,ν'} N` lies in the image of `Φ`. -/
theorem tmul_castKLR_appendR_mul_concat_mem_range (y : KLRAlgebra k Q (ν + ν₀'))
    (T : TensorKLR Q ν (ν₀' + Si i)) (n : N)
    (hm : castKLR Q (add_assoc ν ν₀' (Si i)) (appendR Q (ν + ν₀') i y) *
      concat Q ν (ν₀' + Si i) T ∈ Graded.leftIdeal (oneConcat Q ν (ν₀' + Si i))) :
    (BalancedTensor.tmul (⟨_, hm⟩ : IndBimod Q ν (ν₀' + Si i)) n : Ind Q ν (ν₀' + Si i) N) ∈
      LinearMap.range (indAppend (Q := Q) (ν := ν) (ν₀' := ν₀') (i := i) (N := N)) := by
  have hr : y * oneConcat Q ν ν₀' ∈ Graded.leftIdeal (oneConcat Q ν ν₀') := by
    rw [Graded.mem_leftIdeal, mul_assoc, oneConcat_idem.eq]
  have h1 : (⟨_, hm⟩ : IndBimod Q ν (ν₀' + Si i)) =
      op T • indAppendBimod (i := i) (⟨_, hr⟩ : IndBimod Q ν ν₀') := Subtype.ext (by
    rw [coe_op_smul, unop_op, coe_indAppendBimod, ← castKLR_appendR_mul_oneConcat, mul_assoc,
      oneConcat_mul_concat])
  have h2 : ∀ m : N, (BalancedTensor.tmul (indAppendBimod (i := i) (⟨_, hr⟩ : IndBimod Q ν ν₀'))
      (tensorAppendR Q ν ν₀' i 1 • m) : Ind Q ν (ν₀' + Si i) N) =
      BalancedTensor.tmul (indAppendBimod (i := i) (⟨_, hr⟩ : IndBimod Q ν ν₀')) m := by
    intro m
    rw [← BalancedTensor.op_smul_tmul, ← indAppendBimod_op_smul, op_one, one_smul]
  rw [h1, BalancedTensor.op_smul_tmul, ← h2]
  refine ⟨BalancedTensor.tmul (⟨_, hr⟩ : IndBimod Q ν ν₀')
    (InductionAlong.Res.mk (tensorAppendR Q ν ν₀' i 1 • T • n) ?_), ?_⟩
  · change tensorAppendR Q ν ν₀' i 1 • tensorAppendR Q ν ν₀' i 1 • T • n = _
    rw [smul_smul, ← map_mul, one_mul]
  · rw [indAppend_tmul, InductionAlong.Res.val_mk]

end ImageTerms

/-! ### The Mackey datum of the last strand -/

section LastQuad

variable (ν₀ ν₀' : Multiset I) (i : I)

omit [DecidableEq I] in
theorem lastQuad_h₁ : ν₀ + (ν₀' + Si i) = ν₀ + Si i + ν₀' := by
  rw [← add_assoc, add_right_comm]

/-- The Mackey datum `(α, β, γ, δ) = (ν₀, ν', i, 0)` for restricting `Ind_{ν,ν'}` to
`R(ν + ν₀') ⊗ R(i)`, `ν = ν₀ + i`, `ν' = ν₀' + i`: the last strand at the top comes from the
`ν`-block at the bottom and crosses the whole `ν'`-block. -/
abbrev lastQuad : MackeyQuad (ν₀ + Si i + ν₀') (Si i) (ν₀ + Si i) (ν₀' + Si i) where
  α := ν₀
  β := ν₀' + Si i
  γ := Si i
  δ := 0
  h₁ := lastQuad_h₁ ν₀ ν₀' i
  h₂ := add_zero _
  h₃ := rfl
  h₄ := add_zero _

variable (Q) in
/-- `a ⊗ b ↦ ι(a ⊗ 1_i) ⊗ b`, `R(ν₀) ⊗ R(ν') → R(ν₀ + i) ⊗ R(ν')`. -/
noncomputable def tensorAppendL (ν₀ ν' : Multiset I) (i : I) :
    TensorKLR Q ν₀ ν' →ₙₐ[k] TensorKLR Q (ν₀ + Si i) ν' where
  toFun := TensorProduct.map (appendRLin Q ν₀ i) LinearMap.id
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' s t := by
    induction s using TensorProduct.inductionOn with
    | add s s' hs hs' => simp only [add_mul, map_add, hs, hs']
    | tmul a b =>
      induction t using TensorProduct.inductionOn with
      | add t t' ht ht' => simp only [mul_add, map_add, ht, ht']
      | tmul a' b' =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul,
          LinearMap.id_apply, appendRLin_apply, map_mul]

theorem tensorAppendL_tmul {ν' : Multiset I} (a : KLRAlgebra k Q ν₀) (b : KLRAlgebra k Q ν') :
    tensorAppendL Q ν₀ ν' i (a ⊗ₜ b) = appendR Q ν₀ i a ⊗ₜ b := rfl

theorem tensorAppendL_one {ν' : Multiset I} :
    tensorAppendL Q ν₀ ν' i 1 = oneConcat Q ν₀ (Si i) ⊗ₜ 1 := by
  rw [Algebra.TensorProduct.one_def, tensorAppendL_tmul, appendR_one]

variable {ν₀ ν₀' i}

theorem quadTop_lastQuad (t : TensorKLR Q ν₀ (ν₀' + Si i)) :
    quadTop (lastQuad ν₀ ν₀' i) (t ⊗ₜ 1) =
      castKLR Q (lastQuad_h₁ ν₀ ν₀' i) (concat Q ν₀ (ν₀' + Si i) t) ⊗ₜ 1 := by
  rw [Algebra.TensorProduct.one_def (A := KLRAlgebra k Q (Si i))]
  change TensorProduct.map _ _ _ = _
  rw [TensorProduct.map_tmul]
  change castAlg Q _ _ ⊗ₜ castAlg Q (add_zero _) (concat Q (Si i) 0 (1 ⊗ₜ 1)) = _
  rw [castAlg_eq_castKLR, castAlg_eq_castKLR, concat_one_right]

theorem quadBot_lastQuad (t : TensorKLR Q ν₀ (ν₀' + Si i)) :
    quadBot (lastQuad ν₀ ν₀' i) (t ⊗ₜ 1) = tensorAppendL Q ν₀ (ν₀' + Si i) i t := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => rw [TensorProduct.add_tmul, map_add, map_add, hs, ht]
  | tmul a b =>
    rw [Algebra.TensorProduct.one_def (A := KLRAlgebra k Q (Si i)), quadBot_tmul,
      tensorAppendL_tmul, appendR_apply]
    change castAlg Q rfl _ ⊗ₜ castAlg Q (add_zero _) (concat Q (ν₀' + Si i) 0 (b ⊗ₜ 1)) = _
    rw [castAlg_eq_castKLR, castAlg_eq_castKLR, castKLR_rfl, concat_one_right]

omit [DecidableEq I] in
variable (ν₀ ν₀' i) in
theorem lastQuad_h : ν₀ + Si i + (ν₀' + Si i) = ν₀ + Si i + ν₀' + Si i :=
  (add_assoc _ _ _).symm

variable (Q ν₀ ν₀' i) in
/-- The crossing `ψ_d` of the last-strand Mackey datum. -/
noncomputable def lastψ : KLRAlgebra k Q (ν₀ + Si i + ν₀' + Si i) :=
  ψw (canWord (Multiset.card (ν₀ + Si i + ν₀' + Si i))
    (quadPerm (lastQuad_h ν₀ ν₀' i) (lastQuad ν₀ ν₀' i)))

/-- The intertwining property of `ψ_d` for the last strand: moving `ι(t)` (`t` on the bottom
blocks `ν₀`, `ν'`) through `ψ_d` produces the bottom action of `ι(ι(t₁ ⊗ 1_i) ⊗ t₂)` plus a term of
the lower Mackey step. -/
theorem appendR_castKLR_mul_concat (r : KLRAlgebra k Q (ν₀ + (ν₀' + Si i)))
    (t : TensorKLR Q ν₀ (ν₀' + Si i)) :
    appendR Q _ i (castKLR Q (lastQuad_h₁ ν₀ ν₀' i) (r * concat Q ν₀ (ν₀' + Si i) t)) * lastψ Q ν₀ ν₀' i =
      appendR Q _ i (castKLR Q (lastQuad_h₁ ν₀ ν₀' i) r) *
          quadDefect (lastQuad_h ν₀ ν₀' i) (lastQuad ν₀ ν₀' i) (t ⊗ₜ 1) +
        appendR Q _ i (castKLR Q (lastQuad_h₁ ν₀ ν₀' i) r) * lastψ Q ν₀ ν₀' i *
          botConcat Q (lastQuad_h ν₀ ν₀' i)
            (tensorAppendL Q ν₀ (ν₀' + Si i) i t) := by
  rw [quadDefect_apply, quadTop_lastQuad, quadBot_lastQuad, map_mul, map_mul, ← appendR_apply]
  unfold lastψ
  rw [mul_sub, ← mul_assoc, ← mul_assoc, sub_add_cancel]

end LastQuad

/-! ### The lower Mackey step lies in the image of `Φ` -/

section LowerStep

variable {ν₀ ν₀' : Multiset I} {i : I}
variable {N : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N]
  [IsScalarTower k (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N]

variable (Q ν₀ ν₀' i) in
/-- `z ↦ z 1_{ν,ν'}`, `R(ν + ν₀' + i) → R(ν + ν') 1_{ν,ν'}`, reassociating. -/
noncomputable def lastElt :
    KLRAlgebra k Q (ν₀ + Si i + ν₀' + Si i) →ₗ[k] IndBimod Q (ν₀ + Si i) (ν₀' + Si i) where
  toFun z := ⟨castKLR Q (add_assoc (ν₀ + Si i) ν₀' (Si i)) z * oneConcat Q _ _, by
    rw [Graded.mem_leftIdeal, mul_assoc, oneConcat_idem.eq]⟩
  map_add' z z' := Subtype.ext (by simp [add_mul])
  map_smul' c z := Subtype.ext (by simp)

theorem coe_lastElt (z : KLRAlgebra k Q (ν₀ + Si i + ν₀' + Si i)) :
    (lastElt Q ν₀ ν₀' i z : KLRAlgebra k Q (ν₀ + Si i + (ν₀' + Si i))) =
      castKLR Q (add_assoc (ν₀ + Si i) ν₀' (Si i)) z * oneConcat Q _ _ := rfl

theorem castKLR_botConcat_lastQuad_h (t : TensorKLR Q (ν₀ + Si i) (ν₀' + Si i)) :
    castKLR Q (add_assoc (ν₀ + Si i) ν₀' (Si i)) (botConcat Q (lastQuad_h ν₀ ν₀' i) t) =
      concat Q (ν₀ + Si i) (ν₀' + Si i) t := by
  rw [botConcat_apply, castAlg_eq_castKLR]
  exact castKLR_castAlg_symm _ _

theorem castKLR_botOne_lastQuad_h :
    castKLR Q (add_assoc (ν₀ + Si i) ν₀' (Si i)) (botOne Q (lastQuad_h ν₀ ν₀' i)) =
      oneConcat Q (ν₀ + Si i) (ν₀' + Si i) := by
  rw [← botConcat_one, castKLR_botConcat_lastQuad_h, concat_one]

/-- The generators of the Mackey step with fewer than `|ν'|` crossings lie in the image
of `Φ`. -/
theorem tmul_lastElt_mem_range_of_mem_filt (x : KLRAlgebra k Q (ν₀ + Si i + ν₀')) (n : N)
    {w : KLRAlgebra k Q (ν₀ + Si i + ν₀' + Si i)}
    (hw : w ∈ mackeyBimodFilt Q (lastQuad_h ν₀ ν₀' i) (Multiset.card ν₀')) :
    (BalancedTensor.tmul (lastElt Q ν₀ ν₀' i (appendR Q _ i x * w)) n :
        Ind Q (ν₀ + Si i) (ν₀' + Si i) N) ∈
      LinearMap.range (indAppend (Q := Q) (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i) (N := N)) := by
  rw [mackeyBimodFilt_eq_span_crossings (lastQuad_h ν₀ ν₀' i) (canWord _)
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩)] at hw
  induction hw using Submodule.span_induction with
  | zero => rw [mul_zero, map_zero, BalancedTensor.zero_tmul]; exact zero_mem _
  | add w w' _ _ hw hw' =>
    rw [mul_add, map_add, BalancedTensor.add_tmul]; exact add_mem hw hw'
  | smul c w _ hw =>
    rw [mul_smul_comm, map_smul, BalancedTensor.smul_tmul]; exact Submodule.smul_mem _ c hw
  | mem w hw =>
    obtain ⟨d, t₁, t', hd, hdc, rfl⟩ := hw
    have hc : Multiset.card (ν₀' + Si i) = Multiset.card ν₀' + 1 := by simp
    have h1 : d = 1 := IsDoubleShuffle.eq_one_of_crossCount_lt (Seq.card_add' _ _)
      (by simp) (card_add_bot (lastQuad_h ν₀ ν₀' i)) hd (by omega)
    subst h1
    rw [canWord_one, ψw_nil, mul_one]
    induction t₁ using TensorProduct.inductionOn with
    | add s s' hs hs' => rw [map_add, add_mul, mul_add, map_add, BalancedTensor.add_tmul]
                         exact add_mem hs hs'
    | tmul a u =>
      have hm : castKLR Q (add_assoc (ν₀ + Si i) ν₀' (Si i)) (appendR Q _ i (x * a)) *
          concat Q (ν₀ + Si i) (ν₀' + Si i)
            ((1 ⊗ₜ concat Q ν₀' (Si i) (1 ⊗ₜ u)) * t') ∈
          Graded.leftIdeal (oneConcat Q (ν₀ + Si i) (ν₀' + Si i)) := by
        rw [Graded.mem_leftIdeal, mul_assoc, concat_mul_oneConcat]
      have heq : lastElt Q ν₀ ν₀' i (appendR Q _ i x *
          (concat Q (ν₀ + Si i + ν₀') (Si i) (a ⊗ₜ u) * botConcat Q (lastQuad_h ν₀ ν₀' i) t')) =
          ⟨_, hm⟩ := Subtype.ext (by
        have hsplit : appendR Q _ i x * concat Q (ν₀ + Si i + ν₀') (Si i) (a ⊗ₜ u) =
            appendR Q _ i (x * a) * concat Q (ν₀ + Si i + ν₀') (Si i) (1 ⊗ₜ u) := by
          rw [appendR_apply, appendR_apply, ← concat_mul, ← concat_mul,
            Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
        have hK := castKLR_concat_one_tmul_mul_oneConcat (Q := Q) (X := ν₀ + Si i) (Y := ν₀')
          (Z := Si i) u
        rw [coe_lastElt, ← mul_assoc, hsplit, map_mul, map_mul, castKLR_botConcat_lastQuad_h,
          mul_assoc, mul_assoc, concat_mul_oneConcat, ← oneConcat_mul_concat t',
          ← mul_assoc (castKLR Q _ (concat Q _ _ _)) (oneConcat Q _ _), hK, ← concat_mul])
      rw [heq]
      exact tmul_castKLR_appendR_mul_concat_mem_range _ _ _ hm

/-- **The lower Mackey step lies in the image of `Φ`.** -/
theorem tmul_lastElt_mem_range (x : KLRAlgebra k Q (ν₀ + Si i + ν₀')) (n : N)
    {D : KLRAlgebra k Q (ν₀ + Si i + ν₀' + Si i)}
    (hD : D ∈ mackeyLower k Q (ν₀ + Si i + ν₀' + Si i) (Multiset.card (ν₀ + Si i + ν₀'))
      (Multiset.card (ν₀ + Si i)) (Multiset.card (ν₀' + Si i))) :
    (BalancedTensor.tmul (lastElt Q ν₀ ν₀' i (appendR Q _ i x * D)) n :
        Ind Q (ν₀ + Si i) (ν₀' + Si i) N) ∈
      LinearMap.range (indAppend (Q := Q) (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i) (N := N)) := by
  set z := oneConcat Q (ν₀ + Si i + ν₀') (Si i) * D * botOne Q (lastQuad_h ν₀ ν₀' i)
  have hc : Multiset.card (ν₀' + Si i) = Multiset.card ν₀' + 1 := by simp
  have hz : z ∈ mackeyBimodFilt Q (lastQuad_h ν₀ ν₀' i) (Multiset.card ν₀') := by
    rw [← mackeyLowerBimod_succ]
    refine ⟨(mem_bimod _).2 ?_, ?_⟩
    · simp only [z, ← mul_assoc, oneConcat_idem.eq]
      rw [mul_assoc _ (botOne Q _), (botOne_idem _).eq]
    · have h1 := mackeyLower_concat_mul 1 hD
      have h2 := mackeyLower_mul_botConcat (lastQuad_h ν₀ ν₀' i) 1 h1
      rw [concat_one, botConcat_one, hc] at h2
      exact h2
  have heq : lastElt Q ν₀ ν₀' i (appendR Q _ i x * D) =
      lastElt Q ν₀ ν₀' i (appendR Q _ i x * z) := Subtype.ext (by
    have hy : appendR Q (ν₀ + Si i + ν₀') i x =
        appendR Q _ i x * oneConcat Q (ν₀ + Si i + ν₀') (Si i) := by
      rw [← appendR_one, ← map_mul, mul_one]
    rw [coe_lastElt, coe_lastElt, ← mul_assoc, ← mul_assoc, ← hy, map_mul _ _ (botOne Q _),
      castKLR_botOne_lastQuad_h, mul_assoc, oneConcat_idem.eq])
  rw [heq]
  exact tmul_lastElt_mem_range_of_mem_filt x n hz

end LowerStep

/-! ### The map `Ψ : Ind_{ν₀,ν'} ₁N → Ind_{ν,ν'} N / Φ(Ind_{ν,ν₀'} ₂N)` -/

section Quot

variable (Q) (ν₀ ν₀' : Multiset I) (i : I)

/-- `tensorAppendL` as a nonunital ring map. -/
noncomputable abbrev tensorAppendLHom :
    TensorKLR Q ν₀ (ν₀' + Si i) →ₙ+* TensorKLR Q (ν₀ + Si i) (ν₀' + Si i) :=
  NonUnitalRingHomClass.toNonUnitalRingHom (tensorAppendL Q ν₀ (ν₀' + Si i) i)

/-- **`₁N = (1_{ν₀,i} ⊗ 1) N`**, an `R(ν₀) ⊗ R(ν')`-module through `tensorAppendL`. -/
abbrev ResAppendL (N : Type*) [AddCommGroup N]
    [Module (TensorKLR Q (ν₀ + Si i) (ν₀' + Si i)) N] : Type _ :=
  InductionAlong.Res (tensorAppendLHom Q ν₀ ν₀' i) N

variable {Q ν₀ ν₀' i}
variable {N : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N]
  [IsScalarTower k (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N]

noncomputable instance : Module k (ResAppendL Q ν₀ ν₀' i N) :=
  Module.compHom _ (algebraMap k (TensorKLR Q ν₀ (ν₀' + Si i)))

instance : IsScalarTower k (TensorKLR Q ν₀ (ν₀' + Si i)) (ResAppendL Q ν₀ ν₀' i N) where
  smul_assoc c t n := by
    change (c • t) • n = (algebraMap k (TensorKLR Q ν₀ (ν₀' + Si i)) c) • (t • n)
    rw [Algebra.smul_def, mul_smul]

theorem ResAppendL.val_smul_k (c : k) (n : ResAppendL Q ν₀ ν₀' i N) : (c • n).val = c • n.val := by
  change tensorAppendL Q ν₀ (ν₀' + Si i) i (algebraMap k _ c) • n.val = c • n.val
  rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_assoc]
  exact congrArg (c • ·) n.prop

theorem lastElt_mul_botConcat (Y : KLRAlgebra k Q (ν₀ + Si i + ν₀' + Si i))
    (T : TensorKLR Q (ν₀ + Si i) (ν₀' + Si i)) :
    lastElt Q ν₀ ν₀' i (Y * botConcat Q (lastQuad_h ν₀ ν₀' i) T) =
      op T • lastElt Q ν₀ ν₀' i Y := Subtype.ext (by
  rw [coe_op_smul, unop_op, coe_lastElt, coe_lastElt, map_mul, castKLR_botConcat_lastQuad_h,
    mul_assoc, concat_mul_oneConcat, mul_assoc, oneConcat_mul_concat])

variable (Q ν₀ ν₀' i) in
/-- The bimodule part of `Ψ`: `r ↦ ι(r ⊗ 1_i) ψ_d 1_{ν,ν'}`. -/
noncomputable def lastBimod : IndBimod Q ν₀ (ν₀' + Si i) →ₗ[k] IndBimod Q (ν₀ + Si i) (ν₀' + Si i) where
  toFun r := lastElt Q ν₀ ν₀' i
    (appendR Q _ i (castKLR Q (lastQuad_h₁ ν₀ ν₀' i) (r : KLRAlgebra k Q (ν₀ + (ν₀' + Si i)))) *
      lastψ Q ν₀ ν₀' i)
  map_add' r r' := by rw [Submodule.coe_add, map_add, map_add, add_mul, map_add]
  map_smul' c r := by
    change lastElt Q ν₀ ν₀' i (appendR Q _ i (castKLR Q (lastQuad_h₁ ν₀ ν₀' i)
      (c • (r : KLRAlgebra k Q (ν₀ + (ν₀' + Si i))))) * lastψ Q ν₀ ν₀' i) = c • _
    rw [map_smul, map_smul, smul_mul_assoc, map_smul]

theorem lastBimod_apply (r : IndBimod Q ν₀ (ν₀' + Si i)) :
    lastBimod Q ν₀ ν₀' i r = lastElt Q ν₀ ν₀' i
      (appendR Q _ i (castKLR Q (lastQuad_h₁ ν₀ ν₀' i) (r : KLRAlgebra k Q (ν₀ + (ν₀' + Si i)))) *
        lastψ Q ν₀ ν₀' i) := rfl

/-- `Ψ` on the bimodule is balanced up to the image of `Φ`. -/
theorem tmul_lastBimod_op_smul_sub_mem (r : IndBimod Q ν₀ (ν₀' + Si i))
    (t : TensorKLR Q ν₀ (ν₀' + Si i)) (n : N) :
    (BalancedTensor.tmul (lastBimod Q ν₀ ν₀' i (op t • r)) n -
        BalancedTensor.tmul (lastBimod Q ν₀ ν₀' i r) (tensorAppendL Q ν₀ (ν₀' + Si i) i t • n) :
        Ind Q (ν₀ + Si i) (ν₀' + Si i) N) ∈
      LinearMap.range (indAppend (Q := Q) (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i) (N := N)) := by
  rw [lastBimod_apply, coe_op_smul, unop_op, appendR_castKLR_mul_concat, map_add,
    lastElt_mul_botConcat, BalancedTensor.add_tmul, BalancedTensor.op_smul_tmul, ← lastBimod_apply,
    add_sub_cancel_right]
  exact tmul_lastElt_mem_range _ n (quad_intertwine (lastQuad_h ν₀ ν₀' i) (lastQuad ν₀ ν₀' i) _)

/-- The bilinear map `(r, n) ↦ [ι(r ⊗ 1_i) ψ_d ⊗ n]`. -/
noncomputable def lastBil :
    IndBimod Q ν₀ (ν₀' + Si i) →ₗ[k] ResAppendL Q ν₀ ν₀' i N →ₗ[k]
      (Ind Q (ν₀ + Si i) (ν₀' + Si i) N ⧸
        LinearMap.range (indAppend (Q := Q) (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i) (N := N))) :=
  LinearMap.mk₂ k (fun r n => Submodule.Quotient.mk (BalancedTensor.tmul (lastBimod Q ν₀ ν₀' i r) n.val))
    (fun r r' n => by rw [map_add, BalancedTensor.add_tmul, Submodule.Quotient.mk_add])
    (fun c r n => by rw [map_smul, BalancedTensor.smul_tmul, Submodule.Quotient.mk_smul])
    (fun r n n' => by
      rw [InductionAlong.Res.val_add, BalancedTensor.tmul_add, Submodule.Quotient.mk_add])
    (fun c r n => by
      rw [ResAppendL.val_smul_k, BalancedTensor.tmul_smul, Submodule.Quotient.mk_smul])

/-- **The map `Ψ : Ind_{ν₀,ν'} ₁N → Ind_{ν,ν'} N / Φ(Ind_{ν,ν₀'} ₂N)`**,
`r ⊗ n ↦ [ι(r ⊗ 1_i) ψ_d ⊗ n]`. -/
noncomputable def indLast :
    Ind Q ν₀ (ν₀' + Si i) (ResAppendL Q ν₀ ν₀' i N) →ₗ[k]
      (Ind Q (ν₀ + Si i) (ν₀' + Si i) N ⧸
        LinearMap.range (indAppend (Q := Q) (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i) (N := N))) :=
  BalancedTensor.lift lastBil (fun r t n => by
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    exact tmul_lastBimod_op_smul_sub_mem r t n.val)

theorem indLast_tmul (r : IndBimod Q ν₀ (ν₀' + Si i)) (n : ResAppendL Q ν₀ ν₀' i N) :
    indLast (BalancedTensor.tmul r n) =
      Submodule.Quotient.mk (BalancedTensor.tmul (lastBimod Q ν₀ ν₀' i r) n.val) := rfl

end Quot

end KLRAlgebra

end Categorification.KLR
