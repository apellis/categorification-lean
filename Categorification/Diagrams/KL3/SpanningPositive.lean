/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.NondegPositive
import Categorification.Diagrams.KL3.FinDimHomUp

/-!
# KL III Proposition 3.11 for positive sequences

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.3,
Proposition 3.11 (TeX l. 4568: "For any intermediate choices made, `B_{𝐢,𝐣,λ}` spans
`HOM_U(E_𝐢 1_λ, E_𝐣 1_λ)`"), for **positive** sequences `𝐢`, `𝐣` (simply-laced Cartan data).

## The family `B_{𝐢,𝐣,λ}` for positive sequences

Let `𝐢 = i`, `𝐣 = j ∈ Seq(ν)` (positive sequences with the same letters). An element of the index
set `SpanIdx (posW i) (posW j)` of `B_{𝐢,𝐣,λ}` (`Categorification.Diagrams.KL3.GdimBound`) is a
pairing `σ` of the boundary word `ρW(+i) (+j) = (-i)^{rev} (+j)`, a number of dots on each strand
of `σ` and a bubble monomial `m ∈ Π_λ`. For positive sequences:

* the pairing `σ` joins every lower endpoint to an upper endpoint; it is encoded by the
  permutation `w = posW_perm σ` with `w • i = j`: **the strand starting at the lower endpoint `a`
  ends at the upper endpoint `w a`** (in the boundary word, the lower endpoint `a` sits at
  position `n - 1 - a` and the upper endpoint `x` at position `n + x`);
* the dots are a function `u : Fin n →₀ ℕ` on the lower endpoints (`posW_dots`);
* the minimal diagram of `σ` with these dots is `ψ_{ρ w} x^u 1_i`, `ρ w = TypeA.canWord w` the
  standard reduced word (`ρc`): dots at the bottom of the strands, then the crossings of `ρ w`.

So the element of `B_{𝐢,𝐣,λ}` indexed by `x = (σ, dots, m)` is (`posB`)

`posB x = (i, j)-entry of ϕ_{ν,λ}(ψ_{ρ w} x^u 1_i ⊗ m)`,

`ϕ_{ν,λ} = phi : R(ν) ⊗ Π_λ → END_U(E_ν 1_λ)` of KL III Proposition 3.10.

## Main results

* `posB_mem`: `posB x` is homogeneous of degree `spanDeg x` (the degree of the minimal diagram of
  `σ` computed by KL III's rules, `QuantumGroup.UDot.pdeg`, equals `deg ψ_{ρ w} 1_i`:
  `pdeg_posW`);
* **`prop_3_11_positive`**: for every degree `d`, the elements `posB x` with `spanDeg x = d`
  span `HOM_U(E_i 1_λ, E_j 1_λ)_d` (by Proposition 3.10, `prop310_of_simplyLaced`, and the KL II
  basis theorem);
* `isSpanFamily_posB`, **`cor_3_13_positive`** (Corollary 3.13 for positive sequences),
  **`finrank_eq_iff_linearIndependent_posB`** (eq. (3.68)): the dimension of the degree-`d` part
  is the coefficient of `q^d` in `π ⟨E_i 1_λ, E_j 1_λ⟩` iff the `posB x`, `spanDeg x = d`, are
  linearly independent;
* **`positiveNondeg_iff`**: `PositiveNondeg RD k` (the hypothesis of KL III Theorem 1.2 reduced to
  positive sequences, `Categorification.Diagrams.KL3.NondegPositive`) holds iff for all `λ`, all
  `i, j ∈ Seq(ν)` and all `d`, the family `posB` in degree `d` is linearly independent;
* `gammaUA'_bijective_of_linearIndependent`: hence `γ` is bijective as soon as `B_{+i,+j,λ}` is
  linearly independent for all positive `i, j` (and Proposition 2.5 holds).

Note that `IsSpanFamily`/`Prop311` of `Categorification.Diagrams.KL3.GdimBound` only ask for
*some* graded family indexed by `B_{𝐢,𝐣,λ}`; such a family exists iff the dimension bound of
Corollary 3.13 holds (pad a homogeneous basis with zeros). The statement here is the faithful one:
the spanning family is the explicit family of dotted minimal diagrams with bubbles.
-/

noncomputable section

namespace Categorification.QuantumGroup.UDot

open Equiv

variable {I : Type*} (C : CartanDatum I)

/-! ## Transport of pairings along `Fin.cast` -/

theorem permCongr_finCongr_refl {N : ℕ} (σ : Perm (Fin N)) :
    (finCongr (rfl : N = N)).permCongr σ = σ := by
  ext z; simp [Equiv.permCongr_apply]

theorem isMatching_permCongr {N M : ℕ} (h : N = M) {L : Fin N → Bool × I} {B : Fin M → Bool × I}
    (hLB : ∀ z, L (Fin.cast h.symm z) = B z) (σ : Perm (Fin N)) :
    IsMatching B ((finCongr h).permCongr σ) ↔ IsMatching L σ := by
  subst h
  have : L = B := funext fun z => by simpa using hLB z
  subst this
  rw [permCongr_finCongr_refl]

theorem mdeg_permCongr {N M : ℕ} (h : N = M) {L : Fin N → Bool × I} {B : Fin M → Bool × I}
    (hLB : ∀ z, L (Fin.cast h.symm z) = B z) (ℓ : I → ℤ) (σ : Perm (Fin N)) :
    mdeg C ℓ B ((finCongr h).permCongr σ) = mdeg C ℓ L σ := by
  subst h
  have : L = B := funext fun z => by simpa using hLB z
  subst this
  rw [permCongr_finCongr_refl]

theorem permCongr_finCongr_apply {N M : ℕ} (h : N = M) (σ : Perm (Fin N)) (z : Fin N) :
    (finCongr h).permCongr σ (Fin.cast h z) = Fin.cast h (σ z) := by
  simp [Equiv.permCongr_apply]

/-- For positive sequences with the same letters, the bending exponent is `-κ`:
`rcx (⟨-, λ + b_X⟩) (+c) = -(Σ_j (j·j)/2 ⟨j, λ⟩ + (ν·ν)/2)`. -/
theorem rcx_posW_balanced (ℓ : I → ℤ) {c b : List I} (h : (c : Multiset I) = b) :
    rcx C (wl C ℓ (posW b)) (posW c) = -Kx C ℓ (c : Multiset I) := by
  have h1 := rcx_posW C (wl C ℓ (posW b)) c
  have hw : wl C ℓ (posW b) = fun k => ℓ k + msA C k (b : Multiset I) := by
    funext k; rw [wl, aS_posW]
  rw [hw, S1_add_msA, ← h] at h1
  have h2 := two_mul_hsq C (c : Multiset I)
  rw [Kx, hw, ← h]
  linarith

/-- `invWt` of the inverse permutation: the inversions of `w⁻¹` on `i ∘ w⁻¹` are those of `w`
on `i`. -/
theorem invWt_inv {m : ℕ} (a : Fin m → I) (w : Perm (Fin m)) :
    PreF.invWt C.dot (fun x => a (w⁻¹ x)) w⁻¹ =
      ∑ p ∈ TypeA.invSet m w, C.dot (a p.1) (a p.2) := by
  rw [PreF.invWt]
  refine Finset.sum_nbij' (fun p => (w⁻¹ p.2, w⁻¹ p.1)) (fun p => (w p.2, w p.1))
    (fun p hp => ?_) (fun p hp => ?_) (fun p _ => by simp) (fun p _ => by simp) (fun p _ => rfl)
  · rw [TypeA.mem_invSet] at hp ⊢
    simp only [Perm.apply_inv_self]
    exact ⟨hp.2, hp.1⟩
  · rw [TypeA.mem_invSet] at hp ⊢
    simp only [Perm.inv_apply_self, inv_inv]
    exact ⟨hp.2, hp.1⟩

end Categorification.QuantumGroup.UDot

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation KLR.Diagram MatEnd Equiv Module
open scoped TensorProduct

universe w u v

/-! ## Pairings of two positive sequences -/

section Pairings

variable {I : Type u} {ν : Multiset I} (i j : KLR.Seq ν)

/-- The boundary word `ρW(+i) (+j)` of `(+i, +j)`-pairings. -/
abbrev bw : List (Bool × I) := ρW (posW (word i)) ++ posW (word j)

theorem bw_length : (bw i j).length = Multiset.card ν + Multiset.card ν := by
  simp [bw, ρW, posW, word]

theorem bw_get (z : Fin (Multiset.card ν + Multiset.card ν)) :
    (bw i j).get (Fin.cast (bw_length i j).symm z) =
      blockWord (fun k => i.lbl k.rev) j.lbl z := by
  have hi : (ρW (posW (word i))).length = Multiset.card ν := by simp [ρW, posW, word]
  refine Fin.addCases (fun k => ?_) (fun x => ?_) z
  · rw [blockWord_left]
    simp only [List.get_eq_getElem, Fin.coe_cast, Fin.coe_castAdd]
    rw [List.getElem_append_left (by rw [hi]; exact k.isLt)]
    simp only [ρW_posW, negW, word, List.getElem_map, List.getElem_reverse, List.getElem_ofFn]
    refine Prod.ext rfl ?_
    show i.1 _ = i.1 _
    exact congrArg i.1 (Fin.ext (by simp [Fin.rev]; omega))
  · rw [blockWord_right]
    simp only [List.get_eq_getElem, Fin.coe_cast, Fin.coe_natAdd]
    rw [List.getElem_append_right (by rw [hi]; omega)]
    simp only [posW, word, List.getElem_map, List.getElem_ofFn, hi]
    refine Prod.ext rfl ?_
    show j.1 _ = j.1 _
    exact congrArg j.1 (Fin.ext (by simp [ρW, posW]))

variable {i j}

/-- The transport of permutations of the boundary positions to `Fin (n + n)`. -/
abbrev bwE : Perm (Fin (bw i j).length) ≃ Perm (Fin (Multiset.card ν + Multiset.card ν)) :=
  (finCongr (bw_length i j)).permCongr

/-- Pairings of the boundary word of `(+i, +j)`. -/
abbrev PosPairing (i j : KLR.Seq ν) : Type _ :=
  {σ // σ ∈ pairings (posW (word i)) (posW (word j))}

theorem isMatching_bwE (σ : Perm (Fin (bw i j).length)) :
    IsMatching (blockWord (fun k => i.lbl k.rev) j.lbl) (bwE σ) ↔
      IsMatching (fun p : Fin (bw i j).length => (bw i j).get p) σ :=
  isMatching_permCongr (bw_length i j) (bw_get i j) σ

theorem exists_perm_of_pairing (σ : PosPairing i j) :
    ∃ w' : Perm (Fin (Multiset.card ν)), (∀ x, i.lbl (w' x) = j.lbl x) ∧ blockPerm w' = bwE σ.1 := by
  obtain ⟨w', hw, he⟩ := exists_blockPerm ((isMatching_bwE σ.1).2 (mem_matchings.1 σ.2))
  exact ⟨w', fun x => by simpa using hw x, he⟩

/-- **The permutation of a pairing of `(+i, +j)`**: the strand starting at the lower endpoint `a`
ends at the upper endpoint `posPerm σ a`. -/
def posPerm (σ : PosPairing i j) : Perm (Fin (Multiset.card ν)) :=
  (Classical.choose (exists_perm_of_pairing σ))⁻¹

theorem blockPerm_posPerm (σ : PosPairing i j) : blockPerm (posPerm σ)⁻¹ = bwE σ.1 := by
  rw [posPerm, inv_inv]; exact (Classical.choose_spec (exists_perm_of_pairing σ)).2

theorem posPerm_smul (σ : PosPairing i j) : posPerm σ • i = j := by
  apply Subtype.ext; funext x
  have := (Classical.choose_spec (exists_perm_of_pairing σ)).1 x
  simp only [KLR.Seq.smul_apply, posPerm, inv_inv]
  exact this

theorem bwE_apply (σ : Perm (Fin (bw i j).length)) (z : Fin (Multiset.card ν + Multiset.card ν)) :
    σ (Fin.cast (bw_length i j).symm z) = Fin.cast (bw_length i j).symm (bwE σ z) := by
  simp [Equiv.permCongr_apply]

/-- The strand of `σ` starting at the lower endpoint `a` (in the boundary word: the cup whose left
endpoint is at position `n - 1 - a`). -/
def posArc (σ : PosPairing i j) (a : Fin (Multiset.card ν)) :
    Arc (posW (word i)) (posW (word j)) σ.1 :=
  ⟨Fin.cast (bw_length i j).symm (Fin.castAdd _ a.rev), by
    rw [bwE_apply, ← blockPerm_posPerm, blockPerm_left, Fin.lt_iff_val_lt_val, Fin.coe_cast,
      Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd]
    omega⟩

theorem posArc_bijective (σ : PosPairing i j) : Function.Bijective (posArc σ) := by
  constructor
  · intro a b h
    have := congrArg (fun x : Arc (posW (word i)) (posW (word j)) σ.1 => x.1.val) h
    simp only [posArc, Fin.coe_cast, Fin.coe_castAdd] at this
    exact Fin.rev_injective (Fin.ext this)
  · rintro ⟨p, hp⟩
    obtain ⟨z, rfl⟩ : ∃ z, p = Fin.cast (bw_length i j).symm z :=
      ⟨Fin.cast (bw_length i j) p, by simp⟩
    rw [bwE_apply, ← blockPerm_posPerm] at hp
    have key : ∃ k, z = Fin.castAdd _ k := by
      revert hp
      refine Fin.addCases (fun k => ?_) (fun x => ?_) z
      · intro _; exact ⟨k, rfl⟩
      · intro hp
        rw [blockPerm_right, Fin.lt_iff_val_lt_val, Fin.coe_cast, Fin.coe_cast, Fin.coe_castAdd,
          Fin.coe_natAdd] at hp
        omega
    obtain ⟨k, rfl⟩ := key
    exact ⟨k.rev, Subtype.ext (by simp [posArc, Fin.rev_rev])⟩

/-- The strands of a pairing of `(+i, +j)` are indexed by the lower endpoints. -/
def posArcEquiv (σ : PosPairing i j) :
    Fin (Multiset.card ν) ≃ Arc (posW (word i)) (posW (word j)) σ.1 :=
  Equiv.ofBijective _ (posArc_bijective σ)

theorem arcCol_posArc (σ : PosPairing i j) (a : Fin (Multiset.card ν)) :
    arcCol (posArc σ a) = i.lbl a := by
  have := bw_get i j (Fin.castAdd _ a.rev)
  rw [blockWord_left, Fin.rev_rev] at this
  simp only [arcCol, posArc]
  rw [this]

end Pairings

/-! ## The degree of the minimal diagram of a pairing of positive sequences -/

section Degree

variable {I : Type u} (C : CartanDatum I) {ν : Multiset I} {i j : KLR.Seq ν}

theorem coe_word (i : KLR.Seq ν) : ((word i : List I) : Multiset I) = ν := by
  rw [word, ← Fin.univ_val_map]; exact i.2

theorem coe_ofFn_rev (i : KLR.Seq ν) :
    ((List.ofFn fun k => i.lbl k.rev : List I) : Multiset I) = ν := by
  rw [← Fin.univ_val_map]
  have e : (fun k : Fin (Multiset.card ν) => i.lbl k.rev) = i.1 ∘ Fin.revPerm := rfl
  rw [e, ← Multiset.map_map, Multiset.map_univ_val_equiv]
  exact i.2

/-- **The degree of the minimal diagram of a pairing of positive sequences** (KL III §2.2) is
`deg ψ_{ρ w} 1_i = -Σ_{(a, b) ∈ inv(w)} i_a · i_b`, `w = posPerm σ`. -/
theorem pdeg_posW (ℓ : I → ℤ) (σ : PosPairing i j) :
    pdeg C ℓ (posW (word i)) (posW (word j)) σ.1 =
      -∑ p ∈ TypeA.invSet (Multiset.card ν) (posPerm σ), C.dot (i.lbl p.1) (i.lbl p.2) := by
  set w' := (posPerm σ)⁻¹
  have hw : ∀ x, (fun k => i.lbl k.rev) (Fin.rev (w' x)) = j.lbl x := fun x => by
    show i.1 _ = j.1 x
    have := congrArg (fun s : KLR.Seq ν => s.1 x) (posPerm_smul σ)
    simp only [KLR.Seq.smul_apply] at this
    simp only [Fin.rev_rev, w']
    rw [← this]; rfl
  rw [pdeg, bendDeg_eq_rcx, rcx_posW_balanced C ℓ ((coe_word i).trans (coe_word j).symm),
    ← mdeg_permCongr C (bw_length i j) (bw_get i j), ← blockPerm_posPerm,
    mdeg_blockPerm C hw ℓ, block_exponent C ℓ (fun k => i.lbl k.rev) j.lbl w' hw, coe_word,
    coe_ofFn_rev]
  have hj : j.lbl = fun x => i.lbl (w' x) := funext fun x => (hw x).symm.trans (by simp)
  rw [hj, show w' = (posPerm σ)⁻¹ from rfl, invWt_inv]
  ring

end Degree

/-! ## The family `B_{𝐢,𝐣,λ}` for positive sequences -/

section Family

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k] [DecidableEq I] {ν : Multiset I}
  {i j : KLR.Seq ν}

/-- The dots of an element of `B_{+i,+j,λ}`, as a function on the lower endpoints. -/
def posDots (x : SpanIdx (posW (word i)) (posW (word j))) : Fin (Multiset.card ν) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun a => x.2.1 (posArc x.1 a)

variable (C) in
/-- The KLR degree of the standard element, plus the bubble degree. -/
abbrev stdDegB (p : (KLR.Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) ×
    ((I × ℕ) →₀ ℕ)) : ℤ :=
  (KLR.klGradingDatum2 k C).stdDeg (ρc ν) p.1 + Finsupp.weight (wPi C) p.2

variable (RD k) in
/-- **The element of `B_{+i,+j,λ}` indexed by `x = (σ, dots, m)`**: the `(i, j)`-entry of
`ϕ_{ν,λ}(ψ_{ρ w} x^u 1_i ⊗ m)`, `w = posPerm σ`, `u = posDots x` (KL III §3.2.3: the minimal
diagram of `σ` — the standard reduced word of `w` — with the dots at the bottom of the strands and
the bubble monomial `m` on the right). -/
def posB (μ : X) (x : SpanIdx (posW (word i)) (posW (word j))) :
    (pres RD k).obj (ob RD μ (posW (word i))) ⟶ (pres RD k).obj (ob RD μ (posW (word j))) :=
  phi RD k μ ν (KLR.KL2.basis (k := k) (C := C) (ν := ν) (ρc ν) (hρc ν) (i, posPerm x.1, posDots x)
    ⊗ₜ MvPolynomial.monomial x.2.2 1) i j

omit [DecidableEq I] in
theorem weight_eq_sum (u : Fin (Multiset.card ν) →₀ ℕ) (f : Fin (Multiset.card ν) → ℤ) :
    Finsupp.weight f u = ∑ a, (u a : ℤ) * f a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun a => by simp)]
  simp [nsmul_eq_mul]

omit [DecidableEq I] in
variable (k) in
/-- **The degree of `posB x` is `spanDeg x`**: KL III's degree of the dotted minimal diagram with
its bubble monomial equals the degree of `ψ_{ρ w} x^u 1_i ⊗ m`. -/
theorem spanDeg_eq (ℓ : I → ℤ) (x : SpanIdx (posW (word i)) (posW (word j))) :
    spanDeg C ℓ x = stdDegB C (k := k) ((i, posPerm x.1, posDots x), x.2.2) := by
  simp only [spanDeg, stdDegB, KLR.GradingDatum.stdDeg]
  rw [pdeg_posW C ℓ x.1, KLR.KL2.degW_eq2 (hρc ν (posPerm x.1)).1, (hρc ν (posPerm x.1)).2,
    weight_eq_sum]
  congr 2
  rw [← Equiv.sum_comp (posArcEquiv x.1)]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [posArcEquiv, Equiv.ofBijective_apply, posDots, Finsupp.equivFunOnFinite_symm_apply_toFun,
    arcCol_posArc]
  rfl

end Family

/-! ## Spanning -/

section Span

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k] [DecidableEq I] {ν : Multiset I}

variable (RD k) in
/-- The `(i, j)`-entries of the images under `ϕ_{ν,λ}` of the tensor products of the KL II basis
of `R(ν)` with the bubble monomials. -/
abbrev vB (μ : X) (i j : KLR.Seq ν)
    (p : (KLR.Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) ×
      ((I × ℕ) →₀ ℕ)) :
    (pres RD k).obj (ob RD μ (ups (word i))) ⟶ (pres RD k).obj (ob RD μ (ups (word j))) :=
  phi RD k μ ν (KLR.KL2.basis (k := k) (C := C) (ν := ν) (ρc ν) (hρc ν) p.1 ⊗ₜ
    MvPolynomial.monomial p.2 1) i j

theorem vB_mem (μ : X) (i j : KLR.Seq ν) (p) :
    vB RD k μ i j p ∈ HomD RD k μ (ups (word i)) (ups (word j)) (stdDegB C (k := k) p) := by
  obtain ⟨b, m⟩ := p
  have hb : toUEnd RD k μ ν (KLR.KL2.basis (k := k) (C := C) (ν := ν) (ρc ν) (hρc ν) b) ∈
      matDeg RD k μ ν ((KLR.klGradingDatum2 k C).stdDeg (ρc ν) b) :=
    toUEnd_mem ((KLR.klGradingDatum2 k C).basis_mem_grade _ _ (ρc ν) (hρc ν) b)
  have hm : bubDiag RD k μ ν (bubMap RD k μ (MvPolynomial.monomial m 1)) ∈
      matDeg RD k μ ν (Finsupp.weight (wPi C) m) := by
    rw [bubDiag_apply]
    exact Submodule.sum_mem _ fun l _ => single_mem_matDeg (bubAt_mem μ _ (bubMon_mem μ m))
  have h := mul_mem_matDeg hb hm i j
  rw [vB, phi_tmul]
  exact h

/-- The entries of `ϕ_{ν,λ}(r ⊗ q)`. -/
theorem phi_tmul_apply (μ : X) (r : KLR.R2 k C ν) (q : PiLam I k) (i j : KLR.Seq ν) :
    phi RD k μ ν (r ⊗ₜ q) i j = bubAt RD k μ (ups (word i)) (bubMap RD k μ q).val ≫
      upEnt RD k μ r i j := by
  rw [phi_tmul, MatEnd.mul_apply, Finset.sum_eq_single i]
  · congr 1
    rw [bubDiag_apply, MatEnd.sum_apply, Finset.sum_eq_single i]
    · rw [MatEnd.single_apply_self]
    · intro l _ hl
      rw [MatEnd.single_apply_of_ne _ (fun h => hl h.1.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro l _ hl
    rw [bubDiag_apply, MatEnd.sum_apply, Finset.sum_eq_zero, Limits.zero_comp]
    intro l' _
    rw [MatEnd.single_apply_of_ne _ (fun h => hl (h.2.trans h.1.symm))]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Field k] in
theorem upEnt_eq_zero_right [Field k] (μ : X) {z : KLR.R2 k C ν} {s : KLR.Seq ν}
    (hz : z * KLR.KLRAlgebra.e s = z) (s' j : KLR.Seq ν) (hs : s' ≠ s) :
    upEnt RD k μ z s' j = 0 := by
  rw [upEnt, ← hz, map_mul, toUEnd_e, MatEnd.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [MatEnd.single_apply_of_ne _ (fun h => hs h.1), Limits.zero_comp]

/-- `vB p = 0` unless `p` is a basis element of the corner `1_j R(ν) 1_i`. -/
theorem vB_eq_zero (μ : X) (i j : KLR.Seq ν) (p)
    (hp : ¬ (p.1.1 = i ∧ p.1.2.1 • i = j)) : vB RD k μ i j p = 0 := by
  obtain ⟨⟨i', w, u⟩, m⟩ := p
  set r := KLR.KL2.basis (k := k) (C := C) (ν := ν) (ρc ν) (hρc ν) (i', w, u)
  have hr : KLR.KLRAlgebra.e (w • i') * r * KLR.KLRAlgebra.e i' = r := by
    have := KLR.KLRAlgebra.cornerElt_mem (k := k) (Q := KLR.klQ2 k C) (ρc ν) (hρc ν) (w • i') i'
      (⟨w, rfl⟩, u)
    rw [KLR.KLRAlgebra.mem_corner_iff] at this
    simpa [r, KLR.KL2.basis_apply, KLR.KLRAlgebra.cornerElt, KLR.KLRAlgebra.stdElt] using this
  have hl : KLR.KLRAlgebra.e (w • i') * r = r := by
    conv_lhs => rw [← hr]
    rw [← mul_assoc, ← mul_assoc, KLR.KLRAlgebra.e_mul_self, hr]
  have hrt : r * KLR.KLRAlgebra.e i' = r := by
    conv_lhs => rw [← hr]
    rw [mul_assoc, KLR.KLRAlgebra.e_mul_self, hr]
  rw [vB, phi_tmul_apply]
  by_cases hi : i' = i
  · subst hi
    have hj : j ≠ w • i' := fun h => hp ⟨rfl, h.symm⟩
    rw [upEnt_eq_zero (RD := RD) (k := k) (μ := μ) hl i' j hj, Limits.comp_zero]
  · rw [upEnt_eq_zero_right μ hrt i j (Ne.symm hi), Limits.comp_zero]

omit [DecidableEq I] in
theorem posPerm_eq (σ : PosPairing i j) (w : Perm (Fin (Multiset.card ν)))
    (h : blockPerm w⁻¹ = bwE σ.1) : posPerm σ = w := by
  have := blockPerm_posPerm σ
  rw [← h] at this
  exact inv_injective (blockPerm_injective this)

omit [DecidableEq I] in
/-- Every basis element `ψ_{ρ w} x^u 1_i` of `1_j R(ν) 1_i` (`w • i = j`) with a bubble monomial
comes from an element of `B_{+i,+j,λ}`. -/
theorem exists_spanIdx (w : Perm (Fin (Multiset.card ν))) (hw : w • i = j)
    (u : Fin (Multiset.card ν) →₀ ℕ) (m : (I × ℕ) →₀ ℕ) :
    ∃ x : SpanIdx (posW (word i)) (posW (word j)), posPerm x.1 = w ∧ posDots x = u ∧ x.2.2 = m := by
  have hw' : ∀ x, (fun k => i.lbl k.rev) (Fin.rev (w⁻¹ x)) = j.lbl x := fun x => by
    show i.1 _ = j.1 x
    rw [Fin.rev_rev, ← hw]; rfl
  have hmatch : IsMatching (fun p : Fin (bw i j).length => (bw i j).get p)
      (bwE.symm (blockPerm w⁻¹)) :=
    (isMatching_bwE _).1 (by rw [Equiv.apply_symm_apply]; exact isMatching_blockPerm hw')
  let σ : PosPairing i j := ⟨bwE.symm (blockPerm w⁻¹), mem_matchings.2 hmatch⟩
  have hσ : posPerm σ = w := posPerm_eq σ w (by
    show blockPerm w⁻¹ = bwE (bwE.symm (blockPerm w⁻¹))
    rw [Equiv.apply_symm_apply])
  refine ⟨⟨σ, fun a => u ((posArcEquiv σ).symm a), m⟩, hσ, ?_, rfl⟩
  ext a
  simp only [posDots, Finsupp.equivFunOnFinite_symm_apply_toFun]
  have : posArc σ a = posArcEquiv σ a := rfl
  rw [this, Equiv.symm_apply_apply]

variable (RD k) in
/-- **Proposition 3.10 on the corner**: `HOM_U(E_i 1_λ, E_j 1_λ)` is spanned by the `vB p`
(simply-laced, `I` finite). -/
theorem mem_span_vB [Finite I] (hSL : SimplyLaced C) (μ : X) (i j : KLR.Seq ν)
    (f : (pres RD k).obj (ob RD μ (ups (word i))) ⟶ (pres RD k).obj (ob RD μ (ups (word j)))) :
    f ∈ Submodule.span k (Set.range (vB RD k μ i j)) := by
  classical
  let bR := KLR.KL2.basis (k := k) (C := C) (ν := ν) (ρc ν) (hρc ν)
  let bT := bR.tensorProduct (MvPolynomial.basisMonomials (I × ℕ) k)
  let ev : MatEnd (objNu RD k μ ν) →ₗ[k]
      ((pres RD k).obj (ob RD μ (ups (word i))) ⟶ (pres RD k).obj (ob RD μ (ups (word j)))) :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let L := ev ∘ₗ (phi RD k μ ν).toLinearMap
  have hv : ∀ p, vB RD k μ i j p = L (bT p) := fun p => by
    simp only [L, bT, ev, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [Basis.tensorProduct_apply, MvPolynomial.coe_basisMonomials]
  obtain ⟨t, ht⟩ := prop310_of_simplyLaced (k := k) (RD := RD) hSL μ ν (single i j f)
  have hf : f = L t := by
    simp only [L, ev, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [ht, single_apply_self]
  have hL : L t ∈ LinearMap.range L := ⟨t, rfl⟩
  rw [LinearMap.range_eq_map, ← bT.span_eq, Submodule.map_span, ← Set.range_comp] at hL
  rw [hf]
  convert hL using 3
  funext p
  exact hv p

/-- **Khovanov–Lauda III, Proposition 3.11 for positive sequences** (TeX l. 4568; simply-laced,
`I` finite, `𝕜` a field): for `i, j ∈ Seq(ν)`, a weight `λ` and every degree `d`, the elements
`posB x` of `B_{+i,+j,λ}` of degree `spanDeg x = d` span `HOM_U(E_{+i} 1_λ, E_{+j} 1_λ)_d`. -/
theorem prop_3_11_positive [Finite I] (hSL : SimplyLaced C) (μ : X) (i j : KLR.Seq ν) (d : ℤ) :
    Submodule.span k (Set.range fun x : {x : SpanIdx (posW (word i)) (posW (word j)) //
        spanDeg C (RD.ellOf μ) x = d} => posB RD k μ x.1) =
      HomD RD k μ (posW (word i)) (posW (word j)) d := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have h := vB_mem (RD := RD) (k := k) μ i j ((i, posPerm x.1, posDots x), x.2.2)
    rw [← spanDeg_eq k (RD.ellOf μ) x, hx] at h
    exact h
  · intro f hf
    have h1 := mem_span_vB RD k hSL μ i j f
    have h2 := mem_span_image_of_homogeneous (pres_isHomogeneous (RD := RD) (k := k))
      (vB RD k μ i j) (stdDegB C (k := k)) (vB_mem μ i j) h1 hf
    rw [← Submodule.span_insert_zero]
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨p, hp, rfl⟩
    by_cases h : p.1.1 = i ∧ p.1.2.1 • i = j
    · obtain ⟨⟨i', w, u⟩, m⟩ := p
      obtain ⟨rfl, hw⟩ := h
      obtain ⟨x, hx1, hx2, hx3⟩ := exists_spanIdx w hw u m
      refine Set.mem_insert_of_mem _ ⟨⟨x, ?_⟩, ?_⟩
      · rw [spanDeg_eq k (RD.ellOf μ) x, hx1, hx2, hx3]; exact hp
      · simp only [posB, hx1, hx2, hx3]
    · rw [vB_eq_zero (RD := RD) (k := k) μ i j p h]
      exact Set.mem_insert _ _

end Span

/-! ## Consequences: Corollary 3.13, eq. (3.68) and nondegeneracy for positive sequences -/

section Consequences

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k] [DecidableEq I] [Finite I]
  (hSL : SimplyLaced C)

include hSL in
/-- **`B_{+i,+j,λ}` is a graded spanning family** (`IsSpanFamily`) of
`HOM_U(E_{+i} 1_λ, E_{+j} 1_λ)`. -/
theorem isSpanFamily_posB {ν : Multiset I} (μ : X) (i j : KLR.Seq ν) :
    IsSpanFamily RD k μ (posW (word i)) (posW (word j)) (posB RD k μ) := by
  refine ⟨fun x => ?_, fun d => prop_3_11_positive hSL μ i j d⟩
  have h := vB_mem (RD := RD) (k := k) μ i j ((i, posPerm x.1, posDots x), x.2.2)
  rw [← spanDeg_eq k (RD.ellOf μ) x] at h
  exact h

omit [DecidableEq I] in
/-- The dimension bound given by any graded spanning family indexed by `B_{𝐢,𝐣,λ}`. -/
theorem finrank_le_of_isSpanFamily {μ : X} {s t : List (Letter I)}
    {b : SpanIdx s t → ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t))}
    (hb : IsSpanFamily RD k μ s t b) (d : ℤ) :
    ((finrank k (HomD RD k μ s t d) : ℤ) : ℚ) ≤
      (piLS C * toLS (UDot.KL3.sform RD (E1 RD vQ s μ) (E1 RD vQ t μ))).coeff d := by
  haveI := (prop_3_12 (s := s) (t := t) RD μ d).1
  haveI := Fintype.ofFinite {x : SpanIdx s t // spanDeg C (RD.ellOf μ) x = d}
  rw [← card_fiber_eq μ s t d]
  exact_mod_cast (finrank_le_and_iff _ _ (hb.2 d)).1

include hSL in
/-- **Khovanov–Lauda III, Corollary 3.13 for positive sequences**:
`gdim HOM_U(E_{+i} 1_λ, E_{+j} 1_λ) ≤ π ⟨E_{+i} 1_λ, E_{+j} 1_λ⟩`, coefficientwise. -/
theorem cor_3_13_positive {ν : Multiset I} (μ : X) (i j : KLR.Seq ν) (d : ℤ) :
    ((finrank k (HomD RD k μ (posW (word i)) (posW (word j)) d) : ℤ) : ℚ) ≤
      (piLS C * toLS (UDot.KL3.sform RD (E1 RD vQ (posW (word i)) μ)
        (E1 RD vQ (posW (word j)) μ))).coeff d :=
  finrank_le_of_isSpanFamily (isSpanFamily_posB hSL μ i j) d

include hSL in
/-- **KL III eq. (3.68) for positive sequences**: the dimension of
`HOM_U(E_{+i} 1_λ, E_{+j} 1_λ)_d` equals the coefficient of `q^d` in
`π ⟨E_{+i} 1_λ, E_{+j} 1_λ⟩` iff the elements `posB x` of `B_{+i,+j,λ}` of degree `d` are linearly
independent. -/
theorem finrank_eq_iff_linearIndependent_posB {ν : Multiset I} (μ : X) (i j : KLR.Seq ν)
    (d : ℤ) :
    ((finrank k (HomD RD k μ (posW (word i)) (posW (word j)) d) : ℤ) : ℚ) =
        (piLS C * toLS (UDot.KL3.sform RD (E1 RD vQ (posW (word i)) μ)
          (E1 RD vQ (posW (word j)) μ))).coeff d ↔
      LinearIndependent k fun x : {x : SpanIdx (posW (word i)) (posW (word j)) //
        spanDeg C (RD.ellOf μ) x = d} => posB RD k μ x.1 :=
  finrank_eq_iff_linearIndependent μ _ _ (isSpanFamily_posB hSL μ i j) d

omit [DecidableEq I] [Finite I] in
/-- `⟨E_{+c} 1_λ, E_{+b} 1_λ⟩ = 0` if `c` and `b` do not have the same letters. -/
theorem sform_posW_eq_zero (μ : X) {c b : List I} (h : (c : Multiset I) ≠ b) :
    UDot.KL3.sform RD (E1 RD vQ (posW c) μ) (E1 RD vQ (posW b) μ) = 0 := by
  rw [← (UDot.KL3.thm_2_7 C RD _ _ μ μ).1, UDot.KL3.form, formUD_E1_E1, if_pos rfl]
  have e : ∀ l : List I, (ew (posW l) : UDot.Free (RatFunc ℚ) I) =
      posF (PreF.word (FreeMonoid.ofList l)) := fun l => by rw [posF_word]; rfl
  rw [e, e, B_posF_posF, fF, PreF.form_eq_zero_of_wt_ne]
  simpa [QuantumGroup.wt] using h

include hSL in
/-- **Nondegeneracy for positive sequences is the linear independence of `B`**: `PositiveNondeg`
(the hypothesis of `gammaUA'_bijective_of_positive`, KL III Theorem 1.2 reduced to positive
sequences) holds iff for every `λ`, all `i, j ∈ Seq(ν)` and every degree `d`, the elements of
`B_{+i,+j,λ}` of degree `d` are linearly independent. -/
theorem positiveNondeg_iff :
    PositiveNondeg RD k ↔ ∀ (μ : X) (ν : Multiset I) (i j : KLR.Seq ν) (d : ℤ),
      LinearIndependent k fun x : {x : SpanIdx (posW (word i)) (posW (word j)) //
        spanDeg C (RD.ellOf μ) x = d} => posB RD k μ x.1 := by
  constructor
  · intro h μ ν i j d
    exact (finrank_eq_iff_linearIndependent_posB hSL μ i j d).1 (h μ (word i) (word j) d)
  · intro h μ c b t
    by_cases hcb : (c : Multiset I) = b
    · have hi := word_seqOfList c
      have hj : word (hcb.symm ▸ seqOfList b : KLR.Seq (c : Multiset I)) = b :=
        (word_cast hcb.symm _).trans (word_seqOfList b)
      have := (finrank_eq_iff_linearIndependent_posB (RD := RD) (k := k) hSL μ (seqOfList c)
        (hcb.symm ▸ seqOfList b) t).2 (h μ _ _ _ t)
      rw [hi, hj] at this
      exact this
    · have hp : ¬ (posW c).Perm (posW b) := fun hp => hcb (Multiset.coe_eq_coe.2 (by
        have := hp.map Prod.snd
        simpa [posW, List.map_map, Function.comp_def] using this))
      rw [homD_eq_bot_of_not_perm hSL μ (by simp [Positive, posW]) (by simp [Positive, posW]) hp t,
        finrank_bot, sform_posW_eq_zero μ hcb, map_zero, mul_zero, HahnSeries.coeff_zero]
      simp

include hSL in
/-- **KL III Theorem 1.2 / Proposition 1.4 from the linear independence of `B` for positive
sequences**: if for all `λ`, `i, j ∈ Seq(ν)`, `d` the elements of `B_{+i,+j,λ}` of degree `d` are
linearly independent, and Proposition 2.5 holds, then
`γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))` is bijective. -/
theorem gammaUA'_bijective_of_linearIndependent
    (hli : ∀ (μ : X) (ν : Multiset I) (i j : KLR.Seq ν) (d : ℤ),
      LinearIndependent k fun x : {x : SpanIdx (posW (word i)) (posW (word j)) //
        spanDeg C (RD.ellOf μ) x = d} => posB RD k μ x.1)
    (h25 : UDot.KL3.FormNondeg RD) (lam ρ : X) :
    Function.Bijective (gammaUA' (RD := RD) (k := k) hSL lam ρ) :=
  gammaUA'_bijective_of_positive hSL ((positiveNondeg_iff hSL).2 hli) h25 lam ρ

end Consequences

end Categorification.KL3.Diagram
