/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Twisted.Realize
import Categorification.WeightedKLR.Twisted.Blocks

/-!
# Flips of galleries in the arrangement of positions and weights

Spanning half of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Proposition 2.20 (the basis of the algebra of galleries of the arrangement of
positions and weights; its proof is that of Theorem 2.8). A flip of a word reverses the block of
hyperplanes through a flat of codimension two. In this arrangement a block has two independent
hyperplanes (a square) or three of the shapes `TwTriple` (a hexagon): three diagonals on the
pairs of three strands, or a diagonal `d` with a wall `W` and the wall `W.comap d.refl` (the loop
block when `W` joins the two strands of `d`). No hypothesis on the graph is needed. The defining
relations of the twisted gallery algebra show that a flip changes the gallery by an element with
fewer steps.

## Main results

* `TwGalleryAlgebra.galList_twHexagon_block`: a hexagon of one of the shapes `TwTriple`.
* `TwGalleryAlgebra.galList_block`: reversing a block changes the gallery by an element of
  `stepFilt (length - 2)`.
* `TwGalleryAlgebra.galList_flip`, `TwGalleryAlgebra.galList_reflTransGen`: the same for a
  flip, and for a chain of flips, of a good word.
-/

namespace Categorification.WeightedKLR

open Segment TwChamber

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Relabelling twice by the transposition of the strands of a diagonal is the identity. -/
theorem Hyp.comap_refl_comap_refl (d : Diag ν) (h : Hyp Γ ν) :
    (h.comap d.refl).comap d.refl = h := by
  rw [← Hyp.comap_mul, Diag.refl_mul_refl, Hyp.comap_one]

namespace TwChamber

/-- Across a diagonal `d`, a chamber has the same sign on a wall and on its image under the
transposition of the strands of `d`. -/
theorem Adjacent.inl_eq_comap_refl {C C' : TwChamber Γ ν} {d : Diag ν}
    (hC : C.Adjacent C' (.inr d)) (W : Wall Γ ν) :
    C.1 (.inl W) = C.1 (.inl (W.comap d.refl)) := by
  rw [hC.2 _ Sum.inl_ne_inr, ← hC.refl_smul]
  rfl

end TwChamber

namespace TwGalleryAlgebra

/-- If the middle hyperplane of a hexagon is a diagonal `d` exchanging the outer two, the end
chamber is the reflection of the start chamber. -/
theorem twHexagon_refl_smul (H : TwHexagon Γ ν) {d : Diag ν} (e₂ : H.h₂ = .inr d)
    (hc : H.h₃.comap d.refl = H.h₁) : d.refl • H.A₀ = H.A₃ := by
  have a := H.adj₀₁.smul d.refl
  have hi : d.refl⁻¹ = d.refl := inv_eq_of_mul_eq_one_right (Diag.refl_mul_refl d)
  rw [hi, ← hc, Hyp.comap_refl_comap_refl] at a
  have hr : d.refl • H.A₁ = H.A₂ := Adjacent.refl_smul (by rw [← e₂]; exact H.adj₁₂)
  rw [hr] at a
  exact a.symm.eq_of_adjacent H.adj₂₃

/-- Reversing three hyperplanes of one of the shapes `TwTriple` changes the gallery by an
element of at most one step. -/
theorem galList_twHexagon_block (H : TwHexagon Γ ν) (ht : TwTriple H.h₁ H.h₂ H.h₃) :
    galList k H.A₀ [H.h₁, H.h₂, H.h₃] - galList k H.A₀ [H.h₃, H.h₂, H.h₁] ∈
      stepFilt k Γ ν 1 := by
  rcases ht with ⟨d₁, d₂, d₃, e₁, e₂, e₃, u, v, w, p₁, p₂, p₃⟩ | ⟨d, W, e₁, e₂, e₃⟩ |
    ⟨d, W, e₁, e₂, e₃⟩ | ⟨d, W, e₁, e₂, e₃⟩
  · -- three diagonals
    have pd : Hyp.IsPair (Sum.inr d₂ : Hyp Γ ν) w u := e₂ ▸ p₂.symm
    have key := Hyp.comap_refl_isPair pd p₃.ne p₁.ne.symm p₃.symm
    rw [e₃] at key
    rw [e₁] at p₁
    have hc : H.h₃.comap d₂.refl = H.h₁ := by
      rw [e₃, e₁]
      exact congrArg Sum.inr (Diag.eq_of_isPair (Γ := Γ) key p₁)
    exact galList_hex_diags H d₁ d₂ d₃ u v w e₁ e₂ e₃ p₁
      (by rw [e₂] at p₂; exact p₂) (by rw [e₃] at p₃; exact p₃)
      (twHexagon_refl_smul H e₂ hc)
  · -- the diagonal crossed first
    have hσ := (show H.A₀.Adjacent H.A₁ (.inr d) from e₁ ▸ H.adj₀₁).inl_eq_comap_refl W
    rw [galList_hex_end_diag H W d e₂ (.inl ⟨e₁, e₃⟩) hσ, sub_self]
    exact Submodule.zero_mem _
  · -- the diagonal crossed in the middle
    have hc : H.h₃.comap d.refl = H.h₁ := by
      rw [e₃, e₁]
      exact Hyp.comap_refl_comap_refl d (.inl W)
    have hA := twHexagon_refl_smul H e₂ hc
    have hσ : H.A₀.1 (.inl W) ≠ H.A₀.1 (.inl (W.comap d.refl)) := by
      have s₃ : H.A₃.1 (.inl W) = H.A₀.1 (.inl (W.comap d.refl)) := by rw [← hA]; rfl
      rw [← s₃, ← e₁, ← H.adj₂₃.2 _ H.ne₁₃, ← H.adj₁₂.2 _ H.ne₁₂]
      exact H.adj₀₁.1
    exact stepFilt_mono (Nat.zero_le 1) (galList_hex_mid_diag H W d e₁ e₂ e₃ hσ hA)
  · -- the diagonal crossed last
    have hW : (W.comap d.refl).comap d.refl = W :=
      Sum.inl_injective (Hyp.comap_refl_comap_refl d (.inl W : Hyp Γ ν))
    have hσ := (show H.A₀.Adjacent H.A₅ (.inr d) from e₃ ▸ H.adj₀₅).inl_eq_comap_refl
      (W.comap d.refl)
    rw [galList_hex_end_diag H (W.comap d.refl) d e₂ (.inr ⟨by rw [hW]; exact e₁, e₃⟩) hσ,
      sub_self]
    exact Submodule.zero_mem _

/-- Reversing a block of hyperplanes through a flat of codimension two, along a word all of
whose prefixes, read either way, are chambers, changes the gallery by an element with fewer
steps. -/
theorem galList_block (E : TwChamber Γ ν) {B : List (Hyp Γ ν)} (hlen : 2 ≤ B.length)
    {x : Strand ν ⊕ Γ.E → 𝕜} (hx : ∀ h : Hyp Γ ν, h.twVal x = 0 ↔ h ∈ B)
    (hB : Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h : Hyp Γ ν => h.twLin) '' {h | h ∈ B})) = 2)
    (hw : TwGoodWord E.1 B) (hw' : TwGoodWord E.1 B.reverse) :
    galList k E B - galList k E B.reverse ∈ stepFilt k Γ ν (B.length - 2) := by
  have hle := twBlock_length_le hB hw.1
  have heq := flips_eq_of_perm hw hw' (List.reverse_perm B).symm
  match B, hlen, hle, hx, hB, hw, hw', heq with
  | [h₁, h₂], _, _, hx, _, hw, hw', heq =>
    have hn : h₁ ≠ h₂ := by simpa using hw.1
    obtain ⟨-, a₁, hw₁⟩ := hw.cons
    obtain ⟨-, a₂, -⟩ := hw₁.cons
    obtain ⟨-, a₃, hw₃⟩ := hw'.cons
    obtain ⟨-, a₄, -⟩ := hw₃.cons
    have hD' : (E.flipH h₂).flipH h₁ = (E.flipH h₁).flipH h₂ := heq.symm
    rw [hD'] at a₄
    have := galList_square (k := k) hn (twIndependent_of_pair hx hn) a₁ a₂ a₃ a₄
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [this, sub_self]
    exact Submodule.zero_mem _
  | [h₁, h₂, h₃], _, _, _, hB, hw, hw', heq =>
    have hn := hw.1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨⟨n₁₂, n₁₃⟩, n₂₃, -⟩ := hn
    obtain ⟨-, a₁, hw₁⟩ := hw.cons
    obtain ⟨-, a₂, hw₂⟩ := hw₁.cons
    obtain ⟨-, a₃, -⟩ := hw₂.cons
    obtain ⟨-, a₅, hw₅⟩ := hw'.cons
    obtain ⟨-, a₄, hw₄⟩ := hw₅.cons
    obtain ⟨-, a₆, -⟩ := hw₄.cons
    have hE : ((E.flipH h₃).flipH h₂).flipH h₁ = ((E.flipH h₁).flipH h₂).flipH h₃ := heq.symm
    rw [hE] at a₆
    let H : TwHexagon Γ ν :=
      { A₀ := E, A₁ := E.flipH h₁, A₂ := (E.flipH h₁).flipH h₂,
        A₃ := ((E.flipH h₁).flipH h₂).flipH h₃, A₄ := (E.flipH h₃).flipH h₂,
        A₅ := E.flipH h₃, h₁ := h₁, h₂ := h₂, h₃ := h₃, ne₁₂ := n₁₂, ne₁₃ := n₁₃,
        ne₂₃ := n₂₃, adj₀₁ := a₁, adj₁₂ := a₂, adj₂₃ := a₃, adj₀₅ := a₅, adj₅₄ := a₄,
        adj₄₃ := a₆ }
    have ht := twTriple_of_finrank hB (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) (by simp) (by simp)
      (by simp) n₁₂ n₁₃ n₂₃
    have := galList_twHexagon_block (k := k) H ht
    simpa using this

theorem stepFilt_sub_mul {m n p : ℕ} {a b c d : TwGalleryAlgebra k Γ ν}
    (ha : a ∈ stepFilt k Γ ν m) (hbc : b - c ∈ stepFilt k Γ ν n) (hd : d ∈ stepFilt k Γ ν p) :
    a * (b * d) - a * (c * d) ∈ stepFilt k Γ ν (m + (n + p)) := by
  rw [← mul_sub, ← sub_mul]
  exact mul_mem_stepFilt ha (mul_mem_stepFilt hbc hd)

/-- A flip of a good word changes the gallery by an element with fewer steps. -/
theorem galList_flip {C : TwChamber Γ ν} {w w' : List (Hyp Γ ν)} (hw : TwGoodWord C.1 w)
    (hf : Flip (twAff (Γ := Γ) (ν := ν)) C.1 w w') :
    galList k C w - galList k C w' ∈ stepFilt k Γ ν (w.length - 2) := by
  have hw' := hw.flip hf
  obtain ⟨a, B, c, rfl, rfl, hlen, ⟨x, hx, -⟩, hB⟩ := hf
  have g₁ : TwGoodWord C.1 (a ++ B) := hw.of_append
  have g₂ : TwGoodWord C.1 (a ++ B.reverse) := hw'.of_append
  have hend : C.flips (a ++ B) = C.flips (a ++ B.reverse) :=
    flips_eq_of_perm g₁ g₂ ((List.reverse_perm B).symm.append_left a)
  have hblock := galList_block (k := k) (C.flips a) hlen (x := x) (fun h => hx h) hB
    g₁.append g₂.append
  rw [galList_append C (a ++ B), galList_append C (a ++ B.reverse), galList_append C a B,
    galList_append C a B.reverse, hend]
  refine stepFilt_mono ?_ (stepFilt_sub_mul (galList_mem_stepFilt _ c) hblock
    (galList_mem_stepFilt C a))
  simp only [List.length_append]
  omega

/-- A chain of flips of a good word changes the gallery by an element with fewer steps. -/
theorem galList_reflTransGen {C : TwChamber Γ ν} {w w' : List (Hyp Γ ν)}
    (hw : TwGoodWord C.1 w)
    (hr : Relation.ReflTransGen (Flip (twAff (Γ := Γ) (ν := ν)) C.1) w w') :
    galList k C w - galList k C w' ∈ stepFilt k Γ ν (w.length - 2) := by
  induction hr with
  | refl => rw [sub_self]; exact Submodule.zero_mem _
  | @tail w₁ w₂ hr hf ih =>
    have hl : w₁.length = w.length := (reflTransGen_flip_perm hr).length_eq.symm
    have := galList_flip (k := k) (hw.reflTransGen hr) hf
    rw [hl] at this
    rw [← sub_add_sub_cancel _ (galList k C w₁)]
    exact Submodule.add_mem _ ih this

end TwGalleryAlgebra

end Categorification.WeightedKLR
