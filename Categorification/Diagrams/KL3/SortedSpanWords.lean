/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SpanningSetElim
import Categorification.TypeA.Matsumoto
import Categorification.TypeA.Parabolic
import Categorification.TypeA.DoubleCoset

/-!
# Diagrams without caps and cups, modulo lower terms

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.3
(reduction of diagrams modulo lower terms: "arbitrary homotopies of colored dotted diagrams
modulo lower order terms") and M. Khovanov, A. Lauda, arXiv:0803.4121v2, §2.3 (the same
argument for `R(ν)`: Matsumoto's theorem and the reduction of non-reduced words).

A diagram built from dots and crossings of adjacent strands (upward, downward or sideways,
`xLay`) is, modulo diagrams with fewer crossings (`Lo`), dots at the bottom followed by the
crossings of a word `ρ` (`xWord`, `pushDots`); braid-equivalent words give the same diagram
modulo lower terms (Reidemeister 3, `xWord_braidEquiv`), and a word with a repeated letter
gives lower terms (Reidemeister 2, `xWord_hasRepeat`). The letters after the crossings of a word
are those of the permutation it represents (`getElem?_lapply`).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## Words of crossings -/

/-- Exchange the letters at positions `p`, `p + 1`. -/
def lswap {α : Type*} : List α → ℕ → List α
  | a :: b :: s, 0 => b :: a :: s
  | a :: s, p + 1 => a :: lswap s p
  | s, _ => s

/-- The crossing of the strands at positions `p`, `p + 1`. -/
def xAt : List (Letter I) → ℕ → List (LayerData I)
  | a :: b :: s, 0 => (xLay a b).map (whL [] s)
  | a :: s, p + 1 => (xAt s p).map (whL [a] [])
  | _, _ => []

/-- The diagram of a word of crossings. -/
def xWord : List (Letter I) → List ℕ → List (LayerData I)
  | _, [] => []
  | s, p :: ρ => xAt s p ++ xWord (lswap s p) ρ

/-- The letters after a word of crossings. -/
def lapply {α : Type*} (s : List α) (ρ : List ℕ) : List α := ρ.foldl lswap s

theorem lswap_mid {α : Type*} (u v : List α) (a b : α) :
    lswap (u ++ [a, b] ++ v) u.length = u ++ [b, a] ++ v := by
  induction u with
  | nil => rfl
  | cons x u ih => simp only [List.cons_append, List.length_cons, lswap] at ih ⊢; rw [ih]

theorem xAt_mid (u v : List (Letter I)) (a b : Letter I) :
    xAt (u ++ [a, b] ++ v) u.length = (xLay a b).map (whL u v) := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    simp only [List.cons_append, List.length_cons, xAt] at ih ⊢
    rw [ih]; wnf

theorem exists_mid {α : Type*} : ∀ {s : List α} {p : ℕ}, p + 1 < s.length →
    ∃ u a b v, s = u ++ [a, b] ++ v ∧ u.length = p
  | a :: b :: s, 0, _ => ⟨[], a, b, s, rfl, rfl⟩
  | a :: s, p + 1, h => by
    obtain ⟨u, c, d, v, rfl, rfl⟩ := exists_mid (s := s) (p := p) (by simp at h; omega)
    exact ⟨a :: u, c, d, v, rfl, rfl⟩
  | [], _, h => by simp at h
  | [a], 0, h => by simp at h

theorem length_lswap {α : Type*} : ∀ (s : List α) (p : ℕ), (lswap s p).length = s.length
  | a :: b :: s, 0 => rfl
  | a :: s, p + 1 => by simp [lswap, length_lswap s p]
  | [], _ => rfl
  | [a], 0 => rfl

theorem sChain_xAt {s : List (Letter I)} {p : ℕ} (h : p + 1 < s.length) :
    SChain s (xAt s p) (lswap s p) := by
  obtain ⟨u, a, b, v, rfl, rfl⟩ := exists_mid h
  rw [xAt_mid, lswap_mid]
  simpa using (sChain_xLay a b).whisk u v

theorem ccnt_xAt {s : List (Letter I)} {p : ℕ} (h : p + 1 < s.length) :
    ccnt (xAt s p) = 1 := by
  obtain ⟨u, a, b, v, rfl, rfl⟩ := exists_mid h
  rw [xAt_mid, ccnt_map_whL, ccnt_xLay]

theorem xAt_ne_nil {s : List (Letter I)} {p : ℕ} (h : p + 1 < s.length) :
    xAt s p ≠ [] := by
  obtain ⟨u, a, b, v, rfl, rfl⟩ := exists_mid h
  rw [xAt_mid]; simp [xLay_ne_nil]

theorem sChain_xWord : ∀ {s : List (Letter I)} {ρ : List ℕ}, TypeA.ValidWord s.length ρ →
    SChain s (xWord s ρ) (lapply s ρ)
  | s, [], _ => rfl
  | s, p :: ρ, h => by
    rw [TypeA.validWord_cons] at h
    exact (sChain_xAt h.1).append (sChain_xWord (by rw [length_lswap]; exact h.2))

theorem ccnt_xWord : ∀ {s : List (Letter I)} {ρ : List ℕ}, TypeA.ValidWord s.length ρ →
    ccnt (xWord s ρ) = ρ.length
  | s, [], _ => rfl
  | s, p :: ρ, h => by
    rw [TypeA.validWord_cons] at h
    rw [xWord, ccnt_append, ccnt_xAt h.1, ccnt_xWord (by rw [length_lswap]; exact h.2)]
    simp [add_comm]

theorem length_lapply {α : Type*} : ∀ (s : List α) (ρ : List ℕ), (lapply s ρ).length = s.length
  | s, [] => rfl
  | s, p :: ρ => by simp only [lapply, List.foldl_cons] at *; rw [← lapply, length_lapply, length_lswap]

theorem xWord_append : ∀ (s : List (Letter I)) (ρ σ : List ℕ),
    xWord s (ρ ++ σ) = xWord s ρ ++ xWord (lapply s ρ) σ
  | s, [], σ => rfl
  | s, p :: ρ, σ => by
    simp only [List.cons_append, xWord, xWord_append (lswap s p) ρ σ, List.append_assoc]
    rfl

theorem lapply_append {α : Type*} (s : List α) (ρ σ : List ℕ) :
    lapply s (ρ ++ σ) = lapply (lapply s ρ) σ := by
  simp [lapply, List.foldl_append]

/-! ## Words of crossings and permutations -/

section Perm

open TypeA Equiv

theorem getElem?_lswap {α : Type*} : ∀ (s : List α) (p : ℕ), p + 1 < s.length → ∀ i : ℕ,
    (lswap s p)[i]? = s[swapNat p i]?
  | a :: b :: s, 0, _, i => by
    rcases i with _ | _ | i <;> simp [lswap, swapNat]
  | a :: s, p + 1, h, i => by
    rcases i with _ | i
    · simp [lswap, swapNat]
    · have := getElem?_lswap s p (by simp at h; omega) i
      simp only [lswap, List.getElem?_cons_succ, this]
      unfold swapNat
      split_ifs <;> simp_all
  | [], _, h, _ => by simp at h
  | [a], 0, h, _ => by simp at h

theorem getElem?_lapply {α : Type*} (m : ℕ) : ∀ (ρ : List ℕ) (s : List α), s.length = m →
    ValidWord m ρ → ∀ i : Fin m, (lapply s ρ)[i.val]? = s[(wordProd m ρ i).val]?
  | [], s, _, _, i => by simp [lapply]
  | p :: ρ, s, hs, hv, i => by
    rw [validWord_cons] at hv
    have ih := getElem?_lapply m ρ (lswap s p) (by rw [length_lswap, hs]) hv.2 i
    simp only [lapply, List.foldl_cons] at ih ⊢
    rw [ih, getElem?_lswap s p (by omega), wordProd_cons, Perm.mul_apply, sadj_val_of_lt hv.1]

theorem lswap_perm {α : Type*} : ∀ (s : List α) (p : ℕ), (lswap s p).Perm s
  | a :: b :: s, 0 => by rw [lswap]; exact List.Perm.swap a b s
  | a :: s, p + 1 => by rw [lswap]; exact (lswap_perm s p).cons a
  | [], _ => List.Perm.refl _
  | [a], 0 => List.Perm.refl _

theorem lapply_perm {α : Type*} : ∀ (s : List α) (ρ : List ℕ), (lapply s ρ).Perm s
  | _, [] => List.Perm.refl _
  | s, p :: ρ => (lapply_perm (lswap s p) ρ).trans (lswap_perm s p)

theorem eq_blockPerm_of_preserves {n n' m : ℕ} (h : n + n' = m) (σ : Perm (Fin m))
    (hσ : ∀ i : Fin m, (σ i).val < n ↔ i.val < n) : ∃ a b, σ = blockPerm h a b := by
  have h0 : ∀ τ : Perm (Fin m), (∀ i : Fin m, (τ i).val < n ↔ i.val < n) →
      crossCount n n τ = 0 := by
    intro τ hτ
    unfold crossCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    have := (hτ p).1 hp.2
    omega
  have e : crossCount n n (1 : Perm (Fin m)) = crossCount n n σ := by
    rw [h0 1 (fun i => Iff.rfl), h0 σ hσ]
  obtain ⟨a, b, y, y', hab⟩ := (crossCount_eq_iff_mem_doubleCoset h h 1 σ).1 e
  exact ⟨a * y, b * y', by rw [hab, mul_one, blockPerm_mul]⟩

end Perm

/-! ## Lower terms -/

variable (RD k) in
/-- Diagrams with fewer than `n` crossings. -/
def Lo (ν : X) (s t : List (Letter I)) (n : ℕ) :
    Submodule k ((pres RD k).obj (ob RD ν s) ⟶ (pres RD k).obj (ob RD ν t)) :=
  Submodule.span k {f | ∃ L, ccnt L < n ∧ f = dg RD k ν s t L}

theorem leL_le_lo {ν : X} {s t : List (Letter I)} {c n : ℕ} (h : c < n) :
    LeL RD k ν s t c ≤ Lo RD k ν s t n :=
  Submodule.span_mono fun _ ⟨L, hL, e⟩ => ⟨L, by omega, e⟩

theorem lo_mono {ν : X} {s t : List (Letter I)} {n n' : ℕ} (h : n ≤ n') :
    Lo RD k ν s t n ≤ Lo RD k ν s t n' :=
  Submodule.span_mono fun _ ⟨L, hL, e⟩ => ⟨L, by omega, e⟩

theorem lo_eq_leL {ν : X} {s t : List (Letter I)} {n : ℕ} :
    Lo RD k ν s t (n + 1) = LeL RD k ν s t n := by
  apply le_antisymm
  · exact Submodule.span_mono fun _ ⟨L, hL, e⟩ => ⟨L, by omega, e⟩
  · exact leL_le_lo (by omega)

theorem dg_comp_lo {ν : X} {s t r : List (Letter I)} {n : ℕ} {g} (M : List (LayerData I))
    (hg : g ∈ Lo RD k ν t r n) : dg RD k ν s t M ≫ g ∈ Lo RD k ν s r (ccnt M + n) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨L, hL, rfl⟩ := hg
    by_cases hA : SChain s M t
    · by_cases hB : SChain t L r
      · rw [dg_comp hA hB]; exact Submodule.subset_span ⟨_, by rw [ccnt_append]; omega, rfl⟩
      · rw [dg_of_not hB, Limits.comp_zero]; exact Submodule.zero_mem _
    · rw [dg_of_not hA, Limits.zero_comp]; exact Submodule.zero_mem _
  | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hx

theorem lo_comp_dg {ν : X} {s t r : List (Letter I)} {n : ℕ} {f}
    (hf : f ∈ Lo RD k ν s t n) (M : List (LayerData I)) :
    f ≫ dg RD k ν t r M ∈ Lo RD k ν s r (n + ccnt M) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    by_cases hA : SChain s L t
    · by_cases hB : SChain t M r
      · rw [dg_comp hA hB]; exact Submodule.subset_span ⟨_, by rw [ccnt_append]; omega, rfl⟩
      · rw [dg_of_not hB, Limits.comp_zero]; exact Submodule.zero_mem _
    · rw [dg_of_not hA, Limits.zero_comp]; exact Submodule.zero_mem _
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

theorem lo_sub_trans {ν : X} {s t : List (Letter I)} {n : ℕ} {a b d}
    (h₁ : a - b ∈ Lo RD k ν s t n) (h₂ : b - d ∈ Lo RD k ν s t n) : a - d ∈ Lo RD k ν s t n := by
  have := Submodule.add_mem _ h₁ h₂; rwa [sub_add_sub_cancel] at this

theorem SChain.tgt_unique : ∀ {s t t' : List (Letter I)} {A : List (LayerData I)},
    SChain s A t → SChain s A t' → t = t'
  | _, _, _, [], h, h' => h.symm.trans h'
  | _, _, _, _ :: _, h, h' => SChain.tgt_unique h.2 h'.2

/-- Splitting a diagram after a chain. -/
theorem dg_append_of_left {ν : X} {s m t : List (Letter I)} {A : List (LayerData I)}
    (hA : SChain s A m) (B : List (LayerData I)) :
    dg RD k ν s t (A ++ B) = dg RD k ν s m A ≫ dg RD k ν m t B := by
  by_cases hB : SChain m B t
  · rw [dg_comp hA hB]
  · rw [dg_of_not hB, Limits.comp_zero, dg_of_not]
    intro h
    obtain ⟨m', h1, h2⟩ := SChain.split h
    exact hB (SChain.tgt_unique h1 hA ▸ h2)

variable [DecidableEq I]

/-- A dot passes a crossing (modulo diagrams without crossings). -/
theorem dotThruX (ν : X) (u v : List (Letter I)) (l₁ l₂ : Letter I) (x : LayerData I)
    (hx : x.2.1.isDot = true) (hxc : SChain (u ++ [l₂, l₁] ++ v) [x] (u ++ [l₂, l₁] ++ v)) :
    ∃ x' : LayerData I, x'.2.1.isDot = true ∧
      SChain (u ++ [l₁, l₂] ++ v) [x'] (u ++ [l₁, l₂] ++ v) ∧
      dg RD k ν (u ++ [l₁, l₂] ++ v) (u ++ [l₂, l₁] ++ v) ((xLay l₁ l₂).map (whL u v) ++ [x]) -
        dg RD k ν (u ++ [l₁, l₂] ++ v) (u ++ [l₂, l₁] ++ v) ([x'] ++ (xLay l₁ l₂).map (whL u v)) ∈
      LeL RD k ν (u ++ [l₁, l₂] ++ v) (u ++ [l₂, l₁] ++ v) 0 := by
  obtain ⟨a, g, b⟩ := x
  cases g with
  | dot l =>
    have h : a ++ [l] ++ b = u ++ [l₂] ++ [] ++ [l₁] ++ v := by simpa using hxc.1.symm
    rcases posDot h with ⟨R, hP, hv⟩ | ⟨hu, hl, hv⟩ | ⟨S₁, S₂, hS, -, -⟩ | ⟨hu, hl, hv⟩ | ⟨R, hQ, ha⟩
    · subst hP hv
      refine ⟨(a, .dot l, R ++ [l₁, l₂] ++ v), rfl, ⟨by simp, by simp⟩, leL_sub_of_eq ?_⟩
      have := dg_ichg (RD := RD) (k := k) (μ := ν) (s₀ := a ++ [l] ++ R ++ [l₁, l₂] ++ v)
        (t₀ := a ++ [l] ++ R ++ [l₂, l₁] ++ v) [] [] a v (A := [([], .dot l, [])]) (s := [l])
        (s' := [l]) ⟨rfl, rfl⟩ ((sChain_xLay l₁ l₂).whisk R [])
      wnf at this ⊢
      exact this.symm
    · subst a l b
      refine ⟨(u ++ [l₁], .dot l₂, v), rfl, ⟨by simp, by simp⟩, ?_⟩
      exact dg_mod_free [] [] u v (ds0 (RD := RD) (k := k) _ l₁ l₂)
        ((sChain_xLay l₁ l₂).append ⟨rfl, rfl⟩)
        (SChain.append (⟨rfl, rfl⟩ : SChain [l₁, l₂] [([l₁], .dot l₂, [])] [l₁, l₂]) (sChain_xLay l₁ l₂))
        (by simp) (by simp) (by wnf) (by wnf) (by simp)
    · have := congrArg List.length hS; simp at this; omega
    · subst a l b
      refine ⟨(u, .dot l₁, [l₂] ++ v), rfl, ⟨by simp, by simp⟩, ?_⟩
      exact dg_mod_free [] [] u v (ds1 (RD := RD) (k := k) _ l₁ l₂)
        ((sChain_xLay l₁ l₂).append ⟨rfl, rfl⟩)
        (SChain.append (⟨rfl, rfl⟩ : SChain [l₁, l₂] [([], .dot l₁, [l₂])] [l₁, l₂]) (sChain_xLay l₁ l₂))
        (by simp) (by simp) (by wnf) (by wnf) (by simp)
    · subst v a
      refine ⟨(u ++ [l₁, l₂] ++ R, .dot l, b), rfl, ⟨by simp, by simp⟩, leL_sub_of_eq ?_⟩
      have := dg_ichg (RD := RD) (k := k) (μ := ν) (s₀ := u ++ [l₁, l₂] ++ (R ++ [l] ++ b))
        (t₀ := u ++ [l₂, l₁] ++ (R ++ [l] ++ b)) [] [] u b (A := (xLay l₁ l₂).map (whL [] R))
        (B := [([], .dot l, [])]) (t := [l]) (t' := [l])
        (by simpa using (sChain_xLay l₁ l₂).whisk [] R) ⟨rfl, rfl⟩
      wnf at this ⊢
      exact this
  | _ => simp [Shape.isDot] at hx

/-- Dots pass a crossing (modulo diagrams without crossings). -/
theorem dotsThruX (ν : X) (u v : List (Letter I)) (l₁ l₂ : Letter I) :
    ∀ D : List (LayerData I), AllSh Shape.isDot D →
      SChain (u ++ [l₂, l₁] ++ v) D (u ++ [l₂, l₁] ++ v) →
    ∃ D' : List (LayerData I), AllSh Shape.isDot D' ∧
      SChain (u ++ [l₁, l₂] ++ v) D' (u ++ [l₁, l₂] ++ v) ∧
      dg RD k ν (u ++ [l₁, l₂] ++ v) (u ++ [l₂, l₁] ++ v) ((xLay l₁ l₂).map (whL u v) ++ D) -
        dg RD k ν (u ++ [l₁, l₂] ++ v) (u ++ [l₂, l₁] ++ v) (D' ++ (xLay l₁ l₂).map (whL u v)) ∈
      LeL RD k ν (u ++ [l₁, l₂] ++ v) (u ++ [l₂, l₁] ++ v) 0
  | [], _, _ => ⟨[], fun _ h => by simp at h, rfl, by simp⟩
  | x :: D, hD, hc => by
    have hx : x.2.1.isDot = true := hD x List.mem_cons_self
    have hxc : SChain (u ++ [l₂, l₁] ++ v) [x] (u ++ [l₂, l₁] ++ v) := by
      obtain ⟨a, g, b⟩ := x
      cases g with
      | dot l => exact ⟨hc.1, by simpa using hc.1.symm⟩
      | _ => simp [Shape.isDot] at hx
    have hDc : SChain (u ++ [l₂, l₁] ++ v) D (u ++ [l₂, l₁] ++ v) := by
      have h2 := hc.2
      have e : x.1 ++ x.2.1.cod ++ x.2.2 = u ++ [l₂, l₁] ++ v := hxc.2
      rwa [e] at h2
    obtain ⟨x', hx', hx'c, hm⟩ := dotThruX (RD := RD) (k := k) ν u v l₁ l₂ x hx hxc
    obtain ⟨D', hD', hD'c, hm'⟩ := dotsThruX ν u v l₁ l₂ D (fun y hy => hD y (by simp [hy])) hDc
    refine ⟨x' :: D', ?_, hx'c.append hD'c, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx'
      · exact hD' y hy
    have hX := (sChain_xLay l₁ l₂).whisk u v
    have e1 : dg RD k ν (u ++ [l₁, l₂] ++ v) (u ++ [l₂, l₁] ++ v) ((xLay l₁ l₂).map (whL u v) ++ x :: D) =
        dg RD k ν _ (u ++ [l₂, l₁] ++ v) ((xLay l₁ l₂).map (whL u v) ++ [x]) ≫
          dg RD k ν _ (u ++ [l₂, l₁] ++ v) D := by
      rw [← dg_append_of_left (hX.append hxc)]; simp
    have e2 : dg RD k ν (u ++ [l₁, l₂] ++ v) (u ++ [l₂, l₁] ++ v) ([x'] ++ (xLay l₁ l₂).map (whL u v) ++ D) =
        dg RD k ν _ (u ++ [l₂, l₁] ++ v) ([x'] ++ (xLay l₁ l₂).map (whL u v)) ≫
          dg RD k ν _ (u ++ [l₂, l₁] ++ v) D := by
      rw [← dg_append_of_left (hx'c.append hX)]
    have e3 : dg RD k ν (u ++ [l₁, l₂] ++ v) (u ++ [l₂, l₁] ++ v) ([x'] ++ ((xLay l₁ l₂).map (whL u v) ++ D)) =
        dg RD k ν _ (u ++ [l₁, l₂] ++ v) [x'] ≫
          dg RD k ν _ (u ++ [l₂, l₁] ++ v) ((xLay l₁ l₂).map (whL u v) ++ D) :=
      dg_append_of_left hx'c _
    have e4 : dg RD k ν (u ++ [l₁, l₂] ++ v) (u ++ [l₂, l₁] ++ v) (x' :: D' ++ (xLay l₁ l₂).map (whL u v)) =
        dg RD k ν _ (u ++ [l₁, l₂] ++ v) [x'] ≫
          dg RD k ν _ (u ++ [l₂, l₁] ++ v) (D' ++ (xLay l₁ l₂).map (whL u v)) :=
      dg_append_of_left hx'c _
    have h1 := leL_comp_dg (r := u ++ [l₂, l₁] ++ v) hm D
    have h2 := dg_comp_leL (s := u ++ [l₁, l₂] ++ v) [x'] hm'
    rw [Preadditive.sub_comp, ← e1, ← e2] at h1
    rw [Preadditive.comp_sub, ← e3, ← e4] at h2
    have hxD : ccnt D = 0 := by
      unfold ccnt; rw [List.countP_eq_zero]; intro y hy
      have := hD y (List.mem_cons_of_mem _ hy)
      obtain ⟨a, g, b⟩ := y; cases g <;> simp_all [Shape.isDot, Shape.isCross]
    have hx'0 : ccnt [x'] = 0 := by
      obtain ⟨a, g, b⟩ := x'; cases g <;> simp_all [Shape.isDot, Shape.isCross]
    rw [hxD] at h1; rw [hx'0] at h2
    have := Submodule.add_mem _ h1 h2
    simp only [List.append_assoc, List.singleton_append, List.cons_append] at this
    rw [sub_add_sub_cancel] at this
    simpa using this

/-- A move is a cup. -/
def Mv.isCup : Mv I → Bool
  | .cup .. => true
  | _ => false

omit [DecidableEq I] in
theorem ccnt_eq_zero_of_dots {D : List (LayerData I)} (hD : AllSh Shape.isDot D) : ccnt D = 0 := by
  unfold ccnt; rw [List.countP_eq_zero]; intro y hy
  have := hD y hy
  obtain ⟨a, g, b⟩ := y; cases g <;> simp_all [Shape.isDot, Shape.isCross]

/-- **Dots to the bottom**: a move diagram without cups is, modulo diagrams with fewer crossings,
dots followed by a word of crossings. -/
theorem pushDots (ν : X) : ∀ (ms : List (Mv I)) {s t : List (Letter I)}, MvChain s ms t →
    (∀ m ∈ ms, m.isCup = false) →
    ∃ (D : List (LayerData I)) (ρ : List ℕ), AllSh Shape.isDot D ∧ SChain s D s ∧
      TypeA.ValidWord s.length ρ ∧ ρ.length = ccnt (mvLay ms) ∧
      dg RD k ν s t (mvLay ms) - dg RD k ν s t (D ++ xWord s ρ) ∈
        Lo RD k ν s t (ccnt (mvLay ms))
  | [], s, t, h, _ => ⟨[], [], fun _ h => by simp at h, rfl, fun _ h => by simp at h, rfl,
      by simp [xWord]⟩
  | m :: ms, s, t, ⟨hs, h⟩, hcup => by
    obtain ⟨D, ρ, hD, hDc, hv, hl, hm⟩ := pushDots ν ms h (fun m' hm' => hcup m' (by simp [hm']))
    have hmv : mvLay (m :: ms) = m.lay ++ mvLay ms := rfl
    cases m with
    | dot u l v =>
      have hs' : s = u ++ [l] ++ v := hs
      subst hs'
      have hL : SChain (u ++ [l] ++ v) [(u, .dot l, v)] (u ++ [l] ++ v) := ⟨rfl, rfl⟩
      change SChain (u ++ [l] ++ v) D (u ++ [l] ++ v) at hDc
      change TypeA.ValidWord (u ++ [l] ++ v).length ρ at hv
      change dg RD k ν (u ++ [l] ++ v) t (mvLay ms) - dg RD k ν (u ++ [l] ++ v) t
        (D ++ xWord (u ++ [l] ++ v) ρ) ∈ Lo RD k ν (u ++ [l] ++ v) t (ccnt (mvLay ms)) at hm
      refine ⟨[(u, .dot l, v)] ++ D, ρ, ?_, hL.append hDc, hv, ?_, ?_⟩
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · rw [List.mem_singleton.1 hy]; rfl
        · exact hD y hy
      · rw [hl, hmv, ccnt_append]; simp [Mv.lay]
      · have := dg_comp_lo (s := u ++ [l] ++ v) [(u, .dot l, v)] hm
        rw [Preadditive.comp_sub, ← dg_append_of_left hL, ← dg_append_of_left hL] at this
        rw [ccnt_single_dot, zero_add] at this
        rw [hmv, ccnt_append, show ccnt (Mv.dot u l v).lay = 0 from rfl, zero_add,
          List.append_assoc [(u, Shape.dot l, v)] D]
        exact this
    | cross u l₁ l₂ v =>
      have hs' : s = u ++ [l₁, l₂] ++ v := hs
      subst hs'
      change SChain (u ++ [l₂, l₁] ++ v) D (u ++ [l₂, l₁] ++ v) at hDc
      change TypeA.ValidWord (u ++ [l₂, l₁] ++ v).length ρ at hv
      change dg RD k ν (u ++ [l₂, l₁] ++ v) t (mvLay ms) - dg RD k ν (u ++ [l₂, l₁] ++ v) t
        (D ++ xWord (u ++ [l₂, l₁] ++ v) ρ) ∈ Lo RD k ν (u ++ [l₂, l₁] ++ v) t (ccnt (mvLay ms)) at hm
      obtain ⟨D', hD', hD'c, hm'⟩ := dotsThruX (RD := RD) (k := k) ν u v l₁ l₂ D hD hDc
      have hX : SChain (u ++ [l₁, l₂] ++ v) ((xLay l₁ l₂).map (whL u v)) (u ++ [l₂, l₁] ++ v) :=
        (sChain_xLay l₁ l₂).whisk u v
      have hc1 : ccnt (Mv.cross u l₁ l₂ v).lay = 1 := by simp [Mv.lay, ccnt_map_whL]
      refine ⟨D', u.length :: ρ, hD', hD'c, ?_, ?_, ?_⟩
      · rw [TypeA.validWord_cons]; refine ⟨by simp, ?_⟩
        simpa using hv
      · rw [hmv, ccnt_append, List.length_cons, hl, hc1]; omega
      · have ex : xWord (u ++ [l₁, l₂] ++ v) (u.length :: ρ) =
            (xLay l₁ l₂).map (whL u v) ++ xWord (u ++ [l₂, l₁] ++ v) ρ := by
          rw [xWord, xAt_mid, lswap_mid]
        rw [ex, hmv, ccnt_append, hc1]
        -- the induction hypothesis, after the crossing
        have h1 := dg_comp_lo (s := u ++ [l₁, l₂] ++ v) ((xLay l₁ l₂).map (whL u v)) hm
        rw [Preadditive.comp_sub, ← dg_append_of_left hX, ← dg_append_of_left hX,
          ccnt_map_whL, ccnt_xLay] at h1
        -- the dots pass the crossing
        have h2 := lo_comp_dg (leL_le_lo (n := 1) (by omega) hm') (r := t)
          (xWord (u ++ [l₂, l₁] ++ v) ρ)
        rw [Preadditive.sub_comp, ← dg_append_of_left (hX.append hDc), ← dg_append_of_left
          (hD'c.append hX)] at h2
        have h2' := lo_mono (show 1 + ccnt (xWord (u ++ [l₂, l₁] ++ v) ρ) ≤ 1 + ccnt (mvLay ms) by
          rw [ccnt_xWord hv, hl]) h2
        have := Submodule.add_mem _ h1 h2'
        simp only [List.append_assoc] at this
        rw [sub_add_sub_cancel] at this
        simpa [Mv.lay] using this
    | cup u l v => simp [Mv.isCup] at hcup

/-! ## Braid moves -/

omit [DecidableEq I] in
theorem exists_mid3 {α : Type*} : ∀ {s : List α} {p : ℕ}, p + 2 < s.length →
    ∃ u a b c v, s = u ++ [a, b, c] ++ v ∧ u.length = p
  | a :: b :: c :: s, 0, _ => ⟨[], a, b, c, s, rfl, rfl⟩
  | a :: s, p + 1, h => by
    obtain ⟨u, x, y, z, v, rfl, rfl⟩ := exists_mid3 (s := s) (p := p) (by simp at h; omega)
    exact ⟨a :: u, x, y, z, v, rfl, rfl⟩
  | [], _, h => by simp at h
  | [a], 0, h => by simp at h
  | [a, b], 0, h => by simp at h

omit [DecidableEq I] in
theorem xAt_mid' (u v : List (Letter I)) (a b : Letter I) {p : ℕ} (hp : p = u.length) :
    xAt (u ++ [a, b] ++ v) p = (xLay a b).map (whL u v) := by
  subst hp; exact xAt_mid u v a b

omit [DecidableEq I] in
theorem lswap_mid' {α : Type*} (u v : List α) (a b : α) {p : ℕ} (hp : p = u.length) :
    lswap (u ++ [a, b] ++ v) p = u ++ [b, a] ++ v := by
  subst hp; exact lswap_mid u v a b

omit [DecidableEq I] in
/-- Distant crossings commute. -/
theorem xWord_comm (ν : X) {s t : List (Letter I)} {a b : ℕ} (hab : a + 1 < b)
    (hb : b + 1 < s.length) :
    dg RD k ν s t (xWord s [a, b]) = dg RD k ν s t (xWord s [b, a]) ∧
      lapply s [a, b] = lapply s [b, a] := by
  obtain ⟨u, p, q, w, rfl, rfl⟩ := exists_mid (s := s) (p := a) (by omega)
  obtain ⟨m, r, r', v, rfl, hm⟩ := exists_mid (s := w) (p := b - u.length - 2)
    (by simp at hb; omega)
  have e1 : u ++ [p, q] ++ (m ++ [r, r'] ++ v) = (u ++ [p, q] ++ m) ++ [r, r'] ++ v := by simp
  have e2 : u ++ [q, p] ++ (m ++ [r, r'] ++ v) = (u ++ [q, p] ++ m) ++ [r, r'] ++ v := by simp
  have e3 : (u ++ [p, q] ++ m) ++ [r', r] ++ v = u ++ [p, q] ++ (m ++ [r', r] ++ v) := by simp
  have hb' : b = (u ++ [p, q] ++ m).length := by simp; omega
  have hb'' : b = (u ++ [q, p] ++ m).length := by simp; omega
  simp only [xWord, lapply, List.foldl_cons, List.foldl_nil, List.append_nil]
  rw [xAt_mid, lswap_mid, e2, xAt_mid' _ _ _ _ hb'', lswap_mid' _ _ _ _ hb'', e1,
    xAt_mid' _ _ _ _ hb', lswap_mid' _ _ _ _ hb', e3, xAt_mid, lswap_mid]
  refine ⟨?_, by simp⟩
  have := dg_ichg (RD := RD) (k := k) (μ := ν) (s₀ := u ++ [p, q] ++ m ++ [r, r'] ++ v) (t₀ := t)
    [] [] u v (sChain_xLay p q) ((sChain_xLay r r').whisk m [])
  wnf at this ⊢
  exact this

/-- Reidemeister 3 for words (modulo lower terms). -/
theorem xWord_braid (ν : X) {s t : List (Letter I)} {a : ℕ} (ha : a + 2 < s.length) :
    dg RD k ν s t (xWord s [a, a + 1, a]) - dg RD k ν s t (xWord s [a + 1, a, a + 1]) ∈
      LeL RD k ν s t 2 ∧ lapply s [a, a + 1, a] = lapply s [a + 1, a, a + 1] := by
  obtain ⟨u, l₁, l₂, l₃, v, rfl, rfl⟩ := exists_mid3 ha
  have e : xWord (u ++ [l₁, l₂, l₃] ++ v) [u.length, u.length + 1, u.length] =
      (r3L l₁ l₂ l₃).map (whL u v) := by
    simp only [xWord, List.append_nil]
    rw [show u ++ [l₁, l₂, l₃] ++ v = u ++ [l₁, l₂] ++ ([l₃] ++ v) by simp, xAt_mid, lswap_mid,
      show u ++ [l₂, l₁] ++ ([l₃] ++ v) = (u ++ [l₂]) ++ [l₁, l₃] ++ v by simp,
      xAt_mid' _ _ _ _ (by simp), lswap_mid' _ _ _ _ (by simp),
      show (u ++ [l₂]) ++ [l₃, l₁] ++ v = u ++ [l₂, l₃] ++ ([l₁] ++ v) by simp, xAt_mid]
    simp only [r3L, List.map_append]; wnf
  have e' : xWord (u ++ [l₁, l₂, l₃] ++ v) [u.length + 1, u.length, u.length + 1] =
      (r3R l₁ l₂ l₃).map (whL u v) := by
    simp only [xWord, List.append_nil]
    rw [show u ++ [l₁, l₂, l₃] ++ v = (u ++ [l₁]) ++ [l₂, l₃] ++ v by simp,
      xAt_mid' _ _ _ _ (by simp), lswap_mid' _ _ _ _ (by simp),
      show (u ++ [l₁]) ++ [l₃, l₂] ++ v = u ++ [l₁, l₃] ++ ([l₂] ++ v) by simp, xAt_mid, lswap_mid,
      show u ++ [l₃, l₁] ++ ([l₂] ++ v) = (u ++ [l₃]) ++ [l₁, l₂] ++ v by simp,
      xAt_mid' _ _ _ _ (by simp)]
    simp only [r3R, List.map_append]; wnf
  have hv : TypeA.ValidWord (u ++ [l₁, l₂, l₃] ++ v).length [u.length, u.length + 1, u.length] := by
    simp [TypeA.ValidWord]; omega
  have hv' : TypeA.ValidWord (u ++ [l₁, l₂, l₃] ++ v).length
      [u.length + 1, u.length, u.length + 1] := by
    simp [TypeA.ValidWord]; omega
  have h1 := sChain_xWord hv
  have h2 := sChain_xWord hv'
  rw [e] at h1; rw [e'] at h2
  have h3 := (sChain_r3L l₁ l₂ l₃).whisk u v
  have h4 := (sChain_r3R l₁ l₂ l₃).whisk u v
  refine ⟨?_, (SChain.tgt_unique h1 (by simpa using h3)).trans
    (SChain.tgt_unique h2 (by simpa using h4)).symm⟩
  rw [e, e']
  exact dg_mod_free [] [] u v (r3 (RD := RD) (k := k) _ l₁ l₂ l₃) (sChain_r3L l₁ l₂ l₃)
    (sChain_r3R l₁ l₂ l₃) (by simp [r3L, xLay_ne_nil]) (by simp [r3R, xLay_ne_nil]) (by simp)
    (by simp) (by simp)

/-- A double crossing (modulo lower terms). -/
theorem xWord_rep (ν : X) {s t : List (Letter I)} {a : ℕ} (ha : a + 1 < s.length) :
    dg RD k ν s t (xWord s [a, a]) ∈ LeL RD k ν s t 1 := by
  obtain ⟨u, l₁, l₂, v, rfl, rfl⟩ := exists_mid ha
  simp only [xWord, List.append_nil]
  rw [xAt_mid, lswap_mid, xAt_mid]
  exact dg_mem_free [] [] u v (r2 (RD := RD) (k := k) _ l₁ l₂)
    ((sChain_xLay l₁ l₂).append (sChain_xLay l₂ l₁)) (by simp [xLay_ne_nil]) (by wnf) (by simp)

omit [DecidableEq I] in
/-- A local relation between words of crossings, in context. -/
theorem xWord_ctx (ν : X) {s t : List (Letter I)} (α γ γ' β : List ℕ) {c : ℕ}
    (hv : TypeA.ValidWord s.length (α ++ γ ++ β)) (hv' : TypeA.ValidWord s.length (α ++ γ' ++ β))
    (hγ : dg RD k ν (lapply s α) (lapply (lapply s α) γ) (xWord (lapply s α) γ) -
      dg RD k ν (lapply s α) (lapply (lapply s α) γ) (xWord (lapply s α) γ') ∈
        LeL RD k ν (lapply s α) (lapply (lapply s α) γ) c)
    (happ : lapply (lapply s α) γ = lapply (lapply s α) γ') :
    dg RD k ν s t (xWord s (α ++ γ ++ β)) - dg RD k ν s t (xWord s (α ++ γ' ++ β)) ∈
      LeL RD k ν s t (α.length + c + β.length) := by
  simp only [TypeA.validWord_append] at hv hv'
  set s₁ := lapply s α
  have hl₁ : s₁.length = s.length := length_lapply s α
  have hA : SChain s (xWord s α) s₁ := sChain_xWord hv.1.1
  have hG : SChain s₁ (xWord s₁ γ) (lapply s₁ γ) := sChain_xWord (by rw [hl₁]; exact hv.1.2)
  have hG' : SChain s₁ (xWord s₁ γ') (lapply s₁ γ) := happ ▸ sChain_xWord (by rw [hl₁]; exact hv'.1.2)
  rw [xWord_append, xWord_append, lapply_append, xWord_append, xWord_append, lapply_append, ← happ]
  rw [List.append_assoc, List.append_assoc, dg_append_of_left hA, dg_append_of_left hA,
    dg_append_of_left (t := t) hG, dg_append_of_left (t := t) hG', ← Preadditive.comp_sub,
    ← Preadditive.sub_comp]
  have h := leL_comp_dg (r := t) (dg_comp_leL (s := s) (xWord s α) hγ)
    (xWord (lapply s₁ γ) β)
  rw [ccnt_xWord hv.1.1, ccnt_xWord (by rw [length_lapply, hl₁]; exact hv.2)] at h
  simpa [Category.assoc] using h

omit [DecidableEq I] in
theorem braidEquiv_validWord {m : ℕ} {ρ σ : List ℕ} (h : TypeA.BraidEquiv ρ σ) :
    TypeA.ValidWord m ρ ↔ TypeA.ValidWord m σ :=
  Iff.of_eq (h.eq_of_step (f := TypeA.ValidWord m) fun _ _ h => propext h.validWord_iff)

/-- **Braid-equivalent words give the same diagram modulo lower terms.** -/
theorem xWord_braidEquiv (ν : X) {ρ σ : List ℕ} (h : TypeA.BraidEquiv ρ σ) :
    ∀ {s t : List (Letter I)}, TypeA.ValidWord s.length ρ →
      dg RD k ν s t (xWord s ρ) - dg RD k ν s t (xWord s σ) ∈ Lo RD k ν s t ρ.length := by
  induction h with
  | rel ρ σ h =>
    intro s t hv
    cases h with
    | comm α β hab =>
      rename_i a b
      have hv' := hv
      simp only [TypeA.validWord_append, TypeA.validWord_cons] at hv'
      have hb : b + 1 < (lapply s α).length := by rw [length_lapply]; exact hv'.1.2.2.1
      obtain ⟨e, happ⟩ := xWord_comm (RD := RD) (k := k) ν (t := lapply (lapply s α) [a, b]) hab hb
      refine leL_le_lo (c := α.length + 0 + β.length) (by simp; omega) ?_
      exact xWord_ctx ν α [a, b] [b, a] β hv ((TypeA.BraidStep.comm α β hab).validWord_iff.1 hv)
        (by rw [e, sub_self]; exact Submodule.zero_mem _) happ
    | braid α β a =>
      have hv' := hv
      simp only [TypeA.validWord_append, TypeA.validWord_cons] at hv'
      have ha : a + 2 < (lapply s α).length := by rw [length_lapply]; have := hv'.1.2.2.1; omega
      obtain ⟨e, happ⟩ := xWord_braid (RD := RD) (k := k) ν
        (t := lapply (lapply s α) [a, a + 1, a]) ha
      refine leL_le_lo (c := α.length + 2 + β.length) (by simp; omega) ?_
      exact xWord_ctx ν α _ _ β hv ((TypeA.BraidStep.braid α β a).validWord_iff.1 hv) e happ
  | refl => intro s t _; rw [sub_self]; exact Submodule.zero_mem _
  | symm ρ σ h ih =>
    intro s t hv
    have hv' := (braidEquiv_validWord h).2 hv
    have := Submodule.neg_mem _ (ih (t := t) hv')
    rw [neg_sub, TypeA.BraidEquiv.length_eq h] at this
    exact this
  | trans ρ σ τ h₁ h₂ ih₁ ih₂ =>
    intro s t hv
    have hv' := (braidEquiv_validWord h₁).1 hv
    have := ih₂ (t := t) hv'
    rw [← TypeA.BraidEquiv.length_eq h₁] at this
    exact lo_sub_trans (ih₁ hv) this

omit [DecidableEq I] in
/-- A local diagram in a word of crossings, in context. -/
theorem xWord_ctx_mem (ν : X) {s t : List (Letter I)} (α γ β : List ℕ) {c : ℕ}
    (hv : TypeA.ValidWord s.length (α ++ γ ++ β))
    (hγ : dg RD k ν (lapply s α) (lapply (lapply s α) γ) (xWord (lapply s α) γ) ∈
        LeL RD k ν (lapply s α) (lapply (lapply s α) γ) c) :
    dg RD k ν s t (xWord s (α ++ γ ++ β)) ∈ LeL RD k ν s t (α.length + c + β.length) := by
  simp only [TypeA.validWord_append] at hv
  set s₁ := lapply s α
  have hl₁ : s₁.length = s.length := length_lapply s α
  have hA : SChain s (xWord s α) s₁ := sChain_xWord hv.1.1
  have hG : SChain s₁ (xWord s₁ γ) (lapply s₁ γ) := sChain_xWord (by rw [hl₁]; exact hv.1.2)
  rw [xWord_append, xWord_append, lapply_append]
  rw [List.append_assoc, dg_append_of_left hA, dg_append_of_left (t := t) hG]
  have h := leL_comp_dg (r := t) (dg_comp_leL (s := s) (xWord s α) hγ)
    (xWord (lapply s₁ γ) β)
  rw [ccnt_xWord hv.1.1, ccnt_xWord (by rw [length_lapply, hl₁]; exact hv.2)] at h
  simpa [Category.assoc] using h

/-- A word with a repeated letter gives lower terms. -/
theorem xWord_hasRepeat (ν : X) {ρ : List ℕ} (h : TypeA.HasRepeat ρ) {s t : List (Letter I)}
    (hv : TypeA.ValidWord s.length ρ) : dg RD k ν s t (xWord s ρ) ∈ Lo RD k ν s t ρ.length := by
  obtain ⟨α, β, a, rfl⟩ := h
  have hv' := hv
  simp only [TypeA.validWord_append, TypeA.validWord_cons] at hv'
  have ha : a + 1 < (lapply s α).length := by rw [length_lapply]; exact hv'.1.2.1
  have hr := xWord_rep (RD := RD) (k := k) ν (t := lapply (lapply s α) [a, a]) ha
  exact leL_le_lo (by simp; omega) (xWord_ctx_mem (t := t) ν α [a, a] β hv hr)

end Categorification.KL3.Diagram
