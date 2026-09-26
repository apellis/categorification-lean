/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SortDecomp
import Categorification.Diagrams.KL3.MixedR3Sl2
import Categorification.Diagrams.KL3.SymmetryOmega
import Categorification.Diagrams.KL3.Spanning
import Categorification.Diagrams.KL3.EndOne

/-!
# Local relations of `U` modulo diagrams with fewer crossings

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.3, proof
of Proposition 3.11: "Relations on 2-morphisms in `U(E_ν 1_λ)` allow arbitrary homotopies of
colored dotted diagrams modulo lower order terms, i.e., terms with fewer crossings, fewer
circles, etc." (TeX lines 4568–4580 of `src/sln-2008-ArXiv.tex`).

This file records the local relations used in such arguments in a uniform form: every relation
between diagrams with `c` crossings holds modulo the span `LeL c'` of diagrams with at most
`c' < c` crossings (`ccnt` counts the crossing layers of a normal-form list of layers).

## The crossing of two strands

For signed letters `l₁`, `l₂` the layers `xLay l₁ l₂ : [l₁, l₂] → [l₂, l₁]` form the crossing of
the two strands: the upward or downward crossing if the orientations agree, and the sideways
crossings `crossl`, `crossr` of KL III (`eq_crossl-gen`, `eq_crossr-gen`) otherwise. Each has
exactly one crossing layer.

## Main results

* `isBub_mem_leL`: every element of the image of `Π_λ` (real and fake bubbles and their
  products) is a linear combination of crossingless closed diagrams.
* `ds0`, `ds1`: dots slide through crossings modulo diagrams without crossings.
* `r2`, `r3`: Reidemeister 2 and 3 for all orientations, modulo lower terms.
* `cupCurl`, `capCurl`, `capPF`, `cupPF`: curls and pitchforks, modulo lower terms.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## Crossing counts and lower terms -/

/-- The number of crossing layers of a list of layers. -/
def ccnt (L : List (LayerData I)) : ℕ := L.countP (fun x => x.2.1.isCross)

@[simp] theorem ccnt_nil : ccnt ([] : List (LayerData I)) = 0 := rfl

theorem ccnt_append (L M : List (LayerData I)) : ccnt (L ++ M) = ccnt L + ccnt M := by
  unfold ccnt; rw [List.countP_append]

theorem ccnt_cons (x : LayerData I) (L : List (LayerData I)) :
    ccnt (x :: L) = (if x.2.1.isCross then 1 else 0) + ccnt L := by
  unfold ccnt; rw [List.countP_cons]; split_ifs <;> simp_all [add_comm]

theorem ccnt_map_whL (L : List (LayerData I)) (u v : List (Letter I)) :
    ccnt (L.map (whL u v)) = ccnt L := by
  unfold ccnt; rw [List.countP_map]; rfl

theorem ccnt_replicate_dot (n : ℕ) (a b : List (Letter I)) (l : Letter I) :
    ccnt (List.replicate n (a, Shape.dot l, b)) = 0 := by
  unfold ccnt; rw [List.countP_eq_zero]; intro x hx; rw [List.eq_of_mem_replicate hx]
  simp [Shape.isCross]

@[simp] theorem ccnt_single_cross (a b : List (Letter I)) (ε : Bool) (i j : I) :
    ccnt [(a, Shape.cross ε i j, b)] = 1 := rfl

@[simp] theorem ccnt_single_dot (a b : List (Letter I)) (l : Letter I) :
    ccnt [(a, Shape.dot l, b)] = 0 := rfl

@[simp] theorem ccnt_single_cup (a b : List (Letter I)) (l : Letter I) :
    ccnt [(a, Shape.cup l, b)] = 0 := rfl

@[simp] theorem ccnt_single_cap (a b : List (Letter I)) (l : Letter I) :
    ccnt [(a, Shape.cap l, b)] = 0 := rfl

variable (RD k) in
/-- Linear combinations of diagrams `E_s 1_ν ⟶ E_t 1_ν` with at most `c` crossings. -/
def LeL (ν : X) (s t : List (Letter I)) (c : ℕ) :
    Submodule k ((pres RD k).obj (ob RD ν s) ⟶ (pres RD k).obj (ob RD ν t)) :=
  Submodule.span k {f | ∃ L, ccnt L ≤ c ∧ f = dg RD k ν s t L}

theorem dg_mem_leL {ν : X} {s t : List (Letter I)} {c : ℕ} {L : List (LayerData I)}
    (h : ccnt L ≤ c) : dg RD k ν s t L ∈ LeL RD k ν s t c :=
  Submodule.subset_span ⟨L, h, rfl⟩

theorem leL_mono {ν : X} {s t : List (Letter I)} {c c' : ℕ} (h : c ≤ c') :
    LeL RD k ν s t c ≤ LeL RD k ν s t c' :=
  Submodule.span_mono fun _ ⟨L, hL, e⟩ => ⟨L, hL.trans h, e⟩

theorem dg_comp_dg_mem_leL {ν : X} {s t r : List (Letter I)} {c : ℕ} {L M : List (LayerData I)}
    (h : ccnt L + ccnt M ≤ c) : dg RD k ν s t L ≫ dg RD k ν t r M ∈ LeL RD k ν s r c := by
  by_cases hA : SChain s L t
  · by_cases hB : SChain t M r
    · rw [dg_comp hA hB]; exact dg_mem_leL (by rw [ccnt_append]; omega)
    · rw [dg_of_not hB, Limits.comp_zero]; exact Submodule.zero_mem _
  · rw [dg_of_not hA, Limits.zero_comp]; exact Submodule.zero_mem _

/-- Composition adds crossings. -/
theorem leL_comp {ν : X} {s t r : List (Letter I)} {c c' : ℕ} {f g}
    (hf : f ∈ LeL RD k ν s t c) (hg : g ∈ LeL RD k ν t r c') :
    f ≫ g ∈ LeL RD k ν s r (c + c') := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨M, hM, rfl⟩ := hg
      exact dg_comp_dg_mem_leL (by omega)
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hx
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

theorem dg_comp_leL {ν : X} {s t r : List (Letter I)} {c : ℕ} {g} (M : List (LayerData I))
    (hg : g ∈ LeL RD k ν t r c) : dg RD k ν s t M ≫ g ∈ LeL RD k ν s r (ccnt M + c) :=
  leL_comp (dg_mem_leL le_rfl) hg

theorem leL_comp_dg {ν : X} {s t r : List (Letter I)} {c : ℕ} {f}
    (hf : f ∈ LeL RD k ν s t c) (M : List (LayerData I)) :
    f ≫ dg RD k ν t r M ∈ LeL RD k ν s r (c + ccnt M) :=
  leL_comp hf (dg_mem_leL le_rfl)

/-- Placement between strands preserves crossing counts. -/
theorem plcL_leL {μ : X} {u v s t : List (Letter I)} {c : ℕ} {f}
    (hf : f ∈ LeL RD k (wt RD μ v) s t c) :
    plcL RD k μ u v s t f ∈ LeL RD k μ (u ++ s ++ v) (u ++ t ++ v) c := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    rw [plcL_dg]; exact dg_mem_leL (by rw [ccnt_map_whL]; exact hL)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem ctxL_leL {μ : X} {s₀ t₀ : List (Letter I)} {pre post : List (LayerData I)}
    {u v s t : List (Letter I)} {c : ℕ} {f} (hf : f ∈ LeL RD k (wt RD μ v) s t c) :
    ctxL RD k μ s₀ t₀ pre u v post s t f ∈ LeL RD k μ s₀ t₀ (ccnt pre + c + ccnt post) := by
  have h := dg_comp_leL (s := s₀) pre (leL_comp_dg (plcL_leL (u := u) hf) (r := t₀) post)
  rw [← add_assoc] at h
  exact h

/-! ## Bubbles are linear combinations of crossingless closed diagrams -/

theorem bubMap_mem_leL (lam : X) (p : PiLam I k) :
    (bubMap RD k lam p).val ∈ LeL RD k lam [] [] 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, EndOne.val_algebraMap, ← dg_nil (RD := RD) (k := k) lam []]
    exact Submodule.smul_mem _ _ (dg_mem_leL le_rfl)
  | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  | mul_X p s hp =>
    rw [map_mul, EndOne.val_mul]
    have hX : (bubMap RD k lam (MvPolynomial.X s)).val = bubGen RD k lam s.1 (s.2 + 1) := by
      simp only [bubMap, MvPolynomial.aeval_X]; rfl
    rw [hX]
    have key : bubGen RD k lam s.1 (s.2 + 1) ∈ LeL RD k lam [] [] 0 := ?_
    · have := leL_comp key hp
      simpa using this
    unfold bubGen
    have e : ∀ m : ℤ, 0 ≤ m → ∀ f : ℤ → End ((pres RD k).obj (ob RD lam [])),
        (∀ n : ℕ, f n ∈ LeL RD k lam [] [] 0) → f m ∈ LeL RD k lam [] [] 0 := by
      intro m hm f hf
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      exact hf n
    split_ifs
    · refine e _ (by omega) (cwU RD k lam s.1) fun n => ?_
      rw [cwU_of_nonneg]
      exact dg_mem_leL (by simp [cwLs, ccnt_cons, ccnt_append, ccnt_replicate_dot, Shape.isCross])
    · refine e _ (by omega) (ccwU RD k lam s.1) fun n => ?_
      rw [ccwU_of_nonneg]
      exact dg_mem_leL (by simp [ccwLs, ccnt_cons, ccnt_append, ccnt_replicate_dot, Shape.isCross])

/-- **Bubbles are crossingless**: every element of the image of `Π_λ` is a linear combination of
closed diagrams without crossings. -/
theorem isBub_mem_leL {lam : X} {β : End ((pres RD k).obj (ob RD lam []))}
    (hβ : IsBub RD k lam β) : β ∈ LeL RD k lam [] [] 0 := by
  obtain ⟨p, hp⟩ := hβ
  have : β = (bubMap RD k lam p).val := by
    have := congrArg EndOne.val hp
    exact this.symm
  rw [this]; exact bubMap_mem_leL lam p

/-! ## Rewriting modulo lower terms -/

theorem sub_mem_trans' {M : Type*} [AddCommGroup M] {S : AddSubgroup M} {a b c : M}
    (h₁ : a - b ∈ S) (h₂ : b - c ∈ S) : a - c ∈ S := by
  have := S.add_mem h₁ h₂; rwa [sub_add_sub_cancel] at this

theorem leL_sub_trans {ν : X} {s t : List (Letter I)} {c : ℕ} {a b d}
    (h₁ : a - b ∈ LeL RD k ν s t c) (h₂ : b - d ∈ LeL RD k ν s t c) :
    a - d ∈ LeL RD k ν s t c := by
  have := Submodule.add_mem _ h₁ h₂; rwa [sub_add_sub_cancel] at this

theorem leL_sub_of_eq {ν : X} {s t : List (Letter I)} {c : ℕ} {a b} (h : a = b) :
    a - b ∈ LeL RD k ν s t c := by
  rw [h, sub_self]; exact Submodule.zero_mem _

/-- **A local relation modulo lower terms, in context.** -/
theorem dg_mod_ctx (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A B : List (LayerData I)} {c : ℕ}
    (E : dg RD k (wt RD μ v) s t A - dg RD k (wt RD μ v) s t B ∈ LeL RD k (wt RD μ v) s t c)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀) :
    dg RD k μ s₀ t₀ (pre ++ A.map (whL u v) ++ post) -
        dg RD k μ s₀ t₀ (pre ++ B.map (whL u v) ++ post) ∈
      LeL RD k μ s₀ t₀ (ccnt pre + c + ccnt post) := by
  rw [← ctxL_dg RD k μ hpre hpost A, ← ctxL_dg RD k μ hpre hpost B, ← map_sub]
  exact ctxL_leL E

/-- **A local relation modulo lower terms, at a position.** -/
theorem dg_mod_at {μ : X} {s₀ t₀ : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (u v : List (Letter I)) {s t : List (Letter I)} {A B : List (LayerData I)} {c : ℕ}
    (E : dg RD k (wt RD μ v) s t A - dg RD k (wt RD μ v) s t B ∈ LeL RD k (wt RD μ v) s t c)
    (hpre : SChain s₀ (L.take n) (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) (L.drop (n + A.length)) t₀)
    (hL : (L.drop n).take A.length = A.map (whL u v)) :
    dg RD k μ s₀ t₀ L - dg RD k μ s₀ t₀ (L.take n ++ B.map (whL u v) ++ L.drop (n + A.length)) ∈
      LeL RD k μ s₀ t₀ (ccnt (L.take n) + c + ccnt (L.drop (n + A.length))) := by
  have e : L = L.take n ++ A.map (whL u v) ++ L.drop (n + A.length) := by
    rw [← hL]; exact list_split_at' L n A.length
  have h := dg_mod_ctx μ (L.take n) (L.drop (n + A.length)) u v E hpre hpost
  rw [← e] at h
  exact h

/-- **A local diagram in the lower span, in context.** -/
theorem dg_mem_ctx (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A : List (LayerData I)} {c : ℕ}
    (E : dg RD k (wt RD μ v) s t A ∈ LeL RD k (wt RD μ v) s t c)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀) :
    dg RD k μ s₀ t₀ (pre ++ A.map (whL u v) ++ post) ∈
      LeL RD k μ s₀ t₀ (ccnt pre + c + ccnt post) := by
  rw [← ctxL_dg RD k μ hpre hpost A]
  exact ctxL_leL E

/-! ## The crossing of two strands -/

/-- The crossing `[l₁, l₂] → [l₂, l₁]` of two strands: the upward or downward crossing if the
orientations agree, otherwise the sideways crossing `crossl` or `crossr`. -/
def xLay : Letter I → Letter I → List (LayerData I)
  | (true, i), (true, j) => [([], .cross true i j, [])]
  | (false, i), (false, j) => [([], .cross false i j, [])]
  | (true, i), (false, j) => crosslL i j
  | (false, j), (true, i) => crossrL i j

theorem sChain_xLay (l₁ l₂ : Letter I) : SChain [l₁, l₂] (xLay l₁ l₂) [l₂, l₁] := by
  obtain ⟨_ | _, i⟩ := l₁ <;> obtain ⟨_ | _, j⟩ := l₂ <;>
    simp only [xLay, crosslL, crossrL] <;> schain

@[simp] theorem ccnt_xLay (l₁ l₂ : Letter I) : ccnt (xLay l₁ l₂) = 1 := by
  obtain ⟨_ | _, i⟩ := l₁ <;> obtain ⟨_ | _, j⟩ := l₂ <;> rfl

theorem length_xLay (l₁ l₂ : Letter I) :
    (xLay l₁ l₂).length = if l₁.1 = l₂.1 then 1 else 3 := by
  obtain ⟨_ | _, i⟩ := l₁ <;> obtain ⟨_ | _, j⟩ := l₂ <;> rfl

@[simp] theorem xLay_up_up (i j : I) : xLay (up i) (up j) = [([], .cross true i j, [])] := rfl
@[simp] theorem xLay_dn_dn (i j : I) : xLay (dn i) (dn j) = [([], .cross false i j, [])] := rfl
@[simp] theorem xLay_up_dn (i j : I) : xLay (up i) (dn j) = crosslL i j := rfl
@[simp] theorem xLay_dn_up (i j : I) : xLay (dn j) (up i) = crossrL i j := rfl

theorem sub_mem_of_eq_left {M : Type*} [AddCommGroup M] [Module k M] {S : Submodule k M}
    {a a' b : M} (e : a = a') (h : a' - b ∈ S) : a - b ∈ S := e ▸ h

theorem leL_sub_trans_le {ν : X} {s t : List (Letter I)} {c₁ c : ℕ} {a b d}
    (h₁ : a - b ∈ LeL RD k ν s t c₁) (hc : c₁ ≤ c) (h₂ : b - d ∈ LeL RD k ν s t c) :
    a - d ∈ LeL RD k ν s t c :=
  leL_sub_trans (leL_mono hc h₁) h₂

theorem leL_sub_self {ν : X} {s t : List (Letter I)} {c : ℕ} (a) :
    a - a ∈ LeL RD k ν s t c := by rw [sub_self]; exact Submodule.zero_mem _

/-- `mswap n`: the interchange law at the layers `n`, `n + 1` of the first diagram of a goal
`dg μ s t L - b ∈ S`. -/
macro "mswap " n:term:max : tactic => `(tactic| (
  first
    | refine sub_mem_of_eq_left (dg_swapLR_at _ $n _ _ _ (by exact rfl) (by exact rfl)
        (by exact rfl)) ?_
    | refine sub_mem_of_eq_left (dg_swapRL_at _ $n _ _ _ (by exact rfl) (by exact rfl)
        (by exact rfl)) ?_
  try dnorm))

/-- `mat n u v E`: an exact local rewrite in the first diagram of a goal `dg μ s t L - b ∈ S`. -/
macro "mat " n:term:max u:term:max v:term:max E:term:max : tactic => `(tactic| (
  refine sub_mem_of_eq_left (dg_step_at _ $n $u $v $E (by (try dnorm); schain)
    (by (try dnorm); schain) (by dnorm)) ?_
  try dnorm))

theorem mem_of_eq_left {M : Type*} [AddCommGroup M] [Module k M] {S : Submodule k M}
    {a a' : M} (e : a = a') (h : a' ∈ S) : a ∈ S := e ▸ h

/-- `iswap n`: the interchange law at the layers `n`, `n + 1` of the diagram of a goal
`dg μ s t L ∈ S`. -/
macro "iswap " n:term:max : tactic => `(tactic| (
  first
    | refine mem_of_eq_left (dg_swapLR_at _ $n _ _ _ (by exact rfl) (by exact rfl)
        (by exact rfl)) ?_
    | refine mem_of_eq_left (dg_swapRL_at _ $n _ _ _ (by exact rfl) (by exact rfl)
        (by exact rfl)) ?_
  try dnorm))

/-- `iat n u v E`: an exact local rewrite in the diagram of a goal `dg μ s t L ∈ S`. -/
macro "iat " n:term:max u:term:max v:term:max E:term:max : tactic => `(tactic| (
  refine mem_of_eq_left (dg_step_at _ $n $u $v $E (by (try dnorm); schain)
    (by (try dnorm); schain) (by dnorm)) ?_
  try dnorm))

/-- Normalizes lists of layers, unfolding the crossings `xLay`. -/
macro "xnorm" : tactic => `(tactic| (
  try simp only [xLay_up_up, xLay_dn_dn, xLay_up_dn, xLay_dn_up, crosslL, crossrL]
  try dnorm))

/-- `mmod n u v E`: a local rewrite modulo lower terms in the first diagram of a goal
`dg μ s t L - b ∈ LeL μ s t c`. -/
macro "mmod " n:term:max u:term:max v:term:max E:term:max : tactic => `(tactic| (
  refine leL_sub_trans_le (dg_mod_at _ $n $u $v $E (by xnorm; schain) (by xnorm; schain)
    (by xnorm)) (by xnorm; simp [ccnt_cons, ccnt_append, Shape.isCross]) ?_
  try xnorm))

/-! ## Dots slide through upward crossings -/

/-- A dot on the left upper strand of the upward crossing `ψ_{ij}` slides to the right lower
strand, modulo a diagram without crossings. -/
theorem dsUp0 (ν : X) (i j : I) :
    dg RD k ν [up i, up j] [up j, up i] (xLay (up i) (up j) ++ [([], .dot (up j), [up i])]) -
      dg RD k ν [up i, up j] [up j, up i] ([([up i], .dot (up j), [])] ++ xLay (up i) (up j)) ∈
        LeL RD k ν [up i, up j] [up j, up i] 0 := by
  simp only [xLay, List.singleton_append, List.cons_append, List.nil_append]
  by_cases h : i = j
  · subst h
    rw [dg_slideLEq, add_sub_cancel_left]; exact dg_mem_leL le_rfl
  · exact leL_sub_of_eq (dg_slideLNe RD k ν i j h)

/-- A dot on the right upper strand of `ψ_{ij}` slides to the left lower strand. -/
theorem dsUp1 (ν : X) (i j : I) :
    dg RD k ν [up i, up j] [up j, up i] (xLay (up i) (up j) ++ [([up j], .dot (up i), [])]) -
      dg RD k ν [up i, up j] [up j, up i] ([([], .dot (up i), [up j])] ++ xLay (up i) (up j)) ∈
        LeL RD k ν [up i, up j] [up j, up i] 0 := by
  simp only [xLay, List.singleton_append, List.cons_append, List.nil_append]
  by_cases h : i = j
  · subst h
    rw [dg_slideREq, sub_add_cancel_left, ← neg_one_smul k]
    exact Submodule.smul_mem _ _ (dg_mem_leL le_rfl)
  · exact leL_sub_of_eq (dg_slideRNe RD k ν i j h).symm

/-! ## Transport by the orientation reversal `ω̃` -/

section Omega

variable [DecidableEq I]

omit [DecidableEq I] in
theorem ccnt_wls (L : List (LayerData I)) : ccnt (Omega.wls L) = ccnt L := by
  unfold ccnt Omega.wls; rw [List.countP_map]
  apply List.countP_congr; intro x _
  obtain ⟨a, g, b⟩ := x
  cases g <;> rfl

theorem omega_leL {ν : X} {s t : List (Letter I)} {c : ℕ} {f}
    (hf : f ∈ LeL RD k ν s t c) :
    (omegaU RD k).map f ∈ (LeL RD k (-ν) (s.map Letter.dual) (t.map Letter.dual) c).map
      (TR RD k (Omega.trO ν s) (Omega.trO ν t)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    by_cases h : SChain s L t
    · rw [omegaU_dg ν L h, ← map_smul]
      exact Submodule.mem_map_of_mem (Submodule.smul_mem _ _ (dg_mem_leL (by rwa [ccnt_wls])))
    · rw [dg_of_not h, Functor.map_zero]; exact Submodule.zero_mem _
  | zero => rw [Functor.map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Functor.map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Functor.map_smul]; exact Submodule.smul_mem _ r hx

omit [DecidableEq I] in
theorem TR_mem_map_iff {a a' b b' : Obj (psig RD)} (ea : a = a') (eb : b = b')
    {S : Submodule k ((pres RD k).obj a' ⟶ (pres RD k).obj b')} {f} :
    TR RD k ea eb f ∈ S.map (TR RD k ea eb) ↔ f ∈ S := by
  refine ⟨fun ⟨g, hg, e⟩ => ?_, fun h => Submodule.mem_map_of_mem h⟩
  have : g - f = 0 := by
    rw [← TR_eq_zero ea eb, map_sub, e, sub_self]
  rwa [sub_eq_zero.1 this] at hg

theorem sgnS_sq (L : List (LayerData I)) : Sig.sgnS L * Sig.sgnS L = 1 := by
  unfold Sig.sgnS
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.map_cons, List.prod_cons]
    have : Sig.sgnSh x.2.1 * Sig.sgnSh x.2.1 = 1 := by
      unfold Sig.sgnSh; split
      · split_ifs <;> rfl
      · rfl
    calc Sig.sgnSh x.2.1 * (List.map (fun x => Sig.sgnSh x.2.1) L).prod *
          (Sig.sgnSh x.2.1 * (List.map (fun x => Sig.sgnSh x.2.1) L).prod)
        = (Sig.sgnSh x.2.1 * Sig.sgnSh x.2.1) *
          ((List.map (fun x => Sig.sgnSh x.2.1) L).prod *
            (List.map (fun x => Sig.sgnSh x.2.1) L).prod) := by ring
      _ = 1 := by rw [this, ih, one_mul]

/-- **Transport of a relation modulo lower terms by `ω̃`** (inversion of orientations): if two
diagrams with the same sign agree modulo diagrams with at most `c` crossings, so do their
orientation reversals. -/
theorem omega_transport {ν : X} {s t : List (Letter I)} {c : ℕ} {L₁ L₂ : List (LayerData I)}
    (h₁ : SChain s L₁ t) (h₂ : SChain s L₂ t) (hs : Sig.sgnS L₁ = Sig.sgnS L₂)
    (h : dg RD k ν s t L₁ - dg RD k ν s t L₂ ∈ LeL RD k ν s t c) :
    dg RD k (-ν) (s.map Letter.dual) (t.map Letter.dual) (Omega.wls L₁) -
        dg RD k (-ν) (s.map Letter.dual) (t.map Letter.dual) (Omega.wls L₂) ∈
      LeL RD k (-ν) (s.map Letter.dual) (t.map Letter.dual) c := by
  have h' := omega_leL h
  rw [Functor.map_sub, omegaU_dg ν L₁ h₁, omegaU_dg ν L₂ h₂, hs, ← smul_sub,
    ← LinearMap.map_sub (TR RD k _ _)] at h'
  have := Submodule.smul_mem _ ((Sig.sgnS L₂ : ℤ) : k) h'
  rwa [smul_smul, ← Int.cast_mul, sgnS_sq, Int.cast_one, one_smul, TR_mem_map_iff] at this

theorem omega_transport_single {ν : X} {s t : List (Letter I)} {c : ℕ} {L : List (LayerData I)}
    (hL : SChain s L t) (h : dg RD k ν s t L ∈ LeL RD k ν s t c) :
    dg RD k (-ν) (s.map Letter.dual) (t.map Letter.dual) (Omega.wls L) ∈
      LeL RD k (-ν) (s.map Letter.dual) (t.map Letter.dual) c := by
  have h' := omega_leL h
  rw [omegaU_dg ν L hL] at h'
  have := Submodule.smul_mem _ ((Sig.sgnS L : ℤ) : k) h'
  rwa [smul_smul, ← Int.cast_mul, sgnS_sq, Int.cast_one, one_smul, TR_mem_map_iff] at this

end Omega

/-! ## Dots slide through all crossings -/

theorem leL_sub_comm {ν : X} {s t : List (Letter I)} {c : ℕ} {a b}
    (h : a - b ∈ LeL RD k ν s t c) : b - a ∈ LeL RD k ν s t c := by
  rw [← neg_sub]; exact Submodule.neg_mem _ h

theorem dsUpDn0 (ν : X) (i j : I) :
    dg RD k ν [up i, dn j] [dn j, up i] (xLay (up i) (dn j) ++ [([], .dot (dn j), [up i])]) -
      dg RD k ν [up i, dn j] [dn j, up i] ([([up i], .dot (dn j), [])] ++ xLay (up i) (dn j)) ∈
        LeL RD k ν [up i, dn j] [dn j, up i] 0 := by
  xnorm
  mswap 2; mswap 1
  mat 0 [] [up i, dn j] (dg_dot_cupDn RD k j _).symm
  mmod 1 [dn j] [dn j] (leL_sub_comm (dsUp1 _ j i))
  mat 2 [dn j, up i] [] (dg_dot_cap_dn RD k _ j).symm
  mswap 1; mswap 0
  exact leL_sub_self _

theorem dsUpDn1 (ν : X) (i j : I) :
    dg RD k ν [up i, dn j] [dn j, up i] (xLay (up i) (dn j) ++ [([dn j], .dot (up i), [])]) -
      dg RD k ν [up i, dn j] [dn j, up i] ([([], .dot (up i), [dn j])] ++ xLay (up i) (dn j)) ∈
        LeL RD k ν [up i, dn j] [dn j, up i] 0 := by
  xnorm
  mswap 2
  mmod 1 [dn j] [dn j] (dsUp0 _ j i)
  mswap 0
  exact leL_sub_self _

theorem dsDnUp0 (ν : X) (i j : I) :
    dg RD k ν [dn j, up i] [up i, dn j] (xLay (dn j) (up i) ++ [([], .dot (up i), [dn j])]) -
      dg RD k ν [dn j, up i] [up i, dn j] ([([dn j], .dot (up i), [])] ++ xLay (dn j) (up i)) ∈
        LeL RD k ν [dn j, up i] [up i, dn j] 0 := by
  xnorm
  mswap 2
  mmod 1 [dn j] [dn j] (dsUp1 _ i j)
  mswap 0
  exact leL_sub_self _

theorem dsDnUp1 (ν : X) (i j : I) :
    dg RD k ν [dn j, up i] [up i, dn j] (xLay (dn j) (up i) ++ [([up i], .dot (dn j), [])]) -
      dg RD k ν [dn j, up i] [up i, dn j] ([([], .dot (dn j), [up i])] ++ xLay (dn j) (up i)) ∈
        LeL RD k ν [dn j, up i] [up i, dn j] 0 := by
  xnorm
  mswap 2; mswap 1
  mat 0 [dn j, up i] [] (dg_dot_cupUp RD k j _)
  mmod 1 [dn j] [dn j] (leL_sub_comm (dsUp0 _ i j))
  mat 2 [] [up i, dn j] (dg_dot_cap_up RD k _ j).symm
  mswap 1; mswap 0
  exact leL_sub_self _

section DnDn

variable [DecidableEq I]

theorem dsDn0 (ν : X) (i j : I) :
    dg RD k ν [dn i, dn j] [dn j, dn i] (xLay (dn i) (dn j) ++ [([], .dot (dn j), [dn i])]) -
      dg RD k ν [dn i, dn j] [dn j, dn i] ([([dn i], .dot (dn j), [])] ++ xLay (dn i) (dn j)) ∈
        LeL RD k ν [dn i, dn j] [dn j, dn i] 0 := by
  have h := omega_transport (ν := -ν) (by schain) (by schain)
    (by simp [Sig.sgnS, Sig.sgnSh, mul_comm]) (dsUp0 (RD := RD) (k := k) (-ν) i j)
  rw [neg_neg] at h
  exact h

theorem dsDn1 (ν : X) (i j : I) :
    dg RD k ν [dn i, dn j] [dn j, dn i] (xLay (dn i) (dn j) ++ [([dn j], .dot (dn i), [])]) -
      dg RD k ν [dn i, dn j] [dn j, dn i] ([([], .dot (dn i), [dn j])] ++ xLay (dn i) (dn j)) ∈
        LeL RD k ν [dn i, dn j] [dn j, dn i] 0 := by
  have h := omega_transport (ν := -ν) (by schain) (by schain)
    (by simp [Sig.sgnS, Sig.sgnSh, mul_comm]) (dsUp1 (RD := RD) (k := k) (-ν) i j)
  rw [neg_neg] at h
  exact h

/-- **Dots slide through every crossing modulo diagrams without crossings** (a dot on the left
upper strand). -/
theorem ds0 (ν : X) (l₁ l₂ : Letter I) :
    dg RD k ν [l₁, l₂] [l₂, l₁] (xLay l₁ l₂ ++ [([], .dot l₂, [l₁])]) -
      dg RD k ν [l₁, l₂] [l₂, l₁] ([([l₁], .dot l₂, [])] ++ xLay l₁ l₂) ∈
        LeL RD k ν [l₁, l₂] [l₂, l₁] 0 := by
  obtain ⟨_ | _, i⟩ := l₁ <;> obtain ⟨_ | _, j⟩ := l₂
  · exact dsDn0 ν i j
  · exact dsDnUp0 ν j i
  · exact dsUpDn0 ν i j
  · exact dsUp0 ν i j

/-- **Dots slide through every crossing modulo diagrams without crossings** (a dot on the right
upper strand). -/
theorem ds1 (ν : X) (l₁ l₂ : Letter I) :
    dg RD k ν [l₁, l₂] [l₂, l₁] (xLay l₁ l₂ ++ [([l₂], .dot l₁, [])]) -
      dg RD k ν [l₁, l₂] [l₂, l₁] ([([], .dot l₁, [l₂])] ++ xLay l₁ l₂) ∈
        LeL RD k ν [l₁, l₂] [l₂, l₁] 0 := by
  obtain ⟨_ | _, i⟩ := l₁ <;> obtain ⟨_ | _, j⟩ := l₂
  · exact dsDn1 ν i j
  · exact dsDnUp1 ν j i
  · exact dsUpDn1 ν i j
  · exact dsUp1 ν i j

end DnDn

/-! ## Reidemeister 2 modulo lower terms -/

theorem ncEval_mem {A : Type*} [Ring A] [Algebra k A] {S : Submodule k A} (h1 : (1 : A) ∈ S)
    (hmul : ∀ a b, a ∈ S → b ∈ S → a * b ∈ S) {n : ℕ} (y : Fin n → A) (hy : ∀ a, y a ∈ S)
    (p : MvPolynomial (Fin n) k) : KLR.ncEval y p ∈ S := by
  unfold KLR.ncEval Finsupp.sum
  refine Submodule.sum_mem _ fun s _ => ?_
  dsimp only
  rw [← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hpow : ∀ (a : A) (m : ℕ), a ∈ S → a ^ m ∈ S := by
    intro a m ha
    induction m with
    | zero => rw [pow_zero]; exact h1
    | succ m ih => rw [pow_succ]; exact hmul _ _ ih ha
  have hprod : ∀ l : List A, (∀ x ∈ l, x ∈ S) → l.prod ∈ S := by
    intro l hl
    induction l with
    | nil => exact h1
    | cons x l ih =>
      rw [List.prod_cons]
      exact hmul _ _ (hl x List.mem_cons_self) (ih fun y hy => hl y (List.mem_cons_of_mem _ hy))
  refine hprod _ fun x hx => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
  exact hpow _ _ (hy a)

theorem leL_comp0 {ν : X} {s t r : List (Letter I)} {f g}
    (hf : f ∈ LeL RD k ν s t 0) (hg : g ∈ LeL RD k ν t r 0) : f ≫ g ∈ LeL RD k ν s r 0 := by
  have := leL_comp hf hg; rwa [Nat.add_zero] at this

theorem leL_mul_mem {ν : X} {s : List (Letter I)} (a b : End ((pres RD k).obj (ob RD ν s)))
    (ha : a ∈ LeL RD k ν s s 0) (hb : b ∈ LeL RD k ν s s 0) : a * b ∈ LeL RD k ν s s 0 := by
  rw [End.mul_def]; exact leL_comp0 hb ha

theorem one_mem_leL {ν : X} {s : List (Letter I)} :
    (1 : End ((pres RD k).obj (ob RD ν s))) ∈ LeL RD k ν s s 0 := by
  rw [End.one_def, ← dg_nil]; exact dg_mem_leL le_rfl

theorem r2Up (ν : X) (i j : I) :
    dg RD k ν [up i, up j] [up i, up j] (xLay (up i) (up j) ++ xLay (up j) (up i)) ∈
      LeL RD k ν [up i, up j] [up i, up j] 1 := by
  simp only [xLay_up_up, List.singleton_append]
  rcases eq_or_ne i j with rfl | h
  · rw [dg_sqEq]; exact Submodule.zero_mem _
  · rw [dg_sqNe RD k ν i j h]
    split_ifs
    · exact dg_mem_leL (by simp)
    · exact Submodule.add_mem _ (dg_mem_leL (by simp [ccnt_replicate_dot]))
        (dg_mem_leL (by simp [ccnt_replicate_dot]))

theorem r2UpDn (ν : X) (i j : I) :
    dg RD k ν [up i, dn j] [up i, dn j] (xLay (up i) (dn j) ++ xLay (dn j) (up i)) ∈
      LeL RD k ν [up i, dn j] [up i, dn j] 1 := by
  simp only [xLay_up_dn, xLay_dn_up]
  by_cases h : i = j
  · subst h
    have e := (dg_decompEF RD k i ν).symm
    rw [neg_add_eq_sub, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at e
    rw [← e]
    refine Submodule.sub_mem _ (Submodule.sum_mem _ fun f _ => Submodule.sum_mem _ fun g _ => ?_)
      (dg_mem_leL (by simp))
    refine leL_mono (Nat.zero_le 1) (leL_comp0 (dg_mem_leL ?_)
      (leL_comp0 (isBub_mem_leL (ccwU_isBub _ _)) (dg_mem_leL ?_)))
    · simp [dotCapEFLs, ccnt_cons, ccnt_append, ccnt_replicate_dot, Shape.isCross]
    · simp [cupDotEFLs, ccnt_cons, ccnt_append, ccnt_replicate_dot, Shape.isCross]
  · rw [dg_downupEF RD k i j h]; exact dg_mem_leL (by simp)

theorem r2DnUp (ν : X) (i j : I) :
    dg RD k ν [dn j, up i] [dn j, up i] (xLay (dn j) (up i) ++ xLay (up i) (dn j)) ∈
      LeL RD k ν [dn j, up i] [dn j, up i] 1 := by
  simp only [xLay_up_dn, xLay_dn_up]
  by_cases h : i = j
  · subst h
    have e := (dg_decompFE RD k i ν).symm
    rw [neg_add_eq_sub, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at e
    rw [← e]
    refine Submodule.sub_mem _ (Submodule.sum_mem _ fun f _ => Submodule.sum_mem _ fun g _ => ?_)
      (dg_mem_leL (by simp))
    refine leL_mono (Nat.zero_le 1) (leL_comp0 (dg_mem_leL ?_)
      (leL_comp0 (isBub_mem_leL (cwU_isBub _ _)) (dg_mem_leL ?_)))
    · simp [dotCapFELs, ccnt_cons, ccnt_append, ccnt_replicate_dot, Shape.isCross]
    · simp [cupDotFELs, ccnt_cons, ccnt_append, ccnt_replicate_dot, Shape.isCross]
  · rw [dg_downupFE RD k j i (Ne.symm h)]; exact dg_mem_leL (by simp)

/-! ## Reidemeister 3 modulo lower terms -/

/-- **The braid relation on upward strands modulo diagrams without crossings** (KL III
`eq_r3_easy-gen`, `eq_r3_hard-gen`: the correction term of the latter is a polynomial in dots). -/
theorem r3upMod (ν : X) (c d e : I) :
    dg RD k ν [up c, up d, up e] [up e, up d, up c]
        [([], .cross true c d, [up e]), ([up d], .cross true c e, []), ([], .cross true d e, [up c])] -
      dg RD k ν [up c, up d, up e] [up e, up d, up c]
        [([up c], .cross true d e, []), ([], .cross true c e, [up d]), ([up e], .cross true c d, [])] ∈
      LeL RD k ν [up c, up d, up e] [up e, up d, up c] 0 := by
  by_cases h : c = e ∧ c ≠ d
  · obtain ⟨rfl, hcd⟩ := h
    have key := KLR.Diagram.braidQ_at (KLR.klQ2 k C) (u := []) (v := []) hcd
      (KLR.Diagram.braidL c d c) (KLR.Diagram.braidR c d c) (KLR.Diagram.E0 c d c)
      (KLR.Diagram.E1 c d c) (KLR.Diagram.E2 c d c) rfl rfl rfl rfl rfl
    have key' := congrArg (functorEndAlg k (upFunctor RD k ν) _) key
    rw [map_sub, AlgHom.map_ncEval] at key'
    simp only [functorEndAlg, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      upFunctor_diag, upDiag_eq_dg] at key'
    refine (congrArg (· ∈ _) key').mpr (ncEval_mem one_mem_leL leL_mul_mem _ (fun a => ?_) _)
    fin_cases a <;>
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, upFunctor_diag, upDiag_eq_dg]
      exact dg_mem_leL (by simp [ccnt, Shape.isCross, KLR.Diagram.dl, upLD, upShape])
  · exact leL_sub_of_eq (dg_braid RD k ν c d e h)

/-- **The outer mixed Reidemeister 3 move** (`F_j E_i E_k`), modulo diagrams with fewer
crossings, for all labels (for `i = j ≠ k` the rotation of the correction term of the braid
relation has no crossings). -/
theorem r3outRMod (i k' j : I) (μ : X) :
    dg RD k μ [dn j, up i, up k'] [up k', up i, dn j]
      ([([dn j], .cross true i k', [])] ++ (crossrL k' j).map (whL [] [up i]) ++
        (crossrL i j).map (whL [up k'] [])) -
    dg RD k μ [dn j, up i, up k'] [up k', up i, dn j]
      ((crossrL i j).map (whL [] [up k']) ++ (crossrL k' j).map (whL [up i] []) ++
        [([], .cross true i k', [dn j])]) ∈ LeL RD k μ [dn j, up i, up k'] [up k', up i, dn j] 2 := by
  dnorm
  mswap 3; mswap 4; mswap 2; mswap 3; mswap 1; mswap 2; mswap 5; mswap 4
  mat 3 [dn j, up k'] [up i, dn j] (dg_zigL' RD k _ (up j))
  mswap 0
  mmod 1 [dn j] [dn j] (r3upMod _ i k' j)
  refine leL_sub_comm ?_
  mswap 2; mswap 3; mswap 1; mswap 2; mswap 0; mswap 1; mswap 4; mswap 3
  mat 2 [dn j, up i] [up k', dn j] (dg_zigL' RD k _ (up j))
  mswap 3
  exact leL_sub_self _

/-- The outer mixed Reidemeister 3 move `E_i E_k F_j`, modulo diagrams with fewer crossings. -/
theorem r3outLMod (i k' j : I) (μ : X) :
    dg RD k μ [up i, up k', dn j] [dn j, up k', up i]
      ((crosslL k' j).map (whL [up i] []) ++ (crosslL i j).map (whL [] [up k']) ++
        [([dn j], .cross true i k', [])]) -
    dg RD k μ [up i, up k', dn j] [dn j, up k', up i]
      ([([], .cross true i k', [dn j])] ++ (crosslL i j).map (whL [up k'] []) ++
        (crosslL k' j).map (whL [] [up i])) ∈ LeL RD k μ [up i, up k', dn j] [dn j, up k', up i] 2 := by
  dnorm
  mswap 2; mswap 3; mswap 1; mswap 2; mswap 0; mswap 1; mswap 4; mswap 3
  mat 2 [dn j, up i] [up k', dn j] (dg_zigR' RD k _ (dn j))
  mswap 3
  mmod 1 [dn j] [dn j] (r3upMod _ j i k')
  refine leL_sub_comm ?_
  mswap 3; mswap 4; mswap 2; mswap 3; mswap 1; mswap 2; mswap 0; mswap 5; mswap 4
  mat 3 [dn j, up k'] [up i, dn j] (dg_zigR' RD k _ (dn j))
  exact leL_sub_self _

/-- **The two descriptions of the sideways crossing `F_i E_j → E_j F_i`**: the rotation of the
downward crossing (the orientation reversal of `crossl_{ij}`) is `crossr_{ji}` (cyclicity). -/
theorem dg_wls_crosslL (i j : I) (μ : X) :
    dg RD k μ [dn i, up j] [up j, dn i]
      [([], .cup (up j), [dn i, up j]), ([up j], .cross false j i, [up j]),
        ([up j, dn i], .cap (up j), [])] =
    dg RD k μ [dn i, up j] [up j, dn i] (crossrL j i) := by
  dat 1 [up j] [up j] (dg_cycCrossR RD k j i _)
  dswap 0; dswap 1; dswap 2; dswap 3
  dat 4 [] [dn i, dn j, up j] (dg_zigL' RD k _ (up j))
  dswap 3; dswap 2; dswap 1
  dat 0 [dn i] [] (dg_zigL' RD k _ (up j))

/-- **The two descriptions of the sideways crossing `E_j F_i → F_i E_j`**. -/
theorem dg_wls_crossrL (i j : I) (μ : X) :
    dg RD k μ [up j, dn i] [dn i, up j]
      [([up j, dn i], .cup (dn j), []), ([up j], .cross false i j, [up j]),
        ([], .cap (dn j), [dn i, up j])] =
    dg RD k μ [up j, dn i] [dn i, up j] (crosslL j i) := by
  dat 1 [up j] [up j] (dg_cycCrossL RD k i j _)
  dswap 0; dswap 1; dswap 2; dswap 3
  dat 4 [up j, dn j, dn i] [] (dg_zigR' RD k _ (dn j))
  dswap 3; dswap 2; dswap 1
  dat 0 [] [dn i] (dg_zigR' RD k _ (dn j))

/-- The left-hand side `X₀ X₁ X₀` of the Reidemeister 3 move on `[l₁, l₂, l₃]`. -/
def r3L (l₁ l₂ l₃ : Letter I) : List (LayerData I) :=
  (xLay l₁ l₂).map (whL [] [l₃]) ++ (xLay l₁ l₃).map (whL [l₂] []) ++ (xLay l₂ l₃).map (whL [] [l₁])

/-- The right-hand side `X₁ X₀ X₁` of the Reidemeister 3 move on `[l₁, l₂, l₃]`. -/
def r3R (l₁ l₂ l₃ : Letter I) : List (LayerData I) :=
  (xLay l₂ l₃).map (whL [l₁] []) ++ (xLay l₁ l₃).map (whL [] [l₂]) ++ (xLay l₁ l₂).map (whL [l₃] [])

theorem sChain_r3L (l₁ l₂ l₃ : Letter I) : SChain [l₁, l₂, l₃] (r3L l₁ l₂ l₃) [l₃, l₂, l₁] := by
  unfold r3L
  refine ((sChain_xLay l₁ l₂).whisk [] [l₃]).append (((sChain_xLay l₁ l₃).whisk [l₂] []).append
    ?_) |> fun h => by simpa using h
  simpa using (sChain_xLay l₂ l₃).whisk [] [l₁]

theorem sChain_r3R (l₁ l₂ l₃ : Letter I) : SChain [l₁, l₂, l₃] (r3R l₁ l₂ l₃) [l₃, l₂, l₁] := by
  unfold r3R
  refine ((sChain_xLay l₂ l₃).whisk [l₁] []).append (((sChain_xLay l₁ l₃).whisk [] [l₂]).append
    ?_) |> fun h => by simpa using h
  simpa using (sChain_xLay l₁ l₂).whisk [l₃] []

theorem r3_EEE (ν : X) (c d e : I) :
    dg RD k ν [up c, up d, up e] [up e, up d, up c] (r3L (up c) (up d) (up e)) -
      dg RD k ν [up c, up d, up e] [up e, up d, up c] (r3R (up c) (up d) (up e)) ∈
        LeL RD k ν [up c, up d, up e] [up e, up d, up c] 2 :=
  leL_mono (Nat.zero_le 2) (r3upMod ν c d e)

theorem bubLU_mem_leL {μ : X} {l : Letter I} {β : End ((pres RD k).obj (ob RD (wt RD μ [l]) []))}
    (hβ : IsBub RD k (wt RD μ [l]) β) : bubLU RD k μ l β ∈ LeL RD k μ [l] [l] 0 :=
  plcL_leL (u := []) (v := [l]) (s := []) (t := []) (isBub_mem_leL hβ)

theorem bubRU_mem_leL {μ : X} {l : Letter I} {β : End ((pres RD k).obj (ob RD μ []))}
    (hβ : IsBub RD k μ β) : bubRU RD k μ l β ∈ LeL RD k μ [l] [l] 0 :=
  plcL_leL (u := [l]) (v := []) (s := []) (t := []) (isBub_mem_leL hβ)

theorem sigma1Term_mem (lam : X) (i : I) (f₁ f₂ f₃ f₄ : ℕ) :
    sigma1Term RD k lam i f₁ f₂ f₃ f₄ ∈ LeL RD k lam [up i, dn i, up i] [up i, dn i, up i] 0 := by
  unfold sigma1Term
  have h1 := bubLU_mem_leL (RD := RD) (k := k) (μ := lam) (l := up i)
    (ccwU_isBub (lam := wt RD lam [up i]) i (-ip RD i lam - 3 + f₄))
  refine leL_comp0 (dg_mem_leL ?_) (leL_comp0 h1
    (leL_comp0 (dg_mem_leL ?_) (leL_comp0 (dg_mem_leL ?_) (dg_mem_leL ?_))))
  all_goals simp [ccnt_cons, ccnt_append, ccnt_replicate_dot, Shape.isCross]

theorem sigma2Term_mem (lam : X) (i : I) (g₁ g₂ g₃ g₄ : ℕ) :
    sigma2Term RD k lam i g₁ g₂ g₃ g₄ ∈ LeL RD k lam [up i, dn i, up i] [up i, dn i, up i] 0 := by
  unfold sigma2Term
  have h1 := bubRU_mem_leL (RD := RD) (k := k) (μ := lam) (l := up i)
    (cwU_isBub (lam := lam) i (ip RD i lam - 1 + g₄))
  refine leL_comp0 (dg_mem_leL ?_) (leL_comp0 h1
    (leL_comp0 (dg_mem_leL ?_) (leL_comp0 (dg_mem_leL ?_) (dg_mem_leL ?_))))
  all_goals simp [ccnt_cons, ccnt_append, ccnt_replicate_dot, Shape.isCross]

theorem r3_EFE (ν : X) (i j k' : I) :
    dg RD k ν [up i, dn j, up k'] [up k', dn j, up i] (r3L (up i) (dn j) (up k')) -
      dg RD k ν [up i, dn j, up k'] [up k', dn j, up i] (r3R (up i) (dn j) (up k')) ∈
        LeL RD k ν [up i, dn j, up k'] [up k', dn j, up i] 2 := by
  have e₁ : r3L (up i) (dn j) (up k') = r3mixL i j k' := by
    simp [r3L, r3mixL, xLay_up_dn, xLay_dn_up, xLay_up_up]
  have e₂ : r3R (up i) (dn j) (up k') = r3mixR i j k' := by
    simp [r3R, r3mixR, xLay_up_dn, xLay_dn_up, xLay_up_up]
  rw [e₁, e₂]
  by_cases h : i = j ∧ j = k'
  · obtain ⟨rfl, rfl⟩ := h
    rw [prop35_b]
    refine leL_mono (Nat.zero_le 2) (Submodule.add_mem _ ?_ ?_)
    · split_ifs
      · exact Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun z _ =>
          Submodule.sum_mem _ fun y _ => sigma1Term_mem _ _ _ _ _ _
      · exact Submodule.zero_mem _
    · split_ifs
      · exact Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun z _ =>
          Submodule.sum_mem _ fun y _ => sigma2Term_mem _ _ _ _ _ _
      · exact Submodule.zero_mem _
  · exact leL_sub_of_eq (prop35_a RD k i j k' h ν)

theorem r3_FEE (ν : X) (j i k' : I) :
    dg RD k ν [dn j, up i, up k'] [up k', up i, dn j] (r3L (dn j) (up i) (up k')) -
      dg RD k ν [dn j, up i, up k'] [up k', up i, dn j] (r3R (dn j) (up i) (up k')) ∈
        LeL RD k ν [dn j, up i, up k'] [up k', up i, dn j] 2 := by
  have h := leL_sub_comm (r3outRMod (RD := RD) (k := k) i k' j ν)
  simpa [r3L, r3R, xLay_up_dn, xLay_dn_up, xLay_up_up] using h

theorem r3_EEF (ν : X) (i k' j : I) :
    dg RD k ν [up i, up k', dn j] [dn j, up k', up i] (r3L (up i) (up k') (dn j)) -
      dg RD k ν [up i, up k', dn j] [dn j, up k', up i] (r3R (up i) (up k') (dn j)) ∈
        LeL RD k ν [up i, up k', dn j] [dn j, up k', up i] 2 := by
  have h := leL_sub_comm (r3outLMod (RD := RD) (k := k) i k' j ν)
  simpa [r3L, r3R, xLay_up_dn, xLay_dn_up, xLay_up_up] using h

section R3Omega

variable [DecidableEq I]

theorem sgnS_append₂ (L M : List (LayerData I)) : Sig.sgnS (L ++ M) = Sig.sgnS L * Sig.sgnS M := by
  simp [Sig.sgnS, List.map_append, List.prod_append]

theorem sgnS_xLay (l₁ l₂ : Letter I) : Sig.sgnS (xLay l₁ l₂) = if l₁.2 = l₂.2 then -1 else 1 := by
  obtain ⟨_ | _, i⟩ := l₁ <;> obtain ⟨_ | _, j⟩ := l₂ <;>
    simp [xLay, crosslL, crossrL, Sig.sgnS, Sig.sgnSh, eq_comm]

theorem sgnS_r3 (l₁ l₂ l₃ : Letter I) : Sig.sgnS (r3L l₁ l₂ l₃) = Sig.sgnS (r3R l₁ l₂ l₃) := by
  simp only [r3L, r3R, sgnS_append₂, sgnS_map_whL, sgnS_xLay]
  ring

theorem r3_FFF (ν : X) (c d e : I) :
    dg RD k ν [dn c, dn d, dn e] [dn e, dn d, dn c] (r3L (dn c) (dn d) (dn e)) -
      dg RD k ν [dn c, dn d, dn e] [dn e, dn d, dn c] (r3R (dn c) (dn d) (dn e)) ∈
        LeL RD k ν [dn c, dn d, dn e] [dn e, dn d, dn c] 2 := by
  have h := omega_transport (ν := -ν) (sChain_r3L _ _ _) (sChain_r3R _ _ _) (sgnS_r3 _ _ _)
    (r3_EEE (RD := RD) (k := k) (-ν) c d e)
  rw [neg_neg] at h
  exact h

theorem r3_FEF (ν : X) (i j k' : I) :
    dg RD k ν [dn i, up j, dn k'] [dn k', up j, dn i] (r3L (dn i) (up j) (dn k')) -
      dg RD k ν [dn i, up j, dn k'] [dn k', up j, dn i] (r3R (dn i) (up j) (dn k')) ∈
        LeL RD k ν [dn i, up j, dn k'] [dn k', up j, dn i] 2 := by
  have h := omega_transport (ν := -ν) (sChain_r3L _ _ _) (sChain_r3R _ _ _) (sgnS_r3 _ _ _)
    (r3_EFE (RD := RD) (k := k) (-ν) i j k')
  rw [neg_neg] at h
  simp only [r3L, r3R]
  xnorm
  mat 0 [] [dn k'] (dg_wls_crosslL (RD := RD) (k := k) i j _).symm
  mat 4 [] [dn i] (dg_wls_crossrL (RD := RD) (k := k) k' j _).symm
  refine leL_sub_comm ?_
  mat 0 [dn i] [] (dg_wls_crossrL (RD := RD) (k := k) k' j _).symm
  mat 4 [dn k'] [] (dg_wls_crosslL (RD := RD) (k := k) i j _).symm
  refine leL_sub_comm ?_
  exact h

theorem r3_FFE (ν : X) (i k' j : I) :
    dg RD k ν [dn i, dn k', up j] [up j, dn k', dn i] (r3L (dn i) (dn k') (up j)) -
      dg RD k ν [dn i, dn k', up j] [up j, dn k', dn i] (r3R (dn i) (dn k') (up j)) ∈
        LeL RD k ν [dn i, dn k', up j] [up j, dn k', dn i] 2 := by
  have h := omega_transport (ν := -ν) (sChain_r3L _ _ _) (sChain_r3R _ _ _) (sgnS_r3 _ _ _)
    (r3_EEF (RD := RD) (k := k) (-ν) i k' j)
  rw [neg_neg] at h
  simp only [r3L, r3R]
  xnorm
  mat 1 [dn k'] [] (dg_wls_crosslL (RD := RD) (k := k) i j _).symm
  mat 4 [] [dn i] (dg_wls_crosslL (RD := RD) (k := k) k' j _).symm
  refine leL_sub_comm ?_
  mat 0 [dn i] [] (dg_wls_crosslL (RD := RD) (k := k) k' j _).symm
  mat 3 [] [dn k'] (dg_wls_crosslL (RD := RD) (k := k) i j _).symm
  refine leL_sub_comm ?_
  exact h

theorem r3_EFF (ν : X) (j i k' : I) :
    dg RD k ν [up j, dn i, dn k'] [dn k', dn i, up j] (r3L (up j) (dn i) (dn k')) -
      dg RD k ν [up j, dn i, dn k'] [dn k', dn i, up j] (r3R (up j) (dn i) (dn k')) ∈
        LeL RD k ν [up j, dn i, dn k'] [dn k', dn i, up j] 2 := by
  have h := omega_transport (ν := -ν) (sChain_r3L _ _ _) (sChain_r3R _ _ _) (sgnS_r3 _ _ _)
    (r3_FEE (RD := RD) (k := k) (-ν) j i k')
  rw [neg_neg] at h
  simp only [r3L, r3R]
  xnorm
  mat 0 [] [dn k'] (dg_wls_crossrL (RD := RD) (k := k) i j _).symm
  mat 3 [dn i] [] (dg_wls_crossrL (RD := RD) (k := k) k' j _).symm
  refine leL_sub_comm ?_
  mat 1 [] [dn i] (dg_wls_crossrL (RD := RD) (k := k) k' j _).symm
  mat 4 [dn k'] [] (dg_wls_crossrL (RD := RD) (k := k) i j _).symm
  refine leL_sub_comm ?_
  exact h

/-- **Reidemeister 3 modulo lower terms, for all orientations and labels**: the two composites
of three crossings `[l₁, l₂, l₃] → [l₃, l₂, l₁]` agree modulo diagrams with at most two
crossings. -/
theorem r3 (ν : X) (l₁ l₂ l₃ : Letter I) :
    dg RD k ν [l₁, l₂, l₃] [l₃, l₂, l₁] (r3L l₁ l₂ l₃) -
      dg RD k ν [l₁, l₂, l₃] [l₃, l₂, l₁] (r3R l₁ l₂ l₃) ∈
        LeL RD k ν [l₁, l₂, l₃] [l₃, l₂, l₁] 2 := by
  obtain ⟨_ | _, a⟩ := l₁ <;> obtain ⟨_ | _, b⟩ := l₂ <;> obtain ⟨_ | _, c⟩ := l₃
  · exact r3_FFF ν a b c
  · exact r3_FFE ν a b c
  · exact r3_FEF ν a b c
  · exact r3_FEE ν a b c
  · exact r3_EFF ν a b c
  · exact r3_EFE ν a b c
  · exact r3_EEF ν a b c
  · exact r3_EEE ν a b c

theorem r2Dn (ν : X) (i j : I) :
    dg RD k ν [dn i, dn j] [dn i, dn j] (xLay (dn i) (dn j) ++ xLay (dn j) (dn i)) ∈
      LeL RD k ν [dn i, dn j] [dn i, dn j] 1 := by
  have h := omega_transport_single (ν := -ν) ((sChain_xLay _ _).append (sChain_xLay _ _))
    (r2Up (RD := RD) (k := k) (-ν) i j)
  rw [neg_neg] at h
  exact h

/-- **Reidemeister 2 modulo lower terms, for all orientations and labels.** -/
theorem r2 (ν : X) (l₁ l₂ : Letter I) :
    dg RD k ν [l₁, l₂] [l₁, l₂] (xLay l₁ l₂ ++ xLay l₂ l₁) ∈ LeL RD k ν [l₁, l₂] [l₁, l₂] 1 := by
  obtain ⟨_ | _, a⟩ := l₁ <;> obtain ⟨_ | _, b⟩ := l₂
  · exact r2Dn ν a b
  · exact r2DnUp ν b a
  · exact r2UpDn ν a b
  · exact r2Up ν a b

end R3Omega

/-! ## Curls on cups and caps -/

theorem curlR_mem (ν : X) (i : I) : dg RD k ν [up i] [up i]
      [([up i], .cup (up i), []), ([], .cross true i i, [dn i]), ([up i], .cap (dn i), [])] ∈
      LeL RD k ν [up i] [up i] 0 := by
  rw [dg_curlR]
  refine Submodule.neg_mem _ (Submodule.sum_mem _ fun f _ =>
    leL_comp0 (bubRU_mem_leL (cwU_isBub _ _)) ?_)
  rw [← dotsU_eq]; unfold dots; rw [← dg_of]; exact dg_mem_leL (by simp [ccnt_replicate_dot])

theorem curlL_mem (μ : X) (i : I) : dg RD k μ [up i] [up i]
      [([], .cup (dn i), [up i]), ([dn i], .cross true i i, []), ([], .cap (up i), [up i])] ∈
      LeL RD k μ [up i] [up i] 0 := by
  rw [dg_curlL]
  refine Submodule.sum_mem _ fun f _ => leL_comp0 (bubLU_mem_leL (ccwU_isBub _ _)) ?_
  rw [← dotsU_eq]; unfold dots; rw [← dg_of]; exact dg_mem_leL (by simp [ccnt_replicate_dot])

/-- **A crossing of the two legs of a cup is a lower term** (curl relations of KL III
Definition 3.1 iv), rotated). -/
theorem cupCurl (ν : X) (l : Letter I) :
    dg RD k ν [] [l.dual, l] ([([], .cup l, [])] ++ xLay l l.dual) ∈ LeL RD k ν [] [l.dual, l] 0 := by
  obtain ⟨_ | _, i⟩ := l
  · show dg RD k ν [] [up i, dn i] ([([], .cup (dn i), [])] ++ xLay (dn i) (up i)) ∈ _
    xnorm
    iswap 0
    have := dg_mem_ctx ν [([], .cup (up i), [])] [] [] [dn i] (curlL_mem (RD := RD) (k := k) _ i)
      (by schain) (by schain)
    simpa using this
  · show dg RD k ν [] [dn i, up i] ([([], .cup (up i), [])] ++ xLay (up i) (dn i)) ∈ _
    xnorm
    iswap 0
    have := dg_mem_ctx ν [([], .cup (dn i), [])] [] [dn i] [] (curlR_mem (RD := RD) (k := k) _ i)
      (by schain) (by schain)
    simpa using this

/-- **A crossing of the two legs of a cap is a lower term.** -/
theorem capCurl (ν : X) (l : Letter I) :
    dg RD k ν [l, l.dual] [] (xLay l l.dual ++ [([], .cap l, [])]) ∈
      LeL RD k ν [l, l.dual] [] 0 := by
  obtain ⟨_ | _, i⟩ := l
  · show dg RD k ν [dn i, up i] [] (xLay (dn i) (up i) ++ [([], .cap (dn i), [])]) ∈ _
    xnorm
    iswap 2
    have := dg_mem_ctx ν [] [([], .cap (up i), [])] [dn i] [] (curlR_mem (RD := RD) (k := k) _ i)
      (by schain) (by schain)
    simpa using this
  · show dg RD k ν [up i, dn i] [] (xLay (up i) (dn i) ++ [([], .cap (up i), [])]) ∈ _
    xnorm
    iswap 2
    have := dg_mem_ctx ν [] [([], .cap (dn i), [])] [] [dn i] (curlL_mem (RD := RD) (k := k) _ i)
      (by schain) (by schain)
    simpa using this

/-! ## Pitchfork moves through caps and cups -/

theorem capPF_up_up (ν : X) (j i : I) :
    dg RD k ν [dn j, up i, up j] [up i] ((xLay (dn j) (up i)).map (whL [] [up j]) ++
        [([up i], .cap (up j), [])]) -
      dg RD k ν [dn j, up i, up j] [up i] ((xLay (up i) (up j)).map (whL [dn j] []) ++
        [([], .cap (up j), [up i])]) ∈ LeL RD k ν [dn j, up i, up j] [up i] 0 :=
  leL_sub_of_eq (by simpa using dg_pf_capUp RD k i j ν)

theorem capPF_dn_up (ν : X) (j i : I) :
    dg RD k ν [up j, up i, dn j] [up i] ((xLay (up j) (up i)).map (whL [] [dn j]) ++
        [([up i], .cap (dn j), [])]) -
      dg RD k ν [up j, up i, dn j] [up i] ((xLay (up i) (dn j)).map (whL [up j] []) ++
        [([], .cap (dn j), [up i])]) ∈ LeL RD k ν [up j, up i, dn j] [up i] 0 :=
  leL_sub_of_eq (by simpa using (dg_pf_capDn RD k i j ν).symm)

theorem cupPF_up_up (ν : X) (j i : I) :
    dg RD k ν [up i] [up j, up i, dn j] ([([], .cup (up j), [up i])] ++
        (xLay (dn j) (up i)).map (whL [up j] [])) -
      dg RD k ν [up i] [up j, up i, dn j] ([([up i], .cup (up j), [])] ++
        (xLay (up i) (up j)).map (whL [] [dn j])) ∈ LeL RD k ν [up i] [up j, up i, dn j] 0 :=
  leL_sub_of_eq (by simpa using dg_pf_cupUp RD k i j ν)

theorem cupPF_dn_up (ν : X) (j i : I) :
    dg RD k ν [up i] [dn j, up i, up j] ([([], .cup (dn j), [up i])] ++
        (xLay (up j) (up i)).map (whL [dn j] [])) -
      dg RD k ν [up i] [dn j, up i, up j] ([([up i], .cup (dn j), [])] ++
        (xLay (up i) (dn j)).map (whL [] [up j])) ∈ LeL RD k ν [up i] [dn j, up i, up j] 0 :=
  leL_sub_of_eq (by simpa using (dg_pf_cupDn RD k i j ν).symm)

theorem cupPF_up_dn (ν : X) (j i : I) :
    dg RD k ν [dn i] [up j, dn i, dn j] ([([], .cup (up j), [dn i])] ++
        (xLay (dn j) (dn i)).map (whL [up j] [])) -
      dg RD k ν [dn i] [up j, dn i, dn j] ([([dn i], .cup (up j), [])] ++
        (xLay (dn i) (up j)).map (whL [] [dn j])) ∈ LeL RD k ν [dn i] [up j, dn i, dn j] 0 :=
  leL_sub_of_eq (by simpa using dg_pf_cupUp_down RD k i j ν)

section PFOmega

variable [DecidableEq I]

theorem capPF_dn_dn (ν : X) (j i : I) :
    dg RD k ν [up j, dn i, dn j] [dn i] ((xLay (up j) (dn i)).map (whL [] [dn j]) ++
        [([dn i], .cap (dn j), [])]) -
      dg RD k ν [up j, dn i, dn j] [dn i] ((xLay (dn i) (dn j)).map (whL [up j] []) ++
        [([], .cap (dn j), [dn i])]) ∈ LeL RD k ν [up j, dn i, dn j] [dn i] 0 := by
  have h := omega_transport (ν := -ν) (by simp only [xLay_dn_up, crossrL]; schain) (by schain)
    (by simp [xLay, crossrL, Sig.sgnS, Sig.sgnSh]) (capPF_up_up (RD := RD) (k := k) (-ν) j i)
  rw [neg_neg] at h
  xnorm
  mat 0 [] [dn j] (dg_wls_crossrL (RD := RD) (k := k) i j _).symm
  exact h

theorem capPF_up_dn (ν : X) (j i : I) :
    dg RD k ν [dn j, dn i, up j] [dn i] ((xLay (dn j) (dn i)).map (whL [] [up j]) ++
        [([dn i], .cap (up j), [])]) -
      dg RD k ν [dn j, dn i, up j] [dn i] ((xLay (dn i) (up j)).map (whL [dn j] []) ++
        [([], .cap (up j), [dn i])]) ∈ LeL RD k ν [dn j, dn i, up j] [dn i] 0 := by
  have h := omega_transport (ν := -ν) (by schain) (by simp only [xLay_up_dn, crosslL]; schain)
    (by simp [xLay, crosslL, Sig.sgnS, Sig.sgnSh]) (capPF_dn_up (RD := RD) (k := k) (-ν) j i)
  rw [neg_neg] at h
  xnorm
  refine leL_sub_comm ?_
  mat 0 [dn j] [] (dg_wls_crosslL (RD := RD) (k := k) i j _).symm
  exact leL_sub_comm h

theorem cupPF_dn_dn (ν : X) (j i : I) :
    dg RD k ν [dn i] [dn j, dn i, up j] ([([], .cup (dn j), [dn i])] ++
        (xLay (up j) (dn i)).map (whL [dn j] [])) -
      dg RD k ν [dn i] [dn j, dn i, up j] ([([dn i], .cup (dn j), [])] ++
        (xLay (dn i) (dn j)).map (whL [] [up j])) ∈ LeL RD k ν [dn i] [dn j, dn i, up j] 0 := by
  have h := omega_transport (ν := -ν) (by simp only [xLay_dn_up, crossrL]; schain) (by schain)
    (by simp [xLay, crossrL, Sig.sgnS, Sig.sgnSh]) (cupPF_up_up (RD := RD) (k := k) (-ν) j i)
  rw [neg_neg] at h
  xnorm
  mat 1 [dn j] [] (dg_wls_crossrL (RD := RD) (k := k) i j _).symm
  exact h

/-- **Pitchfork through a cap**: a strand crossing the left leg of a cap below it equals the
strand crossing the right leg (modulo lower terms; in fact exactly). -/
theorem capPF (ν : X) (l m : Letter I) :
    dg RD k ν [l.dual, m, l] [m] ((xLay l.dual m).map (whL [] [l]) ++ [([m], .cap l, [])]) -
      dg RD k ν [l.dual, m, l] [m] ((xLay m l).map (whL [l.dual] []) ++ [([], .cap l, [m])]) ∈
        LeL RD k ν [l.dual, m, l] [m] 0 := by
  obtain ⟨_ | _, j⟩ := l <;> obtain ⟨_ | _, i⟩ := m
  · exact capPF_dn_dn ν j i
  · exact capPF_dn_up ν j i
  · exact capPF_up_dn ν j i
  · exact capPF_up_up ν j i

/-- **Pitchfork through a cup**: a strand crossing the right leg of a cup to its left equals the
strand crossing the left leg of the cup to its right. -/
theorem cupPF (ν : X) (l m : Letter I) :
    dg RD k ν [m] [l, m, l.dual] ([([], .cup l, [m])] ++ (xLay l.dual m).map (whL [l] [])) -
      dg RD k ν [m] [l, m, l.dual] ([([m], .cup l, [])] ++ (xLay m l).map (whL [] [l.dual])) ∈
        LeL RD k ν [m] [l, m, l.dual] 0 := by
  obtain ⟨_ | _, j⟩ := l <;> obtain ⟨_ | _, i⟩ := m
  · exact cupPF_dn_dn ν j i
  · exact cupPF_dn_up ν j i
  · exact cupPF_up_dn ν j i
  · exact cupPF_up_up ν j i

end PFOmega

end Categorification.KL3.Diagram
