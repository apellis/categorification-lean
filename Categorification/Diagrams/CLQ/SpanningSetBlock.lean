/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.SpanningSetCaps
import Categorification.Diagrams.KL3.SpanningSetBlock

/-!
# The cap block: local moves

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.3, proof
of Proposition 3.11 (reduction of diagrams modulo lower terms).

Local relations between the cap block `capBlk S l d` (the strand `B = l` moves left across the
strands `S`, `d` dots on `A = l.dual`, and the cap joining `A` and `B`) and a move just below it,
used to push the block down through a move diagram (`Categorification.Diagrams.KL3.SpanningSetElim`).
Each relation holds exactly or modulo diagrams with fewer crossings (`LeL`).

This is the version for `U_Q(g)` (S. Cautis, A. D. Lauda, arXiv:1111.1431v3, Definition 1.1,
`r = 1`) of `Categorification.Diagrams.KL3.SpanningSetBlock`. The pitchfork moves of `U_Q(g)` hold
up to a unit (`CLQ.capPF`, `CLQ.cupPF`), so `capBlk_enterL`, `cupThru` and `capBlk_cupBright`
hold up to a unit; the membership statements are as for KL III.
-/
noncomputable section
namespace Categorification.KL3.Diagram.CLQ
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k] {sc : CL.CLScalars C k}

/-- The local interchange law for two blocks. -/
theorem ichgLoc (ν : X) {s s' t t' : List (Letter I)} {A B : List (LayerData I)}
    (hA : SChain s A s') (hB : SChain t B t') :
    NF.dg (pres RD k sc) ν (s ++ t) (s' ++ t') (A.map (whL [] t) ++ B.map (whL s' [])) =
      NF.dg (pres RD k sc) ν (s ++ t) (s' ++ t') (B.map (whL s []) ++ A.map (whL [] t')) := by
  simpa using NF.dg_interchange (P := pres RD k sc) (μ := ν) (S := s ++ t) (T := s' ++ t') [] [] hA hB

theorem mem_of_sub_smul_mem {M : Type*} [AddCommGroup M] [Module k M] {S : Submodule k M}
    {a b : M} {c : k} (h : a - c • b ∈ S) (hb : b ∈ S) : a ∈ S :=
  mem_of_sub_mem h (S.smul_mem c hb)

theorem sub_smul_comm_unit {M : Type*} [AddCommGroup M] [Module k M] {S : Submodule k M}
    {a b : M} (c : kˣ) (h : a - (c : k) • b ∈ S) : b - ((c⁻¹ : kˣ) : k) • a ∈ S := by
  have := S.smul_mem (-((c⁻¹ : kˣ) : k)) h
  have e : -((c⁻¹ : kˣ) : k) • (a - (c : k) • b) = b - ((c⁻¹ : kˣ) : k) • a := by
    rw [smul_sub, smul_smul, neg_mul, Units.inv_mul, neg_smul, neg_smul, one_smul]; abel
  rwa [e] at this

theorem smul_sub_smul_mem {M : Type*} [AddCommGroup M] [Module k M] {S : Submodule k M}
    {a b : M} (c : k) (h : a - b ∈ S) : c • a - c • b ∈ S := by
  rw [← smul_sub]; exact S.smul_mem c h

theorem smul_sub_smul_mul_mem {M : Type*} [AddCommGroup M] [Module k M] {S : Submodule k M}
    {a b : M} (c₁ c₂ : k) (h : a - c₂ • b ∈ S) : c₁ • a - (c₁ * c₂) • b ∈ S := by
  rw [mul_smul, ← smul_sub]; exact S.smul_mem c₁ h

/-- `dg_mod_free` with a scalar on the second diagram. -/
theorem dg_mod_free_smul {μ : X} {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A B : List (LayerData I)} {c c' : ℕ} (a : k)
    (E : NF.dg (pres RD k sc) (wt RD μ v) s t A - a • NF.dg (pres RD k sc) (wt RD μ v) s t B ∈
      LeL RD k sc (wt RD μ v) s t c)
    (hA : SChain s A t) (hB : SChain s B t) (hAne : A ≠ []) (hBne : B ≠ [])
    {L L' : List (LayerData I)}
    (hL : L = pre ++ A.map (whL u v) ++ post) (hL' : L' = pre ++ B.map (whL u v) ++ post)
    (hc : ccnt pre + c + ccnt post ≤ c') :
    NF.dg (pres RD k sc) μ s₀ t₀ L - a • NF.dg (pres RD k sc) μ s₀ t₀ L' ∈
      LeL RD k sc μ s₀ t₀ c' := by
  subst hL hL'
  by_cases h : SChain s₀ (pre ++ A.map (whL u v) ++ post) t₀
  · obtain ⟨m', h₁, h₂⟩ := SChain.split h
    obtain ⟨m, h₃, h₄⟩ := SChain.split h₁
    obtain ⟨rfl, rfl⟩ := (sChain_map_whL_iff hA hAne u v m m').1 h₄
    refine leL_mono hc ?_
    rw [← NF.ctxL_dg (pres RD k sc) μ h₃ h₂ A, ← NF.ctxL_dg (pres RD k sc) μ h₃ h₂ B, ← map_smul,
      ← map_sub]
    exact ctxL_leL E
  · have h' : ¬ SChain s₀ (pre ++ B.map (whL u v) ++ post) t₀ := by
      intro h'
      obtain ⟨m', h₁, h₂⟩ := SChain.split h'
      obtain ⟨m, h₃, h₄⟩ := SChain.split h₁
      obtain ⟨rfl, rfl⟩ := (sChain_map_whL_iff hB hBne u v m m').1 h₄
      exact h ((h₃.append (hA.whisk u v)).append h₂)
    rw [NF.dg_of_not h, NF.dg_of_not h', smul_zero, sub_self]; exact Submodule.zero_mem _

variable [DecidableEq I]

theorem capBlk_dotS (hr : ∀ i, sc.r i = 1) (ν : X) (S₁ S₂ : List (Letter I)) (s l : Letter I) (d : ℕ) :
    NF.dg (pres RD k sc) ν ([l.dual] ++ (S₁ ++ [s] ++ S₂) ++ [l]) (S₁ ++ [s] ++ S₂)
        ([([l.dual] ++ S₁, .dot s, S₂ ++ [l])] ++ capBlk (S₁ ++ [s] ++ S₂) l d) -
      NF.dg (pres RD k sc) ν ([l.dual] ++ (S₁ ++ [s] ++ S₂) ++ [l]) (S₁ ++ [s] ++ S₂)
        (capBlk (S₁ ++ [s] ++ S₂) l d ++ [(S₁, .dot s, S₂)]) ∈
      LeL RD k sc ν ([l.dual] ++ (S₁ ++ [s] ++ S₂) ++ [l]) (S₁ ++ [s] ++ S₂)
        ((S₁ ++ [s] ++ S₂).length - 1) := by
  have hS : lmLc (S₁ ++ [s] ++ S₂) l = (lmLc S₂ l).map (whL (S₁ ++ [s]) []) ++
      (xLay s l).map (whL S₁ S₂) ++ (lmLc S₁ l).map (whL [] (s :: S₂)) := by
    rw [List.append_assoc, lmLc_append, List.singleton_append]; simp only [lmLc, List.map_append]; wnf
  rw [capBlk_eq, hS]
  -- step 1: the dot passes `lmLc S₂`
  refine sub_mem_of_eq_left (dg_step_free [] ((xLay s l).map (whL (l.dual :: S₁) S₂) ++
      (lmLc S₁ l).map (whL [l.dual] (s :: S₂)) ++
      List.replicate d ([], .dot l.dual, l :: (S₁ ++ [s] ++ S₂)) ++ [([], .cap l, S₁ ++ [s] ++ S₂)])
      (l.dual :: S₁) [] (ichgLoc (RD := RD) (k := k) (sc := sc) _ (A := [([], .dot s, [])]) (s := [s]) (s' := [s])
        ⟨rfl, rfl⟩ (sChain_lmLc S₂ l))
      (sChain_ichgL ⟨rfl, rfl⟩ (sChain_lmLc S₂ l)) (sChain_ichgR ⟨rfl, rfl⟩ (sChain_lmLc S₂ l))
      (by simp) (by simp) (by wnf) rfl) ?_
  -- step 2: the dot slides through the crossing of `s` with `l`
  refine leL_sub_trans (dg_mod_free ((lmLc S₂ l).map (whL (l.dual :: S₁ ++ [s]) []))
      ((lmLc S₁ l).map (whL [l.dual] (s :: S₂)) ++
      List.replicate d ([], .dot l.dual, l :: (S₁ ++ [s] ++ S₂)) ++ [([], .cap l, S₁ ++ [s] ++ S₂)])
      (l.dual :: S₁) S₂ (leL_sub_comm (ds1 (RD := RD) (k := k) (sc := sc) hr _ s l)) (by simpa using ((show
        SChain [s, l] [([], .dot s, [l])] [s, l] from ⟨rfl, rfl⟩).append (sChain_xLay s l)))
      (by simpa using (sChain_xLay s l).append (show SChain [l, s] [([l], .dot s, [])] [l, s]
        from ⟨rfl, rfl⟩))
      (by simp) (by simp) (by wnf) rfl ?_) ?_
  · simp [ccnt_append, ccnt_map_whL, ccnt_lmLc, ccnt_replicate_dot]; omega
  -- step 3: the dot passes the rest of the block
  refine sub_mem_of_eq_left (dg_step_free ((lmLc S₂ l).map (whL (l.dual :: S₁ ++ [s]) []) ++
      (xLay s l).map (whL (l.dual :: S₁) S₂)) [] [] S₂
      (ichgLoc (RD := RD) (k := k) (sc := sc) _ (B := [([], .dot s, [])]) (t := [s]) (t' := [s])
        (sChain_capBlk S₁ l d) ⟨rfl, rfl⟩).symm
      (sChain_ichgR (sChain_capBlk S₁ l d) ⟨rfl, rfl⟩) (sChain_ichgL (sChain_capBlk S₁ l d) ⟨rfl, rfl⟩)
      (by simp) (by simp [capBlk]) (by simp only [capBlk_eq]; wnf) rfl) ?_
  refine leL_sub_of_eq ?_
  simp only [capBlk_eq]
  wnf


theorem capBlk_crossS (hr : ∀ i, sc.r i = 1) (ν : X) (S₁ S₂ : List (Letter I)) (l₁ l₂ l : Letter I) (d : ℕ) :
    NF.dg (pres RD k sc) ν ([l.dual] ++ (S₁ ++ [l₁, l₂] ++ S₂) ++ [l]) (S₁ ++ [l₂, l₁] ++ S₂)
        ((xLay l₁ l₂).map (whL ([l.dual] ++ S₁) (S₂ ++ [l])) ++ capBlk (S₁ ++ [l₂, l₁] ++ S₂) l d) -
      NF.dg (pres RD k sc) ν ([l.dual] ++ (S₁ ++ [l₁, l₂] ++ S₂) ++ [l]) (S₁ ++ [l₂, l₁] ++ S₂)
        (capBlk (S₁ ++ [l₁, l₂] ++ S₂) l d ++ (xLay l₁ l₂).map (whL S₁ S₂)) ∈
      LeL RD k sc ν ([l.dual] ++ (S₁ ++ [l₁, l₂] ++ S₂) ++ [l]) (S₁ ++ [l₂, l₁] ++ S₂)
        (S₁ ++ [l₁, l₂] ++ S₂).length := by
  simp only [capBlk_eq, lmLc_pair]
  -- step 1: the crossing passes `lmLc S₂`
  refine sub_mem_of_eq_left (dg_step_free [] ((xLay l₁ l).map (whL (l.dual :: S₁ ++ [l₂]) S₂) ++
      (xLay l₂ l).map (whL (l.dual :: S₁) (l₁ :: S₂)) ++
      (lmLc S₁ l).map (whL [l.dual] (l₂ :: l₁ :: S₂)) ++
      List.replicate d ([], .dot l.dual, l :: (S₁ ++ [l₂, l₁] ++ S₂)) ++
      [([], .cap l, S₁ ++ [l₂, l₁] ++ S₂)]) (l.dual :: S₁) []
      (ichgLoc (RD := RD) (k := k) (sc := sc) _ (sChain_xLay l₁ l₂) (sChain_lmLc S₂ l))
      (sChain_ichgL (sChain_xLay l₁ l₂) (sChain_lmLc S₂ l))
      (sChain_ichgR (sChain_xLay l₁ l₂) (sChain_lmLc S₂ l))
      (by simp [xLay_ne_nil]) (by simp [xLay_ne_nil]) (by wnf) rfl) ?_
  -- step 2: Reidemeister 3 with `B`
  refine leL_sub_trans (dg_mod_free ((lmLc S₂ l).map (whL (l.dual :: S₁ ++ [l₁, l₂]) []))
      ((lmLc S₁ l).map (whL [l.dual] (l₂ :: l₁ :: S₂)) ++
      List.replicate d ([], .dot l.dual, l :: (S₁ ++ [l₂, l₁] ++ S₂)) ++
      [([], .cap l, S₁ ++ [l₂, l₁] ++ S₂)])
      (l.dual :: S₁) S₂ (r3 (RD := RD) (k := k) (sc := sc) hr _ l₁ l₂ l) (sChain_r3L l₁ l₂ l) (sChain_r3R l₁ l₂ l)
      (by simp [r3L, xLay_ne_nil]) (by simp [r3R, xLay_ne_nil]) (by simp only [r3L]; wnf) rfl ?_) ?_
  · simp [ccnt_append, ccnt_map_whL, ccnt_lmLc, ccnt_replicate_dot]; omega
  -- step 3: the crossing passes the rest of the block
  refine sub_mem_of_eq_left (dg_step_free ((lmLc S₂ l).map (whL (l.dual :: S₁ ++ [l₁, l₂]) []) ++
      (xLay l₂ l).map (whL (l.dual :: (S₁ ++ [l₁])) S₂) ++
      (xLay l₁ l).map (whL (l.dual :: S₁) (l₂ :: S₂))) [] [] S₂
      (ichgLoc (RD := RD) (k := k) (sc := sc) _ (B := xLay l₁ l₂) (t := [l₁, l₂]) (t' := [l₂, l₁])
        (sChain_capBlk S₁ l d) (sChain_xLay l₁ l₂)).symm
      (sChain_ichgR (sChain_capBlk S₁ l d) (sChain_xLay l₁ l₂))
      (sChain_ichgL (sChain_capBlk S₁ l d) (sChain_xLay l₁ l₂))
      (by simp [xLay_ne_nil]) (by simp [capBlk]) (by simp only [capBlk_eq, r3R]; wnf) rfl) ?_
  refine leL_sub_of_eq ?_
  simp only [capBlk_eq]
  wnf

/-- A strand entering the block from the left joins it (modulo lower terms). -/
theorem capBlk_enterL (hr : ∀ i, sc.r i = 1) (ν : X) (S : List (Letter I)) (e l : Letter I) (d : ℕ) :
    ∃ c : kˣ, NF.dg (pres RD k sc) ν ([l.dual, e] ++ S ++ [l]) (e :: S)
        ((xLay l.dual e).map (whL [] (S ++ [l])) ++ (capBlk S l d).map (whL [e] [])) -
      (c : k) • NF.dg (pres RD k sc) ν ([l.dual, e] ++ S ++ [l]) (e :: S) (capBlk (e :: S) l d) ∈
      LeL RD k sc ν ([l.dual, e] ++ S ++ [l]) (e :: S) S.length := by
  obtain ⟨c, hc⟩ := capPF (RD := RD) (k := k) (sc := sc) hr (wt RD ν S) l e
  refine ⟨c, ?_⟩
  simp only [capBlk_eq, List.map_append, List.map_replicate]
  -- step 1: the crossing passes `lmLc S`
  refine sub_mem_of_eq_left (dg_step_free []
      (List.replicate d (whL [e] [] ([], .dot l.dual, l :: S)) ++ [whL [e] [] ([], .cap l, S)]) [] []
      (ichgLoc (RD := RD) (k := k) (sc := sc) _ (sChain_xLay l.dual e) (sChain_lmLc S l))
      (sChain_ichgL (sChain_xLay l.dual e) (sChain_lmLc S l))
      (sChain_ichgR (sChain_xLay l.dual e) (sChain_lmLc S l))
      (by simp [xLay_ne_nil]) (by simp [xLay_ne_nil]) (by wnf) rfl) ?_
  -- step 2: the dots on `A` pass the crossing
  refine leL_sub_trans (dg_mod_free ((lmLc S l).map (whL [l.dual, e] []))
      [([e], .cap l, S)] [] (l :: S) (ds1rep (RD := RD) (k := k) (sc := sc) hr _ l.dual e d)
      (by simpa using (sChain_xLay l.dual e).append (SChain.replicate d [e] l.dual []))
      (by simpa using (SChain.replicate d [] l.dual [e]).append (sChain_xLay l.dual e))
      (by simp [xLay_ne_nil]) (by simp [xLay_ne_nil]) (by wnf) rfl ?_) ?_
  · simp [ccnt_map_whL, ccnt_lmLc]
  -- step 3: the pitchfork
  refine leL_sub_trans (dg_mod_free_smul ((lmLc S l).map (whL [l.dual, e] []) ++
      List.replicate d ([], .dot l.dual, e :: l :: S)) [] [] S _ hc
      (by simpa using ((sChain_xLay l.dual e).whisk [] [l]).append
                  (show SChain [e, l.dual, l] [([e], .cap l, [])] [e] from ⟨rfl, rfl⟩))
      (by simpa using ((sChain_xLay e l).whisk [l.dual] []).append
                  (show SChain [l.dual, l, e] [([], .cap l, [e])] [e] from ⟨rfl, rfl⟩))
      (by simp [xLay_ne_nil]) (by simp [xLay_ne_nil]) (by wnf) rfl ?_) ?_
  · simp [ccnt_append, ccnt_map_whL, ccnt_lmLc, ccnt_replicate_dot]
  -- step 4: the dots on `A` pass the crossing of `e` and `B`
  refine smul_sub_smul_mem _ (leL_sub_of_eq (dg_step_free ((lmLc S l).map (whL [l.dual, e] []))
      [([], .cap l, e :: S)] [] S
      (ichgLoc (RD := RD) (k := k) (sc := sc) _ (A := List.replicate d ([], .dot l.dual, []))
        (s := [l.dual]) (s' := [l.dual]) (by simpa using SChain.replicate d [] l.dual [])
        (sChain_xLay e l))
      (sChain_ichgL (by simpa using SChain.replicate d [] l.dual []) (sChain_xLay e l))
      (sChain_ichgR (by simpa using SChain.replicate d [] l.dual []) (sChain_xLay e l))
      (by simp [xLay_ne_nil]) (by simp [xLay_ne_nil]) (by wnf) ?_))
  simp only [lmLc, List.map_append]; wnf

/-- A crossing of `A` with the first strand of the block gives lower terms. -/
theorem capBlk_sA (hr : ∀ i, sc.r i = 1) (ν : X) (s : Letter I) (S : List (Letter I)) (l : Letter I) (d : ℕ) :
    NF.dg (pres RD k sc) ν ([s, l.dual] ++ S ++ [l]) (s :: S)
        ((xLay s l.dual).map (whL [] (S ++ [l])) ++ capBlk (s :: S) l d) ∈
      LeL RD k sc ν ([s, l.dual] ++ S ++ [l]) (s :: S) (S.length + 1) := by
  obtain ⟨c, hc⟩ := capPF (RD := RD) (k := k) (sc := sc) hr (wt RD ν S) l s
  simp only [capBlk_eq, lmLc, List.map_append]
  -- step 1: the crossing passes `lmLc S`
  refine mem_of_eq_left (dg_step_free []
      ((xLay s l).map (whL [l.dual] S) ++ List.replicate d ([], .dot l.dual, l :: s :: S) ++
        [([], .cap l, s :: S)]) [] []
      (ichgLoc (RD := RD) (k := k) (sc := sc) _ (sChain_xLay s l.dual) (sChain_lmLc S l))
      (sChain_ichgL (sChain_xLay s l.dual) (sChain_lmLc S l))
      (sChain_ichgR (sChain_xLay s l.dual) (sChain_lmLc S l))
      (by simp [xLay_ne_nil]) (by simp [xLay_ne_nil]) (by wnf) rfl) ?_
  -- step 2: the dots on `A` pass the crossing of `s` and `B`
  refine mem_of_eq_left (dg_step_free ((lmLc S l).map (whL [s, l.dual] []) ++
      (xLay s l.dual).map (whL [] (l :: S))) [([], .cap l, s :: S)] [] S
      (ichgLoc (RD := RD) (k := k) (sc := sc) _ (A := List.replicate d ([], .dot l.dual, []))
        (s := [l.dual]) (s' := [l.dual]) (by simpa using SChain.replicate d [] l.dual [])
        (sChain_xLay s l)).symm
      (sChain_ichgR (by simpa using SChain.replicate d [] l.dual []) (sChain_xLay s l))
      (sChain_ichgL (by simpa using SChain.replicate d [] l.dual []) (sChain_xLay s l))
      (by simp [xLay_ne_nil]) (by simp [xLay_ne_nil]) (by wnf) rfl) ?_
  -- step 3: the pitchfork
  refine mem_of_sub_smul_mem (dg_mod_free_smul ((lmLc S l).map (whL [s, l.dual] []) ++
      (xLay s l.dual).map (whL [] (l :: S)) ++ List.replicate d ([], .dot l.dual, s :: l :: S)) []
      [] S _ (sub_smul_comm_unit c hc)
      (by simpa using ((sChain_xLay s l).whisk [l.dual] []).append
                  (show SChain [l.dual, l, s] [([], .cap l, [s])] [s] from ⟨rfl, rfl⟩))
      (by simpa using ((sChain_xLay l.dual s).whisk [] [l]).append
                  (show SChain [s, l.dual, l] [([s], .cap l, [])] [s] from ⟨rfl, rfl⟩))
      (by simp [xLay_ne_nil]) (by simp [xLay_ne_nil]) (by wnf) rfl ?_) ?_
  · simp [ccnt_append, ccnt_map_whL, ccnt_lmLc, ccnt_replicate_dot]
  -- step 4: the dots on `A` pass the crossing of `s` and `A`
  refine mem_of_sub_mem (dg_mod_free ((lmLc S l).map (whL [s, l.dual] []))
      ((xLay l.dual s).map (whL [] (l :: S)) ++ [([s], .cap l, S)]) [] (l :: S)
      (ds0rep (RD := RD) (k := k) (sc := sc) hr _ s l.dual d)
      (by simpa using (sChain_xLay s l.dual).append (SChain.replicate d [] l.dual [s]))
      (by simpa using (SChain.replicate d [s] l.dual []).append (sChain_xLay s l.dual))
      (by simp [xLay_ne_nil]) (by simp [xLay_ne_nil]) (by wnf) rfl ?_) ?_
  · simp [ccnt_append, ccnt_map_whL, ccnt_lmLc]; try omega
  -- step 5: the double crossing
  refine dg_mem_free ((lmLc S l).map (whL [s, l.dual] []) ++
      List.replicate d ([s], .dot l.dual, l :: S)) [([s], .cap l, S)] [] (l :: S)
      (r2 (RD := RD) (k := k) (sc := sc) hr _ s l.dual) ((sChain_xLay s l.dual).append (sChain_xLay l.dual s))
      (by simp [xLay_ne_nil]) (by wnf) ?_
  simp [ccnt_append, ccnt_map_whL, ccnt_lmLc, ccnt_replicate_dot]; try omega

/-- A crossing of the last strand of the block with `B` gives lower terms. -/
theorem capBlk_sB (hr : ∀ i, sc.r i = 1) (ν : X) (S : List (Letter I)) (s l : Letter I) (d : ℕ) :
    NF.dg (pres RD k sc) ν ([l.dual] ++ S ++ [l, s]) (S ++ [s])
        ((xLay l s).map (whL ([l.dual] ++ S) []) ++ capBlk (S ++ [s]) l d) ∈
      LeL RD k sc ν ([l.dual] ++ S ++ [l, s]) (S ++ [s]) (S.length + 1) := by
  simp only [capBlk_eq, lmLc_snoc, List.map_append]
  refine dg_mem_free [] ((lmLc S l).map (whL [l.dual] [s]) ++
      List.replicate d ([], .dot l.dual, l :: (S ++ [s])) ++ [([], .cap l, S ++ [s])])
      (l.dual :: S) [] (r2 (RD := RD) (k := k) (sc := sc) hr _ l s)
      ((sChain_xLay l s).append (sChain_xLay s l)) (by simp [xLay_ne_nil]) (by wnf) ?_
  simp [ccnt_append, ccnt_map_whL, ccnt_lmLc, ccnt_replicate_dot]; try omega

/-- A crossing of `B` and `A` (no strands in the block) is a curl. -/
theorem capBlk_AB (hr : ∀ i, sc.r i = 1) (ν : X) (l : Letter I) (d : ℕ) :
    NF.dg (pres RD k sc) ν [l, l.dual] [] (xLay l l.dual ++ capBlk [] l d) ∈ LeL RD k sc ν [l, l.dual] [] 0 := by
  simp only [capBlk_eq, lmLc, List.map_nil, List.nil_append]
  refine mem_of_sub_mem (dg_mod_free [] [([], .cap l, [])] [] [] (ds0rep (RD := RD) (k := k) (sc := sc) hr _ l l.dual d)
      (by simpa using (sChain_xLay l l.dual).append (SChain.replicate d [] l.dual [l]))
      (by simpa using (SChain.replicate d [l] l.dual []).append (sChain_xLay l l.dual))
      (by simp [xLay_ne_nil]) (by simp [xLay_ne_nil]) (by simp) rfl (by simp)) ?_
  exact dg_mem_free (List.replicate d ([l], .dot l.dual, [])) [] [] [] (capCurl (RD := RD) (k := k) (sc := sc) _ l)
    (by simpa using (sChain_xLay l l.dual).append
                  (show SChain [l.dual, l] [([], .cap l, [])] [] from ⟨rfl, rfl⟩))
    (by simp [xLay_ne_nil]) (by simp) (by simp [ccnt_replicate_dot])

omit [DecidableEq I] in
/-- A cup creating a strand and `A` cancels the cap (zigzag): the block becomes a strand moving
left across `S`, with `d` dots. -/
theorem capBlk_cupAleft (ν : X) (S : List (Letter I)) (l : Letter I) (d : ℕ) :
    NF.dg (pres RD k sc) ν (S ++ [l]) (l :: S) ([([], .cup l, S ++ [l])] ++ (capBlk S l d).map (whL [l] [])) =
      NF.dg (pres RD k sc) ν (S ++ [l]) (l :: S) (lmLc S l ++ List.replicate d ([], .dot l, S)) := by
  simp only [capBlk_eq, List.map_append, List.map_replicate]
  refine (dg_step_free [] (List.replicate d (whL [l] [] ([], .dot l.dual, l :: S)) ++
      [whL [l] [] ([], .cap l, S)]) [] []
      (ichgLoc (RD := RD) (k := k) (sc := sc) _ (A := [([], .cup l, [])]) (s := []) (s' := [l, l.dual])
        ⟨rfl, rfl⟩ (sChain_lmLc S l))
      (sChain_ichgL ⟨rfl, rfl⟩ (sChain_lmLc S l)) (sChain_ichgR ⟨rfl, rfl⟩ (sChain_lmLc S l))
      (by simp) (by simp) (by wnf) rfl).trans ?_
  refine NF.dg_step (pres RD k sc) ν (lmLc S l) [] [] S (zigDotsL (wt RD ν S) l d)
    (by simpa using sChain_lmLc S l) (by simp) (by wnf) (by wnf)

omit [DecidableEq I] in
/-- A cup creating `A` and `B` (no strands in the block) closes a dotted bubble, which lies in the
image of `Π`. -/
theorem isBub_capBlk_nil (ν : X) (l : Letter I) (d : ℕ) :
    IsBub RD k sc ν (NF.dg (pres RD k sc) ν [] [] ([([], .cup l.dual, [])] ++ capBlk [] l d)) := by
  simp only [capBlk_eq, lmLc, List.map_nil, List.nil_append]
  obtain ⟨_ | _, i⟩ := l
  · have e := NF.dg_step (pres RD k sc) ν [] [([], .cap (dn i), [])] [] [] (dg_dots_cupUp RD k sc i ν d).symm
      rfl ⟨rfl, rfl⟩ (L := [([], .cup (up i), [])] ++ (List.replicate d ([], .dot (up i), [dn i]) ++
        [([], .cap (dn i), [])])) (L' := cwLs i d) (by simp) (by simp [cwLs])
    have e' : Letter.dual ((false, i) : Letter I) = up i := rfl
    rw [e']
    convert dg_cwLs_isBub (RD := RD) (k := k) (sc := sc) (lam := ν) i d using 1
    exact e
  · have e := NF.dg_step (pres RD k sc) ν [] [([], .cap (up i), [])] [] [] (dg_dots_cupDn RD k sc i ν d).symm
      rfl ⟨rfl, rfl⟩ (L := [([], .cup (dn i), [])] ++ (List.replicate d ([], .dot (dn i), [up i]) ++
        [([], .cap (up i), [])])) (L' := ccwLs i d) (by simp) (by simp [ccwLs])
    have e' : Letter.dual ((true, i) : Letter I) = dn i := rfl
    rw [e']
    convert dg_ccwLs_isBub (RD := RD) (k := k) (sc := sc) (lam := ν) i d using 1
    exact e

omit [DecidableEq I] in
/-- A dot on `B` below the cap (no strands in the block) is a dot on `A` (exact). -/
theorem capBlk_dotB_nil (ν : X) (l : Letter I) (d : ℕ) :
    NF.dg (pres RD k sc) ν [l.dual, l] [] ([([l.dual], .dot l, [])] ++ capBlk [] l d) =
      NF.dg (pres RD k sc) ν [l.dual, l] [] (capBlk [] l (d + 1)) := by
  simp only [capBlk_eq, lmLc, List.map_nil, List.nil_append]
  have e₁ := NF.dg_swap_dots (pres RD k sc) ν [] [] [] l.dual l 1 d
  simp only [List.nil_append, List.append_nil, List.replicate_one] at e₁
  refine (NF.dg_step (pres RD k sc) ν [] [([], .cap l, [])] [] [] e₁ rfl ⟨rfl, rfl⟩ (by simp) rfl).trans ?_
  refine (NF.dg_step (pres RD k sc) ν (List.replicate d ([], .dot l.dual, [l])) [] [] [] (dotCap ν l)
    (by simpa using SChain.replicate d [] l.dual [l]) rfl (by simp) rfl).trans ?_
  rw [List.replicate_succ']
  simp

omit [DecidableEq I] in
/-- Dots on the left leg of a cup equal dots on its right leg. -/
theorem dotsCupL (ν : X) (l : Letter I) (d : ℕ) :
    NF.dg (pres RD k sc) ν [] [l.dual, l] ([([], .cup l.dual, [])] ++ List.replicate d ([], .dot l.dual, [l])) =
      NF.dg (pres RD k sc) ν [] [l.dual, l] ([([], .cup l.dual, [])] ++ List.replicate d ([l.dual], .dot l, [])) := by
  obtain ⟨_ | _, i⟩ := l
  · exact (dg_dots_cupUp RD k sc i ν d).symm
  · exact (dg_dots_cupDn RD k sc i ν d).symm

/-- A cup creating `A` and the first strand of the block is a curl: lower terms. -/
theorem capBlk_cupAs (hr : ∀ i, sc.r i = 1) (ν : X) (S : List (Letter I)) (l : Letter I) (d : ℕ) :
    NF.dg (pres RD k sc) ν (S ++ [l]) (l :: S) ([([], .cup l.dual, S ++ [l])] ++ capBlk (l :: S) l d) ∈
      LeL RD k sc ν (S ++ [l]) (l :: S) S.length := by
  obtain ⟨c, hc⟩ := capPF (RD := RD) (k := k) (sc := sc) hr (wt RD ν S) l l
  simp only [capBlk_eq, lmLc, List.map_append]
  have hcup : SChain [] [([], .cup l.dual, [])] [l.dual, l] := ⟨rfl, by simp⟩
  -- step 1: the cup passes `lmLc S`
  refine mem_of_eq_left (dg_step_free []
      ((xLay l l).map (whL [l.dual] S) ++ List.replicate d ([], .dot l.dual, l :: l :: S) ++
        [([], .cap l, l :: S)]) [] []
      (ichgLoc (RD := RD) (k := k) (sc := sc) _ hcup (sChain_lmLc S l))
      (sChain_ichgL hcup (sChain_lmLc S l)) (sChain_ichgR hcup (sChain_lmLc S l))
      (by simp) (by simp) (by wnf) rfl) ?_
  -- step 2: the dots on `A` pass the crossing
  have hD : SChain [l.dual] (List.replicate d ([], .dot l.dual, [])) [l.dual] := by
    simpa using SChain.replicate d [] l.dual []
  refine mem_of_eq_left (dg_step_free (lmLc S l ++ [([], .cup l.dual, l :: S)])
      [([], .cap l, l :: S)] [] S
      (ichgLoc (RD := RD) (k := k) (sc := sc) _ hD (sChain_xLay l l)).symm
      (sChain_ichgR hD (sChain_xLay l l)) (sChain_ichgL hD (sChain_xLay l l))
      (by simp [xLay_ne_nil]) (by simp [xLay_ne_nil]) (by wnf) rfl) ?_
  -- step 3: the dots move to the other leg of the cup
  refine mem_of_eq_left (dg_step_free (lmLc S l)
      ((xLay l l).map (whL [l.dual] S) ++ [([], .cap l, l :: S)]) [] (l :: S)
      (dotsCupL (RD := RD) (k := k) (sc := sc) _ l d)
      (hcup.append (by simpa using SChain.replicate d [] l.dual [l]))
      (hcup.append (by simpa using SChain.replicate d [l.dual] l []))
      (by simp) (by simp) (by wnf) rfl) ?_
  -- step 4: the dots pass the crossing
  refine mem_of_sub_mem (dg_mod_free (lmLc S l ++ [([], .cup l.dual, l :: S)])
      [([], .cap l, l :: S)] [l.dual] S (leL_sub_comm (ds1rep (RD := RD) (k := k) (sc := sc) hr _ l l d))
      (by simpa using (SChain.replicate d [] l [l]).append (sChain_xLay l l))
      (by simpa using (sChain_xLay l l).append (SChain.replicate d [l] l []))
      (by simp [xLay_ne_nil]) (by simp [xLay_ne_nil]) (by wnf) rfl ?_) ?_
  · simp [ccnt_append, ccnt_lmLc]
  -- step 5: the dots pass the cap
  have hD' : SChain [l] (List.replicate d ([], .dot l, [])) [l] := by
    simpa using SChain.replicate d [] l []
  refine mem_of_eq_left (dg_step_free (lmLc S l ++ [([], .cup l.dual, l :: S)] ++
      (xLay l l).map (whL [l.dual] S)) [] [] S
      (ichgLoc (RD := RD) (k := k) (sc := sc) _ (A := [([], .cap l, [])]) (s := [l.dual, l]) (s' := [])
        ⟨rfl, rfl⟩ hD').symm
      (sChain_ichgR ⟨rfl, rfl⟩ hD') (sChain_ichgL ⟨rfl, rfl⟩ hD')
      (by simp) (by simp) (by wnf) rfl) ?_
  -- step 6: the pitchfork
  refine mem_of_sub_smul_mem (dg_mod_free_smul (lmLc S l ++ [([], .cup l.dual, l :: S)])
      (List.replicate d ([], .dot l, S)) [] S _ (sub_smul_comm_unit c hc)
      (by simpa using ((sChain_xLay l l).whisk [l.dual] []).append
                  (show SChain [l.dual, l, l] [([], .cap l, [l])] [l] from ⟨rfl, rfl⟩))
      (by simpa using ((sChain_xLay l.dual l).whisk [] [l]).append
                  (show SChain [l, l.dual, l] [([l], .cap l, [])] [l] from ⟨rfl, rfl⟩))
      (by simp [xLay_ne_nil]) (by simp [xLay_ne_nil]) (by wnf) rfl ?_) ?_
  · simp [ccnt_append, ccnt_lmLc, ccnt_replicate_dot]
  -- step 7: the curl
  have h := cupCurl (RD := RD) (k := k) (sc := sc) (wt RD ν (l :: S)) l.dual
  simp only [Letter.dual_dual] at h
  refine dg_mem_free (lmLc S l) ([([l], .cap l, S)] ++ List.replicate d ([], .dot l, S)) []
    (l :: S) h (hcup.append (by simpa using sChain_xLay l.dual l)) (by simp) (by wnf) ?_
  simp [ccnt_cons, ccnt_lmLc, ccnt_replicate_dot, Shape.isCross]

omit [DecidableEq I] in
/-- A cup creating the last strand of the block and `B` is a curl: lower terms. -/
theorem capBlk_cupsB (ν : X) (S : List (Letter I)) (l : Letter I) (d : ℕ) :
    NF.dg (pres RD k sc) ν ([l.dual] ++ S) (S ++ [l.dual])
        ([([l.dual] ++ S, .cup l.dual, [])] ++ capBlk (S ++ [l.dual]) l d) ∈
      LeL RD k sc ν ([l.dual] ++ S) (S ++ [l.dual]) S.length := by
  simp only [capBlk_eq, lmLc_snoc, List.map_append]
  have h := cupCurl (RD := RD) (k := k) (sc := sc) (wt RD ν []) l.dual
  simp only [Letter.dual_dual] at h
  refine dg_mem_free [] ((lmLc S l).map (whL [l.dual] [l.dual]) ++
      List.replicate d ([], .dot l.dual, l :: (S ++ [l.dual])) ++ [([], .cap l, S ++ [l.dual])])
      (l.dual :: S) [] h ?_ (by simp) (by wnf) ?_
  · simpa using (show SChain [] [([], .cup l.dual, [])] [l.dual, l] by
      refine ⟨rfl, ?_⟩; simp).append (sChain_xLay l.dual l)
  · simp [ccnt_append, ccnt_map_whL, ccnt_lmLc, ccnt_replicate_dot]

/-- A strand passing below both legs of a cup (pitchfork and Reidemeister 2). -/
theorem cupPF2 (hr : ∀ i, sc.r i = 1) (ν : X) (x m : Letter I) :
    NF.dg (pres RD k sc) ν [m] [m, x, x.dual] ([([], .cup x, [m])] ++ (xLay x.dual m).map (whL [x] []) ++
      (xLay x m).map (whL [] [x.dual])) ∈ LeL RD k sc ν [m] [m, x, x.dual] 1 := by
  obtain ⟨c, hc⟩ := cupPF (RD := RD) (k := k) (sc := sc) hr ν x m
  refine mem_of_sub_smul_mem (dg_mod_free_smul [] ((xLay x m).map (whL [] [x.dual])) [] [] _
    hc ?_ ?_ (by simp) (by simp) (by simp) rfl
    (by simp [ccnt_map_whL])) ?_
  · exact (show SChain [m] [([], .cup x, [m])] [x, x.dual, m] from ⟨rfl, by simp⟩).append
      (by simpa using (sChain_xLay x.dual m).whisk [x] [])
  · exact (show SChain [m] [([m], .cup x, [])] [m, x, x.dual] from ⟨by simp, by simp⟩).append
      (by simpa using (sChain_xLay m x).whisk [] [x.dual])
  refine dg_mem_free [([m], .cup x, [])] [] [] [x.dual] (r2 (RD := RD) (k := k) (sc := sc) hr _ m x)
    ((sChain_xLay m x).append (sChain_xLay x m)) (by simp [xLay_ne_nil]) (by wnf) (by simp)

/-- A cup creating two strands of the block gives lower terms. -/
theorem capBlk_cupSS (hr : ∀ i, sc.r i = 1) (ν : X) (S₁ S₂ : List (Letter I)) (x l : Letter I) (d : ℕ) :
    NF.dg (pres RD k sc) ν ([l.dual] ++ (S₁ ++ S₂) ++ [l]) (S₁ ++ [x, x.dual] ++ S₂)
        ([([l.dual] ++ S₁, .cup x, S₂ ++ [l])] ++ capBlk (S₁ ++ [x, x.dual] ++ S₂) l d) ∈
      LeL RD k sc ν ([l.dual] ++ (S₁ ++ S₂) ++ [l]) (S₁ ++ [x, x.dual] ++ S₂)
        ((S₁ ++ S₂).length + 1) := by
  simp only [capBlk_eq, lmLc_pair, List.map_append]
  refine mem_of_eq_left (dg_step_free []
      ((xLay x.dual l).map (whL (l.dual :: (S₁ ++ [x])) S₂) ++
      (xLay x l).map (whL (l.dual :: S₁) (x.dual :: S₂)) ++
      (lmLc S₁ l).map (whL [l.dual] (x :: x.dual :: S₂)) ++
      List.replicate d ([], .dot l.dual, l :: (S₁ ++ [x, x.dual] ++ S₂)) ++
      [([], .cap l, S₁ ++ [x, x.dual] ++ S₂)]) (l.dual :: S₁) []
      (ichgLoc (RD := RD) (k := k) (sc := sc) _ (A := [([], .cup x, [])]) (s := []) (s' := [x, x.dual])
        ⟨rfl, rfl⟩ (sChain_lmLc S₂ l))
      (sChain_ichgL ⟨rfl, rfl⟩ (sChain_lmLc S₂ l)) (sChain_ichgR ⟨rfl, rfl⟩ (sChain_lmLc S₂ l))
      (by simp) (by simp) (by wnf) rfl) ?_
  refine dg_mem_free ((lmLc S₂ l).map (whL (l.dual :: S₁) []))
      ((lmLc S₁ l).map (whL [l.dual] (x :: x.dual :: S₂)) ++
      List.replicate d ([], .dot l.dual, l :: (S₁ ++ [x, x.dual] ++ S₂)) ++
      [([], .cap l, S₁ ++ [x, x.dual] ++ S₂)]) (l.dual :: S₁) S₂ (cupPF2 (RD := RD) (k := k) (sc := sc) hr _ x l)
    ?_ (by simp) (by wnf) ?_
  · exact ((show SChain [l] [([], .cup x, [l])] [x, x.dual, l] from ⟨rfl, by simp⟩).append
      (by simpa using (sChain_xLay x.dual l).whisk [x] [])).append
      (by simpa using (sChain_xLay x l).whisk [] [x.dual])
  · simp [ccnt_append, ccnt_map_whL, ccnt_lmLc, ccnt_replicate_dot]; try omega

/-- A cup on the right of the block's strands, pushed below a strand moving left across the
block (pitchforks): the strand `l*` of the cup moves right instead. -/
theorem cupThru (hr : ∀ i, sc.r i = 1) (l : Letter I) : ∀ (S : List (Letter I)) (ν : X),
    ∃ c : kˣ, NF.dg (pres RD k sc) ν S (l :: S ++ [l.dual])
        ([(S, .cup l, [])] ++ (lmLc S l).map (whL [] [l.dual])) -
      (c : k) • NF.dg (pres RD k sc) ν S (l :: S ++ [l.dual])
        ([([], .cup l, S)] ++ (lmRc l.dual S).map (whL [l] [])) ∈
      LeL RD k sc ν S (l :: S ++ [l.dual]) (S.length - 1)
  | [], ν => ⟨1, by simp [lmLc, lmRc]⟩
  | [s], ν => by
    obtain ⟨c, hc⟩ := cupPF (RD := RD) (k := k) (sc := sc) hr ν l s
    exact ⟨c⁻¹, by simpa [lmLc, lmRc] using sub_smul_comm_unit c hc⟩
  | s :: s' :: S, ν => by
    obtain ⟨c₁, ih⟩ := cupThru hr l (s' :: S) (wt RD ν [])
    obtain ⟨c₂, hc₂⟩ := cupPF (RD := RD) (k := k) (sc := sc) hr (wt RD ν (s' :: S)) l s
    refine ⟨c₁ * c₂⁻¹, ?_⟩
    have e1 : lmLc (s :: s' :: S) l = (lmLc (s' :: S) l).map (whL [s] []) ++
        (xLay s l).map (whL [] (s' :: S)) := rfl
    have e2 : lmRc l.dual (s :: s' :: S) = (xLay l.dual s).map (whL [] (s' :: S)) ++
        (lmRc l.dual (s' :: S)).map (whL [s] []) := rfl
    have hA := (show SChain (s' :: S) [(s' :: S, .cup l, [])] (s' :: S ++ [l, l.dual]) from
      ⟨by simp, by simp⟩).append (by simpa using (sChain_lmLc (s' :: S) l).whisk [] [l.dual])
    have hB := (show SChain (s' :: S) [([], .cup l, s' :: S)] (l :: l.dual :: s' :: S) from
      ⟨by simp, by simp⟩).append (by simpa using (sChain_lmRc l.dual (s' :: S)).whisk [l] [])
    rw [e1, e2]
    -- step 1: the induction hypothesis
    refine leL_sub_trans (dg_mod_free_smul [] ((xLay s l).map (whL [] (s' :: S ++ [l.dual]))) [s] []
      _ ih hA hB (by simp) (by simp) (by wnf) rfl ?_) ?_
    · simp [ccnt_map_whL]
    -- step 2: the crossing of `s` and `l` passes the strand moving right
    rw [Units.val_mul]
    refine smul_sub_smul_mul_mem _ _ ?_
    refine sub_mem_of_eq_left (dg_step_free [([s], .cup l, s' :: S)] [] [] []
      (ichgLoc (RD := RD) (k := k) (sc := sc) _ (sChain_xLay s l) (sChain_lmRc l.dual (s' :: S))).symm
      (sChain_ichgR (sChain_xLay s l) (sChain_lmRc l.dual (s' :: S)))
      (sChain_ichgL (sChain_xLay s l) (sChain_lmRc l.dual (s' :: S)))
      (by simp [xLay_ne_nil]) (by simp [xLay_ne_nil]) (by wnf) rfl) ?_
    -- step 3: the pitchfork
    refine leL_sub_trans_le (dg_mod_free_smul [] ((lmRc l.dual (s' :: S)).map (whL [l, s] [])) [] (s' :: S)
      _ (sub_smul_comm_unit c₂ hc₂)
      ((show SChain [s] [([s], .cup l, [])] [s, l, l.dual] from ⟨by simp, by simp⟩).append
        (by simpa using (sChain_xLay s l).whisk [] [l.dual]))
      ((show SChain [s] [([], .cup l, [s])] [l, l.dual, s] from ⟨by simp, by simp⟩).append
        (by simpa using (sChain_xLay l.dual s).whisk [l] []))
      (by simp) (by simp) (by wnf) rfl le_rfl) (by simp [ccnt_map_whL, ccnt_lmRc]) ?_
    refine smul_sub_smul_mem _ (leL_sub_of_eq ?_)
    wnf

/-- A cup creating `B` and a strand to the right of the block cancels the cap (zigzag, after
pitchforks): the block becomes the strand `A` moving right across `S`, with `d` dots. -/
theorem capBlk_cupBright (hr : ∀ i, sc.r i = 1) (ν : X) (S : List (Letter I)) (l : Letter I) (d : ℕ) :
    ∃ c : kˣ, NF.dg (pres RD k sc) ν ([l.dual] ++ S) (S ++ [l.dual])
        ([([l.dual] ++ S, .cup l, [])] ++ (capBlk S l d).map (whL [] [l.dual])) -
      (c : k) • NF.dg (pres RD k sc) ν ([l.dual] ++ S) (S ++ [l.dual])
        (List.replicate d ([], .dot l.dual, S) ++ lmRc l.dual S) ∈
      LeL RD k sc ν ([l.dual] ++ S) (S ++ [l.dual]) (S.length - 1) := by
  obtain ⟨c, hc⟩ := cupThru (RD := RD) (k := k) (sc := sc) hr l S (wt RD ν [])
  refine ⟨c, ?_⟩
  simp only [capBlk_eq, List.map_append, List.map_replicate]
  -- step 1: pitchforks
  refine leL_sub_trans (dg_mod_free_smul []
      (List.replicate d (whL [] [l.dual] ([], .dot l.dual, l :: S)) ++
        [whL [] [l.dual] ([], .cap l, S)]) [l.dual] [] _ hc
      ((show SChain S [(S, .cup l, [])] (S ++ [l, l.dual]) from ⟨by simp, by simp⟩).append
        (by simpa using (sChain_lmLc S l).whisk [] [l.dual]))
      ((show SChain S [([], .cup l, S)] (l :: l.dual :: S) from ⟨by simp, by simp⟩).append
        (by simpa using (sChain_lmRc l.dual S).whisk [l] []))
      (by simp) (by simp) (by wnf) rfl ?_) ?_
  · have h1 := ccnt_replicate_dot d [] (l :: S ++ [l.dual]) l.dual
    have h2 := ccnt_single_cap [] (S ++ [l.dual]) l
    simp only [whL] at h1 h2 ⊢
    simp only [List.nil_append, List.cons_append] at h1 h2 ⊢
    rw [ccnt_append, h1, h2]; simp
  -- step 2: the strand moving right passes the dots and the cap
  have hDC : SChain [l.dual, l] (List.replicate d ([], .dot l.dual, [l]) ++ [([], .cap l, [])]) [] :=
    (SChain.replicate d [] l.dual [l]).append ⟨rfl, rfl⟩
  refine smul_sub_smul_mem _ (leL_sub_of_eq ((dg_step_free [([l.dual], .cup l, S)] [] [] []
      (ichgLoc (RD := RD) (k := k) (sc := sc) _ hDC (sChain_lmRc l.dual S)).symm
      (sChain_ichgR hDC (sChain_lmRc l.dual S)) (sChain_ichgL hDC (sChain_lmRc l.dual S))
      (by simp) (by simp) (by wnf) rfl).trans ?_))
  -- step 3: the dots pass the cup
  refine (dg_step_free [] ([([], .cap l, l.dual :: S)] ++ lmRc l.dual S) [] S
      (ichgLoc (RD := RD) (k := k) (sc := sc) _ (A := List.replicate d ([], .dot l.dual, []))
        (s := [l.dual]) (s' := [l.dual]) (B := [([], .cup l, [])]) (t := []) (t' := [l, l.dual])
        (by simpa using SChain.replicate d [] l.dual []) ⟨rfl, rfl⟩).symm
      (sChain_ichgR (by simpa using SChain.replicate d [] l.dual []) ⟨rfl, rfl⟩)
      (sChain_ichgL (by simpa using SChain.replicate d [] l.dual []) ⟨rfl, rfl⟩)
      (by simp) (by simp) (by wnf) rfl).trans ?_
  -- step 4: the zigzag
  refine NF.dg_step (pres RD k sc) ν (List.replicate d ([], .dot l.dual, S)) (lmRc l.dual S) [] S
    (NF.dg_zigR' (pres RD k sc) (wt RD ν S) l) (by simpa using SChain.replicate d [] l.dual S)
    (by simpa using sChain_lmRc l.dual S) (by wnf) (by wnf)

end Categorification.KL3.Diagram.CLQ
