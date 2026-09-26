/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Lemma39
import Categorification.Algebra.Graded.Dimension

/-!
# Graded Hom-spaces of `U` between arbitrary 1-morphisms: reductions

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2
(Proposition 3.10; Corollary 3.14, label `cor-ineq`, bounds the graded dimensions of the
Hom-spaces by Laurent series), used in §3.6 for the Krull–Schmidt property of `U̇`.

This file contains the reductions of the finiteness of the graded pieces of
`HOM_U(E_s 1_μ, E_t 1_μ)` (finite-dimensional, zero in sufficiently negative degrees; the
library's `Graded.HasGdim`) to the case of upward sequences `s`, `t`:

* `hasGdim_of_bendSrc`: biadjointness (nested cups and caps, `flatL`/`dg_unbend_flat`) reduces
  `HOM(E_s 1_μ, E_t 1_μ)` to `HOM(1_μ, E_{s* t} 1_μ)`;
* `hasGdim_nil_of_sorted`: the decomposition of identities through sorted words (`decL`)
  reduces `HOM(1_μ, E_w 1_μ)` to `HOM(1_μ, F_d E_c 1_μ)`;
* `hasGdim_of_bendTgt`: bending the downward block `F_d` down on the left (`sharpL`,
  `dg_unbend_sharp`) reduces `HOM(1_μ, F_d E_c 1_μ)` to `HOM(E_{d̄} 1_μ, E_c 1_μ)`, a Hom-space
  between upward sequences.

The generic tools are `gdimMaps` (linear maps sending graded pieces into finite-dimensional
subspaces and killing low degrees; closed under linear combinations), `hasGdim_of_retract`, and
the description of the graded pieces of `U` by normal-form diagrams (`homD_eq_span`).
-/

noncomputable section

namespace Categorification

open Graded

/-! ## Linear maps with finite-dimensional graded images -/

section GdimMaps

variable {k : Type*} [Field k] {M N P : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N]
  [Module k N] [AddCommGroup P] [Module k P]

theorem gdimMaps_map_smul_le (p : Submodule k M) (c : k) (φ : M →ₗ[k] N) : p.map (c • φ) ≤ p.map φ := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨c • x, p.smul_mem c hx, by simp⟩

/-- Linear maps `φ : M → N` sending each graded piece `ℳ d` into a finite-dimensional subspace
and killing `ℳ d` for all sufficiently negative `d`. -/
def gdimMaps (ℳ : ℤ → Submodule k M) : Submodule k (M →ₗ[k] N) where
  carrier := {φ | (∀ d, FiniteDimensional k ((ℳ d).map φ)) ∧ ∃ B : ℤ, ∀ d < B, (ℳ d).map φ = ⊥}
  zero_mem' := ⟨fun d => by rw [Submodule.map_zero]; infer_instance,
    0, fun d _ => Submodule.map_zero _⟩
  add_mem' := by
    rintro φ ψ ⟨hφ, B₁, hB₁⟩ ⟨hψ, B₂, hB₂⟩
    refine ⟨fun d => ?_, min B₁ B₂, fun d hd => ?_⟩
    · haveI := hφ d; haveI := hψ d
      exact Submodule.finiteDimensional_of_le (Submodule.map_add_le _ _ _)
    · refine eq_bot_iff.2 ((Submodule.map_add_le _ _ _).trans ?_)
      rw [hB₁ d (lt_of_lt_of_le hd (min_le_left _ _)), hB₂ d (lt_of_lt_of_le hd (min_le_right _ _)),
        sup_bot_eq]
  smul_mem' := by
    rintro c φ ⟨hφ, B, hB⟩
    refine ⟨fun d => ?_, B, fun d hd => eq_bot_iff.2 ((gdimMaps_map_smul_le _ _ _).trans ?_)⟩
    · haveI := hφ d
      exact Submodule.finiteDimensional_of_le (gdimMaps_map_smul_le _ _ _)
    · rw [hB d hd]

theorem mem_gdimMaps {ℳ : ℤ → Submodule k M} {φ : M →ₗ[k] N} :
    φ ∈ gdimMaps ℳ ↔
      (∀ d, FiniteDimensional k ((ℳ d).map φ)) ∧ ∃ B : ℤ, ∀ d < B, (ℳ d).map φ = ⊥ := Iff.rfl

/-- If the identity sends graded pieces into finite-dimensional subspaces and kills low degrees,
the grading has a graded dimension. -/
theorem hasGdim_of_id_mem {ℳ : ℤ → Submodule k M} (h : LinearMap.id ∈ gdimMaps (N := M) ℳ) :
    HasGdim ℳ where
  finiteDimensional d := by
    have := h.1 d
    rwa [Submodule.map_id] at this
  bddBelow := by
    obtain ⟨B, hB⟩ := h.2
    refine ⟨B, fun d hd => ?_⟩
    by_contra hlt
    exact hd (by rw [← Submodule.map_id (ℳ d)]; exact hB d (lt_of_not_le hlt))

/-- A composite `b ∘ a` in which `a` shifts the grading into a grading with a graded dimension
lies in `gdimMaps`. -/
theorem comp_mem_gdimMaps {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N} [HasGdim 𝒩]
    (a : M →ₗ[k] N) (b : N →ₗ[k] P) (c : ℤ) (ha : ∀ d, (ℳ d).map a ≤ 𝒩 (d + c)) :
    b ∘ₗ a ∈ gdimMaps (N := P) ℳ := by
  refine ⟨fun d => ?_, ?_⟩
  · rw [Submodule.map_comp]
    exact Submodule.finiteDimensional_of_le (Submodule.map_mono (ha d))
  · obtain ⟨B, hB⟩ := HasGdim.bddBelow (ℳ := 𝒩)
    refine ⟨B - c, fun d hd => eq_bot_iff.2 ?_⟩
    have h0 : 𝒩 (d + c) = ⊥ := by
      by_contra hne
      have := hB hne
      omega
    rw [Submodule.map_comp]
    refine (Submodule.map_mono (ha d)).trans ?_
    rw [h0, Submodule.map_bot]

/-- **Graded dimensions transfer along retractions with a degree shift.** -/
theorem hasGdim_of_retract {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N} [HasGdim 𝒩]
    (F : M →ₗ[k] N) (G : N →ₗ[k] M) (c : ℤ) (hF : ∀ d, (ℳ d).map F ≤ 𝒩 (d + c))
    (hGF : ∀ x, G (F x) = x) : HasGdim ℳ := by
  refine hasGdim_of_id_mem ?_
  have h := comp_mem_gdimMaps F G c hF
  rwa [show G ∘ₗ F = LinearMap.id from LinearMap.ext hGF] at h

/-- A grading whose pieces lie in spans of finite sets of vectors, empty in low degrees, has a
graded dimension. -/
theorem hasGdim_of_le_span {ℳ : ℤ → Submodule k M} (S : ℤ → Set M) (hS : ∀ d, (S d).Finite)
    (hle : ∀ d, ℳ d ≤ Submodule.span k (S d)) (B : ℤ) (hB : ∀ d < B, S d = ∅) : HasGdim ℳ where
  finiteDimensional d := by
    haveI := FiniteDimensional.span_of_finite k (hS d)
    exact Submodule.finiteDimensional_of_le (hle d)
  bddBelow := by
    refine ⟨B, fun d hd => ?_⟩
    by_contra hlt
    exact hd (eq_bot_iff.2 ((hle d).trans (by rw [hB d (lt_of_not_le hlt), Submodule.span_empty])))

end GdimMaps

end Categorification

namespace Categorification

open CategoryTheory StringDiagrams Graded

/-! ## Graded pieces of presented categories -/

section Pres

variable {S : Signature} {R : Type*} [CommRing R] {P : Presentation S R} {deg : S.Gen → ℤ}

/-- The degree-`d` part of a Hom-space of a presented category is spanned by the classes of the
diagrams of degree `d`. -/
theorem homDeg_eq_span_diag (P : Presentation S R) (deg : S.Gen → ℤ) (a b : Obj S) (d : ℤ) :
    P.homDeg deg a b d = Submodule.span R (P.diag '' {g : a ⟶ b | Diagram.degree deg g = d}) := by
  rw [Presentation.homDeg, LinDiagram.homDeg, Finsupp.supported_eq_span_single, Submodule.map_span,
    Set.image_image]
  congr 1

/-- **Graded pieces of spans of homogeneous families**: if `x` of degree `d` is a linear
combination of homogeneous elements `v i` of degrees `δ i`, it is a linear combination of those
of degree `d`. -/
theorem mem_span_image_of_homogeneous (hP : P.IsHomogeneous deg) {a b : Obj S} {ι : Type*}
    (v : ι → (P.obj a ⟶ P.obj b)) (δ : ι → ℤ) (hv : ∀ i, v i ∈ P.homDeg deg a b (δ i))
    {x : P.obj a ⟶ P.obj b} (hx : x ∈ Submodule.span R (Set.range v)) {d : ℤ}
    (hxd : x ∈ P.homDeg deg a b d) : x ∈ Submodule.span R (v '' {i | δ i = d}) := by
  rw [← Presentation.homogeneousComponent_of_mem hP hxd]
  clear hxd
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    by_cases h : δ i = d
    · rw [Presentation.homogeneousComponent_of_mem hP (h ▸ hv i)]
      exact Submodule.subset_span ⟨i, h, rfl⟩
    · rw [Presentation.homogeneousComponent_of_mem_of_ne hP (hv i) h]
      exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [map_smul]; exact Submodule.smul_mem _ r hy

end Pres

namespace KL3.Diagram

open QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k]

/-! ## Degrees of normal-form diagrams -/

variable (RD) in
/-- The degree of the normal-form diagram with layers `ls` and rightmost region `μ`. -/
def sdegSum (μ : X) (ls : List (LayerData I)) : ℤ :=
  (ls.map fun x => sdeg RD (wt RD μ x.2.2) x.2.1).sum

variable (RD k) in
/-- The degree-`d` part of `HOM_U(E_s 1_μ, E_t 1_μ)`. -/
abbrev HomD (μ : X) (s t : List (Letter I)) (d : ℤ) :
    Submodule k ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :=
  (pres RD k).homDeg (deg RD) (ob RD μ s) (ob RD μ t) d

@[simp] theorem sdegSum_nil (μ : X) : sdegSum RD μ [] = 0 := rfl

theorem sdegSum_append (μ : X) (a b : List (LayerData I)) :
    sdegSum RD μ (a ++ b) = sdegSum RD μ a + sdegSum RD μ b := by
  simp [sdegSum]

theorem sdegSum_map_whL (μ : X) (u v : List (Letter I)) (A : List (LayerData I)) :
    sdegSum RD μ (A.map (whL u v)) = sdegSum RD (wt RD μ v) A := by
  simp [sdegSum, whL_def, Function.comp_def, wt_append]

/-- **The graded pieces of `U` are spanned by normal-form diagrams.** -/
theorem homD_eq_span (μ : X) (s t : List (Letter I)) (d : ℤ) :
    HomD RD k μ s t d = Submodule.span k
      {f | ∃ ls, SChain s ls t ∧ sdegSum RD μ ls = d ∧ f = dg RD k μ s t ls} := by
  rw [HomD, homDeg_eq_span_diag]
  congr 1
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨ls, hls, rfl⟩ := exists_mkD RD μ g
    exact ⟨ls, hls, by rw [← hg, degree_mkD]; rfl, (dg_of hls).symm⟩
  · rintro ⟨ls, hls, hd, rfl⟩
    exact ⟨mkD RD μ ls hls, by show Diagram.degree _ _ = d; rw [degree_mkD]; exact hd,
      (dg_of hls).symm⟩

theorem dg_mem_homD {μ : X} {s t : List (Letter I)} {ls : List (LayerData I)} {d : ℤ}
    (h : sdegSum RD μ ls = d) : dg RD k μ s t ls ∈ HomD RD k μ s t d := by
  by_cases hc : SChain s ls t
  · rw [dg_of hc]
    exact diag_mem_homDeg' (by rw [degree_mkD]; exact h)
  · rw [dg_of_not hc]
    exact Submodule.zero_mem _

/-- A linear map which shifts the degrees of all normal-form diagrams by `c` is graded of
degree `c`. -/
theorem map_homD_le {μ μ' : X} {s t s' t' : List (Letter I)}
    (Φ : ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) →ₗ[k]
      ((pres RD k).obj (ob RD μ' s') ⟶ (pres RD k).obj (ob RD μ' t'))) (c : ℤ)
    (h : ∀ ls, SChain s ls t → Φ (dg RD k μ s t ls) ∈ HomD RD k μ' s' t' (sdegSum RD μ ls + c))
    (d : ℤ) : (HomD RD k μ s t d).map Φ ≤ HomD RD k μ' s' t' (d + c) := by
  rw [homD_eq_span, Submodule.map_span_le]
  rintro _ ⟨ls, hls, rfl, rfl⟩
  exact h ls hls

/-- **Rewriting in context is graded**, of the degree of the context. -/
theorem map_ctxL_le (μ : X) {s₀ t₀ : List (Letter I)} {pre : List (LayerData I)}
    {u v : List (Letter I)} {post : List (LayerData I)} {s t : List (Letter I)}
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀) (d : ℤ) :
    (HomD RD k (wt RD μ v) s t d).map (ctxL RD k μ s₀ t₀ pre u v post s t) ≤
      HomD RD k μ s₀ t₀ (d + (sdegSum RD μ pre + sdegSum RD μ post)) := by
  refine map_homD_le _ _ (fun ls _ => ?_) d
  rw [ctxL_dg RD k μ hpre hpost]
  refine dg_mem_homD ?_
  rw [sdegSum_append, sdegSum_append, sdegSum_map_whL]; ring

theorem ctxL_mem (μ : X) {s₀ t₀ : List (Letter I)} {pre : List (LayerData I)}
    {u v : List (Letter I)} {post : List (LayerData I)} {s t : List (Letter I)}
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀) {d : ℤ}
    {f : (pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t)}
    (hf : f ∈ HomD RD k (wt RD μ v) s t d) :
    ctxL RD k μ s₀ t₀ pre u v post s t f ∈
      HomD RD k μ s₀ t₀ (d + (sdegSum RD μ pre + sdegSum RD μ post)) :=
  map_ctxL_le μ hpre hpost d ⟨f, hf, rfl⟩

/-- Endomorphisms of `1_μ` placed on the far right keep their degree. -/
theorem bubAt_mem (μ : X) (s : List (Letter I)) {β : End ((pres RD k).obj (ob RD μ []))} {d : ℤ}
    (hβ : β ∈ HomD RD k μ [] [] d) : bubAt RD k μ s β ∈ HomD RD k μ s s d := by
  have := ctxL_mem (RD := RD) (k := k) μ (s₀ := s) (t₀ := s) (pre := []) (u := s) (v := [])
    (post := []) (s := []) (t := []) (show s = s ++ [] ++ [] by simp)
    (show s ++ [] ++ [] = s by simp) hβ
  simpa using this

/-- The bubble monomials have the degrees of eq. (3.24). -/
theorem bubMon_mem (μ : X) (s : (I × ℕ) →₀ ℕ) :
    bubMon RD k μ s ∈ HomD RD k μ [] [] (Finsupp.weight (wPi C) s) :=
  mem_HDo.1 (bubMap_monomial_mem (RD := RD) (k := k) μ s 1)

/-- The image of `Π_μ` is spanned by the bubble monomials. -/
theorem isBub_mem_span {μ : X} {δ : End ((pres RD k).obj (ob RD μ []))} (h : IsBub RD k μ δ) :
    δ ∈ Submodule.span k (Set.range (bubMon RD k μ)) := by
  obtain ⟨p, hp⟩ := h
  have e : δ = (bubMap RD k μ p).val := (congrArg EndOne.val hp).symm
  rw [e, p.as_sum, map_sum]
  simp only [EndOne.val]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [← mul_one (p.coeff s), ← smul_eq_mul, ← MvPolynomial.smul_monomial, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

/-! ## Bending -/

/-- **Bending the source up on the left** (biadjointness, KL III (3.1)–(3.2)): if the graded
pieces of `HOM(1_μ, E_{s* t} 1_μ)` are finite-dimensional and vanish in low degrees, so do those
of `HOM(E_s 1_μ, E_t 1_μ)` (`s* = rd s`). -/
theorem hasGdim_of_bendSrc (μ : X) (s t : List (Letter I))
    [HasGdim (HomD RD k μ [] (rd s ++ t))] : HasGdim (HomD RD k μ s t) := by
  have hpre : SChain [] (cupA (rd s)) (rd s ++ s ++ []) := by simpa using sChain_cupA (rd s)
  have hpostF : SChain (rd s ++ t ++ []) [] (rd s ++ t) := by simp
  have hpreG : SChain s [] (s ++ [] ++ []) := by simp
  have hpostG : SChain (s ++ (rd s ++ t) ++ []) ((capA (rd s)).map (whL [] t)) t := by
    simpa using (sChain_capA (rd s)).whisk [] t
  let F := ctxL RD k μ [] (rd s ++ t) (cupA (rd s)) (rd s) [] [] s t
  let G := ctxL RD k μ s t [] s [] ((capA (rd s)).map (whL [] t)) [] (rd s ++ t)
  have key : G.comp F = LinearMap.id := by
    refine hom_ext_dg RD k μ _ _ (fun A hA => ?_)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, F, G]
    erw [ctxL_dg_nil RD k μ hpre hpostF, ctxL_dg_nil RD k μ hpreG hpostG]
    have e := dg_unbend_flat (RD := RD) (k := k) (rd s) [] [] t (M := A) (by simpa using hA) μ
    rw [rd_rd, rd_nil] at e
    repeat rw [List.append_nil] at e
    refine Eq.trans (dg_list_eq ?_) e
    simp [flatL]
  exact hasGdim_of_retract (𝒩 := HomD RD k μ [] (rd s ++ t)) F G _
    (fun d => map_ctxL_le μ hpre hpostF d) (fun f => LinearMap.congr_fun key f)

/-- **Bending a block on the left of the target down** (biadjointness): if the graded pieces of
`HOM(E_{p* x} 1_μ, E_y 1_μ)` are finite-dimensional and vanish in low degrees, so do those of
`HOM(E_x 1_μ, E_{p y} 1_μ)`. -/
theorem hasGdim_of_bendTgt (μ : X) (p x y : List (Letter I))
    [HasGdim (HomD RD k μ (rd p ++ x) y)] : HasGdim (HomD RD k μ x (p ++ y)) := by
  have hpreF : SChain (rd p ++ x) [] (rd p ++ x ++ []) := by simp
  have hpostF : SChain (rd p ++ (p ++ y) ++ []) ((capA p).map (whL [] y)) y := by
    simpa using (sChain_capA p).whisk [] y
  have hpreG : SChain x ((cupA p).map (whL [] x)) (p ++ (rd p ++ x) ++ []) := by
    simpa using (sChain_cupA p).whisk [] x
  have hpostG : SChain (p ++ y ++ []) [] (p ++ y) := by simp
  let F := ctxL RD k μ (rd p ++ x) y [] (rd p) [] ((capA p).map (whL [] y)) x (p ++ y)
  let G := ctxL RD k μ x (p ++ y) ((cupA p).map (whL [] x)) p [] [] (rd p ++ x) y
  have key : G.comp F = LinearMap.id := by
    refine hom_ext_dg RD k μ _ _ (fun M hM => ?_)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, F, G]
    erw [ctxL_dg_nil RD k μ hpreF hpostF, ctxL_dg_nil RD k μ hpreG hpostG]
    have e := dg_unbend_sharp (RD := RD) (k := k) p [] x y (M := M) (by simpa using hM) μ
    repeat rw [List.append_nil] at e
    refine Eq.trans (dg_list_eq ?_) e
    simp [sharpL]
  exact hasGdim_of_retract (𝒩 := HomD RD k μ (rd p ++ x) y) F G _
    (fun d => map_ctxL_le μ hpreF hpostF d) (fun f => LinearMap.congr_fun key f)

/-! ## Sorting -/

/-- **Reduction to sorted words** (the decomposition `decL` of the identity of `E_w 1_μ` through
words `F_d E_c 1_μ`, simply-laced): if the graded pieces of all `HOM(1_μ, F_d E_c 1_μ)` are
finite-dimensional and vanish in low degrees, so do those of `HOM(1_μ, E_w 1_μ)`. -/
theorem hasGdim_nil_of_sorted (hSL : SimplyLaced C) (μ : X)
    (h : ∀ d c : List I, HasGdim (HomD RD k μ [] (dns d ++ ups c))) (w : List (Letter I)) :
    HasGdim (HomD RD k μ [] w) := by
  let Φ : End ((pres RD k).obj (ob RD μ w)) →ₗ[k]
      (((pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ w)) →ₗ[k]
        ((pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ w))) :=
    (Linear.comp (S := k) (C := (pres RD k).Presented) _ _ _).flip
  have hΦ : ∀ g f, Φ g f = f ≫ g := fun _ _ => rfl
  have hT : decLSet RD k μ w ≤ (gdimMaps (N := (pres RD k).obj (ob RD μ []) ⟶
      (pres RD k).obj (ob RD μ w)) (HomD RD k μ [] w)).comap Φ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨d, c, P, Q, δ, -, hcP, -, hcQ, hδ, rfl⟩
    let Ψ := Φ ∘ₗ (Linear.rightComp k _ (dg RD k μ w (dns d ++ ups c) P ≫
      dg RD k μ (dns d ++ ups c) w Q)) ∘ₗ bubAt RD k μ w
    change δ ∈ (gdimMaps (HomD RD k μ [] w)).comap Ψ
    refine Submodule.span_le.2 ?_ (isBub_mem_span hδ)
    rintro _ ⟨m, rfl⟩
    haveI := h d c
    have e : Ψ (bubMon RD k μ m) = (Linear.rightComp k _ (dg RD k μ (dns d ++ ups c) w Q)) ∘ₗ
        (Linear.rightComp k _ (bubAt RD k μ w (bubMon RD k μ m) ≫
          dg RD k μ w (dns d ++ ups c) P)) := by
      ext f
      change f ≫ (bubAt RD k μ w (bubMon RD k μ m) ≫ (dg RD k μ w (dns d ++ ups c) P ≫
        dg RD k μ (dns d ++ ups c) w Q)) = (f ≫ (bubAt RD k μ w (bubMon RD k μ m) ≫
          dg RD k μ w (dns d ++ ups c) P)) ≫ dg RD k μ (dns d ++ ups c) w Q
      simp only [Category.assoc]
    change Ψ (bubMon RD k μ m) ∈ gdimMaps (HomD RD k μ [] w)
    rw [e]
    refine comp_mem_gdimMaps (𝒩 := HomD RD k μ [] (dns d ++ ups c)) _ _
      (Finsupp.weight (wPi C) m + sdegSum RD μ P) (fun e => ?_)
    rintro _ ⟨f, hf, rfl⟩
    rw [Linear.rightComp_apply]
    exact Presentation.comp_mem_homDeg hf (Presentation.comp_mem_homDeg
      (bubAt_mem μ w (bubMon_mem μ m)) (dg_mem_homD rfl))
  have h1 := hT (decL (RD := RD) (k := k) hSL μ (invL w + 1) w (Nat.lt_succ_self _))
  refine hasGdim_of_id_mem ?_
  have e : Φ (𝟙 _) = LinearMap.id := by ext f; simp [hΦ]
  rw [← e]
  exact h1

end KL3.Diagram

end Categorification
