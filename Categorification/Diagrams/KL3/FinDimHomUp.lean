/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.FinDimHom
import Categorification.Diagrams.KL3.KaroubiKLR
import Categorification.KLR.GradedBasis

/-!
# Finite-dimensional graded Hom-spaces of `U`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.2
(Proposition 3.10: `ϕ_{ν,λ} : R(ν) ⊗ Π_λ → END_U(E_ν 1_λ)` is surjective, eq. (3.30), label
`eq_phi_nu_lambda`), §3.2.3 (Corollary 3.14, label `cor-ineq`:
`gdim HOM_U(E_i 1_λ, E_j 1_λ) ≤ π ⟨E_i 1_λ, E_j 1_λ⟩`) and §3.6 ("The space of homs between any
two objects in `U̇(λ, μ)` is a finite-dimensional `k`-vector space. In particular, the
Krull–Schmidt decomposition theorem holds").

The right-hand side of Corollary 3.14 is a Laurent series in `q` (finitely many terms in each
degree, none in sufficiently negative degrees). We prove this consequence directly — the graded
pieces of `HOM_U(E_s 1_μ, E_t 1_μ)` are finite-dimensional and vanish in sufficiently negative
degrees (the library's `Graded.HasGdim`) — but not the explicit bound by the pairing
`π ⟨E_i 1_λ, E_j 1_λ⟩`, and not the statement of Proposition 3.13 that the sets `B_{i,j,λ}` span.

## Main results

* `hasGdim_seq`, `hasGdim_positive`: the graded pieces of `HOM_U(E_i 1_μ, E_j 1_μ)` for upward
  sequences are finite-dimensional and vanish in sufficiently negative degrees: by Proposition
  3.10 they are spanned by the images of the tensor products of the homogeneous basis
  `ψ_{w} x^u 1_i` of `R(ν)` (KL II basis theorem) with the bubble monomials of `Π_μ`, of which
  there are finitely many in each degree and none below a fixed degree.
* `hasGdim_homD`: **for all signed sequences `s`, `t` and weights `μ`, the graded pieces of
  `HOM_U(E_s 1_μ, E_t 1_μ)` are finite-dimensional and vanish in sufficiently negative
  degrees** (simply-laced Cartan data, `I` finite, `k` a field), by the reductions of
  `Categorification.Diagrams.KL3.FinDimHom` (biadjointness and the sorting decomposition `decL`).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Graded KLR.Diagram MatEnd
open scoped TensorProduct

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k]

/-! ## Upward sequences -/

section Upward

variable [DecidableEq I]

/-- The standard reduced words of the permutations. -/
abbrev ρc (ν : Multiset I) : Equiv.Perm (Fin (Multiset.card ν)) → List ℕ :=
  fun w => TypeA.canWord _ w

omit [DecidableEq I] in
theorem hρc (ν : Multiset I) : ∀ w, TypeA.IsReduced (Multiset.card ν) (ρc ν w) ∧
    TypeA.wordProd (Multiset.card ν) (ρc ν w) = w :=
  fun w => ⟨TypeA.isReduced_canWord _ w, TypeA.wordProd_canWord _ w⟩

variable [Finite I]

/-- **Finite-dimensional graded pieces of `HOM_U(E_i 1_μ, E_j 1_μ)`** for sequences
`i, j ∈ Seq ν` (simply-laced, `I` finite): by Proposition 3.10 every 2-morphism is the
`(i, j)`-entry of the image of an element of `R(ν) ⊗ Π_μ`, hence a linear combination of the
images of `b ⊗ m` (`b` in the homogeneous basis of `R(ν)`, `m` a bubble monomial), which are
homogeneous of degree `deg b + deg m`; there are finitely many such pairs in each degree and
none below a fixed degree. -/
theorem hasGdim_seq (hSL : SimplyLaced C) (μ : X) (ν : Multiset I) (i j : KLR.Seq ν) :
    HasGdim (HomD RD k μ (ups (word i)) (ups (word j))) := by
  classical
  let G := KLR.klGradingDatum2 k C
  let bR := KLR.KL2.basis (k := k) (C := C) (ν := ν) (ρc ν) (hρc ν)
  let bT := bR.tensorProduct (MvPolynomial.basisMonomials (I × ℕ) k)
  let ev : MatEnd (objNu RD k μ ν) →ₗ[k]
      ((pres RD k).obj (ob RD μ (ups (word i))) ⟶ (pres RD k).obj (ob RD μ (ups (word j)))) :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let L := ev ∘ₗ (phi RD k μ ν).toLinearMap
  let v := fun p => L (bT p)
  let δ : (KLR.Seq ν × Equiv.Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) ×
      ((I × ℕ) →₀ ℕ) → ℤ := fun p => G.stdDeg (ρc ν) p.1 + Finsupp.weight (wPi C) p.2
  have hv : ∀ p, v p ∈ HomD RD k μ (ups (word i)) (ups (word j)) (δ p) := by
    rintro ⟨b, m⟩
    have hb : toUEnd RD k μ ν (bR b) ∈ matDeg RD k μ ν (G.stdDeg (ρc ν) b) :=
      toUEnd_mem (G.basis_mem_grade _ _ (ρc ν) (hρc ν) b)
    have hm : bubDiag RD k μ ν (bubMap RD k μ (MvPolynomial.monomial m 1)) ∈
        matDeg RD k μ ν (Finsupp.weight (wPi C) m) := by
      rw [bubDiag_apply]
      exact Submodule.sum_mem _ fun l _ => single_mem_matDeg (bubAt_mem μ _ (bubMon_mem μ m))
    have h := mul_mem_matDeg hb hm i j
    simp only [v, L, bT, ev, LinearMap.coe_comp, Function.comp_apply, Basis.tensorProduct_apply,
      MvPolynomial.coe_basisMonomials, AlgHom.toLinearMap_apply, phi_tmul, LinearMap.coe_mk,
      AddHom.coe_mk]
    exact h
  have hspan : ∀ f, f ∈ Submodule.span k (Set.range v) := by
    intro f
    obtain ⟨t, ht⟩ := prop310_of_simplyLaced (k := k) (RD := RD) hSL μ ν (single i j f)
    have hf : f = L t := by
      simp only [L, ev, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        LinearMap.coe_mk, AddHom.coe_mk]
      rw [ht, single_apply_self]
    have hL : L t ∈ LinearMap.range L := ⟨t, rfl⟩
    rw [LinearMap.range_eq_map, ← bT.span_eq, Submodule.map_span, ← Set.range_comp] at hL
    rw [hf]; exact hL
  obtain ⟨B, hB⟩ := G.bddBelow_stdDeg (ρc ν) (fun a => (C.dot_self_pos a).le) Set.univ
  have hB' : ∀ b, B ≤ G.stdDeg (ρc ν) b := fun b => hB ⟨b, trivial, rfl⟩
  have hw : ∀ m : (I × ℕ) →₀ ℕ, 0 ≤ Finsupp.weight (wPi C) m := weight_wPi_nonneg
  refine hasGdim_of_le_span (fun d => v '' {p | δ p = d}) (fun d => ?_)
    (fun d f hf => mem_span_image_of_homogeneous (pres_isHomogeneous (RD := RD) (k := k)) v δ hv
      (hspan f) hf) B (fun d hd => ?_)
  · refine Set.Finite.image _ ?_
    refine ((Finset.Icc B d).finite_toSet.biUnion fun e _ =>
      (G.finite_stdDeg_eq (ρc ν) (fun a => C.dot_self_pos a) e).prod
        (monDeg_finite (C := C) (d - e))).subset ?_
    rintro ⟨b, m⟩ hp
    simp only [Set.mem_setOf_eq, δ] at hp
    simp only [Set.mem_iUnion, Finset.coe_Icc, Set.mem_Icc, Set.mem_prod, Set.mem_setOf_eq]
    have := hB' b
    have := hw m
    exact ⟨G.stdDeg (ρc ν) b, ⟨by omega, by omega⟩, rfl, show _ = _ by omega⟩
  · refine Set.eq_empty_iff_forall_not_mem.2 fun p hp => ?_
    obtain ⟨p, hp', rfl⟩ := hp
    simp only [Set.mem_setOf_eq, δ] at hp'
    have := hB' p.1
    have := hw p.2
    omega

omit [DecidableEq I] [Finite I] in
/-- Upward diagrams do not change the letters of a sequence, up to order. -/
theorem sChain_upward_perm : ∀ {s t : List (Letter I)} {A : List (LayerData I)}, SChain s A t →
    Upward A → s.Perm t
  | s, t, [], h, _ => h ▸ List.Perm.refl _
  | s, t, x :: A, h, hA => by
    obtain ⟨rfl, h'⟩ := h
    refine List.Perm.trans ?_ (sChain_upward_perm h' fun y hy => hA y (List.mem_cons_of_mem _ hy))
    obtain ⟨a, g, b⟩ := x
    have hg : g.isUp = true := hA _ List.mem_cons_self
    cases g with
    | dot l => exact List.Perm.refl _
    | cross ε c d =>
      refine List.Perm.append_right _ (List.Perm.append_left _ ?_)
      exact List.Perm.swap _ _ _
    | cup l => simp [Shape.isUp] at hg
    | cap l => simp [Shape.isUp] at hg

omit [Finite I] in
/-- Between positive sequences which are not permutations of each other there are no
2-morphisms (Lemma 3.9: all 2-morphisms are upward diagrams times bubbles). -/
theorem homD_eq_bot_of_not_perm (hSL : SimplyLaced C) (μ : X) {s t : List (Letter I)}
    (hs : Positive s) (ht : Positive t) (hp : ¬ s.Perm t) (d : ℤ) : HomD RD k μ s t d = ⊥ := by
  have hbot : upSpan RD k μ s t = ⊥ := by
    rw [eq_bot_iff, upSpan, Submodule.span_le]
    rintro _ ⟨A, γ, hA, hc, -, rfl⟩
    exact absurd (sChain_upward_perm hc hA) hp
  rw [eq_bot_iff, homD_eq_span, Submodule.span_le]
  rintro _ ⟨ls, hls, -, rfl⟩
  have := upSpanDiag_of_simplyLaced (RD := RD) (k := k) hSL μ s t ls hs ht hls
  rwa [hbot] at this

omit [DecidableEq I] in
/-- The sequence `Seq ↑l` of a list `l`. -/
def seqOfList (l : List I) : KLR.Seq (l : Multiset I) :=
  ⟨fun a => l.get (Fin.cast (by simp) a), by
    rw [Fin.univ_val_map, ← List.ofFn_congr (by simp) l.get, List.ofFn_get]⟩

omit [DecidableEq I] [Finite I] in
theorem word_seqOfList (l : List I) : word (seqOfList l) = l := by
  show List.ofFn (fun a => l.get (Fin.cast _ a)) = l
  rw [List.ofFn_congr (by simp : Multiset.card (l : Multiset I) = l.length)]
  simp

omit [DecidableEq I] [Finite I] in
theorem word_cast {ν ν' : Multiset I} (h : ν = ν') (q : KLR.Seq ν) : word (h ▸ q) = word q := by
  subst h; rfl

/-- **Finite-dimensional graded pieces of `HOM_U(E_s 1_μ, E_t 1_μ)` for upward sequences**
(simply-laced, `I` finite). -/
theorem hasGdim_positive (hSL : SimplyLaced C) (μ : X) {s t : List (Letter I)} (hs : Positive s)
    (ht : Positive t) : HasGdim (HomD RD k μ s t) := by
  by_cases hp : s.Perm t
  · have ha : ups (s.map Prod.snd) = s := ups_map_snd hs
    have hb : ups (t.map Prod.snd) = t := ups_map_snd ht
    have hν : ((t.map Prod.snd : List I) : Multiset I) = (s.map Prod.snd : List I) :=
      Multiset.coe_eq_coe.2 (hp.map Prod.snd).symm
    have h := hasGdim_seq (RD := RD) (k := k) hSL μ ((s.map Prod.snd : List I) : Multiset I)
      (seqOfList (s.map Prod.snd)) (hν ▸ seqOfList (t.map Prod.snd))
    have e : word (hν ▸ seqOfList (t.map Prod.snd)) = t.map Prod.snd :=
      (word_cast hν _).trans (word_seqOfList _)
    rw [word_seqOfList, e, ha, hb] at h
    exact h
  · exact hasGdim_of_le_span (fun _ => ∅) (fun _ => Set.finite_empty)
      (fun d => by rw [homD_eq_bot_of_not_perm hSL μ hs ht hp d]; exact bot_le) 0
      (fun _ _ => rfl)

end Upward

/-! ## All signed sequences -/

/-- **KL III, finite-dimensional graded Hom-spaces** (the Corollary 3.14-type statement of
§3.2, input of the Krull–Schmidt property of §3.4/§3.8; simply-laced Cartan data, `I` finite,
`k` a field): for all signed sequences `s`, `t` and every weight `μ`, each graded piece of
`HOM_U(E_s 1_μ, E_t 1_μ)` is finite-dimensional, and the graded pieces vanish in sufficiently
negative degrees. -/
theorem hasGdim_homD [DecidableEq I] [Finite I] (hSL : SimplyLaced C) (μ : X)
    (s t : List (Letter I)) : HasGdim (HomD RD k μ s t) := by
  have hsorted : ∀ d c : List I, HasGdim (HomD RD k μ [] (dns d ++ ups c)) := by
    intro d c
    have hpos : Positive (rd (dns d) ++ []) := by
      rw [List.append_nil]; exact positive_rd_dns d
    haveI := hasGdim_positive (RD := RD) (k := k) hSL μ hpos (show Positive (ups c) by
      simp [Positive, ups])
    exact hasGdim_of_bendTgt μ (dns d) [] (ups c)
  haveI := hasGdim_nil_of_sorted hSL μ hsorted (rd s ++ t)
  exact hasGdim_of_bendSrc μ s t

end Categorification.KL3.Diagram
