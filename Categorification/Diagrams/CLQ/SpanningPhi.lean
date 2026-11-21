/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.Spanning
import Categorification.Diagrams.KL3.SpanningPhi

/-!
# The homomorphism `ϕ_{ν,λ} : R(ν) ⊗ Π_λ → END_U(E_ν 1_λ)`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.2
("Homs between `E_i 1_λ` and `E_j 1_λ` for positive `i` and `j`"): eq. (3.28) (the maps
`ϕ_{i,j,λ} : jR(ν)i ⊗ Π_λ → HOM_U(E_i 1_λ, E_j 1_λ)`), Lemma 3.9 (label `lem_surjective`),
eq. (3.30) and Proposition 3.10 (the sum `ϕ_{ν,λ}` over `i, j ∈ Seq(ν)` is a surjective
homomorphism of graded algebras).

KL III: "Adding upward orientations to a diagram `D` in `R(ν)`, placing it to the left of a
collection of bubbles representing a monomial in `Π_λ` ... induces a grading-preserving
`k`-linear map". Here:

* `bubAt μ s β` places an endomorphism `β` of `1_μ` to the right of the strands `s`
  (rightmost region `μ`); it is an algebra homomorphism (`bubAt_comp`, `bubAt_id`) with central
  image: `bubAt s β ≫ f = f ≫ bubAt t β` for every 2-morphism `f : E_s 1_μ → E_t 1_μ`
  (`bubAt_comm`, interchange law);
* `bubDiag μ ν` is the resulting algebra homomorphism from `END_U(1_μ)` to the matrix algebra
  `END_U(E_ν 1_μ) = ⨁_{i,j ∈ Seq ν} HOM_U(E_i 1_μ, E_j 1_μ)`, with central image
  (`bubDiag_central`);
* `phi μ ν : R(ν) ⊗ Π_μ →ₐ END_U(E_ν 1_μ)` is `ϕ_{ν,μ}` of eq. (3.30), the tensor product of
  `toUEnd` (upward diagrams, `Categorification.Diagrams.KL3.Upward`) and `bubDiag ∘ bubMap`.

`Prop310` is the statement of Proposition 3.10 (surjectivity of `phi`); it is proved, for
every Cartan datum, in `Categorification.Diagrams.KL3.Lemma39` (`prop310`). What is proved is the step "Bubble sliding rules
allow moving bubbles to the far right of the diagram" of KL III's proof of Lemma 3.9:
`slideOutUp` (an element of the image of `Π` inserted in any region of an upward diagram is a
linear combination of upward diagrams followed by bubble monomials on the far right).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
open scoped TensorProduct

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-! ## Endomorphisms of `1_μ` placed on the far right -/

section BubAt

variable (μ : X)

/-- An endomorphism of `1_μ` placed to the right of the strands `s` (rightmost region `μ`). -/
def bubAt (s : List (Letter I)) :
    End ((pres RD k sc).obj (ob RD μ [])) →ₗ[k] End ((pres RD k sc).obj (ob RD μ s)) :=
  ctxL RD k sc μ s s [] s [] [] [] []

theorem bubAt_dg (s : List (Letter I)) (B : List (LayerData I)) :
    bubAt RD k sc μ s (dg RD k sc μ [] [] B) = dg RD k sc μ s s (B.map (whL s [])) := by
  have := ctxL_dg RD k sc μ (s₀ := s) (t₀ := s) (pre := []) (u := s) (v := []) (post := [])
    (s := []) (t := []) (show s = s ++ [] ++ [] by simp) (show s ++ [] ++ [] = s by simp) B
  convert this using 1 <;> first | rfl | simp

theorem bubAt_comm_dg {s t : List (Letter I)} (β : End ((pres RD k sc).obj (ob RD μ [])))
    (A : List (LayerData I)) (hA : SChain s A t) :
    bubAt RD k sc μ s β ≫ dg RD k sc μ s t A = dg RD k sc μ s t A ≫ bubAt RD k sc μ t β := by
  have key := hom_ext_dg RD k sc μ (s := []) (t := [])
    ((Linear.rightComp k _ (dg RD k sc μ s t A)).comp (bubAt RD k sc μ s))
    ((Linear.leftComp k _ (dg RD k sc μ s t A)).comp (bubAt RD k sc μ t)) (fun B hB => ?_)
  · exact LinearMap.congr_fun key β
  change bubAt RD k sc μ s (dg RD k sc μ [] [] B) ≫ dg RD k sc μ s t A =
    dg RD k sc μ s t A ≫ bubAt RD k sc μ t (dg RD k sc μ [] [] B)
  have hBs : SChain s (B.map (whL s [])) s := by simpa using hB.whisk s []
  have hBt : SChain t (B.map (whL t [])) t := by simpa using hB.whisk t []
  rw [bubAt_dg, bubAt_dg, dg_comp hBs hA, dg_comp hA hBt]
  have e := dg_closed_left (RD := RD) (k := k) μ (S := s) (T := t) [] [] (s := s) (s' := t) []
    hB hA
  wnf at e
  exact e.symm

/-- **Bubbles on the far right are central** (interchange law): for every 2-morphism
`f : E_s 1_μ → E_t 1_μ`, `bubAt s β ≫ f = f ≫ bubAt t β`. -/
theorem bubAt_comm {s t : List (Letter I)} (β : End ((pres RD k sc).obj (ob RD μ [])))
    (f : (pres RD k sc).obj (ob RD μ s) ⟶ (pres RD k sc).obj (ob RD μ t)) :
    bubAt RD k sc μ s β ≫ f = f ≫ bubAt RD k sc μ t β := by
  have key := hom_ext_dg RD k sc μ (s := s) (t := t)
    (Linear.leftComp k _ (bubAt RD k sc μ s β)) (Linear.rightComp k _ (bubAt RD k sc μ t β))
    (fun A hA => bubAt_comm_dg RD k sc μ β A hA)
  exact LinearMap.congr_fun key f

theorem bubAt_id (s : List (Letter I)) : bubAt RD k sc μ s (𝟙 _) = 𝟙 _ := by
  rw [← dg_nil (RD := RD) (k := k) μ [], bubAt_dg RD k sc μ s [], List.map_nil, dg_nil]

theorem bubAt_comp (s : List (Letter I)) (β γ : End ((pres RD k sc).obj (ob RD μ []))) :
    bubAt RD k sc μ s (β ≫ γ) = bubAt RD k sc μ s β ≫ bubAt RD k sc μ s γ := by
  have key := hom_ext_dg RD k sc μ (s := []) (t := [])
    ((bubAt RD k sc μ s).comp (Linear.rightComp k _ γ))
    ((Linear.rightComp k _ (bubAt RD k sc μ s γ)).comp (bubAt RD k sc μ s)) (fun B hB => ?_)
  · exact LinearMap.congr_fun key β
  change bubAt RD k sc μ s (dg RD k sc μ [] [] B ≫ γ) = bubAt RD k sc μ s (dg RD k sc μ [] [] B) ≫ _
  have key' := hom_ext_dg RD k sc μ (s := []) (t := [])
    ((bubAt RD k sc μ s).comp (Linear.leftComp k _ (dg RD k sc μ [] [] B)))
    ((Linear.leftComp k _ (bubAt RD k sc μ s (dg RD k sc μ [] [] B))).comp (bubAt RD k sc μ s))
    (fun G hG => ?_)
  · exact LinearMap.congr_fun key' γ
  change bubAt RD k sc μ s (dg RD k sc μ [] [] B ≫ dg RD k sc μ [] [] G) =
    bubAt RD k sc μ s (dg RD k sc μ [] [] B) ≫ bubAt RD k sc μ s (dg RD k sc μ [] [] G)
  have hBs : SChain s (B.map (whL s [])) s := by simpa using hB.whisk s []
  have hGs : SChain s (G.map (whL s [])) s := by simpa using hG.whisk s []
  rw [dg_comp hB hG, bubAt_dg RD k sc μ s _, bubAt_dg RD k sc μ s _,
    bubAt_dg RD k sc μ s _, dg_comp hBs hGs, List.map_append]

end BubAt

/-! ## Upward diagrams with bubbles: moving the bubbles to the far right -/





section UpSpan

variable (μ : X)

/-- The span of the upward diagrams followed by bubble monomials on the far right. -/
def upSpan (S T : List (Letter I)) :
    Submodule k ((pres RD k sc).obj (ob RD μ S) ⟶ (pres RD k sc).obj (ob RD μ T)) :=
  Submodule.span k {f | ∃ (A : List (LayerData I)) (γ : End ((pres RD k sc).obj (ob RD μ []))),
    Upward A ∧ SChain S A T ∧ IsBub RD k sc μ γ ∧ f = dg RD k sc μ S T A ≫ bubAt RD k sc μ T γ}


/-- **Bubbles slide to the far right of upward diagrams** (KL III, proof of Lemma 3.9: "Bubble
sliding rules allow moving bubbles to the far right of the diagram"): an element of the image of
`Π` inserted in any region of an upward diagram is a linear combination of upward diagrams
followed by bubble monomials on the far right. -/
theorem slideOutUp : ∀ (v u : List (Letter I)) {S T : List (Letter I)}
    (pre post : List (LayerData I)), SChain S pre (u ++ v) → SChain (u ++ v) post T →
    Upward pre → Upward post → Positive v →
    ∀ β : End ((pres RD k sc).obj (ob RD (wt RD μ v) [])), IsBub RD k sc (wt RD μ v) β →
      ctxL RD k sc μ S T pre u v post [] [] β ∈ upSpan RD k sc μ S T := by
  intro v
  induction v with
  | nil =>
    intro u S T pre post hpre hpost hupre hupost _ β hβ
    have hpp : SChain S (pre ++ post) T := hpre.append hpost
    have key := hom_ext_dg RD k sc (wt RD μ []) (s := []) (t := [])
      (ctxL RD k sc μ S T pre u [] post [] [])
      (Linear.leftComp k _ (dg RD k sc μ S T (pre ++ post)) ∘ₗ bubAt RD k sc μ T) (fun B hB => ?_)
    · rw [LinearMap.congr_fun key β]
      exact Submodule.subset_span ⟨pre ++ post, β, hupre.append hupost, hpp, hβ, rfl⟩
    rw [ctxL_dg RD k sc μ (by simpa using hpre) (by simpa using hpost)]
    change _ = dg RD k sc μ S T (pre ++ post) ≫ bubAt RD k sc μ T (dg RD k sc μ [] [] B)
    have hBT : SChain T (B.map (whL T [])) T := by simpa using hB.whisk T []
    rw [bubAt_dg, dg_comp hpp hBT]
    have e := dg_closed_left (RD := RD) (k := k) μ (S := S) (T := T) pre [] (s := u) (s' := T) []
      hB (by simpa using hpost)
    wnf at e
    wnf
    exact e.symm
  | cons l v' ih =>
    intro u S T pre post hpre hpost hupre hupost hv β hβ
    rw [ctxL_cons RD k sc μ hpre hpost]
    have hmem := bubLU_mem_slideSetR_gen (wt RD μ v') l (β := β) hβ
    generalize bubLU RD k sc (wt RD μ v') l β = f at hmem ⊢
    induction hmem using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, γ, hγ, rfl⟩ := hf
      rw [ctxL_dots_bubRU RD k sc μ hpre hpost]
      have hrep' : SChain (u ++ l :: v') (List.replicate a (u, .dot l, v')) (u ++ l :: v') :=
        SChain.replicate_of ⟨by simp, by simp⟩ a
      have hup : Upward (List.replicate a (u, Shape.dot l, v')) := by
        intro x hx
        rw [List.eq_of_mem_replicate hx]
        exact hv l List.mem_cons_self
      exact ih (u ++ [l]) _ post (by simpa using hpre.append hrep') (by simpa using hpost)
        (hupre.append hup) hupost (fun l' hl' => hv l' (List.mem_cons_of_mem _ hl')) γ hγ
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

end UpSpan

/-! ## `END_U(1_μ) → END_U(E_ν 1_μ)` -/

section BubDiag

open KLR.Diagram MatEnd

variable [DecidableEq I] (μ : X) (ν : Multiset I)

/-- The objects `E_i 1_μ`, `i ∈ Seq ν` (upward strands). -/
abbrev objNu : KLR.Seq ν → (pres RD k sc).Presented := fun i => (pres RD k sc).obj (ob RD μ (ups (word i)))

/-- An endomorphism of `1_μ` placed on the far right of every `E_i 1_μ`, `i ∈ Seq ν`: a diagonal
element of `END_U(E_ν 1_μ)`. -/
def bubDiag : EndOne RD k sc μ →ₐ[k] MatEnd (objNu RD k sc μ ν) where
  toFun β := ∑ i, single i i (bubAt RD k sc μ (ups (word i)) β.val)
  map_one' := by
    rw [one_eq_sum_single]
    exact Finset.sum_congr rfl fun i _ => by rw [EndOne.val_one, bubAt_id]
  map_mul' β γ := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [single_mul_single, EndOne.val_mul, bubAt_comp]
    · intro j _ hj
      exact single_mul_single_of_ne _ _ hj
    · simp
  map_zero' := by simp
  map_add' β γ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [EndOne.val_add, map_add, single_add]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [one_eq_sum_single, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [EndOne.val_smul, EndOne.val_one, map_smul, bubAt_id, single_smul]

theorem bubDiag_apply (β : EndOne RD k sc μ) :
    bubDiag RD k sc μ ν β = ∑ i, single i i (bubAt RD k sc μ (ups (word i)) β.val) := rfl

theorem bubDiag_mul_single (β : EndOne RD k sc μ) (i j : KLR.Seq ν) (f : objNu RD k sc μ ν i ⟶ objNu RD k sc μ ν j) :
    bubDiag RD k sc μ ν β * single i j f = single i j (f ≫ bubAt RD k sc μ (ups (word j)) β.val) := by
  rw [bubDiag_apply, Finset.sum_mul, Finset.sum_eq_single j]
  · exact single_mul_single i j j f _
  · intro m _ hm
    exact single_mul_single_of_ne _ _ (Ne.symm hm)
  · simp

theorem single_mul_bubDiag (β : EndOne RD k sc μ) (i j : KLR.Seq ν) (f : objNu RD k sc μ ν i ⟶ objNu RD k sc μ ν j) :
    single i j f * bubDiag RD k sc μ ν β = single i j (bubAt RD k sc μ (ups (word i)) β.val ≫ f) := by
  rw [bubDiag_apply, Finset.mul_sum, Finset.sum_eq_single i]
  · exact single_mul_single i i j _ f
  · intro m _ hm
    exact single_mul_single_of_ne _ _ hm
  · simp

/-- **The image of `END_U(1_μ)` in `END_U(E_ν 1_μ)` is central.** -/
theorem bubDiag_central (β : EndOne RD k sc μ) (M : MatEnd (objNu RD k sc μ ν)) :
    bubDiag RD k sc μ ν β * M = M * bubDiag RD k sc μ ν β := by
  rw [eq_sum_single M, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bubDiag_mul_single, single_mul_bubDiag, bubAt_comm]

/-- **KL III eq. (3.30)**: `ϕ_{ν,μ} : R(ν) ⊗ Π_μ → END_U(E_ν 1_μ)`, placing upward diagrams of
`R(ν)` to the left of bubble monomials. -/
def phi : KLR.KLRAlgebra k (CL.qCL sc) ν ⊗[k] PiLam I k →ₐ[k] MatEnd (objNu RD k sc μ ν) :=
  Algebra.TensorProduct.lift (toUEnd RD k sc μ ν) ((bubDiag RD k sc μ ν).comp (bubMap RD k sc μ))
    fun _ _ => (bubDiag_central RD k sc μ ν _ _).symm

theorem phi_tmul (r : KLR.KLRAlgebra k (CL.qCL sc) ν) (p : PiLam I k) :
    phi RD k sc μ ν (r ⊗ₜ p) = toUEnd RD k sc μ ν r * bubDiag RD k sc μ ν (bubMap RD k sc μ p) :=
  Algebra.TensorProduct.lift_tmul _ _ _ r p

/-! ### Upward diagrams as KLR diagrams -/






omit [DecidableEq I] in
theorem dg_upward_eq {w₁ w₂ : List I} {A : List (LayerData I)} (h : SChain (ups w₁) A (ups w₂))
    (hA : Upward A) :
    ∃ d : KLR.Diagram.ob w₁ ⟶ KLR.Diagram.ob w₂,
      dg RD k sc μ (ups w₁) (ups w₂) A = (pres RD k sc).diag (upDiag RD μ d) := by
  have hpos : Positive (ups w₁) := by simp [Positive, ups]
  obtain ⟨hc, hm⟩ := chain_toKLR h hA hpos
  have e₁ : (ups w₁).map Prod.snd = w₁ := by simp [ups, Function.comp_def]
  have e₂ : (ups w₂).map Prod.snd = w₂ := by simp [ups, Function.comp_def]
  rw [e₁, e₂] at hc
  refine ⟨⟨A.map toKLRLayer, hc⟩, ?_⟩
  rw [upDiag_eq_dg]
  exact congrArg _ hm.symm

theorem single_upFunctor_eq (i j : KLR.Seq ν)
    (F : (KLR.Diagram.pres k (CL.qCL sc)).obj (KLR.Diagram.ob (word i)) ⟶
      (KLR.Diagram.pres k (CL.qCL sc)).obj (KLR.Diagram.ob (word j))) :
    single i j ((upFunctor RD k sc μ).map F) =
      toUEnd RD k sc μ ν ((diagREquiv k (CL.qCL sc) ν).symm (single i j F)) := by
  change _ = matEndMap k (upFunctor RD k sc μ) _ ((diagREquiv k (CL.qCL sc) ν)
    ((diagREquiv k (CL.qCL sc) ν).symm (single i j F)))
  rw [AlgEquiv.apply_symm_apply, matEndMap_single]

/-- **Upward diagrams followed by bubble monomials lie in the image of `ϕ_{ν,μ}`.** -/
theorem single_dg_bubAt_mem_range (i j : KLR.Seq ν) {A : List (LayerData I)}
    (h : SChain (ups (word i)) A (ups (word j))) (hA : Upward A)
    {γ : End ((pres RD k sc).obj (ob RD μ []))} (hγ : IsBub RD k sc μ γ) :
    single i j (dg RD k sc μ (ups (word i)) (ups (word j)) A ≫ bubAt RD k sc μ (ups (word j)) γ) ∈
      (phi RD k sc μ ν).range := by
  obtain ⟨p, hp⟩ := hγ
  obtain ⟨d, hd⟩ := dg_upward_eq RD k sc μ h hA
  refine ⟨(diagREquiv k (CL.qCL sc) ν).symm
    (single i j ((KLR.Diagram.pres k (CL.qCL sc)).diag d)) ⊗ₜ p, ?_⟩
  have hp' : bubMap RD k sc μ p = EndOne.of γ := hp
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, phi_tmul, ← single_upFunctor_eq, upFunctor_diag,
    hp', single_mul_bubDiag, EndOne.val_of, bubAt_comm, hd]
  rfl

/-- **The bubble step of KL III's proof of Lemma 3.9**: every element of `upSpan` (in
particular, by `slideOutUp`, every upward diagram with elements of the image of `Π` inserted
in its regions) lies in the image of `ϕ_{ν,μ}` (in the `(i, j)` component). -/
theorem single_upSpan_mem_range (i j : KLR.Seq ν) {x : (pres RD k sc).obj (ob RD μ (ups (word i))) ⟶
    (pres RD k sc).obj (ob RD μ (ups (word j)))} (hx : x ∈ upSpan RD k sc μ (ups (word i)) (ups (word j))) :
    single i j x ∈ (phi RD k sc μ ν).range := by
  induction hx using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, γ, hA, h, hγ, rfl⟩ := hf
    exact single_dg_bubAt_mem_range RD k sc μ ν i j h hA hγ
  | zero => rw [single_zero]; exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => rw [single_add]; exact Subalgebra.add_mem _ hx hy
  | smul r x _ hx => rw [single_smul]; exact Subalgebra.smul_mem _ hx r

/-- **KL III Lemma 3.9, the bubble step**: an upward diagram from
`E_i 1_μ` to `E_j 1_μ` with an element of the image of `Π` inserted in one of its regions (in
the region to the left of the strands `v`, between the layers `pre` and `post`) lies in the
image of `ϕ_{i,j,μ}`. Iterating, the same holds with bubble monomials inserted in any number of
regions. -/
theorem lem39_bubbles (i j : KLR.Seq ν) {pre post : List (LayerData I)}
    {u v : List (Letter I)} (hpre : SChain (ups (word i)) pre (u ++ v))
    (hpost : SChain (u ++ v) post (ups (word j))) (hupre : Upward pre) (hupost : Upward post)
    (hv : Positive v) {β : End ((pres RD k sc).obj (ob RD (wt RD μ v) []))}
    (hβ : IsBub RD k sc (wt RD μ v) β) :
    single i j (ctxL RD k sc μ _ _ pre u v post [] [] β) ∈ (phi RD k sc μ ν).range :=
  single_upSpan_mem_range RD k sc μ ν i j
    (slideOutUp RD k sc μ v u pre post hpre hpost hupre hupost hv β hβ)

/-- **KL III Proposition 3.10** (unlabelled in the TeX; `ϕ_{ν,λ}` is eq. (3.30), label
`eq_phi_nu_lambda`; Lemma 3.9 componentwise):
`ϕ_{ν,μ}` is surjective. -/
def Prop310 : Prop := Function.Surjective (phi RD k sc μ ν)

end BubDiag

end Categorification.KL3.Diagram.CLQ
