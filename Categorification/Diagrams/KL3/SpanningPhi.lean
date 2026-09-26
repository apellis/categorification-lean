/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Spanning

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

`Prop310` is the statement of Proposition 3.10 (surjectivity of `phi`); it is proved for
simply-laced data in `Categorification.Diagrams.KL3.Lemma39` (`prop310_of_simplyLaced`). What is proved is the step "Bubble sliding rules
allow moving bubbles to the far right of the diagram" of KL III's proof of Lemma 3.9:
`slideOutUp` (an element of the image of `Π` inserted in any region of an upward diagram is a
linear combination of upward diagrams followed by bubble monomials on the far right).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
open scoped TensorProduct

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Endomorphisms of `1_μ` placed on the far right -/

section BubAt

variable (μ : X)

/-- An endomorphism of `1_μ` placed to the right of the strands `s` (rightmost region `μ`). -/
def bubAt (s : List (Letter I)) :
    End ((pres RD k).obj (ob RD μ [])) →ₗ[k] End ((pres RD k).obj (ob RD μ s)) :=
  ctxL RD k μ s s [] s [] [] [] []

theorem bubAt_dg (s : List (Letter I)) (B : List (LayerData I)) :
    bubAt RD k μ s (dg RD k μ [] [] B) = dg RD k μ s s (B.map (whL s [])) := by
  have := ctxL_dg RD k μ (s₀ := s) (t₀ := s) (pre := []) (u := s) (v := []) (post := [])
    (s := []) (t := []) (show s = s ++ [] ++ [] by simp) (show s ++ [] ++ [] = s by simp) B
  simpa using this

theorem bubAt_comm_dg {s t : List (Letter I)} (β : End ((pres RD k).obj (ob RD μ [])))
    (A : List (LayerData I)) (hA : SChain s A t) :
    bubAt RD k μ s β ≫ dg RD k μ s t A = dg RD k μ s t A ≫ bubAt RD k μ t β := by
  have key := hom_ext_dg RD k μ (s := []) (t := [])
    ((Linear.rightComp k _ (dg RD k μ s t A)).comp (bubAt RD k μ s))
    ((Linear.leftComp k _ (dg RD k μ s t A)).comp (bubAt RD k μ t)) (fun B hB => ?_)
  · exact LinearMap.congr_fun key β
  change bubAt RD k μ s (dg RD k μ [] [] B) ≫ dg RD k μ s t A =
    dg RD k μ s t A ≫ bubAt RD k μ t (dg RD k μ [] [] B)
  have hBs : SChain s (B.map (whL s [])) s := by simpa using hB.whisk s []
  have hBt : SChain t (B.map (whL t [])) t := by simpa using hB.whisk t []
  rw [bubAt_dg, bubAt_dg, dg_comp hBs hA, dg_comp hA hBt]
  have e := dg_closed_left (RD := RD) (k := k) μ (S := s) (T := t) [] [] (s := s) (s' := t) []
    hB hA
  wnf at e
  exact e.symm

/-- **Bubbles on the far right are central** (interchange law): for every 2-morphism
`f : E_s 1_μ → E_t 1_μ`, `bubAt s β ≫ f = f ≫ bubAt t β`. -/
theorem bubAt_comm {s t : List (Letter I)} (β : End ((pres RD k).obj (ob RD μ [])))
    (f : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :
    bubAt RD k μ s β ≫ f = f ≫ bubAt RD k μ t β := by
  have key := hom_ext_dg RD k μ (s := s) (t := t)
    (Linear.leftComp k _ (bubAt RD k μ s β)) (Linear.rightComp k _ (bubAt RD k μ t β))
    (fun A hA => bubAt_comm_dg RD k μ β A hA)
  exact LinearMap.congr_fun key f

theorem bubAt_id (s : List (Letter I)) : bubAt RD k μ s (𝟙 _) = 𝟙 _ := by
  rw [← dg_nil (RD := RD) (k := k) μ [], bubAt_dg RD k μ s [], List.map_nil, dg_nil]

theorem bubAt_comp (s : List (Letter I)) (β γ : End ((pres RD k).obj (ob RD μ []))) :
    bubAt RD k μ s (β ≫ γ) = bubAt RD k μ s β ≫ bubAt RD k μ s γ := by
  have key := hom_ext_dg RD k μ (s := []) (t := [])
    ((bubAt RD k μ s).comp (Linear.rightComp k _ γ))
    ((Linear.rightComp k _ (bubAt RD k μ s γ)).comp (bubAt RD k μ s)) (fun B hB => ?_)
  · exact LinearMap.congr_fun key β
  change bubAt RD k μ s (dg RD k μ [] [] B ≫ γ) = bubAt RD k μ s (dg RD k μ [] [] B) ≫ _
  have key' := hom_ext_dg RD k μ (s := []) (t := [])
    ((bubAt RD k μ s).comp (Linear.leftComp k _ (dg RD k μ [] [] B)))
    ((Linear.leftComp k _ (bubAt RD k μ s (dg RD k μ [] [] B))).comp (bubAt RD k μ s))
    (fun G hG => ?_)
  · exact LinearMap.congr_fun key' γ
  change bubAt RD k μ s (dg RD k μ [] [] B ≫ dg RD k μ [] [] G) =
    bubAt RD k μ s (dg RD k μ [] [] B) ≫ bubAt RD k μ s (dg RD k μ [] [] G)
  have hBs : SChain s (B.map (whL s [])) s := by simpa using hB.whisk s []
  have hGs : SChain s (G.map (whL s [])) s := by simpa using hG.whisk s []
  rw [dg_comp hB hG, bubAt_dg RD k μ s _, bubAt_dg RD k μ s _,
    bubAt_dg RD k μ s _, dg_comp hBs hGs, List.map_append]

end BubAt

/-! ## Upward diagrams with bubbles: moving the bubbles to the far right -/

/-- The shape is an upward dot or an upward crossing. -/
def Shape.isUp : Shape I → Bool
  | .dot l => l.1
  | .cross ε _ _ => ε
  | _ => false

/-- A list of layers of upward dots and upward crossings. -/
def Upward (ls : List (LayerData I)) : Prop := ∀ x ∈ ls, x.2.1.isUp = true

/-- All strands of the signed sequence are upward. -/
def Positive (w : List (Letter I)) : Prop := ∀ l ∈ w, l.1 = true

theorem Upward.append {a b : List (LayerData I)} (ha : Upward a) (hb : Upward b) :
    Upward (a ++ b) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h

section UpSpan

variable (μ : X)

/-- The span of the upward diagrams followed by bubble monomials on the far right. -/
def upSpan (S T : List (Letter I)) :
    Submodule k ((pres RD k).obj (ob RD μ S) ⟶ (pres RD k).obj (ob RD μ T)) :=
  Submodule.span k {f | ∃ (A : List (LayerData I)) (γ : End ((pres RD k).obj (ob RD μ []))),
    Upward A ∧ SChain S A T ∧ IsBub RD k μ γ ∧ f = dg RD k μ S T A ≫ bubAt RD k μ T γ}

variable (hSL : SimplyLaced C)
include hSL

/-- **Bubbles slide to the far right of upward diagrams** (KL III, proof of Lemma 3.9: "Bubble
sliding rules allow moving bubbles to the far right of the diagram"): an element of the image of
`Π` inserted in any region of an upward diagram is a linear combination of upward diagrams
followed by bubble monomials on the far right. -/
theorem slideOutUp : ∀ (v u : List (Letter I)) {S T : List (Letter I)}
    (pre post : List (LayerData I)), SChain S pre (u ++ v) → SChain (u ++ v) post T →
    Upward pre → Upward post → Positive v →
    ∀ β : End ((pres RD k).obj (ob RD (wt RD μ v) [])), IsBub RD k (wt RD μ v) β →
      ctxL RD k μ S T pre u v post [] [] β ∈ upSpan RD k μ S T := by
  intro v
  induction v with
  | nil =>
    intro u S T pre post hpre hpost hupre hupost _ β hβ
    have hpp : SChain S (pre ++ post) T := hpre.append hpost
    have key := hom_ext_dg RD k (wt RD μ []) (s := []) (t := [])
      (ctxL RD k μ S T pre u [] post [] [])
      (Linear.leftComp k _ (dg RD k μ S T (pre ++ post)) ∘ₗ bubAt RD k μ T) (fun B hB => ?_)
    · rw [LinearMap.congr_fun key β]
      exact Submodule.subset_span ⟨pre ++ post, β, hupre.append hupost, hpp, hβ, rfl⟩
    rw [ctxL_dg RD k μ (by simpa using hpre) (by simpa using hpost)]
    change _ = dg RD k μ S T (pre ++ post) ≫ bubAt RD k μ T (dg RD k μ [] [] B)
    have hBT : SChain T (B.map (whL T [])) T := by simpa using hB.whisk T []
    rw [bubAt_dg, dg_comp hpp hBT]
    have e := dg_closed_left (RD := RD) (k := k) μ (S := S) (T := T) pre [] (s := u) (s' := T) []
      hB (by simpa using hpost)
    wnf at e
    wnf
    exact e.symm
  | cons l v' ih =>
    intro u S T pre post hpre hpost hupre hupost hv β hβ
    rw [ctxL_cons RD k μ hpre hpost]
    have hmem := bubLU_mem_slideSetR hSL (wt RD μ v') l (β := β) hβ
    generalize bubLU RD k (wt RD μ v') l β = f at hmem ⊢
    induction hmem using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, γ, hγ, rfl⟩ := hf
      rw [ctxL_dots_bubRU RD k μ hpre hpost]
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
abbrev objNu : KLR.Seq ν → (pres RD k).Presented := fun i => (pres RD k).obj (ob RD μ (ups (word i)))

/-- An endomorphism of `1_μ` placed on the far right of every `E_i 1_μ`, `i ∈ Seq ν`: a diagonal
element of `END_U(E_ν 1_μ)`. -/
def bubDiag : EndOne RD k μ →ₐ[k] MatEnd (objNu RD k μ ν) where
  toFun β := ∑ i, single i i (bubAt RD k μ (ups (word i)) β.val)
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

theorem bubDiag_apply (β : EndOne RD k μ) :
    bubDiag RD k μ ν β = ∑ i, single i i (bubAt RD k μ (ups (word i)) β.val) := rfl

theorem bubDiag_mul_single (β : EndOne RD k μ) (i j : KLR.Seq ν) (f : objNu RD k μ ν i ⟶ objNu RD k μ ν j) :
    bubDiag RD k μ ν β * single i j f = single i j (f ≫ bubAt RD k μ (ups (word j)) β.val) := by
  rw [bubDiag_apply, Finset.sum_mul, Finset.sum_eq_single j]
  · exact single_mul_single i j j f _
  · intro m _ hm
    exact single_mul_single_of_ne _ _ (Ne.symm hm)
  · simp

theorem single_mul_bubDiag (β : EndOne RD k μ) (i j : KLR.Seq ν) (f : objNu RD k μ ν i ⟶ objNu RD k μ ν j) :
    single i j f * bubDiag RD k μ ν β = single i j (bubAt RD k μ (ups (word i)) β.val ≫ f) := by
  rw [bubDiag_apply, Finset.mul_sum, Finset.sum_eq_single i]
  · exact single_mul_single i i j _ f
  · intro m _ hm
    exact single_mul_single_of_ne _ _ hm
  · simp

/-- **The image of `END_U(1_μ)` in `END_U(E_ν 1_μ)` is central.** -/
theorem bubDiag_central (β : EndOne RD k μ) (M : MatEnd (objNu RD k μ ν)) :
    bubDiag RD k μ ν β * M = M * bubDiag RD k μ ν β := by
  rw [eq_sum_single M, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bubDiag_mul_single, single_mul_bubDiag, bubAt_comm]

/-- **KL III eq. (3.30)**: `ϕ_{ν,μ} : R(ν) ⊗ Π_μ → END_U(E_ν 1_μ)`, placing upward diagrams of
`R(ν)` to the left of bubble monomials. -/
def phi : KLR.R2 k C ν ⊗[k] PiLam I k →ₐ[k] MatEnd (objNu RD k μ ν) :=
  Algebra.TensorProduct.lift (toUEnd RD k μ ν) ((bubDiag RD k μ ν).comp (bubMap RD k μ))
    fun _ _ => (bubDiag_central RD k μ ν _ _).symm

theorem phi_tmul (r : KLR.R2 k C ν) (p : PiLam I k) :
    phi RD k μ ν (r ⊗ₜ p) = toUEnd RD k μ ν r * bubDiag RD k μ ν (bubMap RD k μ p) :=
  Algebra.TensorProduct.lift_tmul _ _ _ r p

/-! ### Upward diagrams as KLR diagrams -/

/-- The KLR generator of an upward shape. -/
def klrGen : Shape I → KLR.Diagram.Gen I
  | .dot l => .dot l.2
  | .cross _ c d => .cross c d
  | .cup l => .dot l.2
  | .cap l => .dot l.2

/-- The KLR layer underlying an upward layer. -/
def toKLRLayer (x : LayerData I) : Layer (KLR.Diagram.sig I) :=
  ⟨(), x.1.map Prod.snd, klrGen x.2.1, x.2.2.map Prod.snd⟩

omit [DecidableEq I] in
theorem ups_map_snd {w : List (Letter I)} (h : Positive w) : ups (w.map Prod.snd) = w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨b, c⟩ := l
    have hb : b = true := h _ List.mem_cons_self
    subst hb
    simp only [List.map_cons, ups, List.map_map] at ih ⊢
    rw [← ih (fun l hl => h l (List.mem_cons_of_mem _ hl))]
    simp [Function.comp_def]

omit [DecidableEq I] in
theorem upShape_dom_positive {g : Shape I} (hg : g.isUp = true) : Positive g.dom ∧ Positive g.cod ∧
    (klrGen g).dom = g.dom.map Prod.snd ∧ (klrGen g).cod = g.cod.map Prod.snd ∧
    upShape (klrGen g) = g := by
  cases g with
  | dot l =>
    obtain ⟨b, c⟩ := l
    simp only [Shape.isUp] at hg; subst hg
    refine ⟨?_, ?_, rfl, rfl, rfl⟩ <;> simp [Positive]
  | cross ε c d =>
    simp only [Shape.isUp] at hg; subst hg
    refine ⟨?_, ?_, rfl, rfl, rfl⟩ <;> simp [Positive]
  | cup l => simp [Shape.isUp] at hg
  | cap l => simp [Shape.isUp] at hg

omit [DecidableEq I] in
/-- An upward normal-form diagram between positive sequences is (the image of) a KLR diagram. -/
theorem chain_toKLR {s t : List (Letter I)} {A : List (LayerData I)} (h : SChain s A t)
    (hA : Upward A) (hs : Positive s) :
    Chain (KLR.Diagram.ob (s.map Prod.snd)) (A.map toKLRLayer) (KLR.Diagram.ob (t.map Prod.snd)) ∧
      (A.map toKLRLayer).map upLD = A := by
  induction A generalizing s with
  | nil => cases h; exact ⟨rfl, rfl⟩
  | cons x A ih =>
    obtain ⟨rfl, h⟩ := h
    obtain ⟨a, g, b⟩ := x
    have hg : g.isUp = true := hA _ List.mem_cons_self
    obtain ⟨_, hcod, hdom', hcod', hup⟩ := upShape_dom_positive hg
    have ha : Positive a := fun l hl => hs l (by simp [hl])
    have hb : Positive b := fun l hl => hs l (by simp [hl])
    have hs' : Positive (a ++ g.cod ++ b) := by
      intro l hl
      simp only [List.mem_append] at hl
      rcases hl with (hl | hl) | hl
      · exact ha l hl
      · exact hcod l hl
      · exact hb l hl
    obtain ⟨hc, hm⟩ := ih h (fun y hy => hA y (List.mem_cons_of_mem _ hy)) hs'
    refine ⟨⟨Layer.valid_of_subsingleton _, ?_, ?_⟩, ?_⟩
    · refine KLR.Diagram.obj_ext ?_
      simp [toKLRLayer, Layer.dom, hdom', KLR.Diagram.ob]
    · convert hc using 1
      refine KLR.Diagram.obj_ext ?_
      simp [toKLRLayer, Layer.cod, hcod', KLR.Diagram.ob]
    · rw [List.map_cons, List.map_cons, hm]
      simp only [upLD, toKLRLayer, ups_map_snd ha, ups_map_snd hb, hup]

omit [DecidableEq I] in
theorem dg_upward_eq {w₁ w₂ : List I} {A : List (LayerData I)} (h : SChain (ups w₁) A (ups w₂))
    (hA : Upward A) :
    ∃ d : KLR.Diagram.ob w₁ ⟶ KLR.Diagram.ob w₂,
      dg RD k μ (ups w₁) (ups w₂) A = (pres RD k).diag (upDiag RD μ d) := by
  have hpos : Positive (ups w₁) := by simp [Positive, ups]
  obtain ⟨hc, hm⟩ := chain_toKLR h hA hpos
  have e₁ : (ups w₁).map Prod.snd = w₁ := by simp [ups, Function.comp_def]
  have e₂ : (ups w₂).map Prod.snd = w₂ := by simp [ups, Function.comp_def]
  rw [e₁, e₂] at hc
  refine ⟨⟨A.map toKLRLayer, hc⟩, ?_⟩
  rw [upDiag_eq_dg]
  exact congrArg _ hm.symm

theorem single_upFunctor_eq (i j : KLR.Seq ν)
    (F : (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob (word i)) ⟶
      (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob (word j))) :
    single i j ((upFunctor RD k μ).map F) =
      toUEnd RD k μ ν ((diagREquiv k (KLR.klQ2 k C) ν).symm (single i j F)) := by
  change _ = matEndMap k (upFunctor RD k μ) _ ((diagREquiv k (KLR.klQ2 k C) ν)
    ((diagREquiv k (KLR.klQ2 k C) ν).symm (single i j F)))
  rw [AlgEquiv.apply_symm_apply, matEndMap_single]

/-- **Upward diagrams followed by bubble monomials lie in the image of `ϕ_{ν,μ}`.** -/
theorem single_dg_bubAt_mem_range (i j : KLR.Seq ν) {A : List (LayerData I)}
    (h : SChain (ups (word i)) A (ups (word j))) (hA : Upward A)
    {γ : End ((pres RD k).obj (ob RD μ []))} (hγ : IsBub RD k μ γ) :
    single i j (dg RD k μ (ups (word i)) (ups (word j)) A ≫ bubAt RD k μ (ups (word j)) γ) ∈
      (phi RD k μ ν).range := by
  obtain ⟨p, hp⟩ := hγ
  obtain ⟨d, hd⟩ := dg_upward_eq RD k μ h hA
  refine ⟨(diagREquiv k (KLR.klQ2 k C) ν).symm
    (single i j ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d)) ⊗ₜ p, ?_⟩
  have hp' : bubMap RD k μ p = EndOne.of γ := hp
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, phi_tmul, ← single_upFunctor_eq, upFunctor_diag,
    hp', single_mul_bubDiag, EndOne.val_of, bubAt_comm, hd]
  rfl

/-- **The bubble step of KL III's proof of Lemma 3.9**: every element of `upSpan` (in
particular, by `slideOutUp`, every upward diagram with elements of the image of `Π` inserted
in its regions) lies in the image of `ϕ_{ν,μ}` (in the `(i, j)` component). -/
theorem single_upSpan_mem_range (i j : KLR.Seq ν) {x : (pres RD k).obj (ob RD μ (ups (word i))) ⟶
    (pres RD k).obj (ob RD μ (ups (word j)))} (hx : x ∈ upSpan RD k μ (ups (word i)) (ups (word j))) :
    single i j x ∈ (phi RD k μ ν).range := by
  induction hx using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, γ, hA, h, hγ, rfl⟩ := hf
    exact single_dg_bubAt_mem_range RD k μ ν i j h hA hγ
  | zero => rw [single_zero]; exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => rw [single_add]; exact Subalgebra.add_mem _ hx hy
  | smul r x _ hx => rw [single_smul]; exact Subalgebra.smul_mem _ hx r

/-- **KL III Lemma 3.9, the bubble step** (simply-laced Cartan data): an upward diagram from
`E_i 1_μ` to `E_j 1_μ` with an element of the image of `Π` inserted in one of its regions (in
the region to the left of the strands `v`, between the layers `pre` and `post`) lies in the
image of `ϕ_{i,j,μ}`. Iterating, the same holds with bubble monomials inserted in any number of
regions. -/
theorem lem39_bubbles (hSL : SimplyLaced C) (i j : KLR.Seq ν) {pre post : List (LayerData I)}
    {u v : List (Letter I)} (hpre : SChain (ups (word i)) pre (u ++ v))
    (hpost : SChain (u ++ v) post (ups (word j))) (hupre : Upward pre) (hupost : Upward post)
    (hv : Positive v) {β : End ((pres RD k).obj (ob RD (wt RD μ v) []))}
    (hβ : IsBub RD k (wt RD μ v) β) :
    single i j (ctxL RD k μ _ _ pre u v post [] [] β) ∈ (phi RD k μ ν).range :=
  single_upSpan_mem_range RD k μ ν i j
    (slideOutUp RD k μ hSL v u pre post hpre hpost hupre hupost hv β hβ)

/-- **KL III Proposition 3.10** (unlabelled in the TeX; `ϕ_{ν,λ}` is eq. (3.30), label
`eq_phi_nu_lambda`; Lemma 3.9 componentwise):
`ϕ_{ν,μ}` is surjective. -/
def Prop310 : Prop := Function.Surjective (phi RD k μ ν)

end BubDiag

end Categorification.KL3.Diagram
