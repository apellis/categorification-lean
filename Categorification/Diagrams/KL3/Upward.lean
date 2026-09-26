/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Presentation
import Categorification.Diagrams.KLR.Comparison

/-!
# The KLR algebras act on upward strands of `U`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1:
the `R(ν)`-relations of Definition 3.1 are the relations of the KLR algebra `R(ν)` of KL II
(with `Q_ij = u^{d_ij} + v^{d_ji}`), imposed on upward strands. Hence for every weight `λ` there
is a homomorphism `R(ν) → END_U(E_ν 1_λ)` (KL III uses it, e.g. in §3.2 and §3.3).

## Main definitions and results

* `upFunctor RD k μ : (KLR pres).Presented ⥤ (pres RD k).Presented` — the linear functor that
  places a KLR diagram on upward strands with rightmost region `μ`; it is well defined because
  it kills every whiskered KLR relation (these are the relations `klr` of `U`) and every
  whiskered instance of the interchange law (by the interchange law of `U`).
* `upFunctor_obj`, `upFunctor_diag`: it sends the sequence `i` to `E_i 1_μ` and a KLR diagram to
  the same diagram on upward strands.
* `toUEnd RD k μ ν : R(ν) →ₐ[k] MatEnd (fun i => E_i 1_μ)` — the algebra homomorphism
  `R(ν) → ⨁_{i, j ∈ Seq ν} Hom_U(E_i 1_μ, E_j 1_μ) = END_U(E_ν 1_μ)` (the endomorphism algebra of
  `⨁_i E_i 1_μ`, as a matrix algebra), with `toUEnd_e`, `toUEnd_x`, `toUEnd_ψ`: it sends the
  idempotent `e(i)`, the dot `x_a` and the crossing `ψ_j` to the identity of `E_i 1_μ`, the dots
  and the crossings on upward strands.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Weights of upward sequences -/

/-- The weight `∑ i_X` of a sequence of vertices. -/
def wsum (l : List I) : X := (l.map RD.iX).sum

theorem wt_ups (μ : X) (l : List I) : wt RD μ (ups l) = wsum RD l + μ := by
  induction l with
  | nil => simp [wsum]
  | cons i l ih => simp [ih, wsum, sh, add_assoc]

theorem wsum_append (l l' : List I) : wsum RD (l ++ l') = wsum RD l + wsum RD l' := by
  simp [wsum]

theorem wsum_gen_cod (g : KLR.Diagram.Gen I) : wsum RD g.cod = wsum RD g.dom := by
  cases g with
  | dot c => rfl
  | cross c d => simp [wsum, add_comm]

/-- KLR diagrams preserve the weight of their boundary sequences. -/
theorem ups_append (a b : List I) : ups (a ++ b) = ups a ++ ups b := by simp [ups]

/-- KLR diagrams preserve the weight of their boundary sequences. -/
theorem chain_wsum {a b : Obj (KLR.Diagram.sig I)} {ls : List (Layer (KLR.Diagram.sig I))}
    (h : Chain a ls b) :
    wsum RD b.word = wsum RD a.word ∧ ∀ L ∈ ls, wsum RD L.dom.word = wsum RD a.word := by
  induction ls generalizing a with
  | nil => cases h; exact ⟨rfl, fun _ h => by simp at h⟩
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    have hL : wsum RD L.cod.word = wsum RD L.dom.word := by
      simp only [KLR.Diagram.Layer.cod_word', KLR.Diagram.Layer.dom_word', wsum_append,
        wsum_gen_cod]
    obtain ⟨h₁, h₂⟩ := ih hc
    refine ⟨h₁.trans hL, fun M hM => ?_⟩
    rcases List.mem_cons.1 hM with rfl | hM
    · rfl
    · exact (h₂ M hM).trans hL

/-! ## Whiskering -/

section Whisker

variable {RD}

/-- The left whiskering object for placing `u ⊗ - ⊗ v` on upward strands, for a diagram with
bottom boundary `a`. -/
def wU (μ : X) (a u : Obj (KLR.Diagram.sig I)) (v : List I) : Obj (psig RD) :=
  ⟨(wt RD μ (ups (u.word ++ a.word ++ v)) : X), wd RD (wt RD μ (ups (a.word ++ v))) (ups u.word)⟩

theorem wU_ok (μ : X) (a u : Obj (KLR.Diagram.sig I)) (v : List I) :
    (ob RD (wt RD μ (ups v)) (ups a.word)).WhiskerOK (wU μ a u v) (wd RD μ (ups v)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [wU, ups_append, List.append_assoc, wt_append]
    exact ok_wd RD _ _
  · simp only [wU, Obj.endR, ob_start, ups_append, List.append_assoc, wt_append]
    exact endR_wd RD _ _
  · simp only [Obj.endR, ob_start, ob_word, endR_wd]
    exact ok_wd RD _ _

theorem wU_whisker (μ : X) {a b u : Obj (KLR.Diagram.sig I)} (v : List I)
    (hab : wsum RD b.word = wsum RD a.word) :
    (ob RD (wt RD μ (ups v)) (ups b.word)).whisker (wU μ a u v) (wd RD μ (ups v)) =
      ob RD μ (ups (b.whisker u v).word) := by
  have e : wt RD (wt RD μ (ups v)) (ups a.word) = wt RD (wt RD μ (ups v)) (ups b.word) := by
    simp only [wt_ups, hab]
  refine Obj.ext ?_ ?_
  · simp only [wU, Obj.whisker_start, ob_start, Obj.whisker_word, ups_append,
      List.append_assoc, wt_append, e]
  · simp only [wU, Obj.whisker_word, ob_word, ups_append, List.append_assoc, wd_append,
      wt_append, e]

theorem upLay_whisker (μ : X) (L : Layer (KLR.Diagram.sig I)) (a u : Obj (KLR.Diagram.sig I))
    (v : List I) (hL : wsum RD L.dom.word = wsum RD a.word) :
    upLay RD μ (L.whisker u v) =
      (upLay RD (wt RD μ (ups v)) L).whisker (wU μ a u v) (wd RD μ (ups v)) := by
  have hL' : wsum RD L.left + (wsum RD L.gen.dom + wsum RD L.right) = wsum RD a.word := by
    rw [← hL]; simp [wsum_append, add_assoc]
  have e : wt RD (wt RD (wt RD μ (ups v)) (ups L.right)) (ups L.left ++ (upShape L.gen).dom) =
      wt RD (wt RD μ (ups v)) (ups a.word) := by
    rw [upShape_dom, ← ups_append]
    simp only [wt_ups, wsum_append, ← hL']
    abel
  refine Layer.ext ?_ ?_ ?_ ?_
  · simp only [upLay, lay, Layer.whisker, wU, ups_append, List.append_assoc, wt_append]
    rw [← e]
    simp only [wt_append]
  · simp only [upLay, lay, Layer.whisker, wU, ups_append, List.append_assoc, wt_append,
      wd_append]
    rw [← e]
    simp only [wt_append]
  · simp only [upLay, lay, Layer.whisker, ups_append, wt_append]
  · simp only [upLay, lay, Layer.whisker, ups_append, wd_append]

theorem upDiag_whisker (μ : X) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b)
    (u : Obj (KLR.Diagram.sig I)) (v : List I) (hw : a.WhiskerOK u v) :
    upDiag RD μ (Diagram.whisker d u v hw) =
      Diagram.cast (Diagram.whisker (upDiag RD (wt RD μ (ups v)) d) (wU μ a u v) (wd RD μ (ups v))
        (wU_ok μ a u v)) (wU_whisker μ v rfl)
        (wU_whisker μ v (chain_wsum RD (Diagram.chain d)).1) := by
  apply Diagram.ext
  simp only [layers_upDiag, Diagram.layers_whisker, Diagram.layers_cast, List.map_map]
  refine List.map_congr_left fun L hL => ?_
  exact upLay_whisker μ L a u v ((chain_wsum RD (Diagram.chain d)).2 L hL)

end Whisker

/-! ## The functor -/

/-- The functor from the free 2-category of KLR diagrams placing them on upward strands with
rightmost region `μ`. -/
def upFree (μ : X) : Obj (KLR.Diagram.sig I) ⥤ (pres RD k).Presented where
  obj a := (pres RD k).obj (ob RD μ (ups a.word))
  map d := (pres RD k).diag (upDiag RD μ d)
  map_id a := by
    rw [← (pres RD k).diag_id]
    exact (pres RD k).diag_eq_of_layers_eq rfl
  map_comp f g := by
    rw [← (pres RD k).diag_comp]
    exact (pres RD k).diag_eq_of_layers_eq (by simp)

theorem freeLift_upFree (μ : X) {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b) :
    (freeLift k (upFree RD k μ)).map f = (pres RD k).lin (upLin RD k μ f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [upLin]
  | add f g hf hg => rw [Functor.map_add, hf, hg, upLin, upLin, upLin, Finsupp.mapDomain_add,
      lin_add]
  | single d r =>
    rw [freeLift_map_single, upLin, Finsupp.mapDomain_single, lin_single]
    rfl

theorem upLin_whisker (μ : X) {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b)
    (u : Obj (KLR.Diagram.sig I)) (v : List I) (hw : a.WhiskerOK u v)
    (hab : wsum RD b.word = wsum RD a.word) :
    upLin RD k μ (LinDiagram.whisker f u v hw) =
      LinDiagram.cast (LinDiagram.whisker (upLin RD k (wt RD μ (ups v)) f) (wU μ a u v)
        (wd RD μ (ups v)) (wU_ok μ a u v)) (wU_whisker μ v rfl) (wU_whisker μ v hab) := by
  simp only [upLin, LinDiagram.whisker, LinDiagram.cast, ← Finsupp.mapDomain_comp]
  congr 1
  funext d
  exact upDiag_whisker μ d u v hw

variable {RD k}

/-- The KLR interchange law holds on upward strands: moving a generator on the right past a
generator on the left. -/
theorem upDiag_interchange (ν : X) (x : InterchangeData (KLR.Diagram.sig I)) (hx : x.Valid) :
    (pres RD k).diag (upDiag RD ν (InterchangeData.ghDiagram hx)) =
      (pres RD k).diag (upDiag RD ν (InterchangeData.hgDiagram hx)) := by
  set g' := upShape x.g
  set h' := upShape x.h
  set ν' := wt RD ν (ups x.mid ++ h'.dom)
  let L := lay RD ν' [] g' []
  let M := lay RD ν (ups x.mid) h' []
  have hLv := lay_valid RD ν' [] g' []
  have hMv := lay_valid RD ν (ups x.mid) h' []
  have hLd : L.dom = ob RD ν' g'.dom := by simpa using lay_dom RD ν' [] g' []
  have hLc : L.cod = ob RD ν' g'.cod := by simpa using lay_cod RD ν' [] g' []
  have hMd : M.dom = ob RD ν (ups x.mid ++ h'.dom) := by simpa using lay_dom RD ν (ups x.mid) h' []
  have hMc : M.cod = ob RD ν (ups x.mid ++ h'.cod) := by simpa using lay_cod RD ν (ups x.mid) h' []
  have hcomp : ∀ s t : List (Letter I), wt RD ν (ups x.mid ++ h'.dom) = wt RD ν t →
      (ob RD ν' s).Composable (ob RD ν t) := fun s t e =>
    ⟨ob_wf RD _ _, by rw [ob_endR, ob_start]; exact e, ob_wf RD _ _⟩
  have hwt : wt RD ν (ups x.mid ++ h'.dom) = wt RD ν (ups x.mid ++ h'.cod) := by
    rw [wt_append, wt_append, Shape.wt_dom_eq_wt_cod]
  have h : L.dom.Composable M.dom := by rw [hLd, hMd]; exact hcomp _ _ rfl
  have h₁ : L.cod.Composable M.dom := by rw [hLc, hMd]; exact hcomp _ _ rfl
  have h₂ : L.dom.Composable M.cod := by rw [hLd, hMc]; exact hcomp _ _ hwt
  have key := (pres RD k).diag_swap_layers_of_composable L M hLv hMv h h₁ h₂
  simp only [Diagram.oddCountList, Signature.IsEven.odd_eq_false, List.filter_cons,
    List.filter_nil, Bool.false_eq_true, ↓reduceIte, List.length_nil, mul_zero, pow_zero,
    one_smul] at key
  have hν' : ν' = wt RD (wt RD ν (ups (KLR.Diagram.Gen.dom x.h))) (ups x.mid) := by
    simp only [ν', h', upShape_dom, wt_append]
  have ha : ob RD ν (ups x.dom.word) = L.dom.tensor M.dom := by
    rw [hLd, hMd]
    refine Obj.ext ?_ ?_
    · simp only [InterchangeData.dom, ob_start, Obj.tensor_start, g', h', upShape_dom, ν',
        KLR.Diagram.sig_dom, ups_append, List.append_assoc, wt_append]
    · simp only [InterchangeData.dom, ob_word, Obj.tensor_word, g', h', upShape_dom, ν',
        KLR.Diagram.sig_dom, ups_append, List.append_assoc, wt_append, wd_append]
  have hb : ob RD ν (ups x.cod.word) = L.cod.tensor M.cod := by
    rw [hLc, hMc]
    have e : ν' = wt RD ν (ups x.mid ++ h'.cod) := hwt
    refine Obj.ext ?_ ?_
    · simp only [InterchangeData.cod, ob_start, Obj.tensor_start, e, g', h', upShape_cod,
        KLR.Diagram.sig_cod, ups_append, List.append_assoc, wt_append]
    · simp only [InterchangeData.cod, ob_word, Obj.tensor_word, e, g', h', upShape_cod,
        KLR.Diagram.sig_cod, ups_append, List.append_assoc, wt_append, wd_append]
  rw [(pres RD k).diag_eq_of_layers_eq' (upDiag RD ν (InterchangeData.ghDiagram hx))
      (Diagram.rwhisker (Diagram.ofLayer L hLv) M.dom h ≫
        Diagram.lwhisker L.cod (Diagram.ofLayer M hMv) h₁) ha hb ?e1,
    (pres RD k).diag_eq_of_layers_eq' (upDiag RD ν (InterchangeData.hgDiagram hx))
      (Diagram.lwhisker L.dom (Diagram.ofLayer M hMv) h ≫
        Diagram.rwhisker (Diagram.ofLayer L hLv) M.cod h₂) ha hb ?e2, key]
  case e1 =>
    simp only [layers_upDiag, InterchangeData.ghDiagram, Diagram.layers_mk, List.map_cons,
      List.map_nil, Diagram.layers_comp, Diagram.layers_rwhisker, Diagram.layers_lwhisker,
      Diagram.layers_ofLayer, List.cons_append, List.nil_append]
    rw [hMd, hLc]
    refine List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, rfl⟩⟩
    · refine Layer.ext ?_ ?_ ?_ ?_ <;>
        simp only [upLay, InterchangeData.gh₁, lay, Layer.wr, L, ν', g', h', ups_append,
          upShape_dom, KLR.Diagram.sig_dom, List.append_assoc, List.nil_append, List.append_nil,
          List.map_nil, wt_append, wd_append, wd_nil, wt_nil, ob_word]
    · refine Layer.ext ?_ ?_ ?_ ?_ <;>
        simp only [upLay, InterchangeData.gh₂, lay, Layer.wl, M, L, ν', g', h', ups_append,
          upShape_dom, upShape_cod, KLR.Diagram.sig_cod, KLR.Diagram.sig_dom, List.append_assoc,
          List.nil_append, List.append_nil, List.map_nil, wt_append, wd_append, wd_nil, wt_nil,
          ob_word, ob_start]
  case e2 =>
    simp only [layers_upDiag, InterchangeData.hgDiagram, Diagram.layers_mk, List.map_cons,
      List.map_nil, Diagram.layers_comp, Diagram.layers_rwhisker, Diagram.layers_lwhisker,
      Diagram.layers_ofLayer, List.cons_append, List.nil_append]
    rw [hMc, hLd]
    have ehc : wt RD ν (ups (KLR.Diagram.Gen.dom x.h)) = wt RD ν (ups (KLR.Diagram.Gen.cod x.h)) := by
      rw [← upShape_dom, ← upShape_cod]; exact Shape.wt_dom_eq_wt_cod _ _
    refine List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, rfl⟩⟩
    · refine Layer.ext ?_ ?_ ?_ ?_ <;>
        simp only [upLay, InterchangeData.hg₁, lay, Layer.wl, M, L, ν', g', h', ehc, ups_append,
          upShape_dom, upShape_cod, KLR.Diagram.sig_cod, KLR.Diagram.sig_dom, List.append_assoc,
          List.nil_append, List.append_nil, List.map_nil, wt_append, wd_append, wd_nil, wt_nil,
          ob_word, ob_start]
    · refine Layer.ext ?_ ?_ ?_ ?_ <;>
        simp only [upLay, InterchangeData.hg₂, lay, Layer.wr, L, ν', g', h', ehc, ups_append,
          upShape_dom, upShape_cod, KLR.Diagram.sig_cod, KLR.Diagram.sig_dom, List.append_assoc,
          List.nil_append, List.append_nil, List.map_nil, wt_append, wd_append, wd_nil, wt_nil,
          ob_word, ob_start]

/-! ## The functor on the presented category -/

variable (RD k)

theorem wsum_relation_cod (r : KLR.Diagram.Rel I) :
    wsum RD (KLR.Diagram.Rel.cod r).word = wsum RD (KLR.Diagram.Rel.dom r).word := by
  cases r <;> simp [KLR.Diagram.Rel.cod, KLR.Diagram.Rel.dom, KLR.Diagram.ob, wsum] <;> abel

theorem upLin_of (μ : X) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    upLin RD k μ (LinDiagram.of d : LinDiagram k a b) = LinDiagram.of (upDiag RD μ d) :=
  Finsupp.mapDomain_single

theorem upLin_sub (μ : X) {a b : Obj (KLR.Diagram.sig I)} (f g : LinDiagram k a b) :
    upLin RD k μ (f - g) = upLin RD k μ f - upLin RD k μ g :=
  (Finsupp.lmapDomain k k (upDiag RD μ (a := a) (b := b))).map_sub f g

theorem upLin_smul (μ : X) {a b : Obj (KLR.Diagram.sig I)} (r : k) (f : LinDiagram k a b) :
    upLin RD k μ (r • f) = r • upLin RD k μ f :=
  Finsupp.mapDomain_smul _ _

/-- The placement of KLR diagrams on upward strands kills the whiskered KLR relations (they are
relations of `U`) and the whiskered interchange law. -/
theorem upFree_respects (μ : X) :
    (KLR.Diagram.pres k (KLR.klQ2 k C)).Respects (upFree RD k μ) where
  rel r u v hw := by
    rw [freeLift_upFree, upLin_whisker RD k μ _ u v hw (wsum_relation_cod RD r)]
    exact (pres RD k).lin_rel_cast (.inr (.klr (wt RD μ (ups v)) r)) _ _ _ _ _
  interchange x hx u v hw := by
    have hab : wsum RD x.cod.word = wsum RD x.dom.word := by
      simp only [InterchangeData.cod, InterchangeData.dom, KLR.Diagram.sig_dom,
        KLR.Diagram.sig_cod, wsum_append, wsum_gen_cod]
    rw [freeLift_upFree, upLin_whisker RD k μ _ u v hw hab, lin_cast, ← LinDiagram.whisk_of_ok,
      ← whisk_lin, InterchangeData.rel, upLin_sub, upLin_smul, upLin_of, upLin_of, lin_sub,
      lin_smul, lin_of, lin_of, upDiag_interchange]
    have hs : x.sign = 1 := by simp [InterchangeData.sign]
    simp [hs, whisk_zero]

/-- **The KLR 2-morphisms on upward strands.** The linear functor from the diagrammatic KLR
category (KL II relations, `Q = klQ2 k C`) to `U`, placing diagrams on upward strands with
rightmost region `μ`: the sequence `i` goes to `E_i 1_μ`. -/
def upFunctor (μ : X) : (KLR.Diagram.pres k (KLR.klQ2 k C)).Presented ⥤ (pres RD k).Presented :=
  (KLR.Diagram.pres k (KLR.klQ2 k C)).lift (upFree_respects RD k μ)

instance (μ : X) : (upFunctor RD k μ).Additive := by unfold upFunctor; infer_instance

instance (μ : X) : (upFunctor RD k μ).Linear k := by unfold upFunctor; infer_instance

@[simp] theorem upFunctor_obj (μ : X) (a : Obj (KLR.Diagram.sig I)) :
    (upFunctor RD k μ).obj ((KLR.Diagram.pres k (KLR.klQ2 k C)).obj a) =
      (pres RD k).obj (ob RD μ (ups a.word)) := rfl

@[simp] theorem upFunctor_diag (μ : X) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    (upFunctor RD k μ).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d) =
      (pres RD k).diag (upDiag RD μ d) :=
  (KLR.Diagram.pres k (KLR.klQ2 k C)).lift_diag _ d

/-! ## `R(ν) → END_U(E_ν 1_λ)` -/

section MatEnd

open KLR.Diagram MatEnd

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞] [Category 𝒟] [Preadditive 𝒟]
  [Linear k 𝒟] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A linear functor induces an algebra homomorphism of matrix algebras of morphisms. -/
def matEndMap (F : 𝒞 ⥤ 𝒟) [F.Additive] [F.Linear k] (Z : ι → 𝒞) :
    MatEnd Z →ₐ[k] MatEnd (fun i => F.obj (Z i)) where
  toFun f i j := F.map (f i j)
  map_one' := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [one_apply_of_ne h]
  map_mul' f g := by
    ext i l
    simp [mul_apply, Functor.map_sum]
  map_zero' := by ext; simp
  map_add' f g := by ext; simp
  commutes' r := by
    ext i j
    simp only [Algebra.algebraMap_eq_smul_one, smul_apply, Functor.map_smul]
    by_cases h : i = j
    · subst h; simp
    · simp [one_apply_of_ne h]

theorem matEndMap_single (F : 𝒞 ⥤ 𝒟) [F.Additive] [F.Linear k] (Z : ι → 𝒞) (i j : ι)
    (f : Z i ⟶ Z j) : matEndMap k F Z (single i j f) = single i j (F.map f) := by
  ext i' j'
  change F.map (single (X := Z) i j f i' j') = single (X := fun i => F.obj (Z i)) i j (F.map f) i' j'
  by_cases h : i' = i ∧ j' = j
  · obtain ⟨rfl, rfl⟩ := h; simp [single_apply]
  · rw [single_apply_of_ne _ h, single_apply_of_ne _ h, F.map_zero]

end MatEnd

variable [DecidableEq I]

open KLR.Diagram in
/-- **`R(ν) → END_U(E_ν 1_μ)`**: the algebra homomorphism from the KLR algebra `R(ν)` of KL II
(`R2 k C ν`) to `⨁_{i, j ∈ Seq ν} Hom_U(E_i 1_μ, E_j 1_μ)` (the endomorphism algebra of
`⨁_i E_i 1_μ`, written as matrices of 2-morphisms), given by placing diagrams on upward strands.
It is the composite of the identification `R(ν) ≅ DiagR` (`diagREquiv`) with `upFunctor`. -/
def toUEnd (μ : X) (ν : Multiset I) :
    KLR.R2 k C ν →ₐ[k] MatEnd (fun i : KLR.Seq ν => (pres RD k).obj (ob RD μ (ups (word i)))) :=
  (matEndMap k (upFunctor RD k μ) _).comp (diagREquiv k (KLR.klQ2 k C) ν).toAlgHom

open KLR.Diagram in
theorem toUEnd_e (μ : X) (ν : Multiset I) (i : KLR.Seq ν) :
    toUEnd RD k μ ν (KLR.KLRAlgebra.e i) = MatEnd.single i i (𝟙 _) := by
  rw [toUEnd]
  show matEndMap k (upFunctor RD k μ) _ (diagREquiv k _ ν (KLR.KLRAlgebra.e i)) = _
  rw [diagREquiv_e, DiagR.E, matEndMap_single, CategoryTheory.Functor.map_id]
  rfl

open KLR.Diagram in
theorem toUEnd_x (μ : X) (ν : Multiset I) (a : Fin (Multiset.card ν)) :
    toUEnd RD k μ ν (KLR.KLRAlgebra.x a) =
      ∑ i, MatEnd.single i i ((upFunctor RD k μ).map (dotE k (KLR.klQ2 k C) i a)) := by
  rw [toUEnd]
  show matEndMap k (upFunctor RD k μ) _ (diagREquiv k _ ν (KLR.KLRAlgebra.x a)) = _
  rw [diagREquiv_x, DiagR.X, map_sum]
  exact Finset.sum_congr rfl fun i _ => matEndMap_single k (upFunctor RD k μ) _ i i _

open KLR.Diagram in
theorem toUEnd_ψ (μ : X) (ν : Multiset I) (j : ℕ) :
    toUEnd RD k μ ν (KLR.KLRAlgebra.ψ j) =
      ∑ i, MatEnd.single i (TypeA.sadj (Multiset.card ν) j • i)
        ((upFunctor RD k μ).map (crossE k (KLR.klQ2 k C) i j)) := by
  rw [toUEnd]
  show matEndMap k (upFunctor RD k μ) _ (diagREquiv k _ ν (KLR.KLRAlgebra.ψ j)) = _
  rw [diagREquiv_ψ, DiagR.Ψ, map_sum]
  exact Finset.sum_congr rfl fun i _ => matEndMap_single k (upFunctor RD k μ) _ i _ _

end Categorification.KL3.Diagram
