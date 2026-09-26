/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SortedAction

/-!
# Split diagrams between sorted words are in the image of `α`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.4:
the homomorphism `α : R(ν) ⊗ R(ν') ⊗ Π_λ → END_U(E_{ν,-ν'} 1_λ)` (3.36), "adding upward
orientations to a diagram in `R(ν)`, downward orientations to a diagram in `R(ν')` […]".

A diagram between sorted words `E_{+a} E_{-b} 1_μ → E_{+a'} E_{-b'} 1_μ` is **split** if it is a
downward diagram on the downward strands followed by an upward diagram on the upward strands
(`SplitSet`); by the interchange law these are exactly the diagrams made of dots and crossings.
We show:

* `dg_downward_eq`: a downward diagram of dots and crossings is `±` the image of a KLR diagram
  under `downFunctor` (KL III (3.31));
* `exists_alpha_eq_split`: every split diagram between `E_{+i} E_{-j} 1_μ` and
  `E_{+i'} E_{-j'} 1_μ` (`i, i' ∈ Seq ν`, `j, j' ∈ Seq ν'`) is an entry of `α(x)` for some
  `x ∈ R(ν) ⊗ R(ν')`; `exists_alpha_eq_split_mem`: if the diagram is homogeneous of degree `d`,
  `x` can be taken of degree `d`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation KLR KLR.Diagram MatEnd
open scoped TensorProduct

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [Field k] [DecidableEq I]

/-! ## Downward diagrams -/

/-- The shape is a downward dot or a downward crossing. -/
def Shape.isDn : Shape I → Bool
  | .dot l => !l.1
  | .cross b _ _ => !b
  | _ => false

/-- A list of layers of downward dots and downward crossings. -/
def Downward (ls : List (LayerData I)) : Prop := ∀ x ∈ ls, x.2.1.isDn = true

/-- All strands of the signed sequence are downward. -/
def Negative (w : List (Letter I)) : Prop := ∀ l ∈ w, l.1 = false

omit [DecidableEq I] in
theorem dns_map_snd {w : List (Letter I)} (h : Negative w) : dns (w.map Prod.snd) = w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨b, c⟩ := l
    have hb : b = false := h _ List.mem_cons_self
    subst hb
    simp only [List.map_cons, dns] at ih ⊢
    rw [ih (fun l hl => h l (List.mem_cons_of_mem _ hl))]

omit [DecidableEq I] in
theorem dnShape_dom_negative {g : Shape I} (hg : g.isDn = true) : Negative g.dom ∧ Negative g.cod ∧
    (klrGen g).dom = g.dom.map Prod.snd ∧ (klrGen g).cod = g.cod.map Prod.snd ∧
    dnShape (klrGen g) = g := by
  cases g with
  | dot l =>
    obtain ⟨b, c⟩ := l
    simp only [Shape.isDn, Bool.not_eq_eq_eq_not, Bool.not_true] at hg; subst hg
    refine ⟨?_, ?_, rfl, rfl, rfl⟩ <;> simp [Negative]
  | cross b c d =>
    simp only [Shape.isDn, Bool.not_eq_eq_eq_not, Bool.not_true] at hg; subst hg
    refine ⟨?_, ?_, rfl, rfl, rfl⟩ <;> simp [Negative]
  | cup l => simp [Shape.isDn] at hg
  | cap l => simp [Shape.isDn] at hg

omit [DecidableEq I] in
/-- A downward normal-form diagram between negative sequences is (the image of) a KLR
diagram. -/
theorem chain_toKLR_dn {s t : List (Letter I)} {A : List (LayerData I)} (h : SChain s A t)
    (hA : Downward A) (hs : Negative s) :
    Chain (KLR.Diagram.ob (s.map Prod.snd)) (A.map toKLRLayer) (KLR.Diagram.ob (t.map Prod.snd)) ∧
      (A.map toKLRLayer).map dnLD = A := by
  induction A generalizing s with
  | nil => cases h; exact ⟨rfl, rfl⟩
  | cons x A ih =>
    obtain ⟨rfl, h⟩ := h
    obtain ⟨a, g, b⟩ := x
    have hg : g.isDn = true := hA _ List.mem_cons_self
    obtain ⟨_, hcod, hdom', hcod', hdn⟩ := dnShape_dom_negative hg
    have ha : Negative a := fun l hl => hs l (by simp [hl])
    have hb : Negative b := fun l hl => hs l (by simp [hl])
    have hs' : Negative (a ++ g.cod ++ b) := by
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
      simp only [dnLD, toKLRLayer, dns_map_snd ha, dns_map_snd hb, hdn]

omit [DecidableEq I] in
theorem sgnS_mul_self (ls : List (LayerData I)) [DecidableEq I] :
    Sig.sgnS ls * Sig.sgnS ls = 1 := by
  induction ls with
  | nil => rfl
  | cons x ls ih =>
    simp only [Sig.sgnS, List.map_cons, List.prod_cons] at ih ⊢
    have hx : Sig.sgnSh x.2.1 * Sig.sgnSh x.2.1 = 1 := by
      rcases x with ⟨a, g, b⟩
      cases g with
      | cross b c d => simp only [Sig.sgnSh]; split_ifs <;> norm_num
      | _ => rfl
    calc Sig.sgnSh x.2.1 * (List.map (fun x => Sig.sgnSh x.2.1) ls).prod *
          (Sig.sgnSh x.2.1 * (List.map (fun x => Sig.sgnSh x.2.1) ls).prod)
        = (Sig.sgnSh x.2.1 * Sig.sgnSh x.2.1) *
          ((List.map (fun x => Sig.sgnSh x.2.1) ls).prod *
            (List.map (fun x => Sig.sgnSh x.2.1) ls).prod) := by ring
      _ = 1 := by rw [hx, ih, one_mul]

/-- **Downward diagrams are KLR diagrams on downward strands**, up to the sign of KL III (3.31). -/
theorem dg_downward_eq (μ : X) {w₁ w₂ : List I} {A : List (LayerData I)}
    (h : SChain (dns w₁) A (dns w₂)) (hA : Downward A) :
    ∃ (d : KLR.Diagram.ob w₁ ⟶ KLR.Diagram.ob w₂) (c : k), c * c = 1 ∧
      TR RD k (omega_ob_ups μ w₁).symm (omega_ob_ups μ w₂).symm
        ((downFunctor RD k μ).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d)) =
        c • dg RD k μ (dns w₁) (dns w₂) A := by
  have hneg : Negative (dns w₁) := by simp [Negative, dns]
  obtain ⟨hc, hm⟩ := chain_toKLR_dn h hA hneg
  have e₁ : (dns w₁).map Prod.snd = w₁ := by simp [dns, Function.comp_def]
  have e₂ : (dns w₂).map Prod.snd = w₂ := by simp [dns, Function.comp_def]
  rw [e₁, e₂] at hc
  refine ⟨⟨A.map toKLRLayer, hc⟩, ((Sig.sgnS ((A.map toKLRLayer).map upLD) : ℤ) : k), ?_, ?_⟩
  · rw [← Int.cast_mul, sgnS_mul_self, Int.cast_one]
  rw [downFunctor_diag, map_smul]
  erw [TR_TR]
  congr 1
  exact congrArg _ hm

/-! ## Split diagrams -/

section Split

variable (μ : X)

/-- **Split diagrams** `E_{+a} E_{-b} 1_μ → E_{+a'} E_{-b'} 1_μ`: a downward diagram of dots and
crossings on the downward strands, followed by an upward diagram on the upward strands. -/
def SplitSet (a b a' b' : List I) :
    Set ((pres RD k).obj (ob RD μ (ups a ++ dns b)) ⟶ (pres RD k).obj (ob RD μ (ups a' ++ dns b'))) :=
  {f | ∃ D U : List (LayerData I), Downward D ∧ Upward U ∧ SChain (dns b) D (dns b') ∧
    SChain (ups a) U (ups a') ∧
    f = dg RD k μ (ups a ++ dns b) (ups a' ++ dns b') (D.map (whL (ups a) []) ++ U.map (whL [] (dns b')))}

variable (ν ν' : Multiset I)

/-- The entries of `α(x ⊗ y)`. -/
theorem alpha_tmul_apply (r : KLR.R2 k C ν) (r' : KLR.R2 k C ν') (s s' : KLR.Seq ν)
    (t t' : KLR.Seq ν') :
    alpha RD k μ ν ν' (r ⊗ₜ r') (s, t) (s', t') =
      alphaDn RD k μ ν ν' r' (s, t) (s, t') ≫ alphaUp RD k μ ν ν' r (s, t') (s', t') := by
  rw [alpha_tmul, MatEnd.mul_apply, Finset.sum_eq_single (s, t')]
  · rintro ⟨a, b⟩ _ hab
    by_cases ha : a = s
    · subst ha
      have hb : b ≠ t' := fun h => hab (by rw [h])
      rw [alphaUp_apply_ne RD k μ ν ν' r _ _ hb, Limits.comp_zero]
    · rw [alphaDn_apply_ne RD k μ ν ν' r' _ _ (Ne.symm ha), Limits.zero_comp]
  · simp

/-- **Split diagrams are entries of `α`.** -/
theorem exists_alpha_eq_split (s s' : KLR.Seq ν) (t t' : KLR.Seq ν')
    {f : (pres RD k).obj (ob RD μ (ups (word s) ++ dns (word t))) ⟶
      (pres RD k).obj (ob RD μ (ups (word s') ++ dns (word t')))}
    (hf : f ∈ SplitSet RD k μ (word s) (word t) (word s') (word t')) :
    ∃ x : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν', alpha RD k μ ν ν' x (s, t) (s', t') = f := by
  obtain ⟨D, U, hD, hU, hDc, hUc, rfl⟩ := hf
  obtain ⟨dU, hdU⟩ := dg_upward_eq RD k (wt RD μ (dns (word t'))) hUc hU
  obtain ⟨dD, c, hc, hdD⟩ := dg_downward_eq RD k μ hDc hD
  refine ⟨(diagREquiv k (KLR.klQ2 k C) ν).symm
      (MatEnd.single s s' ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag dU)) ⊗ₜ
    (diagREquiv k (KLR.klQ2 k C) ν').symm
      (MatEnd.single t t' (c • (KLR.Diagram.pres k (KLR.klQ2 k C)).diag dD)), ?_⟩
  rw [alpha_tmul_apply, alphaDn_apply, alphaUp_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply, MatEnd.single_apply_self, MatEnd.single_apply_self,
    upFunctor_diag, ← hdU, plcL_dg, Functor.map_smul, dnF_apply, map_smul, hdD, smul_smul, hc,
    one_smul]
  erw [plcL_dg]
  rw [TR_dg (RD := RD) (k := k) μ (List.append_nil _).symm (List.append_nil _).symm]
  exact dg_comp (by simpa using hDc.whisk (ups (word s)) []) (by simpa using hUc.whisk [] (dns (word t')))

/-- `α` commutes with taking homogeneous components. -/
theorem alpha_proj (d : ℤ) (y : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν') (p q : KLR.Seq ν × KLR.Seq ν') :
    Presentation.homogeneousComponent (pres_isHomogeneous (RD := RD) (k := k)) d
        (alpha RD k μ ν ν' y p q) =
      alpha RD k μ ν ν' (DirectSum.decompose
        (Graded.tensorGrading ((klGradingDatum2 k C).grade ν) ((klGradingDatum2 k C).grade ν')) y d :
          KLR.R2 k C ν ⊗[k] KLR.R2 k C ν') p q := by
  classical
  set 𝒯 := Graded.tensorGrading ((klGradingDatum2 k C).grade ν) ((klGradingDatum2 k C).grade ν')
  have hy : y = ∑ e ∈ (DirectSum.decompose 𝒯 y).support, (DirectSum.decompose 𝒯 y e : _) :=
    (DirectSum.sum_support_decompose 𝒯 y).symm
  conv_lhs => rw [hy]
  rw [map_sum, MatEnd.sum_apply, map_sum]
  have hterm : ∀ e, Presentation.homogeneousComponent (pres_isHomogeneous (RD := RD) (k := k)) d
      (alpha RD k μ ν ν' (DirectSum.decompose 𝒯 y e : _) p q) =
      if e = d then alpha RD k μ ν ν' (DirectSum.decompose 𝒯 y e : _) p q else 0 := by
    intro e
    have hm := alpha_mem RD k (μ := μ) (DirectSum.decompose 𝒯 y e).2 p q
    split_ifs with h
    · subst h
      exact Presentation.homogeneousComponent_of_mem _ hm
    · exact Presentation.homogeneousComponent_of_mem_of_ne _ hm h
  simp only [hterm, Finset.sum_ite_eq', DFinsupp.mem_support_toFun, ne_eq, ite_not]
  split_ifs with h
  · rw [h]; simp
  · rfl

/-- **Homogeneous split diagrams are entries of `α` of homogeneous elements of the same
degree.** -/
theorem exists_alpha_eq_split_mem (s s' : KLR.Seq ν) (t t' : KLR.Seq ν') {d : ℤ}
    {f : (pres RD k).obj (ob RD μ (ups (word s) ++ dns (word t))) ⟶
      (pres RD k).obj (ob RD μ (ups (word s') ++ dns (word t')))}
    (hf : f ∈ SplitSet RD k μ (word s) (word t) (word s') (word t'))
    (hfd : f ∈ HomD RD k μ (ups (word s) ++ dns (word t)) (ups (word s') ++ dns (word t')) d) :
    ∃ x ∈ Graded.tensorGrading ((klGradingDatum2 k C).grade ν) ((klGradingDatum2 k C).grade ν') d,
      alpha RD k μ ν ν' x (s, t) (s', t') = f := by
  obtain ⟨x, hx⟩ := exists_alpha_eq_split RD k μ ν ν' s s' t t' hf
  refine ⟨_, (DirectSum.decompose _ x d).2, ?_⟩
  rw [← alpha_proj, hx]
  exact Presentation.homogeneousComponent_of_mem _ hfd

end Split

end Categorification.KL3.Diagram
