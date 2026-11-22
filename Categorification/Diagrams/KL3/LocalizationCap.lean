/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Diagrams.KL3.LocalizationPlace

/-!
# Core morphisms of `U′` are closed under caps

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Lemma 3.29. Dots pass a cap (exactly on the far strands, and from one strand of the cap to the
other), and a cup followed by inverse dots and a cap is a negative bubble, which `U′` identifies
with a fake bubble of `U` (Definition 3.28).

## Main results

* `isIso_toLoc_dD`: dots are invertible in `U′`.
* `coreSet_comp_dD`, `coreSet_comp_inv_dD`: core morphisms are closed under dots and inverse
  dots on arbitrary strands.
* `dD_left_comp_cap`, `dD_right_comp_cap`, `dD_near_comp_cap`: dots pass a cap.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]

/-! ## Dots are invertible in `U′` -/

theorem isIso_toLoc_dD_single (μ : X) {t : List (Letter I)} {q : ℕ} (hq : q < t.length) :
    IsIso ((toLoc RD k).map (dD RD k μ t [q])) := by
  obtain ⟨u, l, w, rfl, rfl⟩ := exists_split_dot hq
  rw [show u ++ l :: w = u ++ [l] ++ w by simp]
  have e : dD RD k μ (u ++ [l] ++ w) [u.length] =
      dg RD k μ (u ++ [l] ++ w) (u ++ [l] ++ w) [(u, .dot l, w)] := by
    show dg _ _ _ _ _ (dotAt _ u.length ++ []) = _
    rw [List.append_nil, dotAt_eq' (show u ++ [l] ++ w = u ++ l :: w by simp) rfl]
  rw [e]
  infer_instance

theorem isIso_toLoc_dD (μ : X) (t : List (Letter I)) :
    ∀ (qs : List ℕ), (∀ q ∈ qs, q < t.length) → IsIso ((toLoc RD k).map (dD RD k μ t qs))
  | [], _ => by
    rw [show dD RD k μ t [] = 𝟙 _ from dg_nil μ t, CategoryTheory.Functor.map_id]
    infer_instance
  | q :: qs, h => by
    have hq : q < t.length := h q List.mem_cons_self
    have hqs : ∀ q ∈ qs, q < t.length := fun q' hq' => h q' (List.mem_cons_of_mem _ hq')
    rw [show q :: qs = [q] ++ qs from rfl, dD_append μ (by simpa using hq) hqs,
      Functor.map_comp]
    have := isIso_toLoc_dD μ t qs hqs
    have := isIso_toLoc_dD_single (RD := RD) (k := k) μ hq
    infer_instance

/-! ## Dots and inverse dots on core morphisms -/

/-- Core morphisms are closed under postcomposition with a dot on any strand. -/
theorem coreSet_comp_dD (μ : X) {t : List (Letter I)} {q : ℕ} (hq : q < t.length) {f}
    (hf : f ∈ coreSet RD k μ t) : f ≫ (toLoc RD k).map (dD RD k μ t [q]) ∈ coreSet RD k μ t :=
  coreSet_comp_of_comm μ _ (fun is his => ⟨[], is, dD RD k μ t [q], by simp, his, by
    rw [List.append_nil]; exact dD_comm μ (by simpa using hq) his⟩) hf

/-- A morphism that becomes a core morphism after some dots is a core morphism. -/
theorem coreSet_of_comp_dD (μ : X) {t : List (Letter I)} {qs : List ℕ}
    (hqs : ∀ q ∈ qs, q < t.length) {f}
    (hf : f ≫ (toLoc RD k).map (dD RD k μ t qs) ∈ coreSet RD k μ t) : f ∈ coreSet RD k μ t := by
  obtain ⟨is, his, g, e⟩ := hf
  have hb : ∀ i ∈ qs ++ is, i < t.length := by
    intro i h; rcases List.mem_append.1 h with h | h
    · exact hqs i h
    · exact his i h
  exact ⟨qs ++ is, hb, g, by rw [dD_append μ hqs his, Functor.map_comp, ← Category.assoc, e]⟩

/-! ## Dots pass a cap -/

/-- The cap `E_{l^∨} E_l → 1` between the strands `u` and `v`. -/
abbrev cp (μ : X) (u v : List (Letter I)) (l : Letter I) :
    (pres RD k).obj (ob RD μ (u ++ [l.dual, l] ++ v)) ⟶ (pres RD k).obj (ob RD μ (u ++ [] ++ v)) :=
  dg RD k μ (u ++ [l.dual, l] ++ v) (u ++ [] ++ v) [(u, .cap l, v)]

theorem sChain_cp (u v : List (Letter I)) (l : Letter I) :
    SChain (u ++ [l.dual, l] ++ v) [(u, .cap l, v)] (u ++ [] ++ v) :=
  ⟨rfl, rfl⟩

/-- A dot left of a cap passes it. -/
theorem dD_left_comp_cap (μ : X) (u v : List (Letter I)) (l : Letter I) {p : ℕ}
    (hp : p < u.length) :
    dD RD k μ (u ++ [l.dual, l] ++ v) [p] ≫ cp (RD := RD) (k := k) μ u v l =
      cp μ u v l ≫ dD RD k μ (u ++ [] ++ v) [p] := by
  obtain ⟨u₁, l', u₂, rfl, rfl⟩ := exists_split_dot hp
  have hb : ∀ (x : List (Letter I)), ∀ i ∈ [u₁.length], i < (u₁ ++ l' :: u₂ ++ x ++ v).length := by
    intro x i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi; simp
  rw [dg_comp (sChain_dotsL (hb _)) (sChain_cp _ v l),
    dg_comp (sChain_cp _ v l) (sChain_dotsL (hb _))]
  have e : ∀ (x : List (Letter I)), dotsL (u₁ ++ l' :: u₂ ++ x ++ v) [u₁.length] =
      [(u₁, .dot l', u₂ ++ x ++ v)] := by
    intro x
    rw [dotsL_cons, dotsL_nil,
      dotAt_eq' (show u₁ ++ l' :: u₂ ++ x ++ v = u₁ ++ l' :: (u₂ ++ x ++ v) by simp) rfl]
    rfl
  rw [e, e]
  have E := dg_ichg (RD := RD) (k := k) (μ := μ) (s₀ := u₁ ++ l' :: u₂ ++ [l.dual, l] ++ v)
    (t₀ := u₁ ++ l' :: u₂ ++ [] ++ v) [] [] u₁ v
    (A := [([], .dot l', u₂)]) (B := [([], .cap l, [])])
    (s := l' :: u₂) (s' := l' :: u₂) (t := [l.dual, l]) (t' := [])
    ⟨by simp, rfl⟩ ⟨rfl, rfl⟩
  convert E using 2 <;> simp [whL]

/-- A dot right of a cap passes it. -/
theorem dD_right_comp_cap (μ : X) (u v : List (Letter I)) (l : Letter I) {p : ℕ}
    (hp : u.length + 2 ≤ p) (hp' : p < u.length + 2 + v.length) :
    dD RD k μ (u ++ [l.dual, l] ++ v) [p] ≫ cp (RD := RD) (k := k) μ u v l =
      cp μ u v l ≫ dD RD k μ (u ++ [] ++ v) [p - 2] := by
  obtain ⟨v₁, l', v₂, rfl, hv⟩ := exists_split_dot (t := v) (i := p - (u.length + 2)) (by omega)
  have hb : ∀ i ∈ [p], i < (u ++ [l.dual, l] ++ (v₁ ++ l' :: v₂)).length := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi; simp; omega
  have hb' : ∀ i ∈ [p - 2], i < (u ++ [] ++ (v₁ ++ l' :: v₂)).length := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi; simp; omega
  rw [dg_comp (sChain_dotsL hb) (sChain_cp u _ l),
    dg_comp (sChain_cp u _ l) (sChain_dotsL hb')]
  have e : dotsL (u ++ [l.dual, l] ++ (v₁ ++ l' :: v₂)) [p] =
      [(u ++ [l.dual, l] ++ v₁, .dot l', v₂)] := by
    rw [dotsL_cons, dotsL_nil,
      dotAt_eq' (show u ++ [l.dual, l] ++ (v₁ ++ l' :: v₂) = (u ++ [l.dual, l] ++ v₁) ++ l' :: v₂
        by simp) (by simp; omega)]
    rfl
  have e' : dotsL (u ++ [] ++ (v₁ ++ l' :: v₂)) [p - 2] =
      [(u ++ [] ++ v₁, .dot l', v₂)] := by
    rw [dotsL_cons, dotsL_nil,
      dotAt_eq' (show u ++ [] ++ (v₁ ++ l' :: v₂) = (u ++ [] ++ v₁) ++ l' :: v₂
        by simp) (by simp; omega)]
    rfl
  rw [e, e']
  have E := dg_ichg (RD := RD) (k := k) (μ := μ)
    (s₀ := u ++ [l.dual, l] ++ (v₁ ++ l' :: v₂))
    (t₀ := u ++ [] ++ (v₁ ++ l' :: v₂)) [] [] u v₂
    (A := [([], .cap l, [])]) (B := [(v₁, .dot l', [])])
    (s := [l.dual, l]) (s' := []) (t := v₁ ++ [l']) (t' := v₁ ++ [l'])
    ⟨rfl, rfl⟩ ⟨by simp, by simp⟩
  convert E.symm using 2 <;> simp [whL]

/-- A dot on the right strand of a cap equals a dot on its left strand (cyclicity, KL III
(3.3)). -/
theorem dD_near_comp_cap (μ : X) (u v : List (Letter I)) (l : Letter I) :
    dD RD k μ (u ++ [l.dual, l] ++ v) [u.length + 1] ≫ cp (RD := RD) (k := k) μ u v l =
      dD RD k μ (u ++ [l.dual, l] ++ v) [u.length] ≫ cp μ u v l := by
  have h := congrArg (plcL RD k μ u v [l.dual, l] [])
    (dg_dotR_cap (RD := RD) (k := k) (wt RD μ v) l 0)
  rw [plcL_dg, plcL_dg] at h
  have hb : ∀ i ∈ [u.length + 1], i < (u ++ [l.dual, l] ++ v).length := by
    intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; subst hi; simp
  have hb' : ∀ i ∈ [u.length], i < (u ++ [l.dual, l] ++ v).length := by
    intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; subst hi; simp
  rw [dg_comp (sChain_dotsL hb) (sChain_cp u v l), dg_comp (sChain_dotsL hb') (sChain_cp u v l)]
  have e : dotsL (u ++ [l.dual, l] ++ v) [u.length + 1] = [(u ++ [l.dual], .dot l, v)] := by
    rw [dotsL_cons, dotsL_nil,
      dotAt_eq' (show u ++ [l.dual, l] ++ v = (u ++ [l.dual]) ++ l :: v by simp) (by simp)]
    rfl
  have e' : dotsL (u ++ [l.dual, l] ++ v) [u.length] = [(u, .dot l.dual, l :: v)] := by
    rw [dotsL_cons, dotsL_nil,
      dotAt_eq' (show u ++ [l.dual, l] ++ v = u ++ l.dual :: (l :: v) by simp) rfl]
    rfl
  rw [e, e']
  convert h using 2 <;> simp [whL]

/-! ## Negative bubbles -/

theorem iterComp_succ' {𝒞 : Type*} [Category 𝒞] {a : 𝒞} (f : a ⟶ a) :
    ∀ n, iterComp f (n + 1) = iterComp f n ≫ f
  | 0 => by simp [iterComp]
  | n + 1 => by
    show f ≫ iterComp f (n + 1) = (f ≫ iterComp f n) ≫ f
    rw [iterComp_succ' f n, Category.assoc]

theorem iterComp_comp_iterComp {𝒞 : Type*} [Category 𝒞] {a : 𝒞} {f g : a ⟶ a}
    (h : g ≫ f = 𝟙 a) : ∀ n, iterComp g n ≫ iterComp f n = 𝟙 a
  | 0 => by simp [iterComp]
  | n + 1 => by
    rw [iterComp_succ' f n]
    show (g ≫ iterComp g n) ≫ iterComp f n ≫ f = 𝟙 a
    rw [Category.assoc, ← Category.assoc (iterComp g n), iterComp_comp_iterComp h n,
      Category.id_comp, h]

omit [AddCommGroup Y] in
theorem diag_iterComp {S : Signature} {R : Type*} [CommRing R] (P : Presentation S R) {a : Obj S}
    (f : a ⟶ a) : ∀ n, P.diag (iterComp f n) = iterComp (P.diag f) n
  | 0 => P.diag_id a
  | n + 1 => by
    show P.diag (f ≫ iterComp f n) = P.diag f ≫ iterComp (P.diag f) n
    rw [Presentation.diag_comp, diag_iterComp P f n]

/-- The dots `x^n` on one strand, as an iterated composite. -/
theorem toLoc_dD_replicate (ν : X) (u : List (Letter I)) (l : Letter I) (w : List (Letter I)) :
    ∀ n, (toLoc RD k).map (dD RD k ν (u ++ [l] ++ w) (List.replicate n u.length)) =
      iterComp ((toLoc RD k).map (dg RD k ν (u ++ [l] ++ w) (u ++ [l] ++ w) [(u, .dot l, w)])) n
  | 0 => by
    rw [List.replicate_zero, show dD RD k ν (u ++ [l] ++ w) [] = 𝟙 _ from dg_nil ν _,
      CategoryTheory.Functor.map_id]
    rfl
  | n + 1 => by
    have hd : dD RD k ν (u ++ [l] ++ w) [u.length] =
        dg RD k ν (u ++ [l] ++ w) (u ++ [l] ++ w) [(u, .dot l, w)] := by
      show dg _ _ _ _ _ (dotAt _ u.length ++ []) = _
      rw [List.append_nil, dotAt_eq' (show u ++ [l] ++ w = u ++ l :: w by simp) rfl]
    rw [List.replicate_succ, show u.length :: List.replicate n u.length =
      [u.length] ++ List.replicate n u.length from rfl,
      dD_append ν (by simp) (by intro i hi; rw [List.eq_of_mem_replicate hi]; simp),
      Functor.map_comp, hd, toLoc_dD_replicate ν u l w n]
    rfl

/-- The position of the downward strand of the cap `E_{l^∨} E_l → 1`. -/
def capDn : Letter I → ℕ
  | (true, _) => 0
  | (false, _) => 1

/-- **A cup, inverse dots and a cap form a negative bubble**, which is the image of a 2-morphism
of `U` (Webster arXiv:1309.3796v2, Definition 3.28 and proof of Lemma 3.29). -/
theorem cup_invDots_cap (ν : X) (l : Letter I) (n : ℕ)
    (Y : (presLoc RD k).obj ((incl RD).obj (ob RD ν [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD ν [l.dual, l])))
    (hY : Y ≫ (toLoc RD k).map (dD RD k ν [l.dual, l] (List.replicate n (capDn l))) =
      (toLoc RD k).map (dg RD k ν [] [l.dual, l] [([], .cup l.dual, [])])) :
    ∃ h : (pres RD k).obj (ob RD ν []) ⟶ (pres RD k).obj (ob RD ν []),
      Y ≫ (toLoc RD k).map (dg RD k ν [l.dual, l] [] [([], .cap l, [])]) = (toLoc RD k).map h := by
  obtain ⟨b, i⟩ := l
  cases b with
  | false =>
    revert Y
    show ∀ Y : (presLoc RD k).obj ((incl RD).obj (ob RD ν [])) ⟶
        (presLoc RD k).obj ((incl RD).obj (ob RD ν [up i, dn i])),
      Y ≫ (toLoc RD k).map (dD RD k ν [up i, dn i] (List.replicate n 1)) =
        (toLoc RD k).map (dg RD k ν [] [up i, dn i] [([], .cup (up i), [])]) →
      ∃ h, Y ≫ (toLoc RD k).map (dg RD k ν [up i, dn i] [] [([], .cap (dn i), [])]) =
        (toLoc RD k).map h
    intro Y hY
    have hD := toLoc_dD_replicate (RD := RD) (k := k) ν [up i] (dn i) [] n
    have hinv := iterComp_comp_iterComp
      (IsIso.hom_inv_id ((toLoc RD k).map
        (dg RD k ν ([up i] ++ [dn i] ++ []) ([up i] ++ [dn i] ++ []) [([up i], .dot (dn i), [])])))
      n
    have hY' : Y = (toLoc RD k).map (dg RD k ν [] [up i, dn i] [([], .cup (up i), [])]) ≫
        (presLoc RD k).diag (iterComp (invDot RD ν [up i] i []) n) := by
      rw [← hY]
      change Y = (Y ≫ (toLoc RD k).map (dD RD k ν ([up i] ++ [dn i] ++ [])
        (List.replicate n [up i].length))) ≫ _
      rw [hD, diag_iterComp, diag_invDot_eq_inv, Category.assoc, hinv]
      exact (Category.comp_id Y).symm
    rw [hY']
    cases n with
    | zero =>
      refine ⟨dg RD k ν [] [up i, dn i] [([], .cup (up i), [])] ≫
        dg RD k ν [up i, dn i] [] [([], .cap (dn i), [])], ?_⟩
      have e0 : (presLoc RD k).diag (iterComp (invDot RD ν [up i] i []) 0) = 𝟙 _ :=
        (presLoc RD k).diag_id _
      exact (congrArg (fun z => (_ ≫ z) ≫ _) e0).trans
        ((congrArg (· ≫ _) (Category.comp_id _)).trans ((toLoc RD k).map_comp _ _).symm)
    | succ m =>
      refine ⟨(pres RD k).lin (cwL RD k ν i (-((m : ℤ) + 1))), ?_⟩
      rw [← cwNegHonest_eq, cwNegHonest, Presentation.diag_comp, Presentation.diag_comp,
        ← toLoc_diag, ← toLoc_diag, Category.assoc]
      rw [dg_of (show SChain [] [([], .cup (up i), [])] [up i, dn i] from by constructor <;> rfl),
        dg_of (show SChain [up i, dn i] [([], .cap (dn i), [])] [] from by constructor <;> rfl)]
      rfl
  | true =>
    revert Y
    show ∀ Y : (presLoc RD k).obj ((incl RD).obj (ob RD ν [])) ⟶
        (presLoc RD k).obj ((incl RD).obj (ob RD ν [dn i, up i])),
      Y ≫ (toLoc RD k).map (dD RD k ν [dn i, up i] (List.replicate n 0)) =
        (toLoc RD k).map (dg RD k ν [] [dn i, up i] [([], .cup (dn i), [])]) →
      ∃ h, Y ≫ (toLoc RD k).map (dg RD k ν [dn i, up i] [] [([], .cap (up i), [])]) =
        (toLoc RD k).map h
    intro Y hY
    have hD := toLoc_dD_replicate (RD := RD) (k := k) ν [] (dn i) [up i] n
    have hinv := iterComp_comp_iterComp
      (IsIso.hom_inv_id ((toLoc RD k).map
        (dg RD k ν ([] ++ [dn i] ++ [up i]) ([] ++ [dn i] ++ [up i]) [([], .dot (dn i), [up i])])))
      n
    have hY' : Y = (toLoc RD k).map (dg RD k ν [] [dn i, up i] [([], .cup (dn i), [])]) ≫
        (presLoc RD k).diag (iterComp (invDot RD ν [] i [up i]) n) := by
      rw [← hY]
      change Y = (Y ≫ (toLoc RD k).map (dD RD k ν ([] ++ [dn i] ++ [up i])
        (List.replicate n ([] : List (Letter I)).length))) ≫ _
      rw [hD, diag_iterComp, diag_invDot_eq_inv, Category.assoc, hinv]
      exact (Category.comp_id Y).symm
    rw [hY']
    cases n with
    | zero =>
      refine ⟨dg RD k ν [] [dn i, up i] [([], .cup (dn i), [])] ≫
        dg RD k ν [dn i, up i] [] [([], .cap (up i), [])], ?_⟩
      have e0 : (presLoc RD k).diag (iterComp (invDot RD ν [] i [up i]) 0) = 𝟙 _ :=
        (presLoc RD k).diag_id _
      exact (congrArg (fun z => (_ ≫ z) ≫ _) e0).trans
        ((congrArg (· ≫ _) (Category.comp_id _)).trans ((toLoc RD k).map_comp _ _).symm)
    | succ m =>
      refine ⟨(pres RD k).lin (ccwL RD k ν i (-((m : ℤ) + 1))), ?_⟩
      rw [← ccwNegHonest_eq, ccwNegHonest, Presentation.diag_comp, Presentation.diag_comp,
        ← toLoc_diag, ← toLoc_diag, Category.assoc]
      rw [dg_of (show SChain [] [([], .cup (dn i), [])] [dn i, up i] from by constructor <;> rfl),
        dg_of (show SChain [dn i, up i] [([], .cap (up i), [])] [] from by constructor <;> rfl)]
      rfl

/-! ## Negative bubbles between strands -/

theorem dotAt_whisk (u v t : List (Letter I)) {i : ℕ} (hi : i < t.length) :
    dotAt (u ++ t ++ v) (u.length + i) = (dotAt t i).map (whL u v) := by
  obtain ⟨t₁, l', t₂, rfl, rfl⟩ := exists_split_dot hi
  rw [dotAt_eq' (show u ++ (t₁ ++ l' :: t₂) ++ v = (u ++ t₁) ++ l' :: (t₂ ++ v) by simp)
    (by simp), dotAt_eq]
  simp [whL]

theorem dotsL_whisk (u v t : List (Letter I)) : ∀ {is : List ℕ}, (∀ i ∈ is, i < t.length) →
    dotsL (u ++ t ++ v) (is.map (u.length + ·)) = (dotsL t is).map (whL u v)
  | [], _ => rfl
  | i :: is, h => by
    rw [List.map_cons, dotsL_cons, dotsL_cons, List.map_append,
      dotAt_whisk u v t (h i List.mem_cons_self),
      dotsL_whisk u v t (fun j hj => h j (List.mem_cons_of_mem _ hj))]

theorem sChain_cupDual (l : Letter I) : SChain [] [([], .cup l.dual, [])] [l.dual, l] := by
  obtain ⟨b, i⟩ := l
  cases b <;> exact ⟨rfl, rfl⟩

theorem capDn_lt (l : Letter I) : capDn l < 2 := by
  obtain ⟨b, i⟩ := l
  cases b <;> simp [capDn]

/-- **A cup between strands followed by inverse dots on its downward strand**, which then
closes up with a cap to the image of a 2-morphism of `U`. -/
theorem cup_invDots_cap_placed (μ : X) (u v : List (Letter I)) (l : Letter I) (n : ℕ) :
    ∃ Z : (presLoc RD k).obj ((incl RD).obj (ob RD μ (u ++ [] ++ v))) ⟶
        (presLoc RD k).obj ((incl RD).obj (ob RD μ (u ++ [l.dual, l] ++ v))),
      Z ≫ (toLoc RD k).map (dD RD k μ (u ++ [l.dual, l] ++ v)
          (List.replicate n (u.length + capDn l))) =
        (toLoc RD k).map (dg RD k μ (u ++ [] ++ v) (u ++ [l.dual, l] ++ v)
          [(u, .cup l.dual, v)]) ∧
      ∃ h, Z ≫ (toLoc RD k).map (cp μ u v l) = (toLoc RD k).map h := by
  have hcup := sChain_cupDual l
  have hst : wt RD (wt RD μ v) [l.dual, l] = wt RD (wt RD μ v) [] := hcup.wt_eq RD _
  have hb : ∀ q ∈ List.replicate n (capDn l), q < [l.dual, l].length := by
    intro q hq; rw [List.eq_of_mem_replicate hq]; exact capDn_lt l
  have := isIso_toLoc_dD (RD := RD) (k := k) (wt RD μ v) [l.dual, l] _ hb
  obtain ⟨h, eh⟩ := cup_invDots_cap (RD := RD) (k := k) (wt RD μ v) l n
    ((toLoc RD k).map (dg RD k (wt RD μ v) [] [l.dual, l] [([], .cup l.dual, [])]) ≫
      CategoryTheory.inv ((toLoc RD k).map (dD RD k (wt RD μ v) [l.dual, l]
        (List.replicate n (capDn l))))) (by simp)
  have eD := toLoc_plcL RD k μ u v [l.dual, l] [l.dual, l] rfl
    (dD RD k (wt RD μ v) [l.dual, l] (List.replicate n (capDn l)))
  rw [show dD RD k (wt RD μ v) [l.dual, l] (List.replicate n (capDn l)) =
    dg RD k (wt RD μ v) _ _ (dotsL [l.dual, l] (List.replicate n (capDn l))) from rfl,
    plcL_dg, ← dotsL_whisk u v _ hb, List.map_replicate] at eD
  have eC := toLoc_plcL RD k μ u v [] [l.dual, l] hst
    (dg RD k (wt RD μ v) [] [l.dual, l] [([], .cup l.dual, [])])
  rw [plcL_dg, show List.map (whL u v) [([], Shape.cup l.dual, [])] = [(u, .cup l.dual, v)] by
    simp [whL]] at eC
  have eK := toLoc_plcL RD k μ u v [l.dual, l] [] hst.symm
    (dg RD k (wt RD μ v) [l.dual, l] [] [([], .cap l, [])])
  rw [plcL_dg] at eK
  refine ⟨plcLoc RD k μ u v hst ((toLoc RD k).map
    (dg RD k (wt RD μ v) [] [l.dual, l] [([], .cup l.dual, [])]) ≫
      CategoryTheory.inv ((toLoc RD k).map (dD RD k (wt RD μ v) [l.dual, l]
        (List.replicate n (capDn l))))), ?_, plcL RD k μ u v [] [] h, ?_⟩
  · have e : dD RD k μ (u ++ [l.dual, l] ++ v) (List.replicate n (u.length + capDn l)) =
        dg RD k μ (u ++ [l.dual, l] ++ v) (u ++ [l.dual, l] ++ v)
          (dotsL (u ++ [l.dual, l] ++ v) (List.replicate n (u.length + capDn l))) := rfl
    rw [e, eD, plcLoc_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact eC.symm
  · rw [show cp (RD := RD) (k := k) μ u v l = dg RD k μ _ _ (List.map (whL u v) [([], .cap l, [])])
      by simp [whL], eK, plcLoc_comp, eh]
    exact (toLoc_plcL RD k μ u v [] [] rfl h).symm

end Categorification.KL3.Diagram
