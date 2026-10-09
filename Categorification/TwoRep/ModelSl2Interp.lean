/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelSl2Decomp
import Categorification.Diagrams.KL3.Upward

/-!
# The interpretation of `U(sl₂)` in a strong 2-representation

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Theorem 5.5 for `g = sl₂` (with the dots normalized to `r_i = 1`, CL §2.6.1):
a strong 2-representation of `sl₂` gives a 2-representation of `U(sl₂)`. Here, on
hom categories: for outer regions `s₀`, `t₀` with `s₀ ≡ n₀ (mod 2)`, the `sl₂` model of
`Categorification.TwoRep.ModelSl2` respects every relation of KL III's presentation
`pres sl2RootDatum k` (Definition 3.1: the zigzags, cyclicity of dots and crossings, the nilHecke
relations, the bubble, curl and decomposition relations; the relations between differently
labelled strands are vacuous for `sl₂`), so it descends to a linear functor `interpU` on `U(sl₂)`.
Compatibility with horizontal composition is the whiskering and interchange calculus of
`Categorification.Diagrams.BicatInterp` (`mapChain_whisker`, `functor_map_gh_eq_hg`).

Only regions of the parity of the string matter: a word whose outer region has the parity of `n₀`
has all its regions of that parity (`par_endR`, `par_of_cond`); the relations are checked there.

## Main results

* `StrongSl2.relations_killed`: every relation of `U(sl₂)`, read with its own outer regions;
* `StrongSl2.respects_sl2`, `StrongSl2.interpU`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

section Model

open GradedHomBicat GradedHomCat
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]

namespace StrongSl2

variable (S : StrongSl2 k B)

attribute [local irreducible] KL3.Diagram.sh

omit [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem par_sh (l : Letter Unit) {s : ℤ} (hs : ∃ q : ℤ, s = S.n₀ + 2 * q) :
    ∃ q : ℤ, s - sh sl2RootDatum l = S.n₀ + 2 * q := by
  obtain ⟨q, rfl⟩ := hs
  obtain ⟨b, i⟩ := l
  cases b
  · exact ⟨q + 1, by simp only [sh, sgn_false, sl2RootDatum, neg_smul, one_smul]; ring⟩
  · exact ⟨q - 1, by simp only [sh, sgn_true, sl2RootDatum, one_smul]; ring⟩

omit [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- Reading a well-formed word preserves the parity of the regions. -/
theorem par_endR : ∀ (w : List (Col Unit ℤ)) (s : ℤ), (psig sl2RootDatum).ok s w →
    (∃ q : ℤ, s = S.n₀ + 2 * q) → ∃ q : ℤ, (psig sl2RootDatum).endR s w = S.n₀ + 2 * q
  | [], _, _, hs => hs
  | c :: w, s, h, hs => by
    have h' : sh sl2RootDatum c.l + c.r = s ∧ (psig sl2RootDatum).ok c.r w := h
    refine par_endR w c.r h'.2 ?_
    obtain ⟨q, hq⟩ := par_sh (S := S) c.l hs
    exact ⟨q, by rw [← hq, ← h'.1]; ring⟩

omit [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem par_sh_add (l : Letter Unit) {s : ℤ} (hs : ∃ q : ℤ, sh sl2RootDatum l + s = S.n₀ + 2 * q) :
    ∃ q : ℤ, s = S.n₀ + 2 * q := by
  obtain ⟨q, hq⟩ := par_sh (S := S) l hs
  exact ⟨q, by rw [← hq]; ring⟩

set_option maxHeartbeats 2000000 in
/-- **The relations of `U(sl₂)` hold in the `sl₂` model**: every relation of KL III's
presentation `pres sl2RootDatum k` (the zigzags and the relations of Definition 3.1), read with its
own outer regions, is killed by the interpretation, as soon as its regions have the parity of the
string. -/
theorem relations_killed (i : (pres sl2RootDatum k).Rel)
    (hpar : ∃ q : ℤ, ((pres sl2RootDatum k).dom i).start = S.n₀ + 2 * q) :
    (freeLift k (interp (genImg S) ((pres sl2RootDatum k).dom i).start
      ((pres sl2RootDatum k).dom i).endR).functor).map ((pres sl2RootDatum k).rel i) = 0 := by
  rcases i with (i | c | c) | r
  · exact i.elim
  · change (freeLift k (interp (genImg S) _ _).functor).map
      (LinDiagram.of (Pivotal.zigL (inv sl2RootDatum).toColourDuality c) - LinDiagram.of (𝟙 _)) = 0
    set_option backward.isDefEq.respectTransparency false in
    rw [Functor.map_sub, freeLift_map_of, freeLift_map_of, CategoryTheory.Functor.map_id]
    rw [sub_eq_zero]
    exact zigL_eq S c
  · change (freeLift k (interp (genImg S) _ _).functor).map
      (LinDiagram.of (Pivotal.zigR (inv sl2RootDatum).toColourDuality c) - LinDiagram.of (𝟙 _)) = 0
    set_option backward.isDefEq.respectTransparency false in
    rw [Functor.map_sub, freeLift_map_of, freeLift_map_of, CategoryTheory.Functor.map_id]
    rw [sub_eq_zero]
    exact zigR_eq S c
  · have hrel : (pres sl2RootDatum k).rel (Sum.inr r) = relation k r := rfl
    rw [hrel]
    rcases r with ⟨i, μ⟩ | ⟨i, μ⟩ | ⟨i, lam, α, h⟩ | ⟨i, lam, α, h⟩ | ⟨i, lam, h⟩ | ⟨i, lam, h⟩ |
      ⟨i, lam⟩ | ⟨i, μ⟩ | ⟨i, lam⟩ | ⟨i, lam⟩ | ⟨j, i, μ⟩ | ⟨j, i, μ⟩ | ⟨i, j, h, μ⟩ |
      ⟨i, j, h, μ⟩ | ⟨μ, r⟩
    · cases i
      set_option backward.isDefEq.respectTransparency false in
      rw [relation, Functor.map_sub, freeLift_map_of, freeLift_map_of, sub_eq_zero]
      exact cycDotR S μ
    · cases i
      set_option backward.isDefEq.respectTransparency false in
      rw [relation, Functor.map_sub, freeLift_map_of, freeLift_map_of, sub_eq_zero]
      exact cycDotL S μ
    · cases i
      set_option backward.isDefEq.respectTransparency false in
      rw [relation, freeLift_map_of]
      exact cwReal_eq_zero S hpar (by have h' := h; rw [ip_sl2] at h'; exact h')
    · cases i
      set_option backward.isDefEq.respectTransparency false in
      rw [relation, freeLift_map_of]
      exact ccwReal_eq_zero S hpar (by have h' := h; rw [ip_sl2] at h'; exact h')
    · cases i
      set_option backward.isDefEq.respectTransparency false in
      rw [relation, Functor.map_sub, freeLift_map_of, freeLift_map_of,
        CategoryTheory.Functor.map_id, sub_eq_zero, ip_sl2]
      exact cwReal_deg_zero S hpar (by have h' := h; rw [ip_sl2] at h'; exact h')
    · cases i
      set_option backward.isDefEq.respectTransparency false in
      rw [relation, Functor.map_sub, freeLift_map_of, freeLift_map_of,
        CategoryTheory.Functor.map_id, sub_eq_zero, ip_sl2]
      exact ccwReal_deg_zero S hpar (by have h' := h; rw [ip_sl2] at h'; exact h')
    · cases i
      exact rel_curlR S (par_sh_add (S := S) (up ()) hpar)
    · cases i
      exact rel_curlL S (par_sh_add (S := S) (up ()) hpar)
    · cases i
      exact rel_decompEF S (par_sh_add (S := S) (dn ()) (par_sh_add (S := S) (up ()) hpar))
    · cases i
      exact rel_decompFE S (par_sh_add (S := S) (up ()) (par_sh_add (S := S) (dn ()) hpar))
    · cases i; cases j
      set_option backward.isDefEq.respectTransparency false in
      rw [relation, Functor.map_sub, freeLift_map_of, freeLift_map_of, sub_eq_zero]
      exact cycCrossR S μ
    · cases i; cases j
      set_option backward.isDefEq.respectTransparency false in
      rw [relation, Functor.map_sub, freeLift_map_of, freeLift_map_of, sub_eq_zero]
      exact cycCrossL S μ
    · exact (h (Subsingleton.elim _ _)).elim
    · exact (h (Subsingleton.elim _ _)).elim
    · rcases r with c | ⟨c, d, h⟩ | c | ⟨c, d, h⟩ | c | ⟨c, d, h⟩ | ⟨c, d, e, h⟩ | ⟨c, d, h⟩
      · cases c
        set_option backward.isDefEq.respectTransparency false in
        rw [relation, KLR.Diagram.relation, upLin_of, freeLift_map_of]
        exact klr_sqEq S μ
      · exact (h (Subsingleton.elim _ _)).elim
      · cases c
        set_option backward.isDefEq.respectTransparency false in
        rw [relation, KLR.Diagram.relation, upLin_sub, upLin_sub, upLin_of, upLin_of, upLin_of,
          Functor.map_sub, Functor.map_sub, freeLift_map_of, freeLift_map_of, freeLift_map_of]
        exact klr_slideLEq S μ
      · exact (h (Subsingleton.elim _ _)).elim
      · cases c
        set_option backward.isDefEq.respectTransparency false in
        rw [relation, KLR.Diagram.relation, upLin_sub, upLin_sub, upLin_of, upLin_of, upLin_of,
          Functor.map_sub, Functor.map_sub, freeLift_map_of, freeLift_map_of, freeLift_map_of]
        exact klr_slideREq S μ
      · exact (h (Subsingleton.elim _ _)).elim
      · cases c; cases d; cases e
        set_option backward.isDefEq.respectTransparency false in
        rw [relation, KLR.Diagram.relation, upLin_sub, upLin_of, upLin_of,
          Functor.map_sub, freeLift_map_of, freeLift_map_of]
        exact klr_braid S μ
      · exact (h (Subsingleton.elim _ _)).elim

omit [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- A relation whiskered into a word with outer region of the parity of the string has its own
regions of that parity. -/
theorem par_of_cond {s₀ t₀ : ℤ} (hs : ∃ q : ℤ, s₀ = S.n₀ + 2 * q)
    {a u : Obj (psig sl2RootDatum)} {v : List (Col Unit ℤ)} (hw : a.WhiskerOK u v)
    (hc : Cond (S := psig sl2RootDatum) s₀ t₀ (a.whisker u v)) :
    ∃ q : ℤ, a.start = S.n₀ + 2 * q := by
  have hu : u.start = s₀ := hc.2.2
  have h := par_endR (S := S) u.word u.start hw.1 (hu ▸ hs)
  rw [show (psig sl2RootDatum).endR u.start u.word = a.start from hw.2.1] at h
  exact h

/-- **The `sl₂` model respects the relations of `U(sl₂)`** (KL III Definition 3.1 for `sl₂`, with
CL's scalars `r_i = 1`): for outer regions `s₀`, `t₀` with `s₀ ≡ n₀ (mod 2)`, the interpretation of
the free 2-category on the signature of `U` in the hom category `K^•(q t₀, q s₀)` of the
graded-Hom bicategory descends to `U`. -/
theorem respects_sl2 {s₀ : ℤ} (hs : ∃ q : ℤ, s₀ = S.n₀ + 2 * q) (t₀ : ℤ) :
    (pres sl2RootDatum k).Respects (interp (genImg S) s₀ t₀).functor :=
  respects (genImg S) (pres sl2RootDatum k) s₀ t₀
    (fun i _ _ hw hc => relations_killed S i (par_of_cond (S := S) hs hw hc))
    (fun g => Signature.IsEven.odd_eq_false g)

/-- **The 2-representation of `U(sl₂)` defined by a strong 2-representation**,
on hom categories (CL Theorem 5.5 for `g = sl₂`, with `r_i = 1`): for outer regions `s₀`, `t₀`
with `s₀ ≡ n₀ (mod 2)`, the linear functor from the 2-morphisms of `U` between 1-morphisms
`t₀ → s₀` (reading the regions from the right) to `K^•(q t₀, q s₀)`. -/
def interpU {s₀ : ℤ} (hs : ∃ q : ℤ, s₀ = S.n₀ + 2 * q) (t₀ : ℤ) :
    (pres sl2RootDatum k).Presented ⥤
      (S.model.lift.obj (fo (S := psig sl2RootDatum) t₀) ⟶
        S.model.lift.obj (fo (S := psig sl2RootDatum) s₀)) :=
  (pres sl2RootDatum k).lift (respects_sl2 S hs t₀)

end StrongSl2

end Model

end Categorification.TwoRep
