/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftBubble
import Categorification.Diagrams.CL.Specialize

/-!
# `Γ_N` respects the bubble relations `cwNeg`, `ccwNeg`, `cwOne`, `ccwOne`

KL III, arXiv:0807.3250v1, Definition 3.1, eq. (3.4) (label `eq_positivity_bubbles`: dotted
bubbles of negative degree vanish) and the normalization of degree-zero bubbles
(`Categorification.KL3.Diagram.Rel.cwNeg`, `ccwNeg`, `cwOne`, `ccwOne`); unchanged in
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, `eq_positivity_bubbles`, p. 8).

Each theorem is the hypothesis `hP` of `Categorification.Flag.gamma_respects` for the
corresponding relation index `.inr _` of `CL.presCL (slRootDatum m) K (CL.Sln.slnScalars K m)`.
By `evalB_cwReal`, `evalB_ccwReal`, a real bubble with `α` dots acts on every 1-morphism to its
right by `cwRealH`, `ccwRealH` (KL III Proposition 6.3); these vanish in negative degree and
are `1` in degree zero.
-/

-- Preserve elaboration of semireducible diagram transports.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory Categorification.KL3.Diagram.Signed

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

local notation "PCL" => CL.presCL (slRootDatum m) K (CL.Sln.slnScalars K m)

/-- `evalB` of an identity diagram. -/
theorem evalB_of_id_bub (dnScal : Fin m → Fin m → K) (a : Obj (psig RD)) (s : Wt m)
    (v : List (psig RD).Colour) (ha hb : WOK N s (a.word ++ v)) :
    evalB K N dnScal s v ha hb (LinDiagram.of (𝟙 a)) = BHom.id _ := by
  rw [evalB_of]
  rfl

/-- **`Γ_N` respects `cwNeg`** (KL III (3.4)): a clockwise bubble with `α < n - 1` dots is `0`. -/
theorem evalB_presCL_cwNeg (dnScal : Fin m → Fin m → K) (i : Fin m) (lam : Wt m) (α : ℕ)
    (h : (α : ℤ) < ip RD i lam - 1) (s : Wt m)
    (hs : s = ((PCL).dom (.inr (.cwNeg i lam α h))).start) (v : List (psig RD).Colour)
    (ha : WOK N s (((PCL).dom (.inr (.cwNeg i lam α h))).word ++ v))
    (hb : WOK N s (((PCL).cod (.inr (.cwNeg i lam α h))).word ++ v)) :
    evalB K N dnScal s v ha hb ((PCL).rel (.inr (.cwNeg i lam α h))) = 0 := by
  subst hs
  have hn := ip_eq_nH ha.realized i
  show evalB K N dnScal s v ha hb (LinDiagram.of (cwReal RD s i α)) = 0
  erw [evalB_cwReal dnScal s i α v ha hb]
  rw [cwRealH, ite_eq_right (by rw [hn] at h; simp only [nH] at h; omega), map_zero,
    BHom.mulB_zero']

/-- **`Γ_N` respects `ccwNeg`** (KL III (3.4)): a counterclockwise bubble with `α < -n - 1` dots
is `0`. -/
theorem evalB_presCL_ccwNeg (dnScal : Fin m → Fin m → K) (i : Fin m) (lam : Wt m) (α : ℕ)
    (h : (α : ℤ) < -ip RD i lam - 1) (s : Wt m)
    (hs : s = ((PCL).dom (.inr (.ccwNeg i lam α h))).start) (v : List (psig RD).Colour)
    (ha : WOK N s (((PCL).dom (.inr (.ccwNeg i lam α h))).word ++ v))
    (hb : WOK N s (((PCL).cod (.inr (.ccwNeg i lam α h))).word ++ v)) :
    evalB K N dnScal s v ha hb ((PCL).rel (.inr (.ccwNeg i lam α h))) = 0 := by
  subst hs
  have hn := ip_eq_nH ha.realized i
  show evalB K N dnScal s v ha hb (LinDiagram.of (ccwReal RD s i α)) = 0
  erw [evalB_ccwReal dnScal s i α v ha hb]
  rw [ccwRealH, ite_eq_right (by rw [hn] at h; simp only [nH] at h; omega), map_zero,
    BHom.mulB_zero']

/-- **`Γ_N` respects `cwOne`**: for `n ≥ 1`, the clockwise bubble of degree zero (with `n - 1`
dots) is the identity. -/
theorem evalB_presCL_cwOne (dnScal : Fin m → Fin m → K) (i : Fin m) (lam : Wt m)
    (h : 1 ≤ ip RD i lam) (s : Wt m)
    (hs : s = ((PCL).dom (.inr (.cwOne i lam h))).start) (v : List (psig RD).Colour)
    (ha : WOK N s (((PCL).dom (.inr (.cwOne i lam h))).word ++ v))
    (hb : WOK N s (((PCL).cod (.inr (.cwOne i lam h))).word ++ v)) :
    evalB K N dnScal s v ha hb ((PCL).rel (.inr (.cwOne i lam h))) = 0 := by
  subst hs
  have hn := ip_eq_nH ha.realized i
  show evalB K N dnScal s v ha hb (LinDiagram.of (cwReal RD s i (ip RD i s - 1).toNat) -
    LinDiagram.of (𝟙 _)) = 0
  rw [map_sub]
  erw [evalB_cwReal dnScal s i _ v ha hb, evalB_of_id_bub dnScal _ s v ha hb]
  rw [cwRealH, hn]
  rw [hn] at h
  simp only [nH] at h
  rw [ite_eq_left (by simp only [nH]; omega),
    show (nH (compOf N s) i - 1).toNat + (compOf N s) i.succ + 1 -
    (compOf N s) i.castSucc = 0 by simp only [nH]; omega, PsiH_zero, map_one, BHom.mulB_one]
  exact sub_self _

/-- **`Γ_N` respects `ccwOne`**: for `n ≤ -1`, the counterclockwise bubble of degree zero (with
`-n - 1` dots) is the identity. -/
theorem evalB_presCL_ccwOne (dnScal : Fin m → Fin m → K) (i : Fin m) (lam : Wt m)
    (h : ip RD i lam ≤ -1) (s : Wt m)
    (hs : s = ((PCL).dom (.inr (.ccwOne i lam h))).start) (v : List (psig RD).Colour)
    (ha : WOK N s (((PCL).dom (.inr (.ccwOne i lam h))).word ++ v))
    (hb : WOK N s (((PCL).cod (.inr (.ccwOne i lam h))).word ++ v)) :
    evalB K N dnScal s v ha hb ((PCL).rel (.inr (.ccwOne i lam h))) = 0 := by
  subst hs
  have hn := ip_eq_nH ha.realized i
  show evalB K N dnScal s v ha hb (LinDiagram.of (ccwReal RD s i (-ip RD i s - 1).toNat) -
    LinDiagram.of (𝟙 _)) = 0
  rw [map_sub]
  erw [evalB_ccwReal dnScal s i _ v ha hb, evalB_of_id_bub dnScal _ s v ha hb]
  rw [ccwRealH, hn]
  rw [hn] at h
  simp only [nH] at h
  rw [ite_eq_left (by simp only [nH]; omega),
    show (-nH (compOf N s) i - 1).toNat + (compOf N s) i.castSucc + 1 -
    (compOf N s) i.succ = 0 by simp only [nH]; omega, PhiH_zero, map_one, BHom.mulB_one]
  exact sub_self _

end Categorification.Flag

end
