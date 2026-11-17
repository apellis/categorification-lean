/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Rouquier.SerreGrading

/-!
# Sequence supports of the Serre zigzag

Supporting Rouquier, *2-Kac–Moody algebras*, arXiv:0812.5023v1, §4.1.1,
Proposition 4.2, and its transport to the evenly spaced loadings in Webster,
arXiv:1209.2463v4, §2.4, Theorem 2.19, roadmap C. Horizontal reflection of the
restricted Serre maps has right support on its target sequence before reflection.
This permits composition to be transported by individual matrix entries even
when different loading sequences define the same weighted chamber.
-/

noncomputable section

namespace Categorification.KLR.Rouquier

open KLRAlgebra KL2

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}
  {t : Seq ν} {p N : ℕ} {i j : I}

local notation "A" => KLRAlgebra k Q ν
local notation "S" => serreSeq t p

variable (hpN : p + N < ν.card)
  (ht₀ : ∀ r : Fin ν.card, (r : ℕ) = p → t.lbl r = j)
  (ht : ∀ r : Fin ν.card, p < r → (r : ℕ) ≤ p + N → t.lbl r = i)

include hpN ht₀ ht in
/-- The reflected divided-power idempotent is supported on its sequence. -/
theorem hflip_etop_mul_e {a : ℕ} (ha : a ≤ N) :
    (hflip (etop t p N a) * e (S a) : A) = hflip (etop t p N a) := by
  have he := congrArg (hflip : A → A) (e_mul_etop (k := k) (Q := Q) hpN ht₀ ht ha)
  simpa only [hflip_mul, hflip_e] using he

include hpN ht₀ ht in
/-- The reflected forward arrow has right sequence support at its unreflected target. -/
theorem hflip_serreAp_mul_e (a : ℕ) :
    (hflip (serreAp t p N a) * e (S (a + 1)) : A) = hflip (serreAp t p N a) := by
  have he : (e (S (a + 1)) * serreAp t p N a : A) = serreAp t p N a := by
    by_cases ha : a + 1 ≤ N
    · calc
        _ = e (S (a + 1)) * (etop t p N (a + 1) * serreAp t p N a) := by
          rw [etop_mul_serreAp hpN ht₀ ht]
        _ = (e (S (a + 1)) * etop t p N (a + 1)) * serreAp t p N a :=
          (mul_assoc _ _ _).symm
        _ = _ := by rw [e_mul_etop hpN ht₀ ht ha, etop_mul_serreAp hpN ht₀ ht]
    · rw [serreAp_of_not ha, mul_zero]
  have h := congrArg (hflip : A → A) he
  simpa only [hflip_mul, hflip_e] using h

include hpN ht₀ ht in
/-- The reflected reverse arrow has right sequence support at its unreflected target. -/
theorem hflip_serreAm_mul_e (u : kˣ) (a : ℕ) :
    (hflip (serreAm u t p N a) * e (S (a - 1)) : A) = hflip (serreAm u t p N a) := by
  have he : (e (S (a - 1)) * serreAm u t p N a : A) = serreAm u t p N a := by
    by_cases ha : 1 ≤ a ∧ a ≤ N
    · calc
        _ = e (S (a - 1)) * (etop t p N (a - 1) * serreAm u t p N a) := by
          rw [etop_mul_serreAm hpN ht₀ ht]
        _ = (e (S (a - 1)) * etop t p N (a - 1)) * serreAm u t p N a :=
          (mul_assoc _ _ _).symm
        _ = _ := by rw [e_mul_etop hpN ht₀ ht (by omega), etop_mul_serreAm hpN ht₀ ht]
    · rw [serreAm_of_not u ha, mul_zero]
  have h := congrArg (hflip : A → A) he
  simpa only [hflip_mul, hflip_e] using h

end Categorification.KLR.Rouquier
