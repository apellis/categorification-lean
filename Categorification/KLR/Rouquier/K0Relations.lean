/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Rouquier.SerreGrading
import Categorification.KLR.KL2.K0Relations
import Categorification.KLR.Rouquier.SerreCorrection
import Categorification.KLR.Rouquier.SerreBoundary
import Categorification.KLR.Rouquier.SerreSupports

/-!
# The graded Serre window in projective Grothendieck groups

Rouquier, *2-Kac–Moody algebras*, arXiv:0812.5023v1, §4.1.1,
Proposition 4.2. The homogeneous contracting relation between the divided-power
crossing maps gives an alternating relation in graded projective `K₀`.
The assembly uses the general idempotent zigzag lemma, as in KL II,
arXiv:0804.2080v1, §3, Proposition 6 and Corollary 7.

The initial criterion states the normalized contracting relation explicitly;
it isolates the graded `K₀` argument from the polynomial calculations.
-/

noncomputable section

namespace Categorification.KLR.Rouquier

open MvPolynomial KLRAlgebra QuantumGroup KL2 Categorification.Graded
open LaurentPolynomial Finset

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I} {C : CartanDatum I}
  {t : Seq ν} {p N : ℕ} {i j : I}

local notation "A" => KLRAlgebra k Q ν

private theorem hflip_zsmul (c : ℤ) (a : A) : hflip (c • a) = c • hflip a :=
  map_zsmul (AddMonoidHom.mk' (hflip : A → A) hflip_add) c a

private theorem hflip_neg (a : A) : hflip (-a) = -hflip a :=
  map_neg (AddMonoidHom.mk' (hflip : A → A) hflip_add) a

private theorem neg_one_pow_mul (n : ℕ) (a : A) :
    (-1 : A) ^ n * a = ((-1 : ℤ) ^ n) • a := by
  rw [zsmul_eq_mul]
  push_cast
  rfl

private theorem inv_smul_mul_idem (u : kˣ) {E X : A} (hE : IsIdempotentElem E) (z : ℤ)
    (hX : X = (u : k) • (z • E)) : (↑(u⁻¹) : k) • (X * E) = z • E := by
  rw [hX, smul_mul_assoc, smul_mul_assoc, hE.eq, smul_smul]
  simp only [← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

private theorem neg_one_pow_pred {a : ℕ} (ha : 1 ≤ a) :
    -((-1 : ℤ) ^ (a - 1)) = (-1 : ℤ) ^ a := by
  conv_rhs => rw [show a = a - 1 + 1 by omega, pow_succ, mul_neg_one]

variable (hpN : p + N < ν.card)
  (ht₀ : ∀ r : Fin ν.card, (r : ℕ) = p → t.lbl r = j)
  (ht : ∀ r : Fin ν.card, p < r → (r : ℕ) ≤ p + N → t.lbl r = i)

include hpN ht₀ ht in
theorem serreAm_mul_serreAp (u : kˣ) {a : ℕ} (ha : a + 1 ≤ N) :
    (serreAm u t p N (a + 1) * serreAp t p N a : A) =
      (↑(u⁻¹) : k) • ((aminus t p N (a + 1) * aplus t p N a) * etop t p N a) := by
  rw [serreAm, serreAp, ite_eq_left ⟨by omega, ha⟩, ite_eq_left ha,
    smul_mul_assoc, mul_assoc, ← mul_assoc (etop t p N (a + 1)),
    etop_mul_aplus hpN ht₀ ht ha, ← mul_assoc]

include hpN ht₀ ht in
theorem serreAp_pred_mul_serreAm (u : kˣ) {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ N) :
    (serreAp t p N (a - 1) * serreAm u t p N a : A) =
      (↑(u⁻¹) : k) • ((aplus t p N (a - 1) * aminus t p N a) * etop t p N a) := by
  rw [serreAp, serreAm, ite_eq_left (show a - 1 + 1 ≤ N by omega),
    ite_eq_left ⟨ha1, ha⟩, mul_smul_comm, mul_assoc,
    ← mul_assoc (etop t p N (a - 1)), etop_mul_aminus hpN ht₀ ht ha1 ha, ← mul_assoc]

include hpN ht₀ ht in
/-- The leading coefficient normalization makes the raw Serre homotopy
identities a signed contracting relation on the divided-power idempotents. -/
theorem serre_rel (hQ : IsRouquierQ C Q) (hij : i ≠ j) (hN : N = C.dij i j + 1)
    {a : ℕ} (ha : a ≤ N) :
    (serreAm (hQ.leadingUnit i j hij) t p N (a + 1) * serreAp t p N a -
      serreAp t p N (a - 1) * serreAm (hQ.leadingUnit i j hij) t p N a : A) =
        ((-1 : ℤ) ^ a) • etop t p N a := by
  let u := hQ.leadingUnit i j hij
  have hN1 : 1 ≤ N := by omega
  have hcoeff : (Q i j).coeff (Finsupp.single 0 (N - 1)) = (u : k) := by
    rw [show N - 1 = C.dij i j by omega, IsRouquierQ.coe_leadingUnit]
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · subst a
    rw [serreAm_of_not u (show ¬(1 ≤ 0 ∧ 0 ≤ N) by omega), mul_zero, sub_zero,
      serreAm_mul_serreAp hpN ht₀ ht u hN1]
    have hb := serre_B hpN ht₀ ht hQ hij hN
    have hb' : (aminus t p N 1 * aplus t p N 0 : A) = (u : k) • etop t p N 0 := by
      simpa only [u, IsRouquierQ.coe_leadingUnit] using hb
    have hnorm := inv_smul_mul_idem u (isIdempotentElem_etop hpN ht₀ ht (a := 0) (by omega))
      (z := 1) (by simpa only [one_smul] using hb')
    simpa only [pow_zero, one_smul, Nat.zero_add] using hnorm
  · by_cases haN : a = N
    · subst a
      rw [serreAm_of_not u (show ¬(1 ≤ N + 1 ∧ N + 1 ≤ N) by omega), zero_mul, zero_sub,
        serreAp_pred_mul_serreAm hpN ht₀ ht u hN1 le_rfl]
      have hc := serre_C hpN ht₀ ht hQ hij hN
      have hc' : (aplus t p N (N - 1) * aminus t p N N : A) =
          (u : k) • (((-1 : ℤ) ^ (N - 1)) • etop t p N N) := by
        simpa only [← IsRouquierQ.coe_leadingUnit hQ i j hij, neg_one_pow_mul] using hc
      rw [inv_smul_mul_idem u (isIdempotentElem_etop hpN ht₀ ht le_rfl) _ hc',
        ← neg_smul, neg_one_pow_pred hN1]
    · have ha' : a + 1 ≤ N := by omega
      rw [serreAm_mul_serreAp hpN ht₀ ht u ha',
        serreAp_pred_mul_serreAm hpN ht₀ ht u ha0 ha, ← smul_sub, ← sub_mul]
      have hraw := serre_A (Q := Q) hpN ht₀ ht hij ha0 ha'
        (fun s hs => by simpa only [show N - 1 = C.dij i j by omega] using hQ.support_bound hij hs)
      have hraw' : (aminus t p N (a + 1) * aplus t p N a -
          aplus t p N (a - 1) * aminus t p N a : A) =
            (u : k) • (((-1 : ℤ) ^ a) • etop t p N a) := by
        rw [← neg_sub, hraw, hcoeff, neg_one_pow_mul, ← smul_neg, ← neg_smul,
          neg_one_pow_pred ha0]
      exact inv_smul_mul_idem u (isIdempotentElem_etop hpN ht₀ ht ha) _ hraw'

include hpN ht₀ ht in
theorem isIdempotentElem_hflip_etop {a : ℕ} (ha : a ≤ N) :
    IsIdempotentElem (hflip (etop t p N a : A)) := by
  unfold IsIdempotentElem
  rw [← hflip_mul, (isIdempotentElem_etop hpN ht₀ ht ha).eq]

include hpN ht₀ ht in
theorem hflip_etop_mem_grade (G : GradingDatum Q)
    (hΨ : ∀ c d, G.degΨ c d = -C.dot c d) {a : ℕ} (ha : a ≤ N) :
    hflip (etop t p N a : A) ∈ G.grade ν 0 :=
  G.hflip_mem_grade (fun c d => by rw [hΨ, hΨ, C.symm])
    (etop_mem_grade hpN ht₀ ht G ha)

/-- The reflected divided-power idempotents in the Serre window. -/
def serreE (t : Seq ν) (p N a : ℕ) : A := hflip (etop t p N a)

/-- The forward summand of the reflected Serre idempotent splitting. -/
def serreGp (u : kˣ) (t : Seq ν) (p N a : ℕ) : A :=
  hflip (((-1 : ℤ) ^ a) • (serreAm u t p N (a + 1) * serreAp t p N a))

/-- The reverse summand of the reflected Serre idempotent splitting. -/
def serreGm (u : kˣ) (t : Seq ν) (p N a : ℕ) : A :=
  hflip (-(((-1 : ℤ) ^ a) • (serreAp t p N (a - 1) * serreAm u t p N a)))

/-- The degree of the forward crossing map. -/
def serreDegree (C : CartanDatum I) (i j : I) (N a : ℕ) : ℤ :=
  -((N - a - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j

/-- The homogeneous, sequence-supported idempotent splitting used both in
ordinary `K₀` and in the weighted loading-family transport. -/
structure SerreZigzagData (G : GradingDatum Q) (C : CartanDatum I) (u : kˣ)
    (t : Seq ν) (p N : ℕ) (i j : I) : Prop where
  hE : ∀ a, a ≤ N → IsIdempotentElem (serreE t p N a : A)
  hE0 : ∀ a, a ≤ N → (serreE t p N a : A) ∈ G.grade ν 0
  hER : ∀ a, a ≤ N → (serreE t p N a * e (serreSeq t p a) : A) = serreE t p N a
  hpR : ∀ a, a ≤ N → (serreGp u t p N a * e (serreSeq t p a) : A) = serreGp u t p N a
  hmR : ∀ a, a ≤ N → (serreGm u t p N a * e (serreSeq t p a) : A) = serreGm u t p N a
  hsum : ∀ a, a ≤ N → (serreGp u t p N a + serreGm u t p N a : A) = serreE t p N a
  hpm : ∀ a, a ≤ N → (serreGp u t p N a * serreGm u t p N a : A) = 0
  hmp : ∀ a, a ≤ N → (serreGm u t p N a * serreGp u t p N a : A) = 0
  hpE : ∀ a, a ≤ N → (serreGp u t p N a * serreE t p N a : A) = serreGp u t p N a
  hmE : ∀ a, a ≤ N → (serreGm u t p N a * serreE t p N a : A) = serreGm u t p N a
  hxy : ∀ a, a < N → ∃ x y : A,
    x ∈ G.grade ν (serreDegree C i j N a) ∧ y ∈ G.grade ν (-serreDegree C i j N a) ∧
      x * e (serreSeq t p (a + 1)) = x ∧ y * e (serreSeq t p a) = y ∧
        x * y = serreGp u t p N a ∧ y * x = serreGm u t p N (a + 1)
  hGm : (serreGm u t p N 0 : A) = 0
  hGp : (serreGp u t p N N : A) = 0

include hpN ht₀ ht in
/-- The normalized contracting relation implies the graded Serre window.
The displayed algebraic relation is an explicit intermediate hypothesis;
the polynomial calculations supply it for Rouquier parameters. -/
theorem serre_zigzag_data_of_relation (G : GradingDatum Q)
    (hX : ∀ c, G.degX c = C.dot c c) (hΨ : ∀ c d, G.degΨ c d = -C.dot c d)
    (hij : i ≠ j) (hN : N = C.dij i j + 1) (u : kˣ)
    (hrel : ∀ a, a ≤ N →
      (serreAm u t p N (a + 1) * serreAp t p N a -
        serreAp t p N (a - 1) * serreAm u t p N a : A) =
          ((-1 : ℤ) ^ a) • etop t p N a) :
    SerreZigzagData G C u t p N i j := by
  let Ap : ℕ → A := serreAp t p N
  let Am : ℕ → A := serreAm u t p N
  let E : ℕ → A := etop t p N
  let X : ℕ → A := fun a => ((-1 : ℤ) ^ a) • (Am (a + 1) * Ap a)
  let Y : ℕ → A := fun a => -(((-1 : ℤ) ^ a) • (Ap (a - 1) * Am a))
  have hAm0 : Am 0 = 0 := serreAm_of_not u (by omega)
  have hAmN : Am (N + 1) = 0 := serreAm_of_not u (by omega)
  have hY0 : Y 0 = 0 := by simp only [Y, hAm0, mul_zero, smul_zero, neg_zero]
  have hsum : ∀ a, a ≤ N → X a + Y a = E a := by
    intro a ha
    change ((-1 : ℤ) ^ a) • _ + -(((-1 : ℤ) ^ a) • _) = _
    rw [← sub_eq_add_neg, ← smul_sub, hrel a ha, smul_smul]
    have hs : ((-1 : ℤ) ^ a) * ((-1 : ℤ) ^ a) = 1 := by rw [← mul_pow]; simp
    rw [hs, one_smul]
  have hAA : ∀ a, Am a * Am (a + 1) = 0 :=
    fun a => serreAm_mul_serreAm_succ hpN ht₀ ht hij u a
  have hPP : ∀ a, 1 ≤ a → Ap a * Ap (a - 1) = 0 := by
    intro a ha
    have h := serreAp_succ_mul_serreAp (k := k) (Q := Q) hpN ht₀ ht hij (a - 1)
    rwa [show a - 1 + 1 = a by omega] at h
  have hYX : ∀ a, Y a * X a = 0 := by
    intro a
    simp only [X, Y, neg_mul, smul_mul_smul_comm, mul_assoc, ← mul_assoc (Am a),
      hAA, zero_mul, mul_zero, smul_zero, neg_zero]
  have hXY : ∀ a, X a * Y a = 0 := by
    intro a
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst a; rw [hY0, mul_zero]
    · simp only [X, Y, mul_neg, smul_mul_smul_comm, mul_assoc, ← mul_assoc (Ap a),
        hPP a ha, zero_mul, mul_zero, smul_zero, neg_zero]
  have hEX : ∀ a, E a * X a = X a := by
    intro a
    have he : E a * Am (a + 1) = Am (a + 1) := by
      have he := etop_mul_serreAm (k := k) (Q := Q) hpN ht₀ ht u (a + 1)
      simpa only [Nat.add_sub_cancel] using he
    simp only [X, mul_smul_comm, ← mul_assoc, he]
  have hEY : ∀ a, E a * Y a = Y a := by
    intro a
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst a; rw [hY0, mul_zero]
    · have he : E a * Ap (a - 1) = Ap (a - 1) := by
        have he := etop_mul_serreAp (k := k) (Q := Q) hpN ht₀ ht (a - 1)
        simpa only [show a - 1 + 1 = a by omega] using he
      simp only [Y, mul_neg, mul_smul_comm, ← mul_assoc, he]
  have hflipmem : ∀ {d : ℤ} {a : A}, a ∈ G.grade ν d → hflip a ∈ G.grade ν d :=
    fun ha => G.hflip_mem_grade (fun c d => by rw [hΨ, hΨ, C.symm]) ha
  have hER : ∀ a, a ≤ N → (hflip (E a) * e (serreSeq t p a) : A) = hflip (E a) :=
    fun a ha => hflip_etop_mul_e hpN ht₀ ht ha
  have hpE : ∀ a, (hflip (X a) * hflip (E a) : A) = hflip (X a) :=
    fun a => by rw [← hflip_mul, hEX]
  have hmE : ∀ a, (hflip (Y a) * hflip (E a) : A) = hflip (Y a) :=
    fun a => by rw [← hflip_mul, hEY]
  refine ⟨(fun a ha => isIdempotentElem_hflip_etop hpN ht₀ ht ha),
    (fun a ha => hflip_etop_mem_grade hpN ht₀ ht G hΨ ha), hER, ?_, ?_,
    (fun a ha => by change hflip (X a) + hflip (Y a) = hflip (E a); rw [← hflip_add, hsum a ha]),
    (fun a _ => by change hflip (X a) * hflip (Y a) = 0; rw [← hflip_mul, hYX, hflip_zero]),
    (fun a _ => by change hflip (Y a) * hflip (X a) = 0; rw [← hflip_mul, hXY, hflip_zero]),
    (fun a _ => hpE a), (fun a _ => hmE a), ?_,
    (by change hflip (Y 0) = 0; rw [hY0, hflip_zero]),
    (by change hflip (X N) = 0; simp only [X, hAmN, zero_mul, smul_zero, hflip_zero])⟩
  · intro a ha
    change hflip (X a) * e (serreSeq t p a) = hflip (X a)
    calc
      _ = (hflip (X a) * hflip (E a)) * e (serreSeq t p a) := by rw [hpE]
      _ = _ := by rw [mul_assoc, hER a ha, hpE]
  · intro a ha
    change hflip (Y a) * e (serreSeq t p a) = hflip (Y a)
    calc
      _ = (hflip (Y a) * hflip (E a)) * e (serreSeq t p a) := by rw [hmE]
      _ = _ := by rw [mul_assoc, hER a ha, hmE]
  · intro a ha
    refine ⟨((-1 : ℤ) ^ a) • hflip (Ap a), hflip (Am (a + 1)),
      zsmul_mem (hflipmem (serreAp_mem_grade hpN ht₀ ht G hX hΨ (by omega))) _, ?_, ?_, ?_, ?_, ?_⟩
    · apply hflipmem
      have h := serreAm_mem_grade (k := k) (Q := Q) hpN ht₀ ht G hX hΨ u
        (a := a + 1) (by omega) (by omega)
      convert h using 2
      have hd := C.dij_mul hij
      have hN' : (N : ℤ) = C.dij i j + 1 := by exact_mod_cast hN
      have he₁ : ((N - a - 1 : ℕ) : ℤ) = N - a - 1 := by omega
      have he₂ : ((a + 1 - 1 : ℕ) : ℤ) = a := by omega
      rw [serreDegree, he₁, he₂]
      linear_combination hd + C.dot i i * hN'
    · rw [smul_mul_assoc, hflip_serreAp_mul_e hpN ht₀ ht]
    · have h := hflip_serreAm_mul_e (k := k) (Q := Q) hpN ht₀ ht u (a + 1)
      simpa only [Nat.add_sub_cancel] using h
    · change ((-1 : ℤ) ^ a) • hflip (Ap a) * hflip (Am (a + 1)) = hflip (X a)
      simp only [X]
      rw [hflip_zsmul, hflip_mul, smul_mul_assoc]
    · change hflip (Am (a + 1)) * ((-1 : ℤ) ^ a) • hflip (Ap a) = hflip (Y (a + 1))
      simp only [Y]
      rw [hflip_neg, hflip_zsmul, hflip_mul, mul_smul_comm,
        show a + 1 - 1 = a by omega, pow_succ, mul_neg_one, neg_smul, neg_neg]

include hpN ht₀ ht in
theorem K0_serre_window_of_relation (G : GradingDatum Q)
    (hX : ∀ c, G.degX c = C.dot c c) (hΨ : ∀ c d, G.degΨ c d = -C.dot c d)
    (hij : i ≠ j) (hN : N = C.dij i j + 1) (u : kˣ)
    (hrel : ∀ a, a ≤ N →
      (serreAm u t p N (a + 1) * serreAp t p N a -
        serreAp t p N (a - 1) * serreAm u t p N a : A) =
          ((-1 : ℤ) ^ a) • etop t p N a)
    (sh : ℕ → ℤ)
    (hsh : ∀ a, a < N → sh (a + 1) = sh a +
      (-((N - a - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j))
    (P : ℕ → K0 (G.grade ν))
    (hP : ∀ a (ha : a ≤ N), P a = K0.of (GProj.ofIdempotent
      (hflip (etop t p N a : A)) (isIdempotentElem_hflip_etop hpN ht₀ ht ha)
        (hflip_etop_mem_grade hpN ht₀ ht G hΨ ha))) :
    ∑ a ∈ range (N + 1), ((-1 : LaurentPolynomial ℤ) ^ a * T (-sh a)) • P a = 0 := by
  let D := serre_zigzag_data_of_relation hpN ht₀ ht G hX hΨ hij hN u hrel
  exact Graded.K0.sum_neg_one_pow_smul_of_zigzag D.hE D.hE0 D.hsum D.hpm D.hmp D.hpE D.hmE
    (fun a ha => by
      obtain ⟨x, y, hx, hy, _, _, hxy, hyx⟩ := D.hxy a ha
      exact ⟨x, y, hx, hy, hxy, hyx⟩)
    D.hGm D.hGp hsh P hP

include hpN ht₀ ht in
/-- The sequence-supported homogeneous Serre zigzag for Rouquier parameters. -/
theorem serre_zigzag_data (G : GradingDatum Q)
    (hX : ∀ c, G.degX c = C.dot c c) (hΨ : ∀ c d, G.degΨ c d = -C.dot c d)
    (hQ : IsRouquierQ C Q) (hij : i ≠ j) (hN : N = C.dij i j + 1) :
    SerreZigzagData G C (hQ.leadingUnit i j hij) t p N i j :=
  serre_zigzag_data_of_relation hpN ht₀ ht G hX hΨ hij hN (hQ.leadingUnit i j hij)
    (fun _ ha => serre_rel hpN ht₀ ht hQ hij hN ha)

include hpN ht₀ ht in
/-- Rouquier arXiv:0812.5023v1, §4.1.1, Proposition 4.2: the graded
projective Serre relation for every homogeneous Rouquier polynomial over
every commutative ring. The window may occur inside an arbitrary sequence.
The idempotents are reflected to give left projectives, as in KL II,
arXiv:0804.2080v1, §3, Corollary 7. -/
theorem K0_serre_window (hQ : IsRouquierQ C Q) (hij : i ≠ j)
    (hN : N = C.dij i j + 1) (sh : ℕ → ℤ)
    (hsh : ∀ a, a < N → sh (a + 1) = sh a +
      (-((N - a - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j))
    (P : ℕ → K0 (hQ.gradingDatum.grade ν))
    (hP : ∀ a (ha : a ≤ N), P a = K0.of (GProj.ofIdempotent
      (hflip (etop t p N a : A)) (isIdempotentElem_hflip_etop hpN ht₀ ht ha)
        (hflip_etop_mem_grade hpN ht₀ ht hQ.gradingDatum (fun _ _ => rfl) ha))) :
    ∑ a ∈ range (N + 1), ((-1 : LaurentPolynomial ℤ) ^ a * T (-sh a)) • P a = 0 :=
  K0_serre_window_of_relation hpN ht₀ ht hQ.gradingDatum (fun _ => rfl) (fun _ _ => rfl)
    hij hN (hQ.leadingUnit i j hij) (fun _ ha => serre_rel hpN ht₀ ht hQ hij hN ha)
      sh hsh P hP

end Categorification.KLR.Rouquier
