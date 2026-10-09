/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.NoMix

/-!
# Brundan's relations in `U_Q(g)` without the mixed relations

J. Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1, §§2, 5.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k] {S : CLScalars C k} (hr : ∀ c, S.r c = 1)

include hr

/-- **Outer mixed Reidemeister 3 move** (Brundan (2.4), `lurking`, the case without correction
term): the downward strand passes `k` and `i`, then `ψ_{ik}`, equals `ψ_{ik}`, then the
downward strand passes `i` and `k`; the rotation of the braid relation on `E_j E_i E_k`, unless
`j = k ≠ i`. -/
theorem dgN_r3outL (i k' j : I) (h : ¬ (j = k' ∧ j ≠ i)) (μ : X) :
    dgC (presNM RD k S) μ [up i, up k', dn j] [dn j, up k', up i]
      ((crosslL k' j).map (whL [up i] []) ++ (crosslL i j).map (whL [] [up k']) ++
        [([dn j], .cross true i k', [])]) =
    dgC (presNM RD k S) μ [up i, up k', dn j] [dn j, up k', up i]
      ([([], .cross true i k', [dn j])] ++ (crosslL i j).map (whL [up k'] []) ++
        (crosslL k' j).map (whL [] [up i])) := by
  dnorm
  dswapC 2; dswapC 3; dswapC 1; dswapC 2; dswapC 0; dswapC 1; dswapC 4; dswapC 3
  datC 2 [dn j, up i] [up k', dn j] (dgC_zigR' _ (presNM_zigzags RD k S) _ (dn j))
  dswapC 3
  datC 1 [dn j] [dn j] (dgC_braid (presNM_klr hr) _ j i k' h)
  symm
  dswapC 3; dswapC 4; dswapC 2; dswapC 3; dswapC 1; dswapC 2; dswapC 0; dswapC 5; dswapC 4
  datC 3 [dn j, up k'] [up i, dn j] (dgC_zigR' _ (presNM_zigzags RD k S) _ (dn j))

/-- **Outer mixed Reidemeister 3 move with correction term** (Brundan (2.4), `lurking`, the case
`i = k ≠ j`; here the left upward strand is `a`, the middle upward strand and the downward strand
are `b`): the difference of the two sides is the rotation of the correction term `Q̄_{ba}` of the
deformed braid relation on `E_b E_a E_b`. -/
theorem dgN_lurk (a b : I) (hab : a ≠ b) (μ : X) :
    dgC (presNM RD k S) μ [up a, up b, dn b] [dn b, up b, up a]
      ((crosslL b b).map (whL [up a] []) ++ (crosslL a b).map (whL [] [up b]) ++
        [([dn b], .cross true a b, [])]) =
    dgC (presNM RD k S) μ [up a, up b, dn b] [dn b, up b, up a]
      ([([], .cross true a b, [dn b])] ++ (crosslL a b).map (whL [up b] []) ++
        (crosslL b b).map (whL [] [up a])) +
    ctxLC (presNM RD k S) μ [up a, up b, dn b] [dn b, up b, up a]
      [([], .cup (dn b), [up a, up b, dn b])] [dn b] [dn b]
      [([dn b, up b, up a], .cap (dn b), [])] [up b, up a, up b] [up b, up a, up b]
      (KLR.ncEval (A := End ((presNM RD k S).obj (ob RD (wt RD μ [dn b]) [up b, up a, up b])))
        ![dgC (presNM RD k S) (wt RD μ [dn b]) [up b, up a, up b] [up b, up a, up b]
            [([], .dot (up b), [up a, up b])],
          dgC (presNM RD k S) (wt RD μ [dn b]) [up b, up a, up b] [up b, up a, up b]
            [([up b], .dot (up a), [up b])],
          dgC (presNM RD k S) (wt RD μ [dn b]) [up b, up a, up b] [up b, up a, up b]
            [([up b, up a], .dot (up b), [])]]
        (KLR.qbar (qCL S b a))) := by
  dnorm
  dswapC 2; dswapC 3; dswapC 1; dswapC 2; dswapC 0; dswapC 1; dswapC 4; dswapC 3
  datC 2 [dn b, up a] [up b, dn b] (dgC_zigR' _ (presNM_zigzags RD k S) _ (dn b))
  dswapC 3
  rw [dgC_stepL_at _ 1 [dn b] [dn b]
    (sub_eq_iff_eq_add.mp (dgC_braidQ (presNM_klr hr) _ b a hab.symm)) (by dnorm; schain)
    (by dnorm; schain) (by dnorm), map_add, add_comm]
  congr 1
  dnorm
  rw [ctxLC_dg _ _ (by schain) (by schain)]
  dnorm
  symm
  dswapC 3; dswapC 4; dswapC 2; dswapC 3; dswapC 1; dswapC 2; dswapC 0; dswapC 5; dswapC 4
  datC 3 [dn b, up b] [up a, dn b] (dgC_zigR' _ (presNM_zigzags RD k S) _ (dn b))

omit hr in
/-- A subdiagram whose class is zero kills the whole diagram. -/
theorem dgC_eq_zero_at {P : Presentation.{w, max u v} (psig RD) k} {μ : X}
    {s₀ t₀ : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (u v : List (Letter I)) {s t : List (Letter I)} {A : List (LayerData I)}
    (E : dgC P (wt RD μ v) s t A = 0)
    (hpre : SChain s₀ (L.take n) (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) (L.drop (n + A.length)) t₀)
    (hL : (L.drop n).take A.length = A.map (whL u v)) :
    dgC P μ s₀ t₀ L = 0 := by
  rw [dgC_stepL_at L n u v E hpre hpost hL, map_zero]

omit hr in
theorem plcLC_id (P : Presentation.{w, max u v} (psig RD) k) (μ : X) (u v s : List (Letter I)) :
    plcLC P μ u v s s (𝟙 _) = 𝟙 _ := by
  rw [← dgC_nil, plcLC_dg, List.map_nil, dgC_nil]

omit hr in
/-- The degree-zero fake counterclockwise bubble (label `-1` in a region with `⟨i, ν⟩ = 0`) is
`1`. -/
theorem ccwN_neg_one (ν : X) (i : I) (h : ip RD i ν = 0) : ccwN (RD := RD) S ν i (-1) = 𝟙 _ := by
  rw [ccwN, ccwL, ite_eq_right (by omega), ite_eq_left (by omega)]
  rw [show (-1 + 1 + ip RD i ν).toNat = 0 by omega, grassInv_zero]
  exact (presNM RD k S).lin_id _

omit hr in
/-- The degree-zero fake clockwise bubble (label `-1` in a region with `⟨i, ν⟩ = 0`) is `1`. -/
theorem cwN_neg_one (ν : X) (i : I) (h : ip RD i ν = 0) : cwN (RD := RD) S ν i (-1) = 𝟙 _ := by
  rw [cwN, cwL, ite_eq_right (by omega), ite_eq_left (by omega)]
  rw [show (-1 + 1 - ip RD i ν).toNat = 0 by omega, grassInv_zero]
  exact (presNM RD k S).lin_id _

/-- The layers of the curl `E_i F_i ⟶ 1`: the sideways crossing `crossl i i`, then the cap
`F_i E_i ⟶ 1` (Brundan's `ε' ∘ σ`). -/
def curlALs (i : I) : List (LayerData I) := crosslL i i ++ [([], .cap (up i), [])]

/-- The curl `ε' ∘ σ` vanishes in a region with `⟨i, μ⟩ < 0` (Brundan (3.7), `startd`). -/
theorem dgN_curlA_neg (i : I) (μ : X) (h : ip RD i μ < 0) :
    dgC (presNM RD k S) μ [up i, dn i] [] (curlALs i) = 0 := by
  unfold curlALs; dnorm
  dswapC 2
  have hw : ip RD i (wt RD (wt RD μ [dn i]) [up i]) = ip RD i μ := by simp [wt]
  have E := dgN_curlL (RD := RD) (S := S) hr i (wt RD μ [dn i])
  rw [hw, show (ip RD i μ + 1).toNat = 0 by omega, Finset.sum_range_zero] at E
  exact dgC_eq_zero_at _ 0 [] [dn i] E (by dnorm; schain) (by dnorm; schain) (by dnorm)

/-- The curl `ε' ∘ σ` in a region with `⟨i, μ⟩ = 0` is the cap `E_i F_i ⟶ 1` (Brundan
(3.21), `everything`, degree `0`). -/
theorem dgN_curlA_zero (i : I) (μ : X) (h : ip RD i μ = 0) :
    dgC (presNM RD k S) μ [up i, dn i] [] (curlALs i) =
      dgC (presNM RD k S) μ [up i, dn i] [] [([], .cap (dn i), [])] := by
  unfold curlALs; dnorm
  dswapC 2
  have hw : ip RD i (wt RD (wt RD μ [dn i]) [up i]) = ip RD i μ := by simp [wt]
  have E := dgN_curlL (RD := RD) (S := S) hr i (wt RD μ [dn i])
  rw [hw, show (ip RD i μ + 1).toNat = 1 by omega, Finset.sum_range_one, h,
    show (-0 - 1 + ((0 : ℕ) : ℤ) : ℤ) = -1 by norm_num,
    ccwN_neg_one (S := S) _ i (by rw [hw, h])] at E
  simp only [bubLC, plcLC_id, dotsN, Nat.cast_zero, sub_zero, Int.toNat_zero, List.replicate_zero,
    dgC_nil, Category.comp_id] at E
  rw [← dgC_nil] at E
  rw [dgC_step_at _ 0 [] [dn i] E (by dnorm; schain) (by dnorm; schain) (by dnorm)]
  dnorm

omit hr in
/-- **Pitchfork** (Brundan (2.3), `rightpitchfork`, cap form): an upward strand `j` crossing the
left leg of a cap `E_i F_i ⟶ 1` by the sideways crossing equals it crossing the right leg by the
upward crossing. -/
theorem dgN_pitchCap (i j : I) (μ : X) :
    dgC (presNM RD k S) μ [up i, up j, dn i] [up j]
      ((crosslL j i).map (whL [up i] []) ++ [([], .cap (dn i), [up j])]) =
    dgC (presNM RD k S) μ [up i, up j, dn i] [up j]
      [([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])] := by
  dnorm
  dswapC 2; dswapC 1
  datC 0 [] [up j, dn i] (dgC_zigR' _ (presNM_zigzags RD k S) _ (dn i))

omit hr in
/-- **Pitchfork** (Brundan (2.3), `rightpitchfork`, cup form): an upward strand `j` crossing the
left leg of a cup `1 ⟶ F_i E_i` by the sideways crossing equals it crossing the right leg by the
upward crossing. -/
theorem dgN_pitchCup (i j : I) (μ : X) :
    dgC (presNM RD k S) μ [up j] [dn i, up j, up i]
      ([([up j], .cup (dn i), [])] ++ (crosslL j i).map (whL [] [up i])) =
    dgC (presNM RD k S) μ [up j] [dn i, up j, up i]
      [([], .cup (dn i), [up j]), ([dn i], .cross true i j, [])] := by
  dnorm
  dswapC 0; dswapC 1
  datC 2 [dn i, up j] [] (dgC_zigR' _ (presNM_zigzags RD k S) _ (dn i))

omit hr in
theorem ncEvalB_add {A : Type*} [Ring A] [Algebra k A] {n : ℕ} (y : Fin n → A)
    (p q : MvPolynomial (Fin n) k) : KLR.ncEval y (p + q) = KLR.ncEval y p + KLR.ncEval y q :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_mul])

omit hr in
theorem ncEvalB_monomial {A : Type*} [Ring A] [Algebra k A] {n : ℕ} (y : Fin n → A)
    (s : Fin n →₀ ℕ) (c : k) :
    KLR.ncEval y (MvPolynomial.monomial s c) = algebraMap k A c * (List.ofFn fun a => y a ^ s a).prod :=
  Finsupp.sum_single_index (by simp)

omit hr in
/-- `ncEval` of a monomial in three variables, ordered `x₀^a x₁^b x₂^c`. -/
theorem ncEval_X3 {A : Type*} [Ring A] [Algebra k A] (y : Fin 3 → A) (a b c : ℕ) :
    KLR.ncEval y (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b * MvPolynomial.X 2 ^ c :
      MvPolynomial (Fin 3) k) = y 0 ^ a * y 1 ^ b * y 2 ^ c := by
  have e : (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b * MvPolynomial.X 2 ^ c :
      MvPolynomial (Fin 3) k) =
      MvPolynomial.monomial (Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c) 1 := by
    simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, mul_one]
  rw [e, ncEvalB_monomial, map_one, one_mul, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ,
    List.ofFn_zero]
  simp [Finsupp.single_apply, mul_assoc]

omit hr in
theorem ncEval_C_mul' {A : Type*} [Ring A] [Algebra k A] {n : ℕ} (y : Fin n → A) (c : k)
    (p : MvPolynomial (Fin n) k) :
    KLR.ncEval y (MvPolynomial.C c * p) = algebraMap k A c * KLR.ncEval y p := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [MvPolynomial.C_mul_monomial, ncEvalB_monomial, ncEvalB_monomial, map_mul, mul_assoc]
  | add p q hp hq => rw [mul_add, ncEvalB_add, ncEvalB_add, hp, hq, mul_add]

omit hr in
theorem ncEval_sum' {A : Type*} [Ring A] [Algebra k A] {n : ℕ} (y : Fin n → A) {ι : Type*}
    (s : Finset ι) (p : ι → MvPolynomial (Fin n) k) :
    KLR.ncEval y (∑ x ∈ s, p x) = ∑ x ∈ s, KLR.ncEval y (p x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [KLR.ncEval]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ncEvalB_add, ih]

omit hr in
theorem ctxLC_comp_dgC {P : Presentation.{w, max u v} (psig RD) k} {μ : X}
    {s₀ t₀ t₁ : List (Letter I)} {pre post L : List (LayerData I)} {u v s t : List (Letter I)}
    (hpost : SChain (u ++ t ++ v) post t₀) (hL : SChain t₀ L t₁)
    (f : P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)) :
    ctxLC P μ s₀ t₀ pre u v post s t f ≫ dgC P μ t₀ t₁ L =
      ctxLC P μ s₀ t₁ pre u v (post ++ L) s t f := by
  simp only [ctxLC, LinearMap.coe_mk, AddHom.coe_mk, Category.assoc, dgC_comp hpost hL]

omit hr in
/-- The power of a single-layer endomorphism. -/
theorem dgC_pow {P : Presentation.{w, max u v} (psig RD) k} (μ : X) (w' : List (Letter I))
    (x : LayerData I) (hx : SChain w' [x] w') (n : ℕ) :
    dgEC P μ w' [x] ^ n = dgEC P μ w' (List.replicate n x) :=
  dgEC_pow_single P μ w' x hx n

omit hr in
/-- A product of three endomorphisms given by lists of layers. -/
theorem dgC_mul3 {P : Presentation.{w, max u v} (psig RD) k} (μ : X) (w' : List (Letter I))
    (A B D : List (LayerData I)) (hA : SChain w' A w') (hB : SChain w' B w') (hD : SChain w' D w') :
    dgEC P μ w' A * dgEC P μ w' B * dgEC P μ w' D = dgEC P μ w' (D ++ B ++ A) := by
  rw [End.mul_def, End.mul_def, dgEC, dgEC, dgEC, dgEC, ← Category.assoc, dgC_comp hD hB,
    dgC_comp (hD.append hB) hA]

omit hr in
/-- A monomial of the correction term of `dgN_lurk` (labels `a = j`, `b = i`), capped on the top
left by `F_i E_i ⟶ 1`: the counterclockwise bubble with the dots of the new strand, to the left. -/
theorem dgN_lurkCap_mono (i j : I) (lam : X) (a b c : ℕ) :
    ctxLC (presNM RD k S) lam [up j, up i, dn i] [dn i, up i, up j]
        [([], .cup (dn i), [up j, up i, dn i])] [dn i] [dn i]
        [([dn i, up i, up j], .cap (dn i), [])] [up i, up j, up i] [up i, up j, up i]
        (dgEC (presNM RD k S) (wt RD lam [dn i]) [up i, up j, up i] [([], .dot (up i), [up j, up i])] ^ a *
          dgEC (presNM RD k S) (wt RD lam [dn i]) [up i, up j, up i] [([up i], .dot (up j), [up i])] ^ b *
          dgEC (presNM RD k S) (wt RD lam [dn i]) [up i, up j, up i] [([up i, up j], .dot (up i), [])] ^ c) ≫
      dgC (presNM RD k S) lam [dn i, up i, up j] [up j] [([], .cap (up i), [up j])] =
    dgC (presNM RD k S) lam [up j, up i, dn i] [up j]
      ((ccwLs i a).map (whL [] [up j, up i, dn i]) ++ List.replicate c ([up j], .dot (up i), [dn i]) ++
        List.replicate b ([], .dot (up j), [up i, dn i]) ++ [([up j], .cap (dn i), [])]) := by
  rw [dgC_pow _ _ _ (by schain), dgC_pow _ _ _ (by schain), dgC_pow _ _ _ (by schain),
    dgC_mul3 _ _ _ _ _ (by schain) (by schain) (by schain), ctxLC_comp_dgC (by schain) (by schain),
    ctxLC_dg _ _ (by schain) (by schain)]
  have h1 := dgC_interchange (P := presNM RD k S) (μ := lam) (S := [up j, up i, dn i]) (T := [up j])
    [([], .cup (dn i), [up j, up i, dn i])]
    ([([dn i, up i, up j], .cap (dn i), [])] ++ [([], .cap (up i), [up j])])
    (s := [dn i, up i]) (s' := [dn i, up i]) (t := [up j, up i, dn i]) (t' := [up j, up i, dn i])
    (A := List.replicate a ([dn i], .dot (up i), []))
    (B := List.replicate c ([up j], .dot (up i), [dn i]) ++ List.replicate b ([], .dot (up j), [up i, dn i]))
    (by schain) (by schain)
  have h2 := dgC_interchange (P := presNM RD k S) (μ := lam) (S := [up j, up i, dn i]) (T := [up j])
    ([([], .cup (dn i), [up j, up i, dn i])] ++
      (List.replicate a ([dn i], .dot (up i), [])).map (whL [] [up j, up i, dn i])) []
    (s := [dn i, up i]) (s' := []) (t := [up j, up i, dn i]) (t' := [up j])
    (A := [([], .cap (up i), [])])
    (B := List.replicate c ([up j], .dot (up i), [dn i]) ++ List.replicate b ([], .dot (up j), [up i, dn i]) ++
      [([up j], .cap (dn i), [])])
    (by schain) (by schain)
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil, whL,
    List.append_assoc, List.nil_append, List.cons_append, List.append_nil,
    List.singleton_append] at h1 h2 ⊢
  rw [← h1]
  simp only [ccwLs, List.map_append, List.map_replicate, List.map_cons, List.map_nil, whL,
    List.append_assoc, List.nil_append, List.cons_append, List.append_nil, List.singleton_append]
  rw [← h2]

omit hr in
theorem ip_up (i j : I) (lam : X) : ip RD i (sh RD (up j) + lam) = ip RD i lam + ip RD i (RD.iX j) := by
  simp [ip, sh, up, add_comm]

omit hr in
theorem ip_dn (i j : I) (lam : X) : ip RD i (sh RD (dn j) + lam) = ip RD i lam - ip RD i (RD.iX j) := by
  simp [ip, sh, dn, sub_eq_add_neg, add_comm]

omit hr in
theorem ip_iX_self (i : I) : ip RD i (RD.iX i) = 2 := RD.pair_iY_iX_self i

omit hr in
theorem ip_iX_ne {i j : I} (h : i ≠ j) : ip RD i (RD.iX j) = -(C.dij i j : ℤ) := by
  have hm := C.dij_mul h
  have hpos := C.dot_self_pos i
  rw [ip, RD.pair_iY_iX, show 2 * C.dot i j = -(C.dij i j : ℤ) * C.dot i i by linarith [hm]]
  exact Int.mul_ediv_cancel _ hpos.ne'

omit hr in
/-- A counterclockwise bubble of negative degree at the far left kills a diagram. -/
theorem dgN_ccwLeft_zero {lam : X} {t : List (Letter I)} (w : List (Letter I)) (i : I) (a : ℕ)
    (rest : List (LayerData I)) (h : (a : ℤ) < -ip RD i (wt RD lam w) - 1) (hrest : SChain w rest t) :
    dgC (presNM RD k S) lam w t ((ccwLs i a).map (whL [] w) ++ rest) = 0 := by
  refine dgC_eq_zero_at _ 0 [] w (dgN_ccwNeg S _ i a h) (by simp) ?_ ?_
  · simpa [List.drop_left'] using hrest
  · simp [List.take_left']

omit hr in
/-- The degree-zero counterclockwise bubble at the far left is `1`. -/
theorem dgN_ccwLeft_one {lam : X} {t : List (Letter I)} (w : List (Letter I)) (i : I)
    (rest : List (LayerData I)) (h : ip RD i (wt RD lam w) ≤ -1) (hrest : SChain w rest t) :
    dgC (presNM RD k S) lam w t
        ((ccwLs i (-ip RD i (wt RD lam w) - 1).toNat).map (whL [] w) ++ rest) =
      dgC (presNM RD k S) lam w t rest := by
  rw [dgC_step_at _ 0 [] w (dgN_ccwOne S _ i h) (by simp) (by simpa [List.drop_left'] using hrest)
    (by simp [List.take_left'])]
  simp [List.drop_left']

omit hr in
theorem qbar_C (c : k) : KLR.qbar (MvPolynomial.C c : MvPolynomial (Fin 2) k) = 0 := by
  have := qbar_C_mul_X_pow_mul_X_pow c 0 0
  simpa using this

omit hr in
theorem ip_wt_jii {i j : I} (hij : i ≠ j) (lam : X) :
    ip RD i (wt RD lam [up j, up i, dn i]) = ip RD i lam - C.dij i j := by
  simp only [wt_cons, wt_nil, ip_up, ip_dn, ip_iX_ne hij]; ring

/-- The dots of the correction term of `dgN_lurk` for the labels `a = j`, `b = i` (on
`E_i E_j E_i`, rightmost region `λ - α_i`). -/
abbrev lurkY (i j : I) (lam : X) : Fin 3 → End ((presNM RD k S).obj (ob RD (wt RD lam [dn i]) [up i, up j, up i])) :=
  ![dgEC (presNM RD k S) (wt RD lam [dn i]) [up i, up j, up i] [([], .dot (up i), [up j, up i])],
    dgEC (presNM RD k S) (wt RD lam [dn i]) [up i, up j, up i] [([up i], .dot (up j), [up i])],
    dgEC (presNM RD k S) (wt RD lam [dn i]) [up i, up j, up i] [([up i, up j], .dot (up i), [])]]

omit hr in
/-- The value of a monomial of the capped correction term of `dgN_lurk` in a region with
`⟨i, λ⟩ ≤ 0`: zero unless the new strand carries `d_{ij} - ⟨i, λ⟩ - 1` dots. -/
theorem dgN_lurkCap_val {i j : I} (hij : i ≠ j) (lam : X) (a b c : ℕ)
    (ha : (a : ℤ) ≤ C.dij i j - ip RD i lam - 1) :
    ctxLC (presNM RD k S) lam [up j, up i, dn i] [dn i, up i, up j]
        [([], .cup (dn i), [up j, up i, dn i])] [dn i] [dn i]
        [([dn i, up i, up j], .cap (dn i), [])] [up i, up j, up i] [up i, up j, up i]
        (lurkY i j lam 0 ^ a * lurkY i j lam 1 ^ b * lurkY i j lam 2 ^ c) ≫
      dgC (presNM RD k S) lam [dn i, up i, up j] [up j] [([], .cap (up i), [up j])] =
    if (a : ℤ) = C.dij i j - ip RD i lam - 1 then
      dgC (presNM RD k S) lam [up j, up i, dn i] [up j]
        (List.replicate c ([up j], .dot (up i), [dn i]) ++
          List.replicate b ([], .dot (up j), [up i, dn i]) ++ [([up j], .cap (dn i), [])])
    else 0 := by
  have e := dgN_lurkCap_mono (RD := RD) (S := S) i j lam a b c
  simp only [lurkY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at e ⊢
  rw [e]
  have hw := ip_wt_jii (RD := RD) hij lam
  split_ifs with h
  · have ha' : a = (-ip RD i (wt RD lam [up j, up i, dn i]) - 1).toNat := by omega
    subst ha'
    rw [List.append_assoc, List.append_assoc, dgN_ccwLeft_one _ i _ (by omega) (by schain),
      List.append_assoc]
  · rw [List.append_assoc, List.append_assoc]
    exact dgN_ccwLeft_zero _ i a _ (by omega) (by schain)

/-- The capped correction term of `dgN_lurk` (labels `a = j`, `b = i`), as a `k`-linear function
of the polynomial evaluated on the dots. -/
def lurkCapF (i j : I) (lam : X) :
    MvPolynomial (Fin 3) k →ₗ[k] ((presNM RD k S).obj (ob RD lam [up j, up i, dn i]) ⟶
      (presNM RD k S).obj (ob RD lam [up j])) where
  toFun p := ctxLC (presNM RD k S) lam [up j, up i, dn i] [dn i, up i, up j]
        [([], .cup (dn i), [up j, up i, dn i])] [dn i] [dn i]
        [([dn i, up i, up j], .cap (dn i), [])] [up i, up j, up i] [up i, up j, up i]
        (KLR.ncEval (A := End ((presNM RD k S).obj (ob RD (wt RD lam [dn i]) [up i, up j, up i])))
          (lurkY i j lam) p) ≫
      dgC (presNM RD k S) lam [dn i, up i, up j] [up j] [([], .cap (up i), [up j])]
  map_add' p q := by rw [ncEvalB_add, map_add, Preadditive.add_comp]
  map_smul' c p := by
    rw [MvPolynomial.smul_eq_C_mul, ncEval_C_mul', ← Algebra.smul_def, map_smul, Linear.smul_comp]
    rfl

omit hr in
theorem lurkCapF_X3 {i j : I} (hij : i ≠ j) (lam : X) (a b c : ℕ)
    (ha : (a : ℤ) ≤ C.dij i j - ip RD i lam - 1) :
    lurkCapF (RD := RD) (S := S) i j lam (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b * MvPolynomial.X 2 ^ c) =
    if (a : ℤ) = C.dij i j - ip RD i lam - 1 then
      dgC (presNM RD k S) lam [up j, up i, dn i] [up j]
        (List.replicate c ([up j], .dot (up i), [dn i]) ++
          List.replicate b ([], .dot (up j), [up i, dn i]) ++ [([up j], .cap (dn i), [])])
    else 0 := by
  rw [← dgN_lurkCap_val hij lam a b c ha]
  show ctxLC _ _ _ _ _ _ _ _ _ _ (KLR.ncEval (A := End ((presNM RD k S).obj (ob RD (wt RD lam [dn i])
    [up i, up j, up i]))) (lurkY i j lam) _) ≫ _ = _
  rw [ncEval_X3]

omit hr in
/-- **The capped correction term of `dgN_lurk`** in a region with `⟨i, λ⟩ ≤ 0` (Brundan §5,
proof of (5.2), the terms of (2.4) after capping): `t_{ij}` times the cap `E_i F_i ⟶ 1` if
`⟨i, λ⟩ = 0` and `i · j ≠ 0`, and `0` otherwise. -/
theorem dgN_lurkCap {i j : I} (hij : i ≠ j) (lam : X) (h : ip RD i lam ≤ 0) :
    lurkCapF (RD := RD) (S := S) i j lam (KLR.qbar (qCL S i j)) =
      if ip RD i lam = 0 ∧ C.dot i j ≠ 0 then
        (S.t i j : k) • dgC (presNM RD k S) lam [up j, up i, dn i] [up j] [([up j], .cap (dn i), [])]
      else 0 := by
  by_cases hd : C.dot i j = 0
  · rw [qCL_of_dot_eq_zero S hd, qbar_C, map_zero, ite_eq_right_iff.2 (fun h' => (h'.2 hd).elim)]
  have hdpos := C.dij_pos hij hd
  rw [qbar_qCL S hij hd, map_add, MvPolynomial.C_mul', map_smul]
  simp only [map_sum]
  have hX : ∀ l : ℕ × ℕ, (MvPolynomial.X 0 ^ l.1 * MvPolynomial.X 2 ^ l.2 : MvPolynomial (Fin 3) k) =
      MvPolynomial.X 0 ^ l.1 * MvPolynomial.X 1 ^ 0 * MvPolynomial.X 2 ^ l.2 := fun l => by ring
  have hmem : ∀ {n : ℕ} {l : ℕ × ℕ}, l ∈ Finset.HasAntidiagonal.antidiagonal n → l.1 + l.2 = n :=
    fun hl => Finset.HasAntidiagonal.mem_antidiagonal.1 hl
  -- the `s`-terms vanish
  have hs : (∑ p ∈ Finset.range (C.dij i j), ∑ q ∈ Finset.range (C.dij j i),
      lurkCapF (RD := RD) (S := S) i j lam
        (if C.dot i i * p + C.dot j j * q = -2 * C.dot i j then
          MvPolynomial.C (S.s i j p q) * MvPolynomial.X 1 ^ q *
            ∑ l ∈ Finset.HasAntidiagonal.antidiagonal (p - 1),
              MvPolynomial.X 0 ^ l.1 * MvPolynomial.X 2 ^ l.2
        else 0)) = 0 := by
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
    have hp' := Finset.mem_range.1 hp
    have hq' := Finset.mem_range.1 hq
    split_ifs with hcond
    · have hp0 : p ≠ 0 := by
        rintro rfl
        have hm := C.dij_mul hij.symm
        rw [C.symm j i] at hm
        have hpos := C.dot_self_pos j
        have : C.dot j j * ((q : ℤ) - C.dij j i) = 0 := by push_cast at hcond; linarith
        rcases mul_eq_zero.1 this with h0 | h0
        · omega
        · omega
      rw [mul_assoc, MvPolynomial.C_mul', Finset.mul_sum, map_smul, map_sum]
      refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun l hl => ?_)
      have hl' := hmem hl
      rw [show (MvPolynomial.X 1 ^ q * (MvPolynomial.X 0 ^ l.1 * MvPolynomial.X 2 ^ l.2) :
          MvPolynomial (Fin 3) k) = MvPolynomial.X 0 ^ l.1 * MvPolynomial.X 1 ^ q *
            MvPolynomial.X 2 ^ l.2 by ring, lurkCapF_X3 hij lam _ _ _ (by omega), ite_eq_right (by omega)]
    · exact map_zero _
  rw [hs, add_zero]
  simp_rw [hX]
  rcases lt_or_eq_of_le h with hlt | heq
  · rw [Finset.sum_eq_zero fun l hl => by
      rw [lurkCapF_X3 hij lam _ _ _ (by have := hmem hl; omega), ite_eq_right (by have := hmem hl; omega)],
      smul_zero, ite_eq_right (by omega)]
  · rw [ite_eq_left ⟨heq, hd⟩, Finset.sum_eq_single (C.dij i j - 1, 0)]
    · rw [lurkCapF_X3 hij lam _ _ _ (by omega), ite_eq_left (by simp only; omega)]
      simp
    · intro l hl hne
      have hl' := hmem hl
      rw [lurkCapF_X3 hij lam _ _ _ (by omega), ite_eq_right]
      intro h'
      exact hne (Prod.ext (by simp only at h' ⊢; omega) (by simp only at h' ⊢; omega))
    · intro h'
      exact (h' (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp))).elim

omit hr in
/-- `ncEval` of a constant. -/
theorem ncEval_C' {A : Type*} [Ring A] [Algebra k A] {n : ℕ} (y : Fin n → A) (c : k) :
    KLR.ncEval y (MvPolynomial.C c : MvPolynomial (Fin n) k) = algebraMap k A c := by
  rw [MvPolynomial.C_apply, ncEvalB_monomial]
  simp

/-- The double crossing `E_c E_d ⟶ E_d E_c ⟶ E_c E_d` for `c · d = 0` is `t_{cd}`. -/
theorem dgN_sqNe_zero (μ : X) {c d : I} (h : c ≠ d) (hd : C.dot c d = 0) :
    dgC (presNM RD k S) μ [up c, up d] [up c, up d]
        [([], .cross true c d, []), ([], .cross true d c, [])] =
      (S.t c d : k) • dgC (presNM RD k S) μ [up c, up d] [up c, up d] [] := by
  rw [dgC_sqNe (presNM_klr hr) μ c d h, qCL_of_dot_eq_zero S hd, ncEval_C', Algebra.algebraMap_eq_smul_one,
    dgC_nil]
  rfl

/-- **Brundan (5.4), first relation** (`turn`, `⟨i, λ⟩ ≤ 0`): an upward strand `j` passing
through the curl `ε' ∘ σ` on `E_i F_i` (the strand crosses both legs) equals `t_{ij}` times the
strand to the left of the curl. -/
theorem dgN_turn1 {i j : I} (hij : i ≠ j) (lam : X) (h : ip RD i lam ≤ 0) :
    dgC (presNM RD k S) lam [up j, up i, dn i] [up j]
      ((crosslL i i).map (whL [up j] []) ++ (crosslL j i).map (whL [] [up i]) ++
        [([dn i], .cross true j i, []), ([], .cap (up i), [up j])]) =
    (S.t i j : k) • dgC (presNM RD k S) lam [up j, up i, dn i] [up j]
      ((curlALs i).map (whL [up j] [])) := by
  have hsplit : (crosslL i i).map (whL [up j] []) ++ (crosslL j i).map (whL [] [up i]) ++
      [([dn i], .cross true j i, []), ([], .cap (up i), [up j])] =
      ((crosslL i i).map (whL [up j] []) ++ (crosslL j i).map (whL [] [up i]) ++
        [([dn i], .cross true j i, [])]) ++ [([], .cap (up i), [up j])] := by simp
  rw [hsplit, ← dgC_comp (t := [dn i, up i, up j]) (by dnorm; schain) (by schain),
    dgN_lurk hr j i hij.symm lam, Preadditive.add_comp, dgC_comp (by dnorm; schain) (by schain)]
  have hcorr : ctxLC (presNM RD k S) lam [up j, up i, dn i] [dn i, up i, up j]
      [([], .cup (dn i), [up j, up i, dn i])] [dn i] [dn i]
      [([dn i, up i, up j], .cap (dn i), [])] [up i, up j, up i] [up i, up j, up i]
      (KLR.ncEval (A := End ((presNM RD k S).obj (ob RD (wt RD lam [dn i]) [up i, up j, up i])))
        ![dgC (presNM RD k S) (wt RD lam [dn i]) [up i, up j, up i] [up i, up j, up i]
            [([], .dot (up i), [up j, up i])],
          dgC (presNM RD k S) (wt RD lam [dn i]) [up i, up j, up i] [up i, up j, up i]
            [([up i], .dot (up j), [up i])],
          dgC (presNM RD k S) (wt RD lam [dn i]) [up i, up j, up i] [up i, up j, up i]
            [([up i, up j], .dot (up i), [])]]
        (KLR.qbar (qCL S i j))) ≫
      dgC (presNM RD k S) lam [dn i, up i, up j] [up j] [([], .cap (up i), [up j])] =
      lurkCapF (RD := RD) (S := S) i j lam (KLR.qbar (qCL S i j)) := rfl
  rw [hcorr, dgN_lurkCap hij lam h]
  have hw : ip RD i (wt RD lam [up j]) = ip RD i lam - C.dij i j := by
    simp only [wt_cons, wt_nil, ip_up, ip_iX_ne hij]; ring
  -- the right-hand side
  have hR : dgC (presNM RD k S) lam [up j, up i, dn i] [up j] ((curlALs i).map (whL [up j] [])) =
      if ip RD i lam = 0 then
        dgC (presNM RD k S) lam [up j, up i, dn i] [up j] [([up j], .cap (dn i), [])] else 0 := by
    split_ifs with h0
    · have E : dgC (presNM RD k S) (wt RD lam []) [up i, dn i] [] (curlALs i) =
          dgC (presNM RD k S) (wt RD lam []) [up i, dn i] [] [([], .cap (dn i), [])] :=
        dgN_curlA_zero (RD := RD) hr i lam h0
      rw [show (curlALs i).map (whL [up j] []) = [] ++ (curlALs i).map (whL [up j] []) ++ [] by simp,
        dgC_step_at _ 0 [up j] [] E (by simp) (by (try simp only [curlALs]); dnorm; schain)
          (by (try simp only [curlALs]); dnorm)]
      simp [curlALs, crosslL, whL]
    · have E : dgC (presNM RD k S) (wt RD lam []) [up i, dn i] [] (curlALs i) = 0 :=
        dgN_curlA_neg (RD := RD) hr i lam (by omega)
      exact dgC_eq_zero_at _ 0 [up j] [] E (by simp) (by (try simp only [curlALs]); dnorm; schain)
        (by (try simp only [curlALs]); dnorm)
  rw [hR]
  have hP2 : dgC (presNM RD k S) lam [up j, up i, dn i] [up j]
      (([([], .cross true j i, [dn i])] ++ (crosslL j i).map (whL [up i] []) ++
        (crosslL i i).map (whL [] [up j])) ++ [([], .cap (up i), [up j])]) =
      if ip RD i lam = 0 ∧ C.dot i j = 0 then
        (S.t j i : k) • dgC (presNM RD k S) lam [up j, up i, dn i] [up j] [([up j], .cap (dn i), [])]
      else 0 := by
    split_ifs with hc
    · have hd0 : C.dij i j = 0 := (C.dij_eq_zero_iff hij).2 hc.2
      have E : dgC (presNM RD k S) (wt RD lam [up j]) [up i, dn i] [] (curlALs i) =
          dgC (presNM RD k S) (wt RD lam [up j]) [up i, dn i] [] [([], .cap (dn i), [])] :=
        dgN_curlA_zero (RD := RD) hr i _ (by rw [hw, hc.1, hd0]; rfl)
      rw [dgC_step_at _ 4 [] [up j] E (by (try simp only [curlALs, crosslL]); dnorm; schain)
        (by (try simp only [curlALs, crosslL]); dnorm; schain) (by (try simp only [curlALs]); dnorm)]
      dnorm
      have E2 := dgN_pitchCap (RD := RD) (S := S) i j lam
      rw [dgC_step_at _ 1 [] [] E2 (by (try simp only [crosslL]); dnorm; schain)
        (by (try simp only [crosslL]); dnorm; schain) (by (try simp only [crosslL]); dnorm)]
      dnorm
      have E3 := dgN_sqNe_zero (RD := RD) hr (wt RD lam [dn i]) hij.symm (by rw [C.symm]; exact hc.2)
      rw [dgC_stepL_at _ 0 [] [dn i] E3 (by dnorm; schain) (by dnorm; schain) (by dnorm), map_smul,
        ctxLC_dg _ _ (by dnorm; schain) (by dnorm; schain)]
      simp [curlALs, crosslL, whL]
    · have E : dgC (presNM RD k S) (wt RD lam [up j]) [up i, dn i] [] (curlALs i) = 0 :=
        dgN_curlA_neg (RD := RD) hr i _ (by
          rw [hw]
          by_cases h0 : ip RD i lam = 0
          · have : C.dot i j ≠ 0 := fun h' => hc ⟨h0, h'⟩
            have := C.dij_pos hij this; omega
          · omega)
      exact dgC_eq_zero_at _ 4 [] [up j] E (by (try simp only [curlALs, crosslL]); dnorm; schain)
        (by (try simp only [curlALs, crosslL]); dnorm; schain) (by (try simp only [curlALs]); dnorm)
  rw [hP2]
  by_cases h0 : ip RD i lam = 0
  · by_cases hd : C.dot i j = 0
    · rw [ite_eq_left ⟨h0, hd⟩, ite_eq_right (fun h' => h'.2 hd), add_zero, ite_eq_left h0, S.t_symm i j hd]
    · rw [ite_eq_right (fun h' => hd h'.2), ite_eq_left ⟨h0, hd⟩, zero_add, ite_eq_left h0]
  · rw [ite_eq_right (fun h' => h0 h'.1), ite_eq_right (fun h' => h0 h'.1), ite_eq_right h0, add_zero, smul_zero]

/-- A dot on the left strand of `E_c E_d` slides up through the crossing, `n` times. -/
theorem dgN_slideRNe_pow (μ : X) {c d : I} (h : c ≠ d) (n : ℕ) :
    dgC (presNM RD k S) μ [up c, up d] [up d, up c]
      (List.replicate n ([], .dot (up c), [up d]) ++ [([], .cross true c d, [])]) =
    dgC (presNM RD k S) μ [up c, up d] [up d, up c]
      (([], .cross true c d, []) :: List.replicate n ([up d], .dot (up c), [])) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    show dgC (presNM RD k S) μ [up c, up d] [up d, up c]
      ([([], .dot (up c), [up d])] ++ (List.replicate n ([], .dot (up c), [up d]) ++
        [([], .cross true c d, [])])) = _
    rw [← dgC_comp (t := [up c, up d]) (by schain) (by schain), ih, dgC_comp (by schain) (by schain)]
    show dgC (presNM RD k S) μ [up c, up d] [up d, up c]
      ([([], .dot (up c), [up d]), ([], .cross true c d, [])] ++
        List.replicate n ([up d], .dot (up c), [])) = _
    rw [← dgC_comp (t := [up d, up c]) (by schain) (by schain), dgC_slideRNe (presNM_klr hr) μ c d h,
      dgC_comp (by schain) (by schain)]
    simp [List.replicate_succ]

omit hr in
/-- `ncEval` of a monomial in two variables, ordered `x₀^a x₁^b`. -/
theorem ncEval_X2 {A : Type*} [Ring A] [Algebra k A] (y : Fin 2 → A) (a b : ℕ) :
    KLR.ncEval y (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) k) =
      y 0 ^ a * y 1 ^ b := by
  have e : (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) k) =
      MvPolynomial.monomial (Finsupp.single 0 a + Finsupp.single 1 b) 1 := by
    simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, mul_one]
  rw [e, ncEvalB_monomial, map_one, one_mul, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp [mul_assoc]

omit hr in
/-- A counterclockwise bubble of negative degree to the right of a strand kills a diagram. -/
theorem dgN_ccwRight_zero {lam : X} {t : List (Letter I)} (w : List (Letter I)) (i : I) (a : ℕ)
    (rest : List (LayerData I)) (h : (a : ℤ) < -ip RD i lam - 1) (hrest : SChain w rest t) :
    dgC (presNM RD k S) lam w t ((ccwLs i a).map (whL w []) ++ rest) = 0 := by
  refine dgC_eq_zero_at _ 0 w [] (dgN_ccwNeg S _ i a h) (by simp) ?_ ?_
  · simpa [List.drop_left'] using hrest
  · simp [List.take_left']

omit hr in
/-- The degree-zero counterclockwise bubble to the right of a strand is `1`. -/
theorem dgN_ccwRight_one {lam : X} {t : List (Letter I)} (w : List (Letter I)) (i : I)
    (rest : List (LayerData I)) (h : ip RD i lam ≤ -1) (hrest : SChain w rest t) :
    dgC (presNM RD k S) lam w t ((ccwLs i (-ip RD i lam - 1).toNat).map (whL w []) ++ rest) =
      dgC (presNM RD k S) lam w t rest := by
  rw [dgC_step_at _ 0 w [] (dgN_ccwOne S _ i h) (by simp) (by simpa [List.drop_left'] using hrest)
    (by simp [List.take_left'])]
  simp [List.drop_left']

/-- The dots of the double crossing in `dgN_turn2` (`E_i E_j`, rightmost region `λ`). -/
abbrev turn2Y (i j : I) (lam : X) : Fin 2 → End ((presNM RD k S).obj (ob RD lam [up i, up j])) :=
  ![dgEC (presNM RD k S) lam [up i, up j] [([], .dot (up i), [up j])],
    dgEC (presNM RD k S) lam [up i, up j] [([up i], .dot (up j), [])]]

/-- The left-hand side of `dgN_turn2` after the double crossing is expanded, as a `k`-linear
function of the polynomial. -/
def turn2F (i j : I) (lam : X) (n : ℕ) :
    MvPolynomial (Fin 2) k →ₗ[k] ((presNM RD k S).obj (ob RD lam [up j]) ⟶
      (presNM RD k S).obj (ob RD lam [up j])) where
  toFun p := ctxLC (presNM RD k S) lam [up j] [up j]
    ([([], .cup (dn i), [up j])] ++ List.replicate n ([dn i], .dot (up i), [up j])) [dn i] []
    [([], .cap (up i), [up j])] [up i, up j] [up i, up j]
    (KLR.ncEval (A := End ((presNM RD k S).obj (ob RD lam [up i, up j]))) (turn2Y i j lam) p)
  map_add' p q := by rw [ncEvalB_add, map_add]
  map_smul' c p := by
    rw [MvPolynomial.smul_eq_C_mul, ncEval_C_mul', ← Algebra.smul_def, map_smul]
    rfl

omit hr in
theorem turn2F_X2 (i j : I) (lam : X) (n a b : ℕ) :
    turn2F (RD := RD) (S := S) i j lam n (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) =
      dgC (presNM RD k S) lam [up j] [up j]
        ((ccwLs i (n + a)).map (whL [] [up j]) ++ List.replicate b ([], .dot (up j), [])) := by
  show ctxLC (presNM RD k S) lam [up j] [up j]
    ([([], .cup (dn i), [up j])] ++ List.replicate n ([dn i], .dot (up i), [up j])) [dn i] []
    [([], .cap (up i), [up j])] [up i, up j] [up i, up j]
    (KLR.ncEval (A := End ((presNM RD k S).obj (ob RD lam [up i, up j]))) (turn2Y i j lam)
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)) = _
  rw [ncEval_X2]
  simp only [turn2Y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [dgC_pow _ _ _ (by schain), dgC_pow _ _ _ (by schain), End.mul_def, dgEC, dgEC,
    dgC_comp (by schain) (by schain)]
  erw [ctxLC_dg _ _ (by schain) (by schain)]
  have h1 := dgC_interchange (P := presNM RD k S) (μ := lam) (S := [up j]) (T := [up j])
    ([([], .cup (dn i), [up j])] ++ List.replicate n ([dn i], .dot (up i), [up j]))
    [] (s := [dn i, up i]) (s' := []) (t := [up j]) (t' := [up j])
    (A := List.replicate a ([dn i], .dot (up i), []) ++ [([], .cap (up i), [])])
    (B := List.replicate b ([], .dot (up j), [])) (by schain) (by schain)
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil, whL,
    List.append_assoc, List.nil_append, List.cons_append, List.append_nil] at h1 ⊢
  rw [← h1]
  simp only [ccwLs, List.replicate_add, List.map_append, List.map_cons, List.map_nil,
    List.map_replicate, whL, List.nil_append, List.append_nil, List.cons_append, List.append_assoc,
    List.singleton_append]

omit hr in
theorem turn2F_val (i j : I) (lam : X) (n a b : ℕ)
    (ha : ((n + a : ℕ) : ℤ) ≤ -ip RD i (wt RD lam [up j]) - 1) :
    turn2F (RD := RD) (S := S) i j lam n (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) =
      if ((n + a : ℕ) : ℤ) = -ip RD i (wt RD lam [up j]) - 1 then
        dgC (presNM RD k S) lam [up j] [up j] (List.replicate b ([], .dot (up j), []))
      else 0 := by
  rw [turn2F_X2]
  split_ifs with h
  · have e : n + a = (-ip RD i (wt RD lam [up j]) - 1).toNat := by omega
    rw [e, dgN_ccwLeft_one _ i _ (by omega) (by schain)]
  · exact dgN_ccwLeft_zero _ i _ _ (by omega) (by schain)

/-- **Brundan (5.4), second relation** (`turn`, `⟨i, λ⟩ ≤ 0`, `0 ≤ n < -⟨i, λ⟩`): the upward
strand `j` crossing a counterclockwise bubble with `n` dots (both legs) equals `t_{ij}` times the
strand with the bubble on its right. -/
theorem dgN_turn2 {i j : I} (hij : i ≠ j) (lam : X) (n : ℕ) (hn : (n : ℤ) < -ip RD i lam) :
    dgC (presNM RD k S) lam [up j] [up j]
      ([([up j], .cup (dn i), [])] ++ List.replicate n ([up j, dn i], .dot (up i), []) ++
        (crosslL j i).map (whL [] [up i]) ++ [([dn i], .cross true j i, []), ([], .cap (up i), [up j])]) =
    (S.t i j : k) • dgC (presNM RD k S) lam [up j] [up j]
      ([([up j], .cup (dn i), [])] ++ List.replicate n ([up j, dn i], .dot (up i), []) ++
        [([up j], .cap (up i), [])]) := by
  -- the right-hand side
  have hR : dgC (presNM RD k S) lam [up j] [up j]
      ([([up j], .cup (dn i), [])] ++ List.replicate n ([up j, dn i], .dot (up i), []) ++
        [([up j], .cap (up i), [])]) =
      if (n : ℤ) = -ip RD i lam - 1 then dgC (presNM RD k S) lam [up j] [up j] [] else 0 := by
    have e : [([up j], .cup (dn i), [])] ++ List.replicate n ([up j, dn i], .dot (up i), []) ++
        [([up j], .cap (up i), [])] = (ccwLs i n).map (whL [up j] []) ++ [] := by
      simp [ccwLs, whL, List.map_replicate]
    rw [e]
    split_ifs with h0
    · have e' : n = (-ip RD i lam - 1).toNat := by omega
      rw [e', dgN_ccwRight_one _ i _ (by omega) (by schain)]
    · exact dgN_ccwRight_zero _ i n _ (by omega) (by schain)
  rw [hR]
  -- the left-hand side
  have h1 := dgC_interchange (P := presNM RD k S) (μ := lam) (S := [up j]) (T := [up j])
    [([up j], .cup (dn i), [])] [([dn i], .cross true j i, []), ([], .cap (up i), [up j])]
    (s := [up j, dn i]) (s' := [dn i, up j]) (t := [up i]) (t' := [up i])
    (A := crosslL j i) (B := List.replicate n ([], .dot (up i), [])) (by schain) (by schain)
  simp only [List.map_replicate, whL, List.append_nil, List.nil_append] at h1
  rw [← h1]
  rw [dgC_step_at _ 0 [] [] (dgN_pitchCup (RD := RD) (S := S) i j lam) (by simp)
    (by (try simp only [crosslL]); dnorm; schain) (by (try simp only [crosslL]); dnorm)]
  dnorm
  refine (dgC_step (presNM RD k S) lam [([], .cup (dn i), [up j])]
    [([dn i], .cross true j i, []), ([], .cap (up i), [up j])] [dn i] []
    (dgN_slideRNe_pow (RD := RD) hr (wt RD lam []) hij n).symm (by schain) (by schain)
    (by simp [whL, List.map_replicate]) rfl).trans ?_
  have e2 : ([([], .cup (dn i), [up j])] : List (LayerData I)) ++
      (List.replicate n (([], .dot (up i), [up j]) : LayerData I) ++
        [(([], .cross true i j, []) : LayerData I)]).map (whL [dn i] []) ++
      [([dn i], .cross true j i, []), ([], .cap (up i), [up j])] =
      ([([], .cup (dn i), [up j])] ++ List.replicate n ([dn i], .dot (up i), [up j])) ++
        ([([], .cross true i j, []), ([], .cross true j i, [])] : List (LayerData I)).map
          (whL [dn i] []) ++
        [([], .cap (up i), [up j])] := by
    simp [whL, List.map_replicate]
  rw [e2, dgC_stepL _ lam _ _ [dn i] [] (dgC_sqNe (presNM_klr hr) (wt RD lam []) i j hij)
    (by schain) (by schain) rfl]
  change turn2F (RD := RD) (S := S) i j lam n (qCL S i j) = _
  have hw : ip RD i (wt RD lam [up j]) = ip RD i lam - C.dij i j := by
    simp only [wt_cons, wt_nil, ip_up, ip_iX_ne hij]; ring
  have hX0 : ∀ a : ℕ, (MvPolynomial.X 0 ^ a : MvPolynomial (Fin 2) k) =
      MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ 0 := fun a => by ring
  have hX1 : ∀ b : ℕ, (MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) k) =
      MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ b := fun b => by ring
  by_cases hd : C.dot i j = 0
  · have hd0 : C.dij i j = 0 := (C.dij_eq_zero_iff hij).2 hd
    rw [qCL_of_dot_eq_zero S hd, show (MvPolynomial.C (S.t i j : k) : MvPolynomial (Fin 2) k) =
      MvPolynomial.C (S.t i j : k) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 0) by simp,
      MvPolynomial.C_mul', map_smul, turn2F_val _ _ _ n 0 0 (by omega)]
    split_ifs with h1 h2 h2 <;> first | rfl | omega
  · have hdpos := C.dij_pos hij hd
    have ht' : turn2F (RD := RD) (S := S) i j lam n
        (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ C.dij j i) = 0 := by
      rw [turn2F_val _ _ _ n 0 (C.dij j i) (by push_cast; omega)]
      exact ite_eq_right_iff.2 (fun h' => by push_cast at h'; omega)
    rw [qCL_of_dot_ne_zero S hd, map_add, map_add, MvPolynomial.C_mul', MvPolynomial.C_mul',
      map_smul, map_smul, hX0 (C.dij i j), hX1 (C.dij j i), ht', smul_zero, add_zero,
      turn2F_val _ _ _ n (C.dij i j) 0 (by push_cast; omega)]
    have hs : (turn2F (RD := RD) (S := S) i j lam n) (∑ p ∈ Finset.range (C.dij i j),
        ∑ q ∈ Finset.range (C.dij j i),
          if C.dot i i * (p : ℤ) + C.dot j j * q = -2 * C.dot i j then
            MvPolynomial.C (S.s i j p q) * MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q else 0) = 0 := by
      simp only [map_sum]
      refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q _ => ?_
      have hp' := Finset.mem_range.1 hp
      split_ifs
      · rw [mul_assoc, MvPolynomial.C_mul', map_smul, turn2F_val _ _ _ n _ _ (by omega),
          ite_eq_right_iff.2 (fun h' => by omega), smul_zero]
      · exact map_zero _
    rw [hs, add_zero]
    split_ifs with h1 h2 h2 <;> first | rfl | omega

omit hr in
/-- A dot slides around the cup `1 ⟶ E_i F_i` (left adjunction), from the upward leg to the
downward leg (dot cyclicity, `eq_cyclic_dot`). -/
theorem dgN_cupUp_dot (i : I) (μ : X) :
    dgC (presNM RD k S) μ [] [up i, dn i] [([], .cup (up i), []), ([], .dot (up i), [dn i])] =
      dgC (presNM RD k S) μ [] [up i, dn i] [([], .cup (up i), []), ([up i], .dot (dn i), [])] := by
  symm
  datC 1 [up i] [] (dgN_cycDotR S i μ)
  dswapC 0; dswapC 1
  datC 2 [] [dn i] (dgC_zigL' _ (presNM_zigzags RD k S) _ (up i))

/-- The layers of the curl `1 ⟶ F_i E_i`: the cup `1 ⟶ E_i F_i`, then the sideways crossing
`crossl i i` (Brundan's `σ ∘ η'`). -/
def curlBLs (i : I) : List (LayerData I) := [([], .cup (up i), [])] ++ crosslL i i

/-- The curl `σ ∘ η'` vanishes in a region with `⟨i, λ⟩ > 0` (Brundan (3.6), `startb`). -/
theorem dgN_curlB_pos (i : I) (lam : X) (h : 0 < ip RD i lam) :
    dgC (presNM RD k S) lam [] [dn i, up i] (curlBLs i) = 0 := by
  unfold curlBLs; dnorm
  dswapC 0
  have E := dgN_curlR (RD := RD) (S := S) hr i lam
  rw [show (-ip RD i lam + 1).toNat = 0 by omega, Finset.sum_range_zero, neg_zero] at E
  exact dgC_eq_zero_at _ 1 [dn i] [] E (by dnorm; schain) (by dnorm; schain) (by dnorm)

/-- The curl `σ ∘ η'` in a region with `⟨i, λ⟩ = 0` is minus the cup `1 ⟶ F_i E_i` (Brundan
(3.21), `everything`, degree `0`). -/
theorem dgN_curlB_zero (i : I) (lam : X) (h : ip RD i lam = 0) :
    dgC (presNM RD k S) lam [] [dn i, up i] (curlBLs i) =
      -dgC (presNM RD k S) lam [] [dn i, up i] [([], .cup (dn i), [])] := by
  unfold curlBLs; dnorm
  dswapC 0
  have E := dgN_curlR (RD := RD) (S := S) hr i lam
  rw [show (-ip RD i lam + 1).toNat = 1 by omega, Finset.sum_range_one, h,
    show ((0 : ℤ) - 1 + ((0 : ℕ) : ℤ)) = -1 by norm_num, cwN_neg_one (S := S) _ i h] at E
  simp only [bubRC] at E
  erw [plcLC_id] at E
  simp only [dotsN, neg_zero, Nat.cast_zero, sub_zero, Int.toNat_zero,
    List.replicate_zero, dgC_nil, Category.comp_id] at E
  rw [← dgC_nil] at E
  have E' : dgC (presNM RD k S) (wt RD lam []) [up i] [up i]
      [([up i], .cup (up i), []), ([], .cross true i i, [dn i]), ([up i], .cap (dn i), [])] =
      -dgC (presNM RD k S) (wt RD lam []) [up i] [up i] [] := E
  rw [dgC_stepL_at _ 1 [dn i] [] E' (by dnorm; schain) (by dnorm; schain) (by dnorm), map_neg,
    ctxLC_dg _ _ (by dnorm; schain) (by dnorm; schain)]
  dnorm

omit hr in
/-- `n` dots slide around the cup `1 ⟶ E_i F_i`. -/
theorem dgN_cupUp_dots (i : I) (μ : X) (n : ℕ) :
    dgC (presNM RD k S) μ [] [up i, dn i]
      ([([], .cup (up i), [])] ++ List.replicate n ([], .dot (up i), [dn i])) =
    dgC (presNM RD k S) μ [] [up i, dn i]
      ([([], .cup (up i), [])] ++ List.replicate n ([up i], .dot (dn i), [])) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e1 : ([([], Shape.cup (up i), [])] : List (LayerData I)) ++
        List.replicate (n + 1) ([], Shape.dot (up i), [dn i]) =
        [] ++ [([], Shape.cup (up i), []), ([], .dot (up i), [dn i])] ++
          List.replicate n ([], Shape.dot (up i), [dn i]) := by simp [List.replicate_succ]
    rw [e1, dgC_step (presNM RD k S) μ [] (List.replicate n ([], Shape.dot (up i), [dn i])) [] []
      (dgN_cupUp_dot i μ) (by schain) (by schain) (by simp) rfl]
    have h1 := dgC_interchange (P := presNM RD k S) (μ := μ) (S := []) (T := [up i, dn i])
      [([], .cup (up i), [])] [] (s := [up i]) (s' := [up i]) (t := [dn i]) (t' := [dn i])
      (A := List.replicate n ([], .dot (up i), [])) (B := [([], .dot (dn i), [])]) (by schain)
      (by schain)
    simp only [List.map_replicate, List.map_cons, List.map_nil, whL, List.append_nil,
      List.nil_append, List.cons_append, List.append_assoc] at h1 ⊢
    rw [← h1]
    have h2 : dgC (presNM RD k S) μ [] [up i, dn i]
        (([], .cup (up i), []) :: (List.replicate n ([], .dot (up i), [dn i]) ++
          [([up i], .dot (dn i), [])])) =
        dgC (presNM RD k S) μ [] [up i, dn i]
          (([], .cup (up i), []) :: List.replicate n ([], .dot (up i), [dn i])) ≫
        dgC (presNM RD k S) μ [up i, dn i] [up i, dn i] [([up i], .dot (dn i), [])] := by
      rw [dgC_comp (by schain) (by schain)]; simp
    rw [h2]
    erw [ih]
    rw [dgC_comp (by schain) (by schain)]
    simp [List.replicate_succ']

/-- The layers of the clockwise bubble with `m` dots on its upward leg. -/
def cwUpLs (i : I) (m : ℕ) : List (LayerData I) :=
  [([], .cup (up i), [])] ++ List.replicate m ([], .dot (up i), [dn i]) ++ [([], .cap (dn i), [])]

omit hr in
theorem dgN_cwUp (ν : X) (i : I) (m : ℕ) :
    dgC (presNM RD k S) ν [] [] (cwUpLs i m) = dgC (presNM RD k S) ν [] [] (cwLs i m) := by
  unfold cwUpLs cwLs
  rw [← dgC_comp (t := [up i, dn i]) (by schain) (by schain), dgN_cupUp_dots,
    dgC_comp (by schain) (by schain)]

omit hr in
theorem drop_length_map {α β : Type*} (f : α → β) (l : List α) : (l.map f).drop l.length = [] := by
  rw [← List.length_map f, List.drop_length]

omit hr in
/-- A clockwise bubble (dots on the upward leg) of negative degree at the far right kills a
diagram. -/
theorem dgN_cwUpRight_zero {lam : X} {s : List (Letter I)} (w : List (Letter I)) (i : I) (a : ℕ)
    (pre : List (LayerData I)) (h : (a : ℤ) < ip RD i lam - 1) (hpre : SChain s pre w) :
    dgC (presNM RD k S) lam s w (pre ++ (cwUpLs i a).map (whL w [])) = 0 := by
  have hc : SChain [] (cwUpLs i a) [] := by unfold cwUpLs; schain
  have E : dgC (presNM RD k S) (wt RD lam []) [] [] (cwUpLs i a) = 0 :=
    (dgN_cwUp _ i a).trans (dgN_cwNeg S _ i a h)
  rw [← dgC_comp hpre (by simpa using hc.whisk w []),
    dgC_eq_zero_at ((cwUpLs i a).map (whL w [])) 0 w [] E (by simp)
      (by rw [zero_add, drop_length_map]; simp) (by simp), Limits.comp_zero]

omit hr in
/-- The degree-zero clockwise bubble (dots on the upward leg) at the far right is `1`. -/
theorem dgN_cwUpRight_one {lam : X} {s : List (Letter I)} (w : List (Letter I)) (i : I)
    (pre : List (LayerData I)) (h : 1 ≤ ip RD i lam) (hpre : SChain s pre w) :
    dgC (presNM RD k S) lam s w (pre ++ (cwUpLs i (ip RD i lam - 1).toNat).map (whL w [])) =
      dgC (presNM RD k S) lam s w pre := by
  have hc : SChain [] (cwUpLs i (ip RD i lam - 1).toNat) [] := by unfold cwUpLs; schain
  have E : dgC (presNM RD k S) (wt RD lam []) [] [] (cwUpLs i (ip RD i lam - 1).toNat) =
      dgC (presNM RD k S) (wt RD lam []) [] [] [] :=
    (dgN_cwUp _ i _).trans (dgN_cwOne S _ i h)
  rw [← dgC_comp hpre (by simpa using hc.whisk w []),
    dgC_step_at ((cwUpLs i (ip RD i lam - 1).toNat).map (whL w [])) 0 w [] E (by simp)
      (by rw [zero_add, drop_length_map]; simp) (by simp)]
  rw [zero_add, drop_length_map]
  simp only [List.take_zero, List.map_nil, List.nil_append, List.append_nil]
  rw [dgC_nil, Category.comp_id]

omit hr in
/-- A clockwise bubble (dots on the upward leg) of negative degree at the far left kills a
diagram. -/
theorem dgN_cwUpLeft_zero {lam : X} {t : List (Letter I)} (w : List (Letter I)) (i : I) (a : ℕ)
    (rest : List (LayerData I)) (h : (a : ℤ) < ip RD i (wt RD lam w) - 1) (hrest : SChain w rest t) :
    dgC (presNM RD k S) lam w t ((cwUpLs i a).map (whL [] w) ++ rest) = 0 := by
  refine dgC_eq_zero_at _ 0 [] w ((dgN_cwUp _ i a).trans (dgN_cwNeg S _ i a h)) (by simp) ?_ ?_
  · simpa [List.drop_left'] using hrest
  · simp [List.take_left']

omit hr in
/-- The degree-zero clockwise bubble (dots on the upward leg) at the far left is `1`. -/
theorem dgN_cwUpLeft_one {lam : X} {t : List (Letter I)} (w : List (Letter I)) (i : I)
    (rest : List (LayerData I)) (h : 1 ≤ ip RD i (wt RD lam w)) (hrest : SChain w rest t) :
    dgC (presNM RD k S) lam w t
        ((cwUpLs i (ip RD i (wt RD lam w) - 1).toNat).map (whL [] w) ++ rest) =
      dgC (presNM RD k S) lam w t rest := by
  rw [dgC_step_at _ 0 [] w ((dgN_cwUp _ i _).trans (dgN_cwOne S _ i h)) (by simp)
    (by simpa [List.drop_left'] using hrest) (by simp [List.take_left'])]
  simp [List.drop_left']

/-- A dot on the right strand of `E_c E_d` slides up through the crossing, `n` times
(`dgC_slideLNe` read downwards). -/
theorem dgN_slideLNe_pow (μ : X) {c d : I} (h : c ≠ d) (n : ℕ) :
    dgC (presNM RD k S) μ [up c, up d] [up d, up c]
      (([], .cross true c d, []) :: List.replicate n ([], .dot (up d), [up c])) =
    dgC (presNM RD k S) μ [up c, up d] [up d, up c]
      (List.replicate n ([up c], .dot (up d), []) ++ [([], .cross true c d, [])]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ']
    show dgC (presNM RD k S) μ [up c, up d] [up d, up c]
      ((([], .cross true c d, []) :: List.replicate n ([], .dot (up d), [up c])) ++
        [([], .dot (up d), [up c])]) = _
    rw [← dgC_comp (t := [up d, up c]) (by schain) (by schain), ih, dgC_comp (by schain) (by schain),
      List.append_assoc]
    show dgC (presNM RD k S) μ [up c, up d] [up d, up c]
      (List.replicate n ([up c], .dot (up d), []) ++ [([], .cross true c d, []),
        ([], .dot (up d), [up c])]) = _
    rw [← dgC_comp (t := [up c, up d]) (by schain) (by schain), dgC_slideLNe (presNM_klr hr) μ c d h,
      dgC_comp (by schain) (by schain)]
    simp [List.replicate_succ']

/-- The dots of the double crossing in `dgN_turn2E` (`E_j E_i`, rightmost region `λ + α_i - α_i`
read on `E_j E_i F_i`). -/
abbrev turn2EY (i j : I) (lam : X) :
    Fin 2 → End ((presNM RD k S).obj (ob RD (wt RD lam [dn i]) [up j, up i])) :=
  ![dgEC (presNM RD k S) (wt RD lam [dn i]) [up j, up i] [([], .dot (up j), [up i])],
    dgEC (presNM RD k S) (wt RD lam [dn i]) [up j, up i] [([up j], .dot (up i), [])]]

/-- The left-hand side of `dgN_turn2E` after the double crossing is expanded. -/
def turn2EF (i j : I) (lam : X) (n : ℕ) :
    MvPolynomial (Fin 2) k →ₗ[k] ((presNM RD k S).obj (ob RD lam [up j]) ⟶
      (presNM RD k S).obj (ob RD lam [up j])) where
  toFun p := ctxLC (presNM RD k S) lam [up j] [up j]
    ([([up j], .cup (up i), [])] ++ List.replicate n ([up j], .dot (up i), [dn i])) [] [dn i]
    [([up j], .cap (dn i), [])] [up j, up i] [up j, up i]
    (KLR.ncEval (A := End ((presNM RD k S).obj (ob RD (wt RD lam [dn i]) [up j, up i])))
      (turn2EY i j lam) p)
  map_add' p q := by rw [ncEvalB_add, map_add]
  map_smul' c p := by
    rw [MvPolynomial.smul_eq_C_mul, ncEval_C_mul', ← Algebra.smul_def, map_smul]
    rfl

omit hr in
theorem turn2EF_X2 (i j : I) (lam : X) (n a b : ℕ) :
    turn2EF (RD := RD) (S := S) i j lam n (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) =
      dgC (presNM RD k S) lam [up j] [up j]
        (List.replicate a ([], .dot (up j), []) ++ (cwUpLs i (n + b)).map (whL [up j] [])) := by
  show ctxLC (presNM RD k S) lam [up j] [up j]
    ([([up j], .cup (up i), [])] ++ List.replicate n ([up j], .dot (up i), [dn i])) [] [dn i]
    [([up j], .cap (dn i), [])] [up j, up i] [up j, up i]
    (KLR.ncEval (A := End ((presNM RD k S).obj (ob RD (wt RD lam [dn i]) [up j, up i])))
      (turn2EY i j lam) (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)) = _
  rw [ncEval_X2]
  simp only [turn2EY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [dgC_pow _ _ _ (by schain), dgC_pow _ _ _ (by schain), End.mul_def, dgEC, dgEC,
    dgC_comp (by schain) (by schain), ctxLC_dg _ _ (by schain) (by schain)]
  have h1 := dgC_interchange (P := presNM RD k S) (μ := lam) (S := [up j]) (T := [up j])
    [] [([up j], .cap (dn i), [])] (s := [up j]) (s' := [up j]) (t := []) (t' := [up i, dn i])
    (A := List.replicate a ([], .dot (up j), []))
    (B := [([], .cup (up i), [])] ++ List.replicate n ([], .dot (up i), [dn i]) ++
      List.replicate b ([], .dot (up i), [dn i])) (by schain) (by schain)
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil, whL,
    List.append_assoc, List.nil_append, List.cons_append, List.append_nil] at h1 ⊢
  rw [← h1]
  simp only [cwUpLs, List.replicate_add, List.map_append, List.map_cons, List.map_nil,
    List.map_replicate, whL, List.nil_append, List.append_nil, List.cons_append, List.append_assoc,
    List.singleton_append]

omit hr in
theorem turn2EF_val (i j : I) (lam : X) (n a b : ℕ)
    (hb : ((n + b : ℕ) : ℤ) ≤ ip RD i lam - 1) :
    turn2EF (RD := RD) (S := S) i j lam n (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) =
      if ((n + b : ℕ) : ℤ) = ip RD i lam - 1 then
        dgC (presNM RD k S) lam [up j] [up j] (List.replicate a ([], .dot (up j), []))
      else 0 := by
  rw [turn2EF_X2]
  split_ifs with h
  · have e : n + b = (ip RD i lam - 1).toNat := by omega
    rw [e, dgN_cwUpRight_one _ i _ (by omega) (by schain)]
  · exact dgN_cwUpRight_zero _ i _ _ (by omega) (by schain)

/-- **Brundan, proof of (5.2), second family** (the analogue of (5.4) for `⟨i, λ⟩ ≥ d_{ij}`,
`0 ≤ n < ⟨i, λ⟩ - d_{ij}`): the upward strand `j` crossing a clockwise bubble with `n` dots (both
legs) equals `t_{ij}` times the strand with the bubble on its left. -/
theorem dgN_turn2E {i j : I} (hij : i ≠ j) (lam : X) (n : ℕ)
    (hn : (n : ℤ) < ip RD i lam - C.dij i j) :
    dgC (presNM RD k S) lam [up j] [up j]
      ([([up j], .cup (up i), []), ([], .cross true j i, [dn i])] ++
        (crosslL j i).map (whL [up i] []) ++ List.replicate n ([], .dot (up i), [dn i, up j]) ++
        [([], .cap (dn i), [up j])]) =
    (S.t i j : k) • dgC (presNM RD k S) lam [up j] [up j] ((cwUpLs i n).map (whL [] [up j])) := by
  have hw : ip RD i (wt RD lam [up j]) = ip RD i lam - C.dij i j := by
    simp only [wt_cons, wt_nil, ip_up, ip_iX_ne hij]; ring
  -- the right-hand side
  have hR : dgC (presNM RD k S) lam [up j] [up j] ((cwUpLs i n).map (whL [] [up j])) =
      if (n : ℤ) = ip RD i lam - C.dij i j - 1 then dgC (presNM RD k S) lam [up j] [up j] []
      else 0 := by
    rw [← List.append_nil ((cwUpLs i n).map (whL [] [up j]))]
    split_ifs with h0
    · have e' : n = (ip RD i (wt RD lam [up j]) - 1).toNat := by omega
      rw [e', dgN_cwUpLeft_one _ i _ (by omega) (by schain)]
    · exact dgN_cwUpLeft_zero _ i n _ (by omega) (by schain)
  rw [hR]
  -- the left-hand side
  have h1 : dgC (presNM RD k S) lam [up j] [up j]
      ([([up j], .cup (up i), []), ([], .cross true j i, [dn i])] ++
        (crosslL j i).map (whL [up i] []) ++ List.replicate n ([], .dot (up i), [dn i, up j]) ++
        [([], .cap (dn i), [up j])]) =
      dgC (presNM RD k S) lam [up j] [up j]
      ([([up j], .cup (up i), []), ([], .cross true j i, [dn i])] ++
        List.replicate n ([], .dot (up i), [up j, dn i]) ++ (crosslL j i).map (whL [up i] []) ++
        [([], .cap (dn i), [up j])]) := by
    have := dgC_interchange (P := presNM RD k S) (μ := lam) (S := [up j]) (T := [up j])
      [([up j], .cup (up i), []), ([], .cross true j i, [dn i])] [([], .cap (dn i), [up j])]
      (s := [up i]) (s' := [up i]) (t := [up j, dn i]) (t' := [dn i, up j])
      (A := List.replicate n ([], .dot (up i), [])) (B := crosslL j i) (by schain) (by schain)
    simpa [whL, List.map_replicate] using this.symm
  rw [h1]
  -- the pitchfork at the top
  rw [dgC_step (presNM RD k S) lam
    ([([up j], .cup (up i), []), ([], .cross true j i, [dn i])] ++
      List.replicate n ([], .dot (up i), [up j, dn i])) [] [] [] (dgN_pitchCap (RD := RD) (S := S) i j lam)
    (by schain) (by schain) (by simp) rfl]
  -- the dots slide below the first crossing
  refine (dgC_step (presNM RD k S) lam [([up j], .cup (up i), [])]
    [([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])] [] [dn i]
    (dgN_slideLNe_pow (RD := RD) hr (wt RD lam [dn i]) hij.symm n) (by schain) (by schain)
    (by simp [whL, List.map_replicate]) rfl).trans ?_
  have e2 : ([([up j], .cup (up i), [])] : List (LayerData I)) ++
      (List.replicate n (([up j], .dot (up i), []) : LayerData I) ++
        [(([], .cross true j i, []) : LayerData I)]).map (whL [] [dn i]) ++
      [([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])] =
      ([([up j], .cup (up i), [])] ++ List.replicate n ([up j], .dot (up i), [dn i])) ++
        ([([], .cross true j i, []), ([], .cross true i j, [])] : List (LayerData I)).map
          (whL [] [dn i]) ++
        [([up j], .cap (dn i), [])] := by
    simp [whL, List.map_replicate]
  rw [e2, dgC_stepL _ lam _ _ [] [dn i] (dgC_sqNe (presNM_klr hr) (wt RD lam [dn i]) j i hij.symm)
    (by schain) (by schain) rfl]
  change turn2EF (RD := RD) (S := S) i j lam n (qCL S j i) = _
  have hX0 : ∀ a : ℕ, (MvPolynomial.X 0 ^ a : MvPolynomial (Fin 2) k) =
      MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ 0 := fun a => by ring
  have hX1 : ∀ b : ℕ, (MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) k) =
      MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ b := fun b => by ring
  by_cases hd : C.dot j i = 0
  · have hd0 : C.dij i j = 0 := (C.dij_eq_zero_iff hij).2 (by rw [C.symm]; exact hd)
    rw [qCL_of_dot_eq_zero S hd, show (MvPolynomial.C (S.t j i : k) : MvPolynomial (Fin 2) k) =
      MvPolynomial.C (S.t j i : k) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 0) by simp,
      MvPolynomial.C_mul', map_smul, turn2EF_val _ _ _ n 0 0 (by omega),
      S.t_symm j i hd]
    split_ifs with h1 h2 h2 <;> first | rfl | omega
  · have hdpos := C.dij_pos hij (by rw [C.symm]; exact hd)
    have ht' : turn2EF (RD := RD) (S := S) i j lam n
        (MvPolynomial.X 0 ^ C.dij j i * MvPolynomial.X 1 ^ 0) = 0 := by
      rw [turn2EF_val _ _ _ n (C.dij j i) 0 (by push_cast; omega)]
      exact ite_eq_right_iff.2 (fun h' => by push_cast at h'; omega)
    rw [qCL_of_dot_ne_zero S hd, map_add, map_add, MvPolynomial.C_mul', MvPolynomial.C_mul',
      map_smul, map_smul, hX0 (C.dij j i), hX1 (C.dij i j), ht', smul_zero, zero_add,
      turn2EF_val _ _ _ n 0 (C.dij i j) (by push_cast; omega)]
    have hs : (turn2EF (RD := RD) (S := S) i j lam n) (∑ p ∈ Finset.range (C.dij j i),
        ∑ q ∈ Finset.range (C.dij i j),
          if C.dot j j * (p : ℤ) + C.dot i i * q = -2 * C.dot j i then
            MvPolynomial.C (S.s j i p q) * MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q else 0) = 0 := by
      simp only [map_sum]
      refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q hq => ?_
      have hq' := Finset.mem_range.1 hq
      split_ifs
      · rw [mul_assoc, MvPolynomial.C_mul', map_smul, turn2EF_val _ _ _ n _ _ (by omega),
          ite_eq_right_iff.2 (fun h' => by omega), smul_zero]
      · exact map_zero _
    rw [hs, add_zero]
    split_ifs with h1 h2 h2 <;> first | rfl | omega

end Categorification.KL3.Diagram.CL
