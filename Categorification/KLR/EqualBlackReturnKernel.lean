/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ExitPolynomialMatrix

/-!
# Four equal-black return columns at the right extreme

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21). On either
of the two right-extreme arms the upper return can be followed by the crossing
of the two equal black strands. These four affine columns have two polynomial
rows and two full-joint coefficients when the red/black square is a standard
power of the black dot.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open TypeA Equiv MvPolynomial
variable {I k : Type*} [DecidableEq I] [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
    {ν : Multiset I}
local notation "m" => Multiset.card ν
local notation "R" => KLRAlgebra k Q ν
local notation "P" => MvPolynomial (Fin m) k

/-- Crossing a polynomial above the black-crossed row retains only its
divided difference since the second black crossing squares to zero. -/
private theorem black_cross_polynomial_row (s : Seq ν) (l : List ℕ) (j : ℕ) (hj : j + 1 < m)
    (he : (wordProd m l • s).lbl ⟨j, by omega⟩ = (wordProd m l • s).lbl ⟨j + 1, hj⟩)
    (f : P) :
    (ψ j * (pol f * (ψw (j :: l) * e s)) : R) = pol (NilHecke.dd k m j f) * (ψw (j :: l) * e s) := by
  let r := wordProd m l • s
  let z : R := ψw (j :: l) * e s
  have fixed := sadj_smul_eq_self hj he
  have top : wordProd m (j :: l) • s = r := by rw [wordProd_cons, mul_smul, fixed]
  have hz : e r * z = z := by
    simpa only [top, map_one, one_mul] using e_mul_pol_ψw_e (Q := Q) (1 : P) (j :: l) s
  have sq := exit_square_word (Q := Q) s l j hj
  rw [exitSquarePolynomial, ite_eq_left he, map_zero, zero_mul] at sq
  have nil : ψ j * z = 0 := by simpa only [z, ψw_cons, mul_assoc] using sq
  have cross := ψ_mul_pol_mul_e (Q := Q) j hj r f
  rw [ite_eq_left he] at cross
  change ψ j * (pol f * z) = pol _ * z
  calc
    _ = (ψ j * pol f * e r) * z := by rw [mul_assoc _ (e r), hz, mul_assoc]
    _ = _ := by rw [cross, add_mul, mul_assoc _ (e r), hz, mul_assoc _ (e r), hz,
                 mul_assoc, nil, mul_zero, zero_add]

/-- The four return columns at the equal-black extreme have polynomial rows
`(q, ∂q, 0, 0)` and `(0, s(q), q, ∂q)`. These are exact equations at any
reduced extreme word which stays reduced after swapping the two black strands.
Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21). -/
theorem equalBlack_four_return_matrix_iff (hQ : KLRSymm Q) (s : Seq ν) (l : List ℕ) (b j : ℕ)
    (hb : b + 1 < m) (hj : j + 1 < m) (hl : IsReduced m l) (hjl : IsReduced m (j :: l))
    (he : (wordProd m l • s).lbl ⟨j, by omega⟩ = (wordProd m l • s).lbl ⟨j + 1, hj⟩)
    (f g h i : P) :
    let q := exitSquarePolynomial Q (wordProd m l • s) b hb
    (pol f * (ψw (b :: b :: l) * e s) + pol g * (ψw (j :: b :: b :: l) * e s) +
      pol h * (ψw (b :: b :: j :: l) * e s) + pol i * (ψw (j :: b :: b :: j :: l) * e s) : R) = 0 ↔
      f * q + g * NilHecke.dd k m j q = 0 ∧ g * swapPol j hj q + h * q + i * NilHecke.dd k m j q = 0 := by
  intro q
  have fix := sadj_smul_eq_self hj he
  have tr : wordProd m (j :: l) • s = wordProd m l • s := by rw [wordProd_cons, mul_smul, fix]
  have square := exit_square_word (Q := Q) s (j :: l) b hb
  rw [tr] at square
  have last : (ψw (j :: b :: b :: j :: l) * e s : R) = pol (NilHecke.dd k m j q) * (ψw (j :: l) * e s) := by
    rw [ψw_cons, mul_assoc, square, black_cross_polynomial_row s l j hj he q]
  have first := equalBlack_return_expansion (Q := Q) s l b j hb hj he f g h
  dsimp only at first
  rw [first, last, add_assoc, ← mul_assoc (pol i), ← map_mul, ← add_mul, ← map_add]
  exact top_polynomial_pair_eq_zero_iff_of_reduced hQ hl j hjl s _ _

/-- The monomial `q=X_a^n` divides `g` whenever it divides `g ∂q`. Multiplying
by `X_a-X_b` reduces this to divisibility of `g X_b^n` by `q`. -/
private theorem X_pow_dvd_of_dvd_mul_ddiff {σ : Type*} {a b : σ} (hab : a ≠ b) (n : ℕ)
    {g : MvPolynomial σ k} (h : X a ^ n ∣ g * ddiff a b (X a ^ n)) : X a ^ n ∣ g := by
  classical
  have spec := ddiff_spec (k := k) hab (X a ^ n)
  have sw : rename (swap a b) ((X a : MvPolynomial σ k) ^ n) = X b ^ n := by
    rw [map_pow, rename_X, swap_apply_left]
  rw [sw] at spec
  apply X_pow_dvd_of_dvd_mul_other hab n
  obtain ⟨c, hc⟩ := h
  refine ⟨g - c * (X a - X b), ?_⟩
  linear_combination g * spec - (X a - X b) * hc

/-- For a standard red square `q=X_j^n`, the four-column kernel is generated
over the upper dot polynomials by `(∂q,-q,s(q),0)` and `(0,0,∂q,-q)`.
The two black positions are distinct polynomial variables. The base ring may
have zero divisors. Webster, arXiv:1309.3796v2, §6.1, proof after (6.21). -/
theorem equalBlack_four_return_kernel (hQ : KLRSymm Q) (s : Seq ν) (l : List ℕ) (b j n : ℕ)
    (hb : b + 1 < m) (hj : j + 1 < m) (hl : IsReduced m l) (hjl : IsReduced m (j :: l))
    (he : (wordProd m l • s).lbl ⟨j, by omega⟩ = (wordProd m l • s).lbl ⟨j + 1, hj⟩)
    (hw : exitSquarePolynomial Q (wordProd m l • s) b hb = X (⟨j, by omega⟩ : Fin m) ^ n)
    (f g h i : P) :
    let q : P := X (⟨j, by omega⟩ : Fin m) ^ n
    let q' : P := X (⟨j + 1, hj⟩ : Fin m) ^ n
    let d := NilHecke.dd k m j q
    (pol f * (ψw (b :: b :: l) * e s) + pol g * (ψw (j :: b :: b :: l) * e s) +
      pol h * (ψw (b :: b :: j :: l) * e s) + pol i * (ψw (j :: b :: b :: j :: l) * e s) : R) = 0 ↔
      ∃ u v : P, f = u * d ∧ g = -(u * q) ∧ h = u * q' + v * d ∧ i = -(v * q) := by
  intro q q' d
  let a : Fin m := ⟨j, by omega⟩
  let b' : Fin m := ⟨j + 1, hj⟩
  have hab : a ≠ b' := by intro e; have e' := congrArg Fin.val e; change j = j + 1 at e'; omega
  have sw : swapPol j hj q = q' := by
    change rename (swap a b') ((X a : P) ^ n) = X b' ^ n
    rw [map_pow, rename_X, swap_apply_left]
  have divide {p : P} (hp : q ∣ p * d) : q ∣ p := by
    apply X_pow_dvd_of_dvd_mul_ddiff hab n
    simpa only [d, NilHecke.dd_of_lt hj] using hp
  have reg : IsRegular q := isRegular_X_pow n
  have matrix := equalBlack_four_return_matrix_iff hQ s l b j hb hj hl hjl he f g h i
  dsimp only at matrix
  rw [hw, sw] at matrix
  rw [matrix]
  change (f * q + g * d = 0 ∧ g * q' + h * q + i * d = 0) ↔ _
  constructor
  · rintro ⟨h₀, h₁⟩
    have dg : q ∣ (-g) * d := ⟨f, by linear_combination -h₀⟩
    obtain ⟨u, hu⟩ := divide dg
    have hg : g = -(u * q) := by linear_combination -hu
    subst g
    have di : q ∣ (-i) * d := ⟨h - u * q', by linear_combination -h₁⟩
    obtain ⟨v, hv⟩ := divide di
    have hi : i = -(v * q) := by linear_combination -hv
    subst i
    refine ⟨u, v, reg.right ?_, rfl, reg.right ?_, rfl⟩
    · linear_combination h₀
    · linear_combination h₁
  · rintro ⟨u, v, rfl, rfl, rfl, rfl⟩
    constructor <;> ring

/-- Every polynomial relation in the four return columns admits a single
coefficient at the common full joint. Its two summands use the plain return
and the return with the equal-black crossing on top. Webster,
arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21), in the affine algebra. -/
theorem exists_equalBlack_four_cycle_coefficient (hQ : KLRSymm Q) (s : Seq ν) (l : List ℕ)
    (b n : ℕ) (hp : b + 2 < m) (hl : IsReduced m l) (hjl : IsReduced m ((b + 1) :: l))
    (he : (wordProd m l • s).lbl ⟨b + 1, by omega⟩ = (wordProd m l • s).lbl ⟨b + 2, hp⟩)
    (hn : (wordProd m l • s).lbl ⟨b, by omega⟩ ≠ (wordProd m l • s).lbl ⟨b + 1, by omega⟩)
    (hw : Q ((wordProd m l • s).lbl ⟨b, by omega⟩) ((wordProd m l • s).lbl ⟨b + 1, by omega⟩) = X 1 ^ n)
    (f g h i : P)
    (relation : (pol f * (ψw (b :: b :: l) * e s) + pol g * (ψw ((b + 1) :: b :: b :: l) * e s) +
      pol h * (ψw (b :: b :: (b + 1) :: l) * e s) +
      pol i * (ψw ((b + 1) :: b :: b :: (b + 1) :: l) * e s) : R) = 0) :
    let t := sadj m b • (wordProd m l • s)
    let j := b + 1
    ∃ c : R, c * e (sadj m j • t) = c ∧
      c * (ψw [b, j] * e t) = -(pol f * (ψw [b] * e t) + pol g * (ψw [j, b] * e t)) ∧
      c * (ψw [j] * e t) = pol h * (ψw [b] * e t) + pol i * (ψw [j, b] * e t) := by
  intro t j
  let top := wordProd m l • s
  let L : Fin m := ⟨j, by omega⟩
  let H : Fin m := ⟨j + 1, hp⟩
  let q : P := X L ^ n
  let q' : P := X H ^ n
  let d := NilHecke.dd k m j q
  have hb : b + 1 < m := by omega
  have weight : exitSquarePolynomial Q top b hb = q := by
    unfold exitSquarePolynomial
    dsimp only
    rw [ite_eq_right hn, hw, map_pow, rename_X]
    rfl
  obtain ⟨u, v, hf, hg, hh, hi⟩ := (equalBlack_four_return_kernel hQ s l b j n hb hp hl hjl he weight f g h i).1 relation
  have gen := (equalBlack_return_kernel hQ s l b j n hb hp hl hjl he weight d (-q) q').2
    ⟨1, by simp only [one_mul]; rfl, by simp only [one_mul]; rfl, by simp only [one_mul]; rfl⟩
  obtain ⟨w, fixed, ordinary, reversed⟩ := exists_equalBlack_cycle_coefficient hQ s l b n hp hl hjl he hn hw d (-q) q' gen
  let Y : R := ψw [b] * e t
  let Z : R := ψw [j, b] * e t
  let Barm : R := ψw [b, j] * e t
  let Darm : R := ψw [j] * e t
  have wB : w * Barm = pol q * Z - pol d * Y := by
    change w * Barm = -(pol d * Y + pol (-q) * Z) at ordinary
    rw [ordinary, map_neg, neg_mul]; abel
  have wD : w * Darm = pol q' * Y := reversed
  have tr : wordProd m [b] • t = top := by
    simp only [wordProd_cons, wordProd_nil, mul_one]
    exact sadj_smul_smul b top
  have supported : e top * Y = Y := by
    simpa only [tr, map_one, one_mul] using e_mul_pol_ψw_e (Q := Q) (1 : P) [b] t
  have neq : L ≠ H := by intro z; have h := congrArg Fin.val z; change j = j + 1 at h; omega
  have sw : swapPol j hp q = q' := by
    change rename (swap L H) ((X L : P) ^ n) = X H ^ n
    rw [map_pow, rename_X, swap_apply_left]
  have sw' : swapPol j hp q' = q := by
    change rename (swap L H) ((X H : P) ^ n) = X L ^ n
    rw [map_pow, rename_X, swap_apply_right]
  have dd : NilHecke.dd k m j q' = -d := by
    change NilHecke.dd k m j q' = -NilHecke.dd k m j q
    rw [← sw, NilHecke.dd_of_lt hp]
    exact ddiff_rename_swap neq q
  have crossD : ψ j * (w * Darm) = w * Barm := by
    rw [wD, wB]
    have slide := ψ_mul_pol_mul_e (Q := Q) j hp top q'
    rw [ite_eq_left he, sw', dd, map_neg, neg_mul, ← sub_eq_add_neg] at slide
    have eq := congrArg (· * Y) slide
    rw [sub_mul, mul_assoc _ (e _), supported, mul_assoc _ (e _), supported,
      mul_assoc _ (e _), supported] at eq
    simpa only [Y, Z, ψw_cons, mul_assoc] using eq
  have crossB : ψ j * (w * Barm) = 0 := by
    rw [← crossD, wD]
    have sq := ψ_sq (Q := Q) j hp top
    rw [ite_eq_left he] at sq
    have cut : e top * (pol q' * Y) = pol q' * Y := by
      rw [← mul_assoc, (e_commute_pol _ _).eq, mul_assoc, supported]
    have eq := congrArg (· * (pol q' * Y)) sq
    rwa [mul_assoc _ (e top), cut, mul_assoc, zero_mul] at eq
  refine ⟨pol u * w - pol v * (ψ j * w), ?_, ?_, ?_⟩
  · have cut : w * e (sadj m j • t) = w := fixed
    simp only [sub_mul, mul_assoc, cut]
  · change (pol u * w - pol v * (ψ j * w)) * Barm = -(pol f * Y + pol g * Z)
    rw [sub_mul, mul_assoc, mul_assoc, mul_assoc (ψ j), crossB, mul_zero, sub_zero, wB, hf, hg]
    simp only [map_neg, map_mul, mul_assoc, neg_mul, neg_add_rev, neg_neg, sub_eq_add_neg, mul_add, mul_neg]
    rfl
  · change (pol u * w - pol v * (ψ j * w)) * Darm = pol h * Y + pol i * Z
    rw [sub_mul, mul_assoc, mul_assoc, mul_assoc (ψ j), crossD, wB, wD, hh, hi]
    simp only [map_add, map_neg, map_mul, mul_sub, add_mul, neg_mul, mul_assoc]
    abel

/-- PBW expansion of a supported corner where the only compatible permutations
are two prescribed distinct reduced words. -/
theorem exists_two_corner_coefficients_of_words (hQ : KLRSymm Q) (s t : Seq ν) (l k : List ℕ)
    (hl : IsReduced m l) (hk : IsReduced m k) (huv : wordProd m l ≠ wordProd m k)
    (matching : ∀ w : Perm (Fin m), w • s = t ↔ w = wordProd m l ∨ w = wordProd m k)
    (x : R) (hleft : e t * x = x) (hright : x * e s = x) :
    ∃ f g : P, x = pol f * (ψw l * e s) + pol g * (ψw k * e s) := by
  classical
  let u := wordProd m l
  let v := wordProd m k
  obtain ⟨rep, rU, rV, hrep⟩ := exists_pbw_words_for_pair hl hk huv
  change u ≠ v at huv
  change rep u = l at rU
  change rep v = k at rV
  let f w := exitPolynomial hQ rep hrep s w x
  let term w : R := pol (f w) * ψw (rep w) * e s
  have sum : ∑ w, e t * term w = x := by
    rw [← Finset.mul_sum, show (∑ w, term w) = x * e s from sum_exitPolynomials hQ rep hrep s x, hright, hleft]
  have fix (w : Perm (Fin m)) : e (w • s) * term w = term w := by
    simpa only [(hrep w).2] using e_mul_pol_ψw_e (Q := Q) (f w) (rep w) s
  have vanish (w : Perm (Fin m)) (hu : w ≠ u) (hv : w ≠ v) : e t * term w = 0 := by
    have ne : t ≠ w • s := fun h => ((matching w).mp h.symm).elim hu hv
    rw [← fix w, ← mul_assoc, e_mul_e, ite_eq_right ne, zero_mul]
  rw [Fintype.sum_eq_add _ _ huv (fun w hw => vanish w hw.1 hw.2)] at sum
  have fu := fix u
  have fv := fix v
  rw [(matching u).2 (Or.inl rfl)] at fu
  rw [(matching v).2 (Or.inr rfl)] at fv
  rw [fu, fv] at sum
  exact ⟨f u, f v, by simpa only [term, rU, rV, mul_assoc] using sum.symm⟩

/-- PBW expansion of a supported corner where the only compatible permutations
are a reduced word and its extension by one crossing. -/
theorem exists_two_corner_coefficients (hQ : KLRSymm Q) (s t : Seq ν) (l : List ℕ) (j : ℕ)
    (hl : IsReduced m l) (hjl : IsReduced m (j :: l))
    (matching : ∀ w : Perm (Fin m), w • s = t ↔ w = wordProd m l ∨ w = wordProd m (j :: l))
    (x : R) (hleft : e t * x = x) (hright : x * e s = x) :
    ∃ f g : P, x = pol f * (ψw l * e s) + pol g * (ψw (j :: l) * e s) := by
  exact exists_two_corner_coefficients_of_words hQ s t l (j :: l) hl hjl
    (exists_pbw_words_for_crossing hl j hjl).1 matching x hleft hright

/-- At the right extreme, arbitrary upper elements on the two arms have a
common full-joint lift when the only two permutations from the joint loading to
the fixed top are the red/black return and that return followed by the black
crossing. This condition holds in the four-position interval with two distinct
red labels and two equal black labels. Webster, arXiv:1309.3796v2, §6.1,
proof of Lemma 6.8 after (6.21), before the higher ideal. -/
theorem exists_equalBlack_corner_cycle_coefficient (hQ : KLRSymm Q) (s : Seq ν) (l : List ℕ)
    (b n : ℕ) (hp : b + 2 < m) (hl : IsReduced m l) (hjl : IsReduced m ((b + 1) :: l))
    (he : (wordProd m l • s).lbl ⟨b + 1, by omega⟩ = (wordProd m l • s).lbl ⟨b + 2, hp⟩)
    (hn : (wordProd m l • s).lbl ⟨b, by omega⟩ ≠ (wordProd m l • s).lbl ⟨b + 1, by omega⟩)
    (hw : Q ((wordProd m l • s).lbl ⟨b, by omega⟩) ((wordProd m l • s).lbl ⟨b + 1, by omega⟩) = X 1 ^ n)
    (matching : ∀ w : Perm (Fin m), w • (sadj m b • (wordProd m l • s)) = wordProd m l • s ↔
      w = wordProd m [b] ∨ w = wordProd m [b + 1, b]) (x y : R) :
    let r := wordProd m l • s
    let t := sadj m b • r
    let j := b + 1
    e r * x = x → x * e t = x → e r * y = y → y * e t = y →
    x * (ψw (b :: l) * e s) + y * (ψw (b :: j :: l) * e s) = 0 →
    ∃ c : R, c * e (sadj m j • t) = c ∧ c * (ψw [b, j] * e t) = -x ∧ c * (ψw [j] * e t) = y := by
  intro r t j hx hx' hy hy' rel
  have hb : b + 1 < m := by omega
  have hB : IsReduced m [b] := ⟨by simp [ValidWord, hb], by simp [length_sadj hb]⟩
  have asc : (sadj m b)⁻¹ ⟨b + 1, hb⟩ < (sadj m b)⁻¹ ⟨b + 2, hp⟩ := by
    rw [sadj_inv, sadj_apply_right hb, sadj_apply_of_ne _ (by simp) (by simp)]
    exact Fin.mk_lt_mk.2 (by omega)
  have hJB : IsReduced m [b + 1, b] :=
    ⟨by simp [ValidWord, hp, hb], by simp [length_sadj_mul_of_lt hp asc, length_sadj hb]⟩
  obtain ⟨f, g, xf⟩ := exists_two_corner_coefficients hQ t r [b] j hB hJB matching x hx hx'
  obtain ⟨h, i, yf⟩ := exists_two_corner_coefficients hQ t r [b] j hB hJB matching y hy hy'
  have fix := sadj_smul_eq_self hp he
  have tb : wordProd m (b :: l) • s = t := by rw [wordProd_cons, mul_smul]
  have tjb : wordProd m (b :: j :: l) • s = t := by rw [wordProd_cons, wordProd_cons, mul_smul, mul_smul, fix]
  have mul_arm (F : P) (up down : List ℕ) (correct : wordProd m down • s = t) :
      pol F * (ψw up * e t) * (ψw down * e s : R) = pol F * (ψw (up ++ down) * e s) := by
    have cut : (e t * (ψw down * e s) : R) = ψw down * e s := by
      simpa only [correct, map_one, one_mul] using e_mul_pol_ψw_e (Q := Q) (1 : P) down s
    rw [mul_assoc, mul_assoc _ (e t), cut, ψw_append, mul_assoc]
  rw [xf, yf, add_mul, add_mul, mul_arm _ _ _ tb, mul_arm _ _ _ tb,
    mul_arm _ _ _ tjb, mul_arm _ _ _ tjb, ← add_assoc] at rel
  obtain ⟨c, hc, cB, cD⟩ := exists_equalBlack_four_cycle_coefficient hQ s l b n hp hl hjl he hn hw f g h i rel
  exact ⟨c, hc, xf ▸ cB, yf ▸ cD⟩

end Categorification.KLR.KLRAlgebra
end
