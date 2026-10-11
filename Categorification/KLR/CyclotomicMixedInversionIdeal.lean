import Categorification.KLR.CyclotomicBalanced

noncomputable section
namespace Categorification.KLR.KLRAlgebra.MixedInversion
open TypeA
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}
local notation "R" => KLRAlgebra k Q ν

/-- The actual colour projector at a specified position. -/
def colourIdem (b : Fin (Multiset.card ν)) (i : I) : R :=
  eSum Q (Finset.univ.filter fun s : Seq ν => s.1 b = i)

theorem colourIdem_eq_zero_of_absent (b : Fin (Multiset.card ν)) (i : I) (hi : i ∉ ν) :
    (colourIdem b i : R) = 0 := by
  have hf : (Finset.univ.filter fun s : Seq ν => s.1 b = i) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro s _ hsi
    exact hi (hsi ▸ Seq.mem s b)
  simp only [colourIdem, eSum, hf, Finset.sum_empty]

theorem colourIdem_mul_e (b : Fin (Multiset.card ν)) (i : I) (s : Seq ν) :
    (colourIdem b i : R) * e s = if s.1 b = i then e s else 0 := by
  simp [colourIdem, eSum_mul_e]

theorem e_mul_colourIdem (b : Fin (Multiset.card ν)) (i : I) (s : Seq ν) :
    (e s : R) * colourIdem b i = if s.1 b = i then e s else 0 := by
  simp [colourIdem, e_mul_eSum]

theorem colourIdem_orthogonal (b : Fin (Multiset.card ν)) (i j : I) (hij : i ≠ j) :
    (colourIdem b i : R) * colourIdem b j = 0 := by
  apply ext_e
  intro s
  rw [mul_assoc, colourIdem_mul_e]
  by_cases hj : s.1 b = j
  · rw [ite_eq_left hj, colourIdem_mul_e, ite_eq_right (fun hi => hij (hi.symm.trans hj)), zero_mul]
  · rw [ite_eq_right hj, mul_zero, zero_mul]

theorem colourIdem_commute_of_diagonal (b : Fin (Multiset.card ν)) (i : I) (z : R)
    (hz : ∀ s : Seq ν, Commute z (e s)) : Commute (colourIdem b i) z := by
  unfold colourIdem eSum
  exact Commute.sum_left _ _ _ (fun s _ => (hz s).symm)

/-- A crossing palindrome with a diagonal middle preserves every sequence. -/
theorem palindrome_diagonal (ρ : List ℕ) (z : R)
    (hz : ∀ s : Seq ν, Commute z (e s)) :
    ∀ s : Seq ν, Commute (ψw ρ.reverse * z * ψw ρ) (e s) := by
  induction ρ generalizing z with
  | nil => simpa only [List.reverse_nil, ψw_nil, one_mul, mul_one] using hz
  | cons l ρ ih =>
    have hd : ∀ s : Seq ν, Commute ((ψ l : R) * z * ψ l) (e s) := by
      intro s
      change (_ * _) * e s = e s * (_ * _)
      calc
        _ = ψ l * (z * e (sadj (Multiset.card ν) l • s)) * ψ l := by
          rw [mul_assoc, ψ_mul_e]; simp only [mul_assoc]
        _ = ψ l * (e (sadj (Multiset.card ν) l • s) * z) * ψ l := by rw [(hz _).eq]
        _ = e s * (ψ l * z * ψ l) := by
          rw [← mul_assoc (ψ l), ψ_mul_e, sadj_smul_smul]
          simp only [mul_assoc]
    simpa only [List.reverse_cons, ψw_append, ψw_cons, ψw_nil, mul_one, mul_assoc]
      using ih (ψ l * z * ψ l) hd

/-- Off-diagonal corners kill the actual long cyclotomic correction. -/
theorem offDiagonal_palindrome (b : Fin (Multiset.card ν)) (i j : I) (hij : i ≠ j)
    (ρ : List ℕ) (a : I → Polynomial k) (p : Fin (Multiset.card ν)) :
    (colourIdem b i : R) * (ψw ρ.reverse * cycAt a p * ψw ρ) * colourIdem b j = 0 := by
  have hc := colourIdem_commute_of_diagonal (Q := Q) b i _
    (palindrome_diagonal ρ (cycAt a p) (fun s => cycAt_mul_e' a p s))
  rw [hc.eq, mul_assoc, colourIdem_orthogonal b i j hij, mul_zero]

/-- The last colour is central for both coefficient actions in the parabolic. -/
theorem colourIdem_commute_subR0 (n : ℕ) (hn : n + 1 = Multiset.card ν) (i : I)
    {z : R} (hz : z ∈ subR0 (k := k) (Q := Q) ν) :
    Commute (colourIdem ⟨n, by omega⟩ i) z := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    rcases hz with (⟨b, rfl⟩ | ⟨s, rfl⟩) | ⟨l, hl, rfl⟩
    · exact (x_mul_eSum b _).symm
    · change colourIdem _ i * e s = e s * colourIdem _ i
      rw [colourIdem_mul_e, e_mul_colourIdem]
    · change eSum Q _ * ψ l = ψ l * eSum Q _
      symm
      apply ψ_mul_eSum_of_stable
      intro s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sadj_smul_apply]
      rw [sadj_apply_of_ne _ (by change n ≠ l; omega) (by change n ≠ l + 1; omega)]
  | algebraMap c => exact (Algebra.commutes c _).symm
  | add x y _ _ hx hy => exact hx.add_right hy
  | mul x y _ _ hx hy => exact hx.mul_right hy

/-- Both noncommuting coefficient factors are retained in the vanishing. -/
theorem offDiagonal_parabolic_palindrome (n : ℕ) (hn : n + 1 = Multiset.card ν)
    (i j : I) (hij : i ≠ j) (u v : R)
    (hu : u ∈ subR0 (k := k) (Q := Q) ν)
    (hv : v ∈ subR0 (k := k) (Q := Q) ν)
    (ρ : List ℕ) (a : I → Polynomial k) (p : Fin (Multiset.card ν)) :
    (colourIdem ⟨n, by omega⟩ i : R) *
      (u * (ψw ρ.reverse * cycAt a p * ψw ρ) * v) * colourIdem ⟨n, by omega⟩ j = 0 := by
  have hi := (colourIdem_commute_subR0 n hn i hu).eq
  have hj := (colourIdem_commute_subR0 n hn j hv).eq
  calc
    _ = u * ((colourIdem ⟨n, by omega⟩ i : R) *
        (ψw ρ.reverse * cycAt a p * ψw ρ) * colourIdem ⟨n, by omega⟩ j) * v := by
      simp only [mul_assoc] at hi hj ⊢
      rw [← mul_assoc (colourIdem _ i) u, hi]
      simp only [mul_assoc]
      rw [← hj]
    _ = 0 := by rw [offDiagonal_palindrome _ i j hij, mul_zero, zero_mul]

/-- The actual two-sided corner projection, with no commutativity of coefficients. -/
def cut (b : Fin (Multiset.card ν)) (i j : I) : R →ₗ[k] R where
  toFun z := colourIdem b i * z * colourIdem b j
  map_add' z w := by simp only [mul_add, add_mul]
  map_smul' c z := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

variable (a : I → Polynomial k) (n : ℕ) (hn : n + 1 = Multiset.card ν) (i j : I)
local notation "lastPos" => (Fin.mk n (by omega : n < Multiset.card ν))
local notation "firstPos" => (Fin.mk 0 (by omega : 0 < Multiset.card ν))

/-- Relations imposed by the cyclotomic ideal on either coefficient factor. -/
def coefficientRelations : Submodule k R :=
  Submodule.span k {z | ∃ u v : R,
    (u ∈ subR0 (k := k) (Q := Q) ν ∨ v ∈ subR0 (k := k) (Q := Q) ν) ∧
    z = cut lastPos i j (u * cycAt a firstPos * v)}

theorem cut_cycL0 {z : R} (hz : z ∈ cycL0 a (by omega : 0 < Multiset.card ν)) :
    cut lastPos i j z ∈ coefficientRelations a n hn i j := by
  suffices h : ∀ r : R, cut lastPos i j (r * z) ∈ coefficientRelations a n hn i j by
    simpa only [one_mul] using h 1
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, hv, rfl⟩ := hz
    intro r
    exact Submodule.subset_span ⟨r, v, Or.inr hv, by rw [mul_assoc]⟩
  | zero => intro r; simp only [mul_zero, map_zero, Submodule.zero_mem]
  | add x y _ _ hx hy =>
    intro r
    rw [mul_add, map_add]
    exact Submodule.add_mem _ (hx r) (hy r)
  | smul c z _ hz =>
    intro r
    change cut lastPos i j (r * (c * z)) ∈ _
    rw [← mul_assoc]
    exact hz (r * c)

theorem tauRev_full : (tauRev n n : R) = ψw (List.range n).reverse := by
  unfold tauRev
  congr 1
  apply List.ext_getElem
  · simp
  · intro t ht ht'
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_range]

theorem tauRev_mem_subR1 {d : ℕ} (hd : d < n) :
    (tauRev n d : R) ∈ subR1 (k := k) (Q := Q) ν := by
  induction d with
  | zero => rw [tauRev_zero]; exact Subalgebra.one_mem _
  | succ d ih =>
    rw [tauRev_succ]
    exact Subalgebra.mul_mem _ (ih (by omega)) (ψ_mem_subR1 (by omega))

variable (hsym : KLRSymm Q) (hij : i ≠ j)

include hsym hij in
/-- After the two coefficient relations, the sole possible long term is zero. -/
theorem cut_mul_tauW (r : R) :
    cut lastPos i j (r * tauW a (by omega) n) ∈ coefficientRelations a n hn i j := by
  have hr : r ∈ spTauR (k := k) (Q := Q) ν n n := by
    rw [spTauR_eq_top hsym n hn]; trivial
  induction hr using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, d, hd, rfl⟩ := hz
    by_cases hdn : d < n
    · have hc := cycAt_zero_comm (ν := ν) a (h0 := by omega) (tauRev_mem_subR1 (Q := Q) n hdn)
      have he : (u * tauRev n d) * tauW a (by omega) n =
          u * cycAt a firstPos * (tauRev n d * tauProd n) := by
        simp only [tauW, mul_assoc]
        rw [← mul_assoc (tauRev n d), ← hc]
        simp only [mul_assoc]
      rw [he]
      exact Submodule.subset_span ⟨u, tauRev n d * tauProd n, Or.inl hu, rfl⟩
    · have he : d = n := by omega
      subst d
      have hz := offDiagonal_parabolic_palindrome n hn i j hij u 1 hu
        (Subalgebra.one_mem _) (List.range n) a firstPos
      simp only [mul_one] at hz
      change colourIdem lastPos i * ((u * tauRev n n) * (cycAt a firstPos * tauProd n)) * colourIdem lastPos j ∈ _
      rw [tauRev_full]
      simp only [tauProd, mul_assoc] at hz ⊢
      rw [hz]
      exact Submodule.zero_mem _
  | zero => simp only [zero_mul, map_zero, Submodule.zero_mem]
  | add x y _ _ hx hy =>
    rw [add_mul, map_add]
    exact Submodule.add_mem _ hx hy
  | smul c z _ hz =>
    rw [smul_mul_assoc, map_smul]
    exact Submodule.smul_mem _ c hz

include hsym hij in
/-- The difficult inclusion in KK (5.2), in the actual KLR algebra. -/
theorem cut_cyclotomicIdeal {z : R} (hz : z ∈ cycIdeal Q a ν) :
    cut lastPos i j z ∈ coefficientRelations a n hn i j := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1
    (cycIdeal_le a (by omega : 0 < Multiset.card ν) n hn hz)
  rw [map_add]
  refine Submodule.add_mem _ (cut_cycL0 a n hn i j hx) ?_
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
  exact cut_mul_tauW a n hn i j hsym hij r

include hsym hij in
/-- The full ideal in the off-diagonal corner is exactly the two coefficient ideals. -/
theorem coefficientRelations_eq_cyclotomicIdeal :
    coefficientRelations (Q := Q) a n hn i j =
      Submodule.map (cut lastPos i j) ((cycIdeal Q a ν).asIdeal.restrictScalars k) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro z ⟨u, v, _, rfl⟩
    apply Submodule.mem_map.2
    refine ⟨u * cycAt a firstPos * v, ?_, rfl⟩
    exact TwoSidedIdeal.mul_mem_right _ _ _
      (TwoSidedIdeal.mul_mem_left _ _ _ (cycAt_mem_cycIdeal a (by omega)))
  · rintro z hz
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hz
    exact cut_cyclotomicIdeal a n hn i j hsym hij hx

/-- The coefficient ideal with the last polynomial variable excluded. -/
def lowerCoefficientRelations : Submodule k R :=
  Submodule.span k {z | ∃ u v : R,
    (u ∈ penSub (k := k) (Q := Q) ν ∨ v ∈ penSub (k := k) (Q := Q) ν) ∧
    z = cut lastPos i j (u * cycAt a firstPos * v)}

theorem penSub_le_subR0 : penSub (k := k) (Q := Q) ν ≤ subR0 ν := by
  apply Algebra.adjoin_mono
  rintro z ((⟨t, _, rfl⟩ | ⟨s, rfl⟩) | ⟨l, hl, rfl⟩)
  · exact Or.inl (Or.inl ⟨t, rfl⟩)
  · exact Or.inl (Or.inr ⟨s, rfl⟩)
  · exact Or.inr ⟨l, hl, rfl⟩

theorem cut_left_coefficient (u v : R) (hu : u ∈ subR0 (k := k) (Q := Q) ν) :
    cut lastPos i j (u * cycAt a firstPos * v) ∈ lowerCoefficientRelations a n hn i j := by
  have hu' := subR0_le_penSpan (Q := Q) ν (by omega : 0 < Multiset.card ν) hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨d, c, hc, rfl⟩ := hz
    let X : R := x ⟨Multiset.card ν - 1, by omega⟩
    have hxc : Commute (X ^ d) c := (penSub_commute ν (by omega) hc).pow_left d
    have hxa : Commute (X ^ d) (cycAt a firstPos) :=
      (show Commute X (cycAt a firstPos) from (cycAt_mul_x a _ _).symm).pow_left d
    have he : (X ^ d * c) * cycAt a firstPos * v = c * cycAt a firstPos * (X ^ d * v) := by
      rw [hxc.eq, mul_assoc c, hxa.eq]
      simp only [mul_assoc]
    change cut lastPos i j ((X ^ d * c) * cycAt a firstPos * v) ∈ _
    rw [he]
    exact Submodule.subset_span ⟨c, X ^ d * v, Or.inl hc, rfl⟩
  | zero => simp only [zero_mul, map_zero, Submodule.zero_mem]
  | add x y _ _ hx hy =>
    rw [add_mul, add_mul, map_add]
    exact Submodule.add_mem _ hx hy
  | smul c z _ hz =>
    rw [smul_mul_assoc, smul_mul_assoc, map_smul]
    exact Submodule.smul_mem _ c hz

theorem cut_right_coefficient (u v : R) (hv : v ∈ subR0 (k := k) (Q := Q) ν) :
    cut lastPos i j (u * cycAt a firstPos * v) ∈ lowerCoefficientRelations a n hn i j := by
  have hv' := subR0_le_penSpan (Q := Q) ν (by omega : 0 < Multiset.card ν) hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨d, c, hc, rfl⟩ := hz
    let X : R := x ⟨Multiset.card ν - 1, by omega⟩
    have hxa : Commute (cycAt a firstPos) (X ^ d) :=
      (show Commute (cycAt a firstPos) X from cycAt_mul_x a _ _).pow_right d
    have he : u * cycAt a firstPos * (X ^ d * c) = (u * X ^ d) * cycAt a firstPos * c := by
      rw [mul_assoc u, ← mul_assoc (cycAt a firstPos), hxa.eq]
      simp only [mul_assoc]
    change cut lastPos i j (u * cycAt a firstPos * (X ^ d * c)) ∈ _
    rw [he]
    exact Submodule.subset_span ⟨u * X ^ d, c, Or.inr hc, rfl⟩
  | zero => simp only [mul_zero, map_zero, Submodule.zero_mem]
  | add x y _ _ hx hy =>
    rw [mul_add, map_add]
    exact Submodule.add_mem _ hx hy
  | smul c z _ hz =>
    rw [mul_smul_comm, map_smul]
    exact Submodule.smul_mem _ c hz

/-- Enlarging either coefficient algebra by its commuting last dot changes no relation. -/
theorem coefficientRelations_eq_lower :
    coefficientRelations (Q := Q) a n hn i j = lowerCoefficientRelations a n hn i j := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro z ⟨u, v, h, rfl⟩
    rcases h with hu | hv
    · exact cut_left_coefficient a n hn i j u v hu
    · exact cut_right_coefficient a n hn i j u v hv
  · refine Submodule.span_le.2 ?_
    rintro z ⟨u, v, h, rfl⟩
    exact Submodule.subset_span ⟨u, v, h.imp (fun hu => penSub_le_subR0 hu)
      (fun hv => penSub_le_subR0 hv), rfl⟩

include hsym hij in
/-- KK (5.2): the actual corner ideal equals the two lower coefficient relations. -/
theorem lowerCoefficientRelations_eq_cyclotomicIdeal :
    lowerCoefficientRelations (Q := Q) a n hn i j =
      Submodule.map (cut lastPos i j) ((cycIdeal Q a ν).asIdeal.restrictScalars k) := by
  rw [← coefficientRelations_eq_lower]
  exact coefficientRelations_eq_cyclotomicIdeal a n hn i j hsym hij

end Categorification.KLR.KLRAlgebra.MixedInversion
