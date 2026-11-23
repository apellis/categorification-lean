/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedViolatedQuotient
import Categorification.WeightedKLR.RedStrands.BraidedIdentity

set_option backward.isDefEq.respectTransparency false

/-!
# The bimodule `B_e` is `T^λ`

Webster's quotient bimodules `B_w` (arXiv:1309.3796v2, §6, before Lemma 6.5) are corners of the
quotient `A / J` of the braided Stendhal algebra by the ideal of violated idempotents
(`BraidedStendhalAlgebra.ViolQuotient`). For the identity, the corner at the idempotent of red
order `λ_1, …, λ_ℓ` is the tensor product algebra `T^λ` (Definitions 4.6 and 4.7), as rings.
This makes `B_w` a `T^{wλ}`–`T^λ` bimodule, and it is the case `w = e` of Lemma 6.5 for `B_w`.

The ring `B̃_e` is `T̃^λ` by `cornerEquivStendhal`, so it remains to compare the two ideals. An
element of `J` in the corner `B̃_e` is a combination of products through violated idempotents of
red order `λ_1, …, λ_ℓ`: a violated idempotent of any red order is pushed to this order one
crossing at a time (`redProj_mul_e_mem_violSpan`, from `redProj_mul_mul_e_mem`). Conversely the
violated idempotents of `T̃^λ` are images of violated idempotents of `A`.

## Main results

* `BraidedStendhalAlgebra.redProj_mul_e_mem_violSpan` : `e_κ a e(i)` with `e(i)` violated is a
  combination of products through violated idempotents of red order `κ`.
* `BraidedStendhalAlgebra.identityCornerEquiv` : `B̃_e ≃ T̃^λ` as rings.
* `BraidedStendhalAlgebra.val_mem_violIdeal_iff` : the two ideals correspond.
* `BraidedStendhalAlgebra.violCornerEquiv` : **`B_e ≃ T^λ`** as rings.
-/

namespace Categorification.Stendhal

open KLR TypeA Equiv MvPolynomial RedWord
open scoped List

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν

namespace BraidedStendhalAlgebra

theorem violSpan_mul_mem {κ : List (Fin ℓ)} {z : BraidedStendhalAlgebra k Q Λ ν}
    (hz : z ∈ violSpan k Q Λ ν κ) (w : BraidedStendhalAlgebra k Q Λ ν) :
    z * w ∈ violSpan k Q Λ ν κ := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, j, x, hj, hjκ, rfl⟩ := hz
    simpa only [mul_assoc] using mem_violSpan u (x * w) hj hjκ
  | zero => rw [zero_mul]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [add_mul]; exact add_mem hz hz'
  | smul r z _ hz => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hz

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q)

include hρ hQ in
/-- A violated idempotent `e(i)` of any red order, seen from the red order `κ₂`, is a
combination of products through violated idempotents of red order `κ₂`: by induction on the
number of pairs that the red order of `i` reads in the opposite order to `κ₂`, pushing one
crossing at a time. -/
theorem redProj_mul_e_mem_violSpan {κ₂ : List (Fin ℓ)} (n : ℕ) :
    ∀ κ : List (Fin ℓ), (inversions κ κ₂).card = n → ∀ i : Seq μ, IsViolated i →
      redWord i = κ → ∀ a : BraidedStendhalAlgebra k Q Λ ν,
        redProj k Q Λ ν κ₂ * a * ofKLR k Q Λ ν (KLRAlgebra.e i) ∈ violSpan k Q Λ ν κ₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro κ hn i hv hi a
  set E := ofKLR k Q Λ ν (KLRAlgebra.e i)
  have hPE : redProj k Q Λ ν κ * E = E := by
    rw [redProj_mul_e]; simp only [hi, ite_true, E]
  by_cases hne : κ = κ₂
  · subst hne
    simpa only [mul_one] using mem_violSpan (redProj k Q Λ ν κ * a) 1 hv hi
  by_cases h2 : ∃ j : Seq μ, redWord j = κ₂
  swap
  · push Not at h2
    rw [redProj_eq_zero h2, zero_mul, zero_mul]
    exact zero_mem _
  obtain ⟨j₂, hj₂⟩ := h2
  have hperm : κ.Perm κ₂ := hi ▸ hj₂ ▸ redWord_perm i j₂
  obtain ⟨L, c, d, M, hκ, hdc⟩ :=
    exists_adjacent_inversion (hi ▸ redWord_nodup i) hperm hne
  have hlt : (inversions (L ++ d :: c :: M) κ₂).card < n := by
    rw [← hn, hκ]
    exact card_inversions_swap_lt (hκ ▸ hi ▸ redWord_nodup i) (hj₂ ▸ redWord_nodup j₂) hdc
  obtain ⟨t, ht⟩ := (tensorMult_surjective_iff.1
    (tensorMult_bijective (Λ := Λ) hρ hQ hκ rfl hdc).2) a
  have he : redProj k Q Λ ν κ₂ * a * E =
      redProj k Q Λ ν κ₂ * a * redProj k Q Λ ν κ * E := by
    conv_lhs => rw [← hPE]
    simp only [mul_assoc]
  rw [he, ← ht]
  clear ht
  induction t using CornerTensor.induction_on with
  | tmul x w =>
    rw [CornerTensor.mult_tmul]
    have hpush := redProj_mul_mul_e_mem (Λ := Λ) hρ hQ (hi.trans hκ) hv
      (w * redProj k Q Λ ν κ)
    have key : ∀ z ∈ violSpan k Q Λ ν (L ++ d :: c :: M),
        redProj k Q Λ ν κ₂ * x * z ∈ violSpan k Q Λ ν κ₂ := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨u, j, w', hj, hjκ, rfl⟩ := hz
        have := violSpan_mul_mem (ih _ hlt _ rfl j hj hjκ (x * u)) w'
        simpa only [mul_assoc] using this
      | zero => rw [mul_zero]; exact zero_mem _
      | add z z' _ _ hz hz' => rw [mul_add]; exact add_mem hz hz'
      | smul r z _ hz => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hz
    have := key _ hpush
    simpa only [mul_assoc] using this
  | add s t hs ht => rw [map_add, add_mul]; exact add_mem hs ht

/-! ### The corner `B̃_e` as a ring -/

local notation "P" => redProj k Q Λ ν (List.finRange ℓ)

local notation "hP" => isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := ν)
  (List.finRange ℓ)

theorem toAllOrders_mem_corner_of_mem {x : BraidedStendhalAlgebra k Q Λ ν}
    (hx : x ∈ Subsemigroup.corner P) :
    toAllOrders k Q Λ ν x ∈
      Subsemigroup.corner (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) := by
  obtain ⟨r, rfl⟩ := hx
  exact ⟨toAllOrders k Q Λ ν r, by simp only [map_mul, redProj, toAllOrders_redIdem]⟩

variable (k Q Λ ν) in
/-- `toAllOrders` on the corner `B̃_e`, as a ring homomorphism to `T̃^λ`. -/
noncomputable def identityCornerHom : (hP).Corner →+* StendhalAlgebra k Q Λ ν where
  toFun x := ⟨toAllOrders k Q Λ ν x.1, toAllOrders_mem_corner_of_mem x.2⟩
  map_one' := Subtype.ext (by
    change toAllOrders k Q Λ ν P = StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
    exact toAllOrders_redIdem)
  map_mul' x y := Subtype.ext (map_mul (toAllOrders k Q Λ ν) x.1 y.1)
  map_zero' := Subtype.ext (map_zero (toAllOrders k Q Λ ν))
  map_add' x y := Subtype.ext (map_add (toAllOrders k Q Λ ν) x.1 y.1)

theorem identityCornerHom_val (x : (hP).Corner) :
    (identityCornerHom k Q Λ ν x).1 = toAllOrders k Q Λ ν x.1 := rfl

theorem mem_cornerSpace_of_mem {x : BraidedStendhalAlgebra k Q Λ ν}
    (hx : x ∈ Subsemigroup.corner P) :
    x ∈ cornerSpace k Q Λ ν (List.finRange ℓ) (List.finRange ℓ) := by
  obtain ⟨r, rfl⟩ := hx
  exact ⟨r, by simp [redProj, mul_assoc]⟩

theorem mem_corner_of_mem_cornerSpace {x : BraidedStendhalAlgebra k Q Λ ν}
    (hx : x ∈ cornerSpace k Q Λ ν (List.finRange ℓ) (List.finRange ℓ)) :
    x ∈ Subsemigroup.corner P := by
  obtain ⟨r, rfl⟩ := hx
  exact ⟨r, by simp [redProj, mul_assoc]⟩

include hρ hQ in
theorem identityCornerHom_bijective : Function.Bijective (identityCornerHom k Q Λ ν) := by
  refine ⟨fun x y hxy => ?_, fun s => ?_⟩
  · have h := congrArg Subtype.val hxy
    simp only [identityCornerHom_val] at h
    have hx := mem_cornerSpace_of_mem x.2
    have hy := mem_cornerSpace_of_mem y.2
    have : cornerEquivStendhal hQ ρ hρ ⟨x.1, hx⟩ = cornerEquivStendhal hQ ρ hρ ⟨y.1, hy⟩ :=
      Subtype.ext (by rw [cornerEquivStendhal_apply, cornerEquivStendhal_apply]; exact h)
    have h2 := congrArg Subtype.val ((cornerEquivStendhal hQ ρ hρ).injective this)
    exact Subtype.ext h2
  · set c := (cornerEquivStendhal hQ ρ hρ).symm s
    refine ⟨⟨c.1, mem_corner_of_mem_cornerSpace c.2⟩, Subtype.ext ?_⟩
    rw [identityCornerHom_val, ← cornerEquivStendhal_apply hQ ρ hρ c, LinearEquiv.apply_symm_apply]

/-- **`B̃_e ≃ T̃^λ` as rings** (arXiv:1309.3796v2, Definitions 4.5 and 6.3), for symmetric `Q`:
`toAllOrders` on the corner of the braided Stendhal algebra at the red order
`λ_1, …, λ_ℓ`. -/
noncomputable def identityCornerEquiv : (hP).Corner ≃+* StendhalAlgebra k Q Λ ν :=
  RingEquiv.ofBijective (identityCornerHom k Q Λ ν) (identityCornerHom_bijective hρ hQ)

theorem identityCornerEquiv_apply (x : (hP).Corner) :
    identityCornerEquiv hρ hQ x = identityCornerHom k Q Λ ν x := rfl

/-! ### The two ideals -/

/-- The corner element `e x e`. -/
noncomputable def cornerMk (x : BraidedStendhalAlgebra k Q Λ ν) : (hP).Corner :=
  ⟨P * x * P, x, rfl⟩

theorem cornerMk_val (x : BraidedStendhalAlgebra k Q Λ ν) :
    (cornerMk x).1 = P * x * P := rfl

theorem redProj_mul_e_of_eq {j : Seq μ} (hj : redWord j = List.finRange ℓ)
    (x : BraidedStendhalAlgebra k Q Λ ν) :
    P * (ofKLR k Q Λ ν (KLRAlgebra.e j) * x) = ofKLR k Q Λ ν (KLRAlgebra.e j) * x := by
  rw [← mul_assoc, redProj_mul_e]; simp [hj]

theorem e_mul_redProj_of_eq {j : Seq μ} (hj : redWord j = List.finRange ℓ)
    (x : BraidedStendhalAlgebra k Q Λ ν) :
    ofKLR k Q Λ ν (KLRAlgebra.e j) * (P * x) = ofKLR k Q Λ ν (KLRAlgebra.e j) * x := by
  rw [← mul_assoc, e_mul_redProj]; simp [hj]

theorem cornerMk_e_val {j : Seq μ} (hj : redWord j = List.finRange ℓ) :
    (cornerMk (ofKLR k Q Λ ν (KLRAlgebra.e j))).1 = ofKLR k Q Λ ν (KLRAlgebra.e j) := by
  have h1 : P * ofKLR k Q Λ ν (KLRAlgebra.e j) = ofKLR k Q Λ ν (KLRAlgebra.e j) := by
    rw [redProj_mul_e]; simp [hj]
  have h2 : ofKLR k Q Λ ν (KLRAlgebra.e j) * P = ofKLR k Q Λ ν (KLRAlgebra.e j) := by
    rw [e_mul_redProj]; simp [hj]
  rw [cornerMk_val, h1, h2]

theorem identityCornerHom_e {j : Seq μ} (hj : redWord j = List.finRange ℓ) :
    identityCornerHom k Q Λ ν (cornerMk (ofKLR k Q Λ ν (KLRAlgebra.e j))) =
      StendhalAlgebra.e j ((redWord_eq_finRange_iff j).1 hj) :=
  Subtype.ext (by rw [identityCornerHom_val, cornerMk_e_val hj]; exact toAllOrders_ofKLR _)

include hρ hQ in
/-- An element of `J` in the corner `B̃_e` maps into the violating ideal of `T̃^λ`. -/
theorem identityCornerHom_mem_violatedIdeal (z : BraidedStendhalAlgebra k Q Λ ν)
    (hz : z ∈ violIdeal k Q Λ ν) :
    identityCornerHom k Q Λ ν (cornerMk z) ∈ StendhalAlgebra.violatedIdeal k Q Λ ν := by
  set T := (StendhalAlgebra.violatedIdeal k Q Λ ν).comap (identityCornerHom k Q Λ ν)
  suffices h : cornerMk z ∈ T from (TwoSidedIdeal.mem_comap _).1 h
  -- products through violated idempotents of red order `λ_1, …, λ_ℓ`
  have hspan : ∀ y ∈ violSpan k Q Λ ν (List.finRange ℓ), ∀ b, cornerMk (y * b) ∈ T := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, j, w, hj, hjκ, rfl⟩ := hy
      intro b
      have hE : cornerMk (ofKLR k Q Λ ν (KLRAlgebra.e j)) ∈ T := by
        rw [TwoSidedIdeal.mem_comap, identityCornerHom_e hjκ]
        exact TwoSidedIdeal.subset_span ⟨j, _, hj, rfl⟩
      have heq : cornerMk (u * ofKLR k Q Λ ν (KLRAlgebra.e j) * w * b) =
          cornerMk u * cornerMk (ofKLR k Q Λ ν (KLRAlgebra.e j)) * cornerMk (w * b) := by
        apply Subtype.ext
        change P * _ * P = P * u * P * (cornerMk (ofKLR k Q Λ ν (KLRAlgebra.e j))).1 *
          (P * (w * b) * P)
        rw [cornerMk_e_val hjκ]
        simp only [mul_assoc, redProj_mul_e_of_eq hjκ, e_mul_redProj_of_eq hjκ]
      rw [heq]
      exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ hE)
    | zero =>
      intro b
      have : cornerMk (0 * b) = 0 := by
        apply Subtype.ext
        rw [cornerMk_val, zero_mul, mul_zero, zero_mul]
        rfl
      rw [this]; exact zero_mem T
    | add y y' _ _ hy hy' =>
      intro b
      have : cornerMk ((y + y') * b) = cornerMk (y * b) + cornerMk (y' * b) :=
        Subtype.ext (by rw [cornerMk_val, add_mul, mul_add, add_mul]; rfl)
      rw [this]; exact add_mem (hy b) (hy' b)
    | smul r y _ hy =>
      intro b
      have : cornerMk ((r • y) * b) = cornerMk (algebraMap k _ r) * cornerMk (y * b) := by
        apply Subtype.ext
        simp only [cornerMk_val, Algebra.smul_def]
        change _ = P * algebraMap k _ r * P * (P * (y * b) * P)
        have hc := Algebra.commutes r P
        simp only [mul_assoc] at hc ⊢
        rw [← mul_assoc P P, (hP).eq, ← mul_assoc (algebraMap k _ r) P, hc, mul_assoc P,
          ← mul_assoc P P, (hP).eq]
      rw [this]; exact TwoSidedIdeal.mul_mem_left _ _ _ (hy b)
  rw [violIdeal, TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨_, ⟨a, -, g, ⟨i, hi, rfl⟩, rfl⟩, b, -, rfl⟩ := hz
    have hmem := redProj_mul_e_mem_violSpan hρ hQ (κ₂ := List.finRange ℓ) _ _ rfl i hi rfl a
    have := hspan _ hmem b
    have heq : cornerMk (a * ofKLR k Q Λ ν (KLRAlgebra.e i) * b) =
        cornerMk (P * a * ofKLR k Q Λ ν (KLRAlgebra.e i) * b) :=
      Subtype.ext (by
        rw [cornerMk_val, cornerMk_val]
        simp only [mul_assoc]
        rw [← mul_assoc P P, (hP).eq])
    rw [heq]; exact this
  | zero =>
    have : cornerMk (0 : BraidedStendhalAlgebra k Q Λ ν) = 0 :=
      Subtype.ext (by rw [cornerMk_val, mul_zero, zero_mul]; rfl)
    rw [this]; exact zero_mem T
  | add z w _ _ hz hw =>
    have : cornerMk (z + w) = cornerMk z + cornerMk w :=
      Subtype.ext (by rw [cornerMk_val, mul_add, add_mul]; rfl)
    rw [this]; exact add_mem hz hw
  | neg z _ hz =>
    have : cornerMk (-z) = -cornerMk z := Subtype.ext (by rw [cornerMk_val, mul_neg, neg_mul]; rfl)
    rw [this]; exact neg_mem hz

variable (k Q Λ ν) in
/-- The elements of the corner `B̃_e` lying in `J`, a two-sided ideal of the corner. -/
noncomputable def cornerViolIdeal : TwoSidedIdeal (hP).Corner :=
  TwoSidedIdeal.mk' {y | y.1 ∈ violIdeal k Q Λ ν} (zero_mem (violIdeal k Q Λ ν))
    (fun {x y} hx hy => by
      show x.1 + y.1 ∈ violIdeal k Q Λ ν
      exact add_mem hx hy)
    (fun {x} hx => by
      show -x.1 ∈ violIdeal k Q Λ ν
      exact neg_mem hx)
    (fun {x y} hy => by
      show x.1 * y.1 ∈ violIdeal k Q Λ ν
      exact TwoSidedIdeal.mul_mem_left _ x.1 _ hy)
    (fun {x y} hx => by
      show x.1 * y.1 ∈ violIdeal k Q Λ ν
      exact TwoSidedIdeal.mul_mem_right _ _ y.1 hx)

theorem mem_cornerViolIdeal (y : (hP).Corner) :
    y ∈ cornerViolIdeal k Q Λ ν ↔ y.1 ∈ violIdeal k Q Λ ν := by
  rw [cornerViolIdeal, TwoSidedIdeal.mem_mk']; rfl

include hρ hQ in
/-- **The ideals correspond**: an element of the corner `B̃_e` lies in the ideal `J` of violated
idempotents iff its image in `T̃^λ` lies in the violating ideal. -/
theorem val_mem_violIdeal_iff (x : (hP).Corner) :
    x.1 ∈ violIdeal k Q Λ ν ↔
      identityCornerHom k Q Λ ν x ∈ StendhalAlgebra.violatedIdeal k Q Λ ν := by
  constructor
  · intro hx
    have hx' : cornerMk x.1 = x := by
      apply Subtype.ext
      obtain ⟨r, hr⟩ := x.2
      rw [cornerMk_val, ← hr]
      simp only [mul_assoc, (hP).eq]
      rw [← mul_assoc P P, (hP).eq]
    rw [← hx']
    exact identityCornerHom_mem_violatedIdeal hρ hQ _ hx
  · intro hx
    set e := identityCornerEquiv hρ hQ
    have hle : StendhalAlgebra.violatedIdeal k Q Λ ν ≤
        (cornerViolIdeal k Q Λ ν).comap e.symm := by
      rw [StendhalAlgebra.violatedIdeal, TwoSidedIdeal.span_le]
      rintro _ ⟨j, hj, hv, rfl⟩
      have hjκ := (redWord_eq_finRange_iff j).2 hj
      rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap]
      have : e.symm (StendhalAlgebra.e j hj) = cornerMk (ofKLR k Q Λ ν (KLRAlgebra.e j)) := by
        rw [RingEquiv.symm_apply_eq, identityCornerEquiv_apply, identityCornerHom_e hjκ]
      rw [this, mem_cornerViolIdeal, cornerMk_e_val hjκ]
      exact violMk_eq_zero_iff _ |>.1 (violMk_e hv)
    have := hle hx
    rw [TwoSidedIdeal.mem_comap, ← identityCornerEquiv_apply hρ hQ,
      RingEquiv.symm_apply_apply, mem_cornerViolIdeal] at this
    exact this

/-! ### `B_e ≃ T^λ` -/

variable (k Q Λ ν) in
theorem isIdempotentElem_violRedProj : IsIdempotentElem (violMk k Q Λ ν P) := (hP).map _

local notation "hPbar" => isIdempotentElem_violRedProj k Q Λ ν

variable (k Q Λ ν) in
/-- The quotient map on corners, `B̃_e → B_e`. -/
noncomputable def violCornerHom : (hP).Corner →+* (hPbar).Corner where
  toFun x := ⟨violMk k Q Λ ν x.1, by
    obtain ⟨r, hr⟩ := x.2
    exact ⟨violMk k Q Λ ν r, by rw [← hr]; simp only [map_mul]⟩⟩
  map_one' := rfl
  map_mul' x y := Subtype.ext (map_mul (violMk k Q Λ ν) x.1 y.1)
  map_zero' := Subtype.ext (map_zero (violMk k Q Λ ν))
  map_add' x y := Subtype.ext (map_add (violMk k Q Λ ν) x.1 y.1)

theorem violCornerHom_val (x : (hP).Corner) :
    (violCornerHom k Q Λ ν x).1 = violMk k Q Λ ν x.1 := rfl

theorem violCornerHom_surjective : Function.Surjective (violCornerHom k Q Λ ν) := by
  rintro ⟨_, r, rfl⟩
  obtain ⟨r, rfl⟩ := violMk_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν) r
  exact ⟨cornerMk r, Subtype.ext (by simp only [violCornerHom_val, cornerMk_val, map_mul])⟩

variable (k Q Λ ν) in
/-- The composite `B̃_e → T̃^λ → T^λ`. -/
noncomputable def identityCornerToTensor : (hP).Corner →+* TensorProductAlgebra k Q Λ ν :=
  (TensorProductAlgebra.mk Q Λ ν).toRingHom.comp (identityCornerHom k Q Λ ν)

include hρ hQ in
theorem identityCornerToTensor_surjective :
    Function.Surjective (identityCornerToTensor k Q Λ ν) :=
  (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mk'_surjective.comp
    (identityCornerHom_bijective hρ hQ).2

include hρ hQ in
theorem ker_violCornerHom :
    RingCon.ker (violCornerHom k Q Λ ν) =
      (RingCon.ker (identityCornerToTensor k Q Λ ν)).comap (RingEquiv.refl _) := by
  ext x y
  rw [RingCon.comap_rel, RingCon.ker_apply, RingCon.ker_apply]
  change _ ↔ ((identityCornerHom k Q Λ ν x :
    (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.Quotient) = identityCornerHom k Q Λ ν y)
  rw [RingCon.eq, TwoSidedIdeal.rel_iff, ← map_sub, ← val_mem_violIdeal_iff hρ hQ,
    ← violMk_eq_zero_iff]
  constructor
  · intro h
    have := congrArg Subtype.val h
    simp only [violCornerHom_val] at this
    change violMk k Q Λ ν (x.1 - y.1) = 0
    rw [map_sub, this, sub_self]
  · intro h
    apply Subtype.ext
    simp only [violCornerHom_val]
    change violMk k Q Λ ν (x.1 - y.1) = 0 at h
    rwa [map_sub, sub_eq_zero] at h

/-- **`B_e ≃ T^λ` as rings** (arXiv:1309.3796v2, §6, before Lemma 6.5; Definitions 4.6 and 4.7),
for symmetric `Q`: the corner of the quotient by violated idempotents at the red order
`λ_1, …, λ_ℓ` is Webster's tensor product algebra. -/
noncomputable def violCornerEquiv : (hPbar).Corner ≃+* TensorProductAlgebra k Q Λ ν :=
  (RingCon.quotientKerEquivOfSurjective _ violCornerHom_surjective).symm.trans
    ((RingCon.congr (RingEquiv.refl _) (ker_violCornerHom hρ hQ)).trans
      (RingCon.quotientKerEquivOfSurjective _ (identityCornerToTensor_surjective hρ hQ)))

/-- `violCornerEquiv` sends the class of `x ∈ B̃_e` to the class of its image in `T̃^λ`. -/
theorem violCornerEquiv_violCornerHom (x : (hP).Corner) :
    violCornerEquiv hρ hQ (violCornerHom k Q Λ ν x) =
      TensorProductAlgebra.mk Q Λ ν (identityCornerHom k Q Λ ν x) := by
  rw [violCornerEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    (RingEquiv.symm_apply_eq _).2 (RingCon.quotientKerEquivOfSurjective_mk _ _ x).symm,
    RingCon.congr_mk, RingCon.quotientKerEquivOfSurjective_mk]
  rfl

end BraidedStendhalAlgebra

end Categorification.Stendhal
