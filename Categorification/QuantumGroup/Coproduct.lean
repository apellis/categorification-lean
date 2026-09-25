/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.QBinomial

/-!
# Coassociativity of `r` and the coproduct of divided powers

Lusztig, *Introduction to quantum groups*, 1.2.2 (the remark that `r` is coassociative:
`(r ⊗ 1) r = (1 ⊗ r) r`) and 1.4.2 (`r(θ_i^{(a)}) = Σ_{t+t'=a} v_i^{tt'} θ_i^{(t)} ⊗ θ_i^{(t')}`);
Khovanov–Lauda, arXiv:0803.4121v2, §3.1 (`'f` is a twisted bialgebra with comultiplication
`r`, matching `[Res]`).

## The triple tensor product

`'f ⊗ 'f ⊗ 'f` carries the twisted multiplication
`(x₁ ⊗ x₂ ⊗ x₃)(y₁ ⊗ y₂ ⊗ y₃) = v^{|x₂|·|y₁| + |x₃|·|y₁| + |x₃|·|y₂|} x₁y₁ ⊗ x₂y₂ ⊗ x₃y₃`
(Lusztig 1.2.2 iterated). We realise it as the twisted monoid algebra `PreF.TwCube` of
`FreeMonoid I × FreeMonoid I × FreeMonoid I`. The twisted monoid algebra maps
`PreF.inclL : 'f ⊗ 'f → 'f ⊗ 'f ⊗ 'f`, `x ⊗ y ↦ x ⊗ y ⊗ 1`, and
`PreF.inclR : 'f ⊗ 'f → 'f ⊗ 'f ⊗ 'f`, `x ⊗ y ↦ 1 ⊗ x ⊗ y`, are algebra homomorphisms, and

* `PreF.rTensorId` (`= r ⊗ 1`) is the linear map `x ⊗ y ↦ r(x) ⊗ y` (`PreF.rTensorId_tw`);
* `PreF.idTensorR` (`= 1 ⊗ r`) is the linear map `x ⊗ y ↦ x ⊗ r(y)` (`PreF.idTensorR_tw`).

## Main results

* `PreF.coassoc` — `(r ⊗ 1) ∘ r = (1 ⊗ r) ∘ r`; both equal the algebra homomorphism
  `PreF.r3` with `θ_i ↦ θ_i ⊗ 1 ⊗ 1 + 1 ⊗ θ_i ⊗ 1 + 1 ⊗ 1 ⊗ θ_i`
  (`PreF.rTensorId_r`, `PreF.idTensorR_r`);
* `PreF.r_θ_pow` — `r(θ_i^a) = Σ_{t+t'=a} v_i^{tt'} [a choose t']_{v_i} θ_i^t ⊗ θ_i^{t'}`
  (the quantum binomial theorem for `θ_i ⊗ 1` and `1 ⊗ θ_i`, which `v_i²`-commute);
* `PreF.r_dpow` — **Lusztig 1.4.2**: `r(θ_i^{(a)}) = Σ_{t+t'=a} v_i^{tt'} θ_i^{(t)} ⊗ θ_i^{(t')}`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open Finset
open TwistedMonoidAlgebra (single single_mul_single)
open scoped Classical

/-! ### Algebra maps between twisted monoid algebras -/

namespace TwistedMonoidAlgebra

variable {K : Type*} [CommRing K] {M M' : Type*} [Monoid M] [Monoid M']
  {σ : TwistCocycle K M} {σ' : TwistCocycle K M'}

/-- The algebra homomorphism `K^σ[M] → K^{σ'}[M']`, `[m] ↦ [φ m]`, for a monoid homomorphism
`φ` compatible with the cocycles. -/
def mapDomainAlgHom (φ : M →* M') (h : ∀ a b, σ'.τ (φ a) (φ b) = σ.τ a b) :
    TwistedMonoidAlgebra σ →ₐ[K] TwistedMonoidAlgebra σ' :=
  AlgHom.ofLinearMap (lift fun m => single (φ m) 1)
    (by rw [one_def, lift_single, one_smul, map_one]; rfl)
    (fun x y => by
      induction x using induction_linear with
      | zero => simp only [zero_mul, map_zero]
      | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
      | single a r =>
        induction y using induction_linear with
        | zero => simp only [mul_zero, map_zero]
        | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
        | single b s =>
          rw [single_mul_single, lift_single, lift_single, lift_single, smul_mul_smul_comm,
            single_mul_single, map_mul, h, smul_single, smul_single]
          congr 1
          ring)

theorem mapDomainAlgHom_single (φ : M →* M') (h : ∀ a b, σ'.τ (φ a) (φ b) = σ.τ a b)
    (m : M) (r : K) : mapDomainAlgHom φ h (single m r) = single (φ m) r := by
  change lift (fun m => single (φ m) 1) (single m r) = _
  rw [lift_single, smul_single, mul_one]

end TwistedMonoidAlgebra

namespace PreF

variable {I : Type*} {K : Type*} [CommRing K] {dot : I → I → ℤ} {v : Kˣ}

/-! ### The triple tensor product -/

/-- The 2-cocycle `(a, b) ↦ v^{|a₂|·|b₁| + |a₃|·|b₁| + |a₃|·|b₂|}` defining the twisted
multiplication on `'f ⊗ 'f ⊗ 'f`. -/
def cubeCocycle (K : Type*) [CommRing K] (I : Type*) (dot : I → I → ℤ) (v : Kˣ) :
    TwistCocycle K (FreeMonoid I × FreeMonoid I × FreeMonoid I) where
  τ a b := ((v ^ (wdot dot (wt a.2.1) (wt b.1) + wdot dot (wt a.2.2) (wt b.1) +
    wdot dot (wt a.2.2) (wt b.2.1)) : Kˣ) : K)
  one_left a := by simp
  one_right a := by simp
  assoc a b c := by
    simp only [Prod.fst_mul, Prod.snd_mul, wt_mul, wdot_add_left, wdot_add_right]
    rw [← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add]
    congr 2
    ring

/-- The twisted triple tensor product `'f ⊗ 'f ⊗ 'f`; `single (a, b, c) 1 = a ⊗ b ⊗ c`. -/
abbrev TwCube (K : Type*) [CommRing K] (I : Type*) (dot : I → I → ℤ) (v : Kˣ) :=
  TwistedMonoidAlgebra (cubeCocycle K I dot v)

theorem twCube_single_mul_single (a b : FreeMonoid I × FreeMonoid I × FreeMonoid I) (r s : K) :
    (single a r : TwCube K I dot v) * single b s =
      single (a * b) (((v ^ (wdot dot (wt a.2.1) (wt b.1) + wdot dot (wt a.2.2) (wt b.1) +
        wdot dot (wt a.2.2) (wt b.2.1)) : Kˣ) : K) * r * s) :=
  single_mul_single a b r s

/-- `(u, w) ↦ (u, w, 1)`. -/
def pairL : FreeMonoid I × FreeMonoid I →* FreeMonoid I × FreeMonoid I × FreeMonoid I where
  toFun p := (p.1, p.2, 1)
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

/-- `(u, w) ↦ (1, u, w)`. -/
def pairR : FreeMonoid I × FreeMonoid I →* FreeMonoid I × FreeMonoid I × FreeMonoid I where
  toFun p := (1, p.1, p.2)
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

variable (dot v) in
/-- The algebra homomorphism `'f ⊗ 'f → 'f ⊗ 'f ⊗ 'f`, `x ⊗ y ↦ x ⊗ y ⊗ 1`. -/
def inclL : TwSq K I dot v →ₐ[K] TwCube K I dot v :=
  TwistedMonoidAlgebra.mapDomainAlgHom pairL fun a b => by simp [cubeCocycle, tensorCocycle, pairL]

variable (dot v) in
/-- The algebra homomorphism `'f ⊗ 'f → 'f ⊗ 'f ⊗ 'f`, `x ⊗ y ↦ 1 ⊗ x ⊗ y`. -/
def inclR : TwSq K I dot v →ₐ[K] TwCube K I dot v :=
  TwistedMonoidAlgebra.mapDomainAlgHom pairR fun a b => by simp [cubeCocycle, tensorCocycle, pairR]

theorem inclL_single (u w : FreeMonoid I) (r : K) :
    inclL dot v (single (u, w) r : TwSq K I dot v) = single (u, w, 1) r :=
  TwistedMonoidAlgebra.mapDomainAlgHom_single _ _ _ _

theorem inclR_single (u w : FreeMonoid I) (r : K) :
    inclR dot v (single (u, w) r : TwSq K I dot v) = single (1, u, w) r :=
  TwistedMonoidAlgebra.mapDomainAlgHom_single _ _ _ _

variable (dot v) in
/-- `x ↦ x ⊗ 1 ⊗ 1`. -/
def in1 : PreF K I →ₐ[K] TwCube K I dot v := (inclL dot v).comp (inl dot v)

variable (dot v) in
/-- `x ↦ 1 ⊗ x ⊗ 1`. -/
def in2 : PreF K I →ₐ[K] TwCube K I dot v := (inclL dot v).comp (inr dot v)

variable (dot v) in
/-- `x ↦ 1 ⊗ 1 ⊗ x`. -/
def in3 : PreF K I →ₐ[K] TwCube K I dot v := (inclR dot v).comp (inr dot v)

theorem in1_word (w : FreeMonoid I) : in1 dot v (word w : PreF K I) = single (w, 1, 1) 1 := by
  simp [in1, inl_word, inclL_single]

theorem in2_word (w : FreeMonoid I) : in2 dot v (word w : PreF K I) = single (1, w, 1) 1 := by
  simp [in2, inr_word, inclL_single]

theorem in3_word (w : FreeMonoid I) : in3 dot v (word w : PreF K I) = single (1, 1, w) 1 := by
  simp [in3, inr_word, inclR_single]

theorem inclR_inl (x : PreF K I) : inclR dot v (inl dot v x) = in2 dot v x := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | smul_word w r => rw [map_smul, map_smul, map_smul, inl_word, inclR_single, in2_word]

variable (dot v) in
/-- `r ⊗ 1 : 'f ⊗ 'f → 'f ⊗ 'f ⊗ 'f`, `x ⊗ y ↦ r(x) ⊗ y`. -/
def rTensorId : TwSq K I dot v →ₗ[K] TwCube K I dot v :=
  TwistedMonoidAlgebra.lift fun p => inclL dot v (r dot v (word p.1)) * in3 dot v (word p.2)

variable (dot v) in
/-- `1 ⊗ r : 'f ⊗ 'f → 'f ⊗ 'f ⊗ 'f`, `x ⊗ y ↦ x ⊗ r(y)`. -/
def idTensorR : TwSq K I dot v →ₗ[K] TwCube K I dot v :=
  TwistedMonoidAlgebra.lift fun p => in1 dot v (word p.1) * inclR dot v (r dot v (word p.2))

theorem rTensorId_single (c e : FreeMonoid I) (s : K) :
    rTensorId dot v (single (c, e) s : TwSq K I dot v) =
      s • (inclL dot v (r dot v (word c)) * in3 dot v (word e)) :=
  TwistedMonoidAlgebra.lift_single _ _ _

theorem idTensorR_single (c e : FreeMonoid I) (s : K) :
    idTensorR dot v (single (c, e) s : TwSq K I dot v) =
      s • (in1 dot v (word c) * inclR dot v (r dot v (word e))) :=
  TwistedMonoidAlgebra.lift_single _ _ _

/-- `(r ⊗ 1)(x ⊗ y) = r(x) ⊗ y`, where `X ⊗ y = inclL X · (1 ⊗ 1 ⊗ y)`. -/
theorem rTensorId_tw (x y : PreF K I) :
    rTensorId dot v (tw dot v x y) = inclL dot v (r dot v x) * in3 dot v y := by
  induction x using induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [tw_add_left, map_add, hx, hx', map_add, map_add, add_mul]
  | smul_word u r =>
    induction y using induction_linear with
    | zero => simp
    | add y y' hy hy' => rw [tw_add_right, map_add, hy, hy', map_add, mul_add]
    | smul_word w s =>
      rw [tw_smul_left, tw_smul_right, tw_word, map_smul, map_smul, rTensorId_single,
        map_smul, map_smul, map_smul, smul_mul_smul_comm, smul_smul, one_smul, mul_comm]

/-- `(1 ⊗ r)(x ⊗ y) = x ⊗ r(y)`, where `x ⊗ Y = (x ⊗ 1 ⊗ 1) · inclR Y`. -/
theorem idTensorR_tw (x y : PreF K I) :
    idTensorR dot v (tw dot v x y) = in1 dot v x * inclR dot v (r dot v y) := by
  induction x using induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [tw_add_left, map_add, hx, hx', map_add, add_mul]
  | smul_word u r =>
    induction y using induction_linear with
    | zero => simp
    | add y y' hy hy' => rw [tw_add_right, map_add, hy, hy', map_add, map_add, mul_add]
    | smul_word w s =>
      rw [tw_smul_left, tw_smul_right, tw_word, map_smul, map_smul, idTensorR_single,
        map_smul, map_smul, map_smul, smul_mul_smul_comm, smul_smul, one_smul, mul_comm]

variable (dot v) in
/-- The iterated coproduct: the algebra homomorphism `'f → 'f ⊗ 'f ⊗ 'f` with
`θ_i ↦ θ_i ⊗ 1 ⊗ 1 + 1 ⊗ θ_i ⊗ 1 + 1 ⊗ 1 ⊗ θ_i`. -/
def r3 : PreF K I →ₐ[K] TwCube K I dot v :=
  MonoidAlgebra.lift K (FreeMonoid I) (TwCube K I dot v)
    (FreeMonoid.lift fun i => in1 dot v (θ i) + in2 dot v (θ i) + in3 dot v (θ i))

theorem word_of (j : I) : (word (FreeMonoid.of j) : PreF K I) = θ j := rfl

theorem r3_θ (i : I) :
    r3 dot v (θ i : PreF K I) = in1 dot v (θ i) + in2 dot v (θ i) + in3 dot v (θ i) := by
  simp [r3, θ, word, MonoidAlgebra.lift_single]

theorem r3_word_mul_of (w : FreeMonoid I) (j : I) :
    r3 dot v (word (w * FreeMonoid.of j) : PreF K I) =
      r3 dot v (word w) * (in1 dot v (θ j) + in2 dot v (θ j) + in3 dot v (θ j)) := by
  rw [word_mul, map_mul, word_of, r3_θ]

theorem r3_word_of_mul (j : I) (w : FreeMonoid I) :
    r3 dot v (word (FreeMonoid.of j * w) : PreF K I) =
      (in1 dot v (θ j) + in2 dot v (θ j) + in3 dot v (θ j)) * r3 dot v (word w) := by
  rw [word_mul, map_mul, word_of, r3_θ]

/-! #### `(r ⊗ 1) r = r3` -/

theorem single_mul_inl_θ (c e : FreeMonoid I) (s : K) (j : I) :
    (single (c, e) s : TwSq K I dot v) * inl dot v (θ j) =
      single (c * FreeMonoid.of j, e) (((v ^ wdot dot (wt e) {j} : Kˣ) : K) * s) := by
  rw [θ, inl_word, twSq_single_mul_single]
  simp

theorem single_mul_inr_θ (c e : FreeMonoid I) (s : K) (j : I) :
    (single (c, e) s : TwSq K I dot v) * inr dot v (θ j) = single (c, e * FreeMonoid.of j) s := by
  rw [θ, inr_word, twSq_single_mul_single]
  simp

theorem in3_word_mul_in1 (e : FreeMonoid I) (j : I) :
    in3 dot v (word e : PreF K I) * in1 dot v (θ j) =
      ((v ^ wdot dot (wt e) {j} : Kˣ) : K) • (in1 dot v (θ j) * in3 dot v (word e)) := by
  rw [θ, in3_word, in1_word, twCube_single_mul_single, twCube_single_mul_single,
    TwistedMonoidAlgebra.smul_single]
  simp

theorem in3_word_mul_in2 (e : FreeMonoid I) (j : I) :
    in3 dot v (word e : PreF K I) * in2 dot v (θ j) =
      ((v ^ wdot dot (wt e) {j} : Kˣ) : K) • (in2 dot v (θ j) * in3 dot v (word e)) := by
  rw [θ, in3_word, in2_word, twCube_single_mul_single, twCube_single_mul_single,
    TwistedMonoidAlgebra.smul_single]
  simp

theorem inclL_inl (x : PreF K I) : inclL dot v (inl dot v x) = in1 dot v x := rfl

theorem inclL_inr (x : PreF K I) : inclL dot v (inr dot v x) = in2 dot v x := rfl

theorem inclR_inr (x : PreF K I) : inclR dot v (inr dot v x) = in3 dot v x := rfl

theorem rTensorId_mul_gen (Y : TwSq K I dot v) (j : I) :
    rTensorId dot v (Y * (inl dot v (θ j) + inr dot v (θ j))) =
      rTensorId dot v Y * (in1 dot v (θ j) + in2 dot v (θ j) + in3 dot v (θ j)) := by
  induction Y using TwistedMonoidAlgebra.induction_linear with
  | zero => simp
  | add Y Y' hY hY' => rw [add_mul, map_add, hY, hY', map_add, add_mul]
  | single p s =>
    obtain ⟨c, e⟩ := p
    have h12 : in3 dot v (word e : PreF K I) * (in1 dot v (θ j) + in2 dot v (θ j)) =
        ((v ^ wdot dot (wt e) {j} : Kˣ) : K) • ((in1 dot v (θ j) + in2 dot v (θ j)) *
          in3 dot v (word e)) := by
      rw [mul_add, in3_word_mul_in1, in3_word_mul_in2, add_mul, smul_add]
    rw [mul_add, map_add, single_mul_inl_θ, single_mul_inr_θ, rTensorId_single,
      rTensorId_single, rTensorId_single, word_mul, word_mul, map_mul, map_mul, word_of, r_θ,
      map_mul, map_add, inclL_inl, inclL_inr]
    rw [smul_mul_assoc,
      mul_add (inclL dot v (r dot v (word c)) * in3 dot v (word e)),
      mul_assoc (inclL dot v (r dot v (word c))) (in3 dot v (word e)), h12, mul_smul_comm,
      mul_assoc (inclL dot v (r dot v (word c))) (in3 dot v (word e)) (in3 dot v (θ j)),
      smul_add, smul_smul,
      ← mul_assoc (inclL dot v (r dot v (word c))) (in1 dot v (θ j) + in2 dot v (θ j)),
      mul_comm s]

theorem in2_θ_mul_in1 (j : I) (a : FreeMonoid I) :
    in2 dot v (θ j) * in1 dot v (word a : PreF K I) =
      ((v ^ wdot dot {j} (wt a) : Kˣ) : K) • (in1 dot v (word a) * in2 dot v (θ j)) := by
  rw [θ, in2_word, in1_word, twCube_single_mul_single, twCube_single_mul_single,
    TwistedMonoidAlgebra.smul_single]
  simp

theorem in3_θ_mul_in1 (j : I) (a : FreeMonoid I) :
    in3 dot v (θ j) * in1 dot v (word a : PreF K I) =
      ((v ^ wdot dot {j} (wt a) : Kˣ) : K) • (in1 dot v (word a) * in3 dot v (θ j)) := by
  rw [θ, in3_word, in1_word, twCube_single_mul_single, twCube_single_mul_single,
    TwistedMonoidAlgebra.smul_single]
  simp

theorem idTensorR_gen_mul (j : I) (Y : TwSq K I dot v) :
    idTensorR dot v ((inl dot v (θ j) + inr dot v (θ j)) * Y) =
      (in1 dot v (θ j) + in2 dot v (θ j) + in3 dot v (θ j)) * idTensorR dot v Y := by
  induction Y using TwistedMonoidAlgebra.induction_linear with
  | zero => simp
  | add Y Y' hY hY' => rw [mul_add, map_add, hY, hY', map_add, mul_add]
  | single p s =>
    obtain ⟨a, b⟩ := p
    have h23 : (in2 dot v (θ j) + in3 dot v (θ j)) * in1 dot v (word a : PreF K I) =
        ((v ^ wdot dot {j} (wt a) : Kˣ) : K) • (in1 dot v (word a) *
          (in2 dot v (θ j) + in3 dot v (θ j))) := by
      rw [add_mul, in2_θ_mul_in1, in3_θ_mul_in1, mul_add, smul_add]
    rw [add_mul, map_add, inl_θ_mul_single, inr_θ_mul_single, idTensorR_single,
      idTensorR_single, idTensorR_single, word_mul, word_mul, map_mul, map_mul, word_of, r_θ,
      map_mul, map_add, inclR_inl, inclR_inr, add_assoc, mul_smul_comm, add_mul, mul_assoc,
      ← add_mul (in2 dot v (θ j)) (in3 dot v (θ j)), add_mul (in1 dot v (θ j)), smul_add,
      ← mul_assoc (in2 dot v (θ j) + in3 dot v (θ j)), h23, smul_mul_assoc, smul_smul, mul_comm s,
      mul_assoc (in1 dot v (word a))]

theorem rTensorId_r_ofList (l : List I) :
    rTensorId dot v (r dot v (word (FreeMonoid.ofList l) : PreF K I)) =
      r3 dot v (word (FreeMonoid.ofList l)) := by
  induction l using List.reverseRecOn with
  | nil =>
    rw [FreeMonoid.ofList_nil, word_one, map_one (r dot v), map_one (r3 dot v),
      TwistedMonoidAlgebra.one_def, rTensorId_single]
    simp only [one_smul, word_one, map_one, Prod.fst_one, Prod.snd_one]
    exact mul_one _
  | append_singleton l j ih =>
    rw [FreeMonoid.ofList_append, FreeMonoid.ofList_singleton, word_mul, map_mul, word_of, r_θ,
      rTensorId_mul_gen, ih, ← r3_word_mul_of, word_mul, word_of]

theorem rTensorId_r_word (w : FreeMonoid I) :
    rTensorId dot v (r dot v (word w : PreF K I)) = r3 dot v (word w) :=
  rTensorId_r_ofList w.toList

theorem idTensorR_r_word (w : FreeMonoid I) :
    idTensorR dot v (r dot v (word w : PreF K I)) = r3 dot v (word w) := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    rw [word_one, map_one (r dot v), map_one (r3 dot v), TwistedMonoidAlgebra.one_def,
      idTensorR_single]
    simp only [one_smul, word_one, map_one, Prod.fst_one, Prod.snd_one]
    exact mul_one _
  | mul_of j w ih => rw [r_word_of_mul, idTensorR_gen_mul, ih, r3_word_of_mul]

/-- `(r ⊗ 1)(r y)` is the iterated coproduct `r3 y`. -/
theorem rTensorId_r (y : PreF K I) : rTensorId dot v (r dot v y) = r3 dot v y := by
  have : rTensorId dot v ∘ₗ (r dot v).toLinearMap = (r3 dot v).toLinearMap :=
    lhom_ext fun w => rTensorId_r_word w
  exact LinearMap.congr_fun this y

/-- `(1 ⊗ r)(r y)` is the iterated coproduct `r3 y`. -/
theorem idTensorR_r (y : PreF K I) : idTensorR dot v (r dot v y) = r3 dot v y := by
  have : idTensorR dot v ∘ₗ (r dot v).toLinearMap = (r3 dot v).toLinearMap :=
    lhom_ext fun w => idTensorR_r_word w
  exact LinearMap.congr_fun this y

/-- **Coassociativity of `r`** (Lusztig 1.2.2): `(r ⊗ 1) ∘ r = (1 ⊗ r) ∘ r` on `'f`. -/
theorem coassoc (y : PreF K I) : rTensorId dot v (r dot v y) = idTensorR dot v (r dot v y) := by
  rw [rTensorId_r, idTensorR_r]

/-! ### `r` on powers and divided powers of `θ_i` -/

theorem inr_θ_mul_inl_θ (i : I) :
    inr dot v (θ i) * inl dot v (θ i : PreF K I) =
      ((v ^ dot i i : Kˣ) : K) • (inl dot v (θ i) * inr dot v (θ i)) :=
  inr_θ_mul_inl i (dot i i) (θ i) (word_mem_supp (by simp))

/-- `r(θ_i^a) = Σ_{t+t'=a} v_i^{tt'} [a choose t']_{v_i} θ_i^t ⊗ θ_i^{t'}`, for
`i · i = 2k` and `v_i = v^k`. -/
theorem r_θ_pow (i : I) {k : ℤ} (hk : dot i i = 2 * k) (a : ℕ) :
    r dot v ((θ i : PreF K I) ^ a) = ∑ p ∈ antidiagonal a,
      qbinomCoef (v ^ k) p.1 p.2 • tw dot v (θ i ^ p.1) (θ i ^ p.2) := by
  have h : inr dot v (θ i) * inl dot v (θ i : PreF K I) =
      (((v ^ k) ^ (2 : ℤ) : Kˣ) : K) • (inl dot v (θ i) * inr dot v (θ i)) := by
    rw [inr_θ_mul_inl_θ, ← zpow_mul, hk, mul_comm]
  rw [map_pow, r_θ, qbinomial_theorem (v ^ k) h a]
  refine sum_congr rfl fun p _ => ?_
  rw [tw, map_pow, map_pow]

end PreF

namespace PreF

variable {I : Type*} {K : Type*} [Field K] {dot : I → I → ℤ} {v : Kˣ}

/-- **Lusztig 1.4.2**: `r(θ_i^{(a)}) = Σ_{t+t'=a} v_i^{tt'} θ_i^{(t)} ⊗ θ_i^{(t')}`, provided
`i · i` is even and `[a]_{v_i}^! ≠ 0` (automatic over `ℚ(v)`). -/
theorem r_dpow (i : I) (hev : Even (dot i i)) {a : ℕ} (hq : qfact (vi dot v i) a ≠ 0) :
    r dot v (dpow dot v i a) = ∑ p ∈ antidiagonal a,
      ((vi dot v i ^ ((p.1 : ℤ) * p.2) : Kˣ) : K) •
        tw dot v (dpow dot v i p.1) (dpow dot v i p.2) := by
  have hk : dot i i = 2 * (dot i i / 2) := by obtain ⟨k, hk⟩ := hev; omega
  rw [dpow, map_smul, r_θ_pow i hk, smul_sum]
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨s, s'⟩ := p
  rw [mem_antidiagonal] at hp
  subst hp
  simp only [dpow, tw_smul_left, tw_smul_right, smul_smul, qbinomCoef]
  congr 1
  simp only [vi] at hq ⊢
  rw [qbinom_eq_div _ hq]
  have ha := qfact_ne_zero_of_add_left _ hq
  have hb := qfact_ne_zero_of_add_right _ hq
  field_simp
  exact Or.inl (mul_comm _ _)

end PreF

end Categorification.QuantumGroup

end
