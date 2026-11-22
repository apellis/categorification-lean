/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Sl2Categorification.TopDividedPower
import Categorification.Algebra.NilHeckeModuleRecognition

/-!
# Simple subobjects of divided powers of a lowest-weight simple object

Chuang–Rouquier, arXiv:math/0407205v2, Proposition 5.20 (b), socle part: let `U` be a simple
object of a weak `𝔰𝔩₂`-categorification with nilHecke actions on `E` and `F`, with `F U = 0`,
and let `N = h₊([U])`. For `i ≤ N` and every simple `S`, `dim Hom(S, E^{(i)} U) ≤ 1`.

The argument is that of Chuang–Rouquier, with the nilHecke ring in place of the affine Hecke
algebra. Write `N = i + m` and `T = E^{(N)} U`, which is simple
(`WeakSl2.simple_divObj_top_of_F_eq_zero`). The space `R = Hom(T, E^N U)` is a representation of
`NH_N` of dimension `N!` (since `E^N U ≅ T^{⊕ N!}`) on which the dots act nilpotently. A
nonzero map `φ : S → E^{(i)} U ⊆ E^i U` gives `E^m φ : E^m S → E^N U`, and composing with a
nonzero map `z : T → E^m S` killed by the dots of `E^m` gives a vector of `R` fixed by the
idempotent `e_i` of `NH_i ⊆ NH_N` and killed by the dots `x_b`, `b ≥ i`. These vectors lie on a
line (`NilHecke.exists_forall_mem_span_of_idemNHAt`), and `φ ↦ z ≫ E^m(φ)` is injective.

The local nilpotence of the dot (Chuang–Rouquier, §5.2.1, with eigenvalue `0`) is the
hypothesis `hX`, and the condition `End(S) = k` for simple `S` (Chuang–Rouquier, §5.1.1) is the
hypothesis `hEnd`. The functor `E` is `k`-linear.

## Main results

* `WeakSl2.finrank_hom_divObj_le_one`: **Chuang–Rouquier, Proposition 5.20 (b)**, socle part,
  for `E`: `dim Hom(S, E^{(i)} U) ≤ 1`.
-/

namespace Categorification.Sl2

open CategoryTheory Limits Module

universe v u

variable {C : Type u} [Category.{v} C]

/-! ### Lifting maps through powers of `E` -/

section LiftMap

variable {E : C ⥤ C}

/-- For `g : M ⟶ Eⁱ U`, the map `E^m(g) : E^m M ⟶ E^{i+m} U`. -/
def liftMap {M U : C} {i : ℕ} (g : M ⟶ (Epow E i).obj U) :
    (m : ℕ) → ((Epow E m).obj M ⟶ (Epow E (i + m)).obj U)
  | 0 => g
  | m + 1 => E.map (liftMap g m)

@[simp] theorem liftMap_zero {M U : C} {i : ℕ} (g : M ⟶ (Epow E i).obj U) :
    liftMap g 0 = g := rfl

theorem liftMap_succ {M U : C} {i : ℕ} (g : M ⟶ (Epow E i).obj U) (m : ℕ) :
    liftMap g (m + 1) = E.map (liftMap g m) := rfl

theorem mono_liftMap [E.PreservesMonomorphisms] {M U : C} {i : ℕ} (g : M ⟶ (Epow E i).obj U)
    [Mono g] : ∀ m, Mono (liftMap g m)
  | 0 => inferInstanceAs (Mono g)
  | m + 1 => by
    have := mono_liftMap g m
    rw [liftMap_succ]
    exact E.map_mono _

theorem liftMap_comp {M M' U : C} {i : ℕ} (f : M' ⟶ M) (g : M ⟶ (Epow E i).obj U) :
    ∀ m, liftMap (f ≫ g) m = (Epow E m).map f ≫ liftMap g m
  | 0 => rfl
  | m + 1 => by
    rw [liftMap_succ, liftMap_comp f g m, Functor.map_comp, liftMap_succ]
    rfl

theorem liftMap_add [Preadditive C] [E.Additive] {M U : C} {i : ℕ} (g g' : M ⟶ (Epow E i).obj U) :
    ∀ m, liftMap (g + g') m = liftMap g m + liftMap g' m
  | 0 => rfl
  | m + 1 => by rw [liftMap_succ, liftMap_add g g' m, Functor.map_add]; rfl

theorem liftMap_smul {k : Type*} [CommRing k] [Preadditive C] [Linear k C] [E.Linear k]
    {M U : C} {i : ℕ} (c : k) (g : M ⟶ (Epow E i).obj U) :
    ∀ m, liftMap (c • g) m = c • liftMap g m
  | 0 => rfl
  | m + 1 => by rw [liftMap_succ, liftMap_smul c g m, Functor.map_smul]; rfl

end LiftMap

namespace NilHeckeData

variable [Preadditive C] {E : C ⥤ C} (D : NilHeckeData E)

/-- `E^m(g)` intertwines a dot on an inner strand. -/
theorem liftMap_xE_of_lt {M U : C} {i a : ℕ} (ha : a < i) (g : M ⟶ (Epow E i).obj U) :
    ∀ m, liftMap g m ≫ (D.xE (i + m) a).app U = liftMap (g ≫ (D.xE i a).app U) m
  | 0 => rfl
  | m + 1 => by
    rw [show D.xE (i + (m + 1)) a = sR (i + m) (D.xE (i + m) a) from
      D.xE_succ_of_lt (n := i + m) (by omega), liftMap_succ, liftMap_succ,
      ← liftMap_xE_of_lt ha g m,
      Functor.map_comp]
    rfl

/-- `E^m(g)` intertwines a crossing of inner strands. -/
theorem liftMap_τE_of_lt {M U : C} {i j : ℕ} (hj : j + 1 < i) (g : M ⟶ (Epow E i).obj U) :
    ∀ m, liftMap g m ≫ (D.τE (i + m) j).app U = liftMap (g ≫ (D.τE i j).app U) m
  | 0 => rfl
  | m + 1 => by
    rw [show D.τE (i + (m + 1)) j = sR (i + m) (D.τE (i + m) j) from
      D.τE_succ_of_lt (n := i + m) (by omega), liftMap_succ, liftMap_succ,
      ← liftMap_τE_of_lt hj g m,
      Functor.map_comp]
    rfl

/-- `E^m(g)` intertwines a dot on an outer strand. -/
theorem liftMap_xE_outer {M U : C} {i : ℕ} (g : M ⟶ (Epow E i).obj U) :
    ∀ m c, c < m → liftMap g m ≫ (D.xE (i + m) (i + c)).app U =
      (D.xE m c).app M ≫ liftMap g m
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, c, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · rw [show D.xE (i + (m + 1)) (i + c) = sR (i + m) (D.xE (i + m) (i + c)) from
        D.xE_succ_of_lt (n := i + m) (by omega), D.xE_succ_of_lt h, liftMap_succ]
      change E.map _ ≫ E.map _ = E.map _ ≫ E.map _
      rw [← Functor.map_comp, ← Functor.map_comp, liftMap_xE_outer g m c h]
    · rw [show D.xE (i + (c + 1)) (i + c) = sL (i + c) D.X from D.xE_succ_self _,
        D.xE_succ_self, liftMap_succ]
      exact D.X.naturality (liftMap g c)

/-- `α' ∈ End(E^{i+m})` restricts to `α ∈ End(Eⁱ)` along `E^m(-)` at `U`. -/
def Lifts (U : C) (i m : ℕ) (α' : End (Epow E (i + m))) (α : End (Epow E i)) : Prop :=
  ∀ (M : C) (g : M ⟶ (Epow E i).obj U), liftMap g m ≫ α'.app U = liftMap (g ≫ α.app U) m

omit [Preadditive C] in
theorem lifts_one (U : C) (i m : ℕ) : Lifts (E := E) U i m 1 1 := fun M g => by
  change liftMap g m ≫ 𝟙 _ = liftMap (g ≫ 𝟙 _) m
  simp

omit [Preadditive C] in
theorem Lifts.mul {U : C} {i m : ℕ} {α' β' : End (Epow E (i + m))} {α β : End (Epow E i)}
    (h : Lifts U i m α' α) (h' : Lifts U i m β' β) : Lifts U i m (α' * β') (α * β) :=
  fun M g => by
    change liftMap g m ≫ β'.app U ≫ α'.app U = liftMap (g ≫ β.app U ≫ α.app U) m
    rw [← Category.assoc, h', h, Category.assoc]

theorem lifts_xE {U : C} {i a : ℕ} (ha : a < i) (m : ℕ) :
    Lifts U i m (D.xE (i + m) a) (D.xE i a) := fun _ g => D.liftMap_xE_of_lt ha g m

theorem lifts_τE {U : C} {i j : ℕ} (hj : j + 1 < i) (m : ℕ) :
    Lifts U i m (D.τE (i + m) j) (D.τE i j) := fun _ g => D.liftMap_τE_of_lt hj g m

/-! ### The idempotent of `NH_i` inside `NH_{i+m}` -/

section Gamma

variable [E.Additive] {k : Type*} [Field k] [Linear k C]

open NilHecke MvPolynomial

/-- Multiplication by polynomials, as an algebra map into `NH_n`. -/
noncomputable def polyNH (k : Type*) [Field k] (n : ℕ) :
    MvPolynomial (Fin n) k →ₐ[k] nilHecke k n :=
  (mulPoly k n).codRestrict (nilHecke k n) mulPoly_mem

theorem lifts_polyNH_xDelta (U : C) (i m : ℕ) :
    Lifts U i m (D.γ (k := k) (i + m) (polyNH k (i + m) (xDelta i)))
      (D.γ (k := k) i (polyNH k i (xDelta i))) := by
  let P : MvPolynomial (Fin i) k → Prop := fun q =>
    Lifts U i m (D.γ (k := k) (i + m)
      (polyNH k (i + m) (rename (Fin.castLE (Nat.le_add_right i m)) q)))
      (D.γ (k := k) i (polyNH k i q))
  have hmul : ∀ q r, P q → P r → P (q * r) := fun q r hq hr => by
    simp only [P, map_mul]
    exact hq.mul hr
  have hone : P 1 := by
    simp only [P, map_one]
    exact lifts_one U i m
  have hX : ∀ a : Fin i, P (MvPolynomial.X a) := fun a => by
    simp only [P, rename_X]
    have h1 : polyNH k (i + m) (MvPolynomial.X (Fin.castLE (Nat.le_add_right i m) a)) =
        ⟨mulX k (i + m) (Fin.castLE (Nat.le_add_right i m) a), mulX_mem _⟩ := rfl
    have h2 : polyNH k i (MvPolynomial.X a) = ⟨mulX k i a, mulX_mem a⟩ := rfl
    rw [h1, h2, D.γ_mulX, D.γ_mulX]
    exact D.lifts_xE a.isLt m
  have hpow : ∀ (a : Fin i) (e : ℕ), P (MvPolynomial.X a ^ e) := fun a e => by
    induction e with
    | zero => rw [pow_zero]; exact hone
    | succ e ih => rw [pow_succ]; exact hmul _ _ ih (hX a)
  have hP : P (∏ a : Fin i, MvPolynomial.X a ^ (i - 1 - a)) :=
    Finset.prod_induction _ P hmul hone fun a _ => hpow a _
  simp only [P] at hP
  rw [← xDelta_eq_rename (Nat.le_add_right i m)] at hP
  exact hP

theorem lifts_ddw (U : C) {i : ℕ} (m : ℕ) :
    ∀ ρ : List ℕ, (∀ j ∈ ρ, j + 1 < i) →
      Lifts U i m (D.γ (k := k) (i + m) ⟨ddw ρ, ddw_mem ρ⟩) (D.γ (k := k) i ⟨ddw ρ, ddw_mem ρ⟩)
  | [], _ => by
    have h1 : ∀ n, (⟨ddw [], ddw_mem []⟩ : nilHecke k n) = 1 := fun n => Subtype.ext ddw_nil
    rw [h1, h1, map_one, map_one]
    exact lifts_one U i m
  | j :: ρ, h => by
    have h1 : ∀ n, (⟨ddw (j :: ρ), ddw_mem _⟩ : nilHecke k n) =
        ⟨dd k n j, dd_mem j⟩ * ⟨ddw ρ, ddw_mem ρ⟩ := fun n => Subtype.ext (ddw_cons j ρ)
    rw [h1, h1, map_mul, map_mul, D.γ_dd, D.γ_dd]
    exact (D.lifts_τE (h j (by simp)) m).mul
      (lifts_ddw U m ρ fun l hl => h l (by simp [hl]))

/-- The idempotent `e_i ∈ NH_i ⊆ NH_{i+m}` restricts to `e_i ∈ NH_i` along `E^m(-)`. -/
theorem lifts_idemNHAt (U : C) (i m : ℕ) :
    Lifts U i m (D.γ (k := k) (i + m) (idemNHAt k (i + m) i))
      (D.γ (k := k) i ⟨idemNH k i, idemNH_mem⟩) := by
  have h1 : idemNHAt k (i + m) i = polyNH k (i + m) (xDelta i) * ⟨ddw (w0Word i), ddw_mem _⟩ :=
    rfl
  have h2 : (⟨idemNH k i, idemNH_mem⟩ : nilHecke k i) =
      polyNH k i (xDelta i) * ⟨ddw (w0Word i), ddw_mem _⟩ := rfl
  rw [h1, h2, map_mul, map_mul]
  exact (D.lifts_polyNH_xDelta U i m).mul
    (D.lifts_ddw U m _ fun j hj => lt_of_mem_w0Word hj)

end Gamma

end NilHeckeData

/-- Pairwise commuting maps fixing `0`, each locally nilpotent, have a common nonzero kernel
vector as soon as the domain has a nonzero vector. -/
theorem exists_ne_zero_forall_eq_zero {ι M : Type*} [Zero M] (s : Finset ι) (f : ι → M → M)
    (hzero : ∀ a, f a 0 = 0) (hc : ∀ a b x, f a (f b x) = f b (f a x))
    (hn : ∀ a x, ∃ p, (f a)^[p] x = 0) {v : M} (hv : v ≠ 0) :
    ∃ w, w ≠ 0 ∧ ∀ a ∈ s, f a w = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨v, hv, by simp⟩
  | insert b s _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    have hex : ∃ p, (f b)^[p] w = 0 := hn b w
    have hp0 : Nat.find hex ≠ 0 := by
      intro h
      have := Nat.find_spec hex
      rw [h] at this
      exact hw this
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hp0
    refine ⟨(f b)^[q] w, Nat.find_min hex (by omega), ?_⟩
    intro a ha
    rcases Finset.mem_insert.1 ha with h | ha
    · subst h
      rw [← Function.iterate_succ_apply' (f a), ← hq]
      exact Nat.find_spec hex
    · have hcomm : Function.Commute (f a) (f b) := fun x => hc a b x
      rw [(hcomm.iterate_right q) w, hs a ha]
      exact Function.iterate_fixed (hzero b) q

namespace NilHeckeData

variable [Abelian C] {E : C ⥤ C} (D : NilHeckeData E)

section Socle

variable [E.Additive] {k : Type*} [Field k] [Linear k C]

open NilHecke

/-- If the dot is nilpotent on every object, so is every dot of `Eⁿ`. -/
theorem isNilpotent_xE_app (hX : ∀ M, IsNilpotent (R := End (E.obj M)) (D.X.app M)) :
    ∀ (n a : ℕ) (M : C), IsNilpotent (R := End ((Epow E n).obj M)) ((D.xE n a).app M)
  | 0, _, _ => ⟨1, by rw [pow_one, xE_zero, NatTrans.app_zero]⟩
  | n + 1, a, M => by
    rcases lt_trichotomy a n with h | rfl | h
    · rw [D.xE_succ_of_lt h]
      obtain ⟨p, hp⟩ := isNilpotent_xE_app hX n a M
      refine ⟨p, ?_⟩
      change (E.mapEnd _ ((D.xE n a).app M)) ^ p = 0
      rw [← map_pow, hp]
      exact E.map_zero _ _
    · rw [D.xE_succ_self]
      exact hX _
    · rw [D.xE_of_le (by omega)]
      exact ⟨1, by rw [pow_one, NatTrans.app_zero]⟩

/-- Postcomposition with the action of `NH_n` on `Eⁿ U`, on morphisms out of `T`. -/
noncomputable def postγ (n : ℕ) (T U : C) :
    nilHecke k n →ₐ[k] Module.End k (T ⟶ (Epow E n).obj U) where
  toFun t := Linear.rightComp k T ((D.γ (k := k) n t).app U)
  map_one' := LinearMap.ext fun φ => by simp
  map_mul' s t := LinearMap.ext fun φ => by simp [End.mul_def]
  map_zero' := LinearMap.ext fun φ => by simp
  map_add' s t := LinearMap.ext fun φ => by
    simp only [map_add, LinearMap.add_apply, Linear.rightComp_apply]
    rw [NatTrans.app_add, Preadditive.comp_add]
  commutes' c := LinearMap.ext fun φ => by
    simp only [Algebra.algebraMap_eq_smul_one, Linear.rightComp_apply]
    rw [map_smul, map_one, NatTrans.app_smul, End.one_def, NatTrans.id_app, Linear.comp_smul,
      Category.comp_id, LinearMap.smul_apply, Module.End.one_apply]

@[simp] theorem postγ_apply (n : ℕ) (T U : C) (t : nilHecke k n) (φ : T ⟶ (Epow E n).obj U) :
    D.postγ n T U t φ = φ ≫ (D.γ (k := k) n t).app U := rfl

/-- The image of the idempotent `e_n` acting on `Eⁿ M` is fixed by `e_n`. -/
theorem image_ι_comp_idem (n : ℕ) (M : C) :
    image.ι ((D.γ (k := k) n ⟨idemNH k n, idemNH_mem⟩).app M) ≫
      (D.γ (k := k) n ⟨idemNH k n, idemNH_mem⟩).app M =
      image.ι ((D.γ (k := k) n ⟨idemNH k n, idemNH_mem⟩).app M) := by
  set e := (D.γ (k := k) n ⟨idemNH k n, idemNH_mem⟩).app M
  have he : e ≫ e = e := by
    have h1 : (⟨idemNH k n, idemNH_mem⟩ : nilHecke k n) * ⟨idemNH k n, idemNH_mem⟩ =
        ⟨idemNH k n, idemNH_mem⟩ := Subtype.ext isIdempotentElem_idemNH
    have h2 := congrArg (fun t => (D.γ (k := k) n t).app M) h1
    rw [map_mul] at h2
    exact h2
  rw [← cancel_epi (factorThruImage e), ← Category.assoc, image.fac, he]

variable (k) in
/-- The inclusion `E^{(n)} M ⟶ Eⁿ M`. -/
noncomputable def divι (n : ℕ) (M : C) : D.divObj k n M ⟶ (Epow E n).obj M :=
  image.ι ((D.γ (k := k) n ⟨idemNH k n, idemNH_mem⟩).app M)

variable (k) in
/-- The projection `Eⁿ M ⟶ E^{(n)} M`. -/
noncomputable def divπ (n : ℕ) (M : C) : (Epow E n).obj M ⟶ D.divObj k n M :=
  factorThruImage ((D.γ (k := k) n ⟨idemNH k n, idemNH_mem⟩).app M)

instance (n : ℕ) (M : C) : Mono (D.divι k n M) := by
  unfold divι; exact (Image.monoFactorisation _).m_mono

theorem divπ_divι (n : ℕ) (M : C) :
    D.divπ k n M ≫ D.divι k n M = (D.γ (k := k) n ⟨idemNH k n, idemNH_mem⟩).app M :=
  image.fac _

theorem divι_idem (n : ℕ) (M : C) :
    D.divι k n M ≫ (D.γ (k := k) n ⟨idemNH k n, idemNH_mem⟩).app M = D.divι k n M :=
  D.image_ι_comp_idem n M

omit [Abelian C] in
/-- Iterated postcomposition is postcomposition with a power. -/
theorem iterate_comp {X Y : C} (x : End Y) :
    ∀ (p : ℕ) (φ : X ⟶ Y), (fun ψ => ψ ≫ x)^[p] φ = φ ≫ (x ^ p : End Y)
  | 0, φ => by simp [End.one_def]
  | p + 1, φ => by
    rw [Function.iterate_succ_apply', iterate_comp x p φ, pow_succ', End.mul_def,
      Category.assoc]

variable [E.Linear k]

/-- **Socle bound** (core of Chuang–Rouquier, Proposition 5.20 (b)): if `End(E^{(i+m)} U) = k`,
the dot is nilpotent, `S` is simple and there is a nonzero map `E^{(i+m)} U ⟶ E^m S`, then
`dim Hom(S, E^{(i)} U) ≤ 1`. -/
theorem finrank_hom_divObj_le_one_of_ne_zero [E.PreservesMonomorphisms]
    (hX : ∀ M, IsNilpotent (R := End (E.obj M)) (D.X.app M)) {U S : C} [Simple S] {i m : ℕ}
    (hT : finrank k (D.divObj k (i + m) U ⟶ D.divObj k (i + m) U) = 1)
    {z₀ : D.divObj k (i + m) U ⟶ (Epow E m).obj S} (hz₀ : z₀ ≠ 0) :
    finrank k (S ⟶ D.divObj k i U) ≤ 1 := by
  set T := D.divObj k (i + m) U
  -- a nonzero `z : T ⟶ E^m S` killed by the dots of `E^m`
  obtain ⟨z, hz, hzx⟩ := exists_ne_zero_forall_eq_zero (Finset.range m)
    (fun c (ψ : T ⟶ (Epow E m).obj S) => ψ ≫ (D.xE m c).app S) (fun _ => zero_comp)
    (fun a b ψ => by
      have h := congr_app (D.xE_comm m a b) S
      simp only [End.mul_def, NatTrans.comp_app] at h
      simp only [Category.assoc, h])
    (fun a ψ => by
      obtain ⟨p, hp⟩ := D.isNilpotent_xE_app hX m a S
      exact ⟨p, by rw [iterate_comp, hp, comp_zero]⟩) hz₀
  -- the representation `R = Hom(T, E^N U)` of `NH_N`
  set N := i + m
  let ρ := D.postγ (k := k) N T U
  set eN : nilHecke k N := ⟨idemNH k N, idemNH_mem⟩
  set eU := (D.γ (k := k) N eN).app U
  let g : (T ⟶ T) →ₗ[k] (T ⟶ (Epow E N).obj U) := Linear.rightComp k T (D.divι k N U)
  have hg : Function.Injective g := fun a b h => (cancel_mono (D.divι k N U)).1 h
  have hrange : LinearMap.range (ρ eN) = LinearMap.range g := by
    apply le_antisymm
    · rintro _ ⟨ψ, rfl⟩
      refine ⟨ψ ≫ D.divπ k N U, ?_⟩
      change (ψ ≫ D.divπ k N U) ≫ D.divι k N U = ψ ≫ eU
      rw [Category.assoc, D.divπ_divι]
    · rintro _ ⟨ψ, rfl⟩
      refine ⟨ψ ≫ D.divι k N U, ?_⟩
      change (ψ ≫ D.divι k N U) ≫ eU = ψ ≫ D.divι k N U
      rw [Category.assoc, D.divι_idem]
  have hrk : finrank k (LinearMap.range (ρ eN)) = 1 := by
    rw [hrange, LinearMap.finrank_range_of_inj hg]
    exact hT
  have : FiniteDimensional k (LinearMap.range (ρ eN)) :=
    Module.finite_of_finrank_eq_succ hrk
  have : FiniteDimensional k (T ⟶ (Epow E N).obj U) := by
    obtain ⟨J, _, _, a, b, _, hS⟩ := exists_isSplitting_one_idemNH k N
    have h := hS.map ρ
    rw [map_one] at h
    exact finiteDimensional_of_isSplitting h
  have hR : finrank k (T ⟶ (Epow E N).obj U) = N.factorial := by
    have := finrank_eq_factorial_mul_finrank_range ρ
    rw [this]
    erw [hrk, mul_one]
  have hnil : ∀ a : Fin N, IsNilpotent (ρ ⟨mulX k N a, mulX_mem a⟩) := by
    intro a
    obtain ⟨p, hp⟩ := D.isNilpotent_xE_app hX N a U
    refine ⟨p, ?_⟩
    rw [← map_pow]
    refine LinearMap.ext fun ψ => ?_
    rw [postγ_apply, map_pow, D.γ_mulX]
    have : ((D.xE N a) ^ p).app U = (evalEnd (Epow E N) U (D.xE N a)) ^ p :=
      map_pow (evalEnd (Epow E N) U) (D.xE N a) p
    rw [this, evalEnd_apply, hp, comp_zero, LinearMap.zero_apply]
  obtain ⟨u₀, hu₀⟩ := exists_forall_mem_span_of_idemNHAt ρ hR hnil (Nat.le_add_right i m)
  -- the injective map `φ ↦ z ≫ E^m(φ)`
  let Φ : (S ⟶ D.divObj k i U) →ₗ[k] (T ⟶ (Epow E N).obj U) :=
    { toFun := fun φ => z ≫ liftMap (φ ≫ D.divι k i U) m
      map_add' := fun φ ψ => by
        rw [Preadditive.add_comp, liftMap_add, Preadditive.comp_add]
      map_smul' := fun c φ => by
        rw [Linear.smul_comp, liftMap_smul, Linear.comp_smul]
        rfl }
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    by_contra hne
    have : Mono φ := mono_of_nonzero_from_simple hne
    have : Mono (liftMap (E := E) (φ ≫ D.divι k i U) m) := mono_liftMap _ m
    apply hz
    rw [← cancel_mono (liftMap (E := E) (φ ≫ D.divι k i U) m), zero_comp]
    exact hφ
  have hmem : ∀ φ, Φ φ ∈ k ∙ u₀ := by
    intro φ
    apply hu₀
    · change (z ≫ liftMap (φ ≫ D.divι k i U) m) ≫
          (D.γ (k := k) N (idemNHAt k N i)).app U = z ≫ liftMap (φ ≫ D.divι k i U) m
      rw [Category.assoc, D.lifts_idemNHAt U i m, Category.assoc, D.divι_idem]
    · intro b hb
      obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hb
      have hcm : c < m := by have := b.isLt; omega
      change (z ≫ liftMap (φ ≫ D.divι k i U) m) ≫ (D.γ (k := k) N _).app U = 0
      rw [D.γ_mulX, hc, Category.assoc, liftMap_xE_outer D _ m c hcm, ← Category.assoc,
        hzx c (Finset.mem_range.2 hcm), zero_comp]
  let Φ' := Φ.codRestrict (k ∙ u₀) hmem
  have hΦ' : Function.Injective Φ' := fun a b h => hΦ (congrArg Subtype.val h)
  calc finrank k (S ⟶ D.divObj k i U) ≤ finrank k (k ∙ u₀) :=
        LinearMap.finrank_le_finrank_of_injective hΦ'
    _ ≤ 1 := (finrank_span_le_card ({u₀} : Set _)).trans (by simp)

end Socle

end NilHeckeData

end Categorification.Sl2
