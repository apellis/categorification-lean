import Categorification.KLR.CyclotomicMixedInversionIdeal
import Categorification.KLR.CyclotomicMixedInversionTensor
import Categorification.KLR.CyclotomicLowerExactOne

/-!
# Actual cyclotomic factors of the rectangular mixed tensor

The cut of the penultimate subalgebra is the image of actual last-strand concatenation.
Both orders of multiplication by the cyclotomic generator are retained separately.
The quotient-source map is onto the tensor over `CycKLR γ` of the actual two cyclotomic
one-sided ideals; its kernel is exactly the span of the two factor-ideal relations.
No flatness or assumed kernel/ideal compatibility is used. These comparisons require
only a commutative base. The PBW/domain hypotheses enter in the descent module.
-/
noncomputable section
namespace Categorification.KLR.KLRAlgebra.MixedCyclotomic
open scoped TensorProduct
open MixedAffine Lower
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k)

theorem cast_penSub {μ ν : Multiset I} (h : μ = ν) (z : KLRAlgebra k Q μ) :
    castKLR Q h z ∈ penSub ν ↔ z ∈ penSub μ := by
  subst h
  rfl

theorem penSub_le_core (c : I) (β : Multiset I) :
    penSub (Q := Q) ({c} + β) ≤ cLCore c β := by
  apply Algebra.adjoin_le
  rintro z ((⟨b, hb, rfl⟩ | ⟨s, rfl⟩) | ⟨l, hl, rfl⟩)
  · have hb' : b.val < Multiset.card β := by simpa using hb
    exact x_mem_cLCore c β ⟨b.val, hb'⟩
  · exact e_mem_cLCore c β s
  · apply ψ_mem_cLCore
    simp only [Multiset.card_add, Multiset.card_singleton] at hl
    omega

theorem penSub_project (β : Multiset I) (c : I) {z : KLRAlgebra k Q (β + {c})}
    (hz : z ∈ penSub (β + {c})) :
    ∃ y : KLRAlgebra k Q β, z * inc Q β c 1 = inc Q β c y := by
  let h : β + {c} = {c} + β := add_comm _ _
  obtain ⟨y, hy⟩ := penSub_le_core Q c β ((cast_penSub Q h z).2 hz)
  refine ⟨y, ?_⟩
  apply (castKLR Q h).injective
  change castKLR Q h (z * concat Q β {c} (1 ⊗ₜ 1)) =
    castKLR Q h (concat Q β {c} (y ⊗ₜ 1))
  rw [map_mul]
  exact hy

theorem inc_mem_cycIdeal (a : I → Polynomial k) (β : Multiset I) (c : I)
    {z : KLRAlgebra k Q β} (hz : z ∈ cycIdeal Q a β) :
    inc Q β c z ∈ cycIdeal Q a (β + {c}) := by
  apply (castKLR_mem_cycIdeal a (add_comm β ({c} : Multiset I)) _).1
  exact cL_mem_cycIdeal c β a hz

theorem inc_one_colour (β : Multiset I) (c : I) :
    inc Q β c 1 = MixedInversion.colourIdem ⟨Multiset.card β, by simp⟩ c := by
  apply ext_e
  intro s
  change concat Q β {c} (1 ⊗ₜ 1) * e s = _
  rw [concat_one_tmul_one]
  rw [oneConcat, eSum_mul_e, MixedInversion.colourIdem_mul_e]
  have ht : s ∈ concatSet β {c} ↔ s.1 ⟨Multiset.card β, by simp⟩ = c := by
    rw [mem_concatSet_iff_hasTail (fun j hj => Multiset.mem_singleton.1 hj)]
    constructor
    · intro hs
      exact hs.2 ⟨Multiset.card β, by simp⟩ (by simp)
    · intro hs
      refine ⟨by simp, fun b hb => ?_⟩
      have he : b = ⟨Multiset.card β, by simp⟩ := by
        apply Fin.ext
        have := b.isLt
        simp only [Multiset.card_add, Multiset.card_singleton] at *
        omega
      simpa only [he] using hs
  simp only [ht]


theorem cast_colour {μ ν : Multiset I} (h : μ = ν) (b : Fin (Multiset.card μ)) (c : I) :
    castKLR Q h (MixedInversion.colourIdem b c) =
      MixedInversion.colourIdem (Fin.cast (congrArg Multiset.card h) b) c := by
  subst h
  rfl

theorem cast_cycAt_zero (a : I → Polynomial k) {μ ν : Multiset I} (h : μ = ν)
    (hm : 0 < Multiset.card μ) (hn : 0 < Multiset.card ν) :
    castKLR Q h (cycAt a ⟨0, hm⟩) = cycAt a ⟨0, hn⟩ := by
  subst h
  rfl

theorem inc_one_commute_penSub (β : Multiset I) (c : I)
    {z : KLRAlgebra k Q (β + {c})} (hz : z ∈ penSub (β + {c})) :
    Commute (inc Q β c 1) z := by
  rw [inc_one_colour]
  exact MixedInversion.colourIdem_commute_subR0 (Multiset.card β) (by simp) c
    (MixedInversion.penSub_le_subR0 hz)

theorem inc_cycAt (a : I → Polynomial k) (β : Multiset I) (c : I)
    (hb : 0 < Multiset.card β) :
    inc Q β c (cycAt a ⟨0, hb⟩) =
      cycAt a ⟨0, by simp⟩ * inc Q β c 1 := by
  change concat Q β {c} (cycAt a ⟨0, hb⟩ ⊗ₜ 1) = _
  rw [← cycAt_zero_mul_oneConcat c β a (by simp) hb]
  change _ * _ = _ * concat Q β {c} (1 ⊗ₜ 1)
  rw [concat_one_tmul_one]


theorem inc_cyc_left (a : I → Polynomial k) (β : Multiset I) (c : I)
    (hb : 0 < Multiset.card β) (y : KLRAlgebra k Q β) :
    inc Q β c (cycAt a ⟨0, hb⟩ * y) = cycAt a ⟨0, by simp⟩ * inc Q β c y := by
  rw [map_mul, inc_cycAt, mul_assoc, ← map_mul, one_mul]

theorem inc_cyc_right (a : I → Polynomial k) (β : Multiset I) (c : I)
    (hb : 0 < Multiset.card β) (y : KLRAlgebra k Q β) :
    inc Q β c (y * cycAt a ⟨0, hb⟩) = inc Q β c y * cycAt a ⟨0, by simp⟩ := by
  have hc : Commute (inc Q β c 1) (cycAt a ⟨0, by simp⟩) := by
    rw [inc_one_colour]
    exact MixedInversion.colourIdem_commute_of_diagonal _ _ _ (fun s => cycAt_mul_e' a _ s)
  rw [map_mul, inc_cycAt, ← hc.eq, ← mul_assoc, ← map_mul, mul_one]

theorem penSub_cyc_left (a : I → Polynomial k) (β : Multiset I) (c : I)
    (hb : 0 < Multiset.card β) {u : KLRAlgebra k Q (β + {c})}
    (hu : u ∈ penSub (β + {c})) :
    ∃ b ∈ cycIdeal Q a β,
      inc Q β c 1 * u * cycAt a ⟨0, by simp⟩ = inc Q β c b := by
  obtain ⟨y, hy⟩ := penSub_project Q β c hu
  refine ⟨y * cycAt a ⟨0, hb⟩,
    TwoSidedIdeal.mul_mem_left _ _ _ (cycAt_mem_cycIdeal a hb), ?_⟩
  rw [(inc_one_commute_penSub Q β c hu).eq, hy, inc_cyc_right]

theorem penSub_cyc_right (a : I → Polynomial k) (β : Multiset I) (c : I)
    (hb : 0 < Multiset.card β) {v : KLRAlgebra k Q (β + {c})}
    (hv : v ∈ penSub (β + {c})) :
    ∃ b ∈ cycIdeal Q a β,
      cycAt a ⟨0, by simp⟩ * v * inc Q β c 1 = inc Q β c b := by
  obtain ⟨y, hy⟩ := penSub_project Q β c hv
  refine ⟨cycAt a ⟨0, hb⟩ * y,
    TwoSidedIdeal.mul_mem_right _ _ _ (cycAt_mem_cycIdeal a hb), ?_⟩
  rw [mul_assoc, hy, inc_cyc_left]

variable (γ : Multiset I) (i j : I) (a : I → Polynomial k)
local notation "U" => KLRAlgebra k Q ((γ + Multiset.cons j 0) + Multiset.cons i 0)
local notation "A" => KLRAlgebra k Q (γ + Multiset.cons j 0)
local notation "C" => KLRAlgebra k Q (γ + Multiset.cons i 0)
local notation "T" => Source Q γ i j

def tensorRelations : Submodule k T :=
  Submodule.span k {z | ∃ (x : Left Q γ j) (y : Right Q γ i),
    ((x : A) ∈ cycIdeal Q a (γ + {j}) ∨ (y : C) ∈ cycIdeal Q a (γ + {i})) ∧
    z = BalancedTensor.tmul x y}

def cornerIdeal : Submodule k (bimod Q (weightSquare γ i j)) :=
  Submodule.comap (bimod Q (weightSquare γ i j)).subtype
    ((cycIdeal Q a ((γ + {j}) + {i})).asIdeal.restrictScalars k)

theorem left_ideal_smul {b : A} (hb : b ∈ cycIdeal Q a (γ + {j})) (z : T) :
    b • z ∈ tensorRelations Q γ i j a := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, Submodule.zero_mem]
  | add z w hz hw => rw [smul_add]; exact Submodule.add_mem _ hz hw
  | tmul x y =>
    rw [BalancedTensor.smul_tmul']
    exact Submodule.subset_span ⟨b • x, y,
      Or.inl (TwoSidedIdeal.mul_mem_right _ _ _ hb), rfl⟩

theorem right_ideal_act {b : C} (hb : b ∈ cycIdeal Q a (γ + {i})) (z : T) :
    rightAct Q γ i j b z ∈ tensorRelations Q γ i j a := by
  induction z using BalancedTensor.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add z w hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw
  | tmul x y =>
    exact Submodule.subset_span ⟨x, rightMul Q γ i b y,
      Or.inr (TwoSidedIdeal.mul_mem_left _ _ _ hb), rfl⟩


theorem topOne_colour : (oneConcat Q (γ + {j}) {i} : U) =
    MixedInversion.colourIdem ⟨Multiset.card γ + 1, by simp⟩ i := by
  have h := inc_one_colour Q (γ + {j}) i
  change concat Q (γ + {j}) {i} (1 ⊗ₜ 1) = _ at h
  simpa only [concat_one_tmul_one, Multiset.card_add, Multiset.card_singleton] using h

theorem botOne_colour : (botOne Q (weightSquare γ i j) : U) =
    MixedInversion.colourIdem ⟨Multiset.card γ + 1, by simp⟩ j := by
  rw [← botConcat_one]
  change castKLR Q (weightSquare γ i j) (concat Q (γ + {i}) {j} (1 ⊗ₜ 1)) = _
  change castKLR Q (weightSquare γ i j) (inc Q (γ + {i}) j 1) = _
  rw [inc_one_colour, cast_colour]
  congr 1
  apply Fin.ext
  simp

def project : U →ₗ[k] bimod Q (weightSquare γ i j) where
  toFun z := ⟨oneConcat Q (γ + {j}) {i} * z * botOne Q (weightSquare γ i j), by
    apply (mem_bimod _).2
    simp only [← mul_assoc, oneConcat_idem.eq]
    rw [mul_assoc _ (botOne Q (weightSquare γ i j)), (botOne_idem _).eq]⟩
  map_add' x y := Subtype.ext (by change _ = _ + _; simp only [mul_add, add_mul])
  map_smul' c x := Subtype.ext (by change _ = c • _; simp only [mul_smul_comm, smul_mul_assoc])

theorem project_val (z : U) : (project Q γ i j z : U) =
    MixedInversion.cut ⟨Multiset.card γ + 1, by simp⟩ i j z := by
  change _ * z * _ = _
  rw [topOne_colour, botOne_colour]
  rfl

theorem project_fixed (z : bimod Q (weightSquare γ i j)) : project Q γ i j z = z :=
  Subtype.ext ((mem_bimod _).1 z.2)


theorem left_coefficient_lift (u v : U) (hu : u ∈ penSub ((γ + {j}) + {i})) :
    ∃ b : A, b ∈ cycIdeal Q a (γ + {j}) ∧
      project Q γ i j (u * cycAt a ⟨0, by simp⟩ * v) =
        cornerLeft Q γ i j b (project Q γ i j v) := by
  have hbpos : 0 < Multiset.card (γ + ({j} : Multiset I)) := by simp
  obtain ⟨b, hb, he⟩ := penSub_cyc_left Q a (γ + ({j} : Multiset I)) i hbpos (u := u) hu
  refine ⟨b, hb, Subtype.ext ?_⟩
  change oneConcat Q (γ + {j}) {i} * (u * cycAt a _ * v) * botOne Q _ =
    inc Q (γ + {j}) i b * (oneConcat Q (γ + {j}) {i} * v * botOne Q _)
  have hone : oneConcat Q (γ + {j}) {i} = inc Q (γ + {j}) i 1 := concat_one_tmul_one.symm
  rw [hone]
  calc
    _ = (inc Q (γ + {j}) i 1 * u * cycAt a ⟨0, by simp⟩) * v * botOne Q (weightSquare γ i j) := by simp only [mul_assoc]
    _ = inc Q (γ + {j}) i b * v * botOne Q (weightSquare γ i j) := by rw [he]
    _ = _ := by rw [← mul_assoc, ← mul_assoc, ← map_mul, mul_one]

theorem right_coefficient_lift (u v : U) (hv : v ∈ penSub ((γ + {j}) + {i})) :
    ∃ b : C, b ∈ cycIdeal Q a (γ + {i}) ∧
      project Q γ i j (u * cycAt a ⟨0, by simp⟩ * v) =
        cornerRight Q γ i j b (project Q γ i j u) := by
  let h := weightSquare γ i j
  let v' := castKLR Q h.symm v
  have hv' : v' ∈ penSub ((γ + {i}) + {j}) := (cast_penSub Q h.symm v).2 hv
  have hbpos : 0 < Multiset.card (γ + ({i} : Multiset I)) := by simp
  obtain ⟨b, hb, he⟩ := penSub_cyc_right Q a (γ + ({i} : Multiset I)) j hbpos (v := v') hv'
  have he' := congrArg (castKLR Q h) he
  have hvv : castKLR Q h v' = v := by simp [v']
  have hone : castKLR Q h (inc Q (γ + {i}) j 1) = botOne Q h := by
    change botConcat Q h (1 ⊗ₜ 1) = _
    exact botConcat_one h
  rw [map_mul, map_mul, cast_cycAt_zero Q a h _ (by simp), hvv, hone] at he'
  refine ⟨b, hb, Subtype.ext ?_⟩
  change oneConcat Q (γ + {j}) {i} * (u * cycAt a _ * v) * botOne Q h =
    (oneConcat Q (γ + {j}) {i} * u * botOne Q h) * botConcat Q h (b ⊗ₜ 1)
  calc
    _ = (oneConcat Q (γ + {j}) {i} * u) * (cycAt a ⟨0, by simp⟩ * v * botOne Q h) := by simp only [mul_assoc]
    _ = (oneConcat Q (γ + {j}) {i} * u) * botConcat Q h (b ⊗ₜ 1) := by rw [he']; rfl
    _ = _ := by rw [mul_assoc _ (botOne Q h), botOne_mul_botConcat]


section QuotientSource
variable {k₀ M₀ N₀ V₀ : Type*} [CommRing k₀]
  [AddCommGroup M₀] [Module k₀ M₀] [AddCommGroup N₀] [Module k₀ N₀]
  [AddCommGroup V₀] [Module k₀ V₀]
def descend (q : M₀ →ₗ[k₀] N₀) (hq : Function.Surjective q)
    (f : M₀ →ₗ[k₀] V₀) (hf : LinearMap.ker q ≤ LinearMap.ker f) : N₀ →ₗ[k₀] V₀ :=
  (LinearMap.ker q).liftQ f hf ∘ₗ (q.quotKerEquivOfSurjective hq).symm.toLinearMap
theorem descend_apply (q : M₀ →ₗ[k₀] N₀) (hq : Function.Surjective q)
    (f : M₀ →ₗ[k₀] V₀) (hf : LinearMap.ker q ≤ LinearMap.ker f) (x : M₀) :
    descend q hq f hf (q x) = f x := by
  rw [descend, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl
end QuotientSource

def quotientIncLinear (β : Multiset I) (c : I) :
    CycKLR k Q a β →ₗ[k] CycKLR k Q a (β + {c}) := by
  let f : KLRAlgebra k Q β →ₗ[k] CycKLR k Q a (β + {c}) :=
    { toFun := fun z => CycKLR.mk k Q a (β + {c}) (inc Q β c z)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun r x => by simp only [map_smul, RingHom.id_apply] }
  exact descend (CycKLR.mk k Q a β).toLinearMap CycKLR.mk_surjective f
    (fun z hz => (CycKLR.mk_eq_zero_iff _).2
      (inc_mem_cycIdeal Q a β c ((CycKLR.mk_eq_zero_iff z).1 hz)))

theorem quotientIncLinear_mk (β : Multiset I) (c : I) (z : KLRAlgebra k Q β) :
    quotientIncLinear Q a β c (CycKLR.mk k Q a β z) =
      CycKLR.mk k Q a (β + {c}) (inc Q β c z) := descend_apply _ _ _ _ z

def quotientInc (β : Multiset I) (c : I) :
    CycKLR k Q a β →ₙₐ[k] CycKLR k Q a (β + {c}) where
  toFun := quotientIncLinear Q a β c
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' x y := by
    obtain ⟨x, rfl⟩ := CycKLR.mk_surjective x
    obtain ⟨y, rfl⟩ := CycKLR.mk_surjective y
    rw [← map_mul, quotientIncLinear_mk, map_mul, map_mul,
      quotientIncLinear_mk, quotientIncLinear_mk]

theorem quotientInc_mk (β : Multiset I) (c : I) (z : KLRAlgebra k Q β) :
    quotientInc Q a β c (CycKLR.mk k Q a β z) =
      CycKLR.mk k Q a (β + {c}) (inc Q β c z) := quotientIncLinear_mk Q a β c z

theorem quotientInc_one (β : Multiset I) (c : I) :
    quotientInc Q a β c 1 = CycKLR.mk k Q a (β + {c}) (inc Q β c 1) := by
  rw [← map_one (CycKLR.mk k Q a β), quotientInc_mk]

abbrev QuotientLeft := CornerTensor.Left (quotientInc Q a γ j)
abbrev QuotientRight := CornerTensor.Right (quotientInc Q a γ i) (AlgHom.id k _)
abbrev QuotientSource := BalancedTensor k (CycKLR k Q a (γ + {j}))
  (CycKLR k Q a γ) (QuotientLeft Q γ j a) (QuotientRight Q γ i a)

def leftMk : Left Q γ j →ₗ[k] QuotientLeft Q γ j a where
  toFun x := ⟨CycKLR.mk k Q a (γ + {j}) (x : A), by
    change CycKLR.mk k Q a (γ + {j}) (x : A) * quotientInc Q a γ j 1 = _
    rw [quotientInc_one, ← map_mul, CornerTensor.left_mem]⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (map_smul _ _ _)

def rightMk : Right Q γ i →ₗ[k] QuotientRight Q γ i a where
  toFun y := ⟨CycKLR.mk k Q a (γ + {i}) (y : C), by
    change quotientInc Q a γ i 1 * CycKLR.mk k Q a (γ + {i}) (y : C) = _
    rw [quotientInc_one, ← map_mul]
    exact congrArg (CycKLR.mk k Q a (γ + {i})) (CornerTensor.right_mem _ _ y)⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (map_smul _ _ _)

theorem leftMk_surjective : Function.Surjective (leftMk Q γ j a) := by
  intro x
  obtain ⟨r, hr⟩ := CycKLR.mk_surjective (x : CycKLR k Q a (γ + {j}))
  refine ⟨leftInsert Q γ j r 1, Subtype.ext ?_⟩
  change CycKLR.mk k Q a (γ + {j}) (r * inc Q γ j 1) = _
  rw [map_mul, hr, ← quotientInc_one]
  exact CornerTensor.left_mem _ x

theorem rightMk_surjective : Function.Surjective (rightMk Q γ i a) := by
  intro y
  obtain ⟨r, hr⟩ := CycKLR.mk_surjective (y : CycKLR k Q a (γ + {i}))
  refine ⟨rightInsert Q γ i r 1, Subtype.ext ?_⟩
  change CycKLR.mk k Q a (γ + {i}) (inc Q γ i 1 * r) = _
  rw [map_mul, hr, ← quotientInc_one]
  exact CornerTensor.right_mem _ _ y

theorem leftMk_zero_iff (x : Left Q γ j) :
    leftMk Q γ j a x = 0 ↔ (x : A) ∈ cycIdeal Q a (γ + {j}) := by
  rw [← CycKLR.mk_eq_zero_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem rightMk_zero_iff (y : Right Q γ i) :
    rightMk Q γ i a y = 0 ↔ (y : C) ∈ cycIdeal Q a (γ + {i}) := by
  rw [← CycKLR.mk_eq_zero_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩


theorem leftMk_balance (d : KLRAlgebra k Q γ) (x : Left Q γ j) :
    leftMk Q γ j a (MulOpposite.op d • x) =
      MulOpposite.op (CycKLR.mk k Q a γ d) • leftMk Q γ j a x := by
  apply Subtype.ext
  change CycKLR.mk k Q a (γ + {j}) ((x : A) * inc Q γ j d) =
    CycKLR.mk k Q a (γ + {j}) (x : A) * quotientInc Q a γ j (CycKLR.mk k Q a γ d)
  rw [map_mul, quotientInc_mk]

theorem rightMk_balance (d : KLRAlgebra k Q γ) (y : Right Q γ i) :
    rightMk Q γ i a (d • y) = CycKLR.mk k Q a γ d • rightMk Q γ i a y := by
  apply Subtype.ext
  change CycKLR.mk k Q a (γ + {i}) (inc Q γ i d * (y : C)) =
    quotientInc Q a γ i (CycKLR.mk k Q a γ d) * CycKLR.mk k Q a (γ + {i}) (y : C)
  rw [map_mul, quotientInc_mk]

def tensorMkBil : Left Q γ j →ₗ[k] Right Q γ i →ₗ[k] QuotientSource Q γ i j a :=
  LinearMap.mk₂ k (fun x y => BalancedTensor.tmul (leftMk Q γ j a x) (rightMk Q γ i a y))
    (fun x x' y => by rw [map_add, BalancedTensor.add_tmul])
    (fun c x y => by rw [map_smul, BalancedTensor.smul_tmul])
    (fun x y y' => by rw [map_add, BalancedTensor.tmul_add])
    (fun c x y => by rw [map_smul, BalancedTensor.tmul_smul])

def tensorMk : T →ₗ[k] QuotientSource Q γ i j a :=
  BalancedTensor.lift (tensorMkBil Q γ i j a)
    (fun x d y => by
      change BalancedTensor.tmul (leftMk Q γ j a (MulOpposite.op d • x)) (rightMk Q γ i a y) =
        BalancedTensor.tmul (leftMk Q γ j a x) (rightMk Q γ i a (d • y))
      rw [leftMk_balance, rightMk_balance, BalancedTensor.op_smul_tmul])

theorem tensorMk_tmul (x : Left Q γ j) (y : Right Q γ i) :
    tensorMk Q γ i j a (BalancedTensor.tmul x y) =
      BalancedTensor.tmul (leftMk Q γ j a x) (rightMk Q γ i a y) := rfl

theorem tensorMk_surjective : Function.Surjective (tensorMk Q γ i j a) := by
  intro t
  induction t using BalancedTensor.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add t s ht hs =>
    obtain ⟨t, rfl⟩ := ht
    obtain ⟨s, rfl⟩ := hs
    exact ⟨t + s, map_add _ _ _⟩
  | tmul x y =>
    obtain ⟨x, rfl⟩ := leftMk_surjective Q γ j a x
    obtain ⟨y, rfl⟩ := rightMk_surjective Q γ i a y
    exact ⟨BalancedTensor.tmul x y, rfl⟩

theorem tensorRelations_le_ker : tensorRelations Q γ i j a ≤ LinearMap.ker (tensorMk Q γ i j a) := by
  apply Submodule.span_le.2
  rintro z ⟨x, y, hx | hy, rfl⟩
  · change BalancedTensor.tmul (leftMk Q γ j a x) (rightMk Q γ i a y) = 0
    rw [(leftMk_zero_iff Q γ j a x).2 hx, BalancedTensor.zero_tmul]
  · change BalancedTensor.tmul (leftMk Q γ j a x) (rightMk Q γ i a y) = 0
    rw [(rightMk_zero_iff Q γ i a y).2 hy, BalancedTensor.tmul_zero]

abbrev PresentedSource := T ⧸ tensorRelations Q γ i j a

def presentedBil : Left Q γ j →ₗ[k] Right Q γ i →ₗ[k] PresentedSource Q γ i j a :=
  (BalancedTensor.mkBil k A (KLRAlgebra k Q γ) (Left Q γ j) (Right Q γ i)).compr₂
    (tensorRelations Q γ i j a).mkQ

def presentedLeft : QuotientLeft Q γ j a →ₗ[k] Right Q γ i →ₗ[k] PresentedSource Q γ i j a :=
  descend (leftMk Q γ j a) (leftMk_surjective Q γ j a) (presentedBil Q γ i j a) (by
    intro x hx
    apply LinearMap.ext
    intro y
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact Submodule.subset_span ⟨x, y, Or.inl ((leftMk_zero_iff Q γ j a x).1 hx), rfl⟩)

theorem presentedLeft_mk (x : Left Q γ j) (y : Right Q γ i) :
    presentedLeft Q γ i j a (leftMk Q γ j a x) y =
      (tensorRelations Q γ i j a).mkQ (BalancedTensor.tmul x y) :=
  congrArg (fun f : Right Q γ i →ₗ[k] PresentedSource Q γ i j a => f y)
    (descend_apply _ _ _ _ x)

def presentedQuotientBil : QuotientLeft Q γ j a →ₗ[k] QuotientRight Q γ i a →ₗ[k]
    PresentedSource Q γ i j a :=
  (descend (rightMk Q γ i a) (rightMk_surjective Q γ i a)
    (presentedLeft Q γ i j a).flip (by
      intro y hy
      apply LinearMap.ext
      intro x
      obtain ⟨x, rfl⟩ := leftMk_surjective Q γ j a x
      change presentedLeft Q γ i j a (leftMk Q γ j a x) y = 0
      rw [presentedLeft_mk]
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact Submodule.subset_span ⟨x, y, Or.inr ((rightMk_zero_iff Q γ i a y).1 hy), rfl⟩)).flip

theorem presentedQuotientBil_mk (x : Left Q γ j) (y : Right Q γ i) :
    presentedQuotientBil Q γ i j a (leftMk Q γ j a x) (rightMk Q γ i a y) =
      (tensorRelations Q γ i j a).mkQ (BalancedTensor.tmul x y) := by
  change (descend (rightMk Q γ i a) (rightMk_surjective Q γ i a)
    (presentedLeft Q γ i j a).flip _) (rightMk Q γ i a y) (leftMk Q γ j a x) = _
  exact (congrArg (fun f : QuotientLeft Q γ j a →ₗ[k] PresentedSource Q γ i j a =>
    f (leftMk Q γ j a x)) (descend_apply (rightMk Q γ i a)
      (rightMk_surjective Q γ i a) (presentedLeft Q γ i j a).flip _ y)).trans
        (presentedLeft_mk Q γ i j a x y)

def fromQuotientTensor : QuotientSource Q γ i j a →ₗ[k] PresentedSource Q γ i j a :=
  BalancedTensor.lift (presentedQuotientBil Q γ i j a) (by
    intro x d y
    obtain ⟨x, rfl⟩ := leftMk_surjective Q γ j a x
    obtain ⟨y, rfl⟩ := rightMk_surjective Q γ i a y
    obtain ⟨d, rfl⟩ := CycKLR.mk_surjective d
    rw [← leftMk_balance, ← rightMk_balance, presentedQuotientBil_mk, presentedQuotientBil_mk,
      BalancedTensor.op_smul_tmul])

theorem fromQuotientTensor_mk (z : T) :
    fromQuotientTensor Q γ i j a (tensorMk Q γ i j a z) = (tensorRelations Q γ i j a).mkQ z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => exact presentedQuotientBil_mk Q γ i j a x y

theorem tensorMk_ker_eq : LinearMap.ker (tensorMk Q γ i j a) = tensorRelations Q γ i j a := by
  apply le_antisymm _ (tensorRelations_le_ker Q γ i j a)
  intro z hz
  have he := fromQuotientTensor_mk Q γ i j a z
  change tensorMk Q γ i j a z = 0 at hz
  rw [hz, map_zero] at he
  exact (Submodule.Quotient.mk_eq_zero _).1 he.symm


def quotientCornerSub : Submodule k (CycKLR k Q a ((γ + {j}) + {i})) where
  carrier := {z | CycKLR.mk k Q a ((γ + {j}) + {i}) (oneConcat Q (γ + {j}) {i}) * z *
    CycKLR.mk k Q a ((γ + {j}) + {i}) (botOne Q (weightSquare γ i j)) = z}
  zero_mem' := by change _ * 0 * _ = 0; simp only [mul_zero, zero_mul]
  add_mem' hx hy := by change _ * (_ + _) * _ = _ + _; rw [mul_add, add_mul, hx, hy]
  smul_mem' c z hz := by change _ * (c • z) * _ = c • z; rw [mul_smul_comm, smul_mul_assoc, hz]
abbrev QuotientCorner := ↥(quotientCornerSub Q γ i j a)

def cornerMk : bimod Q (weightSquare γ i j) →ₗ[k] QuotientCorner Q γ i j a where
  toFun z := ⟨CycKLR.mk k Q a ((γ + {j}) + {i}) (z : U), by
    change _ * _ * _ = _
    rw [← map_mul, ← map_mul, (mem_bimod _).1 z.2]⟩
  map_add' z w := Subtype.ext (map_add _ _ _)
  map_smul' c z := Subtype.ext (map_smul _ _ _)

theorem cornerMk_surjective : Function.Surjective (cornerMk Q γ i j a) := by
  intro z
  obtain ⟨r, hr⟩ := CycKLR.mk_surjective (z : CycKLR k Q a ((γ + {j}) + {i}))
  refine ⟨project Q γ i j r, Subtype.ext ?_⟩
  change CycKLR.mk k Q a ((γ + {j}) + {i}) (oneConcat Q (γ + {j}) {i} * r * botOne Q _) = _
  rw [map_mul, map_mul, hr]
  exact z.2

theorem cornerMk_zero_iff (z : bimod Q (weightSquare γ i j)) :
    cornerMk Q γ i j a z = 0 ↔ z ∈ cornerIdeal Q γ i j a := by
  change _ ↔ (z : U) ∈ cycIdeal Q a ((γ + {j}) + {i})
  rw [← CycKLR.mk_eq_zero_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩


def quotientBotLinear : CycKLR k Q a (γ + {i}) →ₗ[k] CycKLR k Q a ((γ + {j}) + {i}) := by
  let f : C →ₗ[k] CycKLR k Q a ((γ + {j}) + {i}) :=
    { toFun := fun b => CycKLR.mk k Q a ((γ + {j}) + {i})
        (castKLR Q (weightSquare γ i j) (inc Q (γ + {i}) j b))
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun r x => by simp only [map_smul, RingHom.id_apply] }
  let q : C →ₗ[k] CycKLR k Q a (γ + {i}) := (CycKLR.mk k Q a (γ + {i})).toLinearMap
  have hf : LinearMap.ker q ≤ LinearMap.ker f := by
    intro b hb
    change CycKLR.mk k Q a ((γ + {j}) + {i})
      (castKLR Q (weightSquare γ i j) (inc Q (γ + {i}) j b)) = 0
    apply (CycKLR.mk_eq_zero_iff _).2
    apply (castKLR_mem_cycIdeal a (weightSquare γ i j) _).2
    have hb' : b ∈ cycIdeal Q a (γ + {i}) := (CycKLR.mk_eq_zero_iff b).1 hb
    exact inc_mem_cycIdeal Q a (γ + ({i} : Multiset I)) j (z := b) hb'
  exact descend q CycKLR.mk_surjective f hf

theorem quotientBotLinear_mk (b : C) :
    quotientBotLinear Q γ i j a (CycKLR.mk k Q a (γ + {i}) b) =
      CycKLR.mk k Q a ((γ + {j}) + {i}) (botConcat Q (weightSquare γ i j) (b ⊗ₜ 1)) :=
  descend_apply _ _ _ _ b

def quotientCornerLeft (b : CycKLR k Q a (γ + {j})) :
    QuotientCorner Q γ i j a →ₗ[k] QuotientCorner Q γ i j a where
  toFun z := ⟨quotientInc Q a (γ + {j}) i b * z.1, by
    obtain ⟨b, rfl⟩ := CycKLR.mk_surjective b
    obtain ⟨z, rfl⟩ := cornerMk_surjective Q γ i j a z
    rw [quotientInc_mk]
    change _ * (_ * CycKLR.mk k Q a ((γ + {j}) + {i}) (z : U)) * _ = _
    have h := (mem_bimod _).1 (cornerLeft Q γ i j b z).2
    change oneConcat Q (γ + {j}) {i} * (inc Q (γ + {j}) i b * (z : U)) *
      botOne Q (weightSquare γ i j) = inc Q (γ + {j}) i b * (z : U) at h
    simpa only [map_mul, cornerMk, LinearMap.coe_mk, AddHom.coe_mk] using
      congrArg (CycKLR.mk k Q a ((γ + {j}) + {i})) h⟩
  map_add' z w := Subtype.ext (mul_add _ _ _)
  map_smul' c z := Subtype.ext (mul_smul_comm _ _ _)

def quotientCornerRight (b : CycKLR k Q a (γ + {i})) :
    QuotientCorner Q γ i j a →ₗ[k] QuotientCorner Q γ i j a where
  toFun z := ⟨z.1 * quotientBotLinear Q γ i j a b, by
    obtain ⟨b, rfl⟩ := CycKLR.mk_surjective b
    obtain ⟨z, rfl⟩ := cornerMk_surjective Q γ i j a z
    rw [quotientBotLinear_mk]
    change _ * (CycKLR.mk k Q a ((γ + {j}) + {i}) (z : U) * _) * _ = _
    have h := (mem_bimod _).1 (cornerRight Q γ i j b z).2
    change oneConcat Q (γ + {j}) {i} * ((z : U) * botConcat Q (weightSquare γ i j) (b ⊗ₜ 1)) *
      botOne Q (weightSquare γ i j) = (z : U) * botConcat Q (weightSquare γ i j) (b ⊗ₜ 1) at h
    simpa only [map_mul, cornerMk, LinearMap.coe_mk, AddHom.coe_mk] using
      congrArg (CycKLR.mk k Q a ((γ + {j}) + {i})) h⟩
  map_add' z w := Subtype.ext (add_mul _ _ _)
  map_smul' c z := Subtype.ext (smul_mul_assoc _ _ _)

theorem cornerMk_left (b : A) (z : bimod Q (weightSquare γ i j)) :
    cornerMk Q γ i j a (cornerLeft Q γ i j b z) =
      quotientCornerLeft Q γ i j a (CycKLR.mk k Q a (γ + {j}) b) (cornerMk Q γ i j a z) := by
  apply Subtype.ext
  change CycKLR.mk k Q a ((γ + {j}) + {i}) (inc Q (γ + {j}) i b * (z : U)) =
    quotientInc Q a (γ + {j}) i (CycKLR.mk k Q a (γ + {j}) b) * _
  rw [quotientInc_mk, map_mul]
  rfl

theorem cornerMk_right (b : C) (z : bimod Q (weightSquare γ i j)) :
    cornerMk Q γ i j a (cornerRight Q γ i j b z) =
      quotientCornerRight Q γ i j a (CycKLR.mk k Q a (γ + {i}) b) (cornerMk Q γ i j a z) := by
  apply Subtype.ext
  change CycKLR.mk k Q a ((γ + {j}) + {i}) ((z : U) * botConcat Q (weightSquare γ i j) (b ⊗ₜ 1)) =
    _ * quotientBotLinear Q γ i j a (CycKLR.mk k Q a (γ + {i}) b)
  rw [quotientBotLinear_mk, map_mul]
  rfl

def quotientRightMul (b : CycKLR k Q a (γ + {i})) :
    QuotientRight Q γ i a →ₗ[CycKLR k Q a γ] QuotientRight Q γ i a where
  toFun y := ⟨y.1 * b, by
    change quotientInc Q a γ i 1 * (y.1 * b) = y.1 * b
    rw [← mul_assoc]
    exact congrArg (· * b) (CornerTensor.right_mem _ _ y)⟩
  map_add' y z := Subtype.ext (add_mul _ _ _)
  map_smul' d y := Subtype.ext (mul_assoc _ _ _)

def quotientRightAct (b : CycKLR k Q a (γ + {i})) :
    QuotientSource Q γ i j a →ₗ[CycKLR k Q a (γ + {j})] QuotientSource Q γ i j a :=
  BalancedTensor.mapRight (quotientRightMul Q γ i a b)

theorem tensorMk_left (b : A) (z : T) :
    tensorMk Q γ i j a (b • z) = CycKLR.mk k Q a (γ + {j}) b • tensorMk Q γ i j a z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add z w hz hw => simp only [smul_add, map_add, hz, hw]
  | tmul x y =>
    rw [BalancedTensor.smul_tmul', tensorMk_tmul, tensorMk_tmul, BalancedTensor.smul_tmul']
    congr 1
    exact Subtype.ext (map_mul _ _ _)

theorem tensorMk_right (b : C) (z : T) :
    tensorMk Q γ i j a (rightAct Q γ i j b z) =
      quotientRightAct Q γ i j a (CycKLR.mk k Q a (γ + {i}) b) (tensorMk Q γ i j a z) := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul x y =>
    change BalancedTensor.tmul (leftMk Q γ j a x) (rightMk Q γ i a (rightMul Q γ i b y)) =
      BalancedTensor.tmul (leftMk Q γ j a x)
        (quotientRightMul Q γ i a (CycKLR.mk k Q a (γ + {i}) b) (rightMk Q γ i a y))
    congr 1
    exact Subtype.ext (map_mul _ _ _)


/-- The impossible-removal block vanishes in the actual cyclotomic algebra. -/
theorem absent_quotient_corner (β : Multiset I) (added target : I)
    (habs : target ∉ β) (hne : target ≠ added) (z : CycKLR k Q a (β + {added})) :
    CycKLR.mk k Q a (β + {added}) (lastColourProjector β added target) * z *
      CycKLR.mk k Q a (β + {added}) (oneConcat Q β {added}) = 0 := by
  rw [lastColourProjector_of_absent β added target habs hne, map_zero, zero_mul, zero_mul]

end Categorification.KLR.KLRAlgebra.MixedCyclotomic
