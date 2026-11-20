/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Concat

/-!
# Algebra maps between corner rings

An algebra map `f : R → S` with `f E = E'` for idempotents `E`, `E'` restricts to a unital
algebra map `E R E → E' S E'` (`KLR.cornerHom`). If `P` is an idempotent of `S` and `E'` lies in
the corner `P S P`, then `E' S E'` is the corner of `E'` in the ring `P S P`
(`KLR.cornerNest`). These are used to transport block embeddings of KLR algebras
(`KLRAlgebra.BlockEmb`) into corners of quotients and of corner rings.

## Main definitions

* `KLR.cornerHom`: the restriction of an algebra map to corners.
* `KLR.cornerNest`: the corner of `E'` in `S` maps into the corner of `E'` in `P S P`.
-/

namespace Categorification.KLR

variable {k : Type*} [CommRing k] {R S : Type*} [Ring R] [Algebra k R] [Ring S] [Algebra k S]

theorem Corner.E_mul_val_mul_E {E : R} {hE : IsIdempotentElem E} (a : hE.Corner) :
    E * a.val * E = a.val := by
  rw [Corner.E_mul_val, Corner.val_mul_E]

/-- **The restriction of an algebra map to corners**: `f : R → S` with `f E = E'` restricts to
a unital algebra map `E R E → E' S E'`. -/
noncomputable def cornerHom (f : R →ₐ[k] S) {E : R} (hE : IsIdempotentElem E) {E' : S}
    (hE' : IsIdempotentElem E') (h : f E = E') : hE.Corner →ₐ[k] hE'.Corner where
  toFun a := Corner.mk (f a.val) (by rw [← h, ← map_mul, ← map_mul, Corner.E_mul_val_mul_E])
  map_one' := Corner.ext (by simp [h])
  map_mul' a b := Corner.ext (by simp)
  map_zero' := Corner.ext (by simp)
  map_add' a b := Corner.ext (by simp)
  commutes' c := Corner.ext (by simp [h])

@[simp] theorem val_cornerHom (f : R →ₐ[k] S) {E : R} (hE : IsIdempotentElem E) {E' : S}
    (hE' : IsIdempotentElem E') (h : f E = E') (a : hE.Corner) :
    (cornerHom f hE hE' h a).val = f a.val := rfl

/-- An idempotent `E'` of the corner ring `P S P` is an idempotent of `S`. -/
theorem isIdempotentElem_val {P : S} {hP : IsIdempotentElem P} {E' : hP.Corner}
    (hE' : IsIdempotentElem E') : IsIdempotentElem E'.val := by
  change E'.val * E'.val = E'.val
  rw [← Corner.val_mul, hE'.eq]

/-- **Nested corners**: for an idempotent `E'` of the corner ring `P S P`, the corner of `E'`
in `S` maps into the corner of `E'` in `P S P`. -/
noncomputable def cornerNest {P : S} {hP : IsIdempotentElem P} {E' : hP.Corner}
    (hE' : IsIdempotentElem E') : (isIdempotentElem_val hE').Corner →ₐ[k] hE'.Corner where
  toFun a := Corner.mk
    (Corner.mk a.val (by
      have ha := Corner.E_mul_val_mul_E a
      have h1 : P * E'.val = E'.val := Corner.E_mul_val E'
      have h2 : E'.val * P = E'.val := Corner.val_mul_E E'
      calc P * a.val * P = P * (E'.val * a.val * E'.val) * P := by rw [ha]
        _ = (P * E'.val) * a.val * (E'.val * P) := by simp only [mul_assoc]
        _ = a.val := by rw [h1, h2, ha]))
    (Corner.ext (by simp [Corner.E_mul_val_mul_E]))
  map_one' := Corner.ext (Corner.ext rfl)
  map_mul' a b := Corner.ext (Corner.ext rfl)
  map_zero' := Corner.ext (Corner.ext rfl)
  map_add' a b := Corner.ext (Corner.ext rfl)
  commutes' c := Corner.ext (Corner.ext (by
    change algebraMap k S c * E'.val = (algebraMap k hP.Corner c * E').val
    rw [Corner.val_mul, Corner.val_algebraMap, mul_assoc, Corner.E_mul_val]))

@[simp] theorem val_val_cornerNest {P : S} {hP : IsIdempotentElem P} {E' : hP.Corner}
    (hE' : IsIdempotentElem E') (a : (isIdempotentElem_val hE').Corner) :
    (cornerNest (k := k) hE' a).val.val = a.val := rfl

end Categorification.KLR
