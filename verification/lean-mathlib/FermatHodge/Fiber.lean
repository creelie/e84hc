import FermatHodge.Main

/-!
# The fibers of multiplication by `5`

For `5 ∣ m`, the solutions of `5 y = 5 x` in `ZMod m` are the five points `x + j m/5`.  Their sum
is `5 x`, and the sum of their representatives in `[0, m)` is the representative of `5 x` plus
`2 m`.  Multiplication by a unit carries the fiber of `x` to the fiber of `t x`.
-/

open Finset

noncomputable section

namespace FermatHodge

open Classical

set_option linter.unusedSectionVars false

variable {m : ℕ} [NeZero m]

/-- The fiber `{x + j m/5 : 0 ≤ j < 5}` of multiplication by `5` through `x`. -/
def fiber5 (x : ZMod m) : Finset (ZMod m) :=
  (range 5).image (fun j : ℕ => x + (j : ZMod m) * ((m / 5 : ℕ) : ZMod m))

/-- The `5`-standard sextuples `{x, x + m/5, ..., x + 4m/5, -5x}`. -/
def Std5 (A : Multiset (ZMod m)) : Prop := ∃ x : ZMod m, A = (fiber5 x).val + {-(5 * x)}

section

variable (h5 : 5 ∣ m)
include h5

lemma five_mul_d : (5 : ZMod m) * ((m / 5 : ℕ) : ZMod m) = 0 := by
  rw [show (5 : ZMod m) = ((5 : ℕ) : ZMod m) by norm_num, ← Nat.cast_mul,
    Nat.mul_div_cancel' h5, ZMod.natCast_self]

lemma d_pos : 0 < m / 5 := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m)) h5)
  (by norm_num)

lemma fiber5_inj : Set.InjOn (fun j : ℕ => (j : ZMod m) * ((m / 5 : ℕ) : ZMod m))
    (range 5 : Set ℕ) := by
  intro j hj j' hj' h
  simp only [coe_range, Set.mem_Iio] at hj hj'
  simp only at h
  have hlt : ∀ i, i < 5 → i * (m / 5) < m := fun i hi => by
    calc i * (m / 5) < 5 * (m / 5) := Nat.mul_lt_mul_of_pos_right hi (d_pos h5)
      _ = m := Nat.mul_div_cancel' h5
  rw [← Nat.cast_mul, ← Nat.cast_mul] at h
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt (hlt j hj), ZMod.val_natCast_of_lt (hlt j' hj')] at this
  exact Nat.eq_of_mul_eq_mul_right (d_pos h5) this

lemma card_fiber5 (x : ZMod m) : (fiber5 x).card = 5 := by
  rw [fiber5, Finset.card_image_of_injOn, card_range]
  intro j hj j' hj' h
  exact fiber5_inj h5 hj hj' (add_left_cancel h)

lemma mem_fiber5 {x y : ZMod m} : y ∈ fiber5 x ↔ 5 * y = 5 * x := by
  constructor
  · intro hy
    rw [fiber5, mem_image] at hy
    obtain ⟨j, _, rfl⟩ := hy
    rw [mul_add, mul_left_comm, five_mul_d h5, mul_zero, add_zero]
  · intro hy
    have h1 : (5 : ZMod m) * (y - x) = 0 := by rw [mul_sub, hy, sub_self]
    set n := (y - x).val with hn
    have hnat : ((5 * n : ℕ) : ZMod m) = 0 := by
      push_cast; rw [hn, ZMod.natCast_zmod_val]; exact h1
    rw [ZMod.natCast_eq_zero_iff] at hnat
    have hd : m / 5 ∣ n := by
      obtain ⟨k, hk⟩ := h5
      rw [hk, Nat.mul_div_cancel_left _ (by norm_num)]
      rw [hk] at hnat
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hnat
    obtain ⟨j, hj⟩ := hd
    have hjlt : j < 5 := by
      have hnlt : n < m := ZMod.val_lt _
      by_contra hc
      push Not at hc
      have : 5 * (m / 5) ≤ j * (m / 5) := Nat.mul_le_mul_right _ hc
      rw [Nat.mul_div_cancel' h5] at this
      rw [hj] at hnlt
      linarith [Nat.mul_comm (m / 5) j]
    rw [fiber5, mem_image]
    refine ⟨j, mem_range.mpr hjlt, ?_⟩
    have : y - x = ((m / 5 * j : ℕ) : ZMod m) := by
      rw [← hj, hn, ZMod.natCast_zmod_val]
    push_cast at this
    rw [mul_comm (j : ZMod m), ← this]; ring

lemma sum_fiber5 (x : ZMod m) : ∑ y ∈ fiber5 x, y = 5 * x := by
  rw [fiber5, Finset.sum_image (fun j hj j' hj' h => fiber5_inj h5 hj hj' (add_left_cancel h))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have := five_mul_d h5
  push_cast
  linear_combination (2 : ZMod m) * this

lemma mod_five_mul {a d r : ℕ} (hr : r < d) : (a * d + r) % (5 * d) = a % 5 * d + r := by
  have h1 : a * d + r = (a % 5 * d + r) + a / 5 * (5 * d) := by
    calc a * d + r = (a % 5 + 5 * (a / 5)) * d + r := by rw [Nat.mod_add_div]
      _ = _ := by ring
  rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt]
  have : a % 5 ≤ 4 := by omega
  calc a % 5 * d + r < 4 * d + d := by
        have := Nat.mul_le_mul_right d this
        omega
    _ = 5 * d := by ring

lemma sum_val_fiber5 (x : ZMod m) : ∑ y ∈ fiber5 x, y.val = (5 * x).val + 2 * m := by
  set d := m / 5 with hd
  have hm : m = 5 * d := (Nat.mul_div_cancel' h5).symm
  have hdpos : 0 < d := d_pos h5
  set v := x.val with hv
  set q := v / d
  set r := v % d
  have hvqr : v = q * d + r := by rw [mul_comm]; exact (Nat.div_add_mod v d).symm
  have hr : r < d := Nat.mod_lt _ hdpos
  have hq : q < 5 := by
    have : v < m := ZMod.val_lt x
    by_contra hc
    push Not at hc
    have : 5 * d ≤ q * d := Nat.mul_le_mul_right _ hc
    omega
  rw [fiber5, Finset.sum_image (fun j hj j' hj' h => fiber5_inj h5 hj hj' (add_left_cancel h))]
  have hterm : ∀ j : ℕ, (x + (j : ZMod m) * ((m / 5 : ℕ) : ZMod m)).val = (q + j) % 5 * d + r := by
    intro j
    have : x + (j : ZMod m) * ((m / 5 : ℕ) : ZMod m) = (((q + j) * d + r : ℕ) : ZMod m) := by
      rw [← ZMod.natCast_zmod_val x]
      push_cast
      rw [← hv, hvqr, ← hd]; push_cast; ring
    rw [this, ZMod.val_natCast, hm, mod_five_mul h5 hr]
  simp_rw [hterm]
  have h5x : (5 * x).val = 5 * r := by
    have : 5 * x = ((5 * r + q * (5 * d) : ℕ) : ZMod m) := by
      have e1 : 5 * r + q * (5 * d) = 5 * v := by rw [hvqr]; ring
      rw [e1]; push_cast; rw [hv, ZMod.natCast_zmod_val]
    rw [this, ZMod.val_natCast, ← hm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [h5x]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  interval_cases q <;> omega

lemma fiber5_mul (t : (ZMod m)ˣ) (x : ZMod m) :
    (fiber5 x).image (fun y => (t : ZMod m) * y) = fiber5 ((t : ZMod m) * x) := by
  ext y'
  rw [mem_image, mem_fiber5 h5]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_fiber5 h5] at hy
    rw [mul_left_comm, hy, mul_left_comm]
  · intro hy'
    refine ⟨((t⁻¹ : (ZMod m)ˣ) : ZMod m) * y', ?_, ?_⟩
    · rw [mem_fiber5 h5, mul_left_comm, hy', mul_left_comm (5 : ZMod m),
        Units.inv_mul_cancel_left]
    · exact Units.mul_inv_cancel_left t y'

lemma sum_val_fiber5_mul (t : (ZMod m)ˣ) (x : ZMod m) :
    ∑ y ∈ fiber5 x, ((t : ZMod m) * y).val = (5 * ((t : ZMod m) * x)).val + 2 * m := by
  rw [← sum_val_fiber5 h5, ← fiber5_mul h5, Finset.sum_image]
  intro a _ b _ hab
  have := congrArg (fun z => ((t⁻¹ : (ZMod m)ˣ) : ZMod m) * z) hab
  simp only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at this
  exact this

end

end FermatHodge
