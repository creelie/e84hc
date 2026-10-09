import FermatHodge.Fiber

/-!
# Hodge sextuples

For `m` prime to `6`, a multiset of six elements of `ZMod m` with sum zero, whose representatives
have a sum independent of the unit `t`, contains a pair `a, -a` or is `5`-standard.

At the maximal order `e` the core dichotomy leaves a full line along `K_5`.  If `25 ∣ e` the line
has five points, fills a fiber of multiplication by `5`, and the sixth entry is `-5x`.  If
`5 ∥ e` the line has four points, missing one point `y₀` of the fiber; replacing the four by the
two points `5x` and `-y₀` gives a Hodge quadruple, which has a pair, and each possible pair gives
either a pair in the sextuple or the `5`-standard form.
-/

open Finset

noncomputable section

namespace FermatHodge

open Classical

set_option linter.unusedSectionVars false

section helpers

/-- If `u ≡ 1` modulo `d` and `d a = 0`, then `u a = a`. -/
lemma sub_one_mul_eq_zero {n d : ℕ} [NeZero n] {u : ZMod n} (hu : (u.cast : ZMod d) = 1)
    {a : ZMod n} (ha : (d : ZMod n) * a = 0) : (u - 1) * a = 0 := by
  rw [ZMod.cast_eq_val] at hu
  have h1 : (((u.val : ℤ) - 1 : ℤ) : ZMod d) = 0 := by push_cast; rw [hu, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  obtain ⟨q, hq⟩ := h1
  have h2 : u - 1 = (d : ZMod n) * q := by
    have : (((u.val : ℤ) - 1 : ℤ) : ZMod n) = (((d : ℤ) * q : ℤ) : ZMod n) := by rw [hq]
    push_cast at this
    rwa [ZMod.natCast_zmod_val] at this
  rw [h2, mul_comm (d : ZMod n), mul_assoc, ha, mul_zero]

lemma five_mul_line {e : ℕ} [NeZero e] (h5 : 5 ∣ e) {k : (ZMod e)ˣ} (hk : k ∈ Kq e 5) :
    (5 : ZMod e) * ((k : ZMod e) - 1) = 0 := by
  have hk' := cast_mem_Kq h5 hk
  rw [ZMod.castHom_apply] at hk'
  have ha : ((e / 5 : ℕ) : ZMod e) * 5 = 0 := by
    rw [show (5 : ZMod e) = ((5 : ℕ) : ZMod e) by norm_num, ← Nat.cast_mul,
      Nat.div_mul_cancel h5, ZMod.natCast_self]
  rw [mul_comm]
  exact sub_one_mul_eq_zero hk' ha

lemma five_mul_kap {m e : ℕ} [NeZero m] (hem : e ∣ m) (y : ZMod e) :
    5 * kap hem y = kap hem (5 * y) := by
  have := map_nsmul (kap hem) 5 y
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at this
  exact this.symm

lemma eq_zero_of_coprime_mul {m k : ℕ} [NeZero m] (hk : Nat.Coprime k m) {z : ZMod m}
    (h : (k : ZMod m) * z = 0) : z = 0 := by
  set u := ZMod.unitOfCoprime k hk
  have hu : (u : ZMod m) = k := ZMod.coe_unitOfCoprime k hk
  calc z = ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * ((u : ZMod m) * z) :=
        (Units.inv_mul_cancel_left u z).symm
    _ = 0 := by rw [hu, h, mul_zero]

end helpers

variable {m : ℕ} [NeZero m]

lemma line_in_fiber {e : ℕ} [NeZero e] (hem : e ∣ m) (h5 : 5 ∣ e) (w : (ZMod e)ˣ)
    {k : (ZMod e)ˣ} (hk : k ∈ Kq e 5) :
    kap hem ((w * k : (ZMod e)ˣ) : ZMod e) ∈ fiber5 (kap hem (w : ZMod e)) := by
  rw [mem_fiber5 (h5.trans hem), five_mul_kap, five_mul_kap]
  congr 1
  rw [Units.val_mul]
  have := five_mul_line h5 hk
  linear_combination (w : ZMod e) * this

/-- **Hodge sextuples.**  For `m` prime to `6`, six elements of `ZMod m` with sum zero whose
representatives have a sum independent of the unit `t` contain a pair `a, -a` or form a
`5`-standard sextuple. -/
theorem sextuple (hm2 : ¬2 ∣ m) (hm3 : ¬3 ∣ m) (hB : BernoulliNV) (A : Multiset (ZMod m))
    (hcard : Multiset.card A = 6) (hA : A.sum = 0) (h : ℕ)
    (hH : ∀ t : (ZMod m)ˣ, (A.map fun a => ((t : ZMod m) * a).val).sum = h) :
    (∃ a ∈ A, -a ∈ A) ∨ Std5 A := by
  have hne : A ≠ 0 := by rintro rfl; simp at hcard
  rcases pair_or_pos A hne with hpair | ⟨e, hNZ, hem, hmax, x0, hx⟩
  · exact Or.inl hpair
  have he2 : ¬2 ∣ e := fun h2 => hm2 (h2.trans hem)
  have he3 : ¬3 ∣ e := fun h3 => hm3 (h3.trans hem)
  obtain ⟨p, hp57, hpe, w, hw⟩ := line_exists hm2 hm3 hem A hA (by omega) h hH hmax hB hx
  have hK := neg_one_not_mem_of_line (cntF_neg hem A) hw
  have hge := line_mass_ge hK (cntF_neg hem A) hw
  have hle : ∑ z, |cntF hem A z| ≤ 12 := by
    have := mass_cntF_le_card hem A
    rw [hcard] at this; push_cast at this; linarith
  rcases hp57 with rfl | rfl
  swap
  · -- a line along `K_7` is impossible
    exfalso
    rcases card_Kq_cases (by norm_num) hpe with hc | hc
    · rw [hc] at hge; push_cast at hge; linarith
    · rw [show (7 : ℕ) - 1 = 6 from rfl] at hc
      refine kill_line hpe he2 he3 (Or.inr hc) (cntF_neg hem A) hw
        (by rw [hc]; push_cast; linarith) (fun hs => sum_cntF_eq_zero hem A hA ?_)
      rw [hs, hc, hcard]
  -- a line along `K_5`
  have h5m : 5 ∣ m := hpe.trans hem
  set x := kap hem (w : ZMod e) with hxdef
  set L := (Kf (Kq e 5)).image (fun k => kap hem ((w * k : (ZMod e)ˣ) : ZMod e)) with hL
  have hLinj : Set.InjOn (fun k => kap hem ((w * k : (ZMod e)ˣ) : ZMod e)) (Kf (Kq e 5)) := by
    intro k _ k' _ hkk
    exact mul_left_cancel (kap_unit_inj hem hkk)
  have hLcard : L.card = Nat.card (Kq e 5) := by rw [hL, card_image_of_injOn hLinj, card_Kf]
  have hLfib : L ⊆ fiber5 x := by
    intro y hy
    rw [hL, mem_image] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact line_in_fiber hem hpe w (mem_Kf.mp hk)
  have hLA : L.val ≤ A := by
    rw [Multiset.le_iff_subset L.nodup]
    intro y hy
    rw [Finset.mem_val, hL, mem_image] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    have := hw k (mem_Kf.mp hk)
    unfold cntF at this
    apply Multiset.count_pos.mp
    omega
  set R := A - L.val with hR
  have hAR : A = L.val + R := (add_tsub_cancel_of_le hLA).symm
  have hRcard : L.card + Multiset.card R = 6 := by
    rw [← hcard, hAR, Multiset.card_add, Finset.card_val]
  have hLsum : ∀ (f : ZMod m → ZMod m), (L.val.map f).sum = ∑ y ∈ L, f y := fun f =>
    (Finset.sum_eq_multiset_sum L f).symm
  rcases card_Kq_cases (by norm_num) hpe with hc | hc
  · -- `25 ∣ e`: the line fills the fiber
    right
    have hLeq : L = fiber5 x :=
      Finset.eq_of_subset_of_card_le hLfib (by rw [card_fiber5 h5m, hLcard, hc])
    have hR1 : Multiset.card R = 1 := by rw [hLcard, hc] at hRcard; omega
    obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp hR1
    have hsumA : 5 * x + b = 0 := by
      have := hA
      rw [hAR, hb, Multiset.sum_add, Multiset.sum_singleton] at this
      have h2 : L.val.sum = ∑ y ∈ L, y := by simp
      rw [h2, hLeq, sum_fiber5 h5m] at this
      exact this
    refine ⟨x, ?_⟩
    rw [hAR, hb, hLeq]
    congr 2
    linear_combination hsumA
  · -- `5 ∥ e`: the line misses one point of the fiber
    rw [show (5 : ℕ) - 1 = 4 from rfl] at hc
    have hR2 : Multiset.card R = 2 := by rw [hLcard, hc] at hRcard; omega
    obtain ⟨b, c, hbc⟩ := Multiset.card_eq_two.mp hR2
    have hbA : b ∈ A := by rw [hAR, hbc]; simp
    have hcA : c ∈ A := by rw [hAR, hbc]; simp
    have hsd : (fiber5 x \ L).card = 1 := by
      rw [Finset.card_sdiff_of_subset hLfib, card_fiber5 h5m, hLcard, hc]
    obtain ⟨y0, hy0⟩ := Finset.card_eq_one.mp hsd
    have hy0m : y0 ∈ fiber5 x \ L := by rw [hy0]; exact mem_singleton_self y0
    have hy0F : y0 ∈ fiber5 x := (mem_sdiff.mp hy0m).1
    have hy0L : y0 ∉ L := (mem_sdiff.mp hy0m).2
    have hfib : fiber5 x = insert y0 L := by
      ext y
      constructor
      · intro hy
        by_cases hyL : y ∈ L
        · exact mem_insert_of_mem hyL
        · have : y ∈ fiber5 x \ L := mem_sdiff.mpr ⟨hy, hyL⟩
          rw [hy0, mem_singleton] at this
          rw [this]; exact mem_insert_self _ _
      · intro hy
        rcases mem_insert.mp hy with rfl | hyL
        · exact hy0F
        · exact hLfib hyL
    have he5 : e ≠ 5 := by
      rintro rfl
      apply hK
      rw [Kq_of_dvd (dvd_refl 5), mem_Nd]
      decide
    have h5x : 5 * x ≠ 0 := by
      intro h0
      rw [hxdef, five_mul_kap] at h0
      have h1 : (5 : ZMod e) * (w : ZMod e) = 0 := kap_inj hem (h0.trans (map_zero _).symm)
      have h2 : (5 : ZMod e) = 0 := by
        have := congrArg (· * ((w⁻¹ : (ZMod e)ˣ) : ZMod e)) h1
        simp only [zero_mul, mul_assoc, Units.mul_inv, mul_one] at this
        exact this
      rw [show (5 : ZMod e) = ((5 : ℕ) : ZMod e) by norm_num, ZMod.natCast_eq_zero_iff] at h2
      exact he5 (Nat.dvd_antisymm h2 hpe)
    have hy00 : y0 ≠ 0 := by
      intro h0; apply h5x
      have := (mem_fiber5 h5m).mp hy0F
      rw [h0, mul_zero] at this; exact this.symm
    have hcop2 : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm2
    have hcop4 : Nat.Coprime 4 m := by
      have := Nat.Coprime.pow_left 2 hcop2; simpa using this
    have two_zero : ∀ z : ZMod m, 2 * z = 0 → z = 0 := fun z hz =>
      eq_zero_of_coprime_mul hcop2 (by push_cast; exact hz)
    have hxy : 5 * x ≠ y0 := by
      intro h0
      have h1 := (mem_fiber5 h5m).mp hy0F
      rw [← h0] at h1
      have h4 : ((4 : ℕ) : ZMod m) * (5 * x) = 0 := by push_cast; linear_combination h1
      exact h5x (eq_zero_of_coprime_mul hcop4 h4)
    -- sums over `A`
    have hmapA : ∀ f : ZMod m → ℕ, (A.map f).sum = ∑ y ∈ L, f y + f b + f c := by
      intro f
      rw [hAR, hbc, Multiset.map_add, Multiset.sum_add, ← Finset.sum_eq_multiset_sum]
      simp [add_assoc]
    have hsumA : 5 * x - y0 + b + c = 0 := by
      have := hA
      rw [hAR, hbc, Multiset.sum_add] at this
      have h2 : L.val.sum = ∑ y ∈ L, y := by simp
      have h3 : ∑ y ∈ L, y = 5 * x - y0 := by
        have := sum_fiber5 h5m x
        rw [hfib, Finset.sum_insert hy0L] at this
        linear_combination this
      rw [h2, h3] at this
      simp at this
      linear_combination this
    -- the moved quadruple `{5x, b, c, -y0}`
    set Q : Multiset (ZMod m) := (5 * x) ::ₘ b ::ₘ c ::ₘ {-y0} with hQ
    have hQcard : Multiset.card Q = 4 := by simp [hQ]
    have hQsum : Q.sum = 0 := by simp [hQ]; linear_combination hsumA
    have hQH : ∀ t : (ZMod m)ˣ, (Q.map fun a => ((t : ZMod m) * a).val).sum = h - m := by
      intro t
      have hAt := hH t
      rw [hmapA] at hAt
      have hF := sum_val_fiber5_mul h5m t x
      rw [hfib, Finset.sum_insert hy0L] at hF
      have hty0 : (t : ZMod m) * y0 ≠ 0 := by
        intro h0; apply hy00
        have := congrArg (((t⁻¹ : (ZMod m)ˣ) : ZMod m) * ·) h0
        simp only [Units.inv_mul_cancel_left, mul_zero] at this
        exact this
      have hneg : ((t : ZMod m) * -y0).val = m - ((t : ZMod m) * y0).val := by
        rw [mul_neg, ZMod.neg_val, if_neg hty0]
      have hlt : ((t : ZMod m) * y0).val < m := ZMod.val_lt _
      have h5t : ((t : ZMod m) * (5 * x)).val = (5 * ((t : ZMod m) * x)).val := by
        rw [mul_left_comm]
      simp only [hQ, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
        Multiset.sum_singleton]
      rw [h5t, hneg]
      omega
    obtain ⟨q, hq, hnq⟩ := quadruple hm2 hm3 hB Q hQcard hQsum (h - m) hQH
    have hStd : b = y0 ∨ c = y0 ∨ b = -(5 * x) ∨ c = -(5 * x) → Std5 A := by
      intro hcase
      have hR' : ({b, c} : Multiset (ZMod m)) = {y0, -(5 * x)} := by
        rcases hcase with h1 | h1 | h1 | h1
        · have h2 : c = -(5 * x) := by rw [h1] at hsumA; linear_combination hsumA
          rw [h1, h2]
        · have h2 : b = -(5 * x) := by rw [h1] at hsumA; linear_combination hsumA
          rw [h1, h2, Multiset.pair_comm]
        · have h2 : c = y0 := by rw [h1] at hsumA; linear_combination hsumA
          rw [h1, h2, Multiset.pair_comm]
        · have h2 : b = y0 := by rw [h1] at hsumA; linear_combination hsumA
          rw [h1, h2]
      refine ⟨x, ?_⟩
      rw [hAR, hbc, hR', hfib, Finset.insert_val_of_notMem hy0L, Multiset.insert_eq_cons,
        Multiset.add_cons, Multiset.cons_add]
    simp only [hQ, Multiset.mem_cons, Multiset.mem_singleton] at hq hnq
    rcases hq with h1 | h1 | h1 | h1 <;> rw [h1] at hnq <;> rcases hnq with h' | h' | h' | h'
    all_goals first
      | exact Or.inr (hStd (Or.inl (by linear_combination -h')))
      | exact Or.inr (hStd (Or.inr (Or.inl (by linear_combination -h'))))
      | exact Or.inr (hStd (Or.inr (Or.inr (Or.inl (by linear_combination -h')))))
      | exact Or.inr (hStd (Or.inr (Or.inr (Or.inr (by linear_combination -h')))))
      | exact Or.inl ⟨b, hbA, by rw [h']; first | exact hbA | exact hcA⟩
      | exact Or.inl ⟨c, hcA, by rw [h']; first | exact hbA | exact hcA⟩
      | exact absurd (two_zero _ (by linear_combination -h')) h5x
      | exact absurd (by linear_combination -h' : 5 * x = y0) hxy
      | exact absurd (two_zero _ (by linear_combination h')) hy00

end FermatHodge
