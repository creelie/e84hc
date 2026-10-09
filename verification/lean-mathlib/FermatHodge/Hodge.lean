import FermatHodge.Level

/-!
# The counting function and the Hodge condition

For a multiset `A` of elements of `ZMod m` and a divisor `e` of `m`, `cntF` counts, for each unit
`z` of `ZMod e`, the copies of `(m / e) z` in `A` minus the copies of `-(m / e) z`.  If `A` satisfies
the Hodge condition (the sum of the representatives of `t A` does not depend on the unit `t`) and
no element of `A` has order above `e`, then `cntF` is orthogonal to every primitive character mod
`e`, provided the Bernoulli sums `∑ χ(s) s` of the odd primitive characters do not vanish.
-/

open Finset

noncomputable section

namespace FermatHodge

open Classical

set_option linter.unusedSectionVars false

variable {m e : ℕ} [NeZero m] [NeZero e]

/-- The counting function at level `e`. -/
def cntF (hem : e ∣ m) (A : Multiset (ZMod m)) (z : (ZMod e)ˣ) : ℤ :=
  (A.count (kap hem (z : ZMod e)) : ℤ) - A.count (kap hem ((-z : (ZMod e)ˣ) : ZMod e))

lemma cntF_neg (hem : e ∣ m) (A : Multiset (ZMod m)) (z : (ZMod e)ˣ) :
    cntF hem A (-z) = -cntF hem A z := by
  unfold cntF; rw [neg_neg]; ring

/-- A multiset sum as a sum over `ZMod m` weighted by multiplicities. -/
lemma msum_eq (A : Multiset (ZMod m)) {M : Type*} [AddCommMonoid M] (f : ZMod m → M) :
    (A.map f).sum = ∑ x, A.count x • f x := by
  rw [Finset.sum_multiset_map_count]
  apply Finset.sum_subset (subset_univ _)
  intro x _ hx
  rw [Multiset.mem_toFinset] at hx
  rw [Multiset.count_eq_zero.mpr hx, zero_smul]

lemma sum_count (A : Multiset (ZMod m)) : ∑ x, A.count x = Multiset.card A := by
  have := msum_eq A (fun _ => (1 : ℕ))
  simp only [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one] at this
  exact this.symm

lemma neg_inv_units (w : (ZMod e)ˣ) : (-w)⁻¹ = -w⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])

lemma kap_unit_inj (hem : e ∣ m) :
    Function.Injective (fun z : (ZMod e)ˣ => kap hem (z : ZMod e)) :=
  fun _ _ h => Units.ext (kap_inj hem h)

/-- The character step: the Hodge condition kills the twisted count for an odd primitive
character whose Bernoulli sum is nonzero. -/
theorem char_step (hem : e ∣ m) (A : Multiset (ZMod m)) (h : ℕ)
    (hH : ∀ t : (ZMod m)ˣ, (A.map fun a => ((t : ZMod m) * a).val).sum = h)
    (hmax : ∀ a ∈ A, addOrderOf a ≤ e)
    (χ : DirichletCharacter ℂ e) (hprim : χ.IsPrimitive) (hodd : χ.Odd) (hB : Bsum χ ≠ 0) :
    ∑ z : (ZMod e)ˣ, (A.count (kap hem (z : ZMod e)) : ℂ) * χ ((z : ZMod e)⁻¹) = 0 := by
  -- the character sums to zero over the units mod `m`
  have hS : ∑ t : (ZMod m)ˣ, χ ((t : ZMod m).cast) = 0 := by
    have h1 : ∑ t : (ZMod m)ˣ, χ ((t : ZMod m).cast) = -∑ t : (ZMod m)ˣ, χ ((t : ZMod m).cast) := by
      rw [← Finset.sum_neg_distrib]
      refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun t => ?_)
      simp only [Equiv.neg_apply, Units.val_neg, ZMod.cast_neg hem]
      rw [hodd.eval_neg, neg_neg]
    linear_combination (1 / 2 : ℂ) * h1
  -- the Hodge condition with weights
  have hcnt : ∀ t : (ZMod m)ˣ, ∑ x, (A.count x : ℂ) * (((t : ZMod m) * x).val : ℂ) = h := by
    intro t
    have := congrArg (fun n : ℕ => (n : ℂ)) (hH t)
    rw [msum_eq] at this
    push_cast at this
    simpa [nsmul_eq_mul] using this
  have key : ∑ x, (A.count x : ℂ) * Gsum hem χ x = 0 := by
    unfold Gsum
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ t : (ZMod m)ˣ, ∑ x, (A.count x : ℂ) * (χ ((t : ZMod m).cast) *
        (((t : ZMod m) * x).val : ℂ)) = χ ((t : ZMod m).cast) * h := by
      intro t
      rw [← hcnt t, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => by ring)
    rw [Finset.sum_congr rfl (fun t _ => h2 t), ← Finset.sum_mul, hS, zero_mul]
  -- only elements of order `e` contribute
  have hsplit : ∑ x, (A.count x : ℂ) * Gsum hem χ x =
      ∑ z : (ZMod e)ˣ, (A.count (kap hem (z : ZMod e)) : ℂ) * Gsum hem χ (kap hem (z : ZMod e)) := by
    refine (Fintype.sum_of_injective _ (kap_unit_inj hem) _ _ (fun x hx => ?_)
      (fun z => rfl)).symm
    by_cases hxA : x ∈ A
    · have hed : ¬e ∣ addOrderOf x := by
        intro hd
        have hpos : 0 < addOrderOf x := addOrderOf_pos x
        have hle := hmax x hxA
        have heq : addOrderOf x = e := le_antisymm hle (Nat.le_of_dvd hpos hd)
        obtain ⟨z, hz⟩ := exists_kap_unit hem heq
        exact hx ⟨z, hz⟩
      rw [Gsum_eq_zero hem χ hprim hed, mul_zero]
    · rw [Multiset.count_eq_zero.mpr hxA, Nat.cast_zero, zero_mul]
  rw [hsplit] at key
  simp_rw [Gsum_kap] at key
  have hC : (Nat.card (ZMod.unitsMap hem).ker : ℂ) * ((m / e : ℕ) : ℂ) ≠ 0 := by
    have h1 : 0 < Nat.card (ZMod.unitsMap hem).ker := Nat.card_pos
    have h2 := div_pos_of_dvd (m := m) hem
    exact mul_ne_zero (by exact_mod_cast h1.ne') (by exact_mod_cast h2.ne')
  have h3 : (Nat.card (ZMod.unitsMap hem).ker : ℂ) * ((m / e : ℕ) : ℂ) * Bsum χ *
      ∑ z : (ZMod e)ˣ, (A.count (kap hem (z : ZMod e)) : ℂ) * χ ((z : ZMod e)⁻¹) = 0 := by
    rw [← key, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => by ring)
  rcases mul_eq_zero.mp h3 with h4 | h4
  · rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 hC
    · exact absurd h5 hB
  · exact h4

/-- The counting function is orthogonal to every primitive character. -/
theorem fourier_cntF (hem : e ∣ m) (A : Multiset (ZMod m)) (h : ℕ)
    (hH : ∀ t : (ZMod m)ˣ, (A.map fun a => ((t : ZMod m) * a).val).sum = h)
    (hmax : ∀ a ∈ A, addOrderOf a ≤ e)
    (hB : ∀ χ : DirichletCharacter ℂ e, χ.IsPrimitive → χ.Odd → Bsum χ ≠ 0)
    (χ : DirichletCharacter ℂ e) (hprim : χ.IsPrimitive) :
    ∑ w, (cntF hem A w : ℂ) * χ ((w : ZMod e)⁻¹) = 0 := by
  set T := ∑ z : (ZMod e)ˣ, (A.count (kap hem (z : ZMod e)) : ℂ) * χ ((z : ZMod e)⁻¹) with hT
  have hT' : ∑ z : (ZMod e)ˣ, (A.count (kap hem ((-z : (ZMod e)ˣ) : ZMod e)) : ℂ) *
      χ ((z : ZMod e)⁻¹) = ∑ z : (ZMod e)ˣ, (A.count (kap hem (z : ZMod e)) : ℂ) *
      χ (-(z : ZMod e)⁻¹) := by
    refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun z => ?_)
    simp only [Equiv.neg_apply]
    rw [ZMod.inv_coe_unit, ZMod.inv_coe_unit, neg_inv_units]
    simp only [Units.val_neg, neg_neg]
  have hsplit : ∑ w, (cntF hem A w : ℂ) * χ ((w : ZMod e)⁻¹) =
      T - ∑ z : (ZMod e)ˣ, (A.count (kap hem ((-z : (ZMod e)ˣ) : ZMod e)) : ℂ) *
        χ ((z : ZMod e)⁻¹) := by
    rw [hT, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    unfold cntF; push_cast; ring
  rw [hsplit, hT']
  rcases χ.even_or_odd with hev | hodd
  · simp_rw [hev.eval_neg]; rw [hT, sub_self]
  · simp_rw [hodd.eval_neg]
    have := char_step hem A h hH hmax χ hprim hodd (hB χ hprim hodd)
    rw [← hT] at this
    simp only [mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add, ← hT, this, add_zero]

/-- The mass of the counting function is at most twice the size of `A`. -/
lemma sum_count_kap_le (hem : e ∣ m) (A : Multiset (ZMod m)) :
    ∑ z : (ZMod e)ˣ, A.count (kap hem (z : ZMod e)) ≤ Multiset.card A := by
  rw [← sum_count A, ← Finset.sum_image (f := fun x => A.count x)
    (fun a _ b _ h => kap_unit_inj hem h)]
  exact Finset.sum_le_sum_of_subset (subset_univ _)

lemma sum_count_kap_neg (hem : e ∣ m) (A : Multiset (ZMod m)) :
    ∑ z : (ZMod e)ˣ, A.count (kap hem ((-z : (ZMod e)ˣ) : ZMod e)) =
      ∑ z : (ZMod e)ˣ, A.count (kap hem (z : ZMod e)) :=
  Fintype.sum_equiv (Equiv.neg _) _ _ (fun z => rfl)

lemma mass_cntF_le (hem : e ∣ m) (A : Multiset (ZMod m)) :
    ∑ z, |cntF hem A z| ≤ 2 * (∑ z : (ZMod e)ˣ, A.count (kap hem (z : ZMod e)) : ℕ) := by
  calc ∑ z, |cntF hem A z| ≤ ∑ z : (ZMod e)ˣ, ((A.count (kap hem (z : ZMod e)) : ℤ) +
        A.count (kap hem ((-z : (ZMod e)ˣ) : ZMod e))) := by
        refine Finset.sum_le_sum (fun z _ => ?_)
        unfold cntF
        refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> omega
    _ = 2 * (∑ z : (ZMod e)ˣ, A.count (kap hem (z : ZMod e)) : ℕ) := by
        rw [Finset.sum_add_distrib]
        have := sum_count_kap_neg hem A
        rw [← Nat.cast_sum, ← Nat.cast_sum, this]; push_cast; ring

lemma mass_cntF_le_card (hem : e ∣ m) (A : Multiset (ZMod m)) :
    ∑ z, |cntF hem A z| ≤ 2 * Multiset.card A := by
  have h1 := mass_cntF_le hem A
  have h2 := sum_count_kap_le hem A
  have h3 : ((∑ z : (ZMod e)ˣ, A.count (kap hem (z : ZMod e)) : ℕ) : ℤ) ≤ Multiset.card A := by
    exact_mod_cast h2
  linarith

/-- If the mass is as large as possible, every element of `A` comes from a unit, and the
weighted sum of the counting function vanishes when `A` sums to zero. -/
theorem sum_cntF_eq_zero (hem : e ∣ m) (A : Multiset (ZMod m)) (hA : A.sum = 0)
    (hmass : ∑ z, |cntF hem A z| = 2 * Multiset.card A) :
    ∑ z, (cntF hem A z : ZMod e) * (z : ZMod e) = 0 := by
  set N := ∑ z : (ZMod e)ˣ, A.count (kap hem (z : ZMod e)) with hN
  have hNc : N = Multiset.card A := by
    have h1 := mass_cntF_le hem A
    have h2 := sum_count_kap_le hem A
    have h3 : (Multiset.card A : ℤ) ≤ N := by linarith
    exact le_antisymm h2 (by exact_mod_cast h3)
  set I := univ.image (fun z : (ZMod e)ˣ => kap hem (z : ZMod e)) with hI
  have hIsum : ∑ x ∈ I, A.count x = N := by
    rw [hI, Finset.sum_image (fun a _ b _ h => kap_unit_inj hem h)]
  have hout : ∀ x ∉ I, A.count x = 0 := by
    have h1 := Finset.sum_sdiff (s₁ := I) (s₂ := univ) (f := fun x => A.count x) (subset_univ _)
    rw [sum_count, hIsum, hNc] at h1
    have h2 : ∑ x ∈ univ \ I, A.count x = 0 := by omega
    intro x hx
    exact (Finset.sum_eq_zero_iff.mp h2) x (by simp [hx])
  -- `A` sums to zero, so the weighted sum of units vanishes
  have hsum1 : ∑ z : (ZMod e)ˣ, A.count (kap hem (z : ZMod e)) • (z : ZMod e) = 0 := by
    apply kap_inj hem
    rw [map_sum, map_zero]
    simp_rw [map_nsmul]
    rw [← Finset.sum_image (f := fun x => A.count x • x)
      (fun a _ b _ h => kap_unit_inj hem h), ← hI]
    rw [Finset.sum_subset (subset_univ I) (fun x _ hx => by rw [hout x hx, zero_smul])]
    rw [← msum_eq, Multiset.map_id', hA]
  have hsum2 : ∑ z : (ZMod e)ˣ, A.count (kap hem ((-z : (ZMod e)ˣ) : ZMod e)) • (z : ZMod e) =
      -∑ z : (ZMod e)ˣ, A.count (kap hem (z : ZMod e)) • (z : ZMod e) := by
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun z => ?_)
    simp only [Equiv.neg_apply, neg_neg, Units.val_neg, smul_neg]
  have : ∑ z, (cntF hem A z : ZMod e) * (z : ZMod e) =
      ∑ z : (ZMod e)ˣ, A.count (kap hem (z : ZMod e)) • (z : ZMod e) -
        ∑ z : (ZMod e)ˣ, A.count (kap hem ((-z : (ZMod e)ˣ) : ZMod e)) • (z : ZMod e) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    unfold cntF; push_cast; simp only [nsmul_eq_mul]; ring
  rw [this, hsum2, hsum1, neg_zero, sub_zero]

end FermatHodge
