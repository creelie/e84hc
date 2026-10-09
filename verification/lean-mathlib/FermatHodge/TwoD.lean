import FermatHodge.Odd

/-!
# The two-coordinate sign-symmetric case

Two independent subgroups `K` and `L` of orders `4` and `6`, each with an element of order two,
and a function on a coset of `K L` that satisfies the iterated difference condition, is odd under
the product of the two elements of order two, has mass at most `12` and is positive at the base
point. Then the function is `1` along a line through the base point, or it is a half-system
product: `2 f = u + v` with `u = ±1` odd along `K` and `v = ±1` odd along `L`.
-/

open Finset

noncomputable section

namespace FermatHodge

open Classical

set_option linter.unusedSectionVars false

variable {G : Type*} [CommGroup G] [Fintype G]

lemma sum_cosetF_single (L : Subgroup G) (y : G) {M : Type*} [AddCommMonoid M] (φ : G → M) :
    ∑ z ∈ cosetF [L] y, φ z = ∑ j ∈ Kf L, φ (y * j) := by
  rw [sum_cosetF_cons (by simp)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cosetF_nil, Finset.sum_singleton]

lemma mass_two {K L : Subgroup G} (hI : K ⊓ L = ⊥) (f : G → ℤ) (x : G) :
    mass [K, L] f x = ∑ i ∈ Kf K, ∑ j ∈ Kf L, |f (x * i * j)| := by
  simp only [mass]
  rw [sum_cosetF_cons (by simpa using hI)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact sum_cosetF_single L (x * i) (fun z => |f z|)

lemma sum_Kf_mul_right {L : Subgroup G} {g : G} (hg : g ∈ L) {M : Type*} [AddCommMonoid M]
    (φ : G → M) :
    ∑ j ∈ Kf L, φ (j * g) = ∑ j ∈ Kf L, φ j := by
  apply Finset.sum_nbij (· * g)
  · intro j hj; simp only [mem_Kf] at hj ⊢; exact L.mul_mem hj hg
  · intro a _ b _ h; exact mul_right_cancel h
  · intro w hw
    refine ⟨w * g⁻¹, ?_, by simp⟩
    simp only [Finset.mem_coe, mem_Kf] at hw ⊢
    exact L.mul_mem hw (L.inv_mem hg)
  · intro z _; rfl

lemma abs_add_add_abs_sub (p q : ℤ) : |p + q| + |p - q| = 2 * max |p| |q| := by
  simp only [abs_eq_max_neg]
  omega

/-- A subgroup of order four with an element of order two, listed. -/
lemma four_elems {K : Subgroup G} (hK : Nat.card K = 4) {ε : G} (hε : ε ∈ K) (hε1 : ε ≠ 1)
    (hε2 : ε * ε = 1) :
    ∃ a ∈ K, Kf K = {1, ε, a, a * ε} ∧ a ≠ 1 ∧ a ≠ ε ∧ a * ε ≠ 1 ∧ a * ε ≠ ε ∧ a * ε ≠ a := by
  have hc : (Kf K).card = 4 := by have := card_Kf K; omega
  have hsub : ({1, ε} : Finset G) ⊆ Kf K := by
    intro z hz; simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [K.one_mem, hε]
  have hlt : ({1, ε} : Finset G).card < (Kf K).card := by
    rw [hc, Finset.card_pair (Ne.symm hε1)]; norm_num
  obtain ⟨a, haK, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [mem_insert, mem_singleton, not_or] at ha
  obtain ⟨ha1, haε⟩ := ha
  rw [mem_Kf] at haK
  have hinv : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right hε2
  have h1 : a * ε ≠ 1 := fun h => haε (by rw [← hinv]; exact eq_inv_of_mul_eq_one_left h)
  have h2 : a * ε ≠ ε := fun h => ha1 (by simpa using h)
  have h3 : a * ε ≠ a := fun h => hε1 (by simpa using h)
  refine ⟨a, haK, ?_, ha1, haε, h1, h2, h3⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz; simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp [K.one_mem, hε, haK, K.mul_mem haK hε]
  · rw [hc, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair (Ne.symm h3)]
    · simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm haε, Ne.symm h2⟩
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨Ne.symm hε1, Ne.symm ha1, Ne.symm h1⟩

lemma sum_Kf_four {K : Subgroup G} {ε a : G} (hKeq : Kf K = {1, ε, a, a * ε}) (hε1 : ε ≠ 1)
    (ha1 : a ≠ 1) (haε : a ≠ ε) (haε1 : a * ε ≠ 1) (haε2 : a * ε ≠ ε) (haε3 : a * ε ≠ a)
    {M : Type*} [AddCommMonoid M] (φ : G → M) :
    ∑ i ∈ Kf K, φ i = φ 1 + φ ε + φ a + φ (a * ε) := by
  rw [hKeq, Finset.sum_insert, Finset.sum_insert, Finset.sum_pair (Ne.symm haε3)]
  · simp only [add_assoc]
  · simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm haε, Ne.symm haε2⟩
  · simp only [mem_insert, mem_singleton, not_or]
    exact ⟨Ne.symm hε1, Ne.symm ha1, Ne.symm haε1⟩

theorem twoD {K L : Subgroup G} (hI : K ⊓ L = ⊥) (hK : Nat.card K = 4) (hL : Nat.card L = 6)
    {ε ε' : G} (hε : ε ∈ K) (hε' : ε' ∈ L) (hε1 : ε ≠ 1) (hε1' : ε' ≠ 1)
    (hε2 : ε * ε = 1)
    {f : G → ℤ} {x : G} (hS : SIAt [K, L] f x)
    (hodd : ∀ z ∈ cosetF [K, L] x, f (z * (ε * ε')) = -f z)
    (hm : mass [K, L] f x ≤ 12) (hx : 1 ≤ f x) :
    (∀ i ∈ K, f (x * i) = 1) ∨ (∀ j ∈ L, f (x * j) = 1) ∨
    (mass [K, L] f x = 12 ∧
      ∃ u v : G → ℤ, (∀ i ∈ K, u i = 1 ∨ u i = -1) ∧ (∀ j ∈ L, v j = 1 ∨ v j = -1) ∧
      (∀ i ∈ K, u (i * ε) = -u i) ∧ (∀ j ∈ L, v (j * ε') = -v j) ∧
      ∀ i ∈ K, ∀ j ∈ L, 2 * f (x * i * j) = u i + v j) := by
  have hmem : ∀ i ∈ K, ∀ j ∈ L, x * i * j ∈ cosetF [K, L] x := by
    intro i hi j hj
    refine mem_cosetF_cons_of hi ?_
    rw [mem_cosetF, show (x * i)⁻¹ * (x * i * j) = j by group]
    simpa using hj
  have hbox : ∀ i ∈ K, ∀ j ∈ L, f (x * i * j) = f (x * i) + f (x * j) - f x := by
    intro i hi j hj
    have h := hS 1 K.one_mem i hi 1 L.one_mem j hj
    simp only [SIAt, mul_one] at h
    rw [mul_right_comm x j i] at h
    linarith
  have hodd' : ∀ i ∈ K, ∀ j ∈ L, f (x * (i * ε) * (j * ε')) = -f (x * i * j) := by
    intro i hi j hj
    rw [← hodd _ (hmem i hi j hj)]
    congr 1
    simp only [mul_assoc, mul_left_comm j ε ε']
  have hA : ∀ i ∈ K, f (x * (i * ε)) + f (x * i) = f x - f (x * ε') := by
    intro i hi
    have h1 := hodd' i hi 1 L.one_mem
    rw [one_mul, mul_one, hbox _ (K.mul_mem hi hε) _ hε'] at h1
    linarith
  have hB : ∀ j ∈ L, f (x * (j * ε')) + f (x * j) = f x - f (x * ε) := by
    intro j hj
    have h1 := hodd' 1 K.one_mem j hj
    rw [one_mul, mul_one, hbox _ hε _ (L.mul_mem hj hε')] at h1
    linarith
  have hA1 : f (x * ε) + f x = f x - f (x * ε') := by
    have := hA 1 K.one_mem; rwa [one_mul, mul_one] at this
  obtain ⟨u, hu⟩ : ∃ u : G → ℤ, ∀ i, u i = 2 * f (x * i) - (f x - f (x * ε')) := ⟨_, fun _ => rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : G → ℤ, ∀ j, v j = 2 * (f (x * j) - f x) + (f x - f (x * ε')) :=
    ⟨_, fun _ => rfl⟩
  have hu_odd : ∀ i ∈ K, u (i * ε) = -u i := by
    intro i hi; rw [hu, hu]; have := hA i hi; linarith
  have hv_odd : ∀ j ∈ L, v (j * ε') = -v j := by
    intro j hj; rw [hv, hv]; have := hB j hj; linarith
  have huv : ∀ i ∈ K, ∀ j ∈ L, 2 * f (x * i * j) = u i + v j := by
    intro i hi j hj; rw [hu, hv, hbox i hi j hj]; ring
  -- the mass in terms of `u` and `v`
  have hrow : ∀ i, ∑ j ∈ Kf L, max |u i| |v j| = ∑ j ∈ Kf L, |u i + v j| := by
    intro i
    have h1 : ∑ j ∈ Kf L, |u i + v j| = ∑ j ∈ Kf L, |u i - v j| := by
      have := sum_Kf_mul_right hε' (fun j => |u i + v j|)
      rw [← this]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [hv_odd j (by simpa using hj), ← sub_eq_add_neg]
    have h2 : ∑ j ∈ Kf L, (|u i + v j| + |u i - v j|) = ∑ j ∈ Kf L, 2 * max |u i| |v j| :=
      Finset.sum_congr rfl (fun j _ => abs_add_add_abs_sub _ _)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← h1] at h2
    linarith
  have e1 : ∑ i ∈ Kf K, ∑ j ∈ Kf L, max |u i| |v j| = 2 * mass [K, L] f x := by
    rw [mass_two hI, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hrow i, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [← huv i (by simpa using hi) j (by simpa using hj), abs_mul]; norm_num
  have hT : ∑ i ∈ Kf K, ∑ j ∈ Kf L, max |u i| |v j| ≤ 24 := by
    rw [e1]; linarith
  -- parity
  have hpar : ∀ i ∈ K, ∀ j ∈ L, (u i + v j) % 2 = 0 := by
    intro i hi j hj; rw [← huv i hi j hj]; omega
  have hx1 : u 1 + v 1 = 2 * f x := by
    have := huv 1 K.one_mem 1 L.one_mem; rw [mul_one, mul_one] at this; linarith
  obtain ⟨a, haK, hKeq, ha1, haε, haε1, haε2, haε3⟩ := four_elems hK hε hε1 hε2
  have hsumK : ∀ φ : G → ℤ, ∑ i ∈ Kf K, φ i = φ 1 + φ ε + φ a + φ (a * ε) := by
    intro φ
    rw [hKeq, Finset.sum_insert, Finset.sum_insert, Finset.sum_pair (Ne.symm haε3)]
    · ring
    · simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm haε, Ne.symm haε2⟩
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨Ne.symm hε1, Ne.symm ha1, Ne.symm haε1⟩
  have hu1 : |u ε| = |u 1| := by
    have := hu_odd 1 K.one_mem; rw [one_mul] at this; rw [this, abs_neg]
  have hua : |u (a * ε)| = |u a| := by rw [hu_odd a haK, abs_neg]
  have hT' : 2 * ∑ j ∈ Kf L, max |u 1| |v j| + 2 * ∑ j ∈ Kf L, max |u a| |v j| ≤ 24 := by
    rw [hsumK, hu1, hua] at hT; linarith
  have hcardL : (Kf L).card = 6 := by have := card_Kf L; omega
  have hM1 : ∀ A : ℤ, 6 * A ≤ ∑ j ∈ Kf L, max A |v j| := by
    intro A
    have := Finset.card_nsmul_le_sum (Kf L) (fun j => max A |v j|) A
      (fun j _ => le_max_left _ _)
    rw [hcardL, nsmul_eq_mul] at this; push_cast at this; linarith
  have hM2 : ∀ A : ℤ, ∑ j ∈ Kf L, |v j| ≤ ∑ j ∈ Kf L, max A |v j| :=
    fun A => Finset.sum_le_sum (fun j _ => le_max_right _ _)
  have hB0 : 0 ≤ ∑ j ∈ Kf L, |v j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hve : |v ε'| = |v 1| := by
    have := hv_odd 1 L.one_mem; rw [one_mul] at this; rw [this, abs_neg]
  have hBpair : 2 * |v 1| ≤ ∑ j ∈ Kf L, |v j| := by
    have := pair_le_sum (s := Kf L) (μ := fun j => |v j|) (fun _ _ => abs_nonneg _)
      (show (1 : G) ∈ Kf L by simp [L.one_mem]) (show ε' ∈ Kf L by simp [hε'])
      (Ne.symm hε1')
    simp only [hve] at this; linarith
  by_cases hodd1 : u 1 % 2 = 1
  · -- the odd case: every term is one
    right; right
    have hvodd : ∀ j ∈ L, v j % 2 = 1 := by
      intro j hj; have := hpar 1 K.one_mem j hj; omega
    have huodd : ∀ i ∈ K, u i % 2 = 1 := by
      intro i hi; have := hpar i hi 1 L.one_mem; have := hvodd 1 L.one_mem; omega
    have hge : ∀ i ∈ Kf K, ∀ j ∈ Kf L, 1 ≤ max |u i| |v j| := by
      intro i hi _ _
      have := huodd i (by simpa using hi)
      have : 1 ≤ |u i| := by rcases abs_cases (u i) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      exact le_trans this (le_max_left _ _)
    have e2 : ∑ i ∈ Kf K, ∑ j ∈ Kf L, (max |u i| |v j| - 1) =
        (∑ i ∈ Kf K, ∑ j ∈ Kf L, max |u i| |v j|) - 24 := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, hcardL, nsmul_eq_mul]
      have hcK : (Kf K).card = 4 := by have := card_Kf K; omega
      rw [hcK]; push_cast; ring
    have hsum0 : ∑ i ∈ Kf K, ∑ j ∈ Kf L, (max |u i| |v j| - 1) = 0 := by
      apply le_antisymm
      · linarith
      · exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => by
          linarith [hge i hi j hj]))
    have hone : ∀ i ∈ K, ∀ j ∈ L, max |u i| |v j| = 1 := by
      intro i hi j hj
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => Finset.sum_nonneg
        (fun j hj => by linarith [hge i hi j hj]))).mp hsum0 i (by simpa using hi)
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => by
        linarith [hge i (by simpa using hi) j hj])).mp h0 j (by simpa using hj)
      linarith
    refine ⟨by linarith, u, v, ?_, ?_, hu_odd, hv_odd, huv⟩
    · intro i hi
      have h1 := hone i hi 1 L.one_mem
      have h2 := huodd i hi
      have h3 : |u i| ≤ 1 := h1 ▸ le_max_left _ _
      rcases abs_cases (u i) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    · intro j hj
      have h1 := hone 1 K.one_mem j hj
      have h2 := hvodd j hj
      have h3 : |v j| ≤ 1 := h1 ▸ le_max_right _ _
      rcases abs_cases (v j) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  · -- the even case
    have hveven : ∀ j ∈ L, v j % 2 = 0 := by
      intro j hj; have := hpar 1 K.one_mem j hj; omega
    have hueven : ∀ i ∈ K, u i % 2 = 0 := by
      intro i hi; have := hpar i hi 1 L.one_mem; have := hveven 1 L.one_mem; omega
    by_cases hpos : 1 ≤ u 1
    · -- a line along `L`
      right; left
      have hu2 : 2 ≤ u 1 := by have := hueven 1 K.one_mem; omega
      have habs : |u 1| = u 1 := abs_of_pos (by omega)
      have h6 := hM1 |u 1|
      have h7 := hM2 |u a|
      have hB : ∑ j ∈ Kf L, |v j| = 0 := by linarith
      have hu12 : u 1 = 2 := by linarith
      have hv0 : ∀ j ∈ L, v j = 0 := by
        intro j hj
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (v j))).mp hB j
          (by simpa using hj)
        exact abs_eq_zero.mp this
      intro j hj
      have := huv 1 K.one_mem j hj
      rw [mul_one, hu12, hv0 j hj] at this
      linarith
    · -- a line along `K`
      left
      have hv1 : 2 ≤ v 1 := by have := hveven 1 L.one_mem; omega
      have habs : |v 1| = v 1 := abs_of_pos (by omega)
      have hA1z : u 1 = 0 := by
        by_contra hne
        have h0 : 2 ≤ |u 1| := by
          have := hueven 1 K.one_mem
          rcases abs_cases (u 1) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
        have h6 := hM1 |u 1|
        have h7 := hM2 |u a|
        linarith
      have hAaz : u a = 0 := by
        by_contra hne
        have h0 : 2 ≤ |u a| := by
          have := hueven a haK
          rcases abs_cases (u a) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
        have h6 := hM1 |u a|
        have h7 := hM2 |u 1|
        linarith
      have hsame : ∑ j ∈ Kf L, max |u 1| |v j| = ∑ j ∈ Kf L, |v j| := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hA1z, abs_zero]; exact max_eq_right (abs_nonneg _)
      have hsame' : ∑ j ∈ Kf L, max |u a| |v j| = ∑ j ∈ Kf L, |v j| := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hAaz, abs_zero]; exact max_eq_right (abs_nonneg _)
      have hv12 : v 1 = 2 := by
        have := hveven 1 L.one_mem
        rw [hsame, hsame'] at hT'
        omega
      have hu0 : ∀ i ∈ K, u i = 0 := by
        intro i hi
        have hi' : i ∈ Kf K := by simpa using hi
        rw [hKeq] at hi'
        simp only [mem_insert, mem_singleton] at hi'
        rcases hi' with rfl | rfl | rfl | rfl
        · exact hA1z
        · have := hu_odd 1 K.one_mem; rw [one_mul] at this; rw [this, hA1z]; rfl
        · exact hAaz
        · rw [hu_odd a haK, hAaz]; rfl
      intro i hi
      have := huv i hi 1 L.one_mem
      rw [mul_one, hu0 i hi, hv12] at this
      linarith

end FermatHodge
