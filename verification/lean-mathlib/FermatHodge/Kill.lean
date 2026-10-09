import FermatHodge.Core

/-!
# Sum arguments at the maximal order

When the whole tuple has the maximal order `e`, the sum of its entries vanishes, so
`∑ F(z) z = 0` in `ZMod e`. This rules out a full line along `K_7`, a full line along `K_5` of
four elements when the tuple has four entries, and the half-system products at `e = 35`.
-/

open Finset

noncomputable section

namespace FermatHodge

open Classical

set_option linter.unusedSectionVars false

section kill

variable {e : ℕ} [NeZero e]

lemma neg_one_not_mem_Nd_of_three_le {d : ℕ} (h : d ∣ e) (hd : 3 ≤ d) :
    (-1 : (ZMod e)ˣ) ∉ Nd h := by
  intro hm
  rw [mem_Nd] at hm
  have h3 : Fact (2 < d) := ⟨by omega⟩
  have : ((ZMod.castHom h (ZMod d)) (-1 : ZMod e)) = 1 := by
    rw [ZMod.castHom_apply]; simpa using hm
  rw [map_neg, map_one] at this
  exact ZMod.neg_one_ne_one this

lemma coprime_six_of (he2 : ¬2 ∣ e) (he3 : ¬3 ∣ e) : Nat.Coprime e 6 := by
  have h2 : Nat.Coprime e 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr he2).symm
  have h3 : Nat.Coprime e 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr he3).symm
  exact Nat.Coprime.mul_right h2 h3

lemma cast_mem_Kq {p : ℕ} (hpe : p ∣ e) {k : (ZMod e)ˣ} (hk : k ∈ Kq e p) :
    (ZMod.castHom (Nat.div_dvd_of_dvd hpe) (ZMod (e / p))) (k : ZMod e) = 1 := by
  rw [Kq_of_dvd hpe, mem_Nd] at hk
  rw [ZMod.castHom_apply]; exact hk

/-- A full line of positive values along `K` uses up the mass `2 |K|`, and then the weighted sum
`∑ F(z) z` is twice the sum of the line. -/
theorem line_mass {K : Subgroup (ZMod e)ˣ} (hK : (-1 : (ZMod e)ˣ) ∉ K)
    {F : (ZMod e)ˣ → ℤ} (hodd : ∀ z, F (-z) = -F z) {w : (ZMod e)ˣ}
    (hw : ∀ k ∈ K, 1 ≤ F (w * k)) (hm : ∑ z, |F z| ≤ 2 * Nat.card K) :
    ∑ z, |F z| = 2 * Nat.card K ∧
      ∑ z, (F z : ZMod e) * (z : ZMod e) = 2 * ∑ k ∈ Kf K, ((w * k : (ZMod e)ˣ) : ZMod e) := by
  have hK' : (-1 : (ZMod e)ˣ) ∉ lspan [K] := by simpa using hK
  have hdisj : Disjoint (cosetF [K] w) (cosetF [K] (w * (-1))) := cosetF_disjoint_neg hK' w
  have hPN : cosetF [K] w ∪ cosetF [K] (w * (-1)) ⊆ univ := subset_univ _
  have hneg : ∀ k, w * (-1) * k = -(w * k) := fun k => by rw [mul_right_comm, mul_neg_one]
  set R := univ \ (cosetF [K] w ∪ cosetF [K] (w * (-1))) with hR
  have hsplitZ : ∑ z, |F z| = ∑ k ∈ Kf K, |F (w * k)| + ∑ k ∈ Kf K, |F (w * k)| +
      ∑ z ∈ R, |F z| := by
    rw [← Finset.sum_sdiff hPN, Finset.sum_union hdisj, sum_cosetF_single K w (fun z => |F z|),
      sum_cosetF_single K (w * (-1)) (fun z => |F z|)]
    simp only [hneg, hodd, abs_neg]
    ring
  have hge : ∀ k ∈ Kf K, 1 ≤ |F (w * k)| := fun k hk =>
    le_trans (hw k (by simpa using hk)) (le_abs_self _)
  have hA : (Nat.card K : ℤ) ≤ ∑ k ∈ Kf K, |F (w * k)| := by
    have := Finset.card_nsmul_le_sum (Kf K) (fun k => |F (w * k)|) 1 hge
    rw [card_Kf, nsmul_eq_mul, mul_one] at this; exact this
  have hR0 : 0 ≤ ∑ z ∈ R, |F z| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hRz : ∑ z ∈ R, |F z| = 0 := by linarith
  have hAeq : ∑ k ∈ Kf K, |F (w * k)| = Nat.card K := by linarith
  have hone : ∀ k ∈ Kf K, F (w * k) = 1 := by
    have h0 : ∑ k ∈ Kf K, (|F (w * k)| - 1) = 0 := by
      rw [Finset.sum_sub_distrib, hAeq, Finset.sum_const, card_Kf]; simp
    intro k hk
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => by linarith [hge k hk])).mp h0 k hk
    have h1 := hw k (by simpa using hk)
    rw [abs_of_pos (by omega)] at this
    omega
  have hRF : ∀ z ∈ R, F z = 0 := fun z hz =>
    abs_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)).mp hRz z hz)
  refine ⟨by rw [hsplitZ, hAeq, hRz]; ring, ?_⟩
  rw [← Finset.sum_sdiff hPN, Finset.sum_union hdisj,
    sum_cosetF_single K w (fun z => (F z : ZMod e) * (z : ZMod e)),
    sum_cosetF_single K (w * (-1)) (fun z => (F z : ZMod e) * (z : ZMod e)),
    Finset.sum_eq_zero (fun z hz => by rw [hRF z hz]; simp), zero_add, two_mul]
  congr 1
  · exact Finset.sum_congr rfl (fun k hk => by rw [hone k hk]; simp)
  · refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [hneg, hodd, hone k hk, Units.val_neg]; simp

lemma eq_one_of_dvd_two_mul {d c : ℕ} (hd : Nat.Coprime d 6) (hc : c = 4 ∨ c = 6)
    (h : d ∣ 2 * c) : d = 1 := by
  have h2 : Nat.Coprime d 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hd
  have h12 : Nat.Coprime d 12 := by
    have : (12 : ℕ) = 6 * 2 := rfl
    rw [this]; exact Nat.Coprime.mul_right hd h2
  have h8 : Nat.Coprime d 8 := by
    have : (8 : ℕ) = 2 ^ 3 := rfl
    rw [this]; exact Nat.Coprime.pow_right 3 h2
  rcases hc with rfl | rfl
  · exact Nat.Coprime.eq_one_of_dvd h8 h
  · exact Nat.Coprime.eq_one_of_dvd h12 h

/-- A full positive line along `K_p` of order `4` or `6` cannot carry the whole tuple. -/
theorem kill_line {p : ℕ} (hpe : p ∣ e) (he2 : ¬2 ∣ e) (he3 : ¬3 ∣ e)
    (hc : Nat.card (Kq e p) = 4 ∨ Nat.card (Kq e p) = 6)
    {F : (ZMod e)ˣ → ℤ} (hodd : ∀ z, F (-z) = -F z) {w : (ZMod e)ˣ}
    (hw : ∀ k ∈ Kq e p, 1 ≤ F (w * k)) (hm : ∑ z, |F z| ≤ 2 * Nat.card (Kq e p))
    (hsum : ∑ z, |F z| = 2 * Nat.card (Kq e p) →
      ∑ z, (F z : ZMod e) * (z : ZMod e) = 0) : False := by
  have hd : e / p ∣ e := Nat.div_dvd_of_dvd hpe
  have hne0 : e / p ≠ 0 := ne_zero_div hpe
  have : NeZero (e / p) := ⟨hne0⟩
  by_cases h1 : e / p = 1
  · have hall : ∀ u : (ZMod e)ˣ, u ∈ Kq e p := by
      intro u
      rw [Kq_of_dvd hpe, mem_Nd]
      have : Subsingleton (ZMod (e / p)) := by rw [h1]; infer_instance
      exact Subsingleton.elim _ _
    have h1' := hw 1 (hall 1)
    have h2' := hw (-1) (hall (-1))
    rw [mul_one] at h1'
    rw [mul_neg_one, hodd] at h2'
    omega
  · have h3 : 3 ≤ e / p := by
      have hodd' : ¬2 ∣ e / p := fun h => he2 (dvd_trans h hd)
      have h2' : e / p ≠ 2 := fun h => hodd' (by rw [h])
      clear hw hm hsum hc
      generalize e / p = q at *
      omega
    have hK : (-1 : (ZMod e)ˣ) ∉ Kq e p := by
      rw [Kq_of_dvd hpe]; exact neg_one_not_mem_Nd_of_three_le hd h3
    obtain ⟨hm2, hS⟩ := line_mass hK hodd hw hm
    rw [hsum hm2] at hS
    have hc' := congrArg (ZMod.castHom hd (ZMod (e / p))) hS
    rw [map_zero, map_mul, map_sum] at hc'
    have hterm : ∀ k ∈ Kf (Kq e p), (ZMod.castHom hd (ZMod (e / p)))
        ((w * k : (ZMod e)ˣ) : ZMod e) = (ZMod.castHom hd (ZMod (e / p))) (w : ZMod e) := by
      intro k hk
      rw [Units.val_mul, map_mul, cast_mem_Kq hpe (k := k) (by simpa using hk), mul_one]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_Kf, nsmul_eq_mul, map_ofNat] at hc'
    have hu : IsUnit ((ZMod.castHom hd (ZMod (e / p))) (w : ZMod e)) := by
      rw [ZMod.castHom_apply, ← ZMod.unitsMap_val hd w]; exact Units.isUnit _
    have h00 : ((2 * Nat.card (Kq e p) : ℕ) : ZMod (e / p)) *
        (ZMod.castHom hd (ZMod (e / p))) (w : ZMod e) = 0 := by
      push_cast; rw [mul_assoc]; exact hc'.symm
    have h0 := (hu.mul_left_eq_zero).mp h00
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact h1 (eq_one_of_dvd_two_mul (Nat.Coprime.coprime_dvd_left hd (coprime_six_of he2 he3))
      hc h0)

/-- The half-system products at conductor `35` are ruled out by the sum modulo `5`. -/
theorem kill_half (h5 : 5 ∣ e) (h7 : 7 ∣ e)
    {F : (ZMod e)ˣ → ℤ} (hmass : ∑ z, |F z| ≤ 12)
    (hsum : ∑ z, |F z| = 12 → ∑ z, (F z : ZMod e) * (z : ZMod e) = 0)
    {y ε ε' : (ZMod e)ˣ} (hε : ε ∈ Kq e 5) (hε' : ε' ∈ Kq e 7) (hεε : ε * ε' = -1)
    (hc5 : Nat.card (Kq e 5) = 4) (hc7 : Nat.card (Kq e 7) = 6)
    (hm12 : mass [Kq e 5, Kq e 7] F y = 12)
    {u v : (ZMod e)ˣ → ℤ} (hu : ∀ i ∈ Kq e 5, u i = 1 ∨ u i = -1)
    (hu' : ∀ i ∈ Kq e 5, u (i * ε) = -u i) (hv' : ∀ j ∈ Kq e 7, v (j * ε') = -v j)
    (huv : ∀ i ∈ Kq e 5, ∀ j ∈ Kq e 7, 2 * F (y * i * j) = u i + v j) : False := by
  have hI : Indep [Kq e 5, Kq e 7] := indep_Kq [5, 7] (by simp) (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨by norm_num, h5⟩
    · exact ⟨by norm_num, h7⟩)
  have hI1 : Kq e 5 ⊓ lspan [Kq e 7] = ⊥ := hI.1
  -- the whole mass sits on the coset of `y`
  set C := cosetF [Kq e 5, Kq e 7] y with hC
  have hCm : ∑ z ∈ C, |F z| = 12 := hm12
  have hsd : ∑ z ∈ univ \ C, |F z| + ∑ z ∈ C, |F z| = ∑ z, |F z| :=
    Finset.sum_sdiff (subset_univ C)
  have hnn : 0 ≤ ∑ z ∈ univ \ C, |F z| := Finset.sum_nonneg (fun z _ => abs_nonneg (F z))
  have h0 : ∑ z ∈ univ \ C, |F z| = 0 := by linarith
  have hrest : ∀ z, z ∉ C → F z = 0 := by
    intro z hz
    exact abs_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)).mp h0 z
      (by simp [hz]))
  have hS := hsum (by linarith)
  have hsub : ∑ z ∈ C, (F z : ZMod e) * (z : ZMod e) = ∑ z, (F z : ZMod e) * (z : ZMod e) :=
    Finset.sum_subset (subset_univ C) (fun z _ hz => by rw [hrest z hz]; simp)
  rw [← hsub, hC, sum_cosetF_cons hI1] at hS
  have hS' : ∑ i ∈ Kf (Kq e 5), ∑ j ∈ Kf (Kq e 7),
      (F (y * i * j) : ZMod e) * ((y * i * j : (ZMod e)ˣ) : ZMod e) = 0 := by
    rw [← hS]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (sum_cosetF_single (Kq e 7) (y * i) (fun z => (F z : ZMod e) * (z : ZMod e))).symm
  -- reduce modulo `5`
  set ψ := ZMod.castHom h5 (ZMod 5) with hψ
  have h57 : 5 ∣ e / 7 := Nat.dvd_div_of_mul_dvd
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 7 5) h7 h5)
  have hψ7 : ∀ j ∈ Kq e 7, ψ (j : ZMod e) = 1 := by
    intro j hj
    rw [Kq_of_dvd h7] at hj
    have hj' := Nd_mono (Nat.div_dvd_of_dvd h7) h5 h57 hj
    rw [mem_Nd] at hj'
    rw [hψ, ZMod.castHom_apply]; exact hj'
  have h55 : ¬5 ∣ e / 5 := by
    intro h
    have := card_Kq_of_dvd (by norm_num) h5 h
    omega
  have hcop : Nat.Coprime (e / 5) 5 :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h55)
  have hinj : ∀ i ∈ Kq e 5, ψ (i : ZMod e) = 1 → i = 1 := by
    intro i hi hψi
    refine eq_one_of_Nd (Nat.div_dvd_of_dvd h5) h5 hcop (Nat.div_mul_cancel h5).symm ?_ ?_
    · rw [← Kq_of_dvd h5]; exact hi
    · rw [mem_Nd]; rw [hψ, ZMod.castHom_apply] at hψi; exact hψi
  have hψε : ψ (ε : ZMod e) = -1 := by
    have := congrArg (fun z : (ZMod e)ˣ => ψ (z : ZMod e)) hεε
    simp only [Units.val_mul, map_mul, Units.val_neg, Units.val_one, map_neg, map_one] at this
    rw [hψ7 ε' hε', mul_one] at this; exact this
  have hε1 : ε ≠ 1 := by
    rintro rfl
    rw [Units.val_one, map_one] at hψε
    exact absurd hψε (by decide)
  have hsq : ε * ε = 1 := by
    apply hinj _ ((Kq e 5).mul_mem hε hε)
    rw [Units.val_mul, map_mul, hψε]; norm_num
  obtain ⟨a, haK, hKeq, ha1, haε, haε1, haε2, haε3⟩ := four_elems hc5 hε hε1 hsq
  have hψa1 : ψ (a : ZMod e) ≠ 1 := fun h => ha1 (hinj a haK h)
  have hψa2 : ψ (a : ZMod e) ≠ -1 := by
    intro h
    apply haε1
    apply hinj _ ((Kq e 5).mul_mem haK hε)
    rw [Units.val_mul, map_mul, h, hψε]; norm_num
  -- the sum of `v` over `K_7` vanishes
  have hvsum : ∑ j ∈ Kf (Kq e 7), v j = 0 := by
    have h1 := sum_Kf_mul_right hε' v
    rw [Finset.sum_congr rfl (fun j hj => hv' j (by simpa using hj)), Finset.sum_neg_distrib] at h1
    linarith
  have hcard7 : (Kf (Kq e 7)).card = 6 := by have := card_Kf (Kq e 7); omega
  -- evaluate the image of twice the sum
  have hT := congrArg ψ hS'
  rw [map_zero, map_sum] at hT
  have hT2 : ∑ i ∈ Kf (Kq e 5), ((6 * u i : ℤ) : ZMod 5) * (ψ (y : ZMod e) * ψ (i : ZMod e)) = 0 := by
    have : (2 : ZMod 5) * ∑ i ∈ Kf (Kq e 5), ψ (∑ j ∈ Kf (Kq e 7),
        (F (y * i * j) : ZMod e) * ((y * i * j : (ZMod e)ˣ) : ZMod e)) = 0 := by
      rw [hT, mul_zero]
    rw [← this, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i ∈ Kq e 5 := by simpa using hi
    rw [map_sum, Finset.mul_sum]
    have hin : ∀ j ∈ Kf (Kq e 7), (2 : ZMod 5) * ψ ((F (y * i * j) : ZMod e) *
        ((y * i * j : (ZMod e)ˣ) : ZMod e)) =
        ((u i + v j : ℤ) : ZMod 5) * (ψ (y : ZMod e) * ψ (i : ZMod e)) := by
      intro j hj
      have hj' : j ∈ Kq e 7 := by simpa using hj
      rw [map_mul, map_intCast, Units.val_mul, Units.val_mul, map_mul, map_mul, hψ7 j hj',
        mul_one, ← huv i hi' j hj']
      push_cast; ring
    rw [Finset.sum_congr rfl hin, ← Finset.sum_mul, ← Int.cast_sum, Finset.sum_add_distrib,
      hvsum, Finset.sum_const, hcard7]
    simp only [Int.cast_mul, Int.cast_ofNat, add_zero, nsmul_eq_mul, Nat.cast_ofNat]
  rw [sum_Kf_four hKeq hε1 ha1 haε haε1 haε2 haε3] at hT2
  have hu1 := hu' 1 (Kq e 5).one_mem
  rw [one_mul] at hu1
  rw [hu1, hu' a haK, Units.val_one, map_one, Units.val_mul, map_mul, hψε] at hT2
  have hy : IsUnit (ψ (y : ZMod e)) := by
    rw [hψ, ZMod.castHom_apply, ← ZMod.unitsMap_val h5 y]; exact Units.isUnit _
  have hkey : ψ (y : ZMod e) * ((12 : ZMod 5) * ((u 1 : ZMod 5) + (u a : ZMod 5) * ψ (a : ZMod e))) = 0 := by
    rw [← hT2]; push_cast; ring
  have h12 : (12 : ZMod 5) * ((u 1 : ZMod 5) + (u a : ZMod 5) * ψ (a : ZMod e)) = 0 :=
    (hy.mul_right_eq_zero).mp hkey
  have hne : (12 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h12' : (u 1 : ZMod 5) + (u a : ZMod 5) * ψ (a : ZMod e) = 0 := by
    exact (mul_eq_zero.mp h12).resolve_left hne
  rcases hu 1 (Kq e 5).one_mem with h1 | h1 <;> rcases hu a haK with h2 | h2 <;>
    rw [h1, h2] at h12' <;> push_cast at h12'
  · exact hψa2 (by linear_combination h12')
  · exact hψa1 (by linear_combination -h12')
  · exact hψa1 (by linear_combination h12')
  · exact hψa2 (by linear_combination -h12')

end kill

end FermatHodge
