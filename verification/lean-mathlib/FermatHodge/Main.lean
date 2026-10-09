import FermatHodge.Hodge

/-!
# Hodge quadruples and sextuples

The combinatorial classification behind the Hodge conjecture for Fermat fourfolds of degree
prime to `6`: for `m` prime to `6`, a multiset of four nonzero elements of `ZMod m` summing to zero
whose representatives have a sum independent of the unit `t` contains a pair `a, -a`; a multiset
of six such elements contains a pair or is a `5`-standard sextuple
`{x, x + m/5, x + 2m/5, x + 3m/5, x + 4m/5, -5x}`.

The one analytic input is `BernoulliNV`: the sums `∑ χ(s) s` of odd primitive Dirichlet
characters do not vanish (equivalently `B_{1,χ} ≠ 0`, a consequence of `L(1, χ̄) ≠ 0`).  Mathlib
has `L(1, χ) ≠ 0` but not yet the value of `L(0, χ)`, so it is kept as a hypothesis.
-/

open Finset

noncomputable section

namespace FermatHodge

open Classical

set_option linter.unusedSectionVars false

/-- The classical nonvanishing of `B_{1,χ}` for odd primitive Dirichlet characters. -/
def BernoulliNV : Prop :=
  ∀ (e : ℕ) [NeZero e] (χ : DirichletCharacter ℂ e), χ.IsPrimitive → χ.Odd → Bsum χ ≠ 0

section line

variable {e : ℕ} [NeZero e]

/-- A line of positive values along `K` forces `-1 ∉ K`. -/
lemma neg_one_not_mem_of_line {K : Subgroup (ZMod e)ˣ} {F : (ZMod e)ˣ → ℤ}
    (hodd : ∀ z, F (-z) = -F z) {w : (ZMod e)ˣ} (hw : ∀ k ∈ K, 1 ≤ F (w * k)) :
    (-1 : (ZMod e)ˣ) ∉ K := by
  intro h
  have h1 := hw 1 K.one_mem
  have h2 := hw (-1) h
  rw [mul_one] at h1
  rw [mul_neg_one, hodd] at h2
  omega

/-- A line of positive values along `K` carries mass at least `2 |K|`. -/
lemma line_mass_ge {K : Subgroup (ZMod e)ˣ} (hK : (-1 : (ZMod e)ˣ) ∉ K)
    {F : (ZMod e)ˣ → ℤ} (hodd : ∀ z, F (-z) = -F z) {w : (ZMod e)ˣ}
    (hw : ∀ k ∈ K, 1 ≤ F (w * k)) : 2 * (Nat.card K : ℤ) ≤ ∑ z, |F z| := by
  have hK' : (-1 : (ZMod e)ˣ) ∉ lspan [K] := by simpa using hK
  have hdisj := cosetF_disjoint_neg hK' w
  have hneg : ∀ k, w * (-1) * k = -(w * k) := fun k => by rw [mul_right_comm, mul_neg_one]
  have h1 : ∑ z ∈ cosetF [K] w ∪ cosetF [K] (w * (-1)), |F z| ≤ ∑ z, |F z| :=
    Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => abs_nonneg _)
  rw [Finset.sum_union hdisj, sum_cosetF_single K w (fun z => |F z|),
    sum_cosetF_single K (w * (-1)) (fun z => |F z|)] at h1
  simp only [hneg, hodd, abs_neg] at h1
  have hge : ∀ k ∈ Kf K, 1 ≤ |F (w * k)| := fun k hk =>
    le_trans (hw k (by simpa using hk)) (le_abs_self _)
  have hA : (Nat.card K : ℤ) ≤ ∑ k ∈ Kf K, |F (w * k)| := by
    have := Finset.card_nsmul_le_sum (Kf K) (fun k => |F (w * k)|) 1 hge
    rw [card_Kf, nsmul_eq_mul, mul_one] at this; exact this
  linarith

end line

section main

variable {m : ℕ} [NeZero m]

/-- The core dichotomy at the maximal order, with the half-systems ruled out: a full line of
positive values along `K_5` or `K_7`. -/
theorem line_exists {e : ℕ} [NeZero e] (hm2 : ¬2 ∣ m) (hm3 : ¬3 ∣ m) (hem : e ∣ m)
    (A : Multiset (ZMod m)) (hA : A.sum = 0) (hcard : Multiset.card A ≤ 6) (h : ℕ)
    (hH : ∀ t : (ZMod m)ˣ, (A.map fun a => ((t : ZMod m) * a).val).sum = h)
    (hmax : ∀ a ∈ A, addOrderOf a ≤ e) (hB : BernoulliNV) {x : (ZMod e)ˣ}
    (hx : 1 ≤ cntF hem A x) :
    ∃ p, (p = 5 ∨ p = 7) ∧ p ∣ e ∧ ∃ w : (ZMod e)ˣ, ∀ k ∈ Kq e p, 1 ≤ cntF hem A (w * k) := by
  have he2 : ¬2 ∣ e := fun h2 => hm2 (h2.trans hem)
  have he3 : ¬3 ∣ e := fun h3 => hm3 (h3.trans hem)
  have hle := mass_cntF_le_card hem A
  have hmass : ∑ z, |cntF hem A z| ≤ 12 := by
    have : (Multiset.card A : ℤ) ≤ 6 := by exact_mod_cast hcard
    linarith
  set ps := e.primeFactors.toList with hps_def
  have hnd : ps.Nodup := Finset.nodup_toList _
  have hmemps : ∀ p, p ∈ ps ↔ p.Prime ∧ p ∣ e := by
    intro p
    rw [hps_def, Finset.mem_toList, Nat.mem_primeFactors]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, NeZero.ne e⟩⟩
  have hps : ∀ p ∈ ps, p.Prime ∧ p ∣ e := fun p hp => (hmemps p).mp hp
  have hcond : ∀ Ks : List (Subgroup (ZMod e)ˣ), Ks.Perm (ps.map (Kq e)) →
      ∀ x, SIAt Ks (cntF hem A) x := by
    intro Ks hperm x
    refine SIAt_of_fourier (cntF hem A)
      (fun χ hχ => fourier_cntF hem A h hH hmax (hB e) χ hχ) Ks (fun p hp hpe => ?_) x
    exact hperm.mem_iff.mpr (List.mem_map.mpr ⟨p, (hmemps p).mpr ⟨hp, hpe⟩, rfl⟩)
  rcases core he2 he3 ps hnd hps (cntF hem A) (cntF_neg hem A) hmass hcond hx with
    ⟨p, hp, hp57, w, hw⟩ |
    ⟨h5, h7, y, ε, hε, ε', hε', hεε, hc5, hc7, hm12, u, v, hu, hv, hu', hv', huv⟩
  · exact ⟨p, hp57, (hps p hp).2, w, hw⟩
  · exfalso
    refine kill_half (hps 5 h5).2 (hps 7 h7).2 hmass (fun h12 => ?_) hε hε' hεε hc5 hc7 hm12
      hu hu' hv' huv
    refine sum_cntF_eq_zero hem A hA ?_
    have : (Multiset.card A : ℤ) ≤ 6 := by exact_mod_cast hcard
    linarith

/-- Choosing the maximal order: either `A` has a pair `a, -a`, or the counting function at the
maximal order `e` is positive somewhere. -/
lemma pair_or_pos (A : Multiset (ZMod m)) (hne : A ≠ 0) :
    (∃ a ∈ A, -a ∈ A) ∨ ∃ e, ∃ _ : NeZero e, ∃ hem : e ∣ m, (∀ a ∈ A, addOrderOf a ≤ e) ∧
      ∃ x : (ZMod e)ˣ, 1 ≤ cntF hem A x := by
  obtain ⟨a0, ha0, hmax0⟩ := Multiset.exists_max_image addOrderOf hne
  have hem : addOrderOf a0 ∣ m := addOrderOf_dvd_m a0
  have hNZ : NeZero (addOrderOf a0) := ⟨(addOrderOf_pos a0).ne'⟩
  obtain ⟨z0, hz0⟩ := exists_kap_unit hem rfl
  by_cases hneg : -a0 ∈ A
  · exact Or.inl ⟨a0, ha0, hneg⟩
  refine Or.inr ⟨addOrderOf a0, hNZ, hem, hmax0, z0, ?_⟩
  unfold cntF
  rw [Units.val_neg, map_neg, hz0, Multiset.count_eq_zero.mpr hneg]
  have := Multiset.count_pos.mpr ha0
  omega

/-- **Hodge quadruples are decomposable.**  For `m` prime to `6`, four nonzero elements of
`ZMod m` with sum zero, whose representatives have a sum independent of the unit `t`, contain a
pair `a, -a`. -/
theorem quadruple (hm2 : ¬2 ∣ m) (hm3 : ¬3 ∣ m) (hB : BernoulliNV) (A : Multiset (ZMod m))
    (hcard : Multiset.card A = 4) (hA : A.sum = 0) (h : ℕ)
    (hH : ∀ t : (ZMod m)ˣ, (A.map fun a => ((t : ZMod m) * a).val).sum = h) :
    ∃ a ∈ A, -a ∈ A := by
  have hne : A ≠ 0 := by rintro rfl; simp at hcard
  rcases pair_or_pos A hne with hpair | ⟨e, hNZ, hem, hmax, x, hx⟩
  · exact hpair
  exfalso
  have he2 : ¬2 ∣ e := fun h2 => hm2 (h2.trans hem)
  have he3 : ¬3 ∣ e := fun h3 => hm3 (h3.trans hem)
  obtain ⟨p, hp57, hpe, w, hw⟩ := line_exists hm2 hm3 hem A hA (by omega) h hH hmax hB hx
  have hK := neg_one_not_mem_of_line (cntF_neg hem A) hw
  have hge := line_mass_ge hK (cntF_neg hem A) hw
  have hle : ∑ z, |cntF hem A z| ≤ 8 := by
    have := mass_cntF_le_card hem A
    rw [hcard] at this; push_cast at this; linarith
  rcases hp57 with rfl | rfl
  · rcases card_Kq_cases (by norm_num) hpe with hc | hc
    · rw [hc] at hge; push_cast at hge; linarith
    · rw [show (5 : ℕ) - 1 = 4 from rfl] at hc
      refine kill_line hpe he2 he3 (Or.inl hc) (cntF_neg hem A) hw
        (by rw [hc]; push_cast; linarith) (fun hs => sum_cntF_eq_zero hem A hA ?_)
      rw [hs, hc, hcard]
  · rcases card_Kq_cases (by norm_num) hpe with hc | hc <;>
      (try rw [show (7 : ℕ) - 1 = 6 from rfl] at hc) <;> rw [hc] at hge <;>
      push_cast at hge <;> linarith

end main

end FermatHodge
