import FermatHodge.Grid

/-!
# Peeling large subgroups, and the sign-symmetric cases
-/

open Finset

noncomputable section

namespace FermatHodge

open Classical

set_option linter.unusedSectionVars false

variable {G : Type*} [CommGroup G] [Fintype G]

lemma cosetF_subset_cons {K : Subgroup G} {Ks : List (Subgroup G)} (x : G) :
    cosetF Ks x ⊆ cosetF (K :: Ks) x := by
  intro z hz
  have := mem_cosetF_cons_of (K := K) (c := 1) K.one_mem (by rwa [mul_one])
  exact this

lemma mass_le_cons {K : Subgroup G} {Ks : List (Subgroup G)} (f : G → ℤ) (x : G) :
    mass Ks f x ≤ mass (K :: Ks) f x :=
  Finset.sum_le_sum_of_subset_of_nonneg (cosetF_subset_cons x) (fun _ _ _ => abs_nonneg _)

/-- If the mass is smaller than the order of the first subgroup, some slice vanishes, and so the
condition passes to every slice. -/
theorem peel {K : Subgroup G} {Ks : List (Subgroup G)} (hI : K ⊓ lspan Ks = ⊥) {f : G → ℤ}
    {x : G} (hS : SIAt (K :: Ks) f x) (hm : mass (K :: Ks) f x < Nat.card K) :
    ∀ c ∈ K, SIAt Ks f (x * c) := by
  have hex : ∃ c0 ∈ K, mass Ks f (x * c0) = 0 := by
    by_contra hno
    push_neg at hno
    have h1 : ∀ c ∈ Kf K, (1 : ℤ) ≤ mass Ks f (x * c) := fun c hc =>
      lt_of_le_of_ne (mass_nonneg _ _ _) (Ne.symm (hno c (by simpa using hc)))
    have := Finset.card_nsmul_le_sum (Kf K) (fun c => mass Ks f (x * c)) 1 h1
    rw [card_Kf, nsmul_eq_mul, mul_one, ← mass_cons hI] at this
    linarith
  obtain ⟨c0, hc0, h0⟩ := hex
  intro c hc
  exact SIAt_slice_of_zero hS hc hc0 (eq_zero_of_mass_eq_zero h0)

theorem peel_list : ∀ (Ls Ss : List (Subgroup G)) (f : G → ℤ) (x : G), Indep (Ls ++ Ss) →
    SIAt (Ls ++ Ss) f x → (∀ L ∈ Ls, mass (Ls ++ Ss) f x < Nat.card L) → SIAt Ss f x
  | [], Ss, f, x, _, hS, _ => hS
  | L :: Ls, Ss, f, x, hI, hS, hm => by
      have h1 := peel hI.1 hS (hm L (by simp)) 1 L.one_mem
      rw [mul_one] at h1
      refine peel_list Ls Ss f x hI.2 h1 (fun L' hL' => ?_)
      exact lt_of_le_of_lt (mass_le_cons (K := L) f x) (hm L' (by simp [hL']))

/-- One subgroup containing the sign: the function vanishes. -/
lemma odd_single {K : Subgroup G} {f : G → ℤ} {x η : G} (hS : SIAt [K] f x) (hη : η ∈ K)
    (hodd : f (x * η) = -f x) : f x = 0 := by
  have := hS 1 K.one_mem η hη
  simp only [SIAt, mul_one] at this
  linarith

lemma Indep_cons_iff {K : Subgroup G} {Ks : List (Subgroup G)} :
    Indep (K :: Ks) ↔ K ⊓ lspan Ks = ⊥ ∧ Indep Ks := Iff.rfl

/-- A large subgroup carrying part of the sign: some slice is a full positive line. -/
theorem odd_big {K : Subgroup G} {Ks : List (Subgroup G)} (hI : Indep (K :: Ks))
    (h4 : ∀ K' ∈ Ks, 4 ≤ Nat.card K')
    (hc4 : Ks.countP (fun K : Subgroup G => Nat.card K = 4) ≤ 1) (hK : 10 ≤ Nat.card K)
    {ε ε' : G} (hε : ε ∈ K) (hε' : ε' ∈ lspan Ks) (hε1 : ε ≠ 1)
    {f : G → ℤ} {x : G} (hS : SIAt (K :: Ks) f x)
    (hodd : ∀ z ∈ cosetF (K :: Ks) x, f (z * (ε * ε')) = -f z)
    (hm : mass (K :: Ks) f x ≤ 12) (hx : 1 ≤ f x) :
    ∃ K' ∈ Ks, Nat.card K' ≤ 6 ∧ ∃ w ∈ cosetF (K :: Ks) x, ∀ k ∈ K', 1 ≤ f (w * k) := by
  obtain ⟨hI1, hI2⟩ := hI
  set μ : G → ℤ := fun c => mass Ks f (x * c) with hμdef
  have hμ0 : ∀ c, 0 ≤ μ c := fun c => mass_nonneg _ _ _
  have hsum : ∑ c ∈ Kf K, μ c ≤ 12 := by rw [← mass_cons hI1]; exact hm
  -- the sign pairs the slice of `c` with the slice of `c * ε`
  have hpair : ∀ c ∈ K, μ (c * ε) = μ c := by
    intro c hc
    simp only [hμdef, mass]
    have h1 : ∑ z ∈ cosetF Ks (x * c), |f z| = ∑ z ∈ cosetF Ks (x * c), |f (z * (ε * ε'))| := by
      refine Finset.sum_congr rfl (fun z hz => ?_)
      rw [hodd z (mem_cosetF_cons_of hc hz), abs_neg]
    rw [h1, sum_cosetF_mul Ks (x * c) (ε * ε') (fun z => |f z|)]
    have h2 : cosetF Ks (x * c * (ε * ε')) = cosetF Ks (x * (c * ε)) := by
      apply cosetF_eq_of_mem
      rw [mem_cosetF]
      have : (x * (c * ε))⁻¹ * (x * c * (ε * ε')) = ε' := by group
      rw [this]; exact hε'
    rw [h2]
  have hεK : (1 : G) * ε ∈ K := by simpa using hε
  have hne1 : (1 : G) ≠ 1 * ε := by rw [one_mul]; exact fun h => hε1 h.symm
  by_cases h0 : ∃ c0 ∈ K, μ c0 = 0
  · obtain ⟨c0, hc0, hμc0⟩ := h0
    have hS1 : SIAt Ks f (x * 1) :=
      SIAt_slice_of_zero hS K.one_mem hc0 (eq_zero_of_mass_eq_zero hμc0)
    rw [mul_one] at hS1
    have hμ1 : μ 1 ≤ 6 := by
      have hp := pair_le_sum (fun d _ => hμ0 d) (show (1 : G) ∈ Kf K by simp)
        (show 1 * ε ∈ Kf K by simpa using hεK) hne1
      have := hpair 1 K.one_mem
      linarith
    have hμ1' : mass Ks f x ≤ 6 := by simpa [hμdef] using hμ1
    obtain ⟨K', hK', hK'6, w, hw, σ, hσ, hl⟩ :=
      grid Ks hI2 h4 hc4 f x hS1 hμ1' ⟨x, self_mem_cosetF _ _, by omega⟩
    have hxl := hl x (self_mem_cosetF _ _)
    have hin : w⁻¹ * x ∈ K' := by
      by_contra hn; rw [if_neg hn] at hxl; omega
    rw [if_pos hin] at hxl
    have hσ1 : σ = 1 := by rcases hσ with h | h <;> omega
    refine ⟨K', hK', hK'6, w, cosetF_subset_cons x hw, fun k hk => ?_⟩
    have hwk : w * k ∈ cosetF Ks x := mem_cosetF_of_mem_lspan hw (le_lspan_of_mem hK' hk)
    rw [hl _ hwk, if_pos (by simpa using hk), hσ1]
  · push_neg at h0
    have hμ1 : ∀ c ∈ K, 1 ≤ μ c := fun c hc => lt_of_le_of_ne (hμ0 c) (Ne.symm (h0 c hc))
    obtain ⟨c, hc, hμc⟩ : ∃ c ∈ K, μ c = 1 := by
      by_contra hno
      push_neg at hno
      have h2 : ∀ c ∈ Kf K, (2 : ℤ) ≤ μ c := by
        intro c hc
        have hc' : c ∈ K := by simpa using hc
        have := hμ1 c hc'; have := hno c hc'; omega
      have := Finset.card_nsmul_le_sum (Kf K) μ 2 h2
      rw [card_Kf, nsmul_eq_mul] at this
      have : (10 : ℤ) ≤ Nat.card K := by exact_mod_cast hK
      linarith
    have hcε : c * ε ∈ K := K.mul_mem hc hε
    have hμcε : μ (c * ε) = 1 := by rw [hpair c hc, hμc]
    -- the two slices agree after translation by ε
    have heq : ∀ z ∈ cosetF Ks (x * c), f z = f (z * ε) := by
      by_contra hall
      push_neg at hall
      obtain ⟨z, hz, hne⟩ := hall
      have hSg := hS c hc ε hε
      have hmg : mass Ks (fun z => f z - f (z * ε)) (x * c) ≤ 2 := by
        simp only [mass]
        calc ∑ z ∈ cosetF Ks (x * c), |f z - f (z * ε)|
            ≤ ∑ z ∈ cosetF Ks (x * c), (|f z| + |f (z * ε)|) :=
              Finset.sum_le_sum (fun z _ => abs_sub _ _)
          _ = μ c + μ (c * ε) := by
              rw [Finset.sum_add_distrib, sum_cosetF_mul Ks (x * c) _ (fun z => |f z|),
                mul_assoc]
              rfl
          _ = 2 := by rw [hμc, hμcε]; norm_num
      obtain ⟨K', hK', -, w, hw, σ, hσ, hl⟩ :=
        grid Ks hI2 h4 hc4 _ (x * c) hSg (by linarith) ⟨z, hz, sub_ne_zero.mpr hne⟩
      have : mass Ks (fun z => f z - f (z * ε)) (x * c) = Nat.card K' := by
        simp only [mass]
        rw [Finset.sum_congr rfl (fun z hz => by beta_reduce; rw [hl z hz])]
        exact mass_line (le_lspan_of_mem hK') hw hσ
      have := h4 K' hK'
      have : (4 : ℤ) ≤ Nat.card K' := by exact_mod_cast this
      linarith
    -- the unique point of the slice of `c`
    obtain ⟨z0, hz0, hf0⟩ : ∃ z0 ∈ cosetF Ks (x * c), f z0 ≠ 0 := by
      by_contra hno; push_neg at hno
      have : μ c = 0 := Finset.sum_eq_zero (fun z hz => by simp [hno z hz])
      omega
    have hz1 : z0 * ε ∈ cosetF Ks (x * (c * ε)) := by
      have := mul_mem_cosetF ε hz0; rwa [mul_assoc] at this
    have hz2 : z0 * (ε * ε') ∈ cosetF Ks (x * (c * ε)) := by
      have := mem_cosetF_of_mem_lspan hz1 hε'; rwa [mul_assoc] at this
    have hv1 : f (z0 * ε) = f z0 := (heq z0 hz0).symm
    have hv2 : f (z0 * (ε * ε')) = -f z0 := hodd z0 (mem_cosetF_cons_of hc hz0)
    have hdist : z0 * ε = z0 * (ε * ε') := by
      by_contra hd
      have hp := pair_le_sum (s := cosetF Ks (x * (c * ε))) (μ := fun z => |f z|)
        (fun _ _ => abs_nonneg _) hz1 hz2 hd
      have : ∑ z ∈ cosetF Ks (x * (c * ε)), |f z| = 1 := hμcε
      rw [this, hv1, hv2, abs_neg] at hp
      have := Int.one_le_abs hf0
      linarith
    rw [hdist] at hv1
    rw [hv1] at hv2
    exact absurd (by omega : f z0 = 0) hf0

end FermatHodge
