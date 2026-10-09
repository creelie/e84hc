import FermatHodge.Slice

/-!
# The grid lemma

If the iterated differences of `f` along independent subgroups of order at least `4`
(at most one of order exactly `4`) vanish on a coset, and the `ℓ¹` mass of `f` on that coset
is at most `6`, then `f` is `0` there, or `±1` on one coset of one of the subgroups and `0`
elsewhere.
-/

open Finset

noncomputable section

namespace FermatHodge

open Classical

set_option linter.unusedSectionVars false

variable {G : Type*} [CommGroup G] [Fintype G]

/-- Two elements of a finset of masses: the sum over a pair is at most the total. -/
lemma pair_le_sum {s : Finset G} {μ : G → ℤ} (hμ : ∀ c ∈ s, 0 ≤ μ c) {c c' : G}
    (hc : c ∈ s) (hc' : c' ∈ s) (hne : c ≠ c') : μ c + μ c' ≤ ∑ d ∈ s, μ d := by
  have hsub : ({c, c'} : Finset G) ⊆ s := by
    intro y hy; simp only [mem_insert, mem_singleton] at hy; rcases hy with rfl | rfl <;> assumption
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y hy _ => hμ y hy)
  rwa [Finset.sum_pair hne] at this

/-- Translating a slice: if `f` agrees with its translate by `j` on the coset of `y`, the masses
agree. -/
lemma mass_eq_of_transl {Ks : List (Subgroup G)} {f : G → ℤ} {y j : G}
    (h : ∀ z ∈ cosetF Ks y, f z = f (z * j)) : mass Ks f y = mass Ks f (y * j) := by
  unfold mass
  rw [← sum_cosetF_mul Ks y j (fun z => |f z|)]
  exact Finset.sum_congr rfl (fun z hz => by rw [h z hz])

/-- If the slice at `c0` vanishes, every slice satisfies the condition for the tail. -/
lemma SIAt_slice_of_zero {K : Subgroup G} {Ks : List (Subgroup G)} {f : G → ℤ} {x c c0 : G}
    (hS : SIAt (K :: Ks) f x) (hc : c ∈ K) (hc0 : c0 ∈ K)
    (h0 : ∀ z ∈ cosetF Ks (x * c0), f z = 0) : SIAt Ks f (x * c) := by
  have hk : c⁻¹ * c0 ∈ K := K.mul_mem (K.inv_mem hc) hc0
  refine SIAt_congr Ks _ f (x * c) ?_ (hS c hc _ hk)
  intro z hz
  have : z * (c⁻¹ * c0) ∈ cosetF Ks (x * c0) := by
    have h1 := mul_mem_cosetF (c⁻¹ * c0) hz
    have h2 : x * c * (c⁻¹ * c0) = x * c0 := by group
    rwa [h2] at h1
  simp [h0 _ this]

theorem grid : ∀ (Ks : List (Subgroup G)), Indep Ks → (∀ K ∈ Ks, 4 ≤ Nat.card K) →
    Ks.countP (fun K : Subgroup G => Nat.card K = 4) ≤ 1 →
    ∀ (f : G → ℤ) (x : G), SIAt Ks f x → mass Ks f x ≤ 6 → (∃ z ∈ cosetF Ks x, f z ≠ 0) →
    ∃ K ∈ Ks, Nat.card K ≤ 6 ∧ ∃ w ∈ cosetF Ks x, ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      ∀ z ∈ cosetF Ks x, f z = if w⁻¹ * z ∈ K then σ else 0
  | [], _, _, _, f, x, hS, _, ⟨z, hz, hfz⟩ => by
      rw [cosetF_nil, Finset.mem_singleton] at hz; subst hz; exact absurd hS hfz
  | K :: Ks, hI, h4, hc4, f, x, hS, hm, hz => by
      obtain ⟨hI1, hI2⟩ := hI
      have h4' : ∀ K' ∈ Ks, 4 ≤ Nat.card K' := fun K' h => h4 K' (List.mem_cons_of_mem _ h)
      have hc4' : Ks.countP (fun K : Subgroup G => Nat.card K = 4) ≤ 1 :=
        le_trans (by rw [List.countP_cons]; omega) hc4
      have hK4 : 4 ≤ Nat.card K := h4 K (by simp)
      have hmass := mass_cons hI1 f x
      set μ : G → ℤ := fun c => mass Ks f (x * c) with hμdef
      have hμ0 : ∀ c, 0 ≤ μ c := fun c => mass_nonneg _ _ _
      have hsum : ∑ c ∈ Kf K, μ c ≤ 6 := by rw [← hmass]; exact hm
      -- P1: two unequal slices carry mass at least the order of some subgroup in the tail
      have P1 : ∀ c ∈ K, ∀ c' ∈ K,
          (∃ z ∈ cosetF Ks (x * c), f z ≠ f (z * (c⁻¹ * c'))) →
          ∃ K' ∈ Ks, 4 ≤ Nat.card K' ∧ (Nat.card K' : ℤ) ≤ μ c + μ c' := by
        intro c hc c' hc' ⟨z, hz, hne⟩
        have hcc : c ≠ c' := by rintro rfl; simp at hne
        have hk : c⁻¹ * c' ∈ K := K.mul_mem (K.inv_mem hc) hc'
        have hSg := hS c hc _ hk
        have hxc : x * c * (c⁻¹ * c') = x * c' := by group
        have hmg : mass Ks (fun z => f z - f (z * (c⁻¹ * c'))) (x * c) ≤ μ c + μ c' := by
          simp only [mass]
          calc ∑ z ∈ cosetF Ks (x * c), |f z - f (z * (c⁻¹ * c'))|
              ≤ ∑ z ∈ cosetF Ks (x * c), (|f z| + |f (z * (c⁻¹ * c'))|) :=
                Finset.sum_le_sum (fun z _ => abs_sub _ _)
            _ = μ c + μ c' := by
                rw [Finset.sum_add_distrib, sum_cosetF_mul Ks (x * c) _ (fun z => |f z|), hxc]
                rfl
        have h2 : μ c + μ c' ≤ 6 :=
          (pair_le_sum (fun d _ => hμ0 d) (by simpa using hc) (by simpa using hc') hcc).trans hsum
        obtain ⟨K', hK', -, w, hw, σ, hσ, hline⟩ :=
          grid Ks hI2 h4' hc4' _ (x * c) hSg (hmg.trans h2) ⟨z, hz, sub_ne_zero.mpr hne⟩
        refine ⟨K', hK', h4' K' hK', ?_⟩
        have hmass' : mass Ks (fun z => f z - f (z * (c⁻¹ * c'))) (x * c) = Nat.card K' := by
          simp only [mass]
          rw [Finset.sum_congr rfl (fun z hz => by beta_reduce; rw [hline z hz])]
          exact mass_line (le_lspan_of_mem hK') hw hσ
        rw [← hmass']; exact hmg
      by_cases hA : ∀ c ∈ K, ∀ z ∈ cosetF Ks (x * c), ∀ k ∈ K, f z = f (z * k)
      · -- Case A: `f` is `K`-invariant on the coset.
        have hinv : ∀ z ∈ cosetF (K :: Ks) x, ∀ k ∈ K, f (z * k) = f z := by
          intro z hz k hk
          obtain ⟨c, hc, hz'⟩ := mem_cosetF_cons.mp hz
          exact (hA c hc z hz' k hk).symm
        obtain ⟨z0, hz0, hf0⟩ := hz
        have hKle : K ≤ lspan (K :: Ks) := le_lspan_of_mem (by simp)
        -- orbit of a point
        have orbit : ∀ z1 ∈ cosetF (K :: Ks) x,
            (∀ z ∈ (cosetF (K :: Ks) x).filter (fun z => z1⁻¹ * z ∈ K), f z = f z1) ∧
            ((cosetF (K :: Ks) x).filter (fun z => z1⁻¹ * z ∈ K)).card = Nat.card K := by
          intro z1 hz1
          refine ⟨?_, card_line hKle hz1⟩
          intro z hz
          rw [Finset.mem_filter] at hz
          have : z = z1 * (z1⁻¹ * z) := by group
          rw [this, hinv z1 hz1 _ hz.2]
        have orbit_mass : ∀ z1 ∈ cosetF (K :: Ks) x,
            ∑ z ∈ (cosetF (K :: Ks) x).filter (fun z => z1⁻¹ * z ∈ K), |f z|
              = (Nat.card K : ℤ) * |f z1| := by
          intro z1 hz1
          rw [Finset.sum_congr rfl (fun z hz => by rw [(orbit z1 hz1).1 z hz]), Finset.sum_const,
            (orbit z1 hz1).2, nsmul_eq_mul]
        have hle : ∀ s ⊆ cosetF (K :: Ks) x, ∑ z ∈ s, |f z| ≤ mass (K :: Ks) f x :=
          fun s hs => Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => abs_nonneg _)
        have h1 : 1 ≤ |f z0| := Int.one_le_abs hf0
        have hO := hle _ (Finset.filter_subset (fun z => z0⁻¹ * z ∈ K) _)
        rw [orbit_mass z0 hz0] at hO
        have hK4' : (4 : ℤ) ≤ Nat.card K := by exact_mod_cast hK4
        have habs : |f z0| = 1 := by nlinarith
        have hKle6 : Nat.card K ≤ 6 := by
          rw [habs, mul_one] at hO; exact_mod_cast hO.trans hm
        have hzero : ∀ z1 ∈ cosetF (K :: Ks) x, ¬ z0⁻¹ * z1 ∈ K → f z1 = 0 := by
          intro z1 hz1 hnot
          by_contra hf1
          have hdisj : Disjoint ((cosetF (K :: Ks) x).filter (fun z => z0⁻¹ * z ∈ K))
              ((cosetF (K :: Ks) x).filter (fun z => z1⁻¹ * z ∈ K)) := by
            rw [Finset.disjoint_left]
            intro z hz hz'
            rw [Finset.mem_filter] at hz hz'
            apply hnot
            have : z0⁻¹ * z1 = (z0⁻¹ * z) * (z1⁻¹ * z)⁻¹ := by group
            rw [this]; exact K.mul_mem hz.2 (K.inv_mem hz'.2)
          have hU := hle _ (Finset.union_subset (Finset.filter_subset (fun z => z0⁻¹ * z ∈ K) _)
            (Finset.filter_subset (fun z => z1⁻¹ * z ∈ K) _))
          rw [Finset.sum_union hdisj, orbit_mass z0 hz0, orbit_mass z1 hz1] at hU
          have h1' : 1 ≤ |f z1| := Int.one_le_abs hf1
          nlinarith
        refine ⟨K, by simp, hKle6, z0, hz0, f z0, (abs_eq zero_le_one).mp habs, ?_⟩
        intro z hz
        split_ifs with h
        · exact (orbit z0 hz0).1 z (Finset.mem_filter.mpr ⟨hz, h⟩)
        · exact hzero z hz h
      · push_neg at hA
        obtain ⟨c, hc, zA, hzA, k, hk, hne⟩ := hA
        by_cases hB1 : ∃ c0 ∈ K, μ c0 = 0
        · -- Case B1: one slice vanishes.
          obtain ⟨c0, hc0, hμc0⟩ := hB1
          have h0 : ∀ z ∈ cosetF Ks (x * c0), f z = 0 := eq_zero_of_mass_eq_zero hμc0
          have line : ∀ c ∈ K, (∃ z ∈ cosetF Ks (x * c), f z ≠ 0) →
              ∃ K' ∈ Ks, Nat.card K' ≤ 6 ∧ ∃ w ∈ cosetF Ks (x * c), ∃ σ : ℤ,
                (σ = 1 ∨ σ = -1) ∧ ∀ z ∈ cosetF Ks (x * c),
                  f z = if w⁻¹ * z ∈ K' then σ else 0 := by
            intro c hc hnz
            have hc6 : μ c ≤ 6 := by
              have := Finset.single_le_sum (fun d _ => hμ0 d) (show c ∈ Kf K by simpa using hc)
              exact this.trans hsum
            exact grid Ks hI2 h4' hc4' f (x * c) (SIAt_slice_of_zero hS hc hc0 h0) hc6 hnz
          have line_mass : ∀ c ∈ K, (∃ z ∈ cosetF Ks (x * c), f z ≠ 0) → 4 ≤ μ c := by
            intro c hc hnz
            obtain ⟨K', hK', -, w, hw, σ, hσ, hl⟩ := line c hc hnz
            have : μ c = Nat.card K' := by
              simp only [hμdef, mass]
              rw [Finset.sum_congr rfl (fun z hz => by rw [hl z hz])]
              exact mass_line (le_lspan_of_mem hK') hw hσ
            rw [this]; exact_mod_cast h4' K' hK'
          obtain ⟨z1, hz1, hf1⟩ := hz
          obtain ⟨c1, hc1, hz1'⟩ := mem_cosetF_cons.mp hz1
          obtain ⟨K', hK', hK'6, w, hw, σ, hσ, hl⟩ := line c1 hc1 ⟨z1, hz1', hf1⟩
          have other : ∀ c2 ∈ K, c2 ≠ c1 → ∀ z ∈ cosetF Ks (x * c2), f z = 0 := by
            intro c2 hc2 hne2 z hz
            by_contra hfz
            have a1 := line_mass c1 hc1 ⟨z1, hz1', hf1⟩
            have a2 := line_mass c2 hc2 ⟨z, hz, hfz⟩
            have := pair_le_sum (fun d _ => hμ0 d) (show c1 ∈ Kf K by simpa using hc1)
              (show c2 ∈ Kf K by simpa using hc2) (Ne.symm hne2)
            linarith
          refine ⟨K', by simp [hK'], hK'6, w, mem_cosetF_cons_of hc1 hw, σ, hσ, ?_⟩
          intro z hz
          obtain ⟨c2, hc2, hz2⟩ := mem_cosetF_cons.mp hz
          by_cases h12 : c2 = c1
          · subst h12; exact hl z hz2
          · rw [other c2 hc2 h12 z hz2]
            have : ¬ w⁻¹ * z ∈ K' := by
              intro hwz
              have hz1'' : z ∈ cosetF Ks (x * c1) := by
                have := mem_cosetF_of_mem_lspan hw (le_lspan_of_mem hK' hwz)
                rwa [mul_inv_cancel_left] at this
              exact Finset.disjoint_left.mp (cosetF_disjoint hI1 hc2 hc1 h12) hz2 hz1''
            simp [this]
        · -- Case B2: every slice carries mass.
          push_neg at hB1
          have hμ1 : ∀ c ∈ K, 1 ≤ μ c := fun c hc =>
            lt_of_le_of_ne (hμ0 c) (Ne.symm (hB1 c hc))
          -- a slice of mass one
          have hstar : ∃ cs ∈ K, μ cs = 1 := by
            by_contra hno
            push_neg at hno
            have h2 : ∀ c ∈ Kf K, (2 : ℤ) ≤ μ c := by
              intro c hc
              have hc' : c ∈ K := by simpa using hc
              have := hμ1 c hc'; have := hno c hc'; omega
            have := Finset.card_nsmul_le_sum (Kf K) μ 2 h2
            rw [card_Kf, nsmul_eq_mul] at this
            have hK4' : (4 : ℤ) ≤ Nat.card K := by exact_mod_cast hK4
            linarith
          obtain ⟨cs, hcs, hμcs⟩ := hstar
          have hck : c * k ∈ K := K.mul_mem hc hk
          have hne' : ∃ z ∈ cosetF Ks (x * c), f z ≠ f (z * (c⁻¹ * (c * k))) :=
            ⟨zA, hzA, by rwa [inv_mul_cancel_left]⟩
          obtain ⟨K1, hK1, hK14, hK1μ⟩ := P1 c hc (c * k) hck hne'
          -- one of the two slices has mass at least two
          obtain ⟨c1, hc1, hμc1⟩ : ∃ c1 ∈ K, 2 ≤ μ c1 := by
            by_cases h : 2 ≤ μ c
            · exact ⟨c, hc, h⟩
            · refine ⟨c * k, hck, ?_⟩
              have : (4 : ℤ) ≤ Nat.card K1 := by exact_mod_cast hK14
              have := hμ1 c hc
              linarith
          -- the slice c1 differs from the slice cs
          have hdiff : ∃ z ∈ cosetF Ks (x * c1), f z ≠ f (z * (c1⁻¹ * cs)) := by
            by_contra hall
            push_neg at hall
            have := mass_eq_of_transl hall
            have h2 : x * c1 * (c1⁻¹ * cs) = x * cs := by group
            rw [h2] at this
            change μ c1 = μ cs at this
            linarith
          obtain ⟨K2, hK2, hK24, hK2μ⟩ := P1 c1 hc1 cs hcs hdiff
          have hK24' : (4 : ℤ) ≤ Nat.card K2 := by exact_mod_cast hK24
          have hμc1' : 3 ≤ μ c1 := by linarith
          -- total mass
          have htot : μ c1 + ((Kf K).card - 1 : ℤ) ≤ ∑ d ∈ Kf K, μ d := by
            have hc1f : c1 ∈ Kf K := by simpa using hc1
            rw [← Finset.add_sum_erase _ _ hc1f]
            have h3 : ((Kf K).erase c1).card • (1 : ℤ) ≤ ∑ d ∈ (Kf K).erase c1, μ d :=
              Finset.card_nsmul_le_sum _ _ _ (fun d hd => hμ1 d (by
                simpa using (Finset.mem_of_mem_erase hd)))
            rw [Finset.card_erase_of_mem hc1f, nsmul_eq_mul, mul_one] at h3
            have hpos : 1 ≤ (Kf K).card := by rw [card_Kf]; omega
            push_cast [Nat.cast_sub hpos] at h3
            linarith
          rw [card_Kf] at htot
          have hK4' : (4 : ℤ) ≤ Nat.card K := by exact_mod_cast hK4
          have hKeq : Nat.card K = 4 := by
            have : (Nat.card K : ℤ) ≤ 4 := by linarith
            exact_mod_cast le_antisymm this hK4'
          have hK2eq : Nat.card K2 = 4 := by
            have : (Nat.card K2 : ℤ) ≤ 4 := by linarith
            exact_mod_cast le_antisymm this hK24'
          have hpos : 0 < Ks.countP (fun K : Subgroup G => Nat.card K = 4) :=
            List.countP_pos_iff.mpr ⟨K2, hK2, decide_eq_true hK2eq⟩
          have hcons : (K :: Ks).countP (fun K : Subgroup G => Nat.card K = 4)
              = Ks.countP (fun K : Subgroup G => Nat.card K = 4) + 1 := by
            rw [List.countP_cons, if_pos (decide_eq_true hKeq)]
          omega

end FermatHodge
