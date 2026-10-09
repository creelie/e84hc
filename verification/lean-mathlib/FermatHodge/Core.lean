import FermatHodge.Units

/-!
# The core lemma at a maximal order

Let `e` be prime to `6`, and let `F` be an odd integer function on `(ZMod e)ˣ` of total mass at
most `12` that satisfies the iterated difference condition for the subgroups `K_p`, `p ∣ e`, in
every order. If `F` is positive somewhere, then `F ≥ 1` along a whole coset of `K_5` or `K_7`,
or `e` has the prime factors `5` and `7` only and `F` is a half-system product on a coset of
`K_5 K_7`.
-/

open Finset

noncomputable section

namespace FermatHodge

open Classical

set_option linter.unusedSectionVars false

section lspan

variable {G : Type*} [CommGroup G] [Fintype G]

lemma lspan_le_of_subset : ∀ (Ks Ks' : List (Subgroup G)), (∀ K ∈ Ks, K ∈ Ks') →
    lspan Ks ≤ lspan Ks'
  | [], _, _ => by simp
  | K :: Ks, Ks', h => by
      rw [lspan_cons]
      exact sup_le (le_lspan_of_mem (h K (by simp)))
        (lspan_le_of_subset Ks Ks' (fun K' hK' => h K' (by simp [hK'])))

lemma lspan_perm {Ks Ks' : List (Subgroup G)} (h : Ks.Perm Ks') : lspan Ks = lspan Ks' :=
  le_antisymm (lspan_le_of_subset _ _ (fun _ hK => h.mem_iff.mp hK))
    (lspan_le_of_subset _ _ (fun _ hK => h.mem_iff.mpr hK))

lemma Indep_of_perm_map {ps qs : List ℕ} {Kf' : ℕ → Subgroup G} (h : ps.Perm qs) :
    (ps.map Kf').Perm (qs.map Kf') := h.map _

end lspan

section cards

variable {e : ℕ} [NeZero e]

lemma five_le_of_dvd {p : ℕ} (hp : p.Prime) (hpe : p ∣ e) (he2 : ¬2 ∣ e) (he3 : ¬3 ∣ e) :
    5 ≤ p := by
  have h2 := hp.two_le
  have hp2 : p ≠ 2 := by rintro rfl; exact he2 hpe
  have hp3 : p ≠ 3 := by rintro rfl; exact he3 hpe
  have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
  omega

lemma four_le_card {p : ℕ} (hp : p.Prime) (hpe : p ∣ e) (he2 : ¬2 ∣ e) (he3 : ¬3 ∣ e) :
    4 ≤ Nat.card (Kq e p) := by
  have := five_le_of_dvd hp hpe he2 he3
  rcases card_Kq_cases hp hpe with h | h <;> omega

lemma eq_five_or_seven {p : ℕ} (hp : p.Prime) (hpe : p ∣ e) (he2 : ¬2 ∣ e) (he3 : ¬3 ∣ e)
    (hc : Nat.card (Kq e p) ≤ 9) : p = 5 ∨ p = 7 := by
  have h5 := five_le_of_dvd hp hpe he2 he3
  have h10 : p ≤ 10 := by rcases card_Kq_cases hp hpe with h | h <;> omega
  interval_cases p <;> first | exact Or.inl rfl | exact Or.inr rfl | (exfalso; norm_num at hp)

lemma eq_five_of_card_four {p : ℕ} (hp : p.Prime) (hpe : p ∣ e) (hc : Nat.card (Kq e p) = 4) :
    p = 5 := by
  rcases card_Kq_cases hp hpe with h | h
  · rw [hc] at h; subst h; norm_num at hp
  · omega

lemma countP_card_four (ps : List ℕ) (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p.Prime ∧ p ∣ e) :
    (ps.map (Kq e)).countP (fun K : Subgroup (ZMod e)ˣ => Nat.card K = 4) ≤ 1 := by
  rw [List.countP_map]
  calc ps.countP ((fun K : Subgroup (ZMod e)ˣ => decide (Nat.card K = 4)) ∘ Kq e)
      ≤ ps.countP (fun p => decide (p = 5)) := by
        apply List.countP_mono_left
        intro p hp h
        simp only [Function.comp_apply, decide_eq_true_eq] at h ⊢
        exact eq_five_of_card_four (hps p hp).1 (hps p hp).2 h
    _ = ps.count 5 := by
        rw [List.count]; first | rfl | (congr 1; funext p; simp [beq_iff_eq])
    _ ≤ 1 := List.nodup_iff_count_le_one.mp hnd 5

end cards

section core

variable {e : ℕ} [NeZero e]

lemma mass_neg_one {Ks : List (Subgroup (ZMod e)ˣ)} {F : (ZMod e)ˣ → ℤ}
    (hodd : ∀ z, F (-z) = -F z) (x : (ZMod e)ˣ) : mass Ks F (x * (-1)) = mass Ks F x := by
  simp only [mass]
  rw [← sum_cosetF_mul Ks x (-1) (fun z => |F z|)]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [mul_neg_one, hodd, abs_neg]

lemma cosetF_disjoint_neg {Ks : List (Subgroup (ZMod e)ˣ)} (h : (-1 : (ZMod e)ˣ) ∉ lspan Ks)
    (x : (ZMod e)ˣ) : Disjoint (cosetF Ks x) (cosetF Ks (x * (-1))) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [mem_cosetF] at hz hz'
  apply h
  have : (x⁻¹ * z) * ((x * (-1))⁻¹ * z)⁻¹ = -1 := by group
  rw [← this]
  exact (lspan Ks).mul_mem hz ((lspan Ks).inv_mem hz')

theorem core (he2 : ¬2 ∣ e) (he3 : ¬3 ∣ e) (ps : List ℕ) (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, p.Prime ∧ p ∣ e)
    (F : (ZMod e)ˣ → ℤ) (hodd : ∀ z, F (-z) = -F z) (hmass : ∑ z, |F z| ≤ 12)
    (hcond : ∀ Ks : List (Subgroup (ZMod e)ˣ), Ks.Perm (ps.map (Kq e)) → ∀ x, SIAt Ks F x)
    {x : (ZMod e)ˣ} (hx : 1 ≤ F x) :
    (∃ p ∈ ps, (p = 5 ∨ p = 7) ∧ ∃ w : (ZMod e)ˣ, ∀ k ∈ Kq e p, 1 ≤ F (w * k)) ∨
    (5 ∈ ps ∧ 7 ∈ ps ∧ ∃ y : (ZMod e)ˣ, ∃ ε ∈ Kq e 5, ∃ ε' ∈ Kq e 7, ε * ε' = -1 ∧
      Nat.card (Kq e 5) = 4 ∧ Nat.card (Kq e 7) = 6 ∧ mass [Kq e 5, Kq e 7] F y = 12 ∧
      ∃ u v : (ZMod e)ˣ → ℤ, (∀ i ∈ Kq e 5, u i = 1 ∨ u i = -1) ∧
        (∀ j ∈ Kq e 7, v j = 1 ∨ v j = -1) ∧
        (∀ i ∈ Kq e 5, u (i * ε) = -u i) ∧ (∀ j ∈ Kq e 7, v (j * ε') = -v j) ∧
        ∀ i ∈ Kq e 5, ∀ j ∈ Kq e 7, 2 * F (y * i * j) = u i + v j) := by
  set Ks0 := ps.map (Kq e) with hKs0
  have hI0 : Indep Ks0 := indep_Kq ps hnd hps
  have h4 : ∀ K ∈ Ks0, 4 ≤ Nat.card K := by
    intro K hK
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hK
    exact four_le_card (hps p hp).1 (hps p hp).2 he2 he3
  have hc4 := countP_card_four ps hnd hps
  have hmass_le : ∀ (Ks : List (Subgroup (ZMod e)ˣ)) (y : (ZMod e)ˣ), mass Ks F y ≤ 12 :=
    fun Ks y => le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => abs_nonneg _)) hmass
  -- a line in one of the `K_p` of order at most `9` gives the first alternative
  have hline : ∀ K ∈ Ks0, Nat.card K ≤ 9 → ∀ w : (ZMod e)ˣ, (∀ k ∈ K, 1 ≤ F (w * k)) →
      ∃ p ∈ ps, (p = 5 ∨ p = 7) ∧ ∃ w : (ZMod e)ˣ, ∀ k ∈ Kq e p, 1 ≤ F (w * k) := by
    intro K hK hc w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hK
    exact ⟨p, hp, eq_five_or_seven (hps p hp).1 (hps p hp).2 he2 he3 hc, w, hw⟩
  by_cases hneg : (-1 : (ZMod e)ˣ) ∈ lspan Ks0
  swap
  · -- `-1` is not in the span: the coset of `x` carries at most half the mass
    left
    have hdisj := cosetF_disjoint_neg hneg x
    have hm6 : mass Ks0 F x ≤ 6 := by
      have h1 : mass Ks0 F x + mass Ks0 F (x * (-1)) ≤ 12 := by
        simp only [mass]
        rw [← Finset.sum_union hdisj]
        exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => abs_nonneg _)) hmass
      rw [mass_neg_one hodd] at h1
      linarith
    obtain ⟨K, hK, hK6, w, hw, σ, hσ, hl⟩ :=
      grid Ks0 hI0 h4 hc4 F x (hcond Ks0 (List.Perm.refl _) x) hm6
        ⟨x, self_mem_cosetF _ _, by omega⟩
    have hwk : ∀ k ∈ K, w * k ∈ cosetF Ks0 x :=
      fun k hk => mem_cosetF_of_mem_lspan hw (le_lspan_of_mem hK hk)
    rcases hσ with rfl | rfl
    · refine hline K hK (by omega) w (fun k hk => ?_)
      rw [hl _ (hwk k hk), if_pos (by simpa using hk)]
    · refine hline K hK (by omega) (w * (-1)) (fun k hk => ?_)
      have := hl _ (hwk k hk)
      rw [if_pos (by simpa using hk)] at this
      rw [mul_right_comm, mul_neg_one, hodd, this]; norm_num
  · -- `-1` lies in the span
    by_cases hbig : ∃ p ∈ ps, 10 ≤ Nat.card (Kq e p)
    · left
      obtain ⟨p, hp, hp10⟩ := hbig
      set rest := (ps.erase p).map (Kq e) with hrest
      have hperm : (ps.map (Kq e)).Perm (Kq e p :: rest) := by
        have := (List.perm_cons_erase hp).map (Kq e)
        simpa using this
      have hnd' : (p :: ps.erase p).Nodup := (List.perm_cons_erase hp).nodup_iff.mp hnd
      have hps' : ∀ q ∈ p :: ps.erase p, q.Prime ∧ q ∣ e :=
        fun q hq => hps q ((List.perm_cons_erase hp).mem_iff.mpr hq)
      have hI : Indep (Kq e p :: rest) := by
        have := indep_Kq (p :: ps.erase p) hnd' hps'
        simpa using this
      have hS : SIAt (Kq e p :: rest) F x := hcond _ hperm.symm x
      have hneg' : (-1 : (ZMod e)ˣ) ∈ Kq e p ⊔ lspan rest := by
        rw [← lspan_cons, ← lspan_perm hperm, ← hKs0]; exact hneg
      obtain ⟨ε, hε, ε', hε', hεε⟩ := Subgroup.mem_sup.mp hneg'
      have hprest : ∀ q ∈ ps.erase p, q.Prime ∧ q ∣ e ∧ q ≠ p := by
        intro q hq
        refine ⟨(hps' q (by simp [hq])).1, (hps' q (by simp [hq])).2, ?_⟩
        rintro rfl; exact (List.nodup_cons.mp hnd').1 hq
      have hp2 : p ≠ 2 := by intro h; apply he2; rw [← h]; exact (hps p hp).2
      have hε1 : ε ≠ 1 := by
        rintro rfl
        rw [one_mul] at hεε
        exact neg_one_not_mem_lspan (hps p hp).1 hp2 (hps p hp).2 _ hprest
          (by rw [← hεε]; exact hε')
      have h4' : ∀ K' ∈ rest, 4 ≤ Nat.card K' :=
        fun K' hK' => h4 K' (hperm.mem_iff.mpr (List.mem_cons_of_mem _ hK'))
      have hc4' : rest.countP (fun K : Subgroup (ZMod e)ˣ => Nat.card K = 4) ≤ 1 := by
        have := countP_card_four (p :: ps.erase p) hnd' hps'
        simp only [List.map_cons, List.countP_cons] at this
        rw [hrest]; omega
      obtain ⟨K', hK', hK'6, w, -, hw⟩ := odd_big hI h4' hc4' hp10 hε hε' hε1 hS
        (fun z _ => by rw [hεε, mul_neg_one, hodd]) (hmass_le _ _) hx
      exact hline K' (hperm.mem_iff.mpr (List.mem_cons_of_mem _ hK')) (by omega) w hw
    · push_neg at hbig
      have h57 : ∀ p ∈ ps, p = 5 ∨ p = 7 :=
        fun p hp => eq_five_or_seven (hps p hp).1 (hps p hp).2 he2 he3 (by
          have := hbig p hp; omega)
      -- `-1 ≠ 1`, so `ps` is not empty
      have hne1 : (-1 : (ZMod e)ˣ) ≠ 1 := by
        intro h1
        have := hodd x
        rw [show (-x : (ZMod e)ˣ) = x * (-1) by rw [mul_neg_one], h1, mul_one] at this
        omega
      by_cases h5 : 5 ∈ ps
      · by_cases h7 : 7 ∈ ps
        · -- both primes: the two-coordinate case
          have hperm : (ps.map (Kq e)).Perm [Kq e 5, Kq e 7] := by
            refine List.Perm.map (Kq e) (l₂ := [5, 7]) ?_
            rw [List.perm_ext_iff_of_nodup hnd (by simp)]
            intro q
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
            constructor
            · intro hq; exact h57 q hq
            · rintro (rfl | rfl) <;> assumption
          have hI : Indep [Kq e 5, Kq e 7] :=
            indep_Kq [5, 7] (by simp) (fun q hq => by
              simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
              rcases hq with rfl | rfl
              · exact hps 5 h5
              · exact hps 7 h7)
          have hI1 : Kq e 5 ⊓ Kq e 7 = ⊥ := by simpa using hI.1
          have hS : SIAt [Kq e 5, Kq e 7] F x := hcond _ hperm.symm x
          have hneg' : (-1 : (ZMod e)ˣ) ∈ Kq e 5 ⊔ Kq e 7 := by
            rw [hKs0, lspan_perm hperm] at hneg; simpa using hneg
          obtain ⟨ε, hε, ε', hε', hεε⟩ := Subgroup.mem_sup.mp hneg'
          have hr5 : ∀ q ∈ [7], q.Prime ∧ q ∣ e ∧ q ≠ 5 := by
            intro q hq; simp only [List.mem_singleton] at hq; subst hq
            exact ⟨(hps 7 h7).1, (hps 7 h7).2, by norm_num⟩
          have hr7 : ∀ q ∈ [5], q.Prime ∧ q ∣ e ∧ q ≠ 7 := by
            intro q hq; simp only [List.mem_singleton] at hq; subst hq
            exact ⟨(hps 5 h5).1, (hps 5 h5).2, by norm_num⟩
          have hn5 := neg_one_not_mem_lspan (hps 5 h5).1 (by norm_num) (hps 5 h5).2 [7] hr5
          have hn7 := neg_one_not_mem_lspan (hps 7 h7).1 (by norm_num) (hps 7 h7).2 [5] hr7
          simp only [List.map_cons, List.map_nil, lspan_cons, lspan_nil, sup_bot_eq] at hn5 hn7
          have hε1 : ε ≠ 1 := by
            rintro rfl; rw [one_mul] at hεε; exact hn5 (by rw [← hεε]; exact hε')
          have hε1' : ε' ≠ 1 := by
            rintro rfl; rw [mul_one] at hεε; exact hn7 (by rw [← hεε]; exact hε)
          -- squares: `ε² ε'² = 1`, and the two subgroups meet trivially
          have hsq : ε * ε = 1 ∧ ε' * ε' = 1 := by
            have h1 : (ε * ε) * (ε' * ε') = 1 := by
              calc (ε * ε) * (ε' * ε') = (ε * ε') * (ε * ε') := mul_mul_mul_comm ε ε ε' ε'
                _ = 1 := by rw [hεε]; simp
            have hm : ε * ε ∈ Kq e 5 ⊓ Kq e 7 := by
              refine ⟨(Kq e 5).mul_mem hε hε, ?_⟩
              have : ε * ε = (ε' * ε')⁻¹ := eq_inv_of_mul_eq_one_left h1
              rw [this]; exact (Kq e 7).inv_mem ((Kq e 7).mul_mem hε' hε')
            rw [hI1, Subgroup.mem_bot] at hm
            refine ⟨hm, ?_⟩
            rw [hm, one_mul] at h1; exact h1
          have hc5 : Nat.card (Kq e 5) = 4 := by
            rcases card_Kq_cases (hps 5 h5).1 (hps 5 h5).2 with h | h
            · exfalso
              have hdvd : orderOf (⟨ε, hε⟩ : Kq e 5) ∣ 5 := by
                have := orderOf_dvd_natCard (⟨ε, hε⟩ : Kq e 5); rwa [h] at this
              have hdvd2 : orderOf (⟨ε, hε⟩ : Kq e 5) ∣ 2 :=
                orderOf_dvd_of_pow_eq_one (by ext; simp [pow_two, hsq.1])
              have : orderOf (⟨ε, hε⟩ : Kq e 5) = 1 :=
                Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 5 2) hdvd hdvd2
              rw [orderOf_eq_one_iff] at this
              exact hε1 (congrArg Subtype.val this)
            · simpa using h
          have hc7 : Nat.card (Kq e 7) = 6 := by
            rcases card_Kq_cases (hps 7 h7).1 (hps 7 h7).2 with h | h
            · exfalso
              have hdvd : orderOf (⟨ε', hε'⟩ : Kq e 7) ∣ 7 := by
                have := orderOf_dvd_natCard (⟨ε', hε'⟩ : Kq e 7); rwa [h] at this
              have hdvd2 : orderOf (⟨ε', hε'⟩ : Kq e 7) ∣ 2 :=
                orderOf_dvd_of_pow_eq_one (by ext; simp [pow_two, hsq.2])
              have : orderOf (⟨ε', hε'⟩ : Kq e 7) = 1 :=
                Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 7 2) hdvd hdvd2
              rw [orderOf_eq_one_iff] at this
              exact hε1' (congrArg Subtype.val this)
            · simpa using h
          have hodd2 : ∀ z ∈ cosetF [Kq e 5, Kq e 7] x, F (z * (ε * ε')) = -F z :=
            fun z _ => by rw [hεε, mul_neg_one, hodd]
          rcases twoD hI1 hc5 hc7 hε hε' hε1 hε1' hsq.1 hS hodd2 (hmass_le _ _) hx with
            hK | hL | ⟨hm12, u, v, hu, hv, hu', hv', huv⟩
          · left; exact ⟨5, h5, Or.inl rfl, x, fun k hk => (hK k hk).ge⟩
          · left; exact ⟨7, h7, Or.inr rfl, x, fun k hk => (hL k hk).ge⟩
          · right
            exact ⟨h5, h7, x, ε, hε, ε', hε', hεε, hc5, hc7, hm12, u, v, hu, hv, hu', hv', huv⟩
        · -- only `5`
          exfalso
          have hperm : (ps.map (Kq e)).Perm [Kq e 5] := by
            refine List.Perm.map (Kq e) (l₂ := [5]) ?_
            rw [List.perm_ext_iff_of_nodup hnd (by simp)]
            intro q
            simp only [List.mem_singleton]
            constructor
            · intro hq
              rcases h57 q hq with rfl | rfl
              · rfl
              · exact absurd hq h7
            · rintro rfl; exact h5
          have hS : SIAt [Kq e 5] F x := hcond _ hperm.symm x
          have hneg' : (-1 : (ZMod e)ˣ) ∈ Kq e 5 := by
            rw [hKs0, lspan_perm hperm] at hneg; simpa using hneg
          have := odd_single hS hneg' (by rw [mul_neg_one, hodd])
          omega
      · by_cases h7 : 7 ∈ ps
        · -- only `7`
          exfalso
          have hperm : (ps.map (Kq e)).Perm [Kq e 7] := by
            refine List.Perm.map (Kq e) (l₂ := [7]) ?_
            rw [List.perm_ext_iff_of_nodup hnd (by simp)]
            intro q
            simp only [List.mem_singleton]
            constructor
            · intro hq
              rcases h57 q hq with rfl | rfl
              · exact absurd hq h5
              · rfl
            · rintro rfl; exact h7
          have hS : SIAt [Kq e 7] F x := hcond _ hperm.symm x
          have hneg' : (-1 : (ZMod e)ˣ) ∈ Kq e 7 := by
            rw [hKs0, lspan_perm hperm] at hneg; simpa using hneg
          have := odd_single hS hneg' (by rw [mul_neg_one, hodd])
          omega
        · -- no primes at all
          exfalso
          have hnil : ps = [] := by
            rw [List.eq_nil_iff_forall_not_mem]
            intro q hq
            rcases h57 q hq with rfl | rfl
            · exact h5 hq
            · exact h7 hq
          rw [hKs0, hnil] at hneg
          simp only [List.map_nil, lspan_nil, Subgroup.mem_bot] at hneg
          exact hne1 hneg

end core

end FermatHodge
