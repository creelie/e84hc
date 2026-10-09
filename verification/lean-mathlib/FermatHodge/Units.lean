import FermatHodge.TwoD

/-!
# The subgroups `K_p` of `(ZMod e)ˣ`

For a prime `p` dividing `e`, `K_p` is the group of units congruent to `1` modulo `e / p`, the
kernel of reduction to `(ZMod (e / p))ˣ`. It has order `p` if `p² ∣ e` and `p - 1` otherwise, and
the `K_p` for distinct primes are independent.
-/

open Finset

noncomputable section

namespace FermatHodge

open Classical

set_option linter.unusedSectionVars false

/-- The units congruent to `1` modulo a divisor `d` of `e`. -/
def Nd {e d : ℕ} (h : d ∣ e) : Subgroup (ZMod e)ˣ := (ZMod.unitsMap h).ker

/-- `K_p`: the units congruent to `1` modulo `e / p`. -/
def Kq (e p : ℕ) : Subgroup (ZMod e)ˣ :=
  if h : p ∣ e then Nd (Nat.div_dvd_of_dvd h) else ⊥

lemma Kq_of_dvd {e p : ℕ} (h : p ∣ e) : Kq e p = Nd (Nat.div_dvd_of_dvd h) := by
  simp [Kq, h]

lemma mem_Nd {e d : ℕ} (h : d ∣ e) {u : (ZMod e)ˣ} :
    u ∈ Nd h ↔ ((u : ZMod e).cast : ZMod d) = 1 := by
  rw [Nd, MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, Units.val_one]

lemma Nd_mono {e d d' : ℕ} (h : d ∣ e) (h' : d' ∣ e) (hdd : d' ∣ d) : Nd h ≤ Nd h' := by
  intro u hu
  rw [Nd, MonoidHom.mem_ker] at hu ⊢
  have : ZMod.unitsMap h' u = ZMod.unitsMap hdd (ZMod.unitsMap h u) := by
    rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp]
  rw [this, hu, map_one]

/-- Congruent to `1` modulo two coprime factors means equal to `1`. -/
lemma eq_one_of_Nd {e d1 d2 : ℕ} [NeZero e] (h1 : d1 ∣ e) (h2 : d2 ∣ e)
    (hcop : Nat.Coprime d1 d2) (he : e = d1 * d2) {u : (ZMod e)ˣ} (hu1 : u ∈ Nd h1)
    (hu2 : u ∈ Nd h2) : u = 1 := by
  rw [mem_Nd, ZMod.cast_eq_val] at hu1 hu2
  have k1 : (u : ZMod e).val ≡ 1 [MOD d1] := by
    rw [← ZMod.natCast_eq_natCast_iff]; simpa using hu1
  have k2 : (u : ZMod e).val ≡ 1 [MOD d2] := by
    rw [← ZMod.natCast_eq_natCast_iff]; simpa using hu2
  have k : (u : ZMod e).val ≡ 1 [MOD e] := by
    have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨k1, k2⟩
    rwa [← he] at this
  apply Units.ext
  rw [Units.val_one, ← ZMod.natCast_zmod_val (u : ZMod e), ← Nat.cast_one,
    ZMod.natCast_eq_natCast_iff]
  exact k

/-- `-1` is not congruent to `1` modulo an odd prime. -/
lemma neg_one_not_mem_Nd {e p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ e) :
    (-1 : (ZMod e)ˣ) ∉ Nd h := by
  intro hm
  rw [mem_Nd] at hm
  have h3 : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  have : ((ZMod.castHom h (ZMod p)) (-1 : ZMod e)) = 1 := by
    rw [ZMod.castHom_apply]; simpa using hm
  rw [map_neg, map_one] at this
  exact ZMod.neg_one_ne_one this

section card

variable {e p : ℕ} [NeZero e]

lemma ne_zero_div (h : p ∣ e) : e / p ≠ 0 := by
  intro h0
  have := Nat.div_mul_cancel h
  rw [h0, zero_mul] at this
  exact NeZero.ne e this.symm

lemma card_Kq_mul (h : p ∣ e) : Nat.card (Kq e p) * (e / p).totient = e.totient := by
  have : NeZero (e / p) := ⟨ne_zero_div h⟩
  rw [Kq_of_dvd h, Nd]
  have h1 := Subgroup.card_mul_index (ZMod.unitsMap (Nat.div_dvd_of_dvd h)).ker
  have c1 : Nat.card (ZMod (e / p))ˣ = (e / p).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have c2 : Nat.card (ZMod e)ˣ = e.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective _),
    Subgroup.card_top, c1, c2] at h1
  exact h1

lemma card_Kq_of_dvd (hp : p.Prime) (h : p ∣ e) (h2 : p ∣ e / p) : Nat.card (Kq e p) = p := by
  have h1 := card_Kq_mul h
  have he : e.totient = p * (e / p).totient := by
    conv_lhs => rw [← Nat.mul_div_cancel' h]
    exact Nat.totient_mul_of_prime_of_dvd hp h2
  have hpos : 0 < (e / p).totient := Nat.totient_pos.2 (Nat.pos_of_ne_zero (ne_zero_div h))
  rw [he] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

lemma card_Kq_of_not_dvd (hp : p.Prime) (h : p ∣ e) (h2 : ¬p ∣ e / p) :
    Nat.card (Kq e p) = p - 1 := by
  have h1 := card_Kq_mul h
  have he : e.totient = (p - 1) * (e / p).totient := by
    conv_lhs => rw [← Nat.mul_div_cancel' h]
    exact Nat.totient_mul_of_prime_of_not_dvd hp h2
  have hpos : 0 < (e / p).totient := Nat.totient_pos.2 (Nat.pos_of_ne_zero (ne_zero_div h))
  rw [he] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

lemma card_Kq_cases (hp : p.Prime) (h : p ∣ e) :
    Nat.card (Kq e p) = p ∨ Nat.card (Kq e p) = p - 1 := by
  by_cases h2 : p ∣ e / p
  · exact Or.inl (card_Kq_of_dvd hp h h2)
  · exact Or.inr (card_Kq_of_not_dvd hp h h2)

end card

section indep

variable {e : ℕ} [NeZero e]

/-- `K_q` lies in the units congruent to `1` modulo the `p`-part of `e`, for `q ≠ p`. -/
lemma Kq_le_Nd_ordProj {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqe : q ∣ e) (hpq : p ≠ q) :
    Kq e q ≤ Nd (Nat.ordProj_dvd e p) := by
  rw [Kq_of_dvd hqe]
  apply Nd_mono
  apply Nat.dvd_div_of_mul_dvd
  have hcop : Nat.Coprime (ordProj[p] e) q :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hq).mpr hpq)
  rw [mul_comm]
  exact hcop.mul_dvd_of_dvd_of_dvd (Nat.ordProj_dvd e p) hqe

lemma lspan_le_Nd_ordProj {p : ℕ} (hp : p.Prime) :
    ∀ qs : List ℕ, (∀ q ∈ qs, q.Prime ∧ q ∣ e ∧ q ≠ p) →
      lspan (qs.map (Kq e)) ≤ Nd (Nat.ordProj_dvd e p)
  | [], _ => by simp
  | q :: qs, h => by
      simp only [List.map_cons, lspan_cons]
      have hq := h q (by simp)
      refine sup_le (Kq_le_Nd_ordProj hp hq.1 hq.2.1 (Ne.symm hq.2.2)) ?_
      exact lspan_le_Nd_ordProj hp qs (fun q' hq' => h q' (by simp [hq']))

lemma Kq_inf_Nd_ordProj {p : ℕ} (hp : p.Prime) (hpe : p ∣ e) :
    Kq e p ⊓ Nd (Nat.ordProj_dvd e p) = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_inf] at hu
  rw [Subgroup.mem_bot]
  have hne : e ≠ 0 := NeZero.ne e
  have hM : ordCompl[p] e ∣ e / p := by
    apply Nat.dvd_div_of_mul_dvd
    have h1 : p ∣ ordProj[p] e :=
      dvd_pow_self p (hp.factorization_pos_of_dvd hne hpe).ne'
    calc p * ordCompl[p] e ∣ ordProj[p] e * ordCompl[p] e := Nat.mul_dvd_mul_right h1 _
      _ = e := Nat.ordProj_mul_ordCompl_eq_self e p
  have hu1 : u ∈ Nd (Nat.ordCompl_dvd e p) := by
    have := hu.1
    rw [Kq_of_dvd hpe] at this
    exact Nd_mono _ _ hM this
  have hcop : Nat.Coprime (ordCompl[p] e) (ordProj[p] e) :=
    ((Nat.coprime_ordCompl hp hne).pow_left _).symm
  exact eq_one_of_Nd (Nat.ordCompl_dvd e p) (Nat.ordProj_dvd e p) hcop
    (by rw [mul_comm]; exact (Nat.ordProj_mul_ordCompl_eq_self e p).symm) hu1 hu.2

theorem indep_Kq : ∀ ps : List ℕ, ps.Nodup → (∀ p ∈ ps, p.Prime ∧ p ∣ e) →
    Indep (ps.map (Kq e))
  | [], _, _ => trivial
  | p :: ps, hnd, h => by
      simp only [List.map_cons]
      have hp := h p (by simp)
      refine ⟨?_, indep_Kq ps (List.nodup_cons.mp hnd).2 (fun q hq => h q (by simp [hq]))⟩
      rw [eq_bot_iff]
      calc Kq e p ⊓ lspan (ps.map (Kq e)) ≤ Kq e p ⊓ Nd (Nat.ordProj_dvd e p) := by
            refine inf_le_inf_left _ (lspan_le_Nd_ordProj hp.1 ps (fun q hq => ?_))
            refine ⟨(h q (by simp [hq])).1, (h q (by simp [hq])).2, ?_⟩
            rintro rfl; exact (List.nodup_cons.mp hnd).1 hq
        _ = ⊥ := Kq_inf_Nd_ordProj hp.1 hp.2

/-- `-1` does not lie in the span of the `K_q` with `q ≠ p`, for an odd prime `p ∣ e`. -/
lemma neg_one_not_mem_lspan {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpe : p ∣ e) (qs : List ℕ)
    (h : ∀ q ∈ qs, q.Prime ∧ q ∣ e ∧ q ≠ p) : (-1 : (ZMod e)ˣ) ∉ lspan (qs.map (Kq e)) := by
  intro hm
  have h1 := lspan_le_Nd_ordProj hp qs h hm
  have hne : e ≠ 0 := NeZero.ne e
  have hpP : p ∣ ordProj[p] e :=
    dvd_pow_self p (hp.factorization_pos_of_dvd hne hpe).ne'
  exact neg_one_not_mem_Nd hp hp2 hpe (Nd_mono _ hpe hpP h1)

end indep

end FermatHodge
