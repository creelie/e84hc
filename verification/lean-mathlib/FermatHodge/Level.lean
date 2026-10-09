import FermatHodge.Fourier

/-!
# From level `m` to level `e`

For `e ∣ m`, `kap` embeds `ZMod e` in `ZMod m` as the multiples of `m / e`; its image is the set of
elements of order dividing `e`, and the units of `ZMod e` go to the elements of order exactly
`e`.  The Hodge condition at level `m` turns, through a character sum, into orthogonality of the
counting function at level `e` to every primitive character.
-/

open Finset

noncomputable section

namespace FermatHodge

open Classical

set_option linter.unusedSectionVars false

section kap

variable {m e : ℕ} [NeZero m]

/-- The embedding `ZMod e → ZMod m`, `y ↦ (m / e) * y`. -/
def kap (hem : e ∣ m) : ZMod e →+ ZMod m :=
  ZMod.lift e ⟨(m / e) • Int.castAddHom (ZMod m), by
    show (m / e) • ((e : ℤ) : ZMod m) = 0
    rw [nsmul_eq_mul, Int.cast_natCast, ← Nat.cast_mul, Nat.div_mul_cancel hem,
      ZMod.natCast_self]⟩

lemma kap_natCast (hem : e ∣ m) (n : ℕ) : kap hem (n : ZMod e) = ((m / e * n : ℕ) : ZMod m) := by
  have : (n : ZMod e) = ((n : ℤ) : ZMod e) := by simp
  rw [this, kap, ZMod.lift_coe]
  simp

lemma div_pos_of_dvd (hem : e ∣ m) : 0 < m / e := by
  have hm : m ≠ 0 := NeZero.ne m
  have he : e ≠ 0 := by rintro rfl; exact hm (Nat.eq_zero_of_zero_dvd hem)
  exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hem) (Nat.pos_of_ne_zero he)

lemma kap_val [NeZero e] (hem : e ∣ m) (y : ZMod e) : (kap hem y).val = m / e * y.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val y]
  rw [kap_natCast, ZMod.val_natCast_of_lt]
  calc m / e * y.val < m / e * e :=
        Nat.mul_lt_mul_of_pos_left (ZMod.val_lt y) (div_pos_of_dvd hem)
    _ = m := Nat.div_mul_cancel hem

lemma kap_inj [NeZero e] (hem : e ∣ m) : Function.Injective (kap hem) := by
  intro y z h
  have := congrArg ZMod.val h
  rw [kap_val, kap_val] at this
  exact ZMod.val_injective e (Nat.eq_of_mul_eq_mul_left (div_pos_of_dvd hem) this)

lemma mul_kap (hem : e ∣ m) (t : ZMod m) (y : ZMod e) :
    t * kap hem y = kap hem ((t.cast : ZMod e) * y) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val t]
  rw [← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul, ZMod.cast_eq_val]

/-- An element of order `e` is the image of a unit. -/
lemma exists_kap_unit [NeZero e] (hem : e ∣ m) {a : ZMod m} (ha : addOrderOf a = e) :
    ∃ z : (ZMod e)ˣ, kap hem (z : ZMod e) = a := by
  have hm : m ≠ 0 := NeZero.ne m
  set n := a.val with hn
  have han : (n : ZMod m) = a := ZMod.natCast_zmod_val a
  rw [← han, ZMod.addOrderOf_coe n hm] at ha
  set g := m.gcd n with hg
  have hgm : g ∣ m := Nat.gcd_dvd_left m n
  have hgn : g ∣ n := Nat.gcd_dvd_right m n
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hm)
  have hme : m = e * g := by rw [← ha, Nat.div_mul_cancel hgm]
  have hdiv : m / e = g := by
    rw [hme, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne e))]
  obtain ⟨b, hb⟩ := hgn
  have hcop : Nat.Coprime b e := by
    have h1 : Nat.gcd (g * e) (g * b) = g * Nat.gcd e b := Nat.gcd_mul_left g e b
    rw [← hb, mul_comm g e, ← hme, ← hg] at h1
    have : Nat.gcd e b = 1 := by
      have h2 : g * 1 = g * Nat.gcd e b := by rw [mul_one]; exact h1
      exact (Nat.eq_of_mul_eq_mul_left hg0 h2).symm
    rw [Nat.Coprime, Nat.gcd_comm]; exact this
  refine ⟨ZMod.unitOfCoprime b hcop, ?_⟩
  rw [ZMod.coe_unitOfCoprime, kap_natCast, hdiv, ← hb]
  exact han

/-- Every element of `ZMod m` has order dividing `m`. -/
lemma addOrderOf_dvd_m (a : ZMod m) : addOrderOf a ∣ m := by
  apply addOrderOf_dvd_of_nsmul_eq_zero
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- A unit congruent to `1` modulo the order of `a` fixes `a`. -/
lemma mul_eq_of_ker {d : ℕ} (hdm : d ∣ m) {a : ZMod m} (had : addOrderOf a = d)
    {n : (ZMod m)ˣ} (hn : n ∈ (ZMod.unitsMap hdm).ker) : (n : ZMod m) * a = a := by
  rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, Units.val_one, ZMod.cast_eq_val] at hn
  have h1 : ((((n : ZMod m).val : ℤ) - 1 : ℤ) : ZMod d) = 0 := by
    push_cast; rw [hn, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  obtain ⟨q, hq⟩ := h1
  have h2 : (n : ZMod m) - 1 = (d : ZMod m) * q := by
    have : ((((n : ZMod m).val : ℤ) - 1 : ℤ) : ZMod m) = (((d : ℤ) * q : ℤ) : ZMod m) := by
      rw [hq]
    push_cast at this
    rwa [ZMod.natCast_zmod_val] at this
  have h3 : (d : ZMod m) * a = 0 := by
    rw [← nsmul_eq_mul, ← had]; exact addOrderOf_nsmul_eq_zero a
  have : ((n : ZMod m) - 1) * a = 0 := by
    rw [h2, mul_comm (d : ZMod m), mul_assoc, h3, mul_zero]
  rw [sub_mul, one_mul, sub_eq_zero] at this
  exact this

end kap

section fiber

variable {H K : Type*} [CommGroup H] [Fintype H] [CommGroup K] [Fintype K]

/-- Summing through a surjective homomorphism multiplies by the size of the kernel. -/
lemma sum_comp_hom (π : H →* K) (hπ : Function.Surjective π) {M : Type*} [AddCommMonoid M]
    (φ : K → M) : ∑ h, φ (π h) = (Nat.card π.ker) • ∑ k, φ k := by
  have hc : (#{h | π h = 1} : ℕ) = Nat.card π.ker := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp [MonoidHom.mem_ker]
  rw [← hc, ← Finset.sum_fiberwise' univ π φ, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_const]
  congr 1
  exact MonoidHom.card_fiber_eq_of_mem_range π (hπ k) ⟨1, map_one π⟩

end fiber

section character

variable {m e : ℕ} [NeZero m] [NeZero e]

/-- A primitive character of level `e` is not trivial on the units congruent to `1` modulo a
divisor `d` of `m` that `e` does not divide. -/
lemma exists_ker_ne_one (hem : e ∣ m) {d : ℕ} (hdm : d ∣ m) (χ : DirichletCharacter ℂ e)
    (hχ : χ.IsPrimitive) (hed : ¬e ∣ d) :
    ∃ n : (ZMod m)ˣ, n ∈ (ZMod.unitsMap hdm).ker ∧ χ ((n : ZMod m).cast) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hd0 : NeZero d := ⟨fun h => NeZero.ne m (Nat.eq_zero_of_zero_dvd (h ▸ hdm))⟩
  set χ' := DirichletCharacter.changeLevel hem χ with hχ'
  have hker : (ZMod.unitsMap hdm).ker ≤ χ'.toUnitHom.ker := by
    intro n hn
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, hχ',
      DirichletCharacter.changeLevel_eq_cast_of_dvd]
    exact hcon n hn
  obtain ⟨_, ψ, hψ⟩ := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hdm).mpr hker
  set L := Nat.lcm e d
  have hLm : L ∣ m := Nat.lcm_dvd hem hdm
  have heL : e ∣ L := Nat.dvd_lcm_left e d
  have hdL : d ∣ L := Nat.dvd_lcm_right e d
  have hL0 : NeZero L := ⟨fun h => NeZero.ne m (Nat.eq_zero_of_zero_dvd (h ▸ hLm))⟩
  have h1 : DirichletCharacter.changeLevel hLm (DirichletCharacter.changeLevel heL χ) =
      DirichletCharacter.changeLevel hLm (DirichletCharacter.changeLevel hdL ψ) := by
    rw [← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans]
    exact hψ
  have h2 := DirichletCharacter.changeLevel_injective hLm h1
  have hLed : L ∣ e * d := Nat.lcm_dvd (Nat.dvd_mul_right e d) (Nat.dvd_mul_left d e)
  have h3 : DirichletCharacter.changeLevel (e.dvd_mul_right d) χ =
      DirichletCharacter.changeLevel (d.dvd_mul_left e) ψ := by
    have := congrArg (DirichletCharacter.changeLevel hLed) h2
    rwa [← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans] at this
  have h4 := DirichletCharacter.factorsThrough_gcd χ ψ h3
  have h5 := DirichletCharacter.conductor_dvd_of_mem_conductorSet χ h4
  rw [hχ] at h5
  exact hed (h5.trans (Nat.gcd_dvd_right e d))

/-- The character sum attached to an element of `ZMod m`. -/
def Gsum (hem : e ∣ m) (χ : DirichletCharacter ℂ e) (a : ZMod m) : ℂ :=
  ∑ t : (ZMod m)ˣ, χ ((t : ZMod m).cast) * (((t : ZMod m) * a).val : ℂ)

lemma Gsum_eq_zero (hem : e ∣ m) (χ : DirichletCharacter ℂ e) (hχ : χ.IsPrimitive)
    {a : ZMod m} (hed : ¬e ∣ addOrderOf a) : Gsum hem χ a = 0 := by
  obtain ⟨n, hn, hχn⟩ := exists_ker_ne_one hem (addOrderOf_dvd_m a) χ hχ hed
  have hna := mul_eq_of_ker (addOrderOf_dvd_m a) rfl hn
  have h : Gsum hem χ a = χ ((n : ZMod m).cast) * Gsum hem χ a := by
    unfold Gsum
    rw [Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft n) _ _ (fun t => ?_)).symm
    simp only [Equiv.coe_mulLeft, Units.val_mul]
    rw [ZMod.cast_mul hem, mul_assoc (n : ZMod m) (t : ZMod m) a,
      mul_left_comm (n : ZMod m) (t : ZMod m) a, hna, map_mul, mul_assoc]
  have h2 : (1 - χ ((n : ZMod m).cast)) * Gsum hem χ a = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3).symm hχn
  · exact h3

/-- The Bernoulli-type sum `∑ χ(s) s`. -/
def Bsum (χ : DirichletCharacter ℂ e) : ℂ := ∑ s : (ZMod e)ˣ, χ s * ((s : ZMod e).val : ℂ)

lemma Gsum_kap (hem : e ∣ m) (χ : DirichletCharacter ℂ e) (z : (ZMod e)ˣ) :
    Gsum hem χ (kap hem (z : ZMod e)) =
      (Nat.card (ZMod.unitsMap hem).ker : ℂ) * ((m / e : ℕ) : ℂ) * χ ((z : ZMod e)⁻¹) *
        Bsum χ := by
  have h1 : ∀ t : (ZMod m)ˣ, χ ((t : ZMod m).cast) * (((t : ZMod m) * kap hem (z : ZMod e)).val : ℂ)
      = (fun s : (ZMod e)ˣ => χ s * (((m / e : ℕ) : ℂ) * (((s : ZMod e) * z).val : ℂ)))
        (ZMod.unitsMap hem t) := by
    intro t
    simp only [ZMod.unitsMap_val]
    rw [mul_kap, kap_val]
    push_cast; ring
  unfold Gsum
  rw [Fintype.sum_congr _ _ h1]
  refine (sum_comp_hom (ZMod.unitsMap hem) (ZMod.unitsMap_surjective hem)
    (fun s : (ZMod e)ˣ => χ s * (((m / e : ℕ) : ℂ) * (((s : ZMod e) * z).val : ℂ)))).trans ?_
  rw [nsmul_eq_mul]
  have h2 : ∑ s : (ZMod e)ˣ, χ s * (((m / e : ℕ) : ℂ) * (((s : ZMod e) * z).val : ℂ)) =
      ((m / e : ℕ) : ℂ) * χ ((z : ZMod e)⁻¹) * Bsum χ := by
    unfold Bsum
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight z) _ _ (fun s => ?_)
    simp only [Equiv.coe_mulRight, Units.val_mul]
    have : (z : ZMod e)⁻¹ = ((z⁻¹ : (ZMod e)ˣ) : ZMod e) := ZMod.inv_coe_unit z
    rw [this, map_mul]
    have hz : χ ((z⁻¹ : (ZMod e)ˣ) : ZMod e) * χ (z : ZMod e) = 1 := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    linear_combination (-(((m / e : ℕ) : ℂ) * χ (s : ZMod e) *
      (((s : ZMod e) * (z : ZMod e)).val : ℂ))) * hz
  rw [h2]; ring

end character

end FermatHodge
