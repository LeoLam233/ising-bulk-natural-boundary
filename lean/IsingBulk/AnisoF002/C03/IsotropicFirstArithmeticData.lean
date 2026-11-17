import IsingBulk.AnisoF002.C03.IsotropicFirstOtherMeans

/-!
# Actual arithmetic data for the three original prime first particles

This record packages the exact constrained-mean statements consumed by
the finite physical coefficient assembly.  Each of its three constructors
is proved from the internal F002 cyclotomic arithmetic, with the actual
physical parity, determinant sign, phase and first particle number.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set

structure IsotropicFirstArithmeticData (m k0 : ℕ) (α phase : ℝ) (σ : ℂ) : Prop where
  offset_physical : m = 0 ∨ m = 1
  angle_pos : 0 < α
  angle_lt_half : α < Real.pi / 2
  phase_physical : phase = 0 ∨ phase = Real.pi
  phase_sign : Complex.exp ((phase : ℂ) * Complex.I) = σ
  sign_physical : σ = 1 ∨ σ = -1
  sign_norm_le_one : ‖σ‖ ≤ 1
  first_count_ge_seven : 7 ≤ m + 2 * k0 + 1
  first_resonance :
    σ * Complex.exp (-(((m + 2 * k0 + 1 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1
  first_lift : ∃ l0 : ℤ, ((m + 2 * k0 + 1 : ℕ) : ℝ) * (-α) = 2 * Real.pi * l0 + phase
  all_means_nonbranch : ∀ N : ℕ, 0 < N → ∀ μ : ℝ, ∀ l : ℤ,
    (N : ℝ) * μ = 2 * Real.pi * l + phase →
    2 * Real.cos α - Real.cos μ ≠ 1
  lower_nonresonance : ∀ k : ℕ, k < k0 → ∀ μ : ℝ, ∀ l : ℤ,
    ((m + 2 * k + 1 : ℕ) : ℝ) * μ = 2 * Real.pi * l + phase →
    1 - σ * upperBoundaryRoot (2 * Real.cos α - Real.cos μ) ^ (m + 2 * k + 1) ≠ 0
  first_only_centers : ∀ μ ∈ Icc (-Real.pi) Real.pi, ∀ l : ℤ,
    ((m + 2 * k0 + 1 : ℕ) : ℝ) * μ = 2 * Real.pi * l + phase →
    1 - σ * upperBoundaryRoot (2 * Real.cos α - Real.cos μ) ^ (m + 2 * k0 + 1) = 0 →
    μ = α ∨ μ = -α

theorem isotropic_prime_odd_count {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    0 + 2 * ((p - 1) / 2) + 1 = p := by
  obtain ⟨d, hd⟩ := hp.odd_of_ne_two (by omega)
  omega

theorem isotropic_prime_even_count {p : ℕ} (hp : 0 < p) :
    1 + 2 * (p - 1) + 1 = 2 * p := by omega

theorem isotropic_positive_prime_first_arithmetic {p a : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (ha : a.Coprime p)
    (hα : 0 < isotropicPrimeAngle p a) (hhalf : isotropicPrimeAngle p a < Real.pi / 2) :
    IsotropicFirstArithmeticData 0 ((p - 1) / 2) (isotropicPrimeAngle p a) 0 1 := by
  have hcount := isotropic_prime_odd_count hp hp7
  have hcos : 0 < Real.cos (isotropicPrimeAngle p a) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hhalf⟩
  have hS : 0 < 2 * Real.cos (isotropicPrimeAngle p a) := by positivity
  have hαI : isotropicPrimeAngle p a ∈ Icc 0 Real.pi :=
    ⟨hα.le, by linarith [Real.pi_pos]⟩
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine {
    offset_physical := Or.inl rfl
    angle_pos := hα
    angle_lt_half := hhalf
    phase_physical := Or.inl rfl
    phase_sign := by simp
    sign_physical := Or.inl rfl
    sign_norm_le_one := by norm_num
    first_count_ge_seven := by omega
    first_resonance := by simpa only [hcount] using isotropic_prime_odd_first_resonance p a hp.pos
    first_lift := ?_
    all_means_nonbranch := ?_
    lower_nonresonance := ?_
    first_only_centers := ?_ }
  · refine ⟨-(a : ℤ), ?_⟩
    rw [hcount, add_zero]
    have hm := isotropic_prime_odd_first_mean p a 0
    simp only [constrainedRightMean, zero_add, add_zero, zero_sub] at hm
    have he := (div_eq_iff hp0).mp hm
    simpa only [mul_comm] using he.symm
  · intro N hN μ l hm
    exact isotropic_prime_positive_all_means_nonbranch hp (by omega) ha hN hS.le
      (Or.inl rfl) l hm
  · intro k hk μ l hm
    have hN : 0 < 0 + 2 * k + 1 := by omega
    have hlt : 0 + 2 * k + 1 < p := by omega
    have hnd := Nat.not_dvd_of_pos_of_lt hN hlt
    simpa only [one_mul] using isotropic_positive_lower_mean_denominator
      hp (by omega) ha hN hnd hS μ l (by simpa only [add_zero] using hm)
  · intro μ hμ l hm hz
    rw [hcount] at hm hz
    by_contra hn
    push Not at hn
    exact isotropic_prime_first_odd_other_mean hp hp7 ha hαI hS hμ l
      (by simpa only [add_zero] using hm) hn.1 hn.2 (by simpa only [one_mul] using hz)

theorem isotropic_even_prime_first_arithmetic {p a : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (ha : a.Coprime p)
    (hα : 0 < isotropicPrimeAngle p a) (hhalf : isotropicPrimeAngle p a < Real.pi / 2) :
    IsotropicFirstArithmeticData 1 (p - 1) (isotropicPrimeAngle p a) 0 1 := by
  have hcount := isotropic_prime_even_count hp.pos
  have hcos : 0 < Real.cos (isotropicPrimeAngle p a) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hhalf⟩
  have hS : 0 < 2 * Real.cos (isotropicPrimeAngle p a) := by positivity
  have hαI : isotropicPrimeAngle p a ∈ Icc 0 Real.pi :=
    ⟨hα.le, by linarith [Real.pi_pos]⟩
  have hp0 : ((2 * p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 2 * p ≠ 0 by omega)
  refine {
    offset_physical := Or.inr rfl
    angle_pos := hα
    angle_lt_half := hhalf
    phase_physical := Or.inl rfl
    phase_sign := by simp
    sign_physical := Or.inl rfl
    sign_norm_le_one := by norm_num
    first_count_ge_seven := by omega
    first_resonance := by simpa only [hcount] using isotropic_prime_even_first_resonance p a hp.pos
    first_lift := ?_
    all_means_nonbranch := ?_
    lower_nonresonance := ?_
    first_only_centers := ?_ }
  · refine ⟨-(2 * a : ℤ), ?_⟩
    rw [hcount, add_zero]
    have hm := isotropic_prime_even_first_mean p a hp.pos 0
    simp only [constrainedRightMean, zero_add, add_zero, zero_sub] at hm
    have he := (div_eq_iff hp0).mp hm
    simpa only [mul_comm] using he.symm
  · intro N hN μ l hm
    exact isotropic_prime_positive_all_means_nonbranch hp (by omega) ha hN hS.le
      (Or.inl rfl) l hm
  · intro k hk μ l hm
    have hN : 0 < 1 + 2 * k + 1 := by omega
    have hlt : 1 + 2 * k + 1 < 2 * p := by omega
    have heven : Even (1 + 2 * k + 1) := ⟨k + 1, by omega⟩
    have hnd := isotropic_lower_even_not_dvd hp (by omega) hN hlt heven
    simpa only [one_mul] using isotropic_positive_lower_mean_denominator
      hp (by omega) ha hN hnd hS μ l (by simpa only [add_zero] using hm)
  · intro μ hμ l hm hz
    rw [hcount] at hm hz
    by_contra hn
    push Not at hn
    exact isotropic_prime_first_even_other_mean hp hp7 ha hαI hS hμ l
      (by simpa only [add_zero] using hm) hn.1 hn.2 (by simpa only [one_mul] using hz)

theorem isotropic_negative_prime_first_arithmetic {p a : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (ha : a.Coprime p)
    (hα : 0 < Real.pi - isotropicPrimeAngle p a)
    (hhalf : Real.pi - isotropicPrimeAngle p a < Real.pi / 2) :
    IsotropicFirstArithmeticData 0 ((p - 1) / 2)
      (Real.pi - isotropicPrimeAngle p a) Real.pi (-1) := by
  have hcount := isotropic_prime_odd_count hp hp7
  have hcos : 0 < Real.cos (Real.pi - isotropicPrimeAngle p a) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hhalf⟩
  have hS : 0 < 2 * Real.cos (Real.pi - isotropicPrimeAngle p a) := by positivity
  have hSneg : 2 * Real.cos (isotropicPrimeAngle p a) ≤ 0 := by
    rw [Real.cos_pi_sub] at hcos
    linarith
  have hαI : Real.pi - isotropicPrimeAngle p a ∈ Icc 0 Real.pi :=
    ⟨hα.le, by linarith [Real.pi_pos]⟩
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine {
    offset_physical := Or.inl rfl
    angle_pos := hα
    angle_lt_half := hhalf
    phase_physical := Or.inr rfl
    phase_sign := Complex.exp_pi_mul_I
    sign_physical := Or.inr rfl
    sign_norm_le_one := by norm_num
    first_count_ge_seven := by omega
    first_resonance := by simpa only [hcount] using
      isotropic_prime_negative_first_resonance p a hp.pos hodd
    first_lift := ?_
    all_means_nonbranch := ?_
    lower_nonresonance := ?_
    first_only_centers := ?_ }
  · obtain ⟨d, hd⟩ := hodd
    refine ⟨(a : ℤ) - d - 1, ?_⟩
    rw [hcount]
    have heq : p = 2 * d + 1 := by omega
    have hm := isotropic_prime_negative_first_mean d a 0
    rw [← heq] at hm
    simp only [constrainedRightMean, zero_add, zero_sub] at hm
    have he := (div_eq_iff hp0).mp hm
    simpa only [mul_comm] using he.symm
  · intro N hN μ l hm
    exact isotropic_prime_negative_all_means_nonbranch hp (by omega) ha hN hSneg
      (Or.inr rfl) l hm
  · intro k hk μ l hm
    have hN : 0 < 0 + 2 * k + 1 := by omega
    have hlt : 0 + 2 * k + 1 < p := by omega
    have hnd := Nat.not_dvd_of_pos_of_lt hN hlt
    have hNodd : Odd (0 + 2 * k + 1) := ⟨k, by omega⟩
    exact isotropic_negative_lower_mean_denominator hp (by omega) ha hN hNodd hnd hS μ l hm
  · intro μ hμ l hm hz
    rw [hcount] at hm hz
    by_contra hn
    push Not at hn
    exact isotropic_prime_first_negative_other_mean hp hp7 ha hαI hS hμ l hm hn.1 hn.2 hz

end
end IsingBulk.AnisoF002.Isotropic
