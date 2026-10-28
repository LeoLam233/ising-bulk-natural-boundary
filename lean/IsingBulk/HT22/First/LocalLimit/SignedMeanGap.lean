import IsingBulk.HT22.Arithmetic.FullFamily
import IsingBulk.HT22.Physical.Angular
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The finite signed equality-mean gap uses the actual absolute-level
endpoint branch, for both upper quadrants and both constraints. -/
namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex IsingBulk.First IsingBulk.PrimeFamily Arithmetic

def signedEqualityMean (negative : Bool) (N : ℕ) (l : ℤ) : ℝ :=
  (2*Real.pi*l+Physical.constraintAngle negative)/N

theorem endpoint_finite_signed_separation {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (M : ℕ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ negative : Bool, ∀ N : ℕ, 1≤N → N≤M →
      δ≤‖1-Physical.constraintSign negative*endpointBranch p a^N‖ := by
  have hpos (negative : Bool) (N : ℕ) (hN : 1≤N) :
      0<‖1-Physical.constraintSign negative*endpointBranch p a^N‖ := by
    apply norm_pos_iff.mpr
    obtain ⟨hp1,hpm⟩ := endpointBranch_pow_ne_signs hp hp5 ha N (by omega)
    cases negative <;> simp only [Physical.constraintSign,Bool.false_eq_true,↓reduceIte,one_mul,neg_mul] <;>
      intro h
    · exact hp1 (sub_eq_zero.mp h).symm
    · apply hpm
      linear_combination h
  induction M with
  | zero => exact ⟨1,zero_lt_one,by intro negative N hN hNM;omega⟩
  | succ M ih =>
    obtain ⟨δ,hδ,hbound⟩ := ih
    let D := min ‖1-endpointBranch p a^(M+1)‖ ‖1+endpointBranch p a^(M+1)‖
    have hD : 0<D := by
      have h0 := hpos false (M+1) (by omega)
      have h1 := hpos true (M+1) (by omega)
      simpa only [D,Physical.constraintSign,Bool.false_eq_true,↓reduceIte,one_mul,neg_mul,sub_neg_eq_add]
        using lt_min h0 h1
    refine ⟨min δ D,lt_min hδ hD,?_⟩
    intro negative N hN hNM
    by_cases hn : N≤M
    · exact (min_le_left _ _).trans (hbound negative N hN hn)
    · have he : N=M+1 := by omega
      subst N
      apply (min_le_right δ D).trans
      cases negative
      · simpa only [Physical.constraintSign,Bool.false_eq_true,↓reduceIte,one_mul] using min_le_left
          ‖1-endpointBranch p a^(M+1)‖ ‖1+endpointBranch p a^(M+1)‖
      · simpa only [Physical.constraintSign,Bool.false_eq_true,↓reduceIte,neg_mul,one_mul,sub_neg_eq_add] using min_le_right
          ‖1-endpointBranch p a^(M+1)‖ ‖1+endpointBranch p a^(M+1)‖

theorem signed_mean_phase_identity (negative : Bool) {N : ℕ} (hN : 0<N)
    (l : ℤ) (b : ℝ) :
    Physical.constraintSign negative*exp (-(b:ℂ)*I)^N =
      exp (-(N:ℂ)*((b+signedEqualityMean negative N l):ℂ)*I) := by
  have hNc : (N:ℂ)≠0 := by exact_mod_cast hN.ne'
  have he : -(N:ℂ)*((b+signedEqualityMean negative N l):ℂ)*I =
      (N:ℂ)*(-(b:ℂ)*I)+((-l:ℤ):ℂ)*(2*Real.pi*I)-
        (Physical.constraintAngle negative:ℂ)*I := by
    unfold signedEqualityMean
    push_cast
    field_simp
    ring
  rw [he,exp_sub,exp_add,exp_int_mul_two_pi_mul_I,mul_one,exp_nat_mul]
  cases negative
  · simp [Physical.constraintSign,Physical.constraintAngle]
  · simp [Physical.constraintSign,Physical.constraintAngle,exp_pi_mul_I,div_neg,div_one]

theorem signed_mean_phase_distance (negative : Bool) {N : ℕ} (hN : 0<N)
    (l : ℤ) (b : ℝ) :
    ‖1-Physical.constraintSign negative*exp (-(b:ℂ)*I)^N‖≤
      (N:ℝ)*|b+signedEqualityMean negative N l| := by
  calc
    _ = ‖exp (I*((-(N:ℝ)*(b+signedEqualityMean negative N l):ℝ):ℂ))-1‖ := by
      rw [signed_mean_phase_identity negative hN l b,norm_sub_rev]
      congr 2
      push_cast
      ring
    _ ≤ ‖-(N:ℝ)*(b+signedEqualityMean negative N l)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by rw [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg N)]

/-- One positive gap precedes epsilon and all integer means for every order
in the fixed finite block, with the absolute physical branch on both signs. -/
theorem finite_signed_mean_separation {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) {M : ℕ} (hM : 0<M) :
    ∃ g : ℝ, 0<g ∧ ∀ negative : Bool, ∀ N : ℕ, 1≤N → N≤M → ∀ l : ℤ,
      g≤|Real.arccos (|2*Real.cos (angle p a)|-1)+signedEqualityMean negative N l| := by
  obtain ⟨δ,hδ,hsep⟩ := endpoint_finite_signed_separation hp hp5 ha M
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  refine ⟨δ/M,div_pos hδ hMr,?_⟩
  intro negative N hN hNM l
  apply (div_le_iff₀ hMr).mpr
  have hn : (N:ℝ)≤M := by exact_mod_cast hNM
  have h := (hsep negative N hN hNM).trans
    (signed_mean_phase_distance negative (by omega) l (Real.arccos (|2*Real.cos (angle p a)|-1)))
  nlinarith [mul_le_mul_of_nonneg_right hn
    (abs_nonneg (Real.arccos (|2*Real.cos (angle p a)|-1)+signedEqualityMean negative N l))]

end
end IsingBulk.HT22.LocalLimit
