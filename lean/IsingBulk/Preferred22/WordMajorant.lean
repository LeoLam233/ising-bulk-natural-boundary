import IsingBulk.Preferred22.RegularMarkedKernel
import IsingBulk.Preferred22.MarkedTransportRecursion
import IsingBulk.Preferred22.AbsoluteTail

/-! Exact conversion of literal normalized marked coefficients into the
source q20 determinant majorant. The scalar coefficient estimate remains
explicit here; factorial decay and the loss/mark budget are proved algebra. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise

/-- Derivatives of determinant order larger than its degree vanish; this
follows from actual repeated-row cancellation and finite injectivity. -/
theorem preferredMarkedMinor_zero_of_length_gt {N : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : List (Fin N × Fin N)) (hN : N<marks.length) :
    preferredMarkedMinor K marks=0 := by
  classical
  by_contra hn
  have hinj : Function.Injective (fun i : Fin marks.length => (marks.get i).1) := by
    intro i j he
    by_contra hij
    exact hn (markedDeterminant_eq_zero_of_row_collision K (fun r => marks.get r) i j hij he)
  have hh := Fintype.card_le_of_injective (fun i : Fin marks.length => (marks.get i).1) hinj
  simp only [Fintype.card_fin] at hh
  omega

/-- The literal Haar/factorial normalization controls the coefficient times
N!, because the remaining angular volume normalization is at least one. -/
theorem preferred_normalized_coefficient_factorial {N : ℕ} (A : ℂ) {M : ℝ}
    (hA : ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*A‖≤M) :
    ‖A‖*(N.factorial:ℝ)≤M := by
  have hH : 1≤(2*Real.pi)^(N-1) := one_le_pow₀ (by linarith [Real.two_le_pi])
  have hn : ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*A‖=
      ‖A‖*(N.factorial:ℝ)*(2*Real.pi)^(N-1) := by
    simp only [norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,
      Complex.norm_ofNat,abs_of_pos Real.pi_pos]
    ring
  rw [hn] at hA
  exact (le_mul_of_one_le_right (by positivity : 0≤‖A‖*(N.factorial:ℝ)) hH).trans hA

/-- A marked term retains the complete unmarked kernel power and the exact
scalar loss. No factorial is absorbed into an unspecified constant. -/
theorem preferred_marked_term_bound {N : ℕ} (hN : 0<N)
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : List (Fin N × Fin N))
    (A : ℂ) {a M : ℝ} (ha : 0<a) (hM : 0≤M)
    (hA : ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*A‖≤M)
    (hK : ∀ i j,‖K i j‖≤a) :
    ‖A*preferredMarkedMinor K marks‖≤M*(Real.exp 1/Real.sqrt N)^N*a^(N-marks.length) := by
  have hf : (0:ℝ)<N.factorial := by positivity
  have hAs := preferred_normalized_coefficient_factorial A hA
  have hm := preferredMarkedMinor_factorial_bound hN K marks a ha hK
  calc
    _ = (‖A‖*(N.factorial:ℝ))*(‖preferredMarkedMinor K marks‖/(N.factorial:ℝ)) := by
      rw [norm_mul]
      field_simp
    _ ≤ M*((Real.exp 1/Real.sqrt N)^N*a^(N-marks.length)) :=
      mul_le_mul hAs hm (by positivity) hM
    _ = _ := by ring

/-- Exact power cancellation from h+ell=2j, including all small N and every
positive diameter. The hypothesis ell<=N is supplied by minor nonvanishing. -/
theorem preferred_marked_scale_identity {N ell h j : ℕ} (hell : ell≤N) (hbudget : h+ell=2*j)
    {K r q : ℝ} (hr : 0<r) (hq : 0<q) :
    (K*r/q)^(N-ell)/r^h=K^(N-ell)*q^ell*(r^N/(r^(2*j)*q^N)) := by
  calc
    _ = K^(N-ell)*q^ell*(r^((N-ell)+ell)/(r^(h+ell)*q^((N-ell)+ell))) := by
      simp only [mul_pow,div_pow,pow_add]
      field_simp [hr.ne',hq.ne']
    _ = _ := by rw [Nat.sub_add_cancel hell,hbudget]

theorem preferred_marked_scale_bound {N ell h j : ℕ} (hell : ell≤N)
    (hellj : ell≤j) (hbudget : h+ell=2*j)
    {K r q D S : ℝ} (hK : 1≤K) (hr : 0<r) (hrD : r≤D) (hq : 0<q) (hqS : q≤S) (hS : 1≤S) :
    (K*r/q)^(N-ell)/D^h≤K^N*S^j*(r^N/(r^(2*j)*q^N)) := by
  have hD : 0<D := hr.trans_le hrD
  have hnum : 0≤(K*r/q)^(N-ell) := by positivity
  have hden : r^h≤D^h := pow_le_pow_left₀ hr.le hrD h
  have hkp : K^(N-ell)≤K^N := pow_le_pow_right₀ hK (Nat.sub_le _ _)
  have hqp : q^ell≤S^j := (pow_le_pow_left₀ hq.le hqS ell).trans (pow_le_pow_right₀ hS hellj)
  calc
    _ ≤ (K*r/q)^(N-ell)/r^h := div_le_div_of_nonneg_left hnum (pow_pos hr h) hden
    _ = _ := preferred_marked_scale_identity hell hbudget hr hq
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul hkp hqp (by positivity) (by positivity)) (by positivity)

/-- The full actual word sum has the q20 scale, once the literal normalized
scalar word bound is established. All marked minors and word counts are
handled here; the estimate is not an assumed differentiated determinant. -/
theorem preferredWordSum_q20_bound {N : ℕ} (hN : 0<N)
    (τ : ℝ) (η p m rcut : ℝ → ℝ) (j J : ℕ) (s : ℂ) (θ : Fin N → ℝ)
    {C K r q D S : ℝ} (hC : 0<C) (hK : 1≤K) (hr : 0<r) (hrD : r≤D)
    (hq : 0<q) (hqS : q≤S) (hS : 1≤S)
    (hentry : ∀ i a,‖preferredSourceRegularKernel τ p m s θ i a‖≤K*r/q)
    (hcoeff : ∀ w : PreferredMarkedWord N j,
      ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*preferredWordCoefficient τ η p m rcut j w s θ‖≤
        C^N*(N:ℝ)^J/D^(preferredWordLoss j w)) :
    ‖preferredWordSum τ η p m rcut j s θ‖≤
      (2*S)^j*shellOrderEnvelope (C*K*Real.exp 1) (J+2*j) N*(r^N/(r^(2*j)*q^N)) := by
  have hD : 0<D := hr.trans_le hrD
  let Q := r^N/(r^(2*j)*q^N)
  let P := C^N*(N:ℝ)^J*(Real.exp 1/Real.sqrt N)^N*K^N*S^j*Q
  have hP : 0≤P := by dsimp [P,Q]; positivity
  have hterm (w : PreferredMarkedWord N j) :
      ‖preferredWordCoefficient τ η p m rcut j w s θ*
        preferredMarkedMinor (preferredSourceRegularKernel τ p m s θ) (preferredWordMarks j w)‖≤P := by
    by_cases hlen : (preferredWordMarks j w).length≤N
    · have hb := preferred_marked_term_bound hN (preferredSourceRegularKernel τ p m s θ)
        (preferredWordMarks j w) (preferredWordCoefficient τ η p m rcut j w s θ)
        (by positivity : 0<K*r/q) (by positivity : 0≤C^N*(N:ℝ)^J/D^(preferredWordLoss j w))
        (hcoeff w) hentry
      have hs := preferred_marked_scale_bound hlen (preferredWordMarks_length j w)
        (preferredWordLoss_budget j w) hK hr hrD hq hqS hS
      calc
        _ ≤ _ := hb
        _ = (C^N*(N:ℝ)^J*(Real.exp 1/Real.sqrt N)^N)*
            ((K*r/q)^(N-(preferredWordMarks j w).length)/D^(preferredWordLoss j w)) := by ring
        _ ≤ P := by
          have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0≤C^N*(N:ℝ)^J*(Real.exp 1/Real.sqrt N)^N)
          simpa only [P,Q,mul_assoc] using hh
    · rw [preferredMarkedMinor_zero_of_length_gt _ _ (Nat.lt_of_not_ge hlen),mul_zero,norm_zero]
      exact hP
  have hcard : (Fintype.card (PreferredMarkedWord N j):ℝ)≤2^j*(N:ℝ)^(2*j) := by
    rw [preferredWord_card]
    have hb : N^2+1≤2*N^2 := by nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hN)]
    have hh := Nat.pow_le_pow_left hb j
    rw [mul_pow,←pow_mul] at hh
    exact_mod_cast hh
  calc
    _ ≤ ∑ w : PreferredMarkedWord N j,
        ‖preferredWordCoefficient τ η p m rcut j w s θ*
          preferredMarkedMinor (preferredSourceRegularKernel τ p m s θ) (preferredWordMarks j w)‖ := norm_sum_le _ _
    _ ≤ ∑ _w : PreferredMarkedWord N j,P := Finset.sum_le_sum (fun w _ => hterm w)
    _ = (Fintype.card (PreferredMarkedWord N j):ℝ)*P := by simp
    _ ≤ (2^j*(N:ℝ)^(2*j))*P := mul_le_mul_of_nonneg_right hcard hP
    _ = _ := by
      dsimp [P,Q,shellOrderEnvelope]
      simp only [mul_pow,div_pow,pow_add]
      ring

end
end IsingBulk.Preferred22
