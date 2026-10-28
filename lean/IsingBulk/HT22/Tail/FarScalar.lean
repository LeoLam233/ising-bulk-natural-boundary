import IsingBulk.HT22.Tail.CoefficientBounds
import IsingBulk.HT22.Tail.BorderedNormalization
import IsingBulk.HT22.Algebra.BorderJetAlgebra

/-! # Actual odd-bordered scalar: fixed-order far estimate
The constant ghost row and column are never marked. Marks exceeding the
ordinary polynomial degree vanish. This supplies the factorial-decaying
bound for the new fixed-v scalar recurrence, not the old LT scalar. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem ordinaryMarkedMinor_uniform {N : ℕ} (hN : 0<N)
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : List (Fin N × Fin N))
    {A : ℝ} (hA : 1≤A) (hK : ∀ i j, ‖K i j‖≤A) :
    ‖ordinaryMarkedMinor K marks‖≤(Real.sqrt (N+1:ℕ))^(N+1)*A^N := by
  by_cases hm : marks.length≤N-1
  · have h := Algebra.borderedMarkedDeterminant_hadamard hm hN K marks.get
      A (lt_of_lt_of_le (by norm_num) hA) hK
    simp only [Nat.cast_add,Nat.cast_one] at ⊢
    apply h.trans
    have hp := pow_le_pow_right₀ hA (show N-1-marks.length≤N by omega)
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  · have hm' : N≤marks.length := by omega
    rw [ordinaryMarkedMinor,Algebra.borderedMarkedDeterminant_eq_zero_of_order hm',norm_zero]
    positivity

/-- Uniform word sum estimate before factorial cancellation. The assumption
is only the already-computed coefficient bound; the actual minor estimate
and count are proved here for every mark order, including excessive marks. -/
theorem wordSum_normalized_bound {N : ℕ} (hN : 0<N)
    (τ : ℝ) (η p m r : ℝ → ℝ) (j : ℕ) (s : ℂ) (θ : Fin N → ℝ)
    (Z : ℂ) {A C : ℝ} (hA : 1≤A) (hC : 0≤C) (J : ℕ)
    (hK : ∀ i l, ‖sourceOrdinaryKernel τ p m s θ i l‖≤A)
    (hc : ∀ w : MarkedWord N j, ‖Z*wordCoefficient τ η p m r j w s θ‖≤C^N*(N:ℝ)^J) :
    ‖Z*wordSum τ η p m r j s θ‖≤
      (2:ℝ)^j*(N:ℝ)^(J+2*j)*(C*A)^N*(Real.sqrt (N+1:ℕ))^(N+1) := by
  classical
  have hm (w : MarkedWord N j) := ordinaryMarkedMinor_uniform hN
    (sourceOrdinaryKernel τ p m s θ) (wordMarks j w) hA hK
  have hb (w : MarkedWord N j) :
      ‖Z*(wordCoefficient τ η p m r j w s θ*
        ordinaryMarkedMinor (sourceOrdinaryKernel τ p m s θ) (wordMarks j w))‖≤
      (C^N*(N:ℝ)^J)*((Real.sqrt (N+1:ℕ))^(N+1)*A^N) := by
    rw [←mul_assoc,norm_mul]
    exact mul_le_mul (hc w) (hm w) (norm_nonneg _) (by positivity)
  have hcount : (Fintype.card (MarkedWord N j):ℝ)≤(2:ℝ)^j*(N:ℝ)^(2*j) := by
    rw [preferredWord_card]
    have h : N^2+1≤2*N^2 := by nlinarith
    have hh := Nat.pow_le_pow_left h j
    rw [mul_pow,←pow_mul] at hh
    exact_mod_cast hh
  calc
    _ = ‖∑ w : MarkedWord N j, Z*(wordCoefficient τ η p m r j w s θ*
        ordinaryMarkedMinor (sourceOrdinaryKernel τ p m s θ) (wordMarks j w))‖ := by
      rw [wordSum,Finset.mul_sum]
    _ ≤ ∑ w : MarkedWord N j, ‖Z*(wordCoefficient τ η p m r j w s θ*
        ordinaryMarkedMinor (sourceOrdinaryKernel τ p m s θ) (wordMarks j w))‖ := norm_sum_le _ _
    _ ≤ (Fintype.card (MarkedWord N j):ℝ)*
        ((C^N*(N:ℝ)^J)*((Real.sqrt (N+1:ℕ))^(N+1)*A^N)) := by
      simpa using Finset.sum_le_sum (fun w (_ : w∈Finset.univ) => hb w)
    _ ≤ ((2:ℝ)^j*(N:ℝ)^(2*j))*
        ((C^N*(N:ℝ)^J)*((Real.sqrt (N+1:ℕ))^(N+1)*A^N)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by rw [pow_add,mul_pow]; ring

/-- Physical N!, not (N+1)!, cancels against the proved bordered bound. -/
theorem wordSum_factorial_bound {N : ℕ} (hN : 0<N)
    (τ : ℝ) (η p m r : ℝ → ℝ) (j : ℕ) (s : ℂ) (θ : Fin N → ℝ)
    {A C : ℝ} (hA : 1≤A) (hC : 0≤C) (J : ℕ)
    (hK : ∀ i l, ‖sourceOrdinaryKernel τ p m s θ i l‖≤A)
    (hc : ∀ w : MarkedWord N j,
      ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*wordCoefficient τ η p m r j w s θ‖≤
        C^N*(N:ℝ)^J) :
    ‖(2*Real.pi:ℂ)^(N-1)*wordSum τ η p m r j s θ‖≤
      (2:ℝ)^j*farOrderEnvelope (C*A*(4*Real.exp 1)) (J+2*j+1) N := by
  have h := wordSum_normalized_bound hN τ η p m r j s θ
    ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1)) hA hC J hK hc
  have hf : (0:ℝ)<N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hh : ‖(2*Real.pi:ℂ)^(N-1)*wordSum τ η p m r j s θ‖≤
      ((2:ℝ)^j*(N:ℝ)^(J+2*j)*(C*A)^N)*
        ((Real.sqrt (N+1:ℕ))^(N+1)/(N.factorial:ℝ)) := by
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hf).mpr
    simpa only [mul_assoc,norm_mul,Complex.norm_natCast,mul_comm] using h
  apply hh.trans
  calc
    _ ≤ ((2:ℝ)^j*(N:ℝ)^(J+2*j)*(C*A)^N)*
        ((N:ℝ)*((4*Real.exp 1)/Real.sqrt N)^N) :=
      mul_le_mul_of_nonneg_left (bordered_hadamard_factorial_envelope hN) (by positivity)
    _ = _ := by
      simp only [farOrderEnvelope,shellOrderEnvelope,pow_succ,mul_pow,div_pow]
      ring

/-- A fixed diameter floor converts every word loss into a fixed-order
constant. The floor is not differentiated and never depends on N. -/
theorem fixed_floor_word_loss {d E : ℝ} (hd : 0<d) (hE : 1≤E)
    (hfloor : 1≤E*d) {ell j : ℕ} (hl : ell≤2*j) :
    1/d^ell≤E^(2*j) := by
  have hi : d⁻¹≤E := by simpa only [one_div] using (div_le_iff₀ hd).mpr hfloor
  calc
    _ = (d⁻¹)^ell := by simp [one_div,inv_pow]
    _ ≤ E^ell := pow_le_pow_left₀ (by positivity) hi ell
    _ ≤ _ := pow_le_pow_right₀ hE hl

/-- Far estimate of the actual new transported scalar from original source
frame jets. No estimate of generated coefficients or completed tail is an
input. The fixed source geometry and the three original jet bounds remain
explicit until the contour-geometry consumer instantiates them. -/
theorem regularTransportedScalar_far_of_source_frames {N : ℕ} (hN : 0<N)
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hRcov : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω)
    (R d D : ℝ) (hR : 1≤R) (hd : 0<d) (hdD : d≤D) (hD : 1≤D)
    (E : ℝ) (hE : 1≤E) (hfloor : 1≤E*d)
    (L M j : ℕ)
    (hseed : ∀ xs : List (Option (Fin N)), xs.length≤j →
      ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*
        frameJet τ p m (regularSeedCoefficient τ η p m r) xs s θ‖≤R^N*(N:ℝ)^L)
    (hB : ∀ i (xs : List (Option (Fin N))), xs.length≤j →
      ‖frameJet τ p m
        (fun t x => residualField t (sourceCoordinate τ p m t x) i) xs s θ‖≤
          R*(N:ℝ)^M/d^(1+xs.length))
    (hK : ∀ (ij : Fin N × Fin N) (xs : List (Option (Fin N))), xs.length≤j →
      ‖frameJet τ p m
        (fun t x => sourceOrdinaryKernel τ p m t x ij.1 ij.2) xs s θ‖≤R)
 :
    ‖(2*Real.pi:ℂ)^(N-1)*regularTransportedScalar τ η p m r j s θ‖≤
      (2:ℝ)^j*farOrderEnvelope
        (((preferredCoefficientCountConstant j:ℝ)*R^(2*j+2)*D^(2*j))*
          E^(2*j)*R*(4*Real.exp 1))
        (L+M*(2*j+1)+3*j+1) N := by
  have hRn : 0≤R := le_trans (by norm_num) hR
  have hEn : 0≤E := le_trans (by norm_num) hE
  have hDn : 0≤D := le_trans (by norm_num) hD
  let C := (preferredCoefficientCountConstant j:ℝ)*R^(2*j+2)*D^(2*j)
  have hC : 0≤C := by dsimp [C]; positivity
  have hc (w : MarkedWord N j) :
      ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*wordCoefficient τ η p m r j w s θ‖≤
        (C*E^(2*j))^N*(N:ℝ)^(L+M*(2*j+1)+j) := by
    have h := wordCoefficient_bound_of_source_frames hN τ δ η p m r hη hp hm hr
      Ω hΩ hpoint hRcov s θ hz R d D hR hd hdD hD L M j hseed hB hK w
    have hl : wordLoss j w≤2*j := by
      change preferredWordLoss j w≤2*j
      have := preferredWordLoss_budget j w
      omega
    have hlos := fixed_floor_word_loss hd hE hfloor hl
    have hpow : E^(2*j)≤(E^(2*j))^N := by
      simpa only [pow_one] using pow_le_pow_right₀ (one_le_pow₀ hE) (Nat.succ_le_iff.mpr hN)
    calc
      _ ≤ C^N*(N:ℝ)^(L+M*(2*j+1)+j)/d^(wordLoss j w) := h
      _ ≤ C^N*(N:ℝ)^(L+M*(2*j+1)+j)*E^(2*j) := by
        rw [div_eq_mul_inv,←one_div]
        exact mul_le_mul_of_nonneg_left hlos (by positivity)
      _ ≤ C^N*(N:ℝ)^(L+M*(2*j+1)+j)*(E^(2*j))^N :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by rw [mul_pow]; ring
  rw [regularTransportedScalar_word_expansion_of_source τ δ η p m r
    hη hp hm hr Ω hΩ hpoint hRcov j s θ hz]
  have hh := wordSum_factorial_bound hN τ η p m r j s θ hR
    (mul_nonneg hC (pow_nonneg hEn _)) (L+M*(2*j+1)+j)
    (fun i l => hK (i,l) [] (by simp)) hc
  convert hh using 1
  congr 2
  omega

end
end IsingBulk.HT22.Tail
