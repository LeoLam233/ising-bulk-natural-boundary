import IsingBulk.HT22.Tail.ScalarTransport
import IsingBulk.Preferred22.RegularKernelQuotient

/-! # The full odd regular-coordinate squared Vandermonde

The pair-level analytic quotient is shared with the verified inverse chart.
The determinant-product theorem is the new HT22 odd-border proof, never
an even determinant or an original HT first/tail endpoint.
-/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000

/-- Exact rational physical-pair / half-angle identity, including diagonals. -/
theorem physicalPair_eq_halfAngle_square {N : ℕ} (w φ : Fin N → ℂ) (i j : Fin N) :
    Algebra.physicalPair (Complex.exp (Complex.I*w i)) (Complex.exp (Complex.I*w j))
      (Complex.exp (-Complex.I*φ i)) (Complex.exp (-Complex.I*φ j)) =
        (halfAngleKernel w φ i j)^2 := by
  have h := Algebra.scaledPair_sq
    (Complex.exp (Complex.I*w i)) (Complex.exp (Complex.I*w j))
    (Complex.exp (-Complex.I*φ i)) (Complex.exp (-Complex.I*φ j))
    (canonicalPhaseGauge w φ i) (canonicalPhaseGauge w φ j)
    (canonicalPhaseGauge_sq w φ i) (canonicalPhaseGauge_sq w φ j)
  have he : scaledPair (canonicalPhaseGauge w φ i) (canonicalPhaseGauge w φ j)
      (dispersionB (Complex.exp (Complex.I*w i)) (Complex.exp (Complex.I*w j))
        (Complex.exp (-Complex.I*φ i)) (Complex.exp (-Complex.I*φ j))) =
      halfAngleKernel w φ i j := by
    simpa only [scaledPair,dispersionB,mul_div_assoc] using canonicalPhaseGauge_halfAngle w φ i j
  rw [he] at h
  exact h.symm

/-- The actual odd bordered determinant is the complete half-angle pair
product. The parity is used only by the independently proved odd identity. -/
theorem odd_regularBorderedKernel_pair_product (n : ℕ) (t : ℂ)
    (v : Fin (2*n+1) → ℂ)
    (hcurve : ∀ i, Complex.cos (regularInverse t (v i))+
      Complex.cos (regularPhase t (v i))=temperatureTrace t)
    (hroot : ∀ i, ‖Complex.exp (-Complex.I*regularPhase t (v i))‖<1) :
    (regularBorderedKernel t v).det =
      ∏ i, ∏ j ∈ Finset.Ioi i,
        (halfAngleKernel (fun a => regularInverse t (v a))
          (fun a => regularPhase t (v a)) i j)^2 := by
  let y := fun i => Complex.exp (Complex.I*regularInverse t (v i))
  let z := fun i => Complex.exp (-Complex.I*regularPhase t (v i))
  have hdisp (i : Fin (2*n+1)) : y i+(y i)⁻¹+z i+(z i)⁻¹=2*temperatureTrace t := by
    have hy := exp_mul_I_dispersion (regularInverse t (v i))
    have hz := exp_mul_I_dispersion (-(regularPhase t (v i)))
    simp only [mul_neg,Complex.cos_neg] at hz
    dsimp only [y,z]
    simp only [neg_mul]
    linear_combination hy+hz+2*hcurve i
  have hden (i j : Fin (2*n+1)) (_hij : i ≠ j) : 1-z i*z j ≠ 0 := by
    intro he
    have hn : ‖z i*z j‖<1 := by
      rw [norm_mul]
      calc
        _ ≤ ‖z i‖*1 := mul_le_mul_of_nonneg_left (hroot j).le (norm_nonneg _)
        _ < 1 := by simpa only [mul_one] using hroot i
    rw [(sub_eq_zero.mp he).symm,norm_one] at hn
    exact (lt_irrefl _ hn)
  have hh := Algebra.odd_constantBorderFirst_determinant n (temperatureTrace t) y z
    (fun _ => Complex.exp_ne_zero _) (fun _ => Complex.exp_ne_zero _) hdisp hden
  change (regularBorderedKernel t v).det = _ at hh
  rw [hh]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  exact physicalPair_eq_halfAngle_square (fun a => regularInverse t (v a))
    (fun a => regularPhase t (v a)) i j

/-- The exact quotient after moving back from q to the fixed-v coordinates. -/
def regularPairQuotient (t v w : ℂ) : ℂ :=
  preferredKernelQuotient t (v-preferredMovingBranch t) (w-preferredMovingBranch t)

def squaredVandermonde {N : ℕ} (v : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, (v i-v j)^2

def regularPairAmplitude {N : ℕ} (t : ℂ) (v : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, (regularPairQuotient t (v i) (v j))^2

/-- F001's N(N−1) zeros in one global regular coordinate, including the
ordinary partial collision diagonals. The analytic domain is explicit. -/
theorem odd_regularBorderedKernel_vandermonde (n : ℕ) (c : ℝ) (t : ℂ)
    (v : Fin (2*n+1) → ℂ)
    (hgood : ∀ i j, PreferredRightRegularPoint c t
      (v i-preferredMovingBranch t) (v j-preferredMovingBranch t))
    (hroot : ∀ i, ‖Complex.exp (-Complex.I*regularPhase t (v i))‖<1)
    (hφ : ∀ i, (regularPhase t (v i)).im<0) :
    (regularBorderedKernel t v).det=squaredVandermonde v*regularPairAmplitude t v := by
  let q := fun i => v i-preferredMovingBranch t
  have hU (i : Fin (2*n+1)) : preferredMovingInverse t (q i)=regularInverse t (v i) :=
    (regularInverse_moving_adapter t (v i)).symm
  have hphase (i : Fin (2*n+1)) : preferredRegularPhase t (q i)=regularPhase t (v i) := by
    unfold preferredRegularPhase regularPhase
    rw [hU]
    dsimp only [q]
    ring
  have hcurve (i : Fin (2*n+1)) : Complex.cos (regularInverse t (v i))+
      Complex.cos (regularPhase t (v i))=temperatureTrace t := by
    rw [←hU,←hphase]
    exact preferredRegular_dispersion t (q i) (hgood i i).2.2.2.2.2.1
  rw [odd_regularBorderedKernel_pair_product n t v hcurve hroot]
  have hpair (i j : Fin (2*n+1)) :
      halfAngleKernel (fun a => regularInverse t (v a)) (fun a => regularPhase t (v a)) i j=
        (v i-v j)*regularPairQuotient t (v i) (v j) := by
    have hh := preferred_regular_pair_factor c t (q i) (q j) (hgood i j)
      (by rw [hphase]; exact hφ i) (by rw [hphase]; exact hφ j)
    change Complex.sin ((preferredMovingInverse t (q i)-preferredMovingInverse t (q j))/2)/
      Complex.sinh (Complex.I*(preferredRegularPhase t (q i)+preferredRegularPhase t (q j))/2)=_ at hh
    rw [hU,hU,hphase,hphase] at hh
    simpa only [halfAngleKernel,regularPairQuotient,q,sub_sub_sub_cancel_right] using hh
  simp_rw [hpair,mul_pow]
  simp only [Finset.prod_mul_distrib,squaredVandermonde,regularPairAmplitude]

end
end IsingBulk.HT22.Tail
