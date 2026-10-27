import IsingBulk.Preferred22.PhysicalKernel

/-! Exact complex-angle half-angle normalization for the actual physical
kernel and one-body factor. No choice of square-root signs remains in the
determinant, and the identities include removable collision loci. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex
open scoped BigOperators

theorem exp_sinh_identity (v : ℂ) :
    2*exp (-v)*sinh v=1-exp (-v)^2 := by
  calc
    _ = exp (-v)*(2*sinh v) := by ring
    _ = exp (-v)*(exp v-exp (-v)) := by rw [Complex.two_sinh]
    _ = 1-exp (-v)^2 := by rw [mul_sub,← exp_add,neg_add_cancel,exp_zero]; ring

theorem oneBody_exp_phase (φ : ℂ) :
    oneBody (exp (-I*φ))=(sinh (I*φ))⁻¹ := by
  have hd : 1-exp (-I*φ)^2=(2*exp (-I*φ))*sinh (I*φ) := by
    simpa only [neg_mul] using (exp_sinh_identity (I*φ)).symm
  rw [oneBody,hd]
  have hn : 2*exp (-I*φ) ≠ 0 := mul_ne_zero (by norm_num) (exp_ne_zero _)
  calc
    _ = (2*exp (-I*φ)*1)/(2*exp (-I*φ)*sinh (I*φ)) := by rw [mul_one]
    _ = _ := by rw [mul_div_mul_left _ _ hn,one_div]

def halfAngleKernel {N : ℕ} (w φ : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => sin ((w i-w j)/2)/sinh (I*(φ i+φ j)/2)

def canonicalPhaseGauge {N : ℕ} (w φ : Fin N → ℂ) (i : Fin N) : ℂ :=
  exp (-I*(φ i+w i)/2)

theorem canonicalPhaseGauge_sq {N : ℕ} (w φ : Fin N → ℂ) (i : Fin N) :
    canonicalPhaseGauge w φ i ^ 2=exp (-I*φ i)/exp (I*w i) := by
  simp only [canonicalPhaseGauge,pow_two,← exp_add,← exp_sub]
  congr 1
  ring

theorem canonicalPhaseGauge_halfAngle {N : ℕ} (w φ : Fin N → ℂ) (i j : Fin N) :
    -I*canonicalPhaseGauge w φ i*canonicalPhaseGauge w φ j*
      (exp (I*w i)-exp (I*w j))/(1-exp (-I*φ i)*exp (-I*φ j))=
      halfAngleKernel w φ i j := by
  let b := exp (-I*(φ i+φ j)/2)
  let u := (w i-w j)/2
  have h1 : canonicalPhaseGauge w φ i*canonicalPhaseGauge w φ j*exp (I*w i)=
      b*exp (u*I) := by
    simp only [canonicalPhaseGauge,b,← exp_add]
    congr 1
    dsimp [u]
    ring
  have h2 : canonicalPhaseGauge w φ i*canonicalPhaseGauge w φ j*exp (I*w j)=
      b*exp (-u*I) := by
    simp only [canonicalPhaseGauge,b,← exp_add]
    congr 1
    dsimp [u]
    ring
  have hnum : -I*canonicalPhaseGauge w φ i*canonicalPhaseGauge w φ j*
      (exp (I*w i)-exp (I*w j))=(2*b)*sin u := by
    calc
      _ = -I*(canonicalPhaseGauge w φ i*canonicalPhaseGauge w φ j*exp (I*w i)-
        canonicalPhaseGauge w φ i*canonicalPhaseGauge w φ j*exp (I*w j)) := by ring
      _ = b*(2*sin u) := by rw [h1,h2,Complex.two_sin]; ring
      _ = _ := by ring
  have hz : exp (-I*φ i)*exp (-I*φ j)=b^2 := by
    simp only [b,pow_two,← exp_add]
    congr 1
    ring
  have hden : 1-exp (-I*φ i)*exp (-I*φ j)=(2*b)*sinh (I*(φ i+φ j)/2) := by
    rw [hz]
    simpa only [b,neg_div,neg_mul] using (exp_sinh_identity (I*(φ i+φ j)/2)).symm
  rw [hnum,hden]
  exact mul_div_mul_left _ _ (mul_ne_zero (by norm_num) (exp_ne_zero _))

/-- The actual gauge determinant equals the literal moving-chart half-angle
determinant for arbitrary complex angles and phases. -/
theorem gaugeKernel_det_eq_halfAngleKernel {N : ℕ} (w φ : Fin N → ℂ) :
    (gaugeKernel (fun i => exp (I*w i)) (fun i => exp (-I*φ i))).det=
      (halfAngleKernel w φ).det := by
  let y : Fin N → ℂ := fun i => exp (I*w i)
  let z : Fin N → ℂ := fun i => exp (-I*φ i)
  let r := canonicalPhaseGauge w φ
  have hm : halfAngleKernel w φ=
      Matrix.diagonal (fun i => -I*r i)*rationalKernel y z*Matrix.diagonal r := by
    ext i j
    simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,rationalKernel]
    have h := canonicalPhaseGauge_halfAngle w φ i j
    dsimp only [y,z,r]
    rw [← h]
    ring
  rw [hm,Matrix.det_mul,Matrix.det_mul,Matrix.det_diagonal,Matrix.det_diagonal]
  rw [gaugeKernel_det_normalization,Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hp : (∏ i,r i)*(∏ i,r i)=∏ i,z i/y i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact (pow_two (r i)).symm.trans (canonicalPhaseGauge_sq w φ i)
  calc
    _ = (-I)^N*((∏ i,r i)*(∏ i,r i))*(rationalKernel y z).det := by rw [hp]
    _ = _ := by ring

end
end IsingBulk.Preferred22
