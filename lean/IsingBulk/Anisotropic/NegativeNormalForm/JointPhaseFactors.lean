import IsingBulk.Anisotropic.NegativeNormalForm.RemovableEnergy

/-! Concrete joint divided differences from the actual cosh dispersion.
No general parameter-dependent division theorem or normal form is assumed. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

def zeroSlope (f : ℂ → ℂ) (z : ℂ) : ℂ := dslope f 0 z

theorem zeroSlope_mul (f : ℂ → ℂ) (z : ℂ) : z*zeroSlope f z=f z-f 0 := by
  simpa only [zeroSlope, sub_zero, smul_eq_mul] using sub_smul_dslope f 0 z

@[simp] theorem zeroSlope_zero (f : ℂ → ℂ) : zeroSlope f 0=deriv f 0 := dslope_same f 0

theorem zeroSlope_analyticAt {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (zeroSlope f) 0 := analyticAt_dslope_center hf

/-- Hyperbolic divided-difference denominator, nonzero near the chosen phase. -/
def hyperbolicDivisor (u z : ℂ) : ℂ :=
  Complex.sinh (u+z/2)*zeroSlope Complex.sinh (z/2)

def hyperbolicDivisorSlope (u z : ℂ) : ℂ :=
  Complex.sinh u*zeroSlope Complex.cosh (z/2)*zeroSlope Complex.sinh (z/2) +
  Complex.cosh u*(zeroSlope Complex.sinh (z/2))^2 +
  Complex.sinh u*zeroSlope (zeroSlope Complex.sinh) (z/2)

@[simp] theorem hyperbolicDivisor_zero (u : ℂ) : hyperbolicDivisor u 0=Complex.sinh u := by
  simp [hyperbolicDivisor]

theorem cosh_increment_factor (u z : ℂ) :
    Complex.cosh (u+z)-Complex.cosh u = z*hyperbolicDivisor u z := by
  have hu : u+z=(u+z/2)+z/2 := by ring
  have hu' : u=(u+z/2)-z/2 := by ring
  have hs := zeroSlope_mul Complex.sinh (z/2)
  simp only [Complex.sinh_zero, sub_zero] at hs
  calc
    _ = 2*Complex.sinh (u+z/2)*Complex.sinh (z/2) := by
      conv_lhs => lhs; arg 1; rw [hu]
      conv_lhs => rhs; arg 1; rw [hu']
      rw [Complex.cosh_add, Complex.cosh_sub]
      ring
    _ = _ := by rw [← hs]; unfold hyperbolicDivisor; ring

/-- The second division is reduced to fixed-center sinh/cosh slopes. -/
theorem hyperbolicDivisor_increment (u z : ℂ) :
    hyperbolicDivisor u z-Complex.sinh u = (z/2)*hyperbolicDivisorSlope u z := by
  have hc := zeroSlope_mul Complex.cosh (z/2)
  have hs := zeroSlope_mul Complex.sinh (z/2)
  have hd := zeroSlope_mul (zeroSlope Complex.sinh) (z/2)
  simp only [Complex.cosh_zero, Complex.sinh_zero, sub_zero, zeroSlope_zero, Complex.deriv_sinh] at *
  simp only [hyperbolicDivisor, hyperbolicDivisorSlope, Complex.sinh_add]
  linear_combination -(Complex.sinh u*zeroSlope Complex.sinh (z/2))*hc -
    (Complex.cosh u*zeroSlope Complex.sinh (z/2))*hs - Complex.sinh u*hd

def cosineFirstFactor (B : ℂ → ℂ) (d t v : ℂ) : ℂ :=
  B t*(Complex.cos d*zeroSlope Complex.cos v-Complex.sin d*zeroSlope Complex.sin v)

def cosineSecondFactor (B : ℂ → ℂ) (d t v : ℂ) : ℂ :=
  B t*(Complex.cos d*zeroSlope (zeroSlope Complex.cos) v-
    Complex.sin d*zeroSlope (zeroSlope Complex.sin) v)

theorem cosineFirstFactor_identity (B : ℂ → ℂ) (d t v : ℂ) :
    negativeDispersion B 0 t (d+v)-negativeDispersion B 0 t d = v*cosineFirstFactor B d t v := by
  have hc := zeroSlope_mul Complex.cos v
  have hs := zeroSlope_mul Complex.sin v
  simp only [Complex.cos_zero, Complex.sin_zero, sub_zero] at *
  simp only [negativeDispersion, zero_add, cosineFirstFactor, Complex.cos_add]
  linear_combination -(B t*Complex.cos d)*hc + (B t*Complex.sin d)*hs

theorem cosineSecondFactor_identity (B : ℂ → ℂ) (d t v : ℂ) :
    cosineFirstFactor B d t v-cosineFirstFactor B d t 0 = v*cosineSecondFactor B d t v := by
  have hc := zeroSlope_mul (zeroSlope Complex.cos) v
  have hs := zeroSlope_mul (zeroSlope Complex.sin) v
  unfold cosineFirstFactor cosineSecondFactor
  linear_combination -(B t*Complex.cos d)*hc + (B t*Complex.sin d)*hs

def phaseIncrement (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d t v : ℂ) : ℂ :=
  negativePhase B phi hphi t (d+v)-negativePhase B phi hphi t d

def phaseFirstFactor (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d t v : ℂ) : ℂ :=
  cosineFirstFactor B d t v /
    hyperbolicDivisor (negativePhase B phi hphi t d) (phaseIncrement B phi hphi d t v)

def phaseSecondFactor (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d t v : ℂ) : ℂ :=
  (cosineSecondFactor B d t v * Complex.sinh (negativePhase B phi hphi t d) -
    cosineFirstFactor B d t 0 * (phaseFirstFactor B phi hphi d t v/2) *
      hyperbolicDivisorSlope (negativePhase B phi hphi t d) (phaseIncrement B phi hphi d t v)) /
  (hyperbolicDivisor (negativePhase B phi hphi t d) (phaseIncrement B phi hphi d t v) *
    Complex.sinh (negativePhase B phi hphi t d))

end
end IsingBulk.Anisotropic.NegativeNormalForm
