import IsingBulk.Anisotropic.NegativeCycles.FreeHomotopyDerivative
import IsingBulk.Anisotropic.NegativeNormalForm.DensityJacobianLinear

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm Set Metric

 theorem norm_freeCoordinates_le {n : ℕ} (v : Config (n+1)) :
    ‖freeCoordinatesCLM n v‖≤‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  exact norm_le_pi_norm v i.castSucc

 theorem norm_freeChart_single_le {n : ℕ} (i : Fin n) :
    ‖freeChartCLM n (Pi.single i 1)‖≤1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · by_cases h : k=i
    · subst k; simp
    · simp [h]

 theorem constrainedDerivative_single_sub_le {n : ℕ}
    (L : Config (n+1)→L[ℂ] Config (n+1)) {e : ℝ} (he : 0≤e)
    (hL : ‖L-ContinuousLinearMap.id ℂ (Config (n+1))‖≤e) (i : Fin n) :
    ‖constrainedDerivative L (Pi.single i 1)-Pi.single i 1‖≤e := by
  have heq : constrainedDerivative L (Pi.single i 1)-Pi.single i 1=
      freeCoordinatesCLM n ((L-ContinuousLinearMap.id ℂ (Config (n+1)))
        (freeChartCLM n (Pi.single i 1))) := by
    simp [constrainedDerivative,ContinuousLinearMap.comp_apply]
    ext k
    simp
  rw [heq]
  calc
    _ ≤ ‖(L-ContinuousLinearMap.id ℂ (Config (n+1))) (freeChartCLM n (Pi.single i 1))‖ := norm_freeCoordinates_le _
    _ ≤ ‖L-ContinuousLinearMap.id ℂ (Config (n+1))‖*‖freeChartCLM n (Pi.single i 1)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ e*1 := mul_le_mul hL (norm_freeChart_single_le i) (norm_nonneg _) he
    _ = e := mul_one _

/-- Every entry of the actual homotopy derivative is bounded independently of dimension. -/
theorem actualHomotopy_derivative_entries_bound {n : ℕ}
    (B : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ) (r C R : ℝ)
    (P : UniformProjectedWitness B phi hphi (n+1) d r C)
    (J : UniformCorrectionWitness B phi hphi (n+1) d r C P R)
    (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) {ρ : ℝ} (hρ : 0≤ρ) (hρR : ρ<R/2)
    (x : ParameterSpace n) (hs : x 0∈Icc (-1/2:ℝ) (3/2))
    (hq : constrainedSquaredRadius (fun i => x i.succ)≤ρ^2) (i : Fin (n+1)) (k : Fin n) :
    ‖fderiv ℝ (freeStraightHomotopy (constrainedMap (fun y => P.V (J.W y)))) x (Pi.single i 1) k‖≤2+ρ := by
  let y := freeChartCLM n (complexSpatial n x)
  let Phi : Config (n+1)→Config (n+1) := fun y => P.V (J.W y)
  let Psi := constrainedMap Phi
  have hyρ : ‖y‖≤ρ := by
    dsimp only [y]
    rw [freeChartCLM_eq_shapeExtend]
    exact norm_shapeExtend_complexify_le _ hρ hq
  have hyR : ‖y‖<R/2 := hyρ.trans_lt hρR
  have hPhi : DifferentiableAt ℂ Phi y :=
    ((J.corrected_bounds B phi hphi d r C R P hr hR hRr).1 y (by simpa using hyR)).differentiableAt
  have hcomp : DifferentiableAt ℂ (fun q => Phi (freeChartCLM n q)) (complexSpatial n x) :=
    hPhi.comp (f := freeChartCLM n) (g := Phi) _ (freeChartCLM n).differentiableAt
  have hPsi : DifferentiableAt ℂ Psi (complexSpatial n x) :=
    (freeCoordinatesCLM n).differentiableAt.comp _ hcomp
  have hD := J.corrected_derivative_bound B phi hphi d r C R P hr hR hRr y hyR
  have hsN : ‖(x 0:ℂ)‖≤3/2 := by
    simp only [Complex.norm_real,Real.norm_eq_abs]
    rw [abs_le]; constructor <;> linarith [hs.1,hs.2]
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [freeStraightHomotopy_time_derivative _ x hPsi]
    have heq : Psi (complexSpatial n x)-complexSpatial n x=
        freeCoordinatesCLM n (Phi y-y) := by
      simp [Psi,constrainedMap,y,ContinuousLinearMap.map_sub]
      ext k
      simp
    have hsmall := ((J.corrected_bounds B phi hphi d r C R P hr hR hRr).2 y hyR.le).2
    have hn : ‖Psi (complexSpatial n x)-complexSpatial n x‖≤(3/32:ℝ)*ρ := by
      rw [heq]
      exact (norm_freeCoordinates_le _).trans (hsmall.trans (mul_le_mul_of_nonneg_left hyρ (by norm_num)))
    have hk := norm_le_pi_norm (Psi (complexSpatial n x)-complexSpatial n x) k
    change ‖(Psi (complexSpatial n x)-complexSpatial n x) k‖≤2+ρ
    linarith
  · rw [freeStraightHomotopy_spatial_derivative _ x hPsi j]
    have hcolumn : ‖fderiv ℂ Psi (complexSpatial n x) (Pi.single j 1)-Pi.single j 1‖≤3/32 := by
      rw [constrainedMap_fderiv hPhi]
      exact constrainedDerivative_single_sub_le _ (by norm_num) hD j
    have hbase : ‖(Pi.single j (1:ℂ) : Config n)‖≤1 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
      intro l
      by_cases h : l=j
      · subst l; simp
      · simp [h]
    have hnorm := norm_add_le (Pi.single j (1:ℂ) : Config n)
      ((x 0:ℂ) • (fderiv ℂ Psi (complexSpatial n x) (Pi.single j 1)-Pi.single j 1))
    rw [norm_smul] at hnorm
    have hmul := mul_le_mul hsN hcolumn (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)
    have hk := norm_le_pi_norm ((Pi.single j (1:ℂ) : Config n)+
      (x 0:ℂ) • (fderiv ℂ Psi (complexSpatial n x) (Pi.single j 1)-Pi.single j 1)) k
    exact hk.trans (by linarith)

end IsingBulk.Anisotropic.NegativeCycles
