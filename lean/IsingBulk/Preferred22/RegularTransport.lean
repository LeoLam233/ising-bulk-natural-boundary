import IsingBulk.Preferred22.Transport
import IsingBulk.Preferred22.ComplexKernelBridge
import IsingBulk.Preferred22.ContourLegality

namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology

/-- The actual occupancy differential has an l1 row bound independent of
particle count. Its diagonal and both rank-one occupancy terms are retained. -/
theorem preferred_shiftJacobian_row_bound {N : ℕ} (hN : 0 < N) (τ B : ℝ)
    (hτ : 0 ≤ τ) (_hB : 0 ≤ B) (p m dp dm : Fin N → ℝ)
    (hp : ∀ i, |p i| ≤ 1) (hm : ∀ i, |m i| ≤ 1)
    (hdp : ∀ i, |dp i| ≤ B) (hdm : ∀ i, |dm i| ≤ B) (i : Fin N) :
    (∑ j, |shiftJacobian τ p m dp dm i j|) ≤ 4*τ*B := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hpSum : |∑ a, p a| ≤ N := by
    calc
      _ ≤ ∑ a, |p a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin N, (1:ℝ) := Finset.sum_le_sum (fun a _ => hp a)
      _ = _ := by simp
  have hmSum : |∑ a, m a| ≤ N := by
    calc
      _ ≤ ∑ a, |m a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin N, (1:ℝ) := Finset.sum_le_sum (fun a _ => hm a)
      _ = _ := by simp
  have hd : |(∑ a, p a)*dm i-(∑ a, m a)*dp i| ≤ 2*(N:ℝ)*B := by
    calc
      _ ≤ |(∑ a, p a)*dm i|+|(∑ a, m a)*dp i| := abs_sub _ _
      _ = |∑ a, p a| * |dm i|+|∑ a, m a| * |dp i| := by rw [abs_mul,abs_mul]
      _ ≤ (N:ℝ)*B+(N:ℝ)*B := add_le_add
        (mul_le_mul hpSum (hdm i) (abs_nonneg _) hNR.le)
        (mul_le_mul hmSum (hdp i) (abs_nonneg _) hNR.le)
      _ = _ := by ring
  have hc (j : Fin N) : |m i*dp j-p i*dm j| ≤ 2*B := by
    calc
      _ ≤ |m i*dp j|+|p i*dm j| := abs_sub _ _
      _ = |m i| * |dp j|+|p i| * |dm j| := by rw [abs_mul,abs_mul]
      _ ≤ 1*B+1*B := add_le_add (mul_le_mul (hm i) (hdp j) (abs_nonneg _) (by norm_num))
        (mul_le_mul (hp i) (hdm j) (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have he (j : Fin N) : |shiftJacobian τ p m dp dm i j| ≤
      (τ/(N:ℝ))*((if i=j then 2*(N:ℝ)*B else 0)+2*B) := by
    unfold shiftJacobian
    rw [abs_mul,abs_of_nonneg (div_nonneg hτ hNR.le)]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hτ hNR.le)
    calc
      _ ≤ |if i=j then (∑ a, p a)*dm i-(∑ a, m a)*dp i else 0| +
        |m i*dp j-p i*dm j| := by
        convert! abs_add_le
          (if i=j then (∑ a, p a)*dm i-(∑ a, m a)*dp i else 0)
          (m i*dp j-p i*dm j) using 1
        ring
      _ ≤ (if i=j then 2*(N:ℝ)*B else 0)+2*B := by
        apply add_le_add _ (hc j)
        split_ifs
        · exact hd
        · simp
  calc
    _ ≤ ∑ j, (τ/(N:ℝ))*((if i=j then 2*(N:ℝ)*B else 0)+2*B) :=
      Finset.sum_le_sum (fun j _ => he j)
    _ = 4*τ*B := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp
      ring

theorem preferred_matrix_mulVec_row_bound {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hrow : ∀ i, (∑ j, ‖A i j‖) ≤ κ) (v : Fin N → ℂ) :
    ‖A.mulVec v‖ ≤ κ*‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hκ (norm_nonneg v))).mpr
  intro i
  calc
    _ ≤ ∑ j, ‖A i j*v j‖ := norm_sum_le _ _
    _ = ∑ j, ‖A i j‖*‖v j‖ := by simp only [norm_mul]
    _ ≤ ∑ j, ‖A i j‖*‖v‖ := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _))
    _ = (∑ j, ‖A i j‖)*‖v‖ := by rw [Finset.sum_mul]
    _ ≤ κ*‖v‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg v)

/-- A pointwise l1 row bound proves a true inverse bound; no determinant
lower-bound assumption or inverse matrix estimate is supplied. -/
theorem preferred_matrix_inverse_of_row_half {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (hrow : ∀ i, (∑ j, ‖(M-1) i j‖) ≤ (1/2:ℝ)) :
    M.det ≠ 0 ∧ ∀ x : Fin N → ℂ, ‖M⁻¹.mulVec x‖ ≤ 2*‖x‖ := by
  have hcoer (v : Fin N → ℂ) : ‖v‖ ≤ 2*‖M.mulVec v‖ := by
    have hh := preferred_matrix_mulVec_row_bound (M-1) (1/2) (by norm_num) hrow v
    rw [Matrix.sub_mulVec,Matrix.one_mulVec] at hh
    have ht := norm_sub_norm_le v (M.mulVec v)
    rw [norm_sub_rev] at ht
    linarith
  have hinj : Function.Injective M.mulVec := by
    intro v w he
    have hh := hcoer (v-w)
    rw [Matrix.mulVec_sub,he,sub_self,norm_zero,mul_zero] at hh
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  have hdet : M.det ≠ 0 := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj))
  refine ⟨hdet,?_⟩
  intro x
  have hh := hcoer (M⁻¹.mulVec x)
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec] at hh
  exact hh

/-- Source-specific, particle-independent inverse bound for the entire
occupancy Jacobian. This is uniform in epsilon because M contains no s. -/
theorem preferredContourMatrix_inverse_bound {N : ℕ} (hN : 0 < N) (τ B : ℝ)
    (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hsmall : 4*τ*B ≤ 1/2)
    (p m : ℝ → ℝ) (θ : Fin N → ℝ)
    (hp : ∀ i, |p (θ i)| ≤ 1) (hm : ∀ i, |m (θ i)| ≤ 1)
    (hdp : ∀ i, |deriv p (θ i)| ≤ B) (hdm : ∀ i, |deriv m (θ i)| ≤ B) :
    (preferredContourMatrix τ p m θ).det ≠ 0 ∧
      ∀ x : Fin N → ℂ, ‖(preferredContourMatrix τ p m θ)⁻¹.mulVec x‖ ≤ 2*‖x‖ := by
  apply preferred_matrix_inverse_of_row_half
  intro i
  have he (j : Fin N) : ‖(preferredContourMatrix τ p m θ-1) i j‖ =
      |shiftJacobian τ (fun a => p (θ a)) (fun a => m (θ a))
        (fun a => deriv p (θ a)) (fun a => deriv m (θ a)) i j| := by
    simp only [Matrix.sub_apply,preferredContourMatrix,Matrix.one_apply]
    rw [show (if i=j then (1:ℂ) else 0)-Complex.I*
      (shiftJacobian τ (fun a => p (θ a)) (fun a => m (θ a))
        (fun a => deriv p (θ a)) (fun a => deriv m (θ a)) i j:ℝ)-
      (if i=j then 1 else 0) = -Complex.I*
      (shiftJacobian τ (fun a => p (θ a)) (fun a => m (θ a))
        (fun a => deriv p (θ a)) (fun a => deriv m (θ a)) i j:ℝ) by ring]
    simp only [norm_mul,norm_neg,Complex.norm_I,Complex.norm_real,one_mul,Real.norm_eq_abs]
  simp_rw [he]
  exact (preferred_shiftJacobian_row_bound hN τ B hτ hB _ _ _ _ hp hm hdp hdm i).trans hsmall

/-- Every physical source phase on the actual contour is recovered by the
regular moving inverse once the exact source inverse identity is known. -/
theorem preferred_regular_phase_on_source {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ)
    (hU : ∀ i, preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i) =
      deformedAngles τ p m θ i) (i : Fin N) :
    preferredRegularPhase s (preferredSourceCoordinate τ p m s θ i) =
      preferredSourcePhase τ p m s θ i := by
  unfold preferredRegularPhase
  rw [hU i]
  unfold preferredSourceCoordinate
  ring

/-- The complete physical seed equals J times the literal source regular
amplitude, with its full real weight and exact Haar normalization. All
one-body cancellations are proved, not folded into a supplied amplitude. -/
theorem preferredPhysicalSeed_eq_regular {N : ℕ} (cell : PreferredTransportCell N)
    (τ : ℝ) (η p m r : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hW : ∀ i, 0 < (temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hU : ∀ i, preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i) =
      deformedAngles τ p m θ i)
    (hUq : ∀ i, preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i) ≠ 0) :
    preferredPhysicalSeed cell τ η p m r s θ =
      (preferredCellWeight cell η p m r θ:ℂ)*preferredCoordinateJacobian τ p m s θ *
        preferredRegularAmplitude s (preferredSourceCoordinate τ p m s θ) := by
  let q := preferredSourceCoordinate τ p m s θ
  let w := deformedAngles τ p m θ
  let φ := preferredSourcePhase τ p m s θ
  have hφ (i : Fin N) : preferredRegularPhase s (q i)=φ i :=
    preferred_regular_phase_on_source τ p m s θ hU i
  have hz (i : Fin N) : physicalRoot (temperatureTrace s-Complex.cos (w i)) =
      Complex.exp (-Complex.I*φ i) := (preferredArccos_physical_upper _ (hW i)).symm
  have hZ : (∏ i, Complex.exp (-Complex.I*φ i))=preferredRegularProductPhase s q := by
    rw [← Complex.exp_sum]
    unfold preferredRegularProductPhase
    simp_rw [hφ]
    congr 1
    rw [Finset.mul_sum]
  have hK : preferredRegularKernel s q=halfAngleKernel w φ := by
    ext i j
    simp only [preferredRegularKernel,halfAngleKernel,hφ]
    rw [hU i,hU j]
  have hdensity : preferredDeformedPhysicalDensity τ p m s θ =
      (1+preferredRegularProductPhase s q)/(1-preferredRegularProductPhase s q) *
        (preferredRegularKernel s q).det * ∏ i, (Complex.sinh (Complex.I*φ i))⁻¹ := by
    unfold preferredDeformedPhysicalDensity
    change (1+∏ i,physicalRoot (temperatureTrace s-Complex.cos (w i)))/
      (1-∏ i,physicalRoot (temperatureTrace s-Complex.cos (w i))) *
      (gaugeKernel (fun i=>Complex.exp (Complex.I*w i))
        (fun i=>physicalRoot (temperatureTrace s-Complex.cos (w i)))).det *
      (∏ i,oneBody (physicalRoot (temperatureTrace s-Complex.cos (w i)))) = _
    simp_rw [hz]
    rw [gaugeKernel_det_eq_halfAngleKernel,hZ,← hK]
    simp only [oneBody_exp_phase]
  have ha : (∏ i, preferredRegularOneBody s (q i)) =
      (∏ i,preferredSourceUQ s (q i))*(∏ i,(Complex.sinh (Complex.I*φ i))⁻¹) := by
    simp only [preferredRegularOneBody,hφ,div_eq_mul_inv,Finset.prod_mul_distrib]
  have hu : (∏ i,(preferredSourceUQ s (q i))⁻¹)*(∏ i,preferredSourceUQ s (q i))=1 := by
    rw [← Finset.prod_mul_distrib]
    have huqi (i : Fin N) : preferredSourceUQ s (q i) ≠ 0 := hUq i
    simp only [inv_mul_cancel₀ (huqi _),Finset.prod_const_one]
  unfold preferredPhysicalSeed preferredCoordinateJacobian preferredRegularAmplitude
  change (preferredCellWeight cell η p m r θ:ℂ)*(preferredContourMatrix τ p m θ).det *
      preferredDeformedPhysicalDensity τ p m s θ / _ =
    (preferredCellWeight cell η p m r θ:ℂ)*
      ((preferredContourMatrix τ p m θ).det*(∏ i,(preferredSourceUQ s (q i))⁻¹))*
        ((1+preferredRegularProductPhase s q)/(1-preferredRegularProductPhase s q)*
          (preferredRegularKernel s q).det*(∏ i,preferredRegularOneBody s (q i)) / _)
  rw [hdensity,ha]
  calc
    _ = ((∏ i,(preferredSourceUQ s (q i))⁻¹)*(∏ i,preferredSourceUQ s (q i))) *
      ((preferredCellWeight cell η p m r θ:ℂ)*(preferredContourMatrix τ p m θ).det *
        ((1+preferredRegularProductPhase s q)/(1-preferredRegularProductPhase s q) *
          (preferredRegularKernel s q).det * ∏ i,(Complex.sinh (Complex.I*φ i))⁻¹) /
          ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))) := by rw [hu,one_mul]
    _ = _ := by ring

/-- Formula (7.5) for the complete actual one-sided source density. The
moving inverse, physical branch and nonzero Uq are all derived here from
primitive source margins on the literal deformed angles. -/
theorem preferred_one_sided_seed_eq_regular {N : ℕ} (cell : PreferredTransportCell N)
    (τ δ : ℝ) (η p m r : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hδ : 0 < δ) (hδπ : δ < Real.pi/2)
    (hS : 0 < (temperatureTrace s).re)
    (hSδ : (temperatureTrace s).re < 2*Real.cos δ)
    (hθ : ∀ i, θ i ∈ Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0 < (temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    preferredPhysicalSeed cell τ η p m r s θ =
      (preferredCellWeight cell η p m r θ:ℂ)*preferredCoordinateJacobian τ p m s θ *
        preferredRegularAmplitude s (preferredSourceCoordinate τ p m s θ) := by
  have hwre (i : Fin N) : (deformedAngles τ p m θ i).re=θ i := by
    simp [deformedAngles,Complex.mul_re]
  have hU (i : Fin N) : preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i)=
      deformedAngles τ p m θ i := by
    exact preferred_global_one_sided_inverse s (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
      (by rw [hwre]; exact (hθ i).1) (by rw [hwre]; exact (hθ i).2) (hW i)
  have hUq (i : Fin N) : preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i) ≠ 0 := by
    exact (preferred_global_one_sided_q_regular s (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
      (by rw [hwre]; exact (hθ i).1) (by rw [hwre]; exact (hθ i).2) (hW i)).2
  exact preferredPhysicalSeed_eq_regular cell τ η p m r s θ hW hU hUq

/-- The upper W-hypothesis in the preceding theorem follows from the actual
balanced occupancy deformation and the support signs of the original bumps. -/
theorem preferred_balanced_seed_eq_regular {N : ℕ} (cell : PreferredTransportCell N)
    (τ δ : ℝ) (η p m r : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hδ : 0 < δ) (hδπ : δ < Real.pi/2) (hτ : 0 ≤ τ)
    (hS : 0 < (temperatureTrace s).re) (hSi : 0 < (temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re < 2*Real.cos δ)
    (hθ : ∀ i, θ i ∈ Set.Icc (-Real.pi-δ) δ)
    (hp0 : ∀ x, 0 ≤ p x) (hm0 : ∀ x, 0 ≤ m x)
    (hps : ∀ x, Real.sin x ≤ 0 → p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → m x=0) :
    preferredPhysicalSeed cell τ η p m r s θ =
      (preferredCellWeight cell η p m r θ:ℂ)*preferredCoordinateJacobian τ p m s θ *
        preferredRegularAmplitude s (preferredSourceCoordinate τ p m s θ) := by
  apply preferred_one_sided_seed_eq_regular cell τ δ η p m r s θ hδ hδπ hS hSδ hθ
  intro i
  have h := homotopy_complexW_im_pos hSi hτ (by norm_num : (0:ℝ) ≤ 1) p m θ hp0 hm0 hps hms i
  simpa only [complexW_homotopyRoot_eq] using h

/-- The full coupled angular q-Jacobian: every entry contains the actual
occupancy Jacobian and the retained integrable inverse-Uq factor. -/
theorem preferredSourceCoordinate_hasDerivAt {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (i j : Fin N)
    (hδ : 0 < δ) (hδπ : δ < Real.pi/2)
    (hS : 0 < (temperatureTrace s).re)
    (hSδ : (temperatureTrace s).re < 2*Real.cos δ)
    (hθ : θ i ∈ Set.Icc (-Real.pi-δ) δ)
    (hW : 0 < (temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    HasDerivAt (fun x : ℝ => preferredSourceCoordinate τ p m s (Function.update θ j x) i)
      ((preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i))⁻¹ *
        preferredContourMatrix τ p m θ i j) (θ j) := by
  have hwre : (deformedAngles τ p m θ i).re=θ i := by simp [deformedAngles,Complex.mul_re]
  have hforward := preferred_forward_coordinate_hasDerivAt s (deformedAngles τ p m θ i) δ
    hδ hδπ hS hSδ (by rw [hwre]; exact hθ.1) (by rw [hwre]; exact hθ.2) hW
  have hdeform := preferred_deformedAngle_hasDerivAt τ p m hp hm θ i j
  have hchain := (hforward.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (θ j) hdeform
    (by simp only [Function.update_eq_self])
  convert! hchain using 1
  simp [ContinuousLinearMap.toSpanSingleton_apply,preferredSourceUQ,
    preferredSourceCoordinate,preferredSourcePhase,mul_comm]

/-- The genuine real-coordinate derivative matrix of the actual q map. -/
def preferredSourceJacobian {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => deriv (fun x : ℝ => preferredSourceCoordinate τ p m s (Function.update θ j x) i) (θ j)

/-- The literal Jacobian factorization (7.4) at every actual contour point. -/
theorem preferredSourceJacobian_factorization {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (hδ : 0 < δ) (hδπ : δ < Real.pi/2)
    (hS : 0 < (temperatureTrace s).re) (hSδ : (temperatureTrace s).re < 2*Real.cos δ)
    (hθ : ∀ i, θ i ∈ Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0 < (temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    preferredSourceJacobian τ p m s θ =
      Matrix.diagonal (fun i => (preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i))⁻¹) *
        preferredContourMatrix τ p m θ := by
  ext i j
  rw [Matrix.diagonal_mul]
  exact (preferredSourceCoordinate_hasDerivAt τ δ p m hp hm s θ i j hδ hδπ hS hSδ (hθ i) (hW i)).deriv

theorem preferredSourceJacobian_det {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (hδ : 0 < δ) (hδπ : δ < Real.pi/2)
    (hS : 0 < (temperatureTrace s).re) (hSδ : (temperatureTrace s).re < 2*Real.cos δ)
    (hθ : ∀ i, θ i ∈ Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0 < (temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    (preferredSourceJacobian τ p m s θ).det = preferredCoordinateJacobian τ p m s θ := by
  rw [preferredSourceJacobian_factorization τ δ p m hp hm s θ hδ hδπ hS hSδ hθ hW,
    Matrix.det_mul,Matrix.det_diagonal,preferredCoordinateJacobian]
  ring

/-- The exact regular-coordinate frame has M inverse times Uq and never
introduces an inverse-Uq factor in differentiated amplitudes. -/
theorem preferredSourceJacobian_inverse {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (hδ : 0 < δ) (hδπ : δ < Real.pi/2)
    (hS : 0 < (temperatureTrace s).re) (hSδ : (temperatureTrace s).re < 2*Real.cos δ)
    (hθ : ∀ i, θ i ∈ Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0 < (temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    (preferredSourceJacobian τ p m s θ)⁻¹ =
      (preferredContourMatrix τ p m θ)⁻¹ *
        Matrix.diagonal (fun i => preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)) := by
  rw [preferredSourceJacobian_factorization τ δ p m hp hm s θ hδ hδπ hS hSδ hθ hW,
    Matrix.mul_inv_rev,Matrix.inv_diagonal]
  have hu (i : Fin N) : preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i) ≠ 0 := by
    have hwre : (deformedAngles τ p m θ i).re=θ i := by simp [deformedAngles,Complex.mul_re]
    exact (preferred_global_one_sided_q_regular s (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
      (by rw [hwre]; exact (hθ i).1) (by rw [hwre]; exact (hθ i).2) (hW i)).2
  let u : (Fin N → ℂ)ˣ :=
    { val := fun i => (preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i))⁻¹
      inv := fun i => preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)
      val_inv := by ext i; exact inv_mul_cancel₀ (hu i)
      inv_val := by ext i; exact mul_inv_cancel₀ (hu i) }
  change (preferredContourMatrix τ p m θ)⁻¹ * Matrix.diagonal (Ring.inverse (u:Fin N → ℂ)) = _
  rw [Ring.inverse_unit]
  rfl

/-- The actual fixed-q frame, with the complete real occupancy dependence,
is exactly the inverse complex angular derivative matrix applied to real
angular derivatives. -/
theorem preferredCoordinateFrame_eq_inverse_jacobian {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (a : Fin N) (F : ℂ → (Fin N → ℝ) → ℂ)
    (hδ : 0 < δ) (hδπ : δ < Real.pi/2)
    (hS : 0 < (temperatureTrace s).re) (hSδ : (temperatureTrace s).re < 2*Real.cos δ)
    (hθ : ∀ i, θ i ∈ Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0 < (temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    preferredCoordinateFrame τ p m a F s θ =
      ∑ i, (preferredSourceJacobian τ p m s θ)⁻¹ i a *
        deriv (fun x : ℝ => F s (Function.update θ i x)) (θ i) := by
  rw [preferredSourceJacobian_inverse τ δ p m hp hm s θ hδ hδπ hS hSδ hθ hW]
  simp only [preferredCoordinateFrame,Matrix.mul_diagonal]


/-- The genuine parameter derivative of the forward moving coordinate,
obtained by differentiating the actual inverse germ. -/
theorem preferred_forward_parameter_hasDerivAt (s w : ℂ) (δ : ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSi : 0<(temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθlo : -Real.pi-δ≤w.re) (hθhi : w.re≤δ)
    (hW : 0<(temperatureTrace s-Complex.cos w).im) :
    let q := preferredArccos (temperatureTrace s-Complex.cos w)+w-preferredMovingBranch s
    HasDerivAt (fun t : ℂ => preferredArccos (temperatureTrace t-Complex.cos w)+w-preferredMovingBranch t)
      (-preferredSourceUDot s q/preferredSourceUQ s q) s := by
  let χ : ℂ → ℂ := fun t => preferredArccos (temperatureTrace t-Complex.cos w)+w-preferredMovingBranch t
  have hs0 : s≠0 := by intro hz; simp [hz,temperatureTrace] at hSi
  have hSa : AnalyticAt ℂ temperatureTrace s := analyticAt_id.add (analyticAt_id.inv hs0)
  have hφ : AnalyticAt ℂ (fun t : ℂ => preferredArccos (temperatureTrace t-Complex.cos w)) s :=
    AnalyticAt.comp (f := fun t : ℂ => temperatureTrace t-Complex.cos w)
      (g := preferredArccos) (IsingBulk.Branch.lowerArccos_analytic_of_upper hW)
      (hSa.sub analyticAt_const)
  have hχ : AnalyticAt ℂ χ s := (hφ.add analyticAt_const).sub
    (preferredMovingBranch_analyticAt_upper s hSi)
  have hU := preferred_global_one_sided_joint_analytic s w δ hδ hδπ hS hSi hSδ hθlo hθhi hW
  have hSr := Complex.continuous_re.continuousAt.comp hSa.continuousAt
  have hWi : ContinuousAt (fun t : ℂ => (temperatureTrace t-Complex.cos w).im) s :=
    Complex.continuous_im.continuousAt.comp (hSa.sub analyticAt_const).continuousAt
  have hslo := (continuousAt_const : ContinuousAt (fun _ : ℂ => (0:ℝ)) s).eventually_lt hSr hS
  have hshi := hSr.eventually_lt (continuousAt_const : ContinuousAt (fun _ : ℂ => 2*Real.cos δ) s) hSδ
  have hwpos := (continuousAt_const : ContinuousAt (fun _ : ℂ => (0:ℝ)) s).eventually_lt hWi hW
  have heq : (fun t : ℂ => preferredMovingInverse t (χ t)) =ᶠ[𝓝 s] (fun _ => w) := by
    filter_upwards [hslo,hshi,hwpos] with t htlo hthi htw
    exact preferred_global_one_sided_inverse t w δ hδ hδπ htlo hthi hθlo hθhi htw
  let L := fderiv ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,χ s)
  have hd := hU.differentiableAt.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk hχ.differentiableAt.hasDerivAt)
  have hz : L (1,deriv χ s)=0 :=
    (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const s w)
  have hdot : L (1,0)=preferredSourceUDot s (χ s) := by
    have hh := hU.differentiableAt.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s (χ s)))
    simpa only [preferredSourceUDot,Function.comp_def,id_eq] using hh.deriv.symm
  have hq : L (0,1)=preferredSourceUQ s (χ s) := by
    have hh := hU.differentiableAt.hasFDerivAt.comp_hasDerivAt (χ s)
      ((hasDerivAt_const (χ s) s).prodMk (hasDerivAt_id (χ s)))
    simpa only [preferredSourceUQ,Function.comp_def] using hh.deriv.symm
  have he : (1,deriv χ s)=(1,0)+(deriv χ s) • ((0,1):ℂ × ℂ) := by ext <;> simp
  rw [he,map_add,map_smul,hdot,hq,smul_eq_mul] at hz
  have hqn : preferredSourceUQ s (χ s)≠0 :=
    (preferred_global_one_sided_q_regular s w δ hδ hδπ hS hSδ hθlo hθhi hW).2
  have hder : deriv χ s= -preferredSourceUDot s (χ s)/preferredSourceUQ s (χ s) := by
    apply (eq_div_iff hqn).mpr
    linear_combination hz
  change HasDerivAt χ (-preferredSourceUDot s (χ s)/preferredSourceUQ s (χ s)) s
  rw [← hder]
  exact hχ.differentiableAt.hasDerivAt

theorem preferredSourceCoordinate_parameter_hasDerivAt {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (i : Fin N)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSi : 0<(temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    HasDerivAt (fun t : ℂ => preferredSourceCoordinate τ p m t θ i)
      (-preferredSourceUDot s (preferredSourceCoordinate τ p m s θ i)/
        preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)) s := by
  have hwre : (deformedAngles τ p m θ i).re=θ i := by simp [deformedAngles,Complex.mul_re]
  exact preferred_forward_parameter_hasDerivAt s (deformedAngles τ p m θ i) δ hδ hδπ hS hSi hSδ
    (by rw [hwre]; exact hθ.1) (by rw [hwre]; exact hθ.2) hW

/-- The actual complex angular Jacobian is nonsingular everywhere in the
source one-sided regular regime once the complete occupancy M is invertible. -/
theorem preferredSourceJacobian_det_ne_zero {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hM : (preferredContourMatrix τ p m θ).det≠0) :
    (preferredSourceJacobian τ p m s θ).det≠0 := by
  rw [preferredSourceJacobian_det τ δ p m hp hm s θ hδ hδπ hS hSδ hθ hW]
  unfold preferredCoordinateJacobian
  apply mul_ne_zero hM
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have hwre : (deformedAngles τ p m θ i).re=θ i := by simp [deformedAngles,Complex.mul_re]
  exact inv_ne_zero (preferred_global_one_sided_q_regular s (deformedAngles τ p m θ i) δ
    hδ hδπ hS hSδ (by rw [hwre]; exact (hθ i).1) (by rw [hwre]; exact (hθ i).2) (hW i)).2

/-- Every actual regular-coordinate frame differentiates the source q map
as the canonical coordinate derivative. The calculation is on real angles. -/
theorem preferredCoordinateFrame_sourceCoordinate {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (a b : Fin N) (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hM : (preferredContourMatrix τ p m θ).det≠0) :
    preferredCoordinateFrame τ p m a (fun t x => preferredSourceCoordinate τ p m t x b) s θ =
      if b=a then 1 else 0 := by
  rw [preferredCoordinateFrame_eq_inverse_jacobian τ δ p m hp hm s θ a _ hδ hδπ hS hSδ hθ hW]
  have hA := preferredSourceJacobian_det_ne_zero τ δ p m hp hm s θ hδ hδπ hS hSδ hθ hW hM
  have hh := congrArg (fun A : Matrix (Fin N) (Fin N) ℂ => A b a)
    (Matrix.mul_nonsing_inv (preferredSourceJacobian τ p m s θ) (isUnit_iff_ne_zero.mpr hA))
  simpa only [Matrix.mul_apply,Matrix.one_apply,preferredSourceJacobian,mul_comm] using hh

/-- The actual fixed-q parameter frame annihilates every source q
coordinate, using the proved complex parameter derivative and real Jacobian. -/
theorem preferredParameterFrame_sourceCoordinate {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (b : Fin N) (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSi : 0<(temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hM : (preferredContourMatrix τ p m θ).det≠0) :
    preferredParameterFrame τ p m (fun t x => preferredSourceCoordinate τ p m t x b) s θ=0 := by
  unfold preferredParameterFrame
  rw [(preferredSourceCoordinate_parameter_hasDerivAt τ δ p m s θ b hδ hδπ hS hSi hSδ (hθ b) (hW b)).deriv]
  simp_rw [(preferredSourceCoordinate_hasDerivAt τ δ p m hp hm s θ b _ hδ hδπ hS hSδ (hθ b) (hW b)).deriv]
  let M := preferredContourMatrix τ p m θ
  let u := fun a => preferredSourceUDot s (preferredSourceCoordinate τ p m s θ a)
  let v := preferredSourceUQ s (preferredSourceCoordinate τ p m s θ b)
  have he : (∑ i, (M⁻¹.mulVec u) i*(v⁻¹*M b i))=v⁻¹*u b := by
    calc
      _ = v⁻¹*(M.mulVec (M⁻¹.mulVec u)) b := by
        simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM),Matrix.one_mulVec]
  change -u b/v+(∑ i, (M⁻¹.mulVec u) i*(v⁻¹*M b i))=0
  rw [he]
  ring

/-- The regular scalar generator on the original real angular domain.
Real cutoff derivatives remain in G; no complex cutoff continuation is used.
This is the operator in (7.9) after J and the frozen product-phase quotient
have been factored out. -/
def preferredRegularTransportStep {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (G : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  preferredParameterFrame τ p m G s θ +
    (∑ a, preferredResidualCollective s (preferredSourceCoordinate τ p m s θ) a *
      preferredCoordinateFrame τ p m a G s θ) +
    (∑ a, preferredCoordinateFrame τ p m a
      (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) a) s θ) * G s θ

/-- The literal frame operator is the material derivative plus the genuine
regular divergence; this algebra introduces no inverse Uq factors. -/
theorem preferredRegularTransportStep_eq {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (G : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) :
    preferredRegularTransportStep τ p m G s θ =
      deriv (fun t => G t θ) s -
        (∑ i, preferredSourceAngularField .right τ p m s θ i *
          deriv (fun x : ℝ => G s (Function.update θ i x)) (θ i)) +
      (∑ a, preferredCoordinateFrame τ p m a
        (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) a) s θ) * G s θ := by
  let M := preferredContourMatrix τ p m θ
  let u := fun a => preferredSourceUDot s (preferredSourceCoordinate τ p m s θ a)
  let v := fun a => preferredSourceUQ s (preferredSourceCoordinate τ p m s θ a)
  let B := preferredResidualCollective s (preferredSourceCoordinate τ p m s θ)
  let g := fun i => deriv (fun x : ℝ => G s (Function.update θ i x)) (θ i)
  have hb : (∑ a, B a*(∑ i, M⁻¹ i a*v a*g i)) =
      ∑ i, (M⁻¹.mulVec (fun a => v a*B a)) i*g i := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold preferredRegularTransportStep
  congr 1
  change deriv (fun t => G t θ) s+(∑ i, (M⁻¹.mulVec u) i*g i)+
    (∑ a, B a*(∑ i, M⁻¹ i a*v a*g i)) =
      deriv (fun t => G t θ) s-(∑ i, -(M⁻¹.mulVec (fun a => u a+v a*B a)) i*g i)
  rw [hb]
  change deriv (fun t => G t θ) s+(∑ i, (M⁻¹.mulVec u) i*g i)+
    (∑ i, (M⁻¹.mulVec (fun a => v a*B a)) i*g i) =
      deriv (fun t => G t θ) s-(∑ i, -(M⁻¹.mulVec (u+(fun a => v a*B a))) i*g i)
  simp only [Matrix.mulVec_add,Pi.add_apply,neg_mul,Finset.sum_neg_distrib,sub_neg_eq_add,
    add_mul,Finset.sum_add_distrib]
  ring

/-- Actual initial regular scalar, including the original smooth cell weight
and constrained Haar normalization, with J and the product-phase quotient
removed only by the proved seed normalization identity. -/
def preferredRegularSeed {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (preferredCellWeight .right η p m r θ:ℂ) *
    (preferredRegularKernel s (preferredSourceCoordinate τ p m s θ)).det *
    (∏ i, preferredRegularOneBody s (preferredSourceCoordinate τ p m s θ i)) /
    ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))

/-- The concrete factored scalar descendants for finite marked-minor
induction. Identification with preferredTransportedDensity requires the
actual coordinate Piola and phase-freezing identities, kept explicit. -/
def preferredRegularTransportedScalar {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ) :
    ℕ → ℂ → (Fin N → ℝ) → ℂ
  | 0 => preferredRegularSeed τ η p m r
  | j+1 => preferredRegularTransportStep τ p m (preferredRegularTransportedScalar τ η p m r j)

/-- The actual physical phase is reconstructed algebraically from the
source q coordinate, retaining its moving center. -/
theorem preferredSourcePhase_coordinate_identity {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) :
    preferredSourcePhase τ p m s θ i=
      preferredSourceCoordinate τ p m s θ i-deformedAngles τ p m θ i+preferredMovingBranch s := by
  unfold preferredSourceCoordinate
  ring

theorem preferredSourcePhase_parameter_hasDerivAt {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (i : Fin N)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSi : 0<(temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    HasDerivAt (fun t : ℂ => preferredSourcePhase τ p m t θ i)
      (-preferredSourceUDot s (preferredSourceCoordinate τ p m s θ i)/
        preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)+deriv preferredMovingBranch s) s := by
  have hq := preferredSourceCoordinate_parameter_hasDerivAt τ δ p m s θ i hδ hδπ hS hSi hSδ hθ hW
  have hb := (preferredMovingBranch_analyticAt_upper s hSi).differentiableAt.hasDerivAt
  have hh := (hq.sub_const (deformedAngles τ p m θ i)).add hb
  convert! hh using 1
  funext t
  exact preferredSourcePhase_coordinate_identity τ p m t θ i

theorem preferredSourcePhase_angular_hasDerivAt {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (i j : Fin N)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    HasDerivAt (fun x : ℝ => preferredSourcePhase τ p m s (Function.update θ j x) i)
      (((preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i))⁻¹-1)*
        preferredContourMatrix τ p m θ i j) (θ j) := by
  have hq := preferredSourceCoordinate_hasDerivAt τ δ p m hp hm s θ i j hδ hδπ hS hSδ hθ hW
  have hw := preferred_deformedAngle_hasDerivAt τ p m hp hm θ i j
  have hh := (hq.sub hw).add_const (preferredMovingBranch s)
  convert! hh using 1
  · funext x
    exact preferredSourcePhase_coordinate_identity τ p m s (Function.update θ j x) i
  · ring

/-- Exact matrix cancellation underlying source phase freezing. The
inverse in this identity is the full coupled occupancy matrix. -/
theorem preferred_material_phase_algebra {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (u v B : Fin N → ℂ) (b : ℂ) (hM : M.det≠0) (hv : ∀ i, v i≠0)
    (hangle : (∑ i, v i*B i)=-(∑ i, u i))
    (hphase : (∑ i, B i)=-(N:ℂ)*b) :
    (∑ i, (-u i/v i+b))-
      (∑ j, preferredAngularRepresentative M u v B j * (∑ i, ((v i)⁻¹-1)*M i j))=0 := by
  let V := preferredAngularRepresentative M u v B
  have hMV (i : Fin N) : (∑ j, M i j*V j)=-(u i+v i*B i) := by
    change (M.mulVec (-(M⁻¹.mulVec (fun a => u a+v a*B a)))) i=-(u i+v i*B i)
    rw [Matrix.mulVec_neg,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec]
    rfl
  have hsum : (∑ j, V j*(∑ i, ((v i)⁻¹-1)*M i j))=
      ∑ i, ((v i)⁻¹-1)*(-(u i+v i*B i)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = ((v i)⁻¹-1)*(∑ j, M i j*V j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hMV]
  change (∑ i, (-u i/v i+b))-(∑ j, V j*(∑ i, ((v i)⁻¹-1)*M i j))=0
  rw [hsum,← Finset.sum_sub_distrib]
  calc
    _ = ∑ i, ((1-v i)*B i-u i+b) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hv i]
      ring
    _ = 0 := movingPhase_transport_zero u v B b hangle (by simpa using hphase)

def preferredSourcePhaseSum {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  ∑ i, preferredSourcePhase τ p m s θ i

/-- The actual complete phase sum is frozen by the literal angular field,
using true complex parameter and real angular derivatives. -/
theorem preferredSourcePhaseSum_material_freeze {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSi : 0<(temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hM : (preferredContourMatrix τ p m θ).det≠0)
    (hc : ∀ i j,
      preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)=
        preferredSourceUQ s (preferredSourceCoordinate τ p m s θ j) →
      preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i)=
        preferredMovingInverse s (preferredSourceCoordinate τ p m s θ j))
    (hR : collectiveDenominator (fun i => preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i))≠0) :
    deriv (fun t : ℂ => preferredSourcePhaseSum τ p m t θ) s-
      (∑ j, preferredSourceAngularField .right τ p m s θ j *
        deriv (fun x : ℝ => preferredSourcePhaseSum τ p m s (Function.update θ j x)) (θ j))=0 := by
  let q := preferredSourceCoordinate τ p m s θ
  let u := fun i => preferredSourceUDot s (q i)
  let v := fun i => preferredSourceUQ s (q i)
  let B := preferredResidualCollective s q
  have hv (i : Fin N) : v i≠0 := by
    have hwre : (deformedAngles τ p m θ i).re=θ i := by simp [deformedAngles,Complex.mul_re]
    exact (preferred_global_one_sided_q_regular s (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
      (by rw [hwre]; exact (hθ i).1) (by rw [hwre]; exact (hθ i).2) (hW i)).2
  obtain ⟨hphase,hangle⟩ := preferredResidualCollective_constraints s q hc hR
  have hparam : HasDerivAt (fun t : ℂ => preferredSourcePhaseSum τ p m t θ)
      (∑ i, (-u i/v i+deriv preferredMovingBranch s)) s := by
    simpa only [preferredSourcePhaseSum,Finset.sum_fn] using
      HasDerivAt.sum (u := Finset.univ) (fun i _ =>
        preferredSourcePhase_parameter_hasDerivAt τ δ p m s θ i hδ hδπ hS hSi hSδ (hθ i) (hW i))
  have hang (j : Fin N) : HasDerivAt
      (fun x : ℝ => preferredSourcePhaseSum τ p m s (Function.update θ j x))
      (∑ i, ((v i)⁻¹-1)*preferredContourMatrix τ p m θ i j) (θ j) := by
    simpa only [preferredSourcePhaseSum,Finset.sum_fn] using
      HasDerivAt.sum (u := Finset.univ) (fun i _ =>
        preferredSourcePhase_angular_hasDerivAt τ δ p m hp hm s θ i j hδ hδπ hS hSδ (hθ i) (hW i))
  rw [hparam.deriv]
  simp_rw [(hang _).deriv]
  exact preferred_material_phase_algebra (preferredContourMatrix τ p m θ) u v B
    (deriv preferredMovingBranch s) hM hv hangle hphase

end
end IsingBulk.Preferred22
