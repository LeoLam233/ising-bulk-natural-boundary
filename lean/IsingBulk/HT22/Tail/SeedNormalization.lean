import IsingBulk.HT22.Tail.ScalarTransport
import IsingBulk.Preferred22.ComplexKernelBridge
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Exact normalization of the HT22 source scalar

This is the zeroth-order physical-to-regular identity with the actual odd
border, the signed resolvent and all occupancy Jacobian factors retained.
-/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry
open scoped BigOperators

/-- The coordinate derivative is unchanged under a fixed-t translation.
This is not a claim about the fixed-coordinate parameter derivative. -/
theorem inverseV_moving_adapter (t v : ℂ) :
    inverseV t v = preferredSourceUQ t (v-preferredMovingBranch t) := by
  have he : regularInverse t = fun q => preferredMovingInverse t (q-preferredMovingBranch t) :=
    funext (regularInverse_moving_adapter t)
  rw [inverseV,Geometry.inverseV,he,deriv_comp_sub_const]
  rfl

theorem sourceCoordinate_moving_adapter {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) (i : Fin N) :
    sourceCoordinate τ p m t θ i-preferredMovingBranch t = preferredSourceCoordinate τ p m t θ i := by
  unfold sourceCoordinate sumCoordinate physicalPhase preferredSourceCoordinate preferredSourcePhase
  ring

/-- Primitive positive-epsilon geometry gives the complete normalization;
no density estimate, contour equality or tail premise appears in this type. -/
theorem physicalSeed_eq_reconstructed_zero {N : ℕ} (σ : ℂ)
    (τ δ : ℝ) (η p m r : ℝ → ℝ) (t : ℂ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace t).re) (hSδ : (temperatureTrace t).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace t-Complex.cos (deformedAngles τ p m θ i)).im) :
    physicalSeed σ τ η p m r t θ = reconstructedDensity σ τ η p m r 0 t θ := by
  let v := sourceCoordinate τ p m t θ
  let w := deformedAngles τ p m θ
  let φ := fun i => physicalPhase t (w i)
  have hwre (i : Fin N) : (w i).re=θ i := by simp [w,deformedAngles,Complex.mul_re]
  have hU (i : Fin N) : regularInverse t (v i)=w i := by
    apply global_one_sided_inverse t (w i) δ hδ hδπ hS hSδ
    · rw [hwre]; exact (hθ i).1
    · rw [hwre]; exact (hθ i).2
    · exact hW i
  have hφ (i : Fin N) : regularPhase t (v i)=φ i := by
    unfold regularPhase
    rw [hU]
    change sumCoordinate t (w i)-w i=physicalPhase t (w i)
    simp only [sumCoordinate,add_sub_cancel_left]
  have hz (i : Fin N) : physicalRoot (temperatureTrace t-Complex.cos (w i))=
      Complex.exp (-Complex.I*φ i) := (physicalPhase_root t (w i) (hW i)).symm
  have hZ : (∏ i, Complex.exp (-Complex.I*φ i))=regularProductPhase t v := by
    rw [←Complex.exp_sum]
    unfold regularProductPhase
    simp_rw [hφ]
    congr 1
    rw [Finset.mul_sum]
  have hUv (i : Fin N) : inverseV t (v i) ≠ 0 := by
    rw [inverseV_moving_adapter,sourceCoordinate_moving_adapter]
    exact (preferred_global_one_sided_q_regular t (w i) δ hδ hδπ hS hSδ
      (by rw [hwre]; exact (hθ i).1) (by rw [hwre]; exact (hθ i).2) (hW i)).2
  have hK : Algebra.constantBorderFirst (fun i => Complex.exp (Complex.I*w i))
      (fun i => physicalRoot (temperatureTrace t-Complex.cos (w i)))=
      sourceBorderedKernel τ p m t θ := by
    change Algebra.constantBorderFirst (fun i => Complex.exp (Complex.I*w i))
      (fun i => physicalRoot (temperatureTrace t-Complex.cos (w i)))=
      Algebra.constantBorderFirst (fun i => Complex.exp (Complex.I*regularInverse t (v i)))
        (fun i => Complex.exp (-Complex.I*regularPhase t (v i)))
    simp_rw [hU,hφ,hz]
  have ha : (∏ i, regularOneBody t (v i))=
      (∏ i, inverseV t (v i))*(∏ i, (Complex.sinh (Complex.I*φ i))⁻¹) := by
    simp only [regularOneBody,hφ,div_eq_mul_inv,Finset.prod_mul_distrib]
  have hu : (∏ i, (inverseV t (v i))⁻¹)*(∏ i, inverseV t (v i))=1 := by
    rw [←Finset.prod_mul_distrib]
    simp only [inv_mul_cancel₀ (hUv _),Finset.prod_const_one]
  unfold physicalSeed
  change (preferredCellWeight .right η p m r θ:ℂ)*(preferredContourMatrix τ p m θ).det*
    ((1+σ*∏ i,physicalRoot (temperatureTrace t-Complex.cos (w i)))/
      (1-σ*∏ i,physicalRoot (temperatureTrace t-Complex.cos (w i))))*
    (Algebra.constantBorderFirst (fun i=>Complex.exp (Complex.I*w i))
      (fun i=>physicalRoot (temperatureTrace t-Complex.cos (w i)))).det*
    (∏ i,oneBody (physicalRoot (temperatureTrace t-Complex.cos (w i))))/_ = _
  rw [hK]
  simp_rw [hz,oneBody_exp_phase]
  rw [hZ]
  unfold reconstructedDensity coordinateJacobian regularTransportedScalar regularSeed regularSeedCoefficient
  change _ = ((preferredContourMatrix τ p m θ).det*(∏ i,(inverseV t (v i))⁻¹))*
    ((1+σ*regularProductPhase t v)/(1-σ*regularProductPhase t v))*
    (((preferredCellWeight .right η p m r θ:ℂ)*(∏ i,regularOneBody t (v i))/_)*
      (sourceBorderedKernel τ p m t θ).det)
  rw [ha]
  calc
    _ = ((∏ i,(inverseV t (v i))⁻¹)*(∏ i,inverseV t (v i)))*
      ((preferredCellWeight .right η p m r θ:ℂ)*(preferredContourMatrix τ p m θ).det*
        ((1+σ*regularProductPhase t v)/(1-σ*regularProductPhase t v))*
        (sourceBorderedKernel τ p m t θ).det*(∏ i,(Complex.sinh (Complex.I*φ i))⁻¹)/
        ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))) := by rw [hu,one_mul]
    _ = _ := by ring

end
end IsingBulk.HT22.Tail
