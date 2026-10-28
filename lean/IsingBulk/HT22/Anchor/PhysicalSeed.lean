import IsingBulk.HT22.Anchor.FixedCoordinate
import IsingBulk.HT22.Physical.ContourDensity
namespace IsingBulk.HT22.Anchor
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry IsingBulk.HT22.Tail
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Actual complete bordered density for any original angular weight. -/
def physicalSeed {N : ℕ} (σ : ℂ) (τ : ℝ) (p m : ℝ → ℝ)
    (weight : ℂ) (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  let w := deformedAngles τ p m θ
  let z := fun i => physicalRoot (temperatureTrace t-Complex.cos (w i))
  let y := fun i => Complex.exp (Complex.I*w i)
  let Z := ∏ i,z i
  weight*(preferredContourMatrix τ p m θ).det *
    ((1+σ*Z)/(1-σ*Z))*(Algebra.constantBorderFirst y z).det *
    (∏ i,oneBody (z i))/((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))

theorem physicalSeed_eq_fixedAmplitude {N : ℕ} (σ : ℂ)
    (τ δ : ℝ) (p m : ℝ → ℝ) (weight : ℂ) (t : ℂ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace t).re) (hSδ : (temperatureTrace t).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace t-Complex.cos (deformedAngles τ p m θ i)).im) :
    physicalSeed σ τ p m weight t θ =
      weight*coordinateJacobian τ p m t θ*fixedAmplitude σ t (sourceCoordinate τ p m t θ) := by
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
  have hUv (i : Fin N) : Tail.inverseV t (v i) ≠ 0 := by
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
      (∏ i, Tail.inverseV t (v i))*(∏ i, (Complex.sinh (Complex.I*φ i))⁻¹) := by
    simp only [regularOneBody,hφ,div_eq_mul_inv,Finset.prod_mul_distrib]
  have hu : (∏ i, (Tail.inverseV t (v i))⁻¹)*(∏ i, Tail.inverseV t (v i))=1 := by
    rw [←Finset.prod_mul_distrib]
    simp only [inv_mul_cancel₀ (hUv _),Finset.prod_const_one]
  unfold physicalSeed
  change weight*(preferredContourMatrix τ p m θ).det*
    ((1+σ*∏ i,physicalRoot (temperatureTrace t-Complex.cos (w i)))/
      (1-σ*∏ i,physicalRoot (temperatureTrace t-Complex.cos (w i))))*
    (Algebra.constantBorderFirst (fun i=>Complex.exp (Complex.I*w i))
      (fun i=>physicalRoot (temperatureTrace t-Complex.cos (w i)))).det*
    (∏ i,oneBody (physicalRoot (temperatureTrace t-Complex.cos (w i))))/_ = _
  rw [hK]
  simp_rw [hz,oneBody_exp_phase]
  rw [hZ]
  unfold coordinateJacobian fixedAmplitude
  change _ = weight*((preferredContourMatrix τ p m θ).det*(∏ i,(Tail.inverseV t (v i))⁻¹))*
    (((1+σ*regularProductPhase t v)/(1-σ*regularProductPhase t v))*
      (sourceBorderedKernel τ p m t θ).det*(∏ i,regularOneBody t (v i))/_)
  rw [ha]
  calc
    _ = ((∏ i,(Tail.inverseV t (v i))⁻¹)*(∏ i,Tail.inverseV t (v i)))*
      (weight*(preferredContourMatrix τ p m θ).det*
        ((1+σ*regularProductPhase t v)/(1-σ*regularProductPhase t v))*
        (sourceBorderedKernel τ p m t θ).det*(∏ i,(Complex.sinh (Complex.I*φ i))⁻¹)/
        ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))) := by rw [hu,one_mul]
    _ = _ := by ring

/-- The exact odd physical weighted contour integrand is the anchor seed. -/
theorem weighted_bareContourDensity_eq_seed (negative : Bool) (n : ℕ)
    (τ : ℝ) (p m : ℝ → ℝ) (weight : ℂ) (t : ℂ) (θ : Fin (2*n+1) → ℝ)
    (hW : ∀ i,0<(temperatureTrace t-Complex.cos (deformedAngles τ p m θ i)).im) :
    weight*Physical.bareContourDensity negative τ p m t θ=
      physicalSeed (Physical.constraintSign negative) τ p m weight t θ := by
  rw [Physical.bareContourDensity_eq_bordered negative n τ p m t θ hW]
  simp only [physicalSeed,Nat.add_sub_cancel,Physical.oneBody_eq_rational,Preferred22.oneBody]
  ring

/-- Every actual anchor cell has the true signed bordered normalized amplitude,
with its weight left on the original real angles and full ambient Jacobian. -/
theorem weighted_bareContourDensity_eq_fixedAmplitude (negative : Bool) (n : ℕ)
    (τ δ : ℝ) (p m : ℝ → ℝ) (weight : ℂ) (t : ℂ) (θ : Fin (2*n+1) → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace t).re) (hSδ : (temperatureTrace t).re<2*Real.cos δ)
    (hθ : ∀ i,θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i,0<(temperatureTrace t-Complex.cos (deformedAngles τ p m θ i)).im) :
    weight*Physical.bareContourDensity negative τ p m t θ=
      weight*coordinateJacobian τ p m t θ*
        fixedAmplitude (Physical.constraintSign negative) t (sourceCoordinate τ p m t θ) := by
  rw [weighted_bareContourDensity_eq_seed negative n τ p m weight t θ hW]
  exact physicalSeed_eq_fixedAmplitude _ τ δ p m weight t θ hδ hδπ hS hSδ hθ hW

end
end IsingBulk.HT22.Anchor
