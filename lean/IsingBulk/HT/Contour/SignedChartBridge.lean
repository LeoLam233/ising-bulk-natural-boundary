import IsingBulk.HT.Contour.SignedRetraction
import IsingBulk.Tail.MicrocoreDensity

/-! Exact original-branch chart correspondence for the signed physical
reduced angular density. No Vandermonde is canceled by division. -/
namespace IsingBulk.HT.Contour
noncomputable section
open Set MeasureTheory
open IsingBulk.First IsingBulk.Tail IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie
open scoped BigOperators

/-- Literal signed source density including the normalized angular measure,
but excluding the single outside factorial. -/
def signedSourceAngularDensity {N : ℕ} (σ : ℂ) (r : ℝ) (s : ℂ)
    (x : Fin N → ℝ) : ℂ :=
  angleProductJacobian r x * signedCanceledDensity σ
    (fun i => globalRoot s (anglePoint r (x i))) (angleTuple r x)

/-- Signed product kernels do not change the exact angular periodicity. -/
theorem signedSourceAngularDensity_periodic (N : ℕ) (σ : ℂ) (r : ℝ) (s : ℂ) :
    CoordinatePeriodic N (signedSourceAngularDensity σ r s) := by
  intro x i
  have he : (fun j => globalRoot s (anglePoint r (Function.update x i (x i+2*Real.pi) j))) =
      (fun j => globalRoot s (anglePoint r (x j))) := by
    funext j
    exact congrArg (globalRoot s) (congrFun (angleTuple_update_period r x i) j)
  simp only [signedSourceAngularDensity,angleProductJacobian_update_period,
    angleTuple_update_period,he]

def signedMicroRegularDensity {N : ℕ} (σ s : ℂ) (φ : Fin N → ℂ) : ℂ :=
  signedGlobalFactor σ (regularZProduct s φ) (regularYProduct s φ)*
    microRegularPairProduct s φ*∏ i,microRegularOneBody s (φ i)

theorem signedMicroRegularDensity_unfactored {N : ℕ} (σ s : ℂ) (φ : Fin N → ℂ) :
    signedMicroRegularDensity σ s φ =
      microcoreVandermondeSquared φ*microRegularAmplitude s φ/
        ((1-σ*regularYProduct s φ)*(1-σ*regularZProduct s φ)) := by
  have hp : microRegularPairProduct s φ = microcoreVandermondeSquared φ*
      (∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j),regularPairCoefficient s (φ i) (φ j)) := by
    unfold microRegularPairProduct microcoreVandermondeSquared branchCompletePair
    simp_rw [Finset.prod_mul_distrib]
  rw [signedMicroRegularDensity,hp]
  unfold signedGlobalFactor microRegularAmplitude
  ring

 theorem signed_micro_regular_density_source (σ : ℂ) {n : ℕ} (s : ℂ) (v θ : ℝ)
    (x : AngularSpace n) (hv : v < 0)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im) :
    chartPullback v θ (signedMicroRegularDensity (N := n+1) σ) s x =
      signedCanceledDensity σ (fun i => globalRoot s (angularY v θ (x i)))
        (fun i => angularY v θ (x i))*∏ i, angularY v θ (x i)/(2*(Real.pi:ℂ)) := by
  have hy : regularYProduct s (chartMap v θ s x)=coordinateProduct (fun i => angularY v θ (x i)) := by
    unfold regularYProduct coordinateProduct
    apply Finset.prod_congr rfl
    intro i _
    exact regularY_chartPhase s v θ (x i) (hg i)
  have hz : regularZProduct s (chartMap v θ s x)=
      coordinateProduct (fun i => globalRoot s (angularY v θ (x i))) := by
    rw [regularZProduct_eq_prod]
    unfold coordinateProduct
    apply Finset.prod_congr rfl
    intro i _
    exact (chart_root_eq_physical s v θ (x i)).symm
  have hp := micro_regular_pair_product_source s v θ x hv hg hi
  have hbody := micro_regular_onebody_product_source s v θ x hv hg hi
  change chartJacobian v θ s x*signedMicroRegularDensity σ s (chartMap v θ s x)=_
  rw [signedMicroRegularDensity,signedGlobalFactor,hy,hz,hp]
  unfold signedCanceledDensity signedGlobalFactor
  calc
    _ = ((coordinateProduct (fun i => globalRoot s (angularY v θ (x i))))⁻¹+
      (coordinateProduct (fun i => angularY v θ (x i)))⁻¹)/
      ((1-σ*coordinateProduct (fun i => globalRoot s (angularY v θ (x i))))*
        (1-σ*coordinateProduct (fun i => angularY v θ (x i))))*
      canceledPairProduct (fun i => globalRoot s (angularY v θ (x i))) (fun i => angularY v θ (x i))*
      (chartJacobian v θ s x*∏ i, microRegularOneBody s (chartPhase s v θ (x i))) := by simp only [chartMap]; ring
    _ = _ := by rw [hbody]; ring


/-- The signed chart keeps the same physical roots, pair product, one-body
measure and fixed real cutoff as the actual source contour. -/
theorem signed_micro_original_density_regular {n : ℕ} (σ s : ℂ) (v θ : ℝ)
    (x : AngularSpace n) (hv : v < 0)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im) :
    chartPullback v θ (signedMicroRegularDensity (N := n+1) σ) s x =
      signedSourceAngularDensity σ (Real.exp v) s (fun i => x i-θ) := by
  rw [signed_micro_regular_density_source σ s v θ x hv hg hi]
  unfold signedSourceAngularDensity angleProductJacobian angleJacobian angleTuple
  simp_rw [anglePoint_eq_angularY]
  ring

/-- Exact factorial attachment of the signed angular source. -/
theorem signedSourceIntegral_eq_angular (σ : ℂ) (N : ℕ) (r : ℝ) (s : ℂ) :
    signedSourceIntegral σ N r s =
      (N.factorial:ℂ)⁻¹ * ∫ x in angleBox N,signedSourceAngularDensity σ r s x := by
  unfold signedSourceIntegral signedSourceAngularDensity
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro x _
  ring

end
end IsingBulk.HT.Contour
