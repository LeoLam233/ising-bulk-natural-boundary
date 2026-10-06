import IsingBulk.Tail.MicrocoreDensityFactors
import IsingBulk.Tail.SelectorOriginal
import IsingBulk.First.SourceAngularPeriodicity

/-! Exact actual-source density in the regular microcore chart. Normalized
one-body measures and the complete pair product are retained. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie
open scoped BigOperators

def microRegularPairProduct {N : ℕ} (s : ℂ) (φ : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j), branchCompletePair (s,φ i,φ j)

def microRegularDensity {N : ℕ} (s : ℂ) (φ : Fin N → ℂ) : ℂ :=
  ((regularZProduct s φ)⁻¹+(regularYProduct s φ)⁻¹)/
    ((1-regularZProduct s φ)*(1-regularYProduct s φ))*
    microRegularPairProduct s φ*∏ i, microRegularOneBody s (φ i)

def microRegularAmplitude {N : ℕ} (s : ℂ) (φ : Fin N → ℂ) : ℂ :=
  ((regularZProduct s φ)⁻¹+(regularYProduct s φ)⁻¹)*
    (∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j), regularPairCoefficient s (φ i) (φ j))*
    ∏ i, microRegularOneBody s (φ i)

 theorem microRegularDensity_unfactored {N : ℕ} (s : ℂ) (φ : Fin N → ℂ) :
    microRegularDensity s φ =
      microcoreVandermondeSquared φ*microRegularAmplitude s φ/regularKernel s φ := by
  have hp : microRegularPairProduct s φ = microcoreVandermondeSquared φ*
      (∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j), regularPairCoefficient s (φ i) (φ j)) := by
    unfold microRegularPairProduct microcoreVandermondeSquared branchCompletePair
    simp_rw [Finset.prod_mul_distrib]
  rw [microRegularDensity,hp]
  unfold microRegularAmplitude regularKernel
  ring

 theorem regularZProduct_eq_prod {N : ℕ} (s : ℂ) (φ : Fin N → ℂ) :
    regularZProduct s φ=∏ i, Complex.exp (-Complex.I*φ i) := by
  rw [regularZProduct,Finset.mul_sum,Complex.exp_sum]

 theorem micro_regular_pair_product_source {n : ℕ} (s : ℂ) (v θ : ℝ)
    (x : AngularSpace n) (hv : v < 0)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im) :
    microRegularPairProduct s (chartMap v θ s x) =
      canceledPairProduct (fun i => globalRoot s (angularY v θ (x i)))
        (fun i => angularY v θ (x i)) := by
  unfold microRegularPairProduct canceledPairProduct
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  exact micro_regular_pair_source s v θ (x i) (x j) hv (hg i) (hg j) (hi i) (hi j)

 theorem micro_regular_onebody_product_source {n : ℕ} (s : ℂ) (v θ : ℝ)
    (x : AngularSpace n) (hv : v < 0)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im) :
    chartJacobian v θ s x*(∏ i, microRegularOneBody s (chartPhase s v θ (x i))) =
      (∏ i, residueFactor (globalRoot s (angularY v θ (x i))))*
        ∏ i, angularY v θ (x i)/(2*(Real.pi:ℂ)) := by
  unfold chartJacobian
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [micro_original_onebody_source s v θ (x i) hv (hg i) (hi i)]
  ring

 theorem micro_regular_density_source {n : ℕ} (s : ℂ) (v θ : ℝ)
    (x : AngularSpace n) (hv : v < 0)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im) :
    chartPullback v θ (@microRegularDensity (n+1)) s x =
      canceledReducedDensity (fun i => globalRoot s (angularY v θ (x i)))
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
  change chartJacobian v θ s x*microRegularDensity s (chartMap v θ s x)=_
  rw [microRegularDensity,hy,hz,hp]
  unfold canceledReducedDensity
  calc
    _ = ((coordinateProduct (fun i => globalRoot s (angularY v θ (x i))))⁻¹+
      (coordinateProduct (fun i => angularY v θ (x i)))⁻¹)/
      ((1-coordinateProduct (fun i => globalRoot s (angularY v θ (x i))))*
        (1-coordinateProduct (fun i => angularY v θ (x i))))*
      canceledPairProduct (fun i => globalRoot s (angularY v θ (x i))) (fun i => angularY v θ (x i))*
      (chartJacobian v θ s x*∏ i, microRegularOneBody s (chartPhase s v θ (x i))) := by simp only [chartMap]; ring
    _ = _ := by rw [hbody]; ring

 theorem anglePoint_eq_angularY (v θ u : ℝ) :
    anglePoint (Real.exp v) (u-θ)=angularY v θ (u:ℂ) := by
  unfold anglePoint circleMap angularY
  rw [Complex.exp_add,Complex.ofReal_exp]
  simp

/-- Complete original reduced density with its actual normalized angular
measure, not an independently declared model integrand. -/
 theorem micro_original_density_regular {n : ℕ} (s : ℂ) (v θ : ℝ)
    (x : AngularSpace n) (hv : v < 0)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im) :
    chartPullback v θ (@microRegularDensity (n+1)) s x =
      sourceReducedAngularDensity (Real.exp v) s (fun i => x i-θ) := by
  let y : Fin (n+1) → ℂ := fun i => angularY v θ (x i)
  let z : Fin (n+1) → ℂ := fun i => globalRoot s (y i)
  have hy0 : ∀ i, y i ≠ 0 := fun _ => Complex.exp_ne_zero _
  have hz0 : ∀ i, z i ≠ 0 := fun _ => globalRoot_nonzero _ _
  have hy : ∀ i, ‖y i‖ < 1 := by
    intro i
    rw [show y i=angularY v θ (x i) from rfl,angularY_norm_real,Real.exp_lt_one_iff]
    exact hv
  have hz : ∀ i, ‖z i‖ < 1 := fun i => interiorRoot_norm_lt_one (hi i)
  have hroot : ∀ i, (z i)^2-(2*IsingBulk.First.sourceS s-y i-(y i)⁻¹)*z i+1=0 :=
    fun i => globalRoot_quadratic s (y i)
  have hp := canceledPairProduct_eq s z y hy0 hz0 hroot
    (fun i j => one_sub_mul_ne_zero_of_norm_lt_one (hy i) (hy j))
    (fun i j => one_sub_mul_ne_zero_of_norm_lt_one (hz i) (hz j))
  have hc : canceledReducedDensity z y=reducedDensity z y := by
    unfold canceledReducedDensity reducedDensity
    rw [hp]
    ring
  rw [micro_regular_density_source s v θ x hv hg hi]
  change canceledReducedDensity z y*(∏ i, y i/(2*(Real.pi:ℂ)))=_
  rw [hc]
  unfold sourceReducedAngularDensity angleProductJacobian angleJacobian angleTuple
  simp_rw [anglePoint_eq_angularY]
  change reducedDensity z y*(∏ i, y i/(2*(Real.pi:ℂ)))=
    (∏ i, y i/(2*(Real.pi:ℂ)))*reducedDensity z y
  ring

end
end IsingBulk.Tail
