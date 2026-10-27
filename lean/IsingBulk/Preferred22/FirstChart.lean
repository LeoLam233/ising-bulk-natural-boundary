import IsingBulk.Preferred22.KernelProduct
import IsingBulk.Preferred22.AngularAnalytic
import IsingBulk.Preferred22.ShapePeriod
import IsingBulk.First.ActualLocalizedPostMeanAsymptotic

/-! Exact identification of the Preferred equal-angle local chart with the
proper local beta-integral calculation. No old complete-tail or boundary
endpoint is imported. Every normalization and root is identified explicitly. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Set MeasureTheory Filter Metric
open scoped BigOperators Topology

def equalAngleData (α : ℝ) (hα : 0 < α) (hαπ : α < Real.pi/2) :
    IsingBulk.First.OrderedChartData where
  alpha := α
  beta := α
  theta := α
  alpha_pos := hα
  alpha_lt := hαπ
  beta_pos := hα
  beta_lt := hαπ
  theta_pos := hα
  theta_lt := hαπ
  angle_relation := by ring

theorem equalAngleData_d (α : ℝ) (hα : 0 < α) (hαπ : α < Real.pi/2) :
    (equalAngleData α hα hαπ).d = sourceCotangent α := by
  have hs : Real.sin α ≠ 0 := (equalAngleData α hα hαπ).sin_alpha_pos.ne'
  have ht := Real.sin_sq_add_cos_sq α
  dsimp [equalAngleData,IsingBulk.First.OrderedChartData.d,sourceCotangent]
  field_simp
  linear_combination -2 * Real.cos α * ht

theorem equalAngleData_Q (α : ℝ) (hα : 0 < α) (hαπ : α < Real.pi/2) (N : ℕ) :
    (equalAngleData α hα hαπ).Q N = 2*N := by
  have hs : Real.sin α ≠ 0 := (equalAngleData α hα hαπ).sin_alpha_pos.ne'
  dsimp [equalAngleData,IsingBulk.First.OrderedChartData.Q]
  field_simp

theorem sourceW_angleRoot (s : ℂ) (θ : ℝ) :
    IsingBulk.First.sourceW s (angleRoot θ) = angularW s θ := by
  rw [IsingBulk.First.sourceW,angleRoot_trace]
  unfold IsingBulk.First.sourceS angularW temperatureTrace
  ring

theorem angular_quadratic_source (s : ℂ) (θ : ℝ) :
    physicalRoot (angularW s θ)^2 -
      (2*IsingBulk.First.sourceS s-angleRoot θ-(angleRoot θ)⁻¹)*
        physicalRoot (angularW s θ)+1 = 0 := by
  rw [← sourceW_angleRoot]
  have h := physicalRoot_quadratic (IsingBulk.First.sourceW s (angleRoot θ))
  dsimp [IsingBulk.First.sourceW] at h ⊢
  linear_combination h

/-- On a regular angular chart, the pair-product form equals the actual
determinant, including coordinate coincidences. -/
theorem physical_determinant_pairProduct {N : ℕ} (hN : Even N)
    {s : ℂ} (hs : 1 < ‖s‖) (θ : Fin N → ℝ)
    (hy : ∀ i j : Fin N, i < j → 1-angleRoot (θ i)*angleRoot (θ j) ≠ 0) :
    (gaugeKernel (fun i => angleRoot (θ i)) (angularRoots s θ)).det =
      IsingBulk.First.pairProduct (angularRoots s θ) *
        IsingBulk.First.pairProduct (fun i => angleRoot (θ i)) := by
  obtain ⟨m,hm⟩ := hN
  have hm' : N=2*m := by omega
  clear hm
  subst N
  rw [physical_determinant_product m hs θ]
  unfold IsingBulk.First.pairProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  have hf : Finset.univ.filter (fun j : Fin (2*m) => i < j) = Finset.Ioi i := by
    ext j
    simp
  rw [hf]
  apply Finset.prod_congr rfl
  intro j hj
  rw [gaugeKernel_square]
  symm
  simpa only [neg_mul,angularRoots] using IsingBulk.First.source_pair_identity (angleRoot_ne_zero _) (angleRoot_ne_zero _)
    (physicalRoot_ne_zero _) (physicalRoot_ne_zero _)
    (angular_quadratic_source s (θ i)) (angular_quadratic_source s (θ j))
    (hy i j (Finset.mem_Ioi.mp hj)) (angular_pair_denominator_ne_zero hs θ i j)

def firstChartAngles {n : ℕ} (α : ℝ) (t : Fin n → ℝ) : Fin (n+1) → ℝ :=
  fun j => constrainedAngles t j-α

theorem firstChart_shapeY {n : ℕ} (α : ℝ) (t : Fin n → ℝ) :
    IsingBulk.First.shapeY α t = fun j => angleRoot (firstChartAngles α t j) := by
  funext j
  unfold IsingBulk.First.shapeY firstChartAngles angleRoot
    IsingBulk.First.shapeExtend constrainedAngles
  rw [ofReal_sub]
  congr 1
  ring

theorem firstChart_shapeZ {n : ℕ} {s : ℂ} (hs : 1 < ‖s‖)
    (α : ℝ) (t : Fin n → ℝ)
    (hr : ∀ j, 0 < (angularW s (firstChartAngles α t j)).re)
    (hi : ∀ j, 0 < (angularW s (firstChartAngles α t j)).im) :
    IsingBulk.First.shapeZ s α t = angularRoots s (firstChartAngles α t) := by
  funext j
  unfold IsingBulk.First.shapeZ
  rw [firstChart_shapeY,sourceW_angleRoot]
  exact IsingBulk.First.phaseRoot_eq_interior_root (physicalRoot_quadratic _)
    (physicalRoot_inside (angularW_off_segment hs _)) (hr j) (hi j)

/-- The actual local density has exactly the Preferred normalized angular
density. The free-coordinate measure contributes precisely (2π)^(−n). -/
theorem postMeanDensity_eq_preferred {n : ℕ} (he : Even (n+1))
    {s : ℂ} (hs : 1 < ‖s‖) (α : ℝ) (t : Fin n → ℝ)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I) = 1)
    (hr : ∀ j, 0 < (angularW s (firstChartAngles α t j)).re)
    (hi : ∀ j, 0 < (angularW s (firstChartAngles α t j)).im)
    (hy : ∀ i j : Fin (n+1), i < j →
      1-angleRoot (firstChartAngles α t i)*angleRoot (firstChartAngles α t j) ≠ 0) :
    IsingBulk.First.postMeanDensity s α t =
      ((2*(Real.pi:ℂ))^n)⁻¹ * fullAngularDensity s (firstChartAngles α t) := by
  let θ := firstChartAngles α t
  let z := angularRoots s θ
  have hz := firstChart_shapeZ hs α t hr hi
  have hY : ∏ j : Fin (n+1), angleRoot (θ j) = 1 := by
    have h := IsingBulk.First.coordinateProduct_shapeY α t ha
    rw [firstChart_shapeY] at h
    exact h
  have hZ : (∏ j, z j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => physicalRoot_ne_zero _)
  have hp : (2*(Real.pi:ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hres : (∏ j, IsingBulk.First.residueFactor (z j)) =
      (∏ j, z j)*(∏ j, oneBody (z j)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    unfold IsingBulk.First.residueFactor oneBody
    ring
  have hmeasure : (∏ j : Fin (n+1), angleRoot (θ j)/(2*(Real.pi:ℂ))) =
      ((2*(Real.pi:ℂ))^(n+1))⁻¹ := by
    rw [Finset.prod_div_distrib,hY]
    simp
  have hdet := physical_determinant_pairProduct he hs θ hy
  have hden : 1-∏ j, z j ≠ 0 := angular_product_denominator_ne_zero (by omega) hs θ
  unfold IsingBulk.First.postMeanDensity IsingBulk.First.shapeRegularNumerator
    IsingBulk.First.shapePoleDenominator IsingBulk.First.shapeZProduct
    IsingBulk.First.coordinateProduct
  rw [hz,firstChart_shapeY]
  change 2*(Real.pi:ℂ)*(((∏ j,z j)⁻¹+1)*
    IsingBulk.First.pairProduct z*IsingBulk.First.pairProduct (fun j => angleRoot (θ j))*
      (∏ j,IsingBulk.First.residueFactor (z j))*(∏ j,angleRoot (θ j)/(2*(Real.pi:ℂ)))) /
    (1-∏ j,z j) = _
  rw [hres,hmeasure]
  simp only [fullAngularDensity]
  dsimp only [θ,z] at hdet ⊢
  rw [hdet]
  dsimp only [θ,z] at hZ hden
  rw [pow_succ]
  field_simp

def localizedPhysicalIntegral {n : ℕ} (α : ℝ)
    (chi : IsingBulk.First.ShapeSpace n → ℂ) (s : ℂ) : ℂ :=
  ∫ t : Fin n → ℝ, chi (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t)) *
    ((((n+1).factorial:ℂ)*(2*(Real.pi:ℂ))^n)⁻¹ *
      fullAngularDensity s (firstChartAngles α t))

end
end IsingBulk.Preferred22
