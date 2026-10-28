import IsingBulk.HT22.First.LocalLimit.SignedCriticalCharts
import IsingBulk.HT22.Arithmetic.BranchCharts

namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex Set Filter IsingBulk.First IsingBulk.Branch IsingBulk.HT.First
open IsingBulk.PrimeFamily Arithmetic
open scoped Topology
set_option backward.isDefEq.respectTransparency false

def physicalCriticalLocalIntegral {n : ℕ} (negative : Bool) (β : ℝ)
    (χ : ShapeSpace n → ℝ) : ℂ → ℂ :=
  if negative then negativeCriticalLocalIntegral β χ
  else angularLocalIntegral β (fun x => (χ x:ℂ))

def physicalCriticalLeadingCoefficient (p : ℕ) (α : ℝ) : ℂ :=
  if negativeSide α then signedCriticalLeadingCoefficient p α
  else equalAngleLeadingCoefficient p α

theorem prime_physicalCriticalLeadingCoefficient_ne_zero {p : ℕ} (hp : p.Prime)
    (hp5 : 5≤p) {a : ℤ} (ha : PrimeIndex p a) :
    physicalCriticalLeadingCoefficient p (angle p a)≠0 := by
  have h := (prime_two_chart_asymptotic hp hp5 ha).1
  unfold physicalCriticalLeadingCoefficient
  split
  · exact signedCriticalLeadingCoefficient_ne_zero h
  · exact h

theorem prime_physicalCritical_lower_limit {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) :
    ∃ R : ℝ,0<R ∧ ∀ χ : ShapeSpace (p-1) → ℝ,
      Continuous χ → χ 0=1 → (∀ x,|χ x|≤1) → (∀ x,χ x≠0 → ‖x‖<R) →
      Tendsto (fun ε : ℝ => ε •
        (deriv^[derivativeOrder p] (physicalCriticalLocalIntegral
          (negativeSide (angle p a)) (primeBranchData hp hp5 ha).alpha χ))
          (radialParameter (primeBranchData hp hp5 ha).alpha ε))
        (𝓝[>] 0) (𝓝 ((1/2:ℂ)*physicalCriticalLeadingCoefficient p (angle p a))) := by
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨hα,hαπ⟩ := primeIndex_angle_bounds hp.pos ha
  have hc : Real.cos (angle p a)≠0 := by
    intro hz
    exact primeRoot_level_ne_zero hp hp5 ha (by rw [hz,mul_zero])
  have he : p-1+1=p := by omega
  have hep : ((p-1:ℕ):ℂ)+1=(p:ℂ) := by exact_mod_cast he
  have hres := prime_equal_angle_resonance hp.ne_zero a
  by_cases h : Real.pi/2<angle p a
  · have ht := negativeCritical_lower_limit (n:=p-1) (by omega)
      (he.symm ▸ ho) (angle p a) hα hαπ hc (by rw [hep];exact hres)
    simpa only [he,physicalCriticalLocalIntegral,physicalCriticalLeadingCoefficient,
      negativeSide,decide_eq_true h,↓reduceIte,primeBranchData,positiveTraceBranchData,
      effectiveAngle,ite_eq_left h] using ht
  · obtain ⟨_,R,hR,hL⟩ := equalAngle_two_chart_limit (n:=p-1) (by omega)
      (he.symm ▸ ho) (angle p a) hα hαπ hc (by rw [hep];exact hres)
    refine ⟨R,hR,?_⟩
    intro χ hχ hχ0 hχb hχs
    have ht := (hL (fun x => (χ x:ℂ)) (continuous_ofReal.comp hχ)
      (by exact_mod_cast hχ0) (fun x => by simpa only [norm_real,Real.norm_eq_abs] using hχb x)
      (fun x hx => hχs x (ofReal_ne_zero.mp hx))).const_mul (1/2:ℂ)
    simp only [physicalCriticalLocalIntegral,physicalCriticalLeadingCoefficient,
      negativeSide,decide_eq_false h,Bool.false_eq_true,↓reduceIte,primeBranchData,positiveTraceBranchData,
      effectiveAngle,ite_eq_right h]
    convert ht using 1
    · funext ε
      rw [angularTwoChartIntegral_eq_twice,iterate_deriv_const_mul]
      simp only [he,real_smul]
      ring
    · rw [he]

end
end IsingBulk.HT22.LocalLimit
