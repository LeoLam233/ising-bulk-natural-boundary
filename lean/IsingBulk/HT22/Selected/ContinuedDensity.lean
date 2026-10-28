import IsingBulk.HT22.Selected.BorderedDisk
import IsingBulk.HT22.Selected.SignedProductDisk
import IsingBulk.Preferred22.SelectedOneBodyDisk

/-! The literal odd bordered density on its actual common selected sheet.
Every real angular weight is inserted only after the whole homotopy. -/
namespace IsingBulk.HT22.Selected
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Algebra
open scoped BigOperators Topology

def selectedContinuedDensity {N : ℕ} (σ : ℂ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (t : ℂ) : ℂ :=
  let z := fun i => preferredSelectedContinuedRoot d B ε τ θ i t
  let y := fun i => Complex.exp (Complex.I*deformedAngles τ B.p B.m θ i)
  (preferredContourMatrix τ B.p B.m θ).det *
    (((1+σ*∏ i,z i)/(1-σ*∏ i,z i))*(constantBorderFirst y z).det*∏ i,oneBody (z i)) /
      ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))

 theorem selectedContinuedDensity_analyticAt {N : ℕ} (σ : ℂ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (t : ℂ)
    (hroot : ∀ i, AnalyticAt ℂ (preferredSelectedContinuedRoot d B ε τ θ i) t)
    (hpair : ∀ i j,1-preferredSelectedContinuedRoot d B ε τ θ i t*
      preferredSelectedContinuedRoot d B ε τ θ j t≠0)
    (hprod : 1-σ*preferredSelectedContinuedProduct d B ε τ θ t≠0) :
    AnalyticAt ℂ (selectedContinuedDensity σ d B ε τ θ) t := by
  let z := fun s i => preferredSelectedContinuedRoot d B ε τ θ i s
  let y := fun i => Complex.exp (Complex.I*deformedAngles τ B.p B.m θ i)
  have hZ := Finset.univ.analyticAt_fun_prod (fun i _ => hroot i)
  have hentry (i j : Fin (N+1)) :
      AnalyticAt ℂ (fun s => constantBorderFirst y (z s) i j) t := by
    cases i using Fin.cases with
    | zero => cases j using Fin.cases <;> exact analyticAt_const
    | succ i =>
      cases j using Fin.cases with
      | zero => exact analyticAt_const
      | succ j =>
        change AnalyticAt ℂ (fun s => -Complex.I *
          ((y i-y j)/(1-z s i*z s j))) t
        exact analyticAt_const.mul ((analyticAt_const.sub analyticAt_const).div
          (analyticAt_const.sub ((hroot i).mul (hroot j))) (hpair i j))
  have hdet : AnalyticAt ℂ (fun s => (constantBorderFirst y (z s)).det) t := by
    simp only [Matrix.det_apply']
    exact Finset.univ.analyticAt_fun_sum (fun e _ =>
      analyticAt_const.mul (Finset.univ.analyticAt_fun_prod (fun i _ => hentry (e i) i)))
  have hbody : AnalyticAt ℂ (fun s => ∏ i,oneBody (z s i)) t := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply (analyticAt_const.mul (hroot i)).div (analyticAt_const.sub ((hroot i).pow 2))
    change 1 - (preferredSelectedContinuedRoot d B ε τ θ i t)^2 ≠ 0
    simpa only [pow_two] using hpair i i
  exact (analyticAt_const.mul ((((analyticAt_const.add (analyticAt_const.mul hZ)).div
    (analyticAt_const.sub (analyticAt_const.mul hZ)) hprod).mul hdet).mul hbody)).div_const

 theorem selectedContinuedDensity_norm {N : ℕ} (σ : ℂ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (t : ℂ)
    {J R K A : ℝ} (hJ : 0≤J) (hR : 0≤R) (hK : 0≤K)
    (hjac : ‖(preferredContourMatrix τ B.p B.m θ).det‖≤J)
    (hres : ‖(1+σ*preferredSelectedContinuedProduct d B ε τ θ t)/
      (1-σ*preferredSelectedContinuedProduct d B ε τ θ t)‖≤R)
    (hdet : ‖(constantBorderFirst (fun i => Complex.exp (Complex.I*deformedAngles τ B.p B.m θ i))
      (fun i => preferredSelectedContinuedRoot d B ε τ θ i t)).det‖≤K)
    (hbody : ∀ i,‖oneBody (preferredSelectedContinuedRoot d B ε τ θ i t)‖≤
      A*preferredSelectedOneBodyProfile d ε (θ i)) :
    ‖selectedContinuedDensity σ d B ε τ θ t‖≤
      J*R*K*A^N*(∏ i,preferredSelectedOneBodyProfile d ε (θ i)) /
        ((N.factorial:ℝ)*(2*Real.pi)^(N-1)) := by
  have hb : ‖∏ i,oneBody (preferredSelectedContinuedRoot d B ε τ θ i t)‖≤
      A^N*(∏ i,preferredSelectedOneBodyProfile d ε (θ i)) := by
    rw [norm_prod]
    calc
      _ ≤ ∏ i,A*preferredSelectedOneBodyProfile d ε (θ i) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hbody i)
      _ = _ := by simp [Finset.prod_mul_distrib]
  have hnum := mul_le_mul (mul_le_mul (mul_le_mul hjac hres (norm_nonneg _) hJ)
    hdet (norm_nonneg _) (mul_nonneg hJ hR)) hb (norm_nonneg _)
    (mul_nonneg (mul_nonneg hJ hR) hK)
  unfold selectedContinuedDensity
  rw [norm_div]
  simp only [norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_ofNat,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa only [preferredSelectedContinuedProduct,mul_assoc] using hnum

end
end IsingBulk.HT22.Selected
