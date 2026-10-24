import IsingBulk.Anisotropic.NegativeNormalForm.UniformMeanField
import IsingBulk.Anisotropic.NegativeNormalForm.UniformCorrectionBounds

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric
open scoped BigOperators

structure UniformCorrectionWitness (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (n : ℕ) (d : ℂ) (r C : ℝ) (P : UniformProjectedWitness B phi hphi n d r C) (R : ℝ) where
  W : Config n → Config n
  w_analytic : AnalyticOnNhd ℂ W (ball 0 (R/2))
  w_zero : W 0=0
  w_deriv : HasFDerivAt W (ContinuousLinearMap.id ℂ (Config n)) 0
  w_perm : ∀ e w, W (permute e w)=permute e (W w)
  w_inverse : ∀ y, ‖y‖≤R/2 → ‖W y‖≤R ∧ ‖W y‖≤2*‖y‖ ∧
    meanCorrection (actualMeanField B phi hphi d P.T P.V (W y)) (W y)=y ∧
    (ZeroMean y → ZeroMean (W y))
  w_lip : ∀ y z, ‖y‖≤R/2 → ‖z‖≤R/2 → ‖W y-W z‖≤2*‖y-z‖
  root_bound : ∀ w, ‖w‖≤R → ‖inverseRootField B phi hphi d P.T P.V w-1‖≤1/64
  normalized_mean_bound : ∀ w, ‖w‖≤R → ‖(n:ℂ) • actualMeanField B phi hphi d P.T P.V w‖≤1/8
  correction_lip : LipschitzOnWith (1/64)
    (fun w => meanCorrection (actualMeanField B phi hphi d P.T P.V w) w-w) (closedBall 0 R)

/-- The actual mean correction has a holomorphic inverse on a dimension-independent ball. -/
theorem exists_uniform_correction_witness (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0) :
    ∃ R r C : ℝ, 0<R ∧ 0<r ∧ 0<C ∧ 4*R≤r ∧
      ∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<R →
      ∃ P : UniformProjectedWitness B phi hphi n d r C,
        Nonempty (UniformCorrectionWitness B phi hphi n d r C P R) := by
  obtain ⟨δ,r,C,L,hδ,hr,hC,hL,hδr,hmean⟩ := exists_uniform_actual_mean_field B phi hphi hB hB0
  obtain ⟨R₀,hR₀,hcorr⟩ := exists_uniform_correction_radius L hL
  let R := min δ (min R₀ (1/(8*(L+1))))/2
  have hR : 0<R := div_pos (lt_min hδ (lt_min hR₀ (by positivity))) (by norm_num)
  have hRδ : R≤δ := by dsimp [R]; linarith [min_le_left δ (min R₀ (1/(8*(L+1))))]
  have hRR : R≤R₀ := by
    have hh := (min_le_right δ (min R₀ (1/(8*(L+1))))).trans (min_le_left R₀ (1/(8*(L+1))))
    dsimp [R]; linarith
  have hRL : L*R≤1/8 := by
    have hh := (min_le_right δ (min R₀ (1/(8*(L+1))))).trans (min_le_right R₀ (1/(8*(L+1))))
    have hpos : 0<1/(8*(L+1)) := by positivity
    have hh' : R≤1/(8*(L+1)) := by dsimp [R]; linarith
    have hmul := (le_div_iff₀ (by positivity : 0<8*(L+1))).mp hh'
    nlinarith

  refine ⟨R,r,C,hR,hr,hC,by linarith,?_⟩
  intro n hn d hd
  obtain ⟨P,hEa,hE0,hEL,hSb⟩ := hmean n hn d (hd.trans_le hRδ)
  let E := dimensionNormalizedMeanField B phi hphi d P.T P.V
  let F : Config n → Config n := fun w => normalizedMeanCorrection (E w) w
  have hEball : AnalyticOnNhd ℂ E (ball 0 R) := hEa.mono (ball_subset_ball hRδ)
  obtain ⟨hFa,hFL⟩ := hcorr R hR hRR n hn E hEball hE0
    (fun w z hw hz => hEL w z (hw.trans hRδ) (hz.trans hRδ))
  have hF0 : F 0=0 := by simp [F,normalizedMeanCorrection,mean]
  have hdF : HasFDerivAt F (ContinuousLinearMap.id ℂ (Config n)) 0 :=
    normalizedMeanCorrection_hasFDerivAt E (hEball 0 (by simpa using hR)) hE0
  have hFactual (w : Config n) : F w=meanCorrection (actualMeanField B phi hphi d P.T P.V w) w := by
    dsimp [F,E]
    rw [dimensionNormalizedMeanField_eq_scaled hn,normalizedMeanCorrection_scaled hn]
  have hFeq (e : Equiv.Perm (Fin n)) (w : Config n) : F (permute e w)=permute e (F w) := by
    rw [hFactual,actualMeanField_permute B phi hphi d P.T P.V P.t_perm P.v_perm,
      meanCorrection_permute,hFactual]
  obtain ⟨W,hWa,hW0,hdW,hWeq,hWs,hWL⟩ := exists_equivariant_quantitative_inverse F R hR (1/64) (by norm_num)
    hFa hF0 hdF hFeq hFL
  have hWdata (y : Config n) (hy : ‖y‖≤R/2) : ‖W y‖≤R ∧ ‖W y‖≤2*‖y‖ ∧ F (W y)=y := by
    have hh := hWs y (by norm_num at *; linarith)
    refine ⟨by simpa using hh.1,?_,hh.2.1⟩
    have hx := hh.2.2
    norm_num at hx
    nlinarith [norm_nonneg y]
  have hsum (w : Config n) : ∑ i, F w i=∑ i, w i := by
    rw [hFactual]
    have hm := meanCoefficients_zeroMean hn (inverseRootField B phi hphi d P.T P.V w)
    change ∑ i, actualMeanField B phi hphi d P.T P.V w i=0 at hm
    simp only [meanCorrection,Finset.sum_add_distrib,← Finset.mul_sum,hm,mul_zero,add_zero]
  refine ⟨P,⟨⟨W,hWa.mono (ball_subset_ball (by norm_num; linarith)),hW0,hdW,hWeq,
    ?_,?_,(fun w hw => hSb w (hw.trans hRδ)),?_,?_⟩⟩⟩
  · intro y hy
    obtain ⟨h1,h2,h3⟩ := hWdata y hy
    refine ⟨h1,h2,by simpa only [hFactual] using h3,?_⟩
    intro hm
    change ∑ i, W y i=0
    rw [← hsum (W y),h3]
    exact hm
  · intro y z hy hz
    have hh := hWL y z (by norm_num at *; linarith) (by norm_num at *; linarith)
    norm_num at hh
    nlinarith [norm_nonneg (y-z)]
  · intro w hw
    have hh := hEL w 0 (hw.trans hRδ) (by simpa using hδ.le)
    simp only [hE0,sub_zero,dimensionNormalizedMeanField_eq_scaled hn] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hw hL.le).trans hRL)
  · change LipschitzOnWith (1/64) (fun w => F w-w) (closedBall 0 R) at hFL
    simpa only [hFactual] using hFL

end
end IsingBulk.Anisotropic.NegativeNormalForm
