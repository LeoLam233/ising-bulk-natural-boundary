import IsingBulk.Anisotropic.NegativeNormalForm.UniformExactNormalForm
import IsingBulk.Anisotropic.NegativeNormalForm.UniformScalarRescaling

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology

/-- The actual canonical pole chart on a common ball, with full-interior
analyticity, global permutation symmetry, and quantitative derivative control. -/
theorem exists_dimension_uniform_canonical_normal_form (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<δ →
      ∃ T : Config n → ℂ, ∃ Psi : Config n → Config n,
        AnalyticOnNhd ℂ T (ball 0 δ) ∧ T 0=1-Complex.cos d ∧
        AnalyticOnNhd ℂ Psi (ball 0 δ) ∧ Psi 0=0 ∧
        HasFDerivAt Psi (scalarConfiguration (Complex.sqrt (centralHessian B phi d))⁻¹) 0 ∧
        (∀ e y, Psi (permute e y)=permute e (Psi y)) ∧
        LipschitzOnWith (1/8) (fun y => Psi y-y) (closedBall 0 δ) ∧
        (∀ y, ‖y‖<δ → ‖fderiv ℂ Psi y-ContinuousLinearMap.id ℂ (Config n)‖≤1/8) ∧
        (∀ y, ‖y‖≤δ → ‖Psi y-y‖≤(1/8)*‖y‖ ∧
          (ZeroMean y → ZeroMean (Psi y) ∧ poleEquation B phi hphi d (T (Psi y)) (Psi y)=0 ∧
            T (Psi y)=1-Complex.cos d+quadratic y/(2*n))) := by
  obtain ⟨δ₀,R,r,C,hδ₀,hR,hr,hC,hδR,hRr,hex⟩ := exists_dimension_uniform_exact_normal_form B phi hphi hB hB0
  obtain ⟨a,ha,hs⟩ := hessian_inverse_sqrt_uniform B phi hB
  let δ := min δ₀ a/4
  have hδ : 0<δ := div_pos (lt_min hδ₀ ha) (by norm_num)
  have hδ0 : 4*δ≤δ₀ := by dsimp [δ]; linarith [min_le_left δ₀ a]
  have hδa : δ≤a := by dsimp [δ]; linarith [min_le_right δ₀ a]
  refine ⟨δ,hδ,?_⟩
  intro n hn d hd
  obtain ⟨P,J,hFa,hF0,hdF,hFeq,hFs⟩ := hex n hn d (by linarith)
  have hdscale := hs d (hd.trans_le hδa)
  let c := (Complex.sqrt (centralHessian B phi d))⁻¹
  let F : Config n → Config n := fun y => P.V (J.W y)
  let Psi : Config n → Config n := fun y => F (scalarConfiguration c y)
  have hinside (y : Config n) (hy : ‖y‖≤δ) : ‖scalarConfiguration c y‖<δ₀ := by
    rw [norm_scalarConfiguration]
    have hh := mul_le_mul hdscale.2.2 hy (norm_nonneg _) (by norm_num : (0:ℝ)≤9/8)
    dsimp [c]
    linarith
  have hPsi : AnalyticOnNhd ℂ Psi (ball 0 δ) := by
    intro y hy
    exact (hFa (scalarConfiguration c y) (by simpa using hinside y (show ‖y‖≤δ by simpa using (mem_ball.mp hy).le))).comp
      (f := scalarConfiguration c) ((scalarConfiguration c).analyticAt y)
  have hPsi0 : Psi 0=0 := by simp [Psi,F,hF0]
  have hdF' : HasFDerivAt F (ContinuousLinearMap.id ℂ (Config n)) (scalarConfiguration c 0) := by simpa using hdF
  have hdPsi : HasFDerivAt Psi (scalarConfiguration c) 0 := by
    convert! hdF'.comp (f := fun y => scalarConfiguration c y) 0 ((scalarConfiguration c).hasFDerivAt (x := 0)) using 1
  have hLip : LipschitzOnWith (1/8) (fun y => Psi y-y) (closedBall 0 δ) :=
    scalar_rescaled_perturbation_lipschitz F c (R/2) δ hδ.le hdscale.2.2 hdscale.2.1 (by linarith)
      (J.corrected_perturbation_lipschitz B phi hphi d r C R P (by linarith))
  refine ⟨P.T,Psi,P.t_analytic.mono (ball_subset_ball (by linarith)),P.t_zero,hPsi,hPsi0,hdPsi,?_,hLip,?_,?_⟩
  · intro e y
    exact (congrArg F (scalarConfiguration_permute c e y)).trans (hFeq e (scalarConfiguration c y))
  · intro y hy
    have hnb : closedBall (0:Config n) δ∈𝓝 y :=
      mem_of_superset (isOpen_ball.mem_nhds (by simpa using hy)) ball_subset_closedBall
    have hh := norm_fderiv_le_of_lipschitzOn ℂ hnb hLip
    change ‖fderiv ℂ (Psi-id) y‖≤(1/8:ℝ) at hh
    rw [fderiv_sub (hPsi y (by simpa using hy)).differentiableAt differentiableAt_id,fderiv_id] at hh
    exact hh
  · intro y hy
    have hh := hLip.dist_le_mul y (by simpa using hy) 0 (by simpa using hδ.le)
    simp only [dist_eq_norm,hPsi0,sub_self,sub_zero,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] at hh
    refine ⟨hh,?_⟩
    intro hm
    have hactual := hFs (scalarConfiguration c y) (hinside y hy).le
    obtain ⟨hmy,hq⟩ := hactual.2.2 (scalarConfiguration_zeroMean c y hm)
    have hnorm : ‖Psi y‖<2*r := by
      have hi := hinside y hy
      change ‖P.V (J.W (scalarConfiguration c y))‖<2*r
      linarith [hactual.1]
    refine ⟨hmy,(P.t_pole (Psi y) hnorm).1,?_⟩
    rw [scalarConfiguration_quadratic] at hq
    change P.T (P.V (J.W (scalarConfiguration c y)))=_
    rw [hq]
    have hc : centralHessian B phi d*c^2=1 := hessian_inverse_sqrt_identity _ hdscale.1
    calc
      _ = 1-Complex.cos d+(centralHessian B phi d*c^2)*quadratic y/(2*n) := by ring
      _ = _ := by rw [hc,one_mul]

end
end IsingBulk.Anisotropic.NegativeNormalForm
