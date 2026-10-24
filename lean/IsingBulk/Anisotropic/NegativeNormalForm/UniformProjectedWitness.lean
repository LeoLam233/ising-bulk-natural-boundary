import IsingBulk.Anisotropic.NegativeNormalForm.UniformProjectedInverse

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric

/-- Data already constructed by the actual dimension-uniform projected inverse theorem. -/
structure UniformProjectedWitness (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (n : ℕ) (d : ℂ) (r C : ℝ) where
  T : Config n → ℂ
  V : Config n → Config n
  t_analytic : AnalyticOnNhd ℂ T (ball 0 (2*r))
  t_zero : T 0=1-Complex.cos d
  t_perm : ∀ e v, T (permute e v)=T v
  t_pole : ∀ v : Config n, ‖v‖<2*r → poleEquation B phi hphi d (T v) v=0 ∧
    (ZeroMean v → ‖T v-(1-Complex.cos d)‖≤C*averageSquaredNorm v)
  t_lip : ∀ v w : Config n, ‖v‖<2*r → ‖w‖<2*r → ‖T v-T w‖≤‖v-w‖
  projected_lip : LipschitzOnWith (1/64)
    (fun v => projectedExtension (fun x => phaseSeparableMap B phi hphi d (T x) x) v-v) (closedBall 0 r)
  v_analytic : AnalyticOnNhd ℂ V (ball 0 (r/2))
  v_analytic_zero : AnalyticAt ℂ V 0
  v_zero : V 0=0
  v_deriv : HasFDerivAt V (ContinuousLinearMap.id ℂ (Config n)) 0
  v_perm : ∀ e v, V (permute e v)=permute e (V v)
  v_inverse : ∀ y, ‖y‖≤r/2 → ‖V y‖≤r ∧ ‖V y‖≤2*‖y‖ ∧
    projectedExtension (fun v => phaseSeparableMap B phi hphi d (T v) v) (V y)=y ∧
    (ZeroMean y → ZeroMean (V y) ∧ project (phaseSeparableMap B phi hphi d (T (V y)) (V y))=y)
  v_lip : ∀ y z, ‖y‖≤r/2 → ‖z‖≤r/2 → ‖V y-V z‖≤2*‖y-z‖

 theorem exists_uniform_projected_witness (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<r →
      Nonempty (UniformProjectedWitness B phi hphi n d r C) := by
  obtain ⟨r,C,hr,hC,hex⟩ := exists_dimension_uniform_projected_inverse B phi hphi hB hB0
  refine ⟨r,C,hr,hC,?_⟩
  intro n hn d hd
  obtain ⟨T,V,hT,hT0,hTp,hTs,hTL,hFL,hVa,hV,hV0,hdV,hVp,hVs,hVL⟩ := hex n hn d hd
  exact ⟨⟨T,V,hT,hT0,hTp,hTs,hTL,hFL,hVa,hV,hV0,hdV,hVp,hVs,hVL⟩⟩

end
end IsingBulk.Anisotropic.NegativeNormalForm
