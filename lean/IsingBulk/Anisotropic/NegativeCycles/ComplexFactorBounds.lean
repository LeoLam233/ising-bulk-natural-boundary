import IsingBulk.Anisotropic.NegativeCycles.LocalPairContraction

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm Set Filter Metric
open scoped Topology

theorem localOneBody_analyticAt (B : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => (Complex.sinh (negativePhase B phi hphi z.1 z.2))⁻¹) (0,0) := by
  have hg : AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2) (0,0) := by
    simpa using negativePhase_analyticAt_center B phi hphi 0 (by simpa using hB)
  apply (Complex.analyticAt_sinh.comp hg).inv
  have hz : negativePhase B phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa using negativePhase_center B phi hphi 0
  change Complex.sinh (negativePhase B phi hphi 0 0)≠0
  rw [hz,Complex.sinh_mul_I,←Complex.ofReal_sin]
  exact mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero

/-- Uniform scalar factors for every particle number, on complex angles. -/
theorem local_complex_factors_bounded (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hr : AnalyticAt ℂ rootB 0) :
    ∃ δ M : ℝ,0<δ ∧ 1≤M ∧ ∀t a : ℂ, ‖t‖<δ → ‖a‖<δ →
      ‖B t‖≤M ∧ ‖rootB t‖≤M ∧ ‖(Complex.sinh (negativePhase B phi hphi t a))⁻¹‖≤M := by
  let O : ℂ × ℂ → ℂ := fun z => (Complex.sinh (negativePhase B phi hphi z.1 z.2))⁻¹
  let M : ℝ := ‖B 0‖+‖rootB 0‖+‖O 0‖+1
  have hm : 1≤M := by dsimp [M]; linarith [norm_nonneg (B 0),norm_nonneg (rootB 0),norm_nonneg (O 0)]
  have hb : ∀ᶠ z : ℂ × ℂ in 𝓝 0, ‖B z.1‖<M :=
    (hB.comp_of_eq analyticAt_fst rfl).continuousAt.norm.eventually_lt_const (by
      dsimp [M]; nlinarith [norm_nonneg (rootB 0),norm_nonneg (O 0)])
  have hr' : ∀ᶠ z : ℂ × ℂ in 𝓝 0, ‖rootB z.1‖<M :=
    (hr.comp_of_eq analyticAt_fst rfl).continuousAt.norm.eventually_lt_const (by
      dsimp [M]; nlinarith [norm_nonneg (B 0),norm_nonneg (O 0)])
  have ho : ∀ᶠ z : ℂ × ℂ in 𝓝 0, ‖O z‖<M :=
    (localOneBody_analyticAt B phi hphi hB).continuousAt.norm.eventually_lt_const (by
      change ‖O 0‖<M
      dsimp [M]; nlinarith [norm_nonneg (B 0),norm_nonneg (rootB 0)])
  have he : ∀ᶠ z : ℂ × ℂ in 𝓝 0, ‖B z.1‖≤M ∧ ‖rootB z.1‖≤M ∧ ‖O z‖≤M := by
    filter_upwards [hb,hr',ho] with z hz hrz hoz
    exact ⟨hz.le,hrz.le,hoz.le⟩
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ,M,hδ,hm,?_⟩
  intro t a ht ha
  have hmem : dist (t,a) (0 : ℂ × ℂ)<δ := by
    simpa [dist_zero_right,Prod.norm_def,max_lt_iff] using And.intro ht ha
  exact hd hmem

end IsingBulk.Anisotropic.NegativeCycles
