import IsingBulk.Anisotropic.NegativeNormalForm.DensityFactors

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm Set Filter Metric
open scoped Topology

/-- The full pair factor, including its anisotropy power, on complex angles. -/
def localCompletePair (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (t a b : ℂ) : ℂ :=
  B t*(Complex.sin ((a-b)/2)/
    Complex.sinh ((negativePhase B phi hphi t a+negativePhase B phi hphi t b)/2))^2

@[simp] theorem localCompletePair_center (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) : localCompletePair B phi hphi 0 0 0=0 := by
  simp [localCompletePair]

theorem localCompletePair_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => localCompletePair B phi hphi z.1 z.2.1 z.2.2) 0 := by
  have hg : AnalyticAt ℂ (fun p : ℂ × ℂ => negativePhase B phi hphi p.1 p.2) (0,0) := by
    simpa using negativePhase_analyticAt_center B phi hphi 0 (by simpa using hB)
  have ha : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.2.1) 0 := analyticAt_fst.comp analyticAt_snd
  have hb : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.2.2) 0 := analyticAt_snd.comp analyticAt_snd
  have h1 : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => negativePhase B phi hphi z.1 z.2.1) 0 :=
    hg.comp_of_eq (analyticAt_fst.prod ha) rfl
  have h2 : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => negativePhase B phi hphi z.1 z.2.2) 0 :=
    hg.comp_of_eq (analyticAt_fst.prod hb) rfl
  have hz : negativePhase B phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa using negativePhase_center B phi hphi 0
  have hden : Complex.sinh ((negativePhase B phi hphi 0 0+negativePhase B phi hphi 0 0)/2)≠0 := by
    rw [hz,show ((phi:ℂ)*Complex.I+(phi:ℂ)*Complex.I)/2=(phi:ℂ)*Complex.I by ring]
    rw [Complex.sinh_mul_I,←Complex.ofReal_sin]
    exact mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero
  exact (hB.comp_of_eq analyticAt_fst rfl).mul
    (((Complex.analyticAt_sin.comp ((ha.sub hb).div_const)).div
      (Complex.analyticAt_sinh.comp ((h1.add h2).div_const)) hden).pow 2)

/-- A dimension-independent complex neighborhood where every complete pair
contracts. No root-modulus or Schur-contractivity assumption is used. -/
theorem localCompletePair_uniform_contraction (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    ∃ δ : ℝ, 0<δ ∧ ∀t a b : ℂ, ‖t‖<δ → ‖a‖<δ → ‖b‖<δ →
      ‖localCompletePair B phi hphi t a b‖≤(1/2:ℝ) := by
  have hc := (localCompletePair_analyticAt B phi hphi hB).continuousAt.norm
  have he : ∀ᶠ z : ℂ × ℂ × ℂ in 𝓝 0,
      ‖localCompletePair B phi hphi z.1 z.2.1 z.2.2‖<(1/2:ℝ) :=
    hc.eventually_lt_const (by simp)
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ,hδ,?_⟩
  intro t a b ht ha hb
  have hmem : dist (t,a,b) (0 : ℂ × ℂ × ℂ)<δ := by
    simpa [dist_zero_right,Prod.norm_def,max_lt_iff] using And.intro ht (And.intro ha hb)
  exact (hd hmem).le

end IsingBulk.Anisotropic.NegativeCycles
