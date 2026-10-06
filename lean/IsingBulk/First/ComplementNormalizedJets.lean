import IsingBulk.First.ComplementMixedRegularity
import IsingBulk.First.ComplementFullPhaseJets

/-! Normalized fixed-radius parameter jets on the compact inverse-radius
parameter interval. No estimate on differentiated coefficients is assumed. -/
namespace IsingBulk.First
noncomputable section
open Filter
open scoped Topology ContDiff

/-- R⁻ʲ times the j-th exponential-amplitude jet, with ρ=R⁻¹ and z=Rv. -/
def normalizedParameterJet (A B : ℂ → ℂ) (ρ v : ℂ) : ℕ → ℂ → ℂ
  | 0 => A
  | j+1 => fun s => ρ * deriv (normalizedParameterJet A B ρ v j) s +
      v * deriv B s * normalizedParameterJet A B ρ v j s

theorem normalizedParameterJet_analyticAt (A B : ℂ → ℂ) (ρ v : ℂ) {s : ℂ}
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s) (j : ℕ) :
    AnalyticAt ℂ (normalizedParameterJet A B ρ v j) s := by
  induction j with
  | zero => exact hA
  | succ j ih =>
    exact (analyticAt_const.mul ih.deriv).add
      ((analyticAt_const.mul hB.deriv).mul ih)

/-- Exact identity with the full phase, for every finite derivative order. -/
theorem normalizedParameterJet_derivative (A B : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hA : AnalyticOnNhd ℂ A U) (hB : AnalyticOnNhd ℂ B U)
    (R v H : ℂ) (hR : R ≠ 0) (j : ℕ) : ∀ s ∈ U,
    (deriv^[j] (fun z => A z * Complex.exp (B z * (R*v) + H))) s =
      R^j * normalizedParameterJet A B R⁻¹ v j s * Complex.exp (B s * (R*v) + H) := by
  induction j with
  | zero => intro s _; simp [normalizedParameterJet]
  | succ j ih =>
    intro s hs
    rw [Function.iterate_succ_apply']
    have he : (deriv^[j] (fun z => A z * Complex.exp (B z * (R*v) + H))) =ᶠ[𝓝 s]
        (fun z => R^j * normalizedParameterJet A B R⁻¹ v j z *
          Complex.exp (B z * (R*v) + H)) := by
      filter_upwards [hU.mem_nhds hs] with z hz
      exact ih z hz
    rw [he.deriv_eq]
    have hc := (normalizedParameterJet_analyticAt A B R⁻¹ v (hA s hs) (hB s hs) j).differentiableAt
    have hd := (hc.hasDerivAt.const_mul (R^j)).mul
      ((((hB s hs).differentiableAt.hasDerivAt.mul_const (R*v)).add_const H).cexp)
    calc
      _ = R^j * deriv (normalizedParameterJet A B R⁻¹ v j) s * Complex.exp (B s * (R*v) + H) +
          R^j * normalizedParameterJet A B R⁻¹ v j s *
            (Complex.exp (B s * (R*v) + H) * (deriv B s * (R*v))) := hd.deriv
      _ = _ := by
        simp only [normalizedParameterJet, pow_succ]
        field_simp

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- All normalized generated coefficient functions are jointly real C∞.
The hypotheses concern the original amplitude and scalar phase only. -/
theorem normalizedParameterJet_joint_contDiffAt (A B : P × ℂ → ℂ) (ρ v : P → ℂ)
    (p : P) (s : ℂ) (hA : ContDiffAt ℝ ∞ A (p,s)) (hB : ContDiffAt ℝ ∞ B (p,s))
    (hρ : ContDiffAt ℝ ∞ ρ p) (hv : ContDiffAt ℝ ∞ v p)
    (hholA : ∀ᶠ q : P × ℂ in 𝓝 (p,s), AnalyticAt ℂ (fun z => A (q.1,z)) q.2)
    (hholB : ∀ᶠ q : P × ℂ in 𝓝 (p,s), AnalyticAt ℂ (fun z => B (q.1,z)) q.2)
    (j : ℕ) :
    ContDiffAt ℝ ∞ (fun q : P × ℂ =>
      normalizedParameterJet (fun z => A (q.1,z)) (fun z => B (q.1,z))
        (ρ q.1) (v q.1) j q.2) (p,s) := by
  induction j with
  | zero => exact hA
  | succ j ih =>
    have hjhol : ∀ᶠ q : P × ℂ in 𝓝 (p,s), DifferentiableAt ℂ
        (normalizedParameterJet (fun z => A (q.1,z)) (fun z => B (q.1,z)) (ρ q.1) (v q.1) j) q.2 := by
      filter_upwards [hholA, hholB] with q ha hb
      exact (normalizedParameterJet_analyticAt _ _ _ _ ha hb j).differentiableAt
    have hj := contDiffAt_parameterized_complex_deriv p s ih hjhol
    have hb := contDiffAt_parameterized_complex_deriv p s hB
      (hholB.mono (fun _ h => h.differentiableAt))
    exact ((hρ.comp (p,s) contDiffAt_fst).mul hj).add
      (((hv.comp (p,s) contDiffAt_fst).mul hb).mul ih)

end
end IsingBulk.First
