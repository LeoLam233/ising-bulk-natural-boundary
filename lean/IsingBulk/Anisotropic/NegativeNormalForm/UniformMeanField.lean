import IsingBulk.Anisotropic.NegativeNormalForm.UniformInverseRootField
import IsingBulk.Anisotropic.NegativeNormalForm.ReciprocalFieldBounds
import IsingBulk.Anisotropic.NegativeNormalForm.EquivariantMeanCorrection

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology

def dimensionNormalizedMeanField {n : ℕ} (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (d : ℂ) (T : Config n → ℂ) (V : Config n → Config n) (w : Config n) : Config n :=
  normalizedMeanField (reciprocalError (inverseRootField B phi hphi d T V w))

 theorem dimensionNormalizedMeanField_eq_scaled {n : ℕ} (hn : n≠0)
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ)
    (T : Config n → ℂ) (V : Config n → Config n) (w : Config n) :
    dimensionNormalizedMeanField B phi hphi d T V w=(n:ℂ) • actualMeanField B phi hphi d T V w :=
  normalizedMeanField_eq_scaled_coefficients hn _

 theorem normalizedReciprocalField_uniform {n : ℕ} (hn : n≠0)
    (S : Config n → Config n) (r L : ℝ) (_hL : 0≤L)
    (hS : AnalyticOnNhd ℂ S (ball 0 r))
    (hb : ∀ w, ‖w‖≤r → ‖S w-1‖≤1/4)
    (hLip : ∀ w z, ‖w‖≤r → ‖z‖≤r → ‖S w-S z‖≤L*‖w-z‖) :
    AnalyticOnNhd ℂ (fun w => normalizedMeanField (reciprocalError (S w))) (ball 0 r) ∧
    (∀ w z, ‖w‖≤r → ‖z‖≤r →
      ‖normalizedMeanField (reciprocalError (S w))-normalizedMeanField (reciprocalError (S z))‖≤32*L*‖w-z‖) := by
  have hA (w : Config n) (hw : ‖w‖≤r) : ‖reciprocalError (S w)‖≤1/2 := by
    have hh := reciprocalError_norm_le (S w) ((hb w hw).trans (by norm_num))
    linarith [hb w hw]
  refine ⟨?_,?_⟩
  · intro w hw
    have hw' : ‖w‖<r := by simpa using hw
    exact normalizedMeanField_analyticAt hn _ w
      (reciprocalError_analyticAt S w (hS w hw) ((hb w hw'.le).trans (by norm_num))) (hA w hw'.le)
  · intro w z hw hz
    have hh := normalizedMeanField_lipschitz hn (reciprocalError (S w)) (reciprocalError (S z)) (hA w hw) (hA z hz)
    have hi := reciprocalError_lipschitz (S w) (S z) ((hb w hw).trans (by norm_num)) ((hb z hz).trans (by norm_num))
    have hl := hLip w z hw hz
    nlinarith

/-- Dimension-free analytic and Lipschitz control of the actual mean field.
All radii and constants are selected before n; the projected witness is the actual constructed one. -/
theorem exists_uniform_actual_mean_field (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0) :
    ∃ δ r C L : ℝ, 0<δ ∧ 0<r ∧ 0<C ∧ 0<L ∧ 4*δ≤r ∧
      ∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<δ →
      ∃ P : UniformProjectedWitness B phi hphi n d r C,
        AnalyticOnNhd ℂ (dimensionNormalizedMeanField B phi hphi d P.T P.V) (ball 0 δ) ∧
        dimensionNormalizedMeanField B phi hphi d P.T P.V 0=0 ∧
        (∀ w z, ‖w‖≤δ → ‖z‖≤δ →
          ‖dimensionNormalizedMeanField B phi hphi d P.T P.V w-
            dimensionNormalizedMeanField B phi hphi d P.T P.V z‖≤L*‖w-z‖) ∧
        (∀ w, ‖w‖≤δ → ‖inverseRootField B phi hphi d P.T P.V w-1‖≤1/64) := by
  obtain ⟨r,C,hr,hC,hP⟩ := exists_uniform_projected_witness B phi hphi hB hB0
  obtain ⟨ρ,L,hρ,hL,hroot,hrootLip⟩ := phaseRootEnergy_uniform_small B phi hphi hB hB0 (1/64) (by norm_num)
  have htau : Tendsto (fun d : ℂ => 1-Complex.cos d) (𝓝 0) (𝓝 0) := by
    have hh : ContinuousAt (fun d : ℂ => 1-Complex.cos d) 0 := by fun_prop
    simpa using hh.tendsto
  have hb : ∀ᶠ d : ℂ in 𝓝 0, ‖1-Complex.cos d‖<ρ/2 ∧ AnalyticAt ℂ B (1-Complex.cos d) ∧
      B (1-Complex.cos d)≠0 ∧ centralHessian B phi d≠0 := by
    filter_upwards [htau.eventually (Metric.ball_mem_nhds (0:ℂ) (by positivity : 0<ρ/2)),
      htau.eventually hB.eventually_analyticAt, htau.eventually (hB.continuousAt.eventually_ne hB0),
      centralHessian_eventually_nonzero B phi hB] with d hd ha hn hh
    exact ⟨by simpa using hd,ha,hn,hh⟩
  obtain ⟨a,ha,hbranch⟩ := Metric.mem_nhds_iff.mp hb
  let δ := min r (min ρ a)/8
  have hδ : 0<δ := div_pos (lt_min hr (lt_min hρ ha)) (by norm_num)
  have hδr : 4*δ≤r := by dsimp [δ]; linarith [min_le_left r (min ρ a)]
  have hδρ : 4*δ≤ρ := by
    have hh := (min_le_right r (min ρ a)).trans (min_le_left ρ a)
    dsimp [δ]; linarith
  have hδa : δ≤a := by
    have hh := (min_le_right r (min ρ a)).trans (min_le_right ρ a)
    dsimp [δ]; linarith
  refine ⟨δ,r,C,64*L,hδ,hr,hC,by positivity,hδr,?_⟩
  intro n hn d hd
  obtain ⟨P⟩ := hP n hn d (by linarith)
  have hbd := hbranch (show d∈ball (0:ℂ) a by simpa using hd.trans_le hδa)
  obtain ⟨hSa,hSb,hSL⟩ := inverseRootField_uniform_on_subball B phi hphi d r C P hr
    δ ρ (1/64) L hδ hδr hδρ hd hbd.1 (by norm_num) hL.le hroot hrootLip
  obtain ⟨hEa,hEL⟩ := normalizedReciprocalField_uniform hn _ δ (2*L) (by positivity) hSa (fun w hw => (hSb w hw).trans (by norm_num)) hSL
  refine ⟨P,hEa,?_,?_,hSb⟩
  · rw [dimensionNormalizedMeanField_eq_scaled hn]
    simp only [actualMeanField,inverseRootField_zero B phi hphi d hbd.2.1 hbd.2.2.1 hbd.2.2.2
      P.T P.t_zero P.V P.v_zero,meanCoefficients_one,smul_zero]
  · intro w z hw hz
    convert hEL w z hw hz using 1
    · rfl
    · ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
