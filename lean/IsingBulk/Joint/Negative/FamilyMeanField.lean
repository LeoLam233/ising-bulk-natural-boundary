import IsingBulk.Joint.Negative.FamilyProjectedWitness
import IsingBulk.Anisotropic.NegativeNormalForm.UniformMeanField
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem compact_family_actual_mean_field (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {K : Set E} (hK : IsCompact K)
    (hB : ∀eta∈K,AnalyticAt ℂ B (0,eta)) (hB0 : ∀eta∈K,B (0,eta)≠0) :
    ∃ δ r C L : ℝ, 0<δ ∧ 0<r ∧ 0<C ∧ 0<L ∧ 4*δ≤r ∧
      ∀eta∈K,∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<δ →
      ∃ P : UniformProjectedWitness (familyMember B eta) phi hphi n d r C,
        AnalyticOnNhd ℂ (dimensionNormalizedMeanField (familyMember B eta) phi hphi d P.T P.V) (ball 0 δ) ∧
        dimensionNormalizedMeanField (familyMember B eta) phi hphi d P.T P.V 0=0 ∧
        (∀ w z, ‖w‖≤δ → ‖z‖≤δ →
          ‖dimensionNormalizedMeanField (familyMember B eta) phi hphi d P.T P.V w-
            dimensionNormalizedMeanField (familyMember B eta) phi hphi d P.T P.V z‖≤L*‖w-z‖) ∧
        (∀ w, ‖w‖≤δ → ‖inverseRootField (familyMember B eta) phi hphi d P.T P.V w-1‖≤1/64) := by
  obtain ⟨r,C,hr,hC,hP⟩ := compact_family_projected_witness B phi hphi hK hB hB0
  obtain ⟨ρ,L,hρ,hL,hroot,hrootLip⟩ := compact_family_root_small B phi hphi hK hB hB0 (1/64) (by norm_num)
  have htau : Tendsto (fun d : ℂ => 1-Complex.cos d) (𝓝 0) (𝓝 0) := by
    have hh : ContinuousAt (fun d : ℂ => 1-Complex.cos d) 0 := by fun_prop
    simpa using hh.tendsto
  obtain ⟨a0,ha0,hbr⟩ := compact_family_branch B phi hK hB hB0
  obtain ⟨a1,ha1,htau1⟩ := Metric.mem_nhds_iff.mp
    (htau.eventually (Metric.ball_mem_nhds (0:ℂ) (by positivity : 0<ρ/2)))
  let a := min a0 a1
  have ha : 0<a := lt_min ha0 ha1
  have hbranch (eta : E) (heta : eta∈K) (d : ℂ) (hd : ‖d‖<a) :
      ‖1-Complex.cos d‖<ρ/2 ∧ AnalyticAt ℂ (familyMember B eta) (1-Complex.cos d) ∧
      familyMember B eta (1-Complex.cos d)≠0 ∧ centralHessian (familyMember B eta) phi d≠0 :=
    ⟨by simpa using htau1 (show d∈ball (0:ℂ) a1 by simpa using hd.trans_le (min_le_right _ _)),
      hbr eta heta d (hd.trans_le (min_le_left _ _))⟩
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
  intro eta heta n hn d hd
  obtain ⟨P⟩ := hP eta heta n hn d (by linarith)
  have hbd := hbranch eta heta d (hd.trans_le hδa)
  obtain ⟨hSa,hSb,hSL⟩ := inverseRootField_uniform_on_subball (familyMember B eta) phi hphi d r C P hr
    δ ρ (1/64) L hδ hδr hδρ hd hbd.1 (by norm_num) hL.le (hroot eta heta) (hrootLip eta heta)
  obtain ⟨hEa,hEL⟩ := normalizedReciprocalField_uniform hn _ δ (2*L) (by positivity) hSa (fun w hw => (hSb w hw).trans (by norm_num)) hSL
  refine ⟨P,hEa,?_,?_,hSb⟩
  · rw [dimensionNormalizedMeanField_eq_scaled hn]
    simp only [actualMeanField,inverseRootField_zero (familyMember B eta) phi hphi d hbd.2.1 hbd.2.2.1 hbd.2.2.2
      P.T P.t_zero P.V P.v_zero,meanCoefficients_one,smul_zero]
  · intro w z hw hz
    convert hEL w z hw hz using 1
    · rfl
    · ring

end
end IsingBulk.Joint.Negative
