import IsingBulk.Joint.Negative.FamilyPole
import IsingBulk.Anisotropic.NegativeNormalForm.UniformPoleSelection

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open scoped Topology

theorem compact_family_uniform_analytic_pole (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {P : Set E} (hP : IsCompact P)
    (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta)) (hB0 : ∀eta∈P,B (0,eta)≠0) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀eta∈P,∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<δ →
      ∃ T : Config n → ℂ, AnalyticOnNhd ℂ T (ball 0 δ) ∧ T 0=1-Complex.cos d ∧
        (∀ e v, T (permute e v)=T v) ∧
        ∀ v : Config n, ‖v‖<δ → poleEquation (familyMember B eta) phi hphi d (T v) v=0 ∧
          ‖T v-(1-Complex.cos d)‖≤C*‖v‖ ∧
          (ZeroMean v → ‖T v-(1-Complex.cos d)‖≤C*averageSquaredNorm v) := by
  obtain ⟨δ,R,C,hδ,hR,hC,hsize,hex⟩ := compact_family_dimension_uniform_pole B phi hphi hP hB hB0
  refine ⟨δ,C,hδ,hC,?_⟩
  intro eta heta n hn d hd
  let τ := 1-Complex.cos d
  let T : Config n → ℂ := fun v => if hv : ‖v‖<δ then Classical.choose (hex eta heta n hn d hd v hv) else τ
  have hs (v : Config n) (hv : ‖v‖<δ) :
      T v∈closedBall τ R ∧ poleEquation (familyMember B eta) phi hphi d (T v) v=0 ∧
      AnalyticAt ℂ (fun z : Config n × ℂ => poleEquation (familyMember B eta) phi hphi d z.2 z.1) (v,T v) ∧
      deriv (fun s => poleEquation (familyMember B eta) phi hphi d s v) (T v)≠0 ∧
      ‖T v-τ‖≤C*‖v‖ ∧ (ZeroMean v → ‖T v-τ‖≤C*averageSquaredNorm v) ∧
      ∀ s∈closedBall τ R, poleEquation (familyMember B eta) phi hphi d s v=0 → s=T v := by
    dsimp only [T]
    rw [dite_eq_left hv]
    exact Classical.choose_spec (hex eta heta n hn d hd v hv)
  have ha : AnalyticOnNhd ℂ T (ball 0 δ) := by
    apply analyticOnNhd_of_unique_scalar_roots isOpen_ball τ R
      (fun v hv => (hs v (by simpa using hv)).2.1)
      (fun v hv => (hs v (by simpa using hv)).2.2.1)
      (fun v hv => (hs v (by simpa using hv)).2.2.2.1)
    · intro v hv
      have hv' : ‖v‖<δ := by simpa using hv
      exact ((hs v hv').2.2.2.2.1).trans_lt ((mul_lt_mul_of_pos_left hv' hC).trans hsize)
    · intro v hv s hsr hsz
      exact (hs v (by simpa using hv)).2.2.2.2.2.2 s hsr hsz
  have hzero : T 0=τ := by
    have hh := (hs 0 (by simpa using hδ)).2.2.2.2.1
    simp only [norm_zero,mul_zero] at hh
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  refine ⟨T,ha,hzero,?_,?_⟩
  · intro e v
    by_cases hv : ‖v‖<δ
    · have hev : ‖permute e v‖<δ := by simpa using hv
      apply (hs v hv).2.2.2.2.2.2 (T (permute e v)) (hs _ hev).1
      have hh := (hs (permute e v) hev).2.1
      simpa only [poleEquation_permute] using hh
    · have hev : ¬‖permute e v‖<δ := by simpa using hv
      simp only [T,dite_eq_right hv,dite_eq_right hev]
  · intro v hv
    exact ⟨(hs v hv).2.1,(hs v hv).2.2.2.2.1,(hs v hv).2.2.2.2.2.1⟩

end
end IsingBulk.Joint.Negative
