import IsingBulk.Joint.Negative.FamilyPoleComparison
import IsingBulk.Joint.Negative.FamilyPoleSelection

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open scoped Topology

/-- A common-domain actual analytic pole with prescribed small image and Lipschitz constant. -/
theorem compact_family_small_lipschitz_pole (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {P : Set E} (hP : IsCompact P)
    (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta)) (hB0 : ∀eta∈P,B (0,eta)≠0)
    (κ η : ℝ) (hκ : 0<κ) (hη : 0<η) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀e∈P,∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<δ →
      ∃ T : Config n → ℂ, AnalyticOnNhd ℂ T (ball 0 δ) ∧ T 0=1-Complex.cos d ∧
        (∀ e v, T (permute e v)=T v) ∧
        (∀ v : Config n, ‖v‖<δ → poleEquation (familyMember B e) phi hphi d (T v) v=0 ∧
          ‖T v‖<η ∧ ‖T v-(1-Complex.cos d)‖≤C*‖v‖ ∧
          (ZeroMean v → ‖T v-(1-Complex.cos d)‖≤C*averageSquaredNorm v)) ∧
        (∀ v w : Config n, ‖v‖<δ → ‖w‖<δ → ‖T v-T w‖≤κ*‖v-w‖) := by
  obtain ⟨δ₀,C,hδ₀,hC,hex⟩ := compact_family_uniform_analytic_pole B phi hphi hP hB hB0
  obtain ⟨ρ,hρ,hcompare⟩ := compact_family_pole_small_comparison B phi hphi hP hB hB0 κ hκ
  let a := min η ρ
  have ha : 0<a := lt_min hη hρ
  have htau : ∀ᶠ d : ℂ in 𝓝 0, ‖1-Complex.cos d‖<a/2 :=
    (show ContinuousAt (fun d : ℂ => ‖1-Complex.cos d‖) 0 by fun_prop).eventually_lt
      continuousAt_const (by simpa using half_pos ha)
  obtain ⟨r,hr,hτ⟩ := Metric.mem_nhds_iff.mp htau
  let δ := min δ₀ (min ρ (min r (a/(2*(C+1)))))
  have hδ : 0<δ := lt_min hδ₀ (lt_min hρ (lt_min hr (by positivity)))
  have hδ0 : δ≤δ₀ := min_le_left _ _
  have hδρ : δ≤ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ≤r := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδC : δ≤a/(2*(C+1)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ,C,hδ,hC,?_⟩
  intro e he n hn d hd
  obtain ⟨T,hT,hT0,hTeq,hTs⟩ := hex e he n hn d (hd.trans_le hδ0)
  have hτa : ‖1-Complex.cos d‖<a/2 := hτ (show d∈ball (0:ℂ) r by simpa using hd.trans_le hδr)
  have hTa (v : Config n) (hv : ‖v‖<δ) : ‖T v‖<a := by
    have hh := (hTs v (hv.trans_le hδ0)).2.1
    have hcv := mul_lt_mul_of_pos_left hv hC
    have hsize := (le_div_iff₀ (show 0<2*(C+1) by positivity)).mp hδC
    have htri := norm_le_norm_sub_add (T v) (1-Complex.cos d)
    nlinarith
  refine ⟨T,hT.mono (ball_subset_ball hδ0),hT0,hTeq,?_,?_⟩
  · intro v hv
    have hh := hTs v (hv.trans_le hδ0)
    exact ⟨hh.1,(hTa v hv).trans_le (min_le_left _ _),hh.2⟩
  · intro v w hv hw
    exact hcompare e he n hn d (hd.trans_le hδρ) v w (hv.trans_le hδρ) (hw.trans_le hδρ)
      (T v) (T w) ((hTa v hv).trans_le (min_le_right _ _))
      ((hTa w hw).trans_le (min_le_right _ _))
      (hTs v (hv.trans_le hδ0)).1 (hTs w (hw.trans_le hδ0)).1

end
end IsingBulk.Joint.Negative
