import IsingBulk.AnisoF002.C03.NegativeInnerModelComparison
import IsingBulk.AnisoF002.C03.NegativeMiddleErrorScales
import IsingBulk.AnisoF002.C03.NegativeResonantReindex

/-!
# Every actual resonant middle coefficient is attached to the model

The particle window is the complete finite set from the frozen proof.
Its lower bound discharges every eventual-particle and radius gate;
its upper bound discharges the common derivative-order and error gates.
The family is quantified after one shared cutoff and a uniform threshold.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

theorem middle_window_order_gate {M N : ℝ} {j : ℕ}
    (hM : 0 ≤ M) (hlog : 0 < Real.log j) (hlarge : M ^ 2 ≤ Real.log j)
    (hwindow : N ^ 2 ≤ highParticleThreshold j) : M * N ^ 2 ≤ (j : ℝ) := by
  have hs : 0 < Real.sqrt (Real.log j) := Real.sqrt_pos.mpr hlog
  have hMle : M ≤ Real.sqrt (Real.log j) := by
    have hh := Real.sq_sqrt hlog.le
    nlinarith
  have hw := (le_div_iff₀ hs).mp hwindow
  have hm := mul_le_mul_of_nonneg_right hMle (sq_nonneg N)
  nlinarith

theorem exists_complete_actual_middle_attachment {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) {a p : ℕ} (hp : Odd p) (hcop : a.Coprime p)
    (hphase : φ = 2 * Real.pi * a / p) :
    ∃ s0 : ℝ, 0 < s0 ∧ ‖Complex.sqrt (B 0) / b 0‖ = 1 ∧
      ∀ s : ℝ, 0 < s → s ≤ s0 → ∀ r Mi ki : ℝ, 0 < r → 0 ≤ Mi →
      ∃ T : ℝ, 0 < T ∧
        ∀ D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) r s Mi ki,
        ∀ j : ℕ, T ≤ Real.log (j : ℝ) → ∀ q ∈ resonantMiddleIndices p j,
        let N := resonantParticleCount p q
        let model := modelCoefficient N j (B (windingTau N : ℂ))
          (firstWindingCurvature N (B (windingTau N : ℂ)) (Real.cos φ) (Real.sin φ))
          (Real.sin φ) (windingTau N)
        ‖innerCyclePoleCoefficient (D (resonantOddIndex p q)) j -
            (Complex.sqrt (B 0) / b 0) * model‖ ≤ ‖model‖ / 16 := by
  obtain ⟨s0, M, E, hs0, hM, hE, hζ, hcompare⟩ :=
    exists_actual_inner_model_comparison hb hB hφ hπ hBi hbsq
  refine ⟨s0, hs0, hζ, ?_⟩
  intro s hs hss r Mi ki hr hMi
  obtain ⟨L, hL⟩ := eventually_atTop.mp (hcompare s hs hss r Mi ki hr hMi)
  let T := max 1 (max (M ^ 2) (max ((64 * E) ^ 4) (2 * (L : ℝ) + 1)))
  have hT : 0 < T := (by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _)
  refine ⟨T, hT, ?_⟩
  intro D j hj q hq
  have hlog1 : 1 ≤ Real.log (j : ℝ) := (le_max_left _ _).trans hj
  have hlog : 0 < Real.log (j : ℝ) := by linarith
  have hLM : M ^ 2 ≤ Real.log (j : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hj)
  have hLE : (64 * E) ^ 4 ≤ Real.log (j : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hj))
  have hLL : 2 * (L : ℝ) + 1 ≤ Real.log (j : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hj))
  have hw := (mem_resonantMiddleIndices_iff hp.pos hlog1).mp hq
  have hNid := resonantOddIndex_particle hp q
  have hindex : L ≤ resonantOddIndex p q := by
    have hh := hLL.trans hw.1
    rw [← hNid] at hh
    have hnat : 2 * L + 1 ≤ 2 * resonantOddIndex p q + 1 := by exact_mod_cast hh
    omega
  have horder := middle_window_order_gate (by linarith : 0 ≤ M) hlog hLM hw.2
  have hres : Complex.exp (-(((2 * resonantOddIndex p q + 1 : ℕ) : ℂ) *
      ((φ : ℂ) * Complex.I))) = 1 := by
    rw [hNid, hphase]
    apply (rational_negative_phase_resonance_iff hp.pos.ne' hcop _).mpr
    exact ⟨2 * q + 1, rfl⟩
  have hc := hL (resonantOddIndex p q) hindex (D (resonantOddIndex p q)) j hres
    (by simpa only [hNid] using horder) (by simpa only [hNid] using hw.1)
  dsimp only at hc ⊢
  have herror : E * ((resonantParticleCount p q : ℕ) : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ 1 / 64 := by
    simpa only [Nat.cast_add, Nat.cast_one] using complete_middle_first_error_small hE.le
      (Nat.cast_nonneg (resonantParticleCount p q)) hlog hw.2 hLE
  have hc' : ‖innerCyclePoleCoefficient (D (resonantOddIndex p q)) j -
      (Complex.sqrt (B 0) / b 0) * modelCoefficient (resonantParticleCount p q) j
        (B (windingTau (resonantParticleCount p q) : ℂ))
        (firstWindingCurvature (resonantParticleCount p q)
          (B (windingTau (resonantParticleCount p q) : ℂ)) (Real.cos φ) (Real.sin φ))
        (Real.sin φ) (windingTau (resonantParticleCount p q))‖ ≤
      (E * (resonantParticleCount p q : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ) + 1 / 32) *
        ‖modelCoefficient (resonantParticleCount p q) j (B (windingTau (resonantParticleCount p q) : ℂ))
          (firstWindingCurvature (resonantParticleCount p q)
            (B (windingTau (resonantParticleCount p q) : ℂ)) (Real.cos φ) (Real.sin φ))
          (Real.sin φ) (windingTau (resonantParticleCount p q))‖ := by
    simpa only [hNid] using hc
  apply hc'.trans
  have hfactor : E * (resonantParticleCount p q : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ) + 1 / 32 ≤ 1 / 16 := by
    linarith
  simpa only [one_div_mul_eq_div] using mul_le_mul_of_nonneg_right hfactor
    (norm_nonneg (modelCoefficient (resonantParticleCount p q) j (B (windingTau (resonantParticleCount p q) : ℂ))
      (firstWindingCurvature (resonantParticleCount p q)
        (B (windingTau (resonantParticleCount p q) : ℂ)) (Real.cos φ) (Real.sin φ))
      (Real.sin φ) (windingTau (resonantParticleCount p q))))

end
end IsingBulk.AnisoF002.NegativeHT
