import IsingBulk.First.PeriodicBump
import IsingBulk.First.PeriodicBoxIntegral

/-! Exact torus/local-lift integral equality, including arbitrary seam centers.
The fundamental box is shifted first; only then is compact support used to
extend the actual local density to the whole Euclidean angular space. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory
open scoped ContDiff

theorem periodicizeBump_integral (N : ℕ) (c : Fin N → ℝ) (w : (Fin N → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) (hsmall : ∀ x, w x ≠ 0 → ∀ i, |x i-c i| ≤ 1/2)
    (F : (Fin N → ℝ) → ℂ) (hF : Continuous F) (hper : CoordinatePeriodic N F) :
    (∫ x in angleBox N, (periodicizeBump c w x : ℂ)*F x) = ∫ x : Fin N → ℝ, (w x:ℂ)*F x := by
  let f : (Fin N → ℝ) → ℂ := fun x => (periodicizeBump c w x:ℂ)*F x
  let d : Fin N → ℝ := fun i => c i-Real.pi
  have hfc : Continuous f :=
    (Complex.continuous_ofReal.comp (periodicizeBump_contDiff c w hw hsmall).continuous).mul hF
  have hfp : CoordinatePeriodic N f := by
    intro x i
    dsimp only [f]
    rw [periodicizeBump_update_period, hper x i]
  calc
    _ = ∫ x in angleBox N, f (fun i => x i+d i) := (angleBox_integral_shift N f hfc hfp d).symm
    _ = ∫ x in angleBox N, (w (fun i => x i+d i):ℂ)*F (fun i => x i+d i) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      dsimp only [f]
      rw [periodicizeBump_eq_on_centeredBox c w hsmall]
      intro i
      have hlo : 0 ≤ x i := hx.1 i
      have hhi : x i ≤ 2*Real.pi := hx.2 i
      dsimp only [d]
      constructor <;> linarith
    _ = ∫ x : Fin N → ℝ, (w (fun i => x i+d i):ℂ)*F (fun i => x i+d i) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : w (fun i => x i+d i)=0 := by
        by_contra hn
        apply hx
        constructor <;> intro i
        · have hh := abs_le.mp (hsmall (fun i => x i+d i) hn i)
          dsimp only [d] at hh
          linarith [hh.1,Real.pi_gt_three]
        · have hh := abs_le.mp (hsmall (fun i => x i+d i) hn i)
          dsimp only [d] at hh
          linarith [hh.2,Real.pi_gt_three]
      rw [hz,Complex.ofReal_zero,zero_mul]
    _ = _ := integral_add_right_eq_self (fun x => (w x:ℂ)*F x) d

/-- Both sides genuinely exist under the stated smooth compact-bump and
continuous-density conditions. -/
theorem periodicizeBump_integrability (N : ℕ) (c : Fin N → ℝ) (w : (Fin N → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsmall : ∀ x, w x ≠ 0 → ∀ i, |x i-c i| ≤ 1/2)
    (F : (Fin N → ℝ) → ℂ) (hF : Continuous F) :
    IntegrableOn (fun x => (periodicizeBump c w x:ℂ)*F x) (angleBox N) ∧
      Integrable (fun x => (w x:ℂ)*F x) := by
  have hW := Complex.continuous_ofReal.comp (periodicizeBump_contDiff c w hw hsmall).continuous
  have hraw := (Complex.continuous_ofReal.comp hw.continuous).mul hF
  have hcraw : HasCompactSupport (fun x => (w x:ℂ)*F x) := by
    exact (hc.comp_left (by simp : ((0:ℝ):ℂ)=0)).mul_right
  exact ⟨(hW.mul hF).continuousOn.integrableOn_compact isCompact_Icc,
    hraw.integrable_of_hasCompactSupport hcraw⟩

end
end IsingBulk.First
