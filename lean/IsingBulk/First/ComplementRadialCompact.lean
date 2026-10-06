import IsingBulk.First.ComplementSourceUniform
import IsingBulk.First.ComplementActiveChart
import IsingBulk.First.MeanParameterDisk

/-! The compact parameter family is constructed from the actual source radial
curve, normalized positive auxiliary simplex, and inverse auxiliary radius. -/
namespace IsingBulk.First
noncomputable section
open Set Filter
open scoped Topology ContDiff
attribute [local fun_prop] source_complexOfReal_contDiff

def sourceRadialPair (θ ε : ℝ) : ℝ × ℂ :=
  (Real.exp (-(Real.sin θ/4)*ε), IsingBulk.Branch.radialParameter θ ε)

def sourceRadialIBPParameter {N : ℕ} (J : Finset (SingularFactorIndex N))
    (θ ε : ℝ) (η : J → ℝ) (t : ℝ) : SourceIBPParameter J :=
  (sourceRadialPair θ ε,(η,t))

theorem sourceRadialPair_continuous (θ : ℝ) : Continuous (sourceRadialPair θ) := by
  unfold sourceRadialPair IsingBulk.Branch.radialParameter
  fun_prop

@[simp] theorem sourceRadialPair_zero (θ : ℝ) :
    sourceRadialPair θ 0 = (1,Complex.exp ((θ : ℂ)*Complex.I)) := by
  simp [sourceRadialPair, IsingBulk.Branch.radialParameter]

/-- The closed radial family has the required actual damping, including its
unit-circle endpoint. The allowed interval is independent of derivative order. -/
theorem sourceRadialPair_closed_damping {θ : ℝ} (hθ : 0 < Real.sin θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Icc 0 ε₀,
      0 < (sourceRadialPair θ ε).1 ∧ (sourceRadialPair θ ε).1 ≤ 1 ∧
      (sourceRadialPair θ ε).2 ≠ 0 ∧
      (sourceRadialPair θ ε).1⁻¹-(sourceRadialPair θ ε).1 ≤
        (sourceS (sourceRadialPair θ ε).2).im := by
  obtain ⟨d,hd,_,hm⟩ := radial_disk_source_trace_margin hθ
  refine ⟨d/2,by positivity,?_⟩
  intro ε hε
  have hεd : ε < d := by linarith [hε.2]
  have hr : 0 < (sourceRadialPair θ ε).1 := Real.exp_pos _
  have hr1 : (sourceRadialPair θ ε).1 ≤ 1 := by
    change Real.exp (-(Real.sin θ/4)*ε) ≤ 1
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hε.1
  have hs : (sourceRadialPair θ ε).2 ≠ 0 := by
    unfold sourceRadialPair IsingBulk.Branch.radialParameter
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith [hε.1])) (Complex.exp_ne_zero _)
  refine ⟨hr,hr1,hs,?_⟩
  rcases eq_or_lt_of_le hε.1 with he | he
  · subst ε
    rw [sourceRadialPair_zero]
    have ht := (IsingBulk.Branch.radial_trace_components θ 0 (by norm_num)).2
    change (sourceS (IsingBulk.Branch.radialParameter θ 0)).im = _ at ht
    simpa [IsingBulk.Branch.radialParameter, sourceS] using ht.ge
  · exact (hm ε he hεd (IsingBulk.Branch.radialParameter θ ε)
      (by simpa using mul_pos (show 0 < Real.sin θ/16 by positivity) he)).2.le

/-- Compactness of the actual parameter image, without replacing the source
radial curve or imposing a generated-amplitude boundedness hypothesis. -/
theorem sourceRadialIBPParameter_compact {N : ℕ} (J : Finset (SingularFactorIndex N))
    (θ ε₀ : ℝ) : IsCompact
      ((fun z : ℝ × (J → ℝ) × ℝ => sourceRadialIBPParameter J θ z.1 z.2.1 z.2.2) ''
        (Icc 0 ε₀ ×ˢ (auxiliarySimplex J ×ˢ Icc 0 1))) := by
  apply (isCompact_Icc.prod ((auxiliarySimplex_isCompact J).prod isCompact_Icc)).image
  exact ((sourceRadialPair_continuous θ).comp continuous_fst).prodMk
    (continuous_snd.fst.prodMk continuous_snd.snd)

end
end IsingBulk.First
