import IsingBulk.First.ComplementDecay
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Compact normalized-parameter bounds for the genuine transpose amplitudes. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure] [TopologicalSpace P]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Compactness gives a uniform integral norm for an actual continuous family
of amplitudes with a common compact angular support. -/
theorem uniform_compact_integral_norm_bound {K : Set P} {L : Set E}
    (hK : IsCompact K) (hL : IsCompact L) (B : P → E → ℂ)
    (hB : ContinuousOn (fun z : P × E => B z.1 z.2) (K ×ˢ L))
    (hsupp : ∀ p ∈ K, ∀ x ∉ L, B p x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, (∫ x, ‖B p x‖ ∂μ) ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (hK.prod hL).exists_bound_of_continuousOn hB
  have hfinite : μ L < ⊤ := hL.measure_lt_top
  let : IsFiniteMeasure (μ.restrict L) := ⟨by simpa using hfinite⟩
  refine ⟨μ.real L * max C₀ 0, mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _), ?_⟩
  intro p hp
  have heq : (∫ x in L, ‖B p x‖ ∂μ) = ∫ x, ‖B p x‖ ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hsupp p hp x hx, norm_zero])
  rw [← heq]
  calc
    _ ≤ ∫ _x in L, max C₀ 0 ∂μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (integrable_const _)
      filter_upwards [ae_restrict_mem hL.measurableSet] with x hx
      exact (hC₀ (p, x) ⟨hp, hx⟩).trans (le_max_left _ _)
    _ = _ := by simp [mul_comm]

/-- Uniform radial decay once continuity of the actual generated normalized
amplitude is verified on the compact parameter set. No decay bound is an input. -/
theorem uniform_nonstationary_decay {K : Set P} {L : Set E}
    (hK : IsCompact K) (hL : IsCompact L) (e : E) (g A : P → E → ℂ)
    (hg : ∀ p ∈ K, ContDiff ℝ ∞ (g p))
    (hA : ∀ p ∈ K, ContDiff ℝ ∞ (A p))
    (hsupp : ∀ p ∈ K, tsupport (A p) ⊆ L)
    (hne : ∀ p ∈ K, ∀ x ∈ tsupport (A p), phaseDirection e (g p) x ≠ 0)
    (hreal : ∀ p ∈ K, ∀ x ∈ tsupport (A p), (g p x).re ≤ 0) (q : ℕ)
    (htrans : ContinuousOn (fun z : P × E => phaseTransposeIter e (g z.1) (A z.1) q z.2)
      (K ×ˢ L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ R : ℝ, 0 < R →
      ‖∫ x, A p x * Complex.exp ((R : ℂ) * g p x) ∂μ‖ ≤ R⁻¹ ^ q * C := by
  have hcompact (p : P) (hp : p ∈ K) : HasCompactSupport (A p) :=
    hL.of_isClosed_subset (isClosed_tsupport _) (hsupp p hp)
  have hzero (p : P) (hp : p ∈ K) (x : E) (hx : x ∉ L) :
      phaseTransposeIter e (g p) (A p) q x = 0 := by
    have hr := phaseTransposeIter_regularity e (hg p hp) (hA p hp) (hcompact p hp) (hne p hp) q
    by_contra hz
    exact hx (hsupp p hp (hr.2.2 (subset_closure hz)))
  obtain ⟨C, hC, hmass⟩ := uniform_compact_integral_norm_bound (μ := μ) hK hL
    (fun p => phaseTransposeIter e (g p) (A p) q) htrans hzero
  refine ⟨C, hC, ?_⟩
  intro p hp R hR
  exact (integral_nonstationary_decay e (hg p hp) (hA p hp) (hcompact p hp)
    (hne p hp) (hreal p hp) q R hR).trans
    (mul_le_mul_of_nonneg_left (hmass p hp) (by positivity))

end
end IsingBulk.First
