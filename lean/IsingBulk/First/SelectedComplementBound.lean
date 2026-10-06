import IsingBulk.First.CompatibleComplement
import IsingBulk.First.ComplementGlobalBound
import IsingBulk.First.AngularReindex
import IsingBulk.First.ShapeLimitTransfer

/-! The actual compatible complementary term is bounded and negligible at
the source square-root scale. Every finite-cover hypothesis is instantiated. -/
namespace IsingBulk.First
noncomputable section
open Complex Filter Set IsingBulk.Branch
open scoped Topology

theorem selected_compatible_complement_bounded {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    {U : Set (Fin (2*p-1) → ℝ)}
    (c : CompatibleYCutoffData (2*p-1) (PrimeFamily.angle p a) (PrimeFamily.angle p b) U) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ‖(deriv^[j] (fun s => localizedDoubleFormFactor (2*p-1+1)
          (sourceRadialPair (selectedOrderedChart ha hb).theta epsilon).1 s
          (fun u => c.remainder u.2)))
          (sourceRadialPair (selectedOrderedChart ha hb).theta epsilon).2‖ ≤ C := by
  have hN : 2*p-1+1=2*p := by have := hp.pos; omega
  have hW := selected_compatible_complement_good hp c
  dsimp only at hW
  have hS : sourceS (exp (((selectedOrderedChart ha hb).theta:ℂ)*I)) =
      ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ) := by
    simpa only [sourceS,PrimeFamily.selectedPoint,selectedOrderedChart,Complex.ofReal_mul,Complex.ofReal_ofNat] using
      PrimeFamily.selectedPoint_relation ha hb
  obtain ⟨e,he,hbound⟩ := selected_complement_global_bound hp hp11 ha hb
    (selectedOrderedChart ha hb).theta (selectedOrderedChart ha hb).sin_theta_pos hS
    (compatibleDoubleComplement hN c) hW.1 hW.2.1 hW.2.2
  refine ⟨e,he,?_⟩
  intro j
  obtain ⟨C,hC,hB⟩ := hbound j
  refine ⟨C,hC,?_⟩
  intro epsilon heps hee
  have h := hB epsilon heps hee
  rw [← iteratedDeriv_eq_iterate] at h ⊢
  change ‖iteratedDeriv j (fun s => localizedDoubleFormFactor (2*p)
    (sourceRadialPair (selectedOrderedChart ha hb).theta epsilon).1 s
    (fun u => reindexYWeight hN c.remainder u.2))
    (sourceRadialPair (selectedOrderedChart ha hb).theta epsilon).2‖ ≤ C at h
  rw [localizedDoubleFormFactor_iteratedDeriv_y_reindex] at h
  exact h

/-- A genuinely bounded error is little-o of the source inverse-square-root
scale; this lemma does not manufacture any boundedness premise for an integral. -/
theorem bounded_radial_term_isLittleO {f : ℝ → ℂ} {C e : ℝ} (he : 0 < e)
    (hb : ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ e → ‖f epsilon‖ ≤ C) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ)) f (fun epsilon => (Real.sqrt epsilon:ℂ)⁻¹) := by
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hbounded : IsBoundedUnder (· ≤ ·) (𝓝[>] (0:ℝ)) (norm ∘ f) := by
    refine ⟨C,eventually_map.mpr ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds he).filter_mono nhdsWithin_le_nhds] with epsilon hp hsmall
    exact hb epsilon hp hsmall.le
  have hz : Tendsto (fun epsilon : ℝ => Real.sqrt epsilon • f epsilon)
      (𝓝[>] 0) (𝓝 (0:ℂ)) := by
    simpa only [Pi.smul_apply] using!
      NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hsqrt hbounded
  simpa only [mul_zero,sub_zero] using normalized_sqrt_limit_isLittleO hz

end
end IsingBulk.First
