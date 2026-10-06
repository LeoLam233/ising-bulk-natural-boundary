import IsingBulk.First.ReducedLocalization
import IsingBulk.First.MeanParameterDisk

/-! Actual fixed-radius representations on the source radial complex disks. -/
namespace IsingBulk.First
noncomputable section

/-- The same source radius and root represent the form factor throughout an
exterior complex disk, including every fixed-radius derivative order. -/
theorem radial_fixed_radius_representation (N : ℕ) (hN : 0 < N) {θ : ℝ}
    (hθ : 0 < Real.sin θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s : ℂ,
      ‖s-IsingBulk.Branch.radialParameter θ ε‖ < (Real.sin θ/16)*ε →
      let r := Real.exp (-(Real.sin θ/4)*ε)
      1 < ‖s‖ ∧ ScalarResidueAdmissible r s (globalRoot s) ∧
      upperFormFactor N s = doubleFormFactor N r s ∧
      upperFormFactor N s = reducedFormFactor N r (globalRoot s) ∧
      ∀ j : ℕ, iteratedDeriv j (upperFormFactor N) s =
        iteratedDeriv j (fun t => doubleFormFactor N r t) s := by
  obtain ⟨ε₀, hε₀, hε₁, hdisk⟩ := radial_disk_source_trace_margin hθ
  refine ⟨ε₀, hε₀, hε₁, ?_⟩
  intro ε hε hεlt s hs
  obtain ⟨hse, hm⟩ := hdisk ε hε hεlt s hs
  dsimp only
  have hr : 0 < Real.exp (-(Real.sin θ/4)*ε) := Real.exp_pos _
  have hr1 : Real.exp (-(Real.sin θ/4)*ε) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos hθ hε]
  have ha := globalRoot_admissible hr hr1 hm
  have he := upperFormFactor_eq_fixed_radius N hN hr hr1 hm
  refine ⟨hse, ha, he, ?_, ?_⟩
  · rw [he]
    exact residue_reduction N hN _ hr s (globalRoot s) (ha.toTuple N)
  · intro j
    exact upperFormFactor_iteratedDeriv_fixed_radius N hN j hr hr1 hm

end
end IsingBulk.First
