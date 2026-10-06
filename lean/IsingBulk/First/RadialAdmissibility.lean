import IsingBulk.First.GlobalResidueRoot
import IsingBulk.Analysis.BranchRadial
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Source radial radii are genuinely admissible on the whole y circle.
All constants are chosen before epsilon; radius remains fixed in s derivatives. -/
namespace IsingBulk.First
noncomputable section
open Filter Set
open scoped Topology

def radialDampingMargin (θ c ε : ℝ) : ℝ :=
  (2*ε-ε^2/(1+ε))*Real.sin θ - (Real.exp (c*ε)-Real.exp (-c*ε))

theorem radialDampingMargin_zero (θ c : ℝ) : radialDampingMargin θ c 0 = 0 := by
  simp [radialDampingMargin]

theorem radialDampingMargin_hasDerivAt (θ c : ℝ) :
    HasDerivAt (radialDampingMargin θ c) (2*Real.sin θ-2*c) 0 := by
  have hp : HasDerivAt (fun ε : ℝ => (2*ε-ε^2/(1+ε))*Real.sin θ) (2*Real.sin θ) 0 := by
    convert (((hasDerivAt_id (0:ℝ)).const_mul 2).sub
      (((hasDerivAt_id (0:ℝ)).pow 2).div ((hasDerivAt_id (0:ℝ)).const_add 1) (by norm_num))).mul_const
      (Real.sin θ) using 1 <;> norm_num
  have he : HasDerivAt (fun ε : ℝ => Real.exp (c*ε)-Real.exp (-c*ε)) (2*c) 0 := by
    convert! (((hasDerivAt_id (0:ℝ)).const_mul c).exp).sub
      (((hasDerivAt_id (0:ℝ)).const_mul (-c)).exp) using 1
    simp
    ring
  exact hp.sub he

theorem radialDampingMargin_linear {θ c : ℝ} (_hθ : 0 < Real.sin θ)
    (hc : c < Real.sin θ/2) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Real.sin θ*ε < radialDampingMargin θ c ε := by
  have ht := (radialDampingMargin_hasDerivAt θ c).tendsto_slope_zero_right
  have hh : Real.sin θ < 2*Real.sin θ-2*c := by linarith
  have hb := ht.eventually (Ioi_mem_nhds hh)
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, Real.sin θ*ε < radialDampingMargin θ c ε := by
    filter_upwards [hb, self_mem_nhdsWithin] with ε hε hεpos
    simp only [zero_add, radialDampingMargin_zero, sub_zero, smul_eq_mul] at hε
    have heps : 0 < ε := hεpos
    have hm := mul_lt_mul_of_pos_left hε heps
    simpa only [← mul_assoc, mul_inv_cancel₀ heps.ne', one_mul, mul_comm ε (Real.sin θ)] using hm
  obtain ⟨δ, hδ, heδ⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  refine ⟨min δ 1, lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  intro ε hε hεδ
  exact heδ ⟨hε, hεδ.trans_le (min_le_left _ _)⟩

theorem radialRadius_parameter_margin {θ c ε : ℝ} (hε : 0 < ε)
    (hlin : Real.sin θ*ε < radialDampingMargin θ c ε) :
    (Real.exp (-c*ε))⁻¹-Real.exp (-c*ε)+Real.sin θ*ε <
      (sourceS (IsingBulk.Branch.radialParameter θ ε)).im := by
  have ht := (IsingBulk.Branch.radial_trace_components θ ε (by linarith)).2
  change (sourceS (IsingBulk.Branch.radialParameter θ ε)).im =
    (2*ε-ε^2/(1+ε))*Real.sin θ at ht
  have hi : (Real.exp (-c*ε))⁻¹=Real.exp (c*ε) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hi, ht]
  unfold radialDampingMargin at hlin
  linarith

/-- Existence of the actual source radius and its global interior root on every
selected positive radial approach. No compactness or model root is assumed. -/
theorem radial_globalRoot_admissible {θ : ℝ} (hθ : 0 < Real.sin θ) :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ScalarResidueAdmissible (Real.exp (-c*ε)) (IsingBulk.Branch.radialParameter θ ε)
        (globalRoot (IsingBulk.Branch.radialParameter θ ε)) := by
  let c : ℝ := Real.sin θ/4
  have hc : 0 < c := by dsimp [c]; positivity
  have hcsmall : c < Real.sin θ/2 := by dsimp [c]; linarith
  obtain ⟨ε₀, hε₀, hε₁, hb⟩ := radialDampingMargin_linear hθ hcsmall
  refine ⟨c, ε₀, hc, hε₀, hε₁, ?_⟩
  intro ε hε hεlt
  apply globalRoot_admissible (Real.exp_pos _)
    (by rw [Real.exp_lt_one_iff]; nlinarith [mul_pos hc hε])
  have hh := radialRadius_parameter_margin hε (hb ε hε hεlt)
  linarith [mul_pos hθ hε]

end
end IsingBulk.First
