import IsingBulk.HT.Tail.SignedExteriorNegativeCover
import IsingBulk.Tail.AllBranchExteriorNegativeCover

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Lie IsingBulk.Tail IsingBulk.HT.Lie Set MeasureTheory

/-- The negative-region bound has a chart radius before epsilon and particle
number. All microcore and attenuation data are derived internally. -/
theorem signed_allBranchExterior_negative_kernel_integral_uniform {d : LocalBranchData} (B : BranchEstimates d) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ξ : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ∀ n : ℕ, ∀ p q : Fin (n+1), p ≠ q → ∀ R a : ℝ, 0 ≤ R → R ≤ r → 0 < a →
      IntegrableOn (signedExteriorKernelDensity (Complex.exp (Complex.I*(ξ:ℂ))) d ε) (allBranchExteriorNegativeRegion p R a) ∧
      (∫ u in allBranchExteriorNegativeRegion p R a, signedExteriorKernelDensity (Complex.exp (Complex.I*(ξ:ℂ))) d ε u) ≤
        allBranchExteriorNegativeCost B ε R a c C (n+1) := by
  obtain ⟨c,C,hc,hC,hint⟩ := signed_allBranchExterior_negative_region_integral B
  obtain ⟨r₀,hr₀,hchart⟩ := original_microcore_chart d
  let R₀ := min r₀ (min B.r (min B.ε₀ (min Real.pi d.c₀⁻¹)))
  have hR₀ : 0 < R₀ := lt_min hr₀ (lt_min B.r_pos (lt_min B.ε₀_pos (lt_min Real.pi_pos (inv_pos.mpr d.c₀_pos))))
  let r := R₀/2
  have hr : 0 < r := half_pos hR₀
  have hsmall : r < r₀ ∧ r < B.r ∧ r < B.ε₀ ∧ r < Real.pi ∧ r < d.c₀⁻¹ := by
    have hh : r < R₀ := half_lt_self hR₀
    simpa only [R₀,lt_min_iff] using hh
  refine ⟨c,C,r,hc,hC,hr,?_⟩
  intro ξ ε hε hεr n p q hpq R a hR hRr ha
  have hα : d.c₀*ε ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hεr.trans hsmall.2.2.2.2.le) d.c₀_pos.le
    rwa [mul_inv_cancel₀ d.c₀_pos.ne'] at hh
  apply hint ξ n ε R a hε (hεr.trans hsmall.2.2.1.le) hR (hRr.trans hsmall.2.1.le)
    (hRr.trans hsmall.2.2.2.1.le) hα ha ?_ p q hpq
  intro u hu
  exact hchart ε hε (hεr.trans_lt hsmall.1) n u
    (fun i => (abs_le.mpr ⟨hu.1 i,hu.2 i⟩).trans_lt (hRr.trans_lt hsmall.1))

/-- Fixed phase convenience form of the uniform endpoint. -/
theorem signed_allBranchExterior_negative_kernel_integral (ξ : ℝ) {d : LocalBranchData} (B : BranchEstimates d) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ∀ n : ℕ, ∀ p q : Fin (n+1), p ≠ q → ∀ R a : ℝ, 0 ≤ R → R ≤ r → 0 < a →
      IntegrableOn (signedExteriorKernelDensity (Complex.exp (Complex.I*(ξ:ℂ))) d ε) (allBranchExteriorNegativeRegion p R a) ∧
      (∫ u in allBranchExteriorNegativeRegion p R a, signedExteriorKernelDensity (Complex.exp (Complex.I*(ξ:ℂ))) d ε u) ≤
        allBranchExteriorNegativeCost B ε R a c C (n+1) := by
  obtain ⟨c,C,r,hc,hC,hr,hmain⟩ := signed_allBranchExterior_negative_kernel_integral_uniform B
  exact ⟨c,C,r,hc,hC,hr,hmain ξ⟩

/-- Physical negative sign, with exactly the LT negative-region cost and
all spectators retained. The phase offset is fixed at pi, not differentiated. -/
theorem negative_allBranchExterior_kernel_integral {d : LocalBranchData} (B : BranchEstimates d) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ∀ n : ℕ, ∀ p q : Fin (n+1), p ≠ q → ∀ R a : ℝ, 0 ≤ R → R ≤ r → 0 < a →
      IntegrableOn (signedExteriorKernelDensity (-1) d ε) (allBranchExteriorNegativeRegion p R a) ∧
      (∫ u in allBranchExteriorNegativeRegion p R a, signedExteriorKernelDensity (-1) d ε u) ≤
        allBranchExteriorNegativeCost B ε R a c C (n+1) := by
  simpa only [mul_comm Complex.I (Real.pi:ℂ),Complex.exp_pi_mul_I] using
    signed_allBranchExterior_negative_kernel_integral Real.pi B

end
end IsingBulk.HT.Tail
