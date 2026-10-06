import IsingBulk.Tail.AllBranchExteriorTermNorm
import IsingBulk.Tail.AllBranchExteriorKernelContinuity

/-! The actual Lie filtration leaves a collision power after every denominator
and spatial differentiation loss. This uses the recovered two-j budget. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie
open scoped BigOperators

theorem allBranchExterior_collision_power_budget (m l s P j : ℕ)
    (horder : m+l+s ≤ 2*j) (hP : 2*j ≤ P) (D H W A B : ℝ)
    (hD : 0 < D) (hD1 : D ≤ 1) (hH : 1 ≤ H) (hW : 0 ≤ W) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (W/D^(m+l))*A*(B*(H*D)^(P-s)) ≤ W*A*B*H^P*D^(P-2*j) := by
  have he : P-s=(P-(m+l+s))+(m+l) := by omega
  have hden : D^(m+l) ≠ 0 := pow_ne_zero _ hD.ne'
  have hid : (W/D^(m+l))*A*(B*(H*D)^(P-s)) = W*A*B*H^(P-s)*D^(P-(m+l+s)) := by
    rw [mul_pow,show D^(P-s)=D^(P-(m+l+s))*D^(m+l) by rw [← pow_add,he]]
    field_simp
  rw [hid]
  have hpowH : H^(P-s) ≤ H^P := pow_le_pow_right₀ hH (Nat.sub_le P s)
  have hpowD : D^(P-(m+l+s)) ≤ D^(P-2*j) :=
    pow_le_pow_of_le_one hD.le hD1 (by omega)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hpowH (by positivity)
  · exact hpowD
  · exact pow_nonneg hD.le _
  · positivity

theorem allBranchExterior_source_term_collision_power {n : ℕ} (d : LocalBranchData) (ε : ℝ)
    (p q : Fin (n+1)) (j : ℕ) (T : SourceJetTerm (n+1)) (hT : T ∈ sourceJetTerms p q j)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (u : AngularSpace n)
    (hp : MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u)
    (hP : 2*j ≤ (n+1)*n) (hdiam : 0 < allBranchExteriorDiameter u) (hdiam1 : allBranchExteriorDiameter u ≤ 1)
    (H W A B : ℝ) (hH : 1 ≤ H) (hW : 0 ≤ W) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : ‖cutoffJet T.cutoff w u‖/
      ‖selectedDifferenceCLM p q (radialParameter d.theta ε,
        chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u)‖^T.pole ≤
          W/allBranchExteriorDiameter u^(T.pole+T.cutoff.length))
    (hreg : ‖T.regularPart (radialParameter d.theta ε,chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u)‖ ≤ A)
    (hnum : ‖numeratorJet T.numerator Q
      (radialParameter d.theta ε,chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u)‖ ≤
        B*(H*allBranchExteriorDiameter u)^((n+1)*n-(spatialWord T.numerator).length)) :
    ‖T.sourceValue p q (-d.c₀*ε) d.thetaB w Q (radialParameter d.theta ε) u‖ ≤
      (W*A*B*H^((n+1)*n))*allBranchExteriorDiameter u^((n+1)*n-2*j)*
        allBranchExteriorKernelDensity d ε u := by
  have hb := allBranchExterior_sourceTerm_norm T p q (-d.c₀*ε) d.thetaB w Q
    (radialParameter d.theta ε) u (W/allBranchExteriorDiameter u^(T.pole+T.cutoff.length)) A
    (B*(H*allBranchExteriorDiameter u)^((n+1)*n-(spatialWord T.numerator).length))
    (by positivity) hA hw hreg hnum
  have horders := (sourceJetTerms_valid p q j T hT).1
  have hc := allBranchExterior_collision_power_budget T.pole T.cutoff.length
    (spatialWord T.numerator).length ((n+1)*n) j horders hP (allBranchExteriorDiameter u) H W A B
    hdiam hdiam1 hH hW hA hB
  have hr (i : Fin (n+1)) : 0 < (originalW d ε (u i)).re := by
    simpa only [original_chartW_eq] using hp.re_pos i
  have hi (i : Fin (n+1)) : 0 < (originalW d ε (u i)).im := by
    simpa only [original_chartW_eq] using hp.im_pos i
  rw [original_chartJacobian_norm d ε u hr hi,original_chartMap_eq] at hb
  have he : ((W/allBranchExteriorDiameter u^(T.pole+T.cutoff.length))*A*
      (B*(H*allBranchExteriorDiameter u)^((n+1)*n-(spatialWord T.numerator).length)))*
      (∏ i, ‖deriv (originalPhase d ε) (u i)‖)/
      ‖regularKernel (radialParameter d.theta ε) (fun i => originalPhase d ε (u i))‖ =
      ((W/allBranchExteriorDiameter u^(T.pole+T.cutoff.length))*A*
      (B*(H*allBranchExteriorDiameter u)^((n+1)*n-(spatialWord T.numerator).length)))*
        allBranchExteriorKernelDensity d ε u := by unfold allBranchExteriorKernelDensity; ring
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hc (allBranchExterior_kernel_density_nonneg d ε u))

end
end IsingBulk.Tail
