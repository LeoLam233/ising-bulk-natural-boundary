import IsingBulk.HT.Lie.SignedKernelDensity
import IsingBulk.HT.Lie.SignedFluxTerms
import IsingBulk.Tail.AllBranchExteriorCollisionPower

namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie IsingBulk.Tail
open scoped BigOperators

theorem signed_source_term_collision_power {n : ℕ} (σ : ℂ) (d : LocalBranchData) (ε : ℝ)
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
    ‖signedSourceValue σ T p q (-d.c₀*ε) d.thetaB w Q (radialParameter d.theta ε) u‖ ≤
      (W*A*B*H^((n+1)*n))*allBranchExteriorDiameter u^((n+1)*n-2*j)*
        signedExteriorKernelDensity σ d ε u := by
  have hb := signedSourceValue_norm σ T p q (-d.c₀*ε) d.thetaB w Q
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
      ‖signedRegularKernel σ (radialParameter d.theta ε) (fun i => originalPhase d ε (u i))‖ =
      ((W/allBranchExteriorDiameter u^(T.pole+T.cutoff.length))*A*
      (B*(H*allBranchExteriorDiameter u)^((n+1)*n-(spatialWord T.numerator).length)))*
        signedExteriorKernelDensity σ d ε u := by unfold signedExteriorKernelDensity; ring
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hc (signed_kernel_density_nonneg σ d ε u))

theorem signed_source_sum_norm {n : ℕ} (σ : ℂ) (p q : Fin (n+1)) (j : ℕ)
    (v θ : ℝ) (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (s : ℂ) (u : AngularSpace n) (B : ℝ)
    (hb : ∀ T ∈ sourceJetTerms p q j, ‖signedSourceValue σ T p q v θ w Q s u‖ ≤ B) :
    ‖((sourceJetTerms p q j).map (fun T => signedSourceValue σ T p q v θ w Q s u)).sum‖ ≤
      (3+3*(n+1):ℝ)^j*B := by
  have hh := norm_list_sum_le_length_mul
    ((sourceJetTerms p q j).map (fun T => signedSourceValue σ T p q v θ w Q s u)) B (by
      intro x hx
      obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hx
      exact hb T hT)
  simpa only [List.length_map,sourceJetTerms_length,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,
    Nat.cast_ofNat,Nat.cast_one] using hh


theorem signed_source_sum_zero_off_support {n : ℕ} (σ : ℂ)
    (p q : Fin (n+1)) (v θ : ℝ) (w : AngularSpace n → ℝ)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (j : ℕ) (s : ℂ) (u : AngularSpace n)
    (hu : u ∉ tsupport w) : signedSourceTermSum σ p q v θ w Q j s u=0 := by
  by_contra h
  exact hu (signedSourceTermSum_support_subset σ v θ p q w Q j s h)

end
end IsingBulk.HT.Lie
