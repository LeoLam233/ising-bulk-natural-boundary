import IsingBulk.Tail.CompactLogYAbsoluteJets
import IsingBulk.Tail.ParameterUniformJets
import IsingBulk.Tail.SelectedPairScaledJets

/-! Uniform joint jets of the literal freezing coefficients. The constants
precede particle number and the full coupled occupancy is differentiated. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem actual_compact_freezing_coefficient_jets (d : LocalBranchData)
    (f : SelectorFunctions) (hf : RegularSelector f) (hp1 : ∀ x, f.p x ≤ 1)
    {a b : ℝ} (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ| < 1)
    (J : ℕ) : ∃ r C : ℝ, 0 < r ∧ 1 ≤ C ∧
      ∀ N : ℕ, 0 < N → ∀ eps τ lam : ℝ, 0 < eps → 0 ≤ τ → τ ≤ 1 →
      0 ≤ lam → lam ≤ 1 → ∀ s : ℂ,
      s ∈ dampingDomain (Real.exp (-d.c₀*eps)) →
      ‖s-radialParameter d.theta 0‖+d.c₀*eps+2*lam ≤ r →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc a b) →
      (∀ i, RealScaledJetBound
        (fun q : ℂ × (Fin N → ℝ) => currentAngularLogYCoefficient f (Real.exp (-d.c₀*eps)) τ lam q.2 i)
        (s,θ) J 1 (C*(N:ℝ)^2) 0) ∧
      RealScaledJetBound
        (fun q : ℂ × (Fin N → ℝ) => currentPhaseParameterDerivative f (Real.exp (-d.c₀*eps)) τ lam q.1 q.2)
        (s,θ) J 1 (C*(N:ℝ)^2) 0 ∧
      ∀ i j, RealScaledJetBound
        (fun q : ℂ × (Fin N → ℝ) => currentAngularDeterminant f (Real.exp (-d.c₀*eps)) τ lam q.1 i j q.2)
        (s,θ) J 1 (C*(N:ℝ)^2) 0 := by
  obtain ⟨CF,hCF,hF⟩ := unwrappedLogY_joint_positive_finite_jets f hf (J+1)
  obtain ⟨r,CG,hr,hCG,hG⟩ := actual_compact_phase_joint_jets d f hf.p_smooth hf.m_smooth
    hf.p_periodic hf.m_periodic (fun x => ⟨hf.p_nonneg x,hp1 x⟩)
    (fun x => ⟨hf.m_nonneg x,hf.m_le_one x⟩) hmargin (J+1)
  let B := CF+CG+1
  have hB : 0 < B := by dsimp [B]; linarith
  let C := B+2*2^J*B^2+1
  have hterm : 0 ≤ (2:ℝ)*2^J*B^2 := by positivity
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨r,C,hr,hC,?_⟩
  intro N hN eps τ lam heps hτ hτ1 hlam hlam1 s hs hsmall θ hθ
  let r0 := Real.exp (-d.c₀*eps)
  let Ω := compactSourceDomain N r0
  have hr0 : 0 < r0 := Real.exp_pos _
  have hr01 : r0 < 1 := Real.exp_lt_one_iff.mpr (by have := d.c₀_pos; nlinarith)
  have hΩ : IsOpen Ω := compactSourceDomain_isOpen N r0
  have hmem : (s,θ) ∈ Ω := ⟨hs,Set.mem_univ _⟩
  have hFs := compactSource_logY_smooth (N := N) f hf r0 τ lam
  have hGs := compactSource_phase_smooth hN f hf hr0 hr01 hτ hlam
  have hFj : ∀ k, 1 ≤ k → k ≤ J+1 →
      ‖iteratedFDeriv ℝ k (fun q : ℂ × (Fin N → ℝ) => unwrappedLogY f r0 τ lam q.2) (s,θ)‖ ≤ B*N := by
    intro k hk hkJ
    exact (hF N hN r0 τ lam hτ hτ1 hlam hlam1 (s,θ) k hk hkJ).trans
      (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith : CF ≤ B) (by positivity))
  have hGj : ∀ k, 1 ≤ k → k ≤ J+1 →
      ‖iteratedFDeriv ℝ k (Function.uncurry (currentComplexPhase f r0 τ lam)) (s,θ)‖ ≤ B*N := by
    intro k _ hkJ
    exact (hG N hN eps τ lam heps.le hτ hτ1 hlam hlam1 s hsmall θ hθ k hkJ).trans
      (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith : CG ≤ B) (by positivity))
  have hBN : 0 ≤ B*(N:ℝ) := by positivity
  have hA (i : Fin N) := parameterSmooth_angular_uniform_jets hΩ hFs hmem J (B*N) hBN
    (Pi.single i 1) (by simp [Pi.norm_single]) hFj
  have hGθ (i : Fin N) := parameterSmooth_angular_uniform_jets hΩ hGs hmem J (B*N) hBN
    (Pi.single i 1) (by simp [Pi.norm_single]) hGj
  have hQ := parameterSmooth_parameter_uniform_jets hΩ hGs hmem J (B*N) hBN hGj
  have hBC : B*(N:ℝ) ≤ C*(N:ℝ)^2 := by
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hBCl : B ≤ C := by dsimp [C]; linarith
    exact (mul_le_mul_of_nonneg_left (le_self_pow₀ hN1 (by decide : 2 ≠ 0)) hB.le).trans
      (mul_le_mul_of_nonneg_right hBCl (sq_nonneg _))
  refine ⟨fun i => (hA i).mono zero_lt_one le_rfl hBC,hQ.mono zero_lt_one le_rfl hBC,?_⟩
  intro i j
  have hd := ((hA i).mul (hGθ j) zero_lt_one).sub ((hA j).mul (hGθ i) zero_lt_one)
  have hd' : RealScaledJetBound
      (fun q : ℂ × (Fin N → ℝ) => currentAngularDeterminant f r0 τ lam q.1 i j q.2)
      (s,θ) J 1 (2^J*(B*N)*(B*N)+2^J*(B*N)*(B*N)) 0 := by
    simpa only [currentAngularDeterminant,angularPairDeterminant,zero_add] using hd
  apply hd'.mono zero_lt_one le_rfl
  have hcost : 2*2^J*B^2 ≤ C := by dsimp [C]; linarith
  calc
    _ = (2*2^J*B^2)*(N:ℝ)^2 := by ring
    _ ≤ C*(N:ℝ)^2 := mul_le_mul_of_nonneg_right hcost (sq_nonneg _)

end
end IsingBulk.Tail
