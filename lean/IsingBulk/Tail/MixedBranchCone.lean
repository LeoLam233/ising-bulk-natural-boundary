import IsingBulk.Tail.MixedFrozenPhase
import IsingBulk.Tail.SelectedFDiskSupport
import IsingBulk.Tail.ProtectedActualPairs
import IsingBulk.Analysis.BranchCone

/-! The positive mixed coarea cone is attached to the actual selected
plateau, with its full occupancy and arbitrary particle count retained. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology

theorem mixedSourcePhase_current (d : LocalBranchData) (eps t u : ℝ) :
    mixedSourcePhase (radialParameter d.theta eps) (plateauY d.c₀ eps d.tau t d.thetaB u) =
      currentPhase d eps t u := by
  rw [currentPhase,currentW_dispersion]
  rfl

theorem currentDu_plateau_numerator (d : LocalBranchData) (eps t u : ℝ) :
    currentDu d eps t u=Complex.I*(plateauY d.c₀ eps d.tau t d.thetaB u-
      (plateauY d.c₀ eps d.tau t d.thetaB u)⁻¹)/2 := by
  have hy : plateauY d.c₀ eps d.tau t d.thetaB u =
      Complex.exp (((-d.c₀*eps+d.tau*t/2:ℝ):ℂ)+(-(d.thetaB:ℂ)+(u:ℂ))*Complex.I) := by
    unfold plateauY
    congr 1
    push_cast
    ring
  rw [hy,← Complex.exp_neg]
  unfold currentDu Complex.sinh
  ring

theorem mixedSourceSlope_current_deriv (d : LocalBranchData) (eps t u : ℝ)
    (hr : 0<(currentW d eps t u).re) (hi : 0<(currentW d eps t u).im) :
    mixedSourceSlope (radialParameter d.theta eps) (plateauY d.c₀ eps d.tau t d.thetaB u)=
      deriv (currentPhase d eps t) u := by
  rw [(currentPhase_hasDerivAt d eps t u hr hi).deriv,currentDu_plateau_numerator]
  unfold mixedSourceSlope
  rw [mixedSourcePhase_current]
  ring

theorem plateauY_rescale_tau (d : LocalBranchData) (eps τ t u : ℝ) :
    plateauY d.c₀ eps d.tau ((τ/d.tau)*t) d.thetaB u=plateauY d.c₀ eps τ t d.thetaB u := by
  unfold plateauY
  congr 1
  have he : d.tau*((τ/d.tau)*t)=τ*t := by field_simp [d.tau_pos.ne']
  rw [he]

theorem mixed_positive_branch_cone (d : LocalBranchData) :
    ∃ r τ₀ : ℝ,0<r ∧ 0<τ₀ ∧ ∀ eps τ t u : ℝ,
      0<eps → eps<r → 0≤τ → τ<τ₀ → 0≤t → t≤1 → 0≤u → u<r →
      (2/3:ℝ)*‖mixedSourceSlope (radialParameter d.theta eps) (plateauY d.c₀ eps τ t d.thetaB u)‖ ≤
        (mixedSourceSlope (radialParameter d.theta eps) (plateauY d.c₀ eps τ t d.thetaB u)).re := by
  obtain ⟨r₁,hr₁,hcone⟩ := current_positive_cone d
  obtain ⟨r₂,hr₂,hbranch⟩ := current_branch_inclusion d
  let r := min r₁ r₂
  have hr : 0<r := lt_min hr₁ hr₂
  refine ⟨r,d.tau*r,hr,mul_pos d.tau_pos hr,?_⟩
  intro eps τ t u heps hepsr hτ hτr ht ht1 hu hur
  have ht' : 0≤(τ/d.tau)*t := mul_nonneg (div_nonneg hτ d.tau_pos.le) ht
  have htr : (τ/d.tau)*t<r := by
    have hτ' : τ/d.tau<r := (div_lt_iff₀ d.tau_pos).mpr (by simpa [mul_comm] using hτr)
    exact (mul_le_of_le_one_right (div_nonneg hτ d.tau_pos.le) ht1).trans_lt hτ'
  obtain ⟨hRe,hIm⟩ := hbranch eps ((τ/d.tau)*t) u heps
    (hepsr.trans_le (min_le_right _ _)) ht' (htr.trans_le (min_le_right _ _))
    (by simpa only [abs_of_nonneg hu] using hur.trans_le (min_le_right _ _))
  rw [← plateauY_rescale_tau d eps τ t u,mixedSourceSlope_current_deriv d eps ((τ/d.tau)*t) u hRe hIm]
  exact hcone eps ((τ/d.tau)*t) u heps (hepsr.trans_le (min_le_left _ _)) ht'
    (htr.trans_le (min_le_left _ _)) hu (hur.trans_le (min_le_left _ _))

theorem mixed_actual_positive_branch_cone (d : LocalBranchData) :
    ∃ r τ₀ : ℝ,0<r ∧ 0<τ₀ ∧ ∀ (N : ℕ) (eps τ lam : ℝ)
      (f : SelectorFunctions) (θ : Fin N → ℝ) (j : Fin N),
      0<N → 0<eps → eps<r → 0≤τ → τ<τ₀ → 0≤lam → lam≤1 →
      (∀ x,0≤f.p x ∧ f.p x≤1) → f.p (θ j)=0 → f.m (θ j)=1 →
      0≤θ j+d.thetaB-2*Real.pi → θ j+d.thetaB-2*Real.pi<r →
      (2/3:ℝ)*‖mixedSourceSlope (radialParameter d.theta eps)
        (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ j)‖ ≤
      (mixedSourceSlope (radialParameter d.theta eps)
        (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ j)).re := by
  obtain ⟨r,τ₀,hr,hτ₀,hcone⟩ := mixed_positive_branch_cone d
  refine ⟨r,τ₀,hr,hτ₀,?_⟩
  intro N eps τ lam f θ j hN heps hepsr hτ hτlt hl0 hl1 hp hpj hmj hu hur
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hP0 := occupancy_nonneg (fun i => (hp (θ i)).1)
  have hPN := occupancy_le (fun i => (hp (θ i)).2)
  rw [deformedPoint_current_plateau f d.thetaB d.c₀ eps τ lam θ j hpj hmj]
  apply hcone eps τ _ _ heps hepsr hτ hτlt (by positivity) _ hu hur
  exact (div_le_one hn).mpr ((mul_le_of_le_one_left hP0 hl1).trans hPN)

end
end IsingBulk.Tail
