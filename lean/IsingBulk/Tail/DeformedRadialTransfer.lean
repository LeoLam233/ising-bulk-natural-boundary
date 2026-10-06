import IsingBulk.Tail.RadialDispersionTransfer
import IsingBulk.Tail.OriginalGlobalDisk
import IsingBulk.Tail.SelectorLegality

/-! Uniform radial-center transfer for the literal coupled contour. Occupancy
is allowed to vary throughout [0,1]; no root or pair estimate is a premise. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch

def coupledRadialExponent (c₀ eps τ lam p m ρ : ℝ) : ℝ :=
  -c₀*eps+lam*τ*(-2*p+ρ*m/2)

theorem coupledRadialExponent_bound {c₀ eps τ lam p m ρ : ℝ}
    (hc : 0 ≤ c₀) (heps : 0 ≤ eps) (hτ : 0 ≤ τ)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    |coupledRadialExponent c₀ eps τ lam p m ρ| ≤ c₀*eps+2*τ := by
  have hρm0 := mul_nonneg hρ0 hm0
  have hρm1 : ρ*m ≤ 1 := (mul_le_mul_of_nonneg_left hm1 hρ0).trans (by simpa using hρ1)
  have hlo : -2 ≤ -2*p+ρ*m/2 := by nlinarith
  have hhi : -2*p+ρ*m/2 ≤ 1/2 := by nlinarith
  have hlo' := mul_le_mul_of_nonneg_left hlo hl0
  have hhi' := mul_le_mul_of_nonneg_left hhi hl0
  have hlamlo : -2 ≤ lam*(-2*p+ρ*m/2) := by nlinarith
  have hlamhi : lam*(-2*p+ρ*m/2) ≤ 1/2 := by nlinarith
  have hτlo := mul_le_mul_of_nonneg_left hlamlo hτ
  have hτhi := mul_le_mul_of_nonneg_left hlamhi hτ
  rw [abs_le]
  unfold coupledRadialExponent
  constructor <;> nlinarith [mul_nonneg hc heps]

/-- Stronger than the manuscript's conservative +5τ transfer cost. -/
theorem coupled_radial_sourceW_transfer (d : LocalBranchData)
    {eps τ lam p m ρ θ : ℝ} (heps : 0 ≤ eps) (hτ : 0 ≤ τ)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hsmall : d.c₀*eps+2*τ ≤ 1) :
    ‖sourceW (radialParameter d.theta eps)
      (radialAnglePoint (coupledRadialExponent d.c₀ eps τ lam p m ρ) θ)-
      (limitingAngularW d.thetaB θ:ℂ)‖ ≤ (3+2*d.c₀)*eps+4*τ := by
  have hv := coupledRadialExponent_bound d.c₀_pos.le heps hτ hl0 hl1 hp0 hp1 hm0 hm1 hρ0 hρ1
  have h := radial_sourceW_transfer (radialParameter d.theta eps) (1+Real.cos d.thetaB)
    (coupledRadialExponent d.c₀ eps τ lam p m ρ) θ (hv.trans hsmall)
  have hs := sourceS_radial_to_boundary d eps heps
  change ‖sourceW (radialParameter d.theta eps)
      (radialAnglePoint (coupledRadialExponent d.c₀ eps τ lam p m ρ) θ)-
      ((1+Real.cos d.thetaB-Real.cos θ:ℝ):ℂ)‖ ≤ _
  linarith

theorem deformedPoint_coupledRadialExponent {N : ℕ} (f : SelectorFunctions)
    (c₀ eps τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    deformedPoint f (Real.exp (-c₀*eps)) τ lam θ i =
      radialAnglePoint (coupledRadialExponent c₀ eps τ lam (f.p (θ i)) (f.m (θ i))
        (occupancy (fun j => f.p (θ j))/(N:ℝ))) (θ i) := by
  rw [deformedPoint_polar f (Real.exp_pos _) τ lam θ i,Real.log_exp]
  unfold radialAnglePoint coupledRadialExponent retractionShift
  congr 1
  push_cast
  ring

/-- Every actual coupled occupancy satisfies the same pointwise transfer;
the estimate is independent of N and applies before integrating any angle. -/
theorem deformedPoint_sourceW_transfer (d : LocalBranchData) {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) {eps τ lam : ℝ} (θ : Fin N → ℝ)
    (heps : 0 ≤ eps) (hτ : 0 ≤ τ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hp : ∀ x, 0 ≤ f.p x ∧ f.p x ≤ 1) (hm : ∀ x, 0 ≤ f.m x ∧ f.m x ≤ 1)
    (hsmall : d.c₀*eps+2*τ ≤ 1) (i : Fin N) :
    ‖sourceW (radialParameter d.theta eps)
      (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i)-
      (limitingAngularW d.thetaB (θ i):ℂ)‖ ≤ (3+2*d.c₀)*eps+4*τ := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hP0 := occupancy_nonneg (fun j => (hp (θ j)).1)
  have hP1 := occupancy_le (fun j => (hp (θ j)).2)
  rw [deformedPoint_coupledRadialExponent]
  exact coupled_radial_sourceW_transfer d heps hτ hl0 hl1 (hp _).1 (hp _).2 (hm _).1 (hm _).2
    (by positivity) ((div_le_one hn).mpr hP1) hsmall

end
end IsingBulk.Tail
