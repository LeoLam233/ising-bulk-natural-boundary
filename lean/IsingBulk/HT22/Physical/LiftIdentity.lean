import IsingBulk.HT22.Physical.CellPartition
import IsingBulk.Preferred22.ContourLift
namespace IsingBulk.HT22.Physical
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators

theorem bareContourDensity_lift (negative : Bool) {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (s : ℂ) (θ : Fin N → ℝ) :
    bareContourDensity negative τ p m s (preferredLiftedAngles δ θ)=bareContourDensity negative τ p m s θ := by
  apply bareContourDensity_congr_data
  · intro i
    exact preferred_periodic_lift angleRoot angleRoot_periodic δ (θ i)
  · intro i
    exact preferred_periodic_lift p hp δ (θ i)
  · intro i
    exact preferred_periodic_lift m hm δ (θ i)
  · intro i
    exact preferred_periodic_lift (deriv p) (bump_derivative_periodic hp) δ (θ i)
  · intro i
    exact preferred_periodic_lift (deriv m) (bump_derivative_periodic hm) δ (θ i)
end
end IsingBulk.HT22.Physical
