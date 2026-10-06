import IsingBulk.First.ResidueAlgebra

/-! Full-site and onsite observables use exactly the same normalized contours
and factorial as the offsite form factor. The published fixed-order smoothness
input concerns the full-site function after its fixed-radius locality bridge. -/
namespace IsingBulk.First
noncomputable section

def onsiteFormFactor (N : ℕ) (r : ℝ) (s : ℂ) : ℂ :=
  (N.factorial : ℂ)⁻¹ * multiCircleIntegral r N (fun y =>
    multiCircleIntegral r N (fun x => onsiteDensity s x y))

def standardFormFactor (N : ℕ) (r : ℝ) (s : ℂ) : ℂ :=
  (N.factorial : ℂ)⁻¹ * multiCircleIntegral r N (fun y =>
    multiCircleIntegral r N (fun x => standardDensity s x y))

end
end IsingBulk.First
