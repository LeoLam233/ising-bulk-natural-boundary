import IsingBulk

/- Ordinary type/application controls through the public root. These examples
are excluded from production imports and production declaration counts. -/
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Final
open Filter Asymptotics
open scoped Topology

example {p N : ℕ} {D eps : ℝ}
    (h : 2*(p+1) ≤ N ∧ (N:ℝ) < D*Real.sqrt (-Real.log eps)) :
    2*p+2 ≤ N ∧ (N:ℝ) ≤ D*Real.sqrt (Real.log (1/eps)) :=
  intermediate_window_subset h

example {p order : ℕ} {d : LocalBranchData}
    (cfg : CommonAllSectorParameters p d order) (j : ℕ) (hj : j ≤ order) :
    (∀ᶠ eps : ℝ in 𝓝[>] 0, Summable (fun N =>
      intermediateKSNormWindowTerm p d cfg.eta d.alpha d.tau j cfg.D eps (eps^cfg.beta) N)) ∧
    (fun eps : ℝ => intermediateKSNormWindow p d cfg.eta d.alpha d.tau j cfg.D eps
      (eps^cfg.beta)) =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) :=
  common_intermediateKSNormWindow_radialSeriesSmall cfg j hj

example {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) (hab : a ≠ b) :
    ∀ j : ℕ, j ≤ (2*p)^2/2-1 →
      (fun eps : ℝ => ∑' n : ℕ, ‖iteratedDeriv j (upperFormFactor (2*(n+p+1)))
        (radialParameter (selectedOrderedChart ha hb).theta eps)‖)
        =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) :=
  theorem_tail hp hp11 ha hb hab

example
    (hTW : ∀ p : ℕ, ∀ a b : ℤ, p.Prime → 11 ≤ p →
      IsingBulk.PrimeFamily.Admissible p a → IsingBulk.PrimeFamily.Admissible p b → a ≠ b →
      PublishedTWFixedOrderInput (IsingBulk.PrimeFamily.selectedPoint p a b)) :
    ∀ z : ℂ, ‖z‖ = 1 → ¬ HasExteriorExtension exteriorNormalizedBulk z :=
  theorem_nb hTW

example {J : ℝ} (hJ : 0 < J) {chi : ℂ → ℂ} {M : ℝ → ℂ}
    (hE1 : PhysicalSusceptibilityE1 J chi M) (hE2 : YangMagnetizationE2 M)
    (hTW : ∀ p : ℕ, ∀ a b : ℤ, p.Prime → 11 ≤ p →
      IsingBulk.PrimeFamily.Admissible p a → IsingBulk.PrimeFamily.Admissible p b → a ≠ b →
      PublishedTWFixedOrderInput (IsingBulk.PrimeFamily.selectedPoint p a b)) :
    AnalyticOnNhd ℂ (rightPhysicalBulk J) {s : ℂ | 1 < ‖s‖ ∧ 0 < s.re} ∧
      (∀ x : ℝ, 16 < x → chi (x:ℂ) = rightPhysicalBulk J (x:ℂ)) ∧
      (∀ z : ℂ, ‖z‖ = 1 → ¬ HasPhysicalBoundaryExtension J exteriorNormalizedBulk z) :=
  theorem_nb_physical hJ hE1 hE2 hTW
