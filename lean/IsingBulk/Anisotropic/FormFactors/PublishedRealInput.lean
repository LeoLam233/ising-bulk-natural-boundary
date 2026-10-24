import IsingBulk.Anisotropic.FormFactors.RealAngular

/-! The external interface is restricted to positive real temperature and
literal spin correlations at each fixed lattice separation. Sources: Bugrij--
Lisovyy, arXiv:0708.3643, (21)--(25),(30)--(39); Iorgov--Lisovyy,
arXiv:1012.2856, Theorem 6.1 and Remark 6.2. ANISO (1.6)--(1.8) fixes the
normalization. This module assumes no contour identity, full-site exchange,
normal convergence, boundary estimate or complex continuation.

`PublishedRealSpinFormFactors` is a predicate, not an axiom. Its use must
remain visible in physical endpoint theorem types. The response convention
below defines covariance normalization; identifying a separately given
uniform-field derivative requires the real linear-response argument. -/
namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open scoped BigOperators

abbrev LatticeSite := ℤ × ℤ

def realProduct (lam x : ℝ) : ℝ := Real.sinh x * Real.sinh (lam*x)
def realB (lam x : ℝ) : ℝ := Real.sinh (lam*x) / Real.sinh x
def realC (lam x : ℝ) : ℝ := Real.cosh x * Real.cosh (lam*x) / Real.sinh x

def realHighPrefactor (lam x : ℝ) : ℝ :=
  (1-realProduct lam x ^ 2) ^ (1/4:ℝ) / Real.sqrt (realProduct lam x)
def realMagnetizationSq (lam x : ℝ) : ℝ :=
  (1-(realProduct lam x)⁻¹ ^ 2) ^ (1/4:ℝ)

def oddSiteSeries (lam x : ℝ) (v : LatticeSite) : ℂ :=
  ∑' n : ℕ, latticeCoefficient (2*n+1) (realB lam x) (realC lam x) v

def evenSiteSeries (lam x : ℝ) (v : LatticeSite) : ℂ :=
  ∑' n : ℕ, latticeCoefficient (2*n+2) (realB lam x) (realC lam x) v

/-- The two-spin functions come from the unique HT state and the LT plus
state (or minus state with the same even correlations), respectively. -/
structure PublishedRealSpinFormFactors (lam : ℝ)
    (corrH corrL : ℝ → LatticeSite → ℝ) : Prop where
  high_onsite : ∀ x, 0 < x → realProduct lam x < 1 → corrH x (0,0) = 1
  low_onsite : ∀ x, 0 < x → 1 < realProduct lam x → corrL x (0,0) = 1
  high_spin : ∀ x, 0 < x → realProduct lam x < 1 → ∀ v,
    (corrH x v:ℂ) = (realHighPrefactor lam x:ℂ) * oddSiteSeries lam x v
  low_spin : ∀ x, 0 < x → 1 < realProduct lam x → ∀ v,
    (corrL x v:ℂ) = (realMagnetizationSq lam x:ℂ) * (1+evenSiteSeries lam x v)

def highCovarianceSum (corrH : ℝ → LatticeSite → ℝ) (x : ℝ) : ℝ :=
  ∑' v : LatticeSite, corrH x v

def lowCovarianceSum (lam : ℝ) (corrL : ℝ → LatticeSite → ℝ) (x : ℝ) : ℝ :=
  ∑' v : LatticeSite, (corrL x v-realMagnetizationSq lam x)

/-- Energy-field normalization at real inverse temperature β=x/(2Jx). -/
def highEnergyFieldResponse (J : ℝ) (corrH : ℝ → LatticeSite → ℝ) (x : ℝ) : ℝ :=
  (x/(2*J))*highCovarianceSum corrH x

def lowEnergyFieldResponse (J lam : ℝ) (corrL : ℝ → LatticeSite → ℝ) (x : ℝ) : ℝ :=
  (x/(2*J))*lowCovarianceSum lam corrL x

theorem low_connected_spin {lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ}
    (h : PublishedRealSpinFormFactors lam corrH corrL) {x : ℝ}
    (hx : 0 < x) (hp : 1 < realProduct lam x) (v : LatticeSite) :
    ((corrL x v-realMagnetizationSq lam x:ℝ):ℂ) =
      (realMagnetizationSq lam x:ℂ)*evenSiteSeries lam x v := by
  push_cast
  rw [h.low_spin x hx hp]
  ring

theorem low_connected_onsite {lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ}
    (h : PublishedRealSpinFormFactors lam corrH corrL) {x : ℝ}
    (hx : 0 < x) (hp : 1 < realProduct lam x) :
    corrL x (0,0)-realMagnetizationSq lam x = 1-realMagnetizationSq lam x := by
  rw [h.low_onsite x hx hp]

/-- No mixture-state zero-magnetization substitution is hidden in the LT sum. -/
theorem low_covariance_subtraction (lam : ℝ) (corrL : ℝ → LatticeSite → ℝ) (x : ℝ) :
    lowCovarianceSum lam corrL x = ∑' v : ℤ × ℤ, (corrL x v-realMagnetizationSq lam x) := rfl
end
end IsingBulk.Anisotropic.FormFactors
