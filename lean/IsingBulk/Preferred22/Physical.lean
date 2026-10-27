import Mathlib.Tactic
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
LT22, Section 2: concrete full-lattice and constrained-angular objects.
No analytic or physical assertion is hidden in these definitions.
The published input predicates below apply only to real s > 1.
-/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Set

def temperatureTrace (s : ℂ) : ℂ := s + s⁻¹

def angularW (s : ℂ) (θ : ℝ) : ℂ := temperatureTrace s - Real.cos θ

def quadraticCandidate (W : ℂ) : ℂ := W + Complex.sqrt (W ^ 2 - 1)

theorem complex_sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z :=
  Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)

theorem quadraticCandidate_product (W : ℂ) :
    quadraticCandidate W * (W - Complex.sqrt (W ^ 2 - 1)) = 1 := by
  unfold quadraticCandidate
  calc
    _ = W ^ 2 - Complex.sqrt (W ^ 2 - 1) ^ 2 := by ring
    _ = 1 := by rw [complex_sqrt_sq]; ring

theorem quadraticCandidate_ne_zero (W : ℂ) : quadraticCandidate W ≠ 0 := by
  intro h
  have := quadraticCandidate_product W
  simp [h] at this

theorem quadraticCandidate_inverse (W : ℂ) :
    (quadraticCandidate W)⁻¹ = W - Complex.sqrt (W ^ 2 - 1) :=
  inv_eq_of_mul_eq_one_right (quadraticCandidate_product W)

theorem quadraticCandidate_trace (W : ℂ) :
    quadraticCandidate W + (quadraticCandidate W)⁻¹ = 2 * W := by
  rw [quadraticCandidate_inverse, quadraticCandidate]
  ring

/-- The root inside the unit disk, selected from the two explicit reciprocal roots.
The `root_inside` theorem below proves the selection on the physical domain. -/
def physicalRoot (W : ℂ) : ℂ :=
  if ‖quadraticCandidate W‖ < 1 then quadraticCandidate W else (quadraticCandidate W)⁻¹

def OffRealSegment (W : ℂ) : Prop := W.im ≠ 0 ∨ 1 < |W.re|

theorem physicalRoot_ne_zero (W : ℂ) : physicalRoot W ≠ 0 := by
  unfold physicalRoot
  split_ifs
  · exact quadraticCandidate_ne_zero W
  · exact inv_ne_zero (quadraticCandidate_ne_zero W)

theorem physicalRoot_trace (W : ℂ) : physicalRoot W + (physicalRoot W)⁻¹ = 2 * W := by
  unfold physicalRoot
  split_ifs
  · exact quadraticCandidate_trace W
  · simpa only [inv_inv, add_comm] using quadraticCandidate_trace W

theorem unit_root_trace_in_segment {z W : ℂ} (hz : ‖z‖ = 1)
    (ht : z + z⁻¹ = 2 * W) : W.im = 0 ∧ |W.re| ≤ 1 := by
  have hs : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hr := congrArg Complex.re ht
  have hi := congrArg Complex.im ht
  norm_num [Complex.add_re, Complex.inv_re, hs, Complex.mul_re] at hr
  norm_num [Complex.add_im, Complex.inv_im, hs, Complex.mul_im] at hi
  have hw : W.re = z.re := by linarith
  constructor
  · linarith
  · rw [hw]
    exact (Complex.abs_re_le_norm z).trans_eq hz

theorem physicalRoot_inside {W : ℂ} (hW : OffRealSegment W) : ‖physicalRoot W‖ < 1 := by
  have hne : ‖quadraticCandidate W‖ ≠ 1 := by
    intro h
    obtain ⟨hi, hr⟩ := unit_root_trace_in_segment h (quadraticCandidate_trace W)
    rcases hW with hW | hW
    · exact hW hi
    · exact (not_lt_of_ge hr) hW
  unfold physicalRoot
  split_ifs with h
  · exact h
  · rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ (lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne))

theorem root_unique_in_disk {W u v : ℂ}
    (hu : u + u⁻¹ = 2 * W) (hv : v + v⁻¹ = 2 * W)
    (hun : u ≠ 0) (hvn : v ≠ 0) (hui : ‖u‖ < 1) (hvi : ‖v‖ < 1) : u = v := by
  have hp : (u - v) * (u * v - 1) = 0 := by
    have h := hu.trans hv.symm
    field_simp at h
    linear_combination h
  rcases mul_eq_zero.mp hp with h | h
  · exact sub_eq_zero.mp h
  · have hprod : u * v = 1 := sub_eq_zero.mp h
    have hnorm : ‖u * v‖ < 1 := by
      rw [norm_mul]
      calc
        ‖u‖ * ‖v‖ ≤ ‖u‖ * 1 := mul_le_mul_of_nonneg_left hvi.le (norm_nonneg u)
        _ < 1 := by simpa using hui
    simp [hprod] at hnorm

/-- The angular dispersion never hits the forbidden real segment at an
exterior temperature. This establishes the domain of the root selection. -/
theorem angularW_off_segment {s : ℂ} (hs : 1 < ‖s‖) (θ : ℝ) :
    OffRealSegment (angularW s θ) := by
  by_contra h
  have hW : (angularW s θ).im = 0 ∧ |(angularW s θ).re| ≤ 1 := by
    simpa [OffRealSegment, not_or, not_lt] using h
  have hns : 1 < Complex.normSq s := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg s]
  have hn : Complex.normSq s ≠ 0 := by linarith
  have hi : s.im - s.im / Complex.normSq s = 0 := by
    simpa [angularW, temperatureTrace, Complex.inv_im, neg_div, sub_eq_add_neg] using hW.1
  have hi' : s.im * (Complex.normSq s - 1) = 0 := by
    have hh : s.im = s.im / Complex.normSq s := sub_eq_zero.mp hi
    have hh' := (eq_div_iff hn).mp hh
    linear_combination hh'
  have him : s.im = 0 := (mul_eq_zero.mp hi').resolve_right (by linarith)
  have hre : 1 < s.re ^ 2 := by
    simpa [Complex.normSq_apply, him, sq] using hns
  have hs0 : s ≠ 0 := by intro hz; norm_num [hz] at hs
  have ht : (temperatureTrace s) * s = s ^ 2 + 1 := by
    unfold temperatureTrace
    field_simp
  have htr := congrArg Complex.re ht
  simp [Complex.mul_re, him, pow_two] at htr
  have hbounds := abs_le.mp hW.2
  have hc0 := Real.neg_one_le_cos θ
  have hc1 := Real.cos_le_one θ
  have hlow : -2 ≤ (temperatureTrace s).re := by
    simp only [angularW, Complex.sub_re, Complex.ofReal_re] at hbounds
    linarith
  have hupp : (temperatureTrace s).re ≤ 2 := by
    simp only [angularW, Complex.sub_re, Complex.ofReal_re] at hbounds
    linarith
  by_cases hp : 0 ≤ s.re
  · have ha : 1 < s.re := by nlinarith
    have hb := mul_le_mul_of_nonneg_right hupp hp
    nlinarith [sq_pos_of_pos (sub_pos.mpr ha)]
  · have ha : s.re < -1 := by nlinarith
    have hb := mul_le_mul_of_nonpos_right hlow (le_of_not_ge hp)
    nlinarith [sq_pos_of_neg (by linarith : s.re + 1 < 0)]

theorem angularRoots_inside {N : ℕ} {s : ℂ} (hs : 1 < ‖s‖)
    (θ : Fin N → ℝ) (i : Fin N) :
    ‖physicalRoot (angularW s (θ i))‖ < 1 :=
  physicalRoot_inside (angularW_off_segment hs (θ i))

def angleRoot (θ : ℝ) : ℂ := Complex.exp (Complex.I * θ)

def angularRoots {N : ℕ} (s : ℂ) (θ : Fin N → ℝ) : Fin N → ℂ :=
  fun i => physicalRoot (angularW s (θ i))

def gaugeKernel {N : ℕ} (y z : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => -Complex.I * Complex.sqrt (z i / y i) * Complex.sqrt (z j / y j) *
    (y i - y j) / (1 - z i * z j)

theorem gaugeKernel_diagonal {N : ℕ} (y z : Fin N → ℂ) (i : Fin N) :
    gaugeKernel y z i i = 0 := by simp [gaugeKernel]

theorem gaugeKernel_skew {N : ℕ} (y z : Fin N → ℂ) (i j : Fin N) :
    gaugeKernel y z j i = -gaugeKernel y z i j := by
  unfold gaugeKernel
  rw [show z j * z i = z i * z j by ring]
  ring

def oneBody (z : ℂ) : ℂ := 2 * z / (1 - z ^ 2)

def fullAngularDensity {N : ℕ} (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  let z := angularRoots s θ
  let Z := ∏ i, z i
  (1 + Z) / (1 - Z) * Matrix.det (gaugeKernel (fun i => angleRoot (θ i)) z) *
    ∏ i, oneBody (z i)

/-- Coordinates of the constrained torus, with the final angle eliminated.
Periodicity allows its last coordinate to be left unwrapped. -/
def constrainedAngles {n : ℕ} (θ : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc θ (-∑ i, θ i)

theorem constrainedAngles_sum {n : ℕ} (θ : Fin n → ℝ) :
    ∑ i, constrainedAngles θ i = 0 := by
  simp [constrainedAngles, Fin.sum_univ_castSucc]

def angularBox (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Ioc (-Real.pi) Real.pi)

/-- Exact coefficient (2.3), including N!, (2π)^(N-1), and N-1 real integrals. -/
def coefficient : ℕ → ℂ → ℂ
  | 0, _ => 0
  | n + 1, s => ((Nat.factorial (n + 1) : ℂ) * (2 * Real.pi : ℂ) ^ n)⁻¹ *
      ∫ θ in angularBox n, fullAngularDensity s (constrainedAngles θ)

/-- Full physical site coefficient before either lattice direction is summed. -/
def siteCoefficient (N : ℕ) (a b : ℤ) (s : ℂ) : ℂ :=
  ((N.factorial : ℂ) * (2 * Real.pi : ℂ) ^ N)⁻¹ *
    ∫ θ in angularBox N,
      Complex.exp (Complex.I * (a : ℂ) * (∑ i, (θ i : ℂ))) *
      (∏ i, angularRoots s θ i) ^ b.natAbs *
      Matrix.det (gaugeKernel (fun i => angleRoot (θ i)) (angularRoots s θ)) *
      ∏ i, oneBody (angularRoots s θ i)

def evenSeries (s : ℂ) : ℂ := ∑' n : ℕ, coefficient (2 * (n + 1)) s

def magnetizationSquared (s : ℂ) : ℂ := (1 - (s ^ (4 : ℕ))⁻¹) ^ (1 / 4 : ℂ)

def bulkFunction (s : ℂ) : ℂ := magnetizationSquared s * evenSeries s

/-- Palmer--Tracy: only the real low-temperature two-point series is an input.
No lattice summation, complex continuation, singularity or tail estimate is included. -/
def PalmerTracyInput (correlation : ℝ → ℤ → ℤ → ℂ) (M : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, 1 < x → ∀ a b : ℤ,
    Summable (fun n : ℕ => siteCoefficient (2 * (n + 1)) a b (x : ℂ)) ∧
    correlation x a b = M x *
      (1 + ∑' n : ℕ, siteCoefficient (2 * (n + 1)) a b (x : ℂ))

def YangInput (M : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, 1 < x → M x = magnetizationSquared (x : ℂ)

def connectedLatticeSum (correlation : ℝ → ℤ → ℤ → ℂ) (M : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' ab : ℤ × ℤ, (correlation x ab.1 ab.2 - M x)

theorem connected_site_of_PalmerTracy {correlation : ℝ → ℤ → ℤ → ℂ} {M : ℝ → ℂ}
    (h : PalmerTracyInput correlation M) {x : ℝ} (hx : 1 < x) (a b : ℤ) :
    correlation x a b - M x =
      M x * (∑' n : ℕ, siteCoefficient (2 * (n + 1)) a b (x : ℂ)) := by
  rw [(h x hx a b).2]
  ring

theorem origin_contribution {correlation : ℝ → ℤ → ℤ → ℂ} {M : ℝ → ℂ} {x : ℝ}
    (hsite : correlation x 0 0 = 1) : correlation x 0 0 - M x = 1 - M x := by
  rw [hsite]

end
end IsingBulk.Preferred22
