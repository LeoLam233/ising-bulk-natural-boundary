import IsingBulk.AnisoF002.C03.RegularEdgeRoot

/-!
# A local continuation of a prescribed simple reciprocal root

The prescribed root, including its sign, is retained exactly. The square
root is applied near one, so this construction also works across real
outside-spectrum points without switching the physical branch.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open scoped Topology

def reciprocalRootContinuation (W₀ r₀ W : ℂ) : ℂ :=
  W - (W₀ - r₀) * Complex.sqrt (1 + (W ^ 2 - W₀ ^ 2) / (W₀ - r₀) ^ 2)

theorem reciprocalRootContinuation_center (W₀ r₀ : ℂ) :
    reciprocalRootContinuation W₀ r₀ W₀ = r₀ := by
  simp [reciprocalRootContinuation, Complex.sqrt]

theorem reciprocalRootContinuation_discriminant {W₀ r₀ : ℂ}
    (hp : r₀ ^ 2 - 2 * W₀ * r₀ + 1 = 0) :
    (W₀ - r₀) ^ 2 = W₀ ^ 2 - 1 := by
  linear_combination hp

theorem reciprocalRootContinuation_simple {W₀ r₀ : ℂ}
    (hp : r₀ ^ 2 - 2 * W₀ * r₀ + 1 = 0) (hd : 1 - r₀ * r₀ ≠ 0) :
    W₀ - r₀ ≠ 0 := by
  intro hz
  have he := sub_eq_zero.mp hz
  rw [he] at hp
  apply hd
  linear_combination hp

theorem reciprocalRootContinuation_polynomial {W₀ r₀ : ℂ}
    (hp : r₀ ^ 2 - 2 * W₀ * r₀ + 1 = 0) (hd : W₀ - r₀ ≠ 0) (W : ℂ) :
    reciprocalRootContinuation W₀ r₀ W ^ 2 -
      2 * W * reciprocalRootContinuation W₀ r₀ W + 1 = 0 := by
  have hs : Complex.sqrt (1 + (W ^ 2 - W₀ ^ 2) / (W₀ - r₀) ^ 2) ^ 2 =
      1 + (W ^ 2 - W₀ ^ 2) / (W₀ - r₀) ^ 2 := by
    simpa only [Complex.sqrt] using
      Complex.cpow_ofNat_inv_pow (1 + (W ^ 2 - W₀ ^ 2) / (W₀ - r₀) ^ 2) 2
  have hm : (W₀ - r₀) ^ 2 * Complex.sqrt
      (1 + (W ^ 2 - W₀ ^ 2) / (W₀ - r₀) ^ 2) ^ 2 =
      (W₀ - r₀) ^ 2 + W ^ 2 - W₀ ^ 2 := by
    rw [hs]
    field_simp
    ring
  have hD := reciprocalRootContinuation_discriminant hp
  unfold reciprocalRootContinuation
  linear_combination hm + hD

theorem reciprocalRootContinuation_analyticAt (W₀ r₀ : ℂ) :
    AnalyticAt ℂ (reciprocalRootContinuation W₀ r₀) W₀ := by
  have ha : AnalyticAt ℂ (fun W : ℂ =>
      1 + (W ^ 2 - W₀ ^ 2) / (W₀ - r₀) ^ 2) W₀ :=
    analyticAt_const.add (((analyticAt_id.pow 2).sub analyticAt_const).div_const)
  have hslit : 1 + (W₀ ^ 2 - W₀ ^ 2) / (W₀ - r₀) ^ 2 ∈ Complex.slitPlane := by
    simp [Complex.mem_slitPlane_iff]
  have hs : AnalyticAt ℂ (fun W : ℂ =>
      Complex.sqrt (1 + (W ^ 2 - W₀ ^ 2) / (W₀ - r₀) ^ 2)) W₀ := by
    simpa only [Complex.sqrt] using
      ha.cpow (g := fun _ : ℂ => (2⁻¹ : ℂ)) analyticAt_const hslit
  exact analyticAt_id.sub (analyticAt_const.mul hs)

end
end IsingBulk.AnisoF002.RegularTail.C03
