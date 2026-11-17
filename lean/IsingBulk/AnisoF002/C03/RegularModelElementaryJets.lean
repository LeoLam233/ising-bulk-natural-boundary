import IsingBulk.AnisoF002.C03.RegularModelCauchy

/-!
# Exact centered Taylor identities for the elementary model factors

The first and second centered differences cancel the appropriate Taylor
jets before any error is estimated.  The logarithm and the literal
(-n^2/2+1)log n factor have explicitly verified derivatives through order
four on the principal slit plane.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology

theorem centered_third_taylor_bounds {s : Set ℂ} (hs : Convex ℝ s)
    {f : ℂ → ℂ} {c δ : ℂ} {M : ℝ} (hf : AnalyticOnNhd ℂ f s)
    (hc : c ∈ s) (hp : c + δ ∈ s) (hm : c - δ ∈ s) (hM : 0 ≤ M)
    (hfour : ∀ z ∈ s, ‖deriv (deriv (deriv (deriv f))) z‖ ≤ M) :
    ‖f (c + δ) - f (c - δ) - 2 * deriv f c * δ‖ ≤
        ‖deriv (deriv (deriv f)) c‖ / 3 * ‖δ‖ ^ 3 + 2 * M * ‖δ‖ ^ 4 ∧
      ‖f (c + δ) - 2 * f c + f (c - δ) - deriv (deriv f) c * δ ^ 2‖ ≤
        2 * M * ‖δ‖ ^ 4 := by
  let Rp := f (c + δ) - f c - deriv f c * δ -
    (deriv (deriv f) c / 2) * δ ^ 2 - (deriv (deriv (deriv f)) c / 6) * δ ^ 3
  let Rm := f (c - δ) - f c - deriv f c * (-δ) -
    (deriv (deriv f) c / 2) * (-δ) ^ 2 - (deriv (deriv (deriv f)) c / 6) * (-δ) ^ 3
  have hT := scalar_third_taylor_remainder hs hf hc hM hfour
  have hRp : ‖Rp‖ ≤ M * ‖δ‖ ^ 4 := by
    simpa only [add_sub_cancel_left] using hT (c + δ) hp
  have hRm : ‖Rm‖ ≤ M * ‖δ‖ ^ 4 := by
    simpa only [sub_sub_cancel_left, norm_neg] using hT (c - δ) hm
  constructor
  · have he : f (c + δ) - f (c - δ) - 2 * deriv f c * δ =
        Rp - Rm + (deriv (deriv (deriv f)) c / 3) * δ ^ 3 := by dsimp [Rp, Rm]; ring
    rw [he]
    calc
      _ ≤ ‖Rp - Rm‖ + ‖(deriv (deriv (deriv f)) c / 3) * δ ^ 3‖ := norm_add_le _ _
      _ ≤ (‖Rp‖ + ‖Rm‖) + ‖(deriv (deriv (deriv f)) c / 3) * δ ^ 3‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (M * ‖δ‖ ^ 4 + M * ‖δ‖ ^ 4) + ‖(deriv (deriv (deriv f)) c / 3) * δ ^ 3‖ :=
        add_le_add (add_le_add hRp hRm) le_rfl
      _ = _ := by rw [norm_mul, norm_div, norm_pow]; norm_num; ring
  · have he : f (c + δ) - 2 * f c + f (c - δ) - deriv (deriv f) c * δ ^ 2 = Rp + Rm := by
      dsimp [Rp, Rm]
      ring
    rw [he]
    calc
      _ ≤ ‖Rp‖ + ‖Rm‖ := norm_add_le _ _
      _ ≤ M * ‖δ‖ ^ 4 + M * ‖δ‖ ^ 4 := add_le_add hRp hRm
      _ = _ := by ring

theorem model_log_first_four_derivatives {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    deriv Complex.log z = z⁻¹ ∧
      deriv (deriv Complex.log) z = -(z⁻¹ ^ 2) ∧
      deriv (deriv (deriv Complex.log)) z = 2 * z⁻¹ ^ 3 ∧
      deriv (deriv (deriv (deriv Complex.log))) z = -6 * z⁻¹ ^ 4 := by
  have h1 (w : ℂ) (hw : w ∈ Complex.slitPlane) : deriv Complex.log w = w⁻¹ := Complex.deriv_log hw
  have h2 (w : ℂ) (hw : w ∈ Complex.slitPlane) : deriv (deriv Complex.log) w = -(w⁻¹ ^ 2) := by
    have he : deriv Complex.log =ᶠ[𝓝 w] Inv.inv :=
      Filter.Eventually.mono
        (show ∀ᶠ u in 𝓝 w, u ∈ Complex.slitPlane from Complex.isOpen_slitPlane.mem_nhds hw)
        (fun u hu => h1 u hu)
    rw [he.deriv_eq, deriv_inv, inv_pow]
  have h3 (w : ℂ) (hw : w ∈ Complex.slitPlane) :
      deriv (deriv (deriv Complex.log)) w = 2 * w⁻¹ ^ 3 := by
    have he : deriv (deriv Complex.log) =ᶠ[𝓝 w] fun u => -(u⁻¹ ^ 2) :=
      Filter.Eventually.mono
        (show ∀ᶠ u in 𝓝 w, u ∈ Complex.slitPlane from Complex.isOpen_slitPlane.mem_nhds hw)
        (fun u hu => h2 u hu)
    have hd : HasDerivAt (fun u : ℂ => -(u⁻¹ ^ 2)) (2 * w⁻¹ ^ 3) w := by
      convert ((hasDerivAt_inv (Complex.slitPlane_ne_zero hw)).pow 2).neg using 1
      simp only [inv_pow]
      ring
    exact he.deriv_eq.trans hd.deriv
  have h4 (w : ℂ) (hw : w ∈ Complex.slitPlane) :
      deriv (deriv (deriv (deriv Complex.log))) w = -6 * w⁻¹ ^ 4 := by
    have he : deriv (deriv (deriv Complex.log)) =ᶠ[𝓝 w] fun u => 2 * u⁻¹ ^ 3 :=
      Filter.Eventually.mono
        (show ∀ᶠ u in 𝓝 w, u ∈ Complex.slitPlane from Complex.isOpen_slitPlane.mem_nhds hw)
        (fun u hu => h3 u hu)
    have hd : HasDerivAt (fun u : ℂ => 2 * u⁻¹ ^ 3) (-6 * w⁻¹ ^ 4) w := by
      convert ((hasDerivAt_inv (Complex.slitPlane_ne_zero hw)).pow 3).const_mul 2 using 1
      simp only [inv_pow]
      ring
    exact he.deriv_eq.trans hd.deriv
  exact ⟨h1 z hz, h2 z hz, h3 z hz, h4 z hz⟩

def modelElementary (z : ℂ) : ℂ := (-z ^ 2 / 2 + 1) * Complex.log z
def modelElementaryFirst (z : ℂ) : ℂ := -z * Complex.log z - z / 2 + z⁻¹
def modelElementarySecond (z : ℂ) : ℂ := -Complex.log z - 3 / 2 - z⁻¹ ^ 2
def modelElementaryThird (z : ℂ) : ℂ := -z⁻¹ + 2 * z⁻¹ ^ 3
def modelElementaryFourth (z : ℂ) : ℂ := z⁻¹ ^ 2 - 6 * z⁻¹ ^ 4

theorem modelElementary_hasDerivAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt modelElementary (modelElementaryFirst z) z := by
  have hn := Complex.slitPlane_ne_zero hz
  convert (((((hasDerivAt_id' z).pow 2).neg.div_const 2).add_const 1).mul
    (Complex.hasDerivAt_log hz)) using 1
  · ext w
    dsimp [modelElementary]
  · dsimp [modelElementaryFirst]
    field_simp [hn]
    ring

theorem modelElementaryFirst_hasDerivAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt modelElementaryFirst (modelElementarySecond z) z := by
  have hn := Complex.slitPlane_ne_zero hz
  convert ((((hasDerivAt_id' z).neg.mul (Complex.hasDerivAt_log hz)).sub
    ((hasDerivAt_id' z).div_const 2)).add (hasDerivAt_inv hn)) using 1
  · ext w
    dsimp [modelElementaryFirst]
  · dsimp [modelElementarySecond]
    field_simp [hn]
    ring

theorem modelElementarySecond_hasDerivAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt modelElementarySecond (modelElementaryThird z) z := by
  convert (((Complex.hasDerivAt_log hz).neg.sub_const (3 / 2)).sub
    ((hasDerivAt_inv (Complex.slitPlane_ne_zero hz)).pow 2)) using 1
  · ext w
    dsimp [modelElementarySecond]
  · dsimp [modelElementaryThird]
    simp only [inv_pow]
    ring

theorem modelElementaryThird_hasDerivAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt modelElementaryThird (modelElementaryFourth z) z := by
  convert ((hasDerivAt_inv (Complex.slitPlane_ne_zero hz)).neg.add
    (((hasDerivAt_inv (Complex.slitPlane_ne_zero hz)).pow 3).const_mul 2)) using 1
  · ext w
    dsimp [modelElementaryThird]
  · dsimp [modelElementaryFourth]
    simp only [inv_pow]
    ring

theorem modelElementary_first_four_derivatives {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    deriv modelElementary z = modelElementaryFirst z ∧
      deriv (deriv modelElementary) z = modelElementarySecond z ∧
      deriv (deriv (deriv modelElementary)) z = modelElementaryThird z ∧
      deriv (deriv (deriv (deriv modelElementary))) z = modelElementaryFourth z := by
  have h1 (w : ℂ) (hw : w ∈ Complex.slitPlane) : deriv modelElementary w = modelElementaryFirst w :=
    (modelElementary_hasDerivAt hw).deriv
  have h2 (w : ℂ) (hw : w ∈ Complex.slitPlane) :
      deriv (deriv modelElementary) w = modelElementarySecond w := by
    have he : deriv modelElementary =ᶠ[𝓝 w] modelElementaryFirst :=
      Filter.Eventually.mono
        (show ∀ᶠ u in 𝓝 w, u ∈ Complex.slitPlane from Complex.isOpen_slitPlane.mem_nhds hw)
        (fun u hu => h1 u hu)
    exact he.deriv_eq.trans (modelElementaryFirst_hasDerivAt hw).deriv
  have h3 (w : ℂ) (hw : w ∈ Complex.slitPlane) :
      deriv (deriv (deriv modelElementary)) w = modelElementaryThird w := by
    have he : deriv (deriv modelElementary) =ᶠ[𝓝 w] modelElementarySecond :=
      Filter.Eventually.mono
        (show ∀ᶠ u in 𝓝 w, u ∈ Complex.slitPlane from Complex.isOpen_slitPlane.mem_nhds hw)
        (fun u hu => h2 u hu)
    exact he.deriv_eq.trans (modelElementarySecond_hasDerivAt hw).deriv
  have h4 (w : ℂ) (hw : w ∈ Complex.slitPlane) :
      deriv (deriv (deriv (deriv modelElementary))) w = modelElementaryFourth w := by
    have he : deriv (deriv (deriv modelElementary)) =ᶠ[𝓝 w] modelElementaryThird :=
      Filter.Eventually.mono
        (show ∀ᶠ u in 𝓝 w, u ∈ Complex.slitPlane from Complex.isOpen_slitPlane.mem_nhds hw)
        (fun u hu => h3 u hu)
    exact he.deriv_eq.trans (modelElementaryThird_hasDerivAt hw).deriv
  exact ⟨h1 z hz, h2 z hz, h3 z hz, h4 z hz⟩

end
end IsingBulk.AnisoF002.NegativeHT
