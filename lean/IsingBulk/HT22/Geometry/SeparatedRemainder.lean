import IsingBulk.HT22.Geometry.AmbientRemainder
import IsingBulk.Preferred22.EqualityCutoff

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Filter IsingBulk.Preferred22
open scoped Topology BigOperators ContDiff

theorem actualEqualitySize_le_diameter_sq {N : ℕ} (θ : Fin N → ℝ) :
    preferredEqualitySize θ≤(N:ℝ)^2*(preferredAngularDiameter θ)^2 := by
  have hp (a b : Fin N) : (θ a-θ b)^2≤(preferredAngularDiameter θ)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (θ a-θ b))
      (preferredAngularDiameter_pair_le θ a b) 2
    simpa only [sq_abs] using hh
  unfold preferredEqualitySize
  calc
    _ ≤ ∑ _a : Fin N,∑ _b : Fin N,(preferredAngularDiameter θ)^2 :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hp a b))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring


def separatedAmbientRemainder {n : ℕ} (r : ℝ) (rem : (Fin n → ℝ) → ℝ)
    (w : Fin (n+1) → ℝ) : ℂ :=
  (preferredEqualityCutoff r w:ℂ)*(ambientRemainder rem w:ℂ)

theorem separatedAmbientRemainder_smooth {n : ℕ} (r : ℝ) (rem : (Fin n → ℝ) → ℝ)
    (hrem : ContDiff ℝ ∞ rem) : ContDiff ℝ ∞ (separatedAmbientRemainder r rem) :=
  (Complex.ofRealCLM.contDiff.comp (preferredEqualityCutoff_smooth r)).mul
    (Complex.ofRealCLM.contDiff.comp (ambientRemainder_contDiff rem hrem))

theorem separatedAmbientRemainder_zero_germ_small {n : ℕ} {r : ℝ} (hr : 0<r)
    (rem : (Fin n → ℝ) → ℝ) (w : Fin (n+1) → ℝ)
    (hD : preferredAngularDiameter w<r/(2*((n+1:ℕ):ℝ))) :
    separatedAmbientRemainder r rem =ᶠ[𝓝 w] (fun _ => 0) := by
  have hNr : 0<((n+1:ℕ):ℝ) := by positivity
  have hd : 0≤preferredAngularDiameter w := Metric.diam_nonneg
  have hh := (lt_div_iff₀ (by positivity : 0<2*((n+1:ℕ):ℝ))).mp hD
  have hsq : (preferredAngularDiameter w*(2*((n+1:ℕ):ℝ)))^2<r^2 := by
    nlinarith [mul_pos (sub_pos.mpr hh) (show 0<r+preferredAngularDiameter w*(2*((n+1:ℕ):ℝ)) by positivity)]
  have hx : preferredEqualitySize w/r^2<(1/4:ℝ) := by
    apply (div_lt_iff₀ (sq_pos_of_pos hr)).mpr
    nlinarith [actualEqualitySize_le_diameter_sq w]
  have hc : ContinuousAt (fun x : Fin (n+1) → ℝ => preferredEqualitySize x/r^2) w :=
    (preferredEqualitySize_smooth.continuous.div_const _).continuousAt
  filter_upwards [hc.eventually_lt continuousAt_const hx] with x hx
  simp only [separatedAmbientRemainder,preferredEqualityCutoff,preferredPopulationCutoff_zero hx.le,
    Complex.ofReal_zero,zero_mul]

theorem separatedAmbientRemainder_zero_germ {n : ℕ} {r : ℝ} (hr : 0<r)
    (rem : (Fin n → ℝ) → ℝ) (w : Fin (n+1) → ℝ)
    (hD : preferredAngularDiameter w=0) :
    separatedAmbientRemainder r rem =ᶠ[𝓝 w] (fun _ => 0) :=
  separatedAmbientRemainder_zero_germ_small hr rem w (by rw [hD]; positivity)

theorem separatedAmbientRemainder_weighted_lift_eq {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB r : ℝ} (hr : 0<r) (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData d B δB rcut) (a : ℝ) (rem : (Fin n → ℝ) → ℝ)
    (hfar : ∀ θ∈signedRightRegion a d B δB,rem θ≠0 →
      r<preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAtTotal a θ)))
    (θ : Fin n → ℝ) (hθ : θ∈angularBox n) :
    let w := preferredLiftedAngles B.delta (constrainedAtTotal a θ)
    separatedAmbientRemainder r rem w * (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut w:ℂ)=
      (rem θ:ℂ) * (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut w:ℂ) := by
  let w := preferredLiftedAngles B.delta (constrainedAtTotal a θ)
  change separatedAmbientRemainder r rem w * _ = _
  have he := ambientRemainder_weighted_lift_eq d B rcut hcut a θ hθ rem
  change ambientRemainder rem w * _ = _ at he
  unfold separatedAmbientRemainder
  rw [mul_assoc,←Complex.ofReal_mul,he,Complex.ofReal_mul]
  by_cases hz : rem θ=0
  · simp only [hz,Complex.ofReal_zero,zero_mul,mul_zero]
  by_cases hw : preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut w=0
  · dsimp only [w] at hw
    simp only [hw,Complex.ofReal_zero,mul_zero]
  have hreg : θ∈signedRightRegion a d B δB := ⟨hθ,actualCellWeight_right_support d B rcut hcut w
    (preferredLiftedAngles_mem_oneSided B.delta _) hw⟩
  have hD := hfar θ hreg hz
  have heq : preferredEqualityCutoff r w=1 := by
    apply preferredPopulationCutoff_one
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    have hs := preferredEqualitySize_diameter_sq w
    change r<preferredAngularDiameter w at hD
    nlinarith [Metric.diam_nonneg (s := Set.range w)]
  rw [heq,Complex.ofReal_one,one_mul]

/-- The one-particle remainder vanishes identically; no N≥3 coarea
estimate is needed for this lower-order edge case. -/
theorem separatedAmbientRemainder_singleton_zero {r : ℝ} (hr : 0<r)
    (rem : (Fin 0 → ℝ) → ℝ) (w : Fin 1 → ℝ) : separatedAmbientRemainder r rem w=0 := by
  have hd : preferredAngularDiameter w=0 := by
    have he : Set.range w={w 0} := by
      ext x
      constructor
      · rintro ⟨i,rfl⟩
        have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
        simp only [hi,mem_singleton_iff]
      · intro hx
        exact ⟨0, (Set.mem_singleton_iff.mp hx).symm⟩
    simp only [preferredAngularDiameter,he,Metric.diam_singleton]
  exact (separatedAmbientRemainder_zero_germ hr rem w hd).self_of_nhds

end
end IsingBulk.HT22.Geometry
