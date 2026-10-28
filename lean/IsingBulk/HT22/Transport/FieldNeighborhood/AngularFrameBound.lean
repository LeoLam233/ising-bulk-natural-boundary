import IsingBulk.HT22.Tail.TotalFrameBounds

/-! Total-order fixed-v angular-field bound for the actual mixed residual.
The finite product proof adapts the published field-independent angular
representative algebra; no old collective field or derivative estimate is used. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open Filter Set IsingBulk.Preferred22
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem angularField_frame_bound_of_factors {N : ℕ} (hN : 0<N)
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hΩpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (hMm : ∀ i b, PreferredMixedSmoothOn
      (fun z => (preferredContourMatrix τ p m z.2)⁻¹ i b) Ω)
    (hQm : ∀ i, PreferredMixedSmoothOn
      (fun z => inverseV z.1 (sourceCoordinate τ p m z.1 z.2 i)) Ω)
    (hDm : ∀ i, PreferredMixedSmoothOn
      (fun z => inverseT z.1 (sourceCoordinate τ p m z.1 z.2 i)) Ω)
    (hBm : ∀ i, PreferredMixedSmoothOn
      (fun z => sourceResidual z.1 (sourceCoordinate τ p m z.1 z.2) i) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (d : ℝ)
    (j LM LB : ℕ) (CM CU CB D : ℝ) (hCM : 0≤CM) (hCU : 0≤CU) (hCB : 0≤CB)
    (hdiam : 0<d) (hdiamD : d≤D) (hD : 1≤D)
    (hMj : ∀ i b xs, xs.length≤j →
      ‖frameJet τ p m (fun _ x => (preferredContourMatrix τ p m x)⁻¹ i b) xs s θ‖≤CM*(N:ℝ)^LM)
    (hUj : ∀ i xs, xs.length≤j →
      ‖frameJet τ p m
        (fun t x => inverseV t (sourceCoordinate τ p m t x i)) xs s θ‖≤CU ∧
      ‖frameJet τ p m
        (fun t x => inverseT t (sourceCoordinate τ p m t x i)) xs s θ‖≤CU)
    (hBj : ∀ i xs, xs.length≤j →
      ‖frameJet τ p m
        (fun t x => sourceResidual t (sourceCoordinate τ p m t x) i) xs s θ‖≤
        CB*(N:ℝ)^LB/d^(1+xs.length))
    (xs : List (Option (Fin N))) (hxs : xs.length≤j) (i : Fin N) :
    ‖frameJet τ p m (fun t x => angularField τ p m t x i) xs s θ‖≤
      (2^j*CM*CU*D^(j+1)+(2^j*CM*D^j)*(2^j*CU*D^j*CB))*
        (N:ℝ)^(LM+LB+1)/d^(1+xs.length) := by
  let M := fun (b : Fin N) (_t : ℂ) (x : Fin N → ℝ) => (preferredContourMatrix τ p m x)⁻¹ i b
  let Q := fun (b : Fin N) (t : ℂ) (x : Fin N → ℝ) => inverseV t (sourceCoordinate τ p m t x b)
  let U := fun (b : Fin N) (t : ℂ) (x : Fin N → ℝ) => inverseT t (sourceCoordinate τ p m t x b)
  let B := fun (b : Fin N) (t : ℂ) (x : Fin N → ℝ) => sourceResidual t (sourceCoordinate τ p m t x) b
  let C₁ := (2:ℝ)^j*CM*CU*D^(j+1)
  let C₂ := ((2:ℝ)^j*CM*D^j)*((2:ℝ)^j*CU*D^j*CB)
  have hD0 : 0≤D := le_trans (by norm_num) hD
  have hn : (1:ℝ)≤N := by exact_mod_cast Nat.succ_le_iff.mpr hN
  have hMweight (b : Fin N) (ys : List (Option (Fin N))) (hys : ys.length≤j) :
      ‖frameJet τ p m (M b) ys s θ‖≤(CM*(N:ℝ)^LM*D^j)/d^(0+ys.length) := by
    simpa only [zero_add] using frameJet_bounded_to_weighted τ p m (M b) s θ j (CM*(N:ℝ)^LM) d D
      (by positivity) hdiam hdiamD hD (hMj i b) ys hys
  have hQweight (b : Fin N) (ys : List (Option (Fin N))) (hys : ys.length≤j) :
      ‖frameJet τ p m (Q b) ys s θ‖≤(CU*D^j)/d^(0+ys.length) := by
    simpa only [zero_add] using frameJet_bounded_to_weighted τ p m (Q b) s θ j CU d D hCU hdiam hdiamD hD
      (fun zs hzs => (hUj b zs hzs).1) ys hys
  have hQB (b : Fin N) (ys : List (Option (Fin N))) (hys : ys.length≤j) :
      ‖frameJet τ p m (fun t x => Q b t x*B b t x) ys s θ‖≤
        (2^j*(CU*D^j)*(CB*(N:ℝ)^LB))/d^(1+ys.length) := by
    simpa only [zero_add] using frameJet_mul_weighted_bound τ δ p m hp hm Ω hΩ hΩpoint hR
      (Q b) (B b) (hQm b) (hBm b) s θ hz j 0 1 (CU*D^j) (CB*(N:ℝ)^LB) d
      (by positivity) (by positivity) hdiam (hQweight b) (hBj b) ys hys
  have hfirst (b : Fin N) :
      ‖frameJet τ p m (fun t x => M b t x*U b t x) xs s θ‖≤
        C₁*(N:ℝ)^(LM+LB)/d^(1+xs.length) := by
    have hh := frameJet_mul_bound τ δ p m hp hm Ω hΩ hΩpoint hR
      (M b) (U b) (hMm i b) (hDm b) s θ hz j (CM*(N:ℝ)^LM) CU (by positivity) hCU
      (hMj i b) (fun ys hys => (hUj b ys hys).2) xs hxs
    have he := inverse_power_loss_bound d D hdiam hdiamD hD 0
      (1+xs.length) (j+1) (Nat.zero_le _) (by
        have := hxs
        omega)
    simp only [pow_zero,div_one] at he
    have hpow : (N:ℝ)^LM≤(N:ℝ)^(LM+LB) := pow_le_pow_right₀ hn (Nat.le_add_right _ _)
    apply hh.trans
    calc
      _ ≤ (2^j*(CM*(N:ℝ)^LM)*CU)*(D^(j+1)/d^(1+xs.length)) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by positivity : 0≤2^j*(CM*(N:ℝ)^LM)*CU)
      _ = C₁*(N:ℝ)^LM/d^(1+xs.length) := by dsimp [C₁]; ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by dsimp [C₁]; positivity)) (by positivity)
  have hsecond (b : Fin N) :
      ‖frameJet τ p m (fun t x => M b t x*(Q b t x*B b t x)) xs s θ‖≤
        C₂*(N:ℝ)^(LM+LB)/d^(1+xs.length) := by
    have hh := frameJet_mul_weighted_bound τ δ p m hp hm Ω hΩ hΩpoint hR
      (M b) (fun t x => Q b t x*B b t x) (hMm i b) ((hQm b).mul (hBm b)) s θ hz j 0 1
      (CM*(N:ℝ)^LM*D^j) (2^j*(CU*D^j)*(CB*(N:ℝ)^LB)) d
      (by positivity) (by positivity) hdiam (hMweight b) (hQB b) xs hxs
    apply hh.trans_eq
    simp only [zero_add]
    dsimp [C₂]
    rw [pow_add (N:ℝ) LM LB]
    ring
  let H := fun (b : Fin N) (t : ℂ) (x : Fin N → ℝ) =>
    M b t x*U b t x+M b t x*(Q b t x*B b t x)
  have hHm (b : Fin N) : PreferredMixedSmoothOn (fun z => H b z.1 z.2) Ω :=
    ((hMm i b).mul (hDm b)).add ((hMm i b).mul ((hQm b).mul (hBm b)))
  have hfun : (fun t x => angularField τ p m t x i)=
      (fun t x => (-1:ℂ)*(∑ b, H b t x)) := by
    funext t x
    simp only [angularField,preferredAngularRepresentative,residualField,
      Matrix.mulVec,dotProduct,H,M,U,Q,B,mul_add,Finset.sum_add_distrib]
    ring
  rw [hfun,frameJet_const_mul τ δ p m hp hm Ω hΩ hΩpoint hR _
    (PreferredMixedSmoothOn.sum hHm) (-1) xs s θ hz,
    frameJet_sum τ δ p m hp hm Ω hΩ hΩpoint hR H hHm xs s θ hz,norm_mul]
  norm_num only [norm_neg,norm_one,one_mul]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _b : Fin N, (C₁+C₂)*(N:ℝ)^(LM+LB)/d^(1+xs.length) := by
      apply Finset.sum_le_sum
      intro b _
      rw [show H b=(fun t x => M b t x*U b t x+M b t x*(Q b t x*B b t x)) by rfl]
      rw [frameJet_add τ δ p m hp hm Ω hΩ hΩpoint hR _ _
        ((hMm i b).mul (hDm b)) ((hMm i b).mul ((hQm b).mul (hBm b))) xs s θ hz]
      apply (norm_add_le _ _).trans
      calc
        _ ≤ C₁*(N:ℝ)^(LM+LB)/d^(1+xs.length)+
            C₂*(N:ℝ)^(LM+LB)/d^(1+xs.length) :=
          add_le_add (hfirst b) (hsecond b)
        _ = _ := by ring
    _ = _ := by simp; rw [pow_succ]; dsimp [C₁,C₂]; ring

theorem angularField_frame_polynomial_bound {N : ℕ} (hN : 0<N)
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hΩpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (hMm : ∀ i b, PreferredMixedSmoothOn
      (fun z => (preferredContourMatrix τ p m z.2)⁻¹ i b) Ω)
    (hQm : ∀ i, PreferredMixedSmoothOn
      (fun z => inverseV z.1 (sourceCoordinate τ p m z.1 z.2 i)) Ω)
    (hDm : ∀ i, PreferredMixedSmoothOn
      (fun z => inverseT z.1 (sourceCoordinate τ p m z.1 z.2 i)) Ω)
    (hBm : ∀ i, PreferredMixedSmoothOn
      (fun z => sourceResidual z.1 (sourceCoordinate τ p m z.1 z.2) i) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (d : ℝ)
    (j L LB : ℕ) (C CB D : ℝ) (hC : 0≤C) (hCB : 0≤CB)
    (hdiam : 0<d) (hdiamD : d≤D) (hD : 1≤D)
    (hMj : ∀ i b xs, xs.length≤j →
      ‖frameJet τ p m (fun _ x => (preferredContourMatrix τ p m x)⁻¹ i b) xs s θ‖≤C*(N:ℝ)^L)
    (hUj : ∀ i xs, xs.length≤j →
      ‖frameJet τ p m
        (fun t x => inverseV t (sourceCoordinate τ p m t x i)) xs s θ‖≤C*(N:ℝ)^L ∧
      ‖frameJet τ p m
        (fun t x => inverseT t (sourceCoordinate τ p m t x i)) xs s θ‖≤C*(N:ℝ)^L)
    (hBj : ∀ i xs, xs.length≤j →
      ‖frameJet τ p m
        (fun t x => sourceResidual t (sourceCoordinate τ p m t x) i) xs s θ‖≤
        CB*(N:ℝ)^LB/d^(1+xs.length))
    (xs : List (Option (Fin N))) (hxs : xs.length≤j) (i : Fin N) :
    ‖frameJet τ p m (fun t x => angularField τ p m t x i) xs s θ‖≤
      (2^j*C^2*D^(j+1)+(2^j*C*D^j)*(2^j*C*D^j*CB))*
        (N:ℝ)^(2*L+LB+1)/d^(1+xs.length) := by
  have hh := angularField_frame_bound_of_factors hN τ δ p m hp hm Ω hΩ hΩpoint hR
    hMm hQm hDm hBm s θ hz d j L LB C (C*(N:ℝ)^L) CB D hC (by positivity) hCB
    hdiam hdiamD hD hMj hUj hBj xs hxs i
  apply hh.trans_eq
  rw [show 2*L+LB+1=L+(L+LB+1) by omega,pow_add]
  ring

end
end IsingBulk.HT22.Tail
