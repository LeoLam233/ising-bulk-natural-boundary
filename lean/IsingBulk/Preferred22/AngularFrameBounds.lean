import IsingBulk.Preferred22.FrameWeightedBounds
import IsingBulk.Preferred22.SourceFrameFactors

/-! Quantitative source-frame calculus for the literal angular
representative. Its occupancy inverse matrix, Uq, Udot and B are retained. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem preferredAngularField_frame_bound_of_factors {N : ℕ} (hN : 0<N)
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (hBa : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredResidualCollective z.1 z.2)
      (s,preferredSourceCoordinate τ p m s θ))
    (j LM LB : ℕ) (CM CU CB D : ℝ) (hCM : 0≤CM) (hCU : 0≤CU) (hCB : 0≤CB)
    (hdiam : 0<preferredAngularDiameter θ) (hdiamD : preferredAngularDiameter θ≤D) (hD : 1≤D)
    (hMj : ∀ i b xs, xs.length≤j →
      ‖preferredFrameJet τ p m (fun _ x => (preferredContourMatrix τ p m x)⁻¹ i b) xs s θ‖≤CM*(N:ℝ)^LM)
    (hUj : ∀ i xs, xs.length≤j →
      ‖preferredFrameJet τ p m
        (fun t x => preferredSourceUQ t (preferredSourceCoordinate τ p m t x i)) xs s θ‖≤CU ∧
      ‖preferredFrameJet τ p m
        (fun t x => preferredSourceUDot t (preferredSourceCoordinate τ p m t x i)) xs s θ‖≤CU)
    (hBj : ∀ i xs, xs.length≤j →
      ‖preferredFrameJet τ p m
        (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) i) xs s θ‖≤
        CB*(N:ℝ)^LB/preferredAngularDiameter θ^(1+preferredCoordinateJetOrder xs))
    (xs : List (Option (Fin N))) (hxs : xs.length≤j) (i : Fin N) :
    ‖preferredFrameJet τ p m (fun t x => preferredSourceAngularField .right τ p m t x i) xs s θ‖≤
      (2^j*CM*CU*D^(j+1)+(2^j*CM*D^j)*(2^j*CU*D^j*CB))*
        (N:ℝ)^(LM+LB+1)/preferredAngularDiameter θ^(1+preferredCoordinateJetOrder xs) := by
  have hgeom := preferredFramePoint_eventually τ δ p m hp hm s θ hpoint hθ
  have hχ := (preferredSourceCoordinate_contDiffAt τ p m hp hm s θ hpoint.trace_im hpoint.upper).continuousAt
  have hΨ : ContinuousAt (fun z : ℂ × (Fin N → ℝ) =>
      (z.1,preferredSourceCoordinate τ p m z.1 z.2)) (s,θ) := continuousAt_fst.prodMk hχ
  have ha := hΨ.tendsto.eventually hBa.eventually_analyticAt
  obtain ⟨Ω,hΩsub,hΩ,hz⟩ := mem_nhds_iff.mp (hgeom.and ha)
  have hΩpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2 := fun z hz => (hΩsub hz).1
  obtain ⟨hMm,hQm,hDm⟩ := preferred_source_inverse_factors_mixed τ δ p m hp hm Ω hΩpoint
  have hBm (b : Fin N) : PreferredMixedSmoothOn
      (fun z => preferredResidualCollective z.1 (preferredSourceCoordinate τ p m z.1 z.2) b) Ω :=
    preferred_analytic_pullback_mixed τ δ p m hp hm Ω hΩpoint
      (fun z => preferredResidualCollective z.1 z.2 b)
      (fun z hz => analyticAt_pi_iff.mp (hΩsub hz).2 b)
  let d := preferredAngularDiameter θ
  let M := fun (b : Fin N) (_t : ℂ) (x : Fin N → ℝ) => (preferredContourMatrix τ p m x)⁻¹ i b
  let Q := fun (b : Fin N) (t : ℂ) (x : Fin N → ℝ) => preferredSourceUQ t (preferredSourceCoordinate τ p m t x b)
  let U := fun (b : Fin N) (t : ℂ) (x : Fin N → ℝ) => preferredSourceUDot t (preferredSourceCoordinate τ p m t x b)
  let B := fun (b : Fin N) (t : ℂ) (x : Fin N → ℝ) => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) b
  let C₁ := (2:ℝ)^j*CM*CU*D^(j+1)
  let C₂ := ((2:ℝ)^j*CM*D^j)*((2:ℝ)^j*CU*D^j*CB)
  have hD0 : 0≤D := le_trans (by norm_num) hD
  have hn : (1:ℝ)≤N := by exact_mod_cast Nat.succ_le_iff.mpr hN
  have hMweight (b : Fin N) (ys : List (Option (Fin N))) (hys : ys.length≤j) :
      ‖preferredFrameJet τ p m (M b) ys s θ‖≤(CM*(N:ℝ)^LM*D^j)/d^(0+preferredCoordinateJetOrder ys) := by
    simpa only [zero_add] using preferredFrameJet_bounded_to_weighted τ p m (M b) s θ j (CM*(N:ℝ)^LM) d D
      (by positivity) hdiam hdiamD hD (hMj i b) ys hys
  have hQweight (b : Fin N) (ys : List (Option (Fin N))) (hys : ys.length≤j) :
      ‖preferredFrameJet τ p m (Q b) ys s θ‖≤(CU*D^j)/d^(0+preferredCoordinateJetOrder ys) := by
    simpa only [zero_add] using preferredFrameJet_bounded_to_weighted τ p m (Q b) s θ j CU d D hCU hdiam hdiamD hD
      (fun zs hzs => (hUj b zs hzs).1) ys hys
  have hQB (b : Fin N) (ys : List (Option (Fin N))) (hys : ys.length≤j) :
      ‖preferredFrameJet τ p m (fun t x => Q b t x*B b t x) ys s θ‖≤
        (2^j*(CU*D^j)*(CB*(N:ℝ)^LB))/d^(1+preferredCoordinateJetOrder ys) := by
    simpa only [zero_add] using preferredFrameJet_mul_weighted_bound τ δ p m hp hm Ω hΩ hΩpoint
      (Q b) (B b) (hQm b) (hBm b) s θ hz j 0 1 (CU*D^j) (CB*(N:ℝ)^LB) d
      (by positivity) (by positivity) hdiam (hQweight b) (hBj b) ys hys
  have hfirst (b : Fin N) :
      ‖preferredFrameJet τ p m (fun t x => M b t x*U b t x) xs s θ‖≤
        C₁*(N:ℝ)^(LM+LB)/d^(1+preferredCoordinateJetOrder xs) := by
    have hh := preferredFrameJet_mul_bound τ δ p m hp hm Ω hΩ hΩpoint
      (M b) (U b) (hMm i b) (hDm b) s θ hz j (CM*(N:ℝ)^LM) CU (by positivity) hCU
      (hMj i b) (fun ys hys => (hUj b ys hys).2) xs hxs
    have he := inverse_power_loss_bound d D hdiam hdiamD hD 0
      (1+preferredCoordinateJetOrder xs) (j+1) (Nat.zero_le _) (by
        have := (preferredCoordinateJetOrder_le_length xs).trans hxs
        omega)
    simp only [pow_zero,div_one] at he
    have hpow : (N:ℝ)^LM≤(N:ℝ)^(LM+LB) := pow_le_pow_right₀ hn (Nat.le_add_right _ _)
    apply hh.trans
    calc
      _ ≤ (2^j*(CM*(N:ℝ)^LM)*CU)*(D^(j+1)/d^(1+preferredCoordinateJetOrder xs)) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by positivity : 0≤2^j*(CM*(N:ℝ)^LM)*CU)
      _ = C₁*(N:ℝ)^LM/d^(1+preferredCoordinateJetOrder xs) := by dsimp [C₁]; ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by dsimp [C₁]; positivity)) (by positivity)
  have hsecond (b : Fin N) :
      ‖preferredFrameJet τ p m (fun t x => M b t x*(Q b t x*B b t x)) xs s θ‖≤
        C₂*(N:ℝ)^(LM+LB)/d^(1+preferredCoordinateJetOrder xs) := by
    have hh := preferredFrameJet_mul_weighted_bound τ δ p m hp hm Ω hΩ hΩpoint
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
  have hfun : (fun t x => preferredSourceAngularField .right τ p m t x i)=
      (fun t x => (-1:ℂ)*(∑ b, H b t x)) := by
    funext t x
    simp only [preferredSourceAngularField,preferredAngularRepresentative,preferredResidualField,
      Matrix.mulVec,dotProduct,H,M,U,Q,B,mul_add,Finset.sum_add_distrib]
    ring
  rw [hfun,preferredFrameJet_const_mul τ δ p m hp hm Ω hΩ hΩpoint _
    (PreferredMixedSmoothOn.sum hHm) (-1) xs s θ hz,
    preferredFrameJet_sum τ δ p m hp hm Ω hΩ hΩpoint H hHm xs s θ hz,norm_mul]
  norm_num only [norm_neg,norm_one,one_mul]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _b : Fin N, (C₁+C₂)*(N:ℝ)^(LM+LB)/d^(1+preferredCoordinateJetOrder xs) := by
      apply Finset.sum_le_sum
      intro b _
      rw [show H b=(fun t x => M b t x*U b t x+M b t x*(Q b t x*B b t x)) by rfl]
      rw [preferredFrameJet_add τ δ p m hp hm Ω hΩ hΩpoint _ _
        ((hMm i b).mul (hDm b)) ((hMm i b).mul ((hQm b).mul (hBm b))) xs s θ hz]
      apply (norm_add_le _ _).trans
      calc
        _ ≤ C₁*(N:ℝ)^(LM+LB)/d^(1+preferredCoordinateJetOrder xs)+
            C₂*(N:ℝ)^(LM+LB)/d^(1+preferredCoordinateJetOrder xs) :=
          add_le_add (hfirst b) (hsecond b)
        _ = _ := by ring
    _ = _ := by simp; rw [pow_succ]; dsimp [C₁,C₂,d]; ring

end
end IsingBulk.Preferred22
