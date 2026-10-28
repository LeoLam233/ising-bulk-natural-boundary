import IsingBulk.HT22.Transport.SharpCovarianceJets.Normalize

/-! Frozen manuscript sharp R ,  reciprocal-R and centered-G table for the
actual unshifted fixed-v source. Every order shares a protected ball; all
constants and geometry are chosen before N and the radial parameter. -/
namespace IsingBulk.HT22.SharpCovarianceJets
noncomputable section
open Set Metric Geometry IsingBulk.Preferred22
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem actual_sharp_covariance_jets (b : PreferredBranchData) (M : ℝ) (hM : 0 < M) :
     ∃  cap : ℝ , 0 < cap  ∧ cap < b.alpha  ∧  ∀ B : PreferredCoareaBump b , B.delta < cap  → 
     ∃  ε₀ τ₀ δB ρ₀ c₀ : ℝ , 0 < ε₀  ∧ 0 < τ₀  ∧ 0 < δB  ∧ δB < B.delta  ∧ 0 < ρ₀  ∧ 0 < c₀  ∧ 
     ∀ m : ℕ ,  ∃ C : ℝ , 0 < C  ∧  ∀ N : ℕ , 0 < N  →  ∀ ε τ μ r : ℝ , 
    0 < ε  → ε < ε₀  → 0 ≤ τ  → τ < τ₀  → 0 < r  → |μ|+r+ε ≤ M  → 
     ∀ θ : Fin N → ℝ , ( ∀ i , -δB ≤ θ i+b.b  ∧ θ i ≤ B.delta)  → 
    ( ∀ i , μ-2*r ≤ θ i+b.b  ∧ θ i+b.b ≤ μ+2*r)  → 
     ∀ i k : Fin N , ( ∀ a , θ i ≤ θ a  ∧ θ a ≤ θ k)  → r ≤ θ k-θ i  → 
    let T := |μ|+r+ε
    let Δ := r/Real.sqrt T
    let x : SourcePoint N := (IsingBulk.Branch.radialParameter b.alpha ε , 
      Tail.sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ)
    ( ∀ y ∈ ball x (ρ₀*Δ/(N:ℝ)^2) , c₀*Real.sqrt T*Δ^2 ≤ ‖sourceCovariance y.1 y.2‖)  ∧ 
    ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => sourceCovariance z.1 z.2) x‖ ≤ 
      C*(N:ℝ)^(2*m+2)*Real.sqrt T*Δ^2/Δ^m  ∧ 
    ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => (sourceCovariance z.1 z.2)⁻¹) x‖ ≤ 
      C*(N:ℝ)^(2*m+2)/(Real.sqrt T*Δ^(m+2))  ∧ 
     ∀ a , ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => sourceCentered z.1 z.2 a) x‖ ≤ 
      C*(N:ℝ)^(2*m+2)*Real.sqrt T*Δ/Δ^m := by
  obtain ⟨cap , hcap , hcapa , hsource⟩ := actual_sharp_scale_jets_uniform_cap b M hM
  refine ⟨cap , hcap , hcapa , ?_⟩
  intro B hB
  obtain ⟨A , e , t , δ , η , c , K , hA , he , ht , hδ , hδB , hη , hc , hK , hsource⟩ := hsource B
  have hKp : 0 < K := zero_lt_one.trans_le hK
  refine ⟨e , t , δ , η*K , c*K^3/2 , he , ht , hδ , hδB , by positivity , by positivity , ?_⟩
  intro m
  let AR := cauchyJetConstant m*(36*A)^2/η^m
  let AG := cauchyJetConstant m*(36*A)/η^m
  let AI := cauchyJetConstant m*2/c/η^m
  have hAR : 0 < AR := by have := cauchyJetConstant_pos m;dsimp [AR];positivity
  have hAG : 0 < AG := by have := cauchyJetConstant_pos m;dsimp [AG];positivity
  have hAI : 0 < AI := by have := cauchyJetConstant_pos m;dsimp [AI];positivity
  let C := 1+AR*K^3+AG*K^2+AI
  have hC : 0 < C := by dsimp [C];positivity
  have hRC : AR*K^3 ≤ C := by dsimp [C]; nlinarith [show 0 ≤ AG*K^2 by positivity]
  have hGC : AG*K^2 ≤ C := by dsimp [C]; nlinarith [show 0 ≤ AR*K^3 by positivity]
  have hIC : AI ≤ C := by dsimp [C]; nlinarith [show 0 ≤ AR*K^3 by positivity, show 0 ≤ AG*K^2 by positivity]
  refine ⟨C , hC , ?_⟩
  intro N hN ε τ μ r hε hεr hτ hτr hr hTM θ hθ hwindow i k hext hgap
  have hh := (hsource N hN ε τ μ r hε hεr hτ hτr hr hTM θ
    (fun a => ⟨(hθ a).1 , le_min ((hθ a).2.trans hB.le) (hθ a).2⟩) hwindow i k hext hgap).2 m
  let T := |μ|+r+ε
  let Δ := r/Real.sqrt T
  have hT : 0 < T := by dsimp [T];positivity
  have hS : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hΔ : 0 < Δ := by dsimp [Δ];positivity
  have hn1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0:ℝ) < N := zero_lt_one.trans_le hn1
  rw [show K*r/Real.sqrt (|μ|+r+ε)=K*Δ by dsimp [Δ,T];ring] at hh
  change SharpBounds _ A (K*Real.sqrt T) (K*Δ) c η m at hh
  obtain ⟨hmargin , hR , hG , hI⟩ := hh
  refine ⟨?_ , ?_ , ?_ , ?_⟩
  · intro y hy
    have hy' : y ∈ ball (IsingBulk.Branch.radialParameter b.alpha ε,
        Tail.sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ) (η*(K*Δ)/(N:ℝ)^2) := by
      simpa only [Δ,T,mul_assoc] using hy
    have hb := hmargin y hy'
    change (c*K^3/2)*Real.sqrt T*Δ^2 ≤ _
    convert hb using 1
    ring
  · change ‖_‖ ≤ C*(N:ℝ)^(2*m+2)*Real.sqrt T*Δ^2/Δ^m
    apply hR.trans
    apply (scaled_positive_envelope_le AR ((N:ℝ)^(2*m+2)) (Real.sqrt T) Δ K 2 m
      hAR.le (by positivity) hS.le hΔ hK).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hRC (by positivity)) hS.le) (by positivity)) (by positivity)
  · change ‖_‖ ≤ C*(N:ℝ)^(2*m+2)/(Real.sqrt T*Δ^(m+2))
    apply hI.trans
    apply (scaled_inverse_envelope_le AI ((N:ℝ)^(2*m)) (Real.sqrt T) Δ K m
      hAI.le (by positivity) hS hΔ hK).trans
    exact div_le_div_of_nonneg_right (mul_le_mul hIC
      (pow_le_pow_right₀ hn1 (by omega)) (by positivity) hC.le) (by positivity)
  · intro a
    change ‖_‖ ≤ C*(N:ℝ)^(2*m+2)*Real.sqrt T*Δ/Δ^m
    apply (hG a).trans
    have hb := scaled_positive_envelope_le AG ((N:ℝ)^(2*m+1)) (Real.sqrt T) Δ K 1 m
      hAG.le (by positivity) hS.le hΔ hK
    simp only [pow_one] at hb
    apply hb.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul hGC (pow_le_pow_right₀ hn1 (by omega)) (by positivity) hC.le) hS.le) hΔ.le) (by positivity)

end
end IsingBulk.HT22.SharpCovarianceJets
