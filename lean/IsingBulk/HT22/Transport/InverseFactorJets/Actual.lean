import IsingBulk.HT22.Transport.InverseFactorJets.Conversion

/-! Uniform actual inverse-factor frame budgets. The cap is chosen before the
bump; the single epsilon/tau/negative-sliver domain is chosen before both the
finite derivative order and the unbounded particle number. -/
namespace IsingBulk.HT22.InverseFactorJets
noncomputable section
open Set Filter IsingBulk.Preferred22 IsingBulk.HT22.Tail IsingBulk.HT22.SeedFrameConversion
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- All literal fixed-v source-frame words of the actual inverse occupancy
matrix and both actual inverse derivatives have a fixed-order polynomial
particle cost. No derivative estimate, covariance separation, or analytic
continuation of a real smooth bump is a premise. -/
theorem actual_inverse_factor_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ J : ℕ, ∃ C : ℝ, 1≤C ∧
      ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
      ∀ xs : List (Option (Fin N)), xs.length≤J →
      (∀ i a, ‖frameJet τ B.p B.m
        (fun _ x => (preferredContourMatrix τ B.p B.m x)⁻¹ i a) xs
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C*(N:ℝ)^(J*J+4*J)) ∧
      (∀ i, ‖frameJet τ B.p B.m
        (fun t x => inverseV t (sourceCoordinate τ B.p B.m t x i)) xs
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C*(N:ℝ)^(J*J+4*J) ∧
        ‖frameJet τ B.p B.m
        (fun t x => inverseT t (sourceCoordinate τ B.p B.m t x i)) xs
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C*(N:ℝ)^(J*J+4*J)) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := preferred_actual_angular_frame_control d
  obtain ⟨εb,hεb,hbranch⟩ := Anchor.actual_branch_velocity_jets d
  obtain ⟨rB,hrB,hBa⟩ := Metric.eventually_nhds_iff.mp
    (preferredMovingBranch_analyticAt_reference d).eventually_analyticAt
  let K := Metric.closedBall (preferredSelectedPoint d) (rB/2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKa : ∀ t∈K, AnalyticAt ℂ preferredMovingBranch t := by
    intro t ht
    apply hBa
    have hh : dist t (preferredSelectedPoint d)≤rB/2 := ht
    linarith
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨εS,τS,δS,hεS,hτS,hδS,hδSB,hS⟩ := hsource B hBcap
  obtain ⟨δ,εF,τF,_hδ,_hδa,hεF,hτF,hframe⟩ := preferred_actual_frame_points d B
  refine ⟨min εS (min εF (min εb (rB/2))),min τS τF,δS,
    lt_min hεS (lt_min hεF (lt_min hεb (half_pos hrB))),
    lt_min hτS hτF,hδS,hδSB,?_⟩
  intro J
  obtain ⟨A,hA,hAb⟩ := hS J
  obtain ⟨C,hC,hCb⟩ := coefficients_compact_bound K hK hKa J
  choose V hV hVb using hbranch
  let W := 1+∑ k∈Finset.range (J+1), V k
  have hWsum : 0≤∑ k∈Finset.range (J+1), V k :=
    Finset.sum_nonneg (fun k _ => zero_le_one.trans (hV k))
  have hW : 1≤W := by dsimp [W]; linarith
  have hVW (k : ℕ) (hk : k≤J) : V k≤W := by
    have hh := Finset.single_le_sum (fun l (_ : l∈Finset.range (J+1)) => zero_le_one.trans (hV l))
      (show k∈Finset.range (J+1) by simp; omega)
    dsimp [W]
    linarith
  let D := A^2+A+2^J*A*W
  have hD : 1≤D := by
    have : 0≤2^J*A*W := by positivity
    dsimp [D]
    nlinarith [sq_nonneg A]
  have hDA : A≤D := by
    dsimp [D]
    nlinarith [sq_nonneg A,show 0≤2^J*A*W by positivity]
  have hDA2 : A^2≤D := by
    dsimp [D]
    nlinarith [show 0≤2^J*A*W by positivity]
  have hDU : A+2^J*A*W≤D := by dsimp [D]; nlinarith [sq_nonneg A]
  refine ⟨3^J*C*D,one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hC) hD,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ xs hxs
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have heS := hεr.trans_le (min_le_left _ _)
  have heF := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heB := hεr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heK := hεr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have htS := hτr.trans_le (min_le_left _ _)
  have htF := hτr.trans_le (min_le_right _ _)
  obtain ⟨hpoint,hθstrict⟩ := hframe δS hδS hδSB N hN ε τ hε heF hτ htF θ hθ
  obtain ⟨_hMall,hM,hMj,hU,hG⟩ := hAb N hN ε τ hε heS hτ htS θ hθ
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hsK : s∈K := by
    change dist s (preferredSelectedPoint d)≤rB/2
    rw [dist_eq_norm,preferred_radial_distance,abs_of_pos hε]
    exact heK.le
  obtain ⟨Ω,hsub,hΩ,hz⟩ := mem_nhds_iff.mp
    (preferredFramePoint_eventually τ δ B.p B.m B.smooth B.m_smooth s θ hpoint hθstrict)
  have hpoints : ∀ z∈Ω, PreferredFramePoint τ δ B.p B.m z.1 z.2 := fun z hz => hsub hz
  obtain ⟨hvmix,htmix⟩ := inverse_factors_mixed τ δ B.p B.m B.smooth B.m_smooth Ω hΩ hpoints
  have hnpow : 1≤(N:ℝ)^(J*J+3*J) := one_le_pow₀ hn
  have hDN : D≤D*(N:ℝ)^(J*J+3*J) := le_mul_of_one_le_right (zero_le_one.trans hD) hnpow
  have hconvert (F : ℂ → (Fin N → ℝ) → ℂ)
      (hFm : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
      (hFb : ∀ ys : List (Option (Fin N)), ys.length≤J →
        ‖preferredFrameJet τ B.p B.m F ys s θ‖≤D*(N:ℝ)^(J*J+3*J)) :
      ‖frameJet τ B.p B.m F xs s θ‖≤(3^J*C*D)*(N:ℝ)^(J*J+4*J) := by
    have hh := frameJet_bound_of_shared τ δ B.p B.m B.smooth B.m_smooth Ω hΩ hpoints F hFm
      J C (D*(N:ℝ)^(J*J+3*J)) (zero_le_one.trans hC) (by positivity) 1 s θ hz
      (fun cs hcs => hCb cs hcs s hsK) (by simpa only [one_mul] using hFb) xs hxs
    simp only [one_mul] at hh
    have hg := conversion_polynomial_growth N J (J*J+3*J) hN D C
      (zero_le_one.trans hD) (zero_le_one.trans hC)
    convert hh.trans hg using 1
    congr 2
    omega
  constructor
  · intro i a
    have hentry : ContDiff ℝ ∞ (fun x : Fin N → ℝ => (preferredContourMatrix τ B.p B.m x)⁻¹ i a) :=
      contDiff_pi.mp (contDiff_pi.mp hM i) a
    have hmixed : PreferredMixedSmoothOn
        (fun z : ℂ × (Fin N → ℝ) => (preferredContourMatrix τ B.p B.m z.2)⁻¹ i a) Ω := by
      intro z _
      exact ⟨hentry.contDiffAt.comp z contDiffAt_snd,differentiableAt_const (𝕜 := ℂ) ((preferredContourMatrix τ B.p B.m z.2)⁻¹ i a)⟩
    apply hconvert _ hmixed
    intro ys hys
    have hh := hG _ hentry (A*(N:ℝ)^J) (by positivity) (hMj i a) ys hys
    have heq : A*(N:ℝ)^(J*J+2*J)*(A*(N:ℝ)^J)=A^2*(N:ℝ)^(J*J+3*J) := by
      rw [show J*J+3*J=(J*J+2*J)+J by omega,pow_add]
      ring
    rw [heq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hDA2 (by positivity))
  · intro i
    constructor
    · apply hconvert _ (hvmix i)
      intro ys hys
      simpa only [inverseV_moving_adapter,sourceCoordinate_moving_adapter] using
        ((hU ys hys i).1.trans (hDA.trans hDN))
    · apply hconvert _ (htmix i)
      intro ys hys
      have hb (zs : List (Option (Fin N))) (hzs : zs.length≤J) :
          ‖preferredFrameJet τ B.p B.m (fun t _ => deriv preferredMovingBranch t) zs s θ‖≤W := by
        obtain ⟨ha,hj⟩ := hVb zs.length ε hε heB
        exact Anchor.branch_velocity_frame_bound τ δ B.p B.m B.smooth B.m_smooth s θ
          hpoint hθstrict zs W (zero_le_one.trans hW) ha (hj.trans (hVW zs.length hzs))
      exact (shared_inverseT_frame_bound τ δ B.p B.m B.smooth B.m_smooth Ω hΩ hpoints
        s θ hz J A W (zero_le_one.trans hA) (zero_le_one.trans hW) hU hb ys hys i).trans
        (hDU.trans hDN)

end
end IsingBulk.HT22.InverseFactorJets
