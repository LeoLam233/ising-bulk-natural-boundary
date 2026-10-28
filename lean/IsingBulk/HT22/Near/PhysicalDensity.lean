import IsingBulk.HT22.Tail.ActualNearQuadraticFull
import IsingBulk.HT22.Far.SignedDensityFactor

/-! The actual same transported physical density, not an abstract shell
majorant, retains its full squared collision degree and signed resolvent. -/
namespace IsingBulk.HT22.Near
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Geometry Set
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem actual_near_physical_density (d : PreferredBranchData) (M : ℝ) (hM : 0<M) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ k : ℕ, ∃ E : ℝ, 1≤E ∧ ∀ a : ℝ, ∀ n : ℕ, ∀ ε τ μ r : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → |μ|+r+ε≤M →
      ∀ θ : Fin (2*n+1) → ℝ,
      (∀ i, -δB≤θ i+d.b ∧ θ i≤B.delta) →
      (∀ i, μ-2*r≤θ i+d.b ∧ θ i+d.b≤μ+2*r) →
      ∀ i l : Fin (2*n+1), (∀ b, θ i≤θ b ∧ θ b≤θ l) → r≤θ l-θ i →
      ‖transportedDensity (Complex.exp (-Complex.I*(a:ℂ))) τ preferredPopulationCutoff B.p B.m rcut k
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
      (E^((2*n+1)^2)*(r/Real.sqrt (|μ|+r+ε))^((2*n+1)*(2*n))/
        (r/Real.sqrt (|μ|+r+ε))^(2*k))*signedJacobianResolvent a d B ε τ θ := by
  obtain ⟨cn,hcn,hcna,hn⟩ := actual_near_scalar_quadratic_full d M hM
  obtain ⟨cc,hcc,_hcca,hc⟩ := actual_collision_source_chart d
  refine ⟨min cn cc,lt_min hcn hcc,(min_le_left _ _).trans_lt hcna,?_⟩
  intro B hB
  obtain ⟨_cap,en,tn,bn,_D,_hcap,_hcapa,hen,htn,hbn,hbnB,_hD,hnear⟩ := hn B (hB.trans_le (min_le_left _ _))
  obtain ⟨c,δ,ec,tc,bc,_hc,hec,htc,hbc,hbcB,hchart⟩ := hc B (hB.trans_le (min_le_right _ _))
  obtain ⟨J,eJ,hJ,heJ,hJbound⟩ := Far.signed_actual_JH_bound d B
  let e := min en (min ec eJ)
  let t := min 1 (min tn tc)
  let b := min bn bc
  refine ⟨e,t,b,lt_min hen (lt_min hec heJ),lt_min zero_lt_one (lt_min htn htc),
    lt_min hbn hbc,(min_le_left _ _).trans_lt hbnB,?_⟩
  intro rcut hrcut hperiod k
  obtain ⟨E,hE,hEb⟩ := hnear rcut hrcut hperiod k
  let F := 2*max 1 J
  have hF : 1≤F := by dsimp [F];linarith [le_max_left (1:ℝ) J]
  refine ⟨F*E,one_le_mul_of_one_le_of_one_le hF hE,?_⟩
  intro a n ε τ μ r hε hεe hτ hτt hr hTM θ hθ hwin i l hext hgap
  have hes : ε<en ∧ ε<ec ∧ ε<eJ := by simpa only [e,lt_min_iff] using hεe
  have hts : τ<1 ∧ τ<tn ∧ τ<tc := by simpa only [t,lt_min_iff] using hτt
  have hnθ (i) : -bn≤θ i+d.b ∧ θ i≤B.delta :=
    ⟨by have := (hθ i).1;have hb : b≤bn := min_le_left _ _;linarith,(hθ i).2⟩
  have hcθ (i) : -bc≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta := by
    have hb : b≤bc := min_le_right _ _
    constructor <;> linarith [(hθ i).1,(hθ i).2]
  obtain ⟨Ω,hΩ,hz,hpoint,hR,_hgood⟩ := hchart (2*n+1) (by omega) ε τ μ r
    hε hes.2.1 hτ hts.2.2 hr θ hcθ hwin i l hext hgap
  have hs := hEb n ε τ μ r hε hes.1 hτ hts.2.1 hr hTM θ hnθ hwin i l hext hgap
  have hjθ (i) : θ i∈Icc (-Real.pi-B.delta) B.delta := by
    have hbB : b<B.delta := (min_le_left _ _).trans_lt hbnB
    constructor <;> linarith [(hθ i).1,(hθ i).2,d.b_lt]
  have hj := hJbound a (2*n+1) (by omega) ε τ hε hes.2.2 hτ hts.1.le θ hjθ
  have hσ : ‖Complex.exp (-Complex.I*(a:ℂ))‖≤1 := by
    rw [Complex.norm_exp]
    simp
  rw [transportedDensity_eq_reconstructed (by omega) _ hσ τ δ preferredPopulationCutoff B.p B.m rcut
    preferredPopulationCutoff_smooth B.smooth B.m_smooth hrcut Ω hΩ hpoint hR k _ θ hz,
    reconstructedDensity_eq_source _ τ δ preferredPopulationCutoff B.p B.m rcut k _ θ (hpoint _ hz),
    ←mul_assoc,norm_mul]
  have hnn : 2*n+1≤(2*n+1)^2 := by nlinarith
  have h2 : (2:ℝ)≤2^(2*n+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : 1≤2*n+1)
  have hJF : 2*J^(2*n+1)≤F^((2*n+1)^2) := by
    calc
      _ ≤ 2^(2*n+1)*(max 1 J)^(2*n+1) :=
        mul_le_mul h2 (pow_le_pow_left₀ hJ.le (le_max_right _ _) _) (by positivity) (by positivity)
      _ = F^(2*n+1) := by rw [←mul_pow]
      _ ≤ _ := pow_le_pow_right₀ hF hnn
  have hnnJ : 0≤signedJacobianResolvent a d B ε τ θ := by unfold signedJacobianResolvent;positivity
  have hh := mul_le_mul (hj.trans (mul_le_mul_of_nonneg_right hJF hnnJ)) hs
    (norm_nonneg _) (by positivity)
  apply hh.trans_eq
  rw [mul_pow]
  ring

end
end IsingBulk.HT22.Near
