import IsingBulk.HT22.Transport.FieldNeighborhood.InverseVScale
import IsingBulk.HT22.Tail.SeedCalculus

/-! The actual all-particle square-root inverse slope bound. -/
namespace IsingBulk.HT22
noncomputable section
open Set Metric Geometry IsingBulk.Preferred22
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem actual_inverseV_square_root_scale_uniform_cap (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,
    ∃ C ε₀ τ₀ δB : ℝ, 0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧
      0<δB ∧ δB<B.delta ∧ ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+d.b ∧ θ i≤min cap B.delta) →
      (∀ i, μ-2*r≤θ i+d.b ∧ θ i+d.b≤μ+2*r) → ∀ i,
      ‖sourceInverseV (IsingBulk.Branch.radialParameter d.alpha ε)
        (Tail.sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i)‖≤
        C*Real.sqrt (|μ|+r+ε) := by
  obtain ⟨cap,ρ,c,D,hcap,hcapa,hρ,_hc,hD,hconv,hzero,hgood,himage⟩ :=
    preferred_uniform_regular_source_domain d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B
  have hz : (0:ℂ)∈D := interior_subset hzero
  have hu : ∀ t q : ℂ, ‖t-preferredSelectedPoint d‖<ρ → q∈D →
      AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (t,q) := by
    intro t q ht hq
    exact (hgood t q 0 ht hq hz).2.1
  obtain ⟨R,hR,hRρ,hjets⟩ := preferred_global_parameter_q_bound d ρ D hρ hD hconv hz hu
  obtain ⟨A,hA,hAq⟩ := hjets 0
  obtain ⟨r₀,hr₀,himage⟩ := himage B.p B.m B.smooth.continuous
    (B.smooth.continuous.comp continuous_neg)
  obtain ⟨K,εk,τk,δk,hK,hεk,hτk,hδk,hδkB,hscale⟩ :=
    preferred_actual_coordinate_absolute_scale d B
  let ε₀ := min εk (min r₀ R)
  let τ₀ := min τk r₀
  let δB := min δk (r₀/2)
  refine ⟨A*K,ε₀,τ₀,δB,by positivity,
    lt_min hεk (lt_min hr₀ hR),lt_min hτk hr₀,
    lt_min hδk (by positivity),(min_le_left _ _).trans_lt hδkB,?_⟩
  intro N hN ε τ μ r hε hε₀ hτ hτ₀ hr θ hθ hwindow i
  have hεk' : ε<εk := hε₀.trans_le (min_le_left _ _)
  have hεr : ε<r₀ := hε₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεR : ε<R := hε₀.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hτk' : τ<τk := hτ₀.trans_le (min_le_left _ _)
  have hτr : τ<r₀ := hτ₀.trans_le (min_le_right _ _)
  have hθk (i : Fin N) : -δk≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta := by
    have hh := hθ i
    have hδ : δB≤δk := min_le_left _ _
    have hhi := hh.2.trans (min_le_right _ _)
    constructor <;> linarith [hh.1]
  let t := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m t θ i
  have htR : ‖t-preferredSelectedPoint d‖≤R := by
    rw [preferred_radial_distance,abs_of_pos hε]
    exact hεR.le
  have hq : q∈D := by
    have hmeans := actual_occupancy_box hN B θ
    have hh := himage ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
      (by simpa only [abs_of_pos hε] using hεr)
      (by simpa only [abs_of_nonneg hτ] using hτr) hmeans.1 hmeans.2
      (by have hδ : δB≤r₀/2 := min_le_right _ _; linarith [(hθ i).1])
      ((hθ i).2.trans (min_le_left _ _))
    exact interior_subset (by simpa only [preferredBumpCoordinate_actual] using hh)
  have hqa := hAq t q htR hq
  have hj := preferredParameterQJet_eq_iteratedDeriv 0 t q
    (hu t q (by linarith) hq)
  rw [hj,iteratedDeriv_zero] at hqa
  have hv : sourceInverseV t (Tail.sourceCoordinate τ B.p B.m t θ i)=
      deriv (preferredMovingInverse t) q := by
    change Tail.inverseV t (Tail.sourceCoordinate τ B.p B.m t θ i)=_
    rw [Tail.inverseV_moving_adapter,Tail.sourceCoordinate_moving_adapter]
    rfl
  rw [hv]
  have hs := hscale N hN ε τ μ r hε hεk' hτ hτk' hr θ hθk hwindow i
  exact hqa.trans (by nlinarith [mul_le_mul_of_nonneg_left hs hA.le])

theorem actual_inverseV_square_root_scale (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ cap C ε₀ τ₀ δB : ℝ, 0<cap ∧ cap<d.alpha ∧ 0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧
      0<δB ∧ δB<B.delta ∧ ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+d.b ∧ θ i≤min cap B.delta) →
      (∀ i, μ-2*r≤θ i+d.b ∧ θ i+d.b≤μ+2*r) → ∀ i,
      ‖sourceInverseV (IsingBulk.Branch.radialParameter d.alpha ε)
        (Tail.sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i)‖≤
        C*Real.sqrt (|μ|+r+ε) := by
  obtain ⟨cap,hcap,hcapa,hall⟩ := actual_inverseV_square_root_scale_uniform_cap d
  obtain ⟨C,ε₀,τ₀,δB,hrest⟩ := hall B
  exact ⟨cap,C,ε₀,τ₀,δB,hcap,hcapa,hrest⟩

end
end IsingBulk.HT22
