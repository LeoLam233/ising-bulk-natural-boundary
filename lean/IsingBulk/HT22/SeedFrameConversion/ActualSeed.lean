import IsingBulk.HT22.SeedFrameConversion.Bounds
import IsingBulk.HT22.Tail.SeedCalculus
import IsingBulk.Preferred22.ActualSeedFrames

/-! Actual original smooth seed jets in the F001 fixed-v frame. Constants
and parameter domains precede the derivative order; no descendant bound
or completed old transport endpoint is a premise. -/
namespace IsingBulk.HT22.SeedFrameConversion
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem conversion_growth (N j E : ℕ) (hN : 0<N) (A B : ℝ) (hA : 1≤A) (hB : 1≤B) :
    ((N:ℝ)+2)^j*(B*(A^N*(N:ℝ)^E)) ≤
      ((3:ℝ)^j*B*A)^N*(N:ℝ)^(E+j) := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hb : 1≤(3:ℝ)^j*B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hB
  calc
    _ ≤ ((3:ℝ)*N)^j*(B*(A^N*(N:ℝ)^E)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (by positivity)
    _ = ((3:ℝ)^j*B)*A^N*(N:ℝ)^(E+j) := by rw [mul_pow,pow_add]; ring
    _ ≤ ((3:ℝ)^j*B)^N*A^N*(N:ℝ)^(E+j) := by
      gcongr
      exact le_self_pow₀ hb (by omega)
    _ = _ := by simp only [mul_pow]

theorem actual_normalized_seed_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
        ∀ j : ℕ, ∃ A : ℝ, 1≤A ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        ∀ xs : List (Option (Fin N)), xs.length≤j →
        ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*frameJet τ B.p B.m
          (regularSeedCoefficient τ preferredPopulationCutoff B.p B.m rcut) xs
          (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤A^N*(N:ℝ)^(j*j+6*j) := by
  obtain ⟨cap,hcap,hcapa,hseed⟩ := preferred_actual_normalized_seed_frame_jets d
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
  obtain ⟨εS,τS,δS,hεS,hτS,hδS,hδSB,hS⟩ := hseed B hBcap
  obtain ⟨δ,εF,τF,hδ,_hδa,hεF,hτF,hframe⟩ := preferred_actual_frame_points d B
  refine ⟨min εS (min εF (rB/2)),min τS τF,δS,
    lt_min hεS (lt_min hεF (half_pos hrB)),lt_min hτS hτF,hδS,hδSB,?_⟩
  intro rcut hrcut hrper j
  obtain ⟨A,hA,hAb⟩ := hS rcut hrcut hrper j
  obtain ⟨C,hC,hCb⟩ := coefficients_compact_bound K hK hKa j
  refine ⟨(3:ℝ)^j*C*A,
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hC) hA,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ xs hxs
  have heS := hεr.trans_le (min_le_left _ _)
  have heF := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heK := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have htS := hτr.trans_le (min_le_left _ _)
  have htF := hτr.trans_le (min_le_right _ _)
  obtain ⟨hpoint,hθstrict⟩ := hframe δS hδS hδSB N hN ε τ hε heF hτ htF θ hθ
  let t := IsingBulk.Branch.radialParameter d.alpha ε
  have htK : t∈K := by
    change dist t (preferredSelectedPoint d)≤rB/2
    rw [dist_eq_norm,preferred_radial_distance,abs_of_pos hε]
    exact heK.le
  have he := preferredFramePoint_eventually τ δ B.p B.m B.smooth B.m_smooth t θ hpoint hθstrict
  obtain ⟨Ω,hsub,hΩ,hz⟩ := mem_nhds_iff.mp he
  have hpoints : ∀ z∈Ω, PreferredFramePoint τ δ B.p B.m z.1 z.2 := fun z hz => hsub hz
  have hmix := regularSeedCoefficient_mixed τ δ preferredPopulationCutoff B.p B.m rcut
    preferredPopulationCutoff_smooth B.smooth B.m_smooth hrcut Ω hpoints
  have hold (ys : List (Option (Fin N))) (hys : ys.length≤j) :
      ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*preferredFrameJet τ B.p B.m
        (regularSeedCoefficient τ preferredPopulationCutoff B.p B.m rcut) ys t θ‖≤
      A^N*(N:ℝ)^(j*j+5*j) := by
    have heq : regularSeedCoefficient (N:=N) τ preferredPopulationCutoff B.p B.m rcut =
        preferredRegularSeedCoefficient τ preferredPopulationCutoff B.p B.m rcut := by
      funext s x
      exact regularSeedCoefficient_eq_shared ..
    rw [heq]
    exact hAb N hN ε τ hε heS hτ htS θ hθ ys hys
  have hbound := frameJet_bound_of_shared τ δ B.p B.m B.smooth B.m_smooth Ω hΩ hpoints _ hmix
    j C (A^N*(N:ℝ)^(j*j+5*j)) (by linarith) (by positivity)
    ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1)) t θ hz
    (fun cs hcs => hCb cs hcs t htK) hold xs hxs
  have hgrowth := conversion_growth N j (j*j+5*j) hN A C hA hC
  convert hbound.trans hgrowth using 1
  congr 2
  omega

end
end IsingBulk.HT22.SeedFrameConversion
