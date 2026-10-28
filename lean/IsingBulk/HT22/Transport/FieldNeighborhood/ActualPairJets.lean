import IsingBulk.HT22.Transport.FieldNeighborhood.SourceUniformDomain
import IsingBulk.HT22.Transport.FieldNeighborhood.ActualInverseVScale
import IsingBulk.HT22.Transport.FieldNeighborhood.PairSlopeJets

/-! Actual-contour mixed field jets. Only the remaining quantitative
covariance/diameter inputs are exposed; all inverse analytic neighborhoods
and partial jet bounds are proved from the physical source. -/
namespace IsingBulk.HT22
noncomputable section
open Set Metric Geometry IsingBulk.Preferred22
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem actual_residualPairSlope_joint_jets (b : PreferredBranchData)
    (B : PreferredCoareaBump b) :
    ∃ cap C r₀ δB κ : ℝ, 0<cap ∧ cap<b.alpha ∧ 0<C ∧ 0<r₀ ∧
      0<δB ∧ δB<B.delta ∧ 0<κ ∧ ∀ N : ℕ, 0<N → ∀ ε τ μ r H d c η : ℝ,
      0<ε → ε<r₀ → 0≤τ → τ<r₀ → 0<r →
      0<H → 0<d → 0<c → d≤H → Real.sqrt (|μ|+r+ε)≤H →
      0<η → η≤1 → η*d≤κ → η*d≤r₀ → η≤c/(4*(18*C)^2) →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+b.b ∧ θ i≤min cap B.delta) →
      (∀ i, μ-2*r≤θ i+b.b ∧ θ i+b.b≤μ+2*r) →
      (∀ i j, ‖Tail.sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ i-
        Tail.sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ j‖≤d) →
      c*H*d^2≤‖sourceCovariance (IsingBulk.Branch.radialParameter b.alpha ε)
        (Tail.sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ)‖ →
      ∀ a₁ a₂ : Fin N, ∀ m : ℕ,
      ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => Tail.residualPairSlope z.1 z.2 a₁ a₂)
        (IsingBulk.Branch.radialParameter b.alpha ε,
          Tail.sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ)‖≤
        (cauchyJetConstant m*(10*C^2/c)/η^m)*(N:ℝ)^(2*m+2)/d^(m+2) := by
  obtain ⟨cap₁,R,κ,A,D,hcap₁,hcap₁a,hR,hκ,hA,hD,hdata,hinside⟩ :=
    actual_inverse_uniform_domain b B
  obtain ⟨cap₂,K,ε₂,τ₂,δ₂,hcap₂,hcap₂a,hK,hε₂,hτ₂,hδ₂,hδ₂B,hscale⟩ :=
    actual_inverseV_square_root_scale b B
  let cap := min cap₁ cap₂
  let C := max A K
  let r₀ := min (R/2) (min ε₂ τ₂)
  let δB := min δ₂ (R/2)
  have hC : 0<C := hA.trans_le (le_max_left _ _)
  have hr₀ : 0<r₀ := lt_min (by positivity) (lt_min hε₂ hτ₂)
  have hrR : r₀≤R/2 := min_le_left _ _
  have hdR : δB≤R/2 := min_le_right _ _
  refine ⟨cap,C,r₀,δB,κ,lt_min hcap₁ hcap₂,(min_le_left _ _).trans_lt hcap₁a,
    hC,hr₀,lt_min hδ₂ (by positivity),(min_le_left _ _).trans_lt hδ₂B,hκ,?_⟩
  intro N hN ε τ μ r H d c η hε hε₀ hτ hτ₀ hr hH hd hc hdH hscaleH
    hη hη1 hηκ hηr hηc θ hθ hwindow hdiam hcov a₁ a₂ m
  let t := IsingBulk.Branch.radialParameter b.alpha ε
  let v := Tail.sourceCoordinate τ B.p B.m t θ
  let x : SourcePoint N := (t,v)
  let radius := η*d/(N:ℝ)^2
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hradius : radius≤η*d := div_le_self (by positivity) (one_le_pow₀ hn)
  have heR : |ε|<R := by rw [abs_of_pos hε]; linarith
  have htR : |τ|<R := by rw [abs_of_nonneg hτ]; linarith
  have hθR (i : Fin N) : -b.b-R≤θ i ∧ θ i≤cap₁ := by
    have hh := hθ i
    constructor
    · linarith [hh.1]
    · exact (hh.2.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hi (i : Fin N) : closedBall (v i) radius ⊆ D :=
    (closedBall_subset_closedBall (hradius.trans hηκ)).trans
      (hinside N hN ε τ heR htR θ hθR i)
  have htime (s : ℂ) (hs : ‖s-t‖≤radius) : ‖s-preferredSelectedPoint b‖≤R := by
    have he : ‖t-preferredSelectedPoint b‖=ε := by rw [preferred_radial_distance,abs_of_pos hε]
    have hh := norm_add_le (s-t) (t-preferredSelectedPoint b)
    rw [sub_add_sub_cancel] at hh
    linarith
  have hdata' (s q : ℂ) (hs : ‖s-t‖≤radius) (hq : q∈D) := hdata s q (htime s hs) hq
  have hV (i : Fin N) : ‖sourceInverseV t (v i)‖≤C*H := by
    have he₂ : ε<ε₂ := hε₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have ht₂ : τ<τ₂ := hτ₀.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hθ₂ (i : Fin N) : -δ₂≤θ i+b.b ∧ θ i≤min cap₂ B.delta := by
      have hh := hθ i
      constructor
      · have hδ : δB≤δ₂ := min_le_left _ _; linarith [hh.1]
      · exact le_min ((hh.2.trans (min_le_left _ _)).trans (min_le_right _ _))
          (hh.2.trans (min_le_right _ _))
    have hv := hscale N hN ε τ μ r hε he₂ hτ ht₂ hr θ hθ₂ hwindow i
    exact hv.trans (mul_le_mul (le_max_right A K) hscaleH (Real.sqrt_nonneg _) hC.le)
  exact residualPairSlope_jets_of_base_inverse_geometry hN x D C H d c η hC hH hd hc hdH
    hη hη1 hηc hD hi
    (fun s q hs hq => (hdata' s q hs hq).1)
    (fun s q hs hq => (hdata' s q hs hq).2.2.1.trans (le_max_left _ _))
    (fun s q hs hq => (hdata' s q hs hq).2.2.2.trans (le_max_left _ _))
    (fun s q hs hq => (hdata' s q hs hq).2.1.trans (le_max_left _ _)) hV hdiam hcov a₁ a₂ m

theorem actual_residualPairSlope_joint_jets_uniform_cap (b : PreferredBranchData)
    :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b,
    ∃ C r₀ δB κ : ℝ, 0<C ∧ 0<r₀ ∧
      0<δB ∧ δB<B.delta ∧ 0<κ ∧ ∀ N : ℕ, 0<N → ∀ ε τ μ r H d c η : ℝ,
      0<ε → ε<r₀ → 0≤τ → τ<r₀ → 0<r →
      0<H → 0<d → 0<c → d≤H → Real.sqrt (|μ|+r+ε)≤H →
      0<η → η≤1 → η*d≤κ → η*d≤r₀ → η≤c/(4*(18*C)^2) →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+b.b ∧ θ i≤min cap B.delta) →
      (∀ i, μ-2*r≤θ i+b.b ∧ θ i+b.b≤μ+2*r) →
      (∀ i j, ‖Tail.sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ i-
        Tail.sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ j‖≤d) →
      c*H*d^2≤‖sourceCovariance (IsingBulk.Branch.radialParameter b.alpha ε)
        (Tail.sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ)‖ →
      ∀ a₁ a₂ : Fin N, ∀ m : ℕ,
      ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => Tail.residualPairSlope z.1 z.2 a₁ a₂)
        (IsingBulk.Branch.radialParameter b.alpha ε,
          Tail.sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ)‖≤
        (cauchyJetConstant m*(10*C^2/c)/η^m)*(N:ℝ)^(2*m+2)/d^(m+2) := by
  obtain ⟨cap₁,hcap₁,hcap₁a,hdomain⟩ := actual_inverse_uniform_domain_uniform_cap b
  obtain ⟨cap₂,hcap₂,hcap₂a,hscale0⟩ := actual_inverseV_square_root_scale_uniform_cap b
  let cap := min cap₁ cap₂
  refine ⟨cap,lt_min hcap₁ hcap₂,(min_le_left _ _).trans_lt hcap₁a,?_⟩
  intro B
  obtain ⟨R,κ,A,D,hR,hκ,hA,hD,hdata,hinside⟩ := hdomain B
  obtain ⟨K,ε₂,τ₂,δ₂,hK,hε₂,hτ₂,hδ₂,hδ₂B,hscale⟩ := hscale0 B
  let C := max A K
  let r₀ := min (R/2) (min ε₂ τ₂)
  let δB := min δ₂ (R/2)
  have hC : 0<C := hA.trans_le (le_max_left _ _)
  have hr₀ : 0<r₀ := lt_min (by positivity) (lt_min hε₂ hτ₂)
  have hrR : r₀≤R/2 := min_le_left _ _
  have hdR : δB≤R/2 := min_le_right _ _
  refine ⟨C,r₀,δB,κ,hC,hr₀,lt_min hδ₂ (by positivity),(min_le_left _ _).trans_lt hδ₂B,hκ,?_⟩
  intro N hN ε τ μ r H d c η hε hε₀ hτ hτ₀ hr hH hd hc hdH hscaleH
    hη hη1 hηκ hηr hηc θ hθ hwindow hdiam hcov a₁ a₂ m
  let t := IsingBulk.Branch.radialParameter b.alpha ε
  let v := Tail.sourceCoordinate τ B.p B.m t θ
  let x : SourcePoint N := (t,v)
  let radius := η*d/(N:ℝ)^2
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hradius : radius≤η*d := div_le_self (by positivity) (one_le_pow₀ hn)
  have heR : |ε|<R := by rw [abs_of_pos hε]; linarith
  have htR : |τ|<R := by rw [abs_of_nonneg hτ]; linarith
  have hθR (i : Fin N) : -b.b-R≤θ i ∧ θ i≤cap₁ := by
    have hh := hθ i
    constructor
    · linarith [hh.1]
    · exact (hh.2.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hi (i : Fin N) : closedBall (v i) radius ⊆ D :=
    (closedBall_subset_closedBall (hradius.trans hηκ)).trans
      (hinside N hN ε τ heR htR θ hθR i)
  have htime (s : ℂ) (hs : ‖s-t‖≤radius) : ‖s-preferredSelectedPoint b‖≤R := by
    have he : ‖t-preferredSelectedPoint b‖=ε := by rw [preferred_radial_distance,abs_of_pos hε]
    have hh := norm_add_le (s-t) (t-preferredSelectedPoint b)
    rw [sub_add_sub_cancel] at hh
    linarith
  have hdata' (s q : ℂ) (hs : ‖s-t‖≤radius) (hq : q∈D) := hdata s q (htime s hs) hq
  have hV (i : Fin N) : ‖sourceInverseV t (v i)‖≤C*H := by
    have he₂ : ε<ε₂ := hε₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have ht₂ : τ<τ₂ := hτ₀.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hθ₂ (i : Fin N) : -δ₂≤θ i+b.b ∧ θ i≤min cap₂ B.delta := by
      have hh := hθ i
      constructor
      · have hδ : δB≤δ₂ := min_le_left _ _; linarith [hh.1]
      · exact le_min ((hh.2.trans (min_le_left _ _)).trans (min_le_right _ _))
          (hh.2.trans (min_le_right _ _))
    have hv := hscale N hN ε τ μ r hε he₂ hτ ht₂ hr θ hθ₂ hwindow i
    exact hv.trans (mul_le_mul (le_max_right A K) hscaleH (Real.sqrt_nonneg _) hC.le)
  exact residualPairSlope_jets_of_base_inverse_geometry hN x D C H d c η hC hH hd hc hdH
    hη hη1 hηc hD hi
    (fun s q hs hq => (hdata' s q hs hq).1)
    (fun s q hs hq => (hdata' s q hs hq).2.2.1.trans (le_max_left _ _))
    (fun s q hs hq => (hdata' s q hs hq).2.2.2.trans (le_max_left _ _))
    (fun s q hs hq => (hdata' s q hs hq).2.1.trans (le_max_left _ _)) hV hdiam hcov a₁ a₂ m

end
end IsingBulk.HT22
