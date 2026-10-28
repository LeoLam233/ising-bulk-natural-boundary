import IsingBulk.HT22.Transport.SharpCovarianceJets.ActualInputs
import IsingBulk.HT22.Geometry.CovarianceShell

namespace IsingBulk.HT22.SharpCovarianceJets
noncomputable section
open Set Metric Geometry IsingBulk.Preferred22
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem actual_sharp_scale_jets_uniform_cap (b : PreferredBranchData)
    (M : ℝ) (hM : 0<M) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b,
    ∃ C ε₀ τ₀ δB η c K : ℝ,
      0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      0<η ∧ 0<c ∧ 1≤K ∧
      ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → |μ|+r+ε≤M →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+b.b ∧ θ i≤min cap B.delta) →
      (∀ i, μ-2*r≤θ i+b.b ∧ θ i+b.b≤μ+2*r) →
      ∀ i j : Fin N, (∀ a, θ i≤θ a ∧ θ a≤θ j) → r≤θ j-θ i →
      sourceCovariance (IsingBulk.Branch.radialParameter b.alpha ε)
        (Tail.sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ) ≠ 0 ∧
      ∀ m : ℕ, SharpBounds
        (IsingBulk.Branch.radialParameter b.alpha ε,
          Tail.sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ)
        C (K*Real.sqrt (|μ|+r+ε)) (K*r/Real.sqrt (|μ|+r+ε)) c η m := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_sharp_joint_jets_uniform_cap b
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B
  obtain ⟨C,r₀,δ₀,κ,hC,hr₀,hδ₀,hδ₀B,hκ,hjets⟩ :=
    hsource B
  obtain ⟨cR,eR,tR,δR,hcR,heR,htR,hδR,hδRB,hcov⟩ := actual_mixed_covariance_shell b B
  obtain ⟨D,eD,tD,δD,hD,heD,htD,hδD,hδDB,hdiam⟩ := preferred_actual_coordinate_difference b B
  let K := max 1 D
  have hK1 : 1≤K := le_max_left _ _
  have hK : 0<K := zero_lt_one.trans_le hK1
  let c := cR/K^3
  have hc : 0<c := by dsimp [c]; positivity
  let L := K*Real.sqrt M
  have hL : 0<L := by dsimp [L]; positivity
  let η := min 1 (min (κ/L) (min (r₀/L) (c/(4*(18*C)^2))))
  have hη : 0<η := lt_min zero_lt_one (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hη1 : η≤1 := min_le_left _ _
  have hηκ : η≤κ/L := (min_le_right _ _).trans (min_le_left _ _)
  have hηr : η≤r₀/L := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηc : η≤c/(4*(18*C)^2) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let ε₀ := min r₀ (min eR eD)
  let τ₀ := min r₀ (min tR tD)
  let δB := min δ₀ (min δR δD)
  have hδB : 0<δB := lt_min hδ₀ (lt_min hδR hδD)
  refine ⟨C,ε₀,τ₀,δB,η,c,K,hC,lt_min hr₀ (lt_min heR heD),
    lt_min hr₀ (lt_min htR htD),hδB,(min_le_left _ _).trans_lt hδ₀B,hη,hc,hK1,?_⟩
  intro N hN ε τ μ r hε hε₀ hτ hτ₀ hr hTM θ hθ hwindow i j hext hgap
  let T := |μ|+r+ε
  let H := K*Real.sqrt T
  let d := K*r/Real.sqrt T
  have hT : 0<T := by dsimp [T]; positivity
  have hs : 0<Real.sqrt T := Real.sqrt_pos.mpr hT
  have hH : 0<H := by dsimp [H]; positivity
  have hd : 0<d := by dsimp [d]; positivity
  have hrT : r≤T := by dsimp [T]; linarith [abs_nonneg μ]
  have hdH : d≤H := by
    apply (div_le_iff₀ hs).mpr
    dsimp only [H]
    nlinarith [Real.sq_sqrt hT.le,mul_le_mul_of_nonneg_left hrT hK.le]
  have hscale : Real.sqrt T≤H := le_mul_of_one_le_left hs.le hK1
  have hdL : d≤L := hdH.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hTM) hK.le)
  have hηdκ : η*d≤κ :=
    (mul_le_mul_of_nonneg_left hdL hη.le).trans ((le_div_iff₀ hL).mp hηκ)
  have hηdr : η*d≤r₀ :=
    (mul_le_mul_of_nonneg_left hdL hη.le).trans ((le_div_iff₀ hL).mp hηr)
  have hεbase : ε<r₀ := hε₀.trans_le (min_le_left _ _)
  have hτbase : τ<r₀ := hτ₀.trans_le (min_le_left _ _)
  have hεR : ε<eR := hε₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hτR : τ<tR := hτ₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεD : ε<eD := hε₀.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hτD : τ<tD := hτ₀.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hθbase (a : Fin N) : -δ₀≤θ a+b.b ∧ θ a≤min cap B.delta := by
    have hδ : δB≤δ₀ := min_le_left _ _
    exact ⟨by linarith [(hθ a).1],(hθ a).2⟩
  have hθR (a : Fin N) : θ a∈Icc (-b.b-δR) B.delta := by
    have hδ : δB≤δR := (min_le_right _ _).trans (min_le_left _ _)
    exact ⟨by linarith [(hθ a).1],(hθ a).2.trans (min_le_right _ _)⟩
  have hθD (a : Fin N) : -δD≤θ a+b.b ∧ θ a+b.b≤b.b+B.delta := by
    have hδ : δB≤δD := (min_le_right _ _).trans (min_le_right _ _)
    have hhi := (hθ a).2.trans (min_le_right _ _)
    constructor <;> linarith [(hθ a).1]
  let t := IsingBulk.Branch.radialParameter b.alpha ε
  let v := Tail.sourceCoordinate τ B.p B.m t θ
  have hdiam' (a b' : Fin N) : ‖v a-v b'‖≤d := by
    have hh := hdiam N hN ε τ μ r hε hεD hτ hτD hr θ hθD hwindow a b'
    have he : v a-v b' = preferredSourceCoordinate τ B.p B.m t θ a-
        preferredSourceCoordinate τ B.p B.m t θ b' := by
      have ha := Tail.sourceCoordinate_moving_adapter τ B.p B.m t θ a
      have hb := Tail.sourceCoordinate_moving_adapter τ B.p B.m t θ b'
      dsimp only [v]
      linear_combination ha-hb
    rw [he]
    exact hh.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 D) hr.le) hs.le)
  have hR := (hcov N hN ε τ μ r hε hεR hτ hτR hr θ hθR hwindow i j hext hgap).2.1
  have hcov' : c*H*d^2≤‖sourceCovariance t v‖ := by
    have he : c*H*d^2=cR*r^2/Real.sqrt T := by
      dsimp only [c,H,d]
      field_simp
    rw [he]
    exact hR
  have hne : sourceCovariance t v≠0 := by
    intro he
    rw [he,norm_zero] at hcov'
    have hp : 0<c*H*d^2 := by positivity
    linarith
  refine ⟨hne,?_⟩
  intro m
  exact hjets N hN ε τ μ r H d c η hε hεbase hτ hτbase hr hH hd hc hdH hscale
    hη hη1 hηdκ hηdr hηc θ hθbase hwindow hdiam' hcov' m

end
end IsingBulk.HT22.SharpCovarianceJets
