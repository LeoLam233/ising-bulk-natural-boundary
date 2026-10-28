import IsingBulk.HT22.Tail.ActualCollisionChart
import IsingBulk.HT22.Tail.ActualVandermondeScale
import IsingBulk.HT22.Tail.ActualPairQuotientJets
import IsingBulk.HT22.SeedFrameConversion.ActualSeed
import IsingBulk.HT22.Transport.FieldNeighborhood.UniformFrameBudget
import IsingBulk.HT22.Transport.FieldNeighborhood.UniformPairBudget
import IsingBulk.HT22.Tail.ShellScale

/-! Actual near-shell scalar bound. The cap in the returned source window
is explicit; it is not silently replaced by the original bump support. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Geometry Set
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def nearScalarCoefficient (k : ℕ) (RA Q RB RC RV D : ℝ) (N : ℕ) : ℝ :=
  (((2^k*(RA^N*(N:ℝ)^(k*k+6*k))*(2^k*((2^k*(2^k*Q*Q))^N))^N)/
      ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))‖)*D^k)*
    (D^2+2^k*(2*(N:ℝ)*(RB*(N:ℝ)^(2*(k+1)+2))+
      2*(N:ℝ)^2*(RC*(N:ℝ)^(2*k+2))))^k*RV^(N*(N-1))

theorem actual_near_scalar (d : PreferredBranchData) (M : ℝ) (hM : 0<M) :
    ∃ cap₀ : ℝ, 0<cap₀ ∧ cap₀<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap₀ →
      ∃ cap ε₀ τ₀ δB D : ℝ, 0<cap ∧ cap<d.alpha ∧ 0<ε₀ ∧ 0<τ₀ ∧
        0<δB ∧ δB<B.delta ∧ 1≤D ∧
      ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
      ∀ k : ℕ, ∃ RA Q RB RC RV : ℝ, 1≤RA ∧ 1≤Q ∧ 0<RB ∧ 0<RC ∧ 0<RV ∧
      ∀ n : ℕ, ∀ ε τ μ r : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → |μ|+r+ε≤M →
      ∀ θ : Fin (2*n+1) → ℝ,
      (∀ i, -δB≤θ i+d.b ∧ θ i≤min cap B.delta) →
      (∀ i, μ-2*r≤θ i+d.b ∧ θ i+d.b≤μ+2*r) →
      ∀ i a : Fin (2*n+1), (∀ b, θ i≤θ b ∧ θ b≤θ a) → r≤θ a-θ i →
      ‖regularTransportedScalar τ preferredPopulationCutoff B.p B.m rcut k
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
      nearScalarCoefficient k RA Q RB RC RV D (2*n+1)*
        (r/Real.sqrt (|μ|+r+ε))^((2*n+1)*(2*n))/(r/Real.sqrt (|μ|+r+ε))^(2*k) := by
  obtain ⟨cg,hcg,hcga,hG⟩ := actual_collision_source_chart d
  obtain ⟨ca,hca,hcaa,hA⟩ := SeedFrameConversion.actual_normalized_seed_frame_jets d
  obtain ⟨cq,hcq,hcqa,hQ⟩ := actual_pairQuotient_frame_jets d
  refine ⟨min cg (min ca cq),lt_min hcg (lt_min hca hcq),(min_le_left _ _).trans_lt hcga,?_⟩
  intro B hcap₀
  have hcaps : B.delta<cg ∧ B.delta<ca ∧ B.delta<cq := by simpa only [lt_min_iff] using hcap₀
  obtain ⟨c,δ,eg,tg,dg,hc,heg,htg,hdg,hdgB,hchart⟩ := hG B hcaps.1
  obtain ⟨ea,ta,da,hea,hta,hda,hdaB,hseed⟩ := hA B hcaps.2.1
  obtain ⟨eq,tq,dq,heq,htq,hdq,hdqB,hquot⟩ := hQ B hcaps.2.2
  obtain ⟨RV,ev,tv,dv,hRV,hev,htv,hdv,hdvB,hvand⟩ := actual_full_vandermonde_scale d B
  obtain ⟨cb,eb,tb,db,hcb,hcba,heb,htb,hdb,hdbB,hfield⟩ := actual_mixed_field_uniform_frame_budget d B M hM
  obtain ⟨cc,ec,tc,dc,hcc,hcca,hec,htc,hdc,hdcB,hslope⟩ := actual_pair_slope_uniform_frame_budget d B M hM
  let e := min eg (min ea (min eq (min ev (min eb ec))))
  let t := min tg (min ta (min tq (min tv (min tb tc))))
  let b := min dg (min da (min dq (min dv (min db dc))))
  let cap := min cb cc
  let D := 1+Real.sqrt M
  have hD : 1≤D := by dsimp [D]; linarith [Real.sqrt_nonneg M]
  refine ⟨cap,e,t,b,D,lt_min hcb hcc,(min_le_left _ _).trans_lt hcba,
    lt_min heg (lt_min hea (lt_min heq (lt_min hev (lt_min heb hec)))),
    lt_min htg (lt_min hta (lt_min htq (lt_min htv (lt_min htb htc)))),
    lt_min hdg (lt_min hda (lt_min hdq (lt_min hdv (lt_min hdb hdc)))),
    (min_le_left _ _).trans_lt hdgB,hD,?_⟩
  intro rcut hrcut hperiod k
  obtain ⟨RA,hRA,hAj⟩ := hseed rcut hrcut hperiod k
  obtain ⟨Q,hQp,hQj⟩ := hquot k
  obtain ⟨RB,hRB,hBj⟩ := hfield (k+1)
  obtain ⟨RC,hRC,hCj⟩ := hslope k
  refine ⟨RA,max 1 Q,RB,RC,RV,hRA,le_max_left _ _,hRB,hRC,hRV,?_⟩
  intro n ε τ μ r hε hεr hτ hτr hr hTM θ hθ hwin i a hext hgap
  let N := 2*n+1
  have hN : 0<N := by dsimp [N]; omega
  have hes : ε<eg ∧ ε<ea ∧ ε<eq ∧ ε<ev ∧ ε<eb ∧ ε<ec := by simpa only [e,lt_min_iff] using hεr
  have hts : τ<tg ∧ τ<ta ∧ τ<tq ∧ τ<tv ∧ τ<tb ∧ τ<tc := by simpa only [t,lt_min_iff] using hτr
  have hds : b≤dg ∧ b≤da ∧ b≤dq ∧ b≤dv ∧ b≤db ∧ b≤dc := by
    simpa only [b,le_min_iff] using (le_rfl : b≤b)
  have hbox {b' : ℝ} (hb' : b≤b') (u : Fin N) :
      -b'≤θ u+d.b ∧ θ u+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg hb').trans (hθ u).1,by linarith [(hθ u).2.trans (min_le_right _ _)]⟩
  have hboxfield (u : Fin N) : -db≤θ u+d.b ∧ θ u≤min cb B.delta :=
    ⟨(neg_le_neg hds.2.2.2.2.1).trans (hθ u).1,
      (hθ u).2.trans (min_le_min (min_le_left _ _) le_rfl)⟩
  have hboxslope (u : Fin N) : -dc≤θ u+d.b ∧ θ u≤min cc B.delta :=
    ⟨(neg_le_neg hds.2.2.2.2.2).trans (hθ u).1,
      (hθ u).2.trans (min_le_min (min_le_right _ _) le_rfl)⟩
  obtain ⟨Ω,hΩ,hz,hpoint,hR,hgood⟩ := hchart N hN ε τ μ r hε hes.1 hτ hts.1 hr θ (hbox hds.1) hwin i a hext hgap
  let Δ := r/Real.sqrt (|μ|+r+ε)
  have hΔ : 0<Δ := by dsimp [Δ]; positivity
  have hΔD : Δ≤D := by
    have hh := shellCoordinateScale_le_sqrt μ hr hε.le
    have hh' := Real.sqrt_le_sqrt hTM
    change Δ≤Real.sqrt (|μ|+r+ε) at hh
    dsimp [D]
    linarith
  have hCm := sourcePairSlope_mixed τ δ B.p B.m B.smooth B.m_smooth Ω hpoint hR
  have hAj' (xs : List (Option (Fin N))) (hxs : xs.length≤k) :
      ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*frameJet τ B.p B.m
        (preferredRegularSeedCoefficient τ preferredPopulationCutoff B.p B.m rcut) xs
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤RA^N*(N:ℝ)^(k*k+6*k) := by
    have hh := hAj N hN ε τ hε hes.2.1 hτ hts.2.1 θ (hbox hds.2.1) xs hxs
    have he : regularSeedCoefficient τ preferredPopulationCutoff B.p B.m rcut (N:=N)=
        preferredRegularSeedCoefficient τ preferredPopulationCutoff B.p B.m rcut := by
      funext t x
      exact regularSeedCoefficient_eq_shared _ _ _ _ _ _ _
    rw [he] at hh
    exact hh
  have hQj' (u v : Fin N) (xs : List (Option (Fin N))) (hxs : xs.length≤k) :
      ‖frameJet τ B.p B.m (fun t x => preferredSourceKernelQuotient τ B.p B.m t x u v) xs
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤max 1 Q :=
    (hQj N hN ε τ hε hes.2.2.1 hτ hts.2.2.1 θ (hbox hds.2.2.1) xs hxs u v).trans (le_max_right _ _)
  have hs := odd_source_vandermonde_bound n τ δ c preferredPopulationCutoff B.p B.m rcut
    preferredPopulationCutoff_smooth B.smooth B.m_smooth hrcut Ω hΩ hpoint hR hCm hgood
    (IsingBulk.Branch.radialParameter d.alpha ε) θ hz k (RA^N*(N:ℝ)^(k*k+6*k)) (max 1 Q)
    (RB*(N:ℝ)^(2*(k+1)+2)) (RC*(N:ℝ)^(2*k+2)) Δ D (by positivity) (le_max_left _ _)
    (by positivity) (by positivity) hΔ hΔD hD
    (by simpa only [N,Nat.add_sub_cancel] using hAj') hQj'
    (fun u xs hxs => hBj N hN ε τ μ r hε hes.2.2.2.2.1 hτ hts.2.2.2.2.1 hr hTM
      θ hboxfield hwin i a hext hgap xs hxs u)
    (fun u v xs hxs => hCj N hN ε τ μ r hε hes.2.2.2.2.2 hτ hts.2.2.2.2.2 hr hTM
      θ hboxslope hwin i a hext hgap xs hxs u v)
  have hv := hvand N hN ε τ μ r hε hes.2.2.2.1 hτ hts.2.2.2.1 hr θ (hbox hds.2.2.2.1) hwin
  apply hs.trans
  calc
    _ ≤ _*(RV*Δ)^(N*(N-1)) := mul_le_mul_of_nonneg_left hv (by positivity)
    _ = _ := by simp only [nearScalarCoefficient,N,Nat.add_sub_cancel,mul_pow]; ring

end
end IsingBulk.HT22.Tail
