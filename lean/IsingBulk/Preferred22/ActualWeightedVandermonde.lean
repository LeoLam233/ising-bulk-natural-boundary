import IsingBulk.Preferred22.VandermondeGeometry
import IsingBulk.Preferred22.WeightedSourceVandermonde
import IsingBulk.Preferred22.SmoothMultiplierFrames
import IsingBulk.Preferred22.ActualSeedFrames
import IsingBulk.Preferred22.SourceKernelQuotient
import IsingBulk.Preferred22.CollectiveFrameJets

/-! The complete finite-particle collision degree for the literal regular
transport descendants. All analytic and quantitative hypotheses are
discharged from original source data. Constants may depend on the fixed
finite particle order; no natural subtraction truncates the loss. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem preferred_actual_weighted_vandermonde_bound (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δ₀ : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δ₀ ∧ δ₀<B.delta ∧
        ∀ δB : ℝ, 0<δB → δB≤δ₀ →
        ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
        ∀ j n : ℕ, 0<n → ∀ ψ : (Fin (2*n) → ℝ) → ℂ,ContDiff ℝ ∞ ψ →
        ∃ C : ℝ, 0<C ∧
        ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin (2*n) → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        0<preferredAngularDiameter θ →
        ‖preferredWeightedRegularScalar ψ τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
          C/preferredAngularDiameter θ^(2*j)*
            ‖preferredSquaredVandermonde (preferredSourceCoordinate τ B.p B.m
              (IsingBulk.Branch.radialParameter d.alpha ε) θ)‖ := by
  obtain ⟨capG,hcapG,hcapGa,hG⟩ := preferred_actual_vandermonde_geometry d
  obtain ⟨capA,hcapA,hcapAa,hA⟩ := preferred_actual_normalized_seed_frame_jets d
  obtain ⟨capQ,hcapQ,hcapQa,hQ⟩ := preferred_actual_kernel_quotient_frame_jets d
  obtain ⟨capB,hcapB,hcapBa,hB⟩ := preferred_actual_collective_frame_jets d
  obtain ⟨capC,hcapC,hcapCa,hC⟩ := preferred_actual_collective_difference_frame_jets d
  obtain ⟨capF,hcapF,_hcapFa,hF⟩ := preferred_actual_smooth_angular_frame_jets d
  refine ⟨min (min capG (min capA (min capQ (min capB capC)))) capF,
    lt_min (lt_min hcapG (lt_min hcapA (lt_min hcapQ (lt_min hcapB hcapC)))) hcapF,
    ((min_le_left _ _).trans (min_le_left _ _)).trans_lt hcapGa,?_⟩
  intro B hBcap
  have hcaps : B.delta<capG ∧ B.delta<capA ∧ B.delta<capQ ∧ B.delta<capB ∧ B.delta<capC := by
    simpa only [lt_min_iff] using (hBcap.trans_le (min_le_left _ _))
  obtain ⟨c,δ,εG,τG,δG,hc,hεG,hτG,hδG,hδGB,hgeom⟩ := hG B hcaps.1
  obtain ⟨εA,τA,δA,hεA,hτA,hδA,hδAB,hseed⟩ := hA B hcaps.2.1
  obtain ⟨εQ,τQ,δQ,hεQ,hτQ,hδQ,hδQB,hquotient⟩ := hQ B hcaps.2.2.1
  obtain ⟨εB,τB,δB₁,hεB,hτB,hδB₁,hδB₁B,hcollective⟩ := hB B hcaps.2.2.2.1
  obtain ⟨εC,τC,δC,hεC,hτC,hδC,hδCB,hdifference⟩ := hC B hcaps.2.2.2.2
  obtain ⟨εF,τF,δF,hεF,hτF,hδF,_hδFB,hψframes⟩ := hF B (hBcap.trans_le (min_le_right _ _))
  let ε₀ := min (min εG (min εA (min εQ (min εB εC)))) εF
  let τ₀ := min (min τG (min τA (min τQ (min τB τC)))) τF
  let δ₀ := min (min δG (min δA (min δQ (min δB₁ δC)))) δF
  have hε₀ : 0<ε₀ := lt_min (lt_min hεG (lt_min hεA (lt_min hεQ (lt_min hεB hεC)))) hεF
  have hτ₀ : 0<τ₀ := lt_min (lt_min hτG (lt_min hτA (lt_min hτQ (lt_min hτB hτC)))) hτF
  have hδ₀ : 0<δ₀ := lt_min (lt_min hδG (lt_min hδA (lt_min hδQ (lt_min hδB₁ hδC)))) hδF
  have hδ₀B : δ₀<B.delta := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt hδGB
  refine ⟨ε₀,τ₀,δ₀,hε₀,hτ₀,hδ₀,hδ₀B,?_⟩
  intro δB hδB hδB₀ rcut hrcut hrcutp j n hn ψ hψ
  have hδs : δB≤δG ∧ δB≤δA ∧ δB≤δQ ∧ δB≤δB₁ ∧ δB≤δC := by
    simpa only [le_min_iff] using (hδB₀.trans (min_le_left _ _))
  obtain ⟨CA,hCA,hAj⟩ := hseed rcut hrcut hrcutp j
  obtain ⟨CQ,hCQ,hQj⟩ := hquotient j
  obtain ⟨CB,hCB,hBj⟩ := hcollective (j+1)
  obtain ⟨CC,hCC,hCj⟩ := hdifference j
  let N := 2*n
  have hN : 0<N := by dsimp [N]; omega
  obtain ⟨M,hM,hψj⟩ := hψframes N hN ψ hψ j
  let A := CA^N*(N:ℝ)^(j*j+5*j)
  let Q := max 1 CQ
  let B₀ := CB*(N:ℝ)^(2*(j+1)+2)
  let C₀ := CC*(N:ℝ)^(2*j+2)
  let D := d.b+2*B.delta+1
  have hA0 : 0≤A := by dsimp [A]; positivity
  have hQ1 : 1≤Q := le_max_left _ _
  have hB0 : 0≤B₀ := by dsimp [B₀]; positivity
  have hC0 : 0≤C₀ := by dsimp [C₀]; positivity
  have hD : 1≤D := by dsimp [D]; linarith [d.b_pos,B.delta_pos]
  let Z : ℂ := (N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1)
  let R := (((2:ℝ)^j*M)*((2:ℝ)^j*A*(2^j*((2^j*(2^j*Q*Q))^N))^N)/‖Z‖)*D^j*
    (D^2+2^j*(2*(N:ℝ)*B₀+2*(N:ℝ)^2*C₀))^j
  refine ⟨|R|+1,by positivity,?_⟩
  intro ε τ hε hεr hτ hτr θ hθ hdiam
  have hes : ε<εG ∧ ε<εA ∧ ε<εQ ∧ ε<εB ∧ ε<εC := by
    simpa only [lt_min_iff] using (hεr.trans_le (min_le_left _ _))
  have hts : τ<τG ∧ τ<τA ∧ τ<τQ ∧ τ<τB ∧ τ<τC := by
    simpa only [lt_min_iff] using (hτr.trans_le (min_le_left _ _))
  have hθG (i : Fin N) : -δG≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg hδs.1).trans (hθ i).1,(hθ i).2⟩
  have hθA (i : Fin N) : -δA≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg hδs.2.1).trans (hθ i).1,(hθ i).2⟩
  have hθQ (i : Fin N) : -δQ≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg hδs.2.2.1).trans (hθ i).1,(hθ i).2⟩
  have hθB (i : Fin N) : -δB₁≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg hδs.2.2.2.1).trans (hθ i).1,(hθ i).2⟩
  have hθC (i : Fin N) : -δC≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg hδs.2.2.2.2).trans (hθ i).1,(hθ i).2⟩
  obtain ⟨hpoint,hθstrict,hBa,hCa,hgood⟩ := hgeom N hN ε τ hε hes.1 hτ hts.1 θ hθG hdiam
  have hdiamD : preferredAngularDiameter θ≤D := by
    apply Metric.diam_le_of_forall_dist_le (le_trans (by norm_num) hD)
    rintro _ ⟨i,rfl⟩ _ ⟨k,rfl⟩
    rw [Real.dist_eq]
    apply abs_le.mpr
    have hδBB : δB<B.delta := hδB₀.trans_lt hδ₀B
    constructor <;> dsimp [D] <;> linarith [(hθ i).1,(hθ i).2,(hθ k).1,(hθ k).2]
  have hθF (i : Fin N) : -δF≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg (hδB₀.trans (min_le_right _ _))).trans (hθ i).1,(hθ i).2⟩
  have hh := preferred_weighted_source_vandermonde_bound n ψ hψ τ δ c preferredPopulationCutoff B.p B.m rcut
    preferredPopulationCutoff_smooth B.smooth B.m_smooth hrcut
    (IsingBulk.Branch.radialParameter d.alpha ε) θ hpoint hθstrict hBa hCa hgood
    j M A Q B₀ C₀ D hM.le hA0 hQ1 hB0 hC0 hdiam hdiamD hD
    (fun xs hxs => hψj ε τ hε (hεr.trans_le (min_le_right _ _)) hτ
      (hτr.trans_le (min_le_right _ _)) θ hθF xs hxs)
    (fun xs hxs => hAj N hN ε τ hε hes.2.1 hτ hts.2.1 θ hθA xs hxs)
    (fun i k xs hxs => (hQj N hN ε τ hε hes.2.2.1 hτ hts.2.2.1 θ hθQ xs hxs i k).trans (le_max_right _ _))
    (fun a xs hxs => hBj N hN ε τ hε hes.2.2.2.1 hτ hts.2.2.2.1 θ hθB hdiam xs hxs a)
    (fun i k xs hxs => hCj N hN ε τ hε hes.2.2.2.2 hτ hts.2.2.2.2 θ hθC hdiam xs hxs i k)
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply div_le_div_of_nonneg_right _ (by positivity)
  change R≤|R|+1
  linarith [le_abs_self R]

end
end IsingBulk.Preferred22
