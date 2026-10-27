import IsingBulk.Preferred22.CoefficientBounds
import IsingBulk.Preferred22.CollectiveFrameJets
import IsingBulk.Preferred22.RegularFrameJets

/-! Actual-source coefficient norm reduction. The collective and kernel
jet estimates and all geometry are proved; only the exact normalized seed
frame estimate remains as an explicit original-cutoff/product input. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferred_actual_word_bound_of_seed (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ j : ℕ, ∀ A : ℝ, 1≤A → ∀ L : ℕ, ∃ C : ℝ, 0<C ∧
        ∀ η rcut : ℝ → ℝ, ContDiff ℝ ∞ η → ContDiff ℝ ∞ rcut →
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        0<preferredAngularDiameter θ →
        (∀ xs : List (Option (Fin N)), xs.length≤j →
          ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*
            preferredFrameJet τ B.p B.m (preferredRegularSeedCoefficient τ η B.p B.m rcut) xs
              (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤A^N*(N:ℝ)^L) →
        ∀ w : PreferredMarkedWord N j,
        ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*preferredWordCoefficient τ η B.p B.m rcut j w
          (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
          C^N*(N:ℝ)^(L+(2*j+2)*(2*j+1)+j)/preferredAngularDiameter θ^(preferredWordLoss j w) := by
  obtain ⟨capB,hcapB,hcapBa,hBj⟩ := preferred_actual_collective_frame_jets d
  obtain ⟨capK,hcapK,hcapKa,hKj⟩ := preferred_actual_regular_frame_jets d
  obtain ⟨capA,hcapA,hcapAa,hAn⟩ := preferred_actual_collective_neighborhood d
  refine ⟨min capB (min capK capA),lt_min hcapB (lt_min hcapK hcapA),
    (min_le_left _ _).trans_lt hcapBa,?_⟩
  intro B hBcap
  obtain ⟨εB,τB,δB₁,hεB,hτB,hδB₁,hδB₁B,hBjets⟩ := hBj B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨εK,τK,δB₂,hεK,hτK,hδB₂,hδB₂B,hKjets⟩ :=
    hKj B (hBcap.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨a,M,εA,τA,δB₃,ha,hM,hεA,hτA,hδB₃,hδB₃B,hneigh⟩ :=
    hAn B (hBcap.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨δ,εF,τF,hδ,hδa,hεF,hτF,hframe⟩ := preferred_actual_frame_points d B
  let ε₀ := min εB (min εK (min εA εF))
  let τ₀ := min τB (min τK (min τA τF))
  let δB := min δB₁ (min δB₂ δB₃)
  have hδB : 0<δB := lt_min hδB₁ (lt_min hδB₂ hδB₃)
  have hδBB : δB<B.delta := (min_le_left _ _).trans_lt hδB₁B
  refine ⟨ε₀,τ₀,δB,lt_min hεB (lt_min hεK (lt_min hεA hεF)),
    lt_min hτB (lt_min hτK (lt_min hτA hτF)),hδB,hδBB,?_⟩
  intro j A hA L
  obtain ⟨CB,hCB,hBbound⟩ := hBjets j
  obtain ⟨CK,hCK,hKbound⟩ := hKjets j
  let R := max A (max CB CK)
  have hR : 1≤R := hA.trans (le_max_left _ _)
  have hRpos : 0<R := lt_of_lt_of_le (by norm_num) hR
  let D := d.b+2*B.delta+1
  have hD : 1≤D := by dsimp [D]; linarith [d.b_pos,B.delta_pos]
  let C := (preferredCoefficientCountConstant j:ℝ)*R^(2*j+2)*D^(2*j)
  have hC : 0<C := by
    have hh : (0:ℝ)<preferredCoefficientCountConstant j := by exact_mod_cast preferredCoefficientCountConstant_pos j
    have hDp : 0<D := lt_of_lt_of_le (by norm_num) hD
    dsimp [C]
    positivity
  refine ⟨C,hC,?_⟩
  intro η rcut hη hrcut N hN ε τ hε hεr hτ hτr θ hθ hdiam hseed w
  have heB : ε<εB := hεr.trans_le (min_le_left _ _)
  have heK : ε<εK := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heA : ε<εA := hεr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heF : ε<εF := hεr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have htB : τ<τB := hτr.trans_le (min_le_left _ _)
  have htK : τ<τK := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htA : τ<τA := hτr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htF : τ<τF := hτr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hθB (i : Fin N) : -δB₁≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg (min_le_left _ _)).trans (hθ i).1,(hθ i).2⟩
  have hθK (i : Fin N) : -δB₂≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg ((min_le_right _ _).trans (min_le_left _ _))).trans (hθ i).1,(hθ i).2⟩
  have hθA (i : Fin N) : -δB₃≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg ((min_le_right _ _).trans (min_le_right _ _))).trans (hθ i).1,(hθ i).2⟩
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  have hBa : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredResidualCollective z.1 z.2) (s,q) :=
    preferredResidualCollective_analyticAt_of_rescaled hN s q a (preferredAngularDiameter θ) ha hdiam
      ((hneigh N hN ε τ hε heA hτ htA θ hθA hdiam).1 0 (by simp))
  obtain ⟨hpoint,hθstrict⟩ := hframe δB hδB hδBB N hN ε τ hε heF hτ htF θ hθ
  have hdiamD : preferredAngularDiameter θ≤D := by
    apply Metric.diam_le_of_forall_dist_le (le_trans (by norm_num) hD)
    rintro _ ⟨i,rfl⟩ _ ⟨k,rfl⟩
    rw [Real.dist_eq]
    apply abs_le.mpr
    constructor <;> dsimp [D] <;> linarith [(hθ i).1,(hθ i).2,(hθ k).1,(hθ k).2]
  exact preferredWordCoefficient_bound_of_source_frames hN τ δ η B.p B.m rcut hη B.smooth B.m_smooth hrcut
    s θ hpoint hθstrict hBa R D hR hdiam hdiamD hD L (2*j+2) j
    (fun xs hxs => (hseed xs hxs).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (le_trans (by norm_num) hA) (le_max_left _ _) _) (by positivity)))
    (fun i xs hxs => (hBbound N hN ε τ hε heB hτ htB θ hθB hdiam xs hxs i).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right A (max CB CK))) (by positivity)) (by positivity)))
    (fun ij xs hxs => ((hKbound N hN ε τ hε heK hτ htK θ hθK xs hxs).2 ij.1 ij.2).trans
      ((le_max_right _ _).trans (le_max_right A (max CB CK)))) w

end
end IsingBulk.Preferred22
