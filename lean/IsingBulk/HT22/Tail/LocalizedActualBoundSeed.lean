import IsingBulk.HT22.Tail.LocalizedActualBoundDet
import IsingBulk.HT22.Tail.LocalizedSeed
import IsingBulk.HT22.Tail.ActualRightChart
import IsingBulk.HT22.Transport.FieldNeighborhood.SmoothWeightJets
import IsingBulk.HT22.SeedFrameConversion.ActualSeed
import IsingBulk.HT22.Kernel.ActualJets
import IsingBulk.HT22.Far.UnscaledShell

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem norm_le_normalized_seed_norm (N : ℕ) (z : ℂ) :
    ‖z‖≤‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*z‖ := by
  have hfac : (1:ℝ)≤N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hh := Far.norm_le_haar_norm (N-1) z
  apply hh.trans
  calc
    _ ≤ (N.factorial:ℝ)*‖(2*Real.pi:ℂ)^(N-1)*z‖ := le_mul_of_one_le_left (norm_nonneg _) hfac
    _ = _ := by simp only [norm_mul,Complex.norm_natCast];ring

theorem actual_localized_seed_frame_jets (b : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b,B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ,0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ N : ℕ,0<N → ∀ W : (Fin N → ℝ) → ℂ,ContDiff ℝ ∞ W →
    ∀ rcut : ℝ → ℝ,ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ j : ℕ,∃ C : ℝ,0<C ∧ ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
    ∀ θ : Fin N → ℝ,(∀ i,-δB≤θ i+b.b ∧ θ i+b.b≤b.b+B.delta) →
    0<preferredAngularDiameter θ → ∀ xs : List (Option (Fin N)),xs.length≤j →
    ‖frameJet τ B.p B.m (localizedSeed τ preferredPopulationCutoff B.p B.m rcut W) xs
      (IsingBulk.Branch.radialParameter b.alpha ε) θ‖≤C := by
  obtain ⟨cS,hcS,hcSa,hseed⟩ := SeedFrameConversion.actual_normalized_seed_frame_jets b
  obtain ⟨cK,hcK,_hcKa,hkernel⟩ := Kernel.actual_ordinary_kernel_frame_jets b
  obtain ⟨cW,hcW,_hcWa,hweight⟩ := actual_smooth_weight_frame_jets b
  obtain ⟨cR,hcR,_hcRa,hchart⟩ := actual_right_source_chart b
  refine ⟨min cS (min cK (min cW cR)),by positivity,(min_le_left _ _).trans_lt hcSa,?_⟩
  intro B hB
  obtain ⟨eS,tS,dS,heS,htS,hdS,hdSB,hseed⟩ := hseed B (hB.trans_le (by simp))
  obtain ⟨eK,tK,dK,heK,htK,hdK,_hdKB,hkernel⟩ := hkernel B (hB.trans_le (by simp))
  obtain ⟨eW,tW,dW,heW,htW,hdW,_hdWB,hweight⟩ := hweight B (hB.trans_le (by simp))
  obtain ⟨c,δ,eR,tR,dR,_hc,heR,htR,hdR,_hdRB,hchart⟩ := hchart B (hB.trans_le (by simp))
  let e := min eS (min eK (min eW eR))
  let t := min tS (min tK (min tW tR))
  let d := min dS (min dK (min dW dR))
  refine ⟨e,t,d,by positivity,by positivity,by positivity,(min_le_left _ _).trans_lt hdSB,?_⟩
  intro N hN W hW rcut hrcut hrper j
  obtain ⟨AS,hAS,hS⟩ := hseed rcut hrcut hrper j
  obtain ⟨AK,hAK,hK⟩ := hkernel j
  obtain ⟨AW,hAW,hWb⟩ := hweight N hN W hW j
  let CK := max 1 AK
  let CS := AS^N*(N:ℝ)^(j*j+6*j)
  let CD := (1+∑ σ : Equiv.Perm (Fin (N+1)), ‖((Equiv.Perm.sign σ:ℤ):ℂ)‖)*(2^j*CK)^(N+1)
  have hCS : 0<CS := by
    have hn : (0:ℝ)<N := by exact_mod_cast hN
    dsimp [CS]
    positivity
  have hCD : 0<CD := by dsimp [CD,CK];positivity
  refine ⟨2^j*AW*(2^j*CS*CD),by positivity,?_⟩
  intro ε τ hε hεr hτ hτr θ hθ hdiam xs hxs
  have heps : ε<eS ∧ ε<eK ∧ ε<eW ∧ ε<eR := by simpa only [e,lt_min_iff] using hεr
  have htaus : τ<tS ∧ τ<tK ∧ τ<tW ∧ τ<tR := by simpa only [t,lt_min_iff] using hτr
  have hdS' : d≤dS := by simp [d]
  have hdK' : d≤dK := by simp [d]
  have hdW' : d≤dW := by simp [d]
  have hdR' : d≤dR := by simp [d]
  have hbox (d' : ℝ) (hd' : d≤d') (i : Fin N) : -d'≤θ i+b.b ∧ θ i+b.b≤b.b+B.delta :=
    ⟨by linarith [(hθ i).1],(hθ i).2⟩
  obtain ⟨Ω,hΩ,hz,hpoint,hR,_⟩ := hchart N hN ε τ hε heps.2.2.2 hτ htaus.2.2.2
    θ (hbox dR hdR') hdiam
  let s := IsingBulk.Branch.radialParameter b.alpha ε
  have hseedmix := regularSeedCoefficient_mixed τ δ preferredPopulationCutoff B.p B.m rcut
    preferredPopulationCutoff_smooth B.smooth B.m_smooth hrcut Ω hpoint
  have hdetmix := matrix_det_mixed Ω (sourceBorderedKernel τ B.p B.m)
    (sourceBorderedKernel_entry_mixed τ δ B.p B.m B.smooth B.m_smooth Ω hpoint)
  have hregmix : PreferredMixedSmoothOn (fun z => regularSeed τ preferredPopulationCutoff B.p B.m rcut z.1 z.2) Ω :=
    hseedmix.mul hdetmix
  have hwmix : PreferredMixedSmoothOn (fun z : ℂ × (Fin N → ℝ) => W z.2) Ω := by
    intro z _
    exact ⟨(hW.comp contDiff_snd).contDiffAt,by change DifferentiableAt ℂ (fun _ : ℂ => W z.2) z.1;fun_prop⟩
  have hSb (ys : List (Option (Fin N))) (hys : ys.length≤j) :
      ‖frameJet τ B.p B.m (regularSeedCoefficient τ preferredPopulationCutoff B.p B.m rcut) ys s θ‖≤CS :=
    (norm_le_normalized_seed_norm N _).trans (hS N hN ε τ hε heps.1 hτ htaus.1 θ (hbox dS hdS') ys hys)
  have hKb (i k : Fin N) (ys : List (Option (Fin N))) (hys : ys.length≤j) :
      ‖frameJet τ B.p B.m (fun t x => sourceOrdinaryKernel τ B.p B.m t x i k) ys s θ‖≤CK :=
    (hK N hN ε τ hε heps.2.1 hτ htaus.2.1 θ (hbox dK hdK') ys hys i k).trans (le_max_right _ _)
  have hDb (ys : List (Option (Fin N))) (hys : ys.length≤j) :
      ‖frameJet τ B.p B.m (fun t x => (sourceBorderedKernel τ B.p B.m t x).det) ys s θ‖≤CD :=
    frameJet_det_bound τ δ B.p B.m B.smooth B.m_smooth Ω hΩ hpoint hR _
      (sourceBorderedKernel_entry_mixed τ δ B.p B.m B.smooth B.m_smooth Ω hpoint)
      s θ hz j CK (by dsimp [CK];positivity)
      (fun i k zs hzs => sourceBorderedKernel_frame_bound τ B.p B.m s θ j CK (le_max_left _ _) hKb i k zs hzs) ys hys
  have hregb (ys : List (Option (Fin N))) (hys : ys.length≤j) :
      ‖frameJet τ B.p B.m (regularSeed τ preferredPopulationCutoff B.p B.m rcut) ys s θ‖≤2^j*CS*CD :=
    frameJet_mul_bound τ δ B.p B.m B.smooth B.m_smooth Ω hΩ hpoint hR _ _ hseedmix hdetmix
      s θ hz j CS CD hCS.le hCD.le hSb hDb ys hys
  exact frameJet_mul_bound τ δ B.p B.m B.smooth B.m_smooth Ω hΩ hpoint hR _ _ hwmix hregmix
    s θ hz j AW (2^j*CS*CD) hAW.le (by positivity)
    (fun ys hys => hWb ε τ hε heps.2.2.1 hτ htaus.2.2.1 θ (hbox dW hdW') ys hys) hregb xs hxs

end
end IsingBulk.HT22.Tail
