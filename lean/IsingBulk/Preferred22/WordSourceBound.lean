import IsingBulk.Preferred22.WordMajorant
import IsingBulk.Preferred22.PhysicalJacobianBound
import IsingBulk.Preferred22.PhysicalTransportIteration
import IsingBulk.Preferred22.SourceMarkedWords
import IsingBulk.Preferred22.ShellGeometry

/-! The remaining scalar coefficient estimate is applied to the literal
physical descendants. The source geometry, exact all-order Piola identity,
finite marked-word expansion, determinant minors and factorials are proved. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators Topology ContDiff

/-- The precise scalar estimate remaining after the actual finite word
expansion. It retains the normalization and states no shell or tail bound. -/
def PreferredNormalizedWordBound (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (δB τ ε₀ : ℝ) (η rcut : ℝ → ℝ) (k : ℕ) : Prop :=
  ∀ j : ℕ,j≤k → ∃ C : ℝ,∃ J : ℕ,0<C ∧
    ∀ N : ℕ,2≤N → ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ θ : Fin N → ℝ,
      θ∈preferredRightAngularBox d B.delta δB N → 0<preferredAngularDiameter θ →
      ∀ w : PreferredMarkedWord N j,
      ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*preferredWordCoefficient τ η B.p B.m rcut j w
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖ ≤
        C^N*(N:ℝ)^J/(preferredAngularDiameter θ)^(preferredWordLoss j w)

/-- The fixed-order combinatorial factor is absorbed only exponentially in
N. The exact N! decay remains in the displayed shell envelope. -/
theorem preferred_word_envelope_absorb {N j J : ℕ} (hN : 0<N)
    {S M C : ℝ} (hS : 1≤S) (hM : 0≤M) (hC : 0≤C) :
    M^N*(2*S)^j*shellOrderEnvelope C J N ≤
      shellOrderEnvelope ((2*S)^j*M*C) J N := by
  have ha : 1≤(2*S)^j := one_le_pow₀ (by linarith)
  have hp : (2*S)^j≤((2*S)^j)^N := by
    simpa only [pow_one] using pow_le_pow_right₀ ha (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hN))
  calc
    _ ≤ M^N*((2*S)^j)^N*shellOrderEnvelope C J N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (pow_nonneg hM _))
        (by unfold shellOrderEnvelope; positivity)
    _ = _ := by unfold shellOrderEnvelope; simp only [mul_pow,div_pow]; ring

/-- Actual q20 from the precise normalized word bound. All physical
identities and every regular kernel entry estimate are discharged here.
The square-root scale upper bound is explicit and will follow from the
actual constrained shell geometry. -/
theorem preferred_actual_word_source_majorant (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ K M ε₀ τ₀ δ₀ : ℝ,1≤K ∧ 0<M ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δ₀ ∧ δ₀<B.delta ∧
      ∀ N : ℕ,2≤N → ∀ ε τ t r S : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      0<r → 1≤S → Real.sqrt (|t|+r+ε)≤S →
      ∀ θ : Fin N → ℝ,
      (∀ v,-δ₀≤θ v+d.b ∧ θ v+d.b≤d.b+B.delta) →
      (∀ v,t-2*r≤θ v+d.b ∧ θ v+d.b≤t+2*r) →
      r≤preferredAngularDiameter θ →
      ∀ η rcut : ℝ → ℝ,ContDiff ℝ ∞ η → ContDiff ℝ ∞ rcut →
      ∀ j J : ℕ,∀ C : ℝ,0<C →
      (∀ w : PreferredMarkedWord N j,
        ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*preferredWordCoefficient τ η B.p B.m rcut j w
          (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
          C^N*(N:ℝ)^J/(preferredAngularDiameter θ)^(preferredWordLoss j w)) →
      ‖preferredTransportedDensity .right τ η B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
        2*shellOrderEnvelope ((2*S)^j*M*(C*K*Real.exp 1)) (J+2*j) N*
          (r^N/(r^(2*j)*(Real.sqrt (|t|+r+ε))^N))*preferredJacobianResolvent d B ε τ θ := by
  obtain ⟨cs,hcs,hcsa,hsize⟩ := preferred_actual_regular_size d
  obtain ⟨cf,hcf,_hcfa,hfactor⟩ := preferred_actual_all_order_factorization d
  obtain ⟨cw,hcw,_hcwa,hwords⟩ := preferred_actual_marked_word_expansion d
  let cap := min cs (min cf cw)
  refine ⟨cap,lt_min hcs (lt_min hcf hcw),(min_le_left _ _).trans_lt hcsa,?_⟩
  intro B hBcap
  obtain ⟨τs,δs,εs,Cs,hτs,hδs,hεs,hCs,hs⟩ := hsize B.delta B.delta_pos
    (hBcap.trans_le (min_le_left _ _)) B.p B.m B.smooth.continuous B.m_smooth.continuous
    (fun x => ⟨B.lower_bound x,B.upper_bound x⟩)
    (fun x => ⟨B.lower_bound (-x),B.upper_bound (-x)⟩)
    (fun x hx => B.p_zero_of_sin_nonpos hx) (fun x hx => B.m_zero_of_sin_nonneg hx)
  obtain ⟨δf,τf,εf,hδf,_hδfδ,hτf,hεf,hf⟩ := hfactor B
    (hBcap.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨εw,τw,δw,hεw,hτw,hδw,_hδwδ,hw⟩ := hwords B
    (hBcap.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨Cd,εd,τd,δd,hCd,hεd,hτd,hδd,hδdδ,hd⟩ := preferred_actual_coordinate_difference d B
  obtain ⟨M,εM,hM,hεM,hJM⟩ := preferred_actual_JH_bound d B
  let K := max 1 (Cs*Cd)
  let ε₀ := min εs (min εf (min εw (min εd εM)))
  let τ₀ := min τs (min τf (min τw (min τd 1)))
  let δ₀ := min δs (min δf (min δw δd))
  have hε₀ : 0<ε₀ := lt_min hεs (lt_min hεf (lt_min hεw (lt_min hεd hεM)))
  have hτ₀ : 0<τ₀ := lt_min hτs (lt_min hτf (lt_min hτw (lt_min hτd (by norm_num))))
  have hδ₀ : 0<δ₀ := lt_min hδs (lt_min hδf (lt_min hδw hδd))
  have hδd' : δ₀≤δd := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ₀δ : δ₀<B.delta := hδd'.trans_lt hδdδ
  refine ⟨K,M,ε₀,τ₀,δ₀,le_max_left _ _,hM,hε₀,hτ₀,hδ₀,hδ₀δ,?_⟩
  intro N hN ε τ t r S hε hεr hτ hτr hr hS hscale θ hbox hwindow hrD η rcut hη hrcut j J C hC hcoeff
  have hN0 : 0<N := by omega
  have hD : 0<preferredAngularDiameter θ := hr.trans_le hrD
  have hεs' : ε<εs := hεr.trans_le (min_le_left _ _)
  have hεf' : ε<εf := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεw' : ε<εw := hεr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεd' : ε<εd := hεr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hεM' : ε<εM := hεr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hτs' : τ<τs := hτr.trans_le (min_le_left _ _)
  have hτf' : τ<τf := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hτw' : τ<τw := hτr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hτd' : τ<τd := hτr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hτ1 : τ≤1 := (hτr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))).le
  have hδs' : δ₀≤δs := min_le_left _ _
  have hδf' : δ₀≤δf := (min_le_right _ _).trans (min_le_left _ _)
  have hδw' : δ₀≤δw := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hboxs : θ∈preferredRightAngularBox d B.delta δs N := fun i =>
    ⟨by linarith [(hbox i).1],by linarith [(hbox i).2]⟩
  have hboxf : θ∈preferredRightAngularBox d B.delta δf N := fun i =>
    ⟨by linarith [(hbox i).1],by linarith [(hbox i).2]⟩
  have hboxw (i : Fin N) : -δw≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨by linarith [(hbox i).1],(hbox i).2⟩
  have hboxd (i : Fin N) : -δd≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨by linarith [(hbox i).1],(hbox i).2⟩
  have hθ (i : Fin N) : θ i∈Icc (-Real.pi-B.delta) B.delta :=
    ⟨by linarith [(hbox i).1,d.b_lt],by linarith [(hbox i).2]⟩
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hreg := hs τ hτ hτs' N hN ε θ hε hεs' hboxs
  have hdiff := hd N hN0 ε τ t r hε hεd' hτ hτd' hr θ hboxd hwindow
  have hq : 0<Real.sqrt (|t|+r+ε) := Real.sqrt_pos.2 (by positivity)
  have hentry (i a : Fin N) : ‖preferredSourceRegularKernel τ B.p B.m s θ i a‖≤K*r/Real.sqrt (|t|+r+ε) := by
    calc
      _ ≤ Cs*‖preferredSourceCoordinate τ B.p B.m s θ i-preferredSourceCoordinate τ B.p B.m s θ a‖ := (hreg i).2 a
      _ ≤ Cs*(Cd*r/Real.sqrt (|t|+r+ε)) := mul_le_mul_of_nonneg_left (hdiff i a) hCs.le
      _ = (Cs*Cd)*r/Real.sqrt (|t|+r+ε) := by ring
      _ ≤ K*r/Real.sqrt (|t|+r+ε) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le) hq.le
  have hws := preferredWordSum_q20_bound hN0 τ η B.p B.m rcut j J s θ hC
    (le_max_left _ _ : 1≤K) hr hrD hq hscale hS hentry hcoeff
  have hjs := hJM N hN0 ε τ hε hεM' hτ hτ1 θ hθ
  have henv := preferred_word_envelope_absorb (j := j) (J := J+2*j) hN0 hS hM.le
    (by positivity : 0≤C*K*Real.exp 1)
  rw [hf N hN ε τ hε hεf' hτ hτf' θ hboxf hD η rcut hη hrcut j,
    hw N hN0 ε τ hε hεw' hτ hτw' θ hboxw hD η rcut hη hrcut j,norm_mul]
  calc
    _ ≤ (2*M^N*preferredJacobianResolvent d B ε τ θ)*
        ((2*S)^j*shellOrderEnvelope (C*K*Real.exp 1) (J+2*j) N*
          (r^N/(r^(2*j)*(Real.sqrt (|t|+r+ε))^N))) :=
      mul_le_mul hjs hws (norm_nonneg _) (mul_nonneg (by positivity : 0≤2*M^N)
        (preferredJacobianResolvent_nonneg d B ε τ θ))
    _ = 2*(M^N*(2*S)^j*shellOrderEnvelope (C*K*Real.exp 1) (J+2*j) N)*
        (r^N/(r^(2*j)*(Real.sqrt (|t|+r+ε))^N))*preferredJacobianResolvent d B ε τ θ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left henv (by norm_num)) (by positivity))
      (preferredJacobianResolvent_nonneg d B ε τ θ)

end
end IsingBulk.Preferred22
