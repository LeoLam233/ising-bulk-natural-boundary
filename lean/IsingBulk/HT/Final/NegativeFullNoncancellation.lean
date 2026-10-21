import IsingBulk.HT.Final.NegativeLowFullTerms
import IsingBulk.HT.Final.ExteriorFullSeries
import IsingBulk.HT.First.NegativeFirstTheorem
import IsingBulk.HT.Tail.FullOddTailAssembly

/-! Noncancellation for the original negative integer-angle family. The FIRST
term, every lower coefficient and the complete higher odd tail concern the
same literal full-site contour source and the same selected point. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.HT.First IsingBulk.HT.Tail Filter
open scoped Topology BigOperators

theorem selected_negative_upper_full_asymptotic {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (hab : a ≠ b) :
    let k := derivativeOrder p
    let L := Regular.oddLocalLeadingCoefficient (negativeSelectedRegularChart ha hb) p
    4*L ≠ 0 ∧ Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun eps => iteratedDeriv k upperFullOddSeries
        (radialParameter (negativeSelectedRegularChart ha hb).theta eps)-(eps:ℂ)⁻¹*(4*L))
      (fun eps : ℝ => (eps:ℂ)⁻¹) := by
  dsimp only
  let A := negativeSelectedRegularChart ha hb
  let k := derivativeOrder p
  let L := Regular.oddLocalLeadingCoefficient A p
  obtain ⟨hL,hFirst⟩ := Regular.negative_first_standard_odd_source_asymptotic hp hp11 ha hb hab
  obtain ⟨d,hd,hRep⟩ := radial_upper_full_derivatives p hp.pos A.sin_theta_pos
  have hF : Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun eps => iteratedDeriv k (upperFullCoefficient p) (radialParameter A.theta eps)
        -(eps:ℂ)⁻¹*(4*L)) (fun eps : ℝ => (eps:ℂ)⁻¹) := by
    apply hFirst.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds] with eps he heD
    rw [hRep eps he heD]
  have hLow := negative_lower_full_sum_littleO hp hp11 ha hb k
  have hTail : Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun eps => ∑' n : ℕ,iteratedDeriv k (upperFullCoefficient (oddTailParticle p n))
        (radialParameter A.theta eps)) (fun eps : ℝ => (eps:ℂ)⁻¹) := by
    have hz := negative_original_family_upper_full_odd_tail_epsilon_zero hp hp11 ha hb k le_rfl
    simpa only [mul_zero,sub_zero] using normalized_epsilon_limit_isLittleO hz
  have hq : 2*(p/2)+1 = p := by
    obtain ⟨q,hq⟩ := hp.odd_of_ne_two (by omega)
    omega
  refine ⟨hL,?_⟩
  apply ((hLow.add hF).add hTail).congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with eps he
  rw [upperFullOddSeries_radial_split (p/2) k A.sin_theta_pos he,hq]
  ring

theorem selected_negative_exterior_full_limit {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (hab : a ≠ b) :
    let k := derivativeOrder p
    let L := Regular.oddLocalLeadingCoefficient (negativeSelectedRegularChart ha hb) p
    4*L ≠ 0 ∧ Tendsto (fun eps : ℝ => eps • iteratedDeriv k exteriorOddSeries
      ((1+(eps:ℂ))*PrimeFamily.selectedPoint p a b)) (𝓝[>] 0) (𝓝 (4*L)) := by
  dsimp only
  obtain ⟨hL,hA⟩ := selected_negative_upper_full_asymptotic hp hp11 ha hb hab
  refine ⟨hL,?_⟩
  apply (epsilon_limit_of_isLittleO hA).congr'
  filter_upwards [self_mem_nhdsWithin] with eps he
  have hpath : radialParameter (negativeSelectedRegularChart ha hb).theta eps =
      (1+(eps:ℂ))*PrimeFamily.selectedPoint p a b := by
    simp only [radialParameter,negativeSelectedRegularChart,PrimeFamily.selectedPoint,
      Complex.ofReal_add,Complex.ofReal_one]
  rw [← hpath,exteriorOddSeries_iteratedDeriv_eq_upper _
    (IsingBulk.Final.sourceRadialTrace_pos (negativeSelectedRegularChart ha hb).sin_theta_pos he)]

theorem selected_negative_exterior_no_extension {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (hab : a ≠ b) :
    ¬ IsingBulk.Final.HasExteriorExtension exteriorOddSeries (PrimeFamily.selectedPoint p a b) := by
  obtain ⟨hL,hlim⟩ := selected_negative_exterior_full_limit hp hp11 ha hb hab
  exact no_extension_of_nonzero_epsilon_radial_limit
    (Complex.norm_exp_ofReal_mul_I _) hL (derivativeOrder p) hlim

end
end IsingBulk.HT.Final
