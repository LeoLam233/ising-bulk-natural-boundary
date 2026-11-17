import IsingBulk.AnisoF002.C03.PhysicalLatticeSummability
import IsingBulk.AnisoF002.C03.PhysicalContourIntegration

/-!
# The actual full lattice sum equals the original full contour coefficient

The two integer geometric sums include the origin and both coordinate
axes.  Their exchange with the complete coupled contour integral is proved
by a summable uniform angular majorant on the original finite box.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter MeasureTheory IsingBulk.First IsingBulk.Anisotropic
  IsingBulk.Anisotropic.FormFactors
open scoped Topology BigOperators

theorem literal_complex_integer_geometric {X : ℂ} (hX : ‖X‖ < 1) :
    HasSum (fun m : ℤ => X ^ m.natAbs) ((1 + X) / (1 - X)) := by
  have h0 := hasSum_geometric_of_norm_lt_one hX
  have hn : HasSum (fun n : ℕ => X ^ ((n : ℤ).natAbs)) (1 - X)⁻¹ := by
    simpa only [Int.natAbs_natCast] using h0
  have hneg : HasSum (fun n : ℕ => X ^ (-(n + 1 : ℤ)).natAbs) (X * (1 - X)⁻¹) := by
    have he : HasSum (fun n : ℕ => X ^ (n + 1)) (X * (1 - X)⁻¹) := by
      simpa only [pow_succ'] using h0.mul_left X
    convert he using 1
    funext n
    congr 1
  convert HasSum.of_nat_of_neg_add_one (f := fun m : ℤ => X ^ m.natAbs) hn hneg using 1
  rw [div_eq_mul_inv]
  ring

theorem literal_latticeDensity_tsum {N : ℕ} {lam : ℝ} {z : ℂ} (x y : Fin N → ℂ)
    (hx : ‖coordinateProduct x‖ < 1) (hy : ‖coordinateProduct y‖ < 1) :
    (∑' v : LatticeSite, literalLatticeDensity lam z v x y) = fullDensity lam z x y := by
  have hX : Summable (fun m : ℤ => ‖coordinateProduct x ^ m.natAbs‖) := by
    simp only [norm_pow]
    exact literal_integer_geometric_summable (norm_nonneg _) hx
  have hY : Summable (fun m : ℤ => ‖coordinateProduct y ^ m.natAbs‖) := by
    simp only [norm_pow]
    exact literal_integer_geometric_summable (norm_nonneg _) hy
  unfold literalLatticeDensity
  rw [tsum_mul_right, ← tsum_mul_tsum_of_summable_norm hX hY,
    (literal_complex_integer_geometric hx).tsum_eq, (literal_complex_integer_geometric hy).tsum_eq]
  unfold FormFactors.onsiteDensity fullDensity
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem literal_pairProduct_continuous_family {E : Type*} [TopologicalSpace E] {N : ℕ}
    (x : E → Fin N → ℂ) (hx : ∀ i, Continuous (fun q => x q i))
    (hn : ∀ q i j, 1 - x q i * x q j ≠ 0) :
    Continuous (fun q => First.pairProduct (x q)) := by
  unfold First.pairProduct First.pairKernel
  apply continuous_finsetProd
  intro i _
  apply continuous_finsetProd
  intro j _
  exact ((hx i).sub (hx j)).div (continuous_const.sub ((hx i).mul (hx j))) (fun q => hn q i j)

theorem literal_commonDensity_continuous_angles {N : ℕ} {lam r : ℝ} {z : ℂ}
    (h : ContourAnnulus lam z r) :
    Continuous (fun q : (Fin N → ℝ) × (Fin N → ℝ) =>
      FormFactors.commonDensity lam z (angleTuple r q.1) (angleTuple r q.2)) := by
  let x := fun q : (Fin N → ℝ) × (Fin N → ℝ) => angleTuple r q.1
  let y := fun q : (Fin N → ℝ) × (Fin N → ℝ) => angleTuple r q.2
  have hx (i) : Continuous (fun q => x q i) := (continuous_apply i).comp
    ((literal_angleTuple_continuous r).comp continuous_fst)
  have hy (i) : Continuous (fun q => y q i) := (continuous_apply i).comp
    ((literal_angleTuple_continuous r).comp continuous_snd)
  have hxn (q) (i) : ‖x q i‖ = r := literal_anglePoint_norm h.1.le _
  have hyn (q) (i) : ‖y q i‖ = r := literal_anglePoint_norm h.1.le _
  have hx0 (q) (i) : x q i ≠ 0 := norm_ne_zero_iff.mp ((hxn q i).trans_ne h.1.ne')
  have hy0 (q) (i) : y q i ≠ 0 := norm_ne_zero_iff.mp ((hyn q i).trans_ne h.1.ne')
  have hD (i) : Continuous (fun q => (sliceDispersion lam z (x q i) (y q i))⁻¹) := by
    have hd : Continuous (fun q => sliceDispersion lam z (x q i) (y q i)) := by
      unfold sliceDispersion dispersionPolynomial
      exact (continuous_const.sub (continuous_const.mul ((hx i).add ((hx i).inv₀ (fun q => hx0 q i))))).sub
        (continuous_const.mul ((hy i).add ((hy i).inv₀ (fun q => hy0 q i))))
    apply hd.inv₀
    intro q
    exact h.2.2 _ _ (hxn q i).ge ((hxn q i).le.trans h.2.1.le)
      (hyn q i).ge ((hyn q i).le.trans h.2.1.le)
  exact ((literal_pairProduct_continuous_family x hx (fun q i j =>
    pair_root_denominator_ne_zero ((hxn q i).trans_lt h.2.1) ((hxn q j).trans_lt h.2.1))).mul
    (literal_pairProduct_continuous_family y hy (fun q i j =>
      pair_root_denominator_ne_zero ((hyn q i).trans_lt h.2.1) ((hyn q j).trans_lt h.2.1)))).mul
        (continuous_finsetProd _ (fun i _ => hD i))

theorem literal_latticeDensity_continuous_angles {N : ℕ} {lam r : ℝ} {z : ℂ}
    (h : ContourAnnulus lam z r) (v : LatticeSite) :
    Continuous (fun q : (Fin N → ℝ) × (Fin N → ℝ) =>
      literalLatticeDensity lam z v (angleTuple r q.1) (angleTuple r q.2)) := by
  have hx : Continuous (fun q : (Fin N → ℝ) × (Fin N → ℝ) => coordinateProduct (angleTuple r q.1)) :=
    continuous_finsetProd _ (fun i _ => (continuous_apply i).comp
      ((literal_angleTuple_continuous r).comp continuous_fst))
  have hy : Continuous (fun q : (Fin N → ℝ) × (Fin N → ℝ) => coordinateProduct (angleTuple r q.2)) :=
    continuous_finsetProd _ (fun i _ => (continuous_apply i).comp
      ((literal_angleTuple_continuous r).comp continuous_snd))
  have hne (q : (Fin N → ℝ) × (Fin N → ℝ)) :
      coordinateProduct (angleTuple r q.1) * coordinateProduct (angleTuple r q.2) ≠ 0 := by
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => norm_ne_zero_iff.mp
        ((literal_anglePoint_norm h.1.le (q.1 i)).trans_ne h.1.ne'))
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => norm_ne_zero_iff.mp
        ((literal_anglePoint_norm h.1.le (q.2 i)).trans_ne h.1.ne'))
  exact ((hx.pow v.1.natAbs).mul (hy.pow v.2.natAbs)).mul
    (((hx.mul hy).inv₀ hne).mul (literal_commonDensity_continuous_angles h))

theorem literal_latticeAngular_continuous {N : ℕ} {lam r : ℝ} {z : ℂ}
    (h : ContourAnnulus lam z r) (v : LatticeSite) :
    Continuous (literalDoubleAngularIntegrand r r (literalLatticeDensity lam z v) (N := N)) :=
  (((literal_angleProductJacobian_continuous r).comp continuous_snd).mul
    ((literal_angleProductJacobian_continuous r).comp continuous_fst)).mul
      (literal_latticeDensity_continuous_angles h v)

theorem literal_latticeAngular_zero_factor {N : ℕ} (lam r : ℝ) (z : ℂ)
    (v : LatticeSite) (q : (Fin N → ℝ) × (Fin N → ℝ)) :
    literalDoubleAngularIntegrand r r (literalLatticeDensity lam z v) q =
      (coordinateProduct (angleTuple r q.1) ^ v.1.natAbs *
        coordinateProduct (angleTuple r q.2) ^ v.2.natAbs) *
        literalDoubleAngularIntegrand r r (literalLatticeDensity lam z (0, 0)) q := by
  simp only [literalDoubleAngularIntegrand, literalLatticeDensity, Int.natAbs_zero, pow_zero, one_mul]
  ring

theorem literal_latticeAngular_uniform_majorant {N : ℕ} (hN : 0 < N)
    {lam r : ℝ} {z : ℂ} (h : ContourAnnulus lam z r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : LatticeSite, ∀ q ∈ angleBox N ×ˢ angleBox N,
      ‖literalDoubleAngularIntegrand r r (literalLatticeDensity lam z v) q‖ ≤ C * literalSiteEnvelope r v := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (literal_latticeAngular_continuous (N := N) h (0, 0)).continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro v q hq
  have hp : r ^ N ≤ r := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    rw [pow_succ]
    exact mul_le_of_le_one_left h.1.le (pow_le_one₀ h.1.le h.2.1.le)
  have hcoord (p : Fin N → ℝ) : ‖coordinateProduct (angleTuple r p)‖ ≤ r := by
    calc
      _ = r ^ N := by simp only [coordinateProduct, norm_prod, angleTuple,
        literal_anglePoint_norm h.1.le, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := hp
  rw [literal_latticeAngular_zero_factor, norm_mul, norm_mul, norm_pow, norm_pow]
  have hxpow := pow_le_pow_left₀ (norm_nonneg _) (hcoord q.1) v.1.natAbs
  have hypow := pow_le_pow_left₀ (norm_nonneg _) (hcoord q.2) v.2.natAbs
  have hxy := mul_le_mul hxpow hypow (pow_nonneg (norm_nonneg _) _) (pow_nonneg h.1.le _)
  have hh := mul_le_mul hxy ((hM q hq).trans (le_max_left M 0)) (norm_nonneg _)
    (mul_nonneg (pow_nonneg h.1.le _) (pow_nonneg h.1.le _))
  simpa only [literalSiteEnvelope, mul_comm (max M 0)] using hh

theorem literal_latticeCoefficient_tsum {N : ℕ} (hN : 0 < N)
    {lam r : ℝ} {z : ℂ} (h : ContourAnnulus lam z r) :
    (∑' v : LatticeSite, literalLatticeCoefficientAtRadius N r lam z v) =
      unscaledFullCoefficientAtRadius N r lam z := by
  let K : Set ((Fin N → ℝ) × (Fin N → ℝ)) := angleBox N ×ˢ angleBox N
  let F (v : LatticeSite) := literalDoubleAngularIntegrand r r (literalLatticeDensity lam z v) (N := N)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hFi (v : LatticeSite) : IntegrableOn (F v) K :=
    (literal_latticeAngular_continuous h v).continuousOn.integrableOn_compact hK
  obtain ⟨C, hC, hbound⟩ := literal_latticeAngular_uniform_majorant hN h
  have hsum : Summable (fun v : LatticeSite => ∫ q in K, ‖F v q‖) := by
    apply (((literalSiteEnvelope_summable h.1.le h.2.1).mul_left C).mul_right (volume.real K)).of_nonneg_of_le
    · intro v
      exact integral_nonneg (fun _ => norm_nonneg _)
    · intro v
      have hh := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := K)
        (f := fun q => ‖F v q‖) hK.measure_lt_top
        (fun q hq => by simpa only [norm_norm] using hbound v q hq)
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hh
      exact hh
  have hi := integral_tsum_of_summable_integral_norm hFi hsum
  have hcoef (v : LatticeSite) : literalLatticeCoefficientAtRadius N r lam z v =
      (N.factorial : ℂ)⁻¹ * ∫ q in K, F v q := by
    unfold literalLatticeCoefficientAtRadius
    rw [literal_doubleContour_eq_box r r _ (literal_latticeDensity_continuous_angles h v)]
  calc
    _ = (N.factorial : ℂ)⁻¹ * ∑' v : LatticeSite, ∫ q in K, F v q := by
      simp_rw [hcoef]
      rw [tsum_mul_left]
    _ = (N.factorial : ℂ)⁻¹ * ∫ q in K, ∑' v : LatticeSite, F v q := by rw [hi]
    _ = (N.factorial : ℂ)⁻¹ * ∫ q in K, literalDoubleAngularIntegrand r r (fullDensity lam z) q := by
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro q
      dsimp only [F, literalDoubleAngularIntegrand]
      rw [tsum_mul_left, literal_latticeDensity_tsum]
      · exact literal_coordinateProduct_norm_lt_one hN (fun i =>
          (literal_anglePoint_norm h.1.le (q.1 i)).trans_lt h.2.1)
      · exact literal_coordinateProduct_norm_lt_one hN (fun i =>
          (literal_anglePoint_norm h.1.le (q.2 i)).trans_lt h.2.1)
    _ = _ := (literal_fixedCoefficient_eq_box hN h).symm

end
end IsingBulk.AnisoF002.RegularTail.C03
