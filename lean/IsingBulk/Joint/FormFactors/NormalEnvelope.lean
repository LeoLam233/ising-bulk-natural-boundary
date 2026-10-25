import IsingBulk.Joint.FormFactors.ContourNorm
import IsingBulk.Joint.FormFactors.KernelBound
import IsingBulk.Joint.FormFactors.RadiusIndependence
import IsingBulk.Joint.Geometry.Basic
import IsingBulk.Anisotropic.FormFactors.NormalConvergence

/-! Common local all-particle bounds in the two independent complex couplings.
The numerical Hadamard envelope and its parity summability are reused exactly. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
set_option maxHeartbeats 300000
open Set Filter
open IsingBulk.Anisotropic.FormFactors (contourKernelBound contourPairBound
  circle_pairProduct_bound hadamardEnvelope weighted_envelope contourKernelBound_ge_one)
open scoped Topology

theorem fullCoefficient_hadamard_bound (N : ℕ) (hN : 0 < N)
    {r M : ℝ} {K : Coupling} (ha : ContourAnnulus K r) (hK : K ∉ spectralSet) (hM : 0 ≤ M)
    (hD : ∀ x y : ℂ, ‖x‖=r → ‖y‖=r → ‖(dispersion K x y)⁻¹‖ ≤ M) :
    ‖unscaledFullCoefficient N K‖ ≤
      ((2/(1-r))^2*contourKernelBound r)*hadamardEnvelope (contourPairBound r*M) N := by
  have hh := unscaledFullCoefficientAtRadius_norm_le N hN (K := K) (r := r) (M := M)
    (A := contourKernelBound r*(contourPairBound r)^N*(N:ℝ)^(N-N/2)) ha.1 ha.2.1 hM hD
    (fun x y hx hy => circle_pairProduct_bound N hN ha.1 ha.2.1 x y hx hy)
  have he : unscaledFullCoefficient N K = unscaledFullCoefficientAtRadius N r K :=
    unscaledFullCoefficient_eq_fixed_radius N hN (K := K) (r := r) hK ha
  have hscalar :
      (2/(1-r))^2*(contourKernelBound r*(contourPairBound r)^N*(N:ℝ)^(N-N/2))*M^N /
        (N.factorial:ℝ) =
      ((2/(1-r))^2*contourKernelBound r)*hadamardEnvelope (contourPairBound r*M) N := by
    unfold hadamardEnvelope
    rw [mul_pow]
    ring
  calc
    ‖unscaledFullCoefficient N K‖ = ‖unscaledFullCoefficientAtRadius N r K‖ := congrArg norm he
    _ ≤ _ := hh.trans_eq hscalar

theorem local_fullCoefficient_envelope {K : Coupling} (hK : K ∉ spectralSet) :
    ∃ D C : ℝ, 0 < D ∧ 0 < C ∧ ∀ᶠ L in 𝓝 K, ∀ N : ℕ, 0 < N →
      ‖unscaledFullCoefficient N L‖ ≤ D*hadamardEnvelope C N := by
  obtain ⟨r,ha⟩ := contourAnnulus_exists hK
  obtain ⟨M,hM,hlocal⟩ := local_inverse_dispersion_bound ha
  refine ⟨(2/(1-r))^2*contourKernelBound r,contourPairBound r*M,?_,?_,?_⟩
  · have hc := contourKernelBound_ge_one ha.1.le ha.2.1
    have hd : 0 < 1-r := by linarith [ha.2.1]
    positivity
  · have hc := contourKernelBound_ge_one ha.1.le ha.2.1
    unfold contourPairBound
    exact mul_pos (div_pos (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hc)) (sq_pos_of_pos ha.1)) hM
  · filter_upwards [hlocal,contourAnnulus_eventually ha,
      spectralSet_isClosed.isOpen_compl.mem_nhds hK] with L hL hLa hLc
    intro N hN
    exact fullCoefficient_hadamard_bound N hN hLa hLc hM.le hL

theorem p_analyticAt (K : Coupling) : AnalyticAt ℂ p K :=
  (Complex.analyticAt_sinh.comp analyticAt_fst).mul
    (Complex.analyticAt_sinh.comp analyticAt_snd)

theorem local_weighted_envelope (N k : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hk : ∀ n, k n ≤ N n)
    (hs : ∀ C : ℝ, 0 ≤ C → Summable (fun n => hadamardEnvelope C (N n)))
    {K : Coupling} (hK : K ∉ spectralSet) :
    ∃ U ∈ 𝓝 K, IsOpen U ∧ U ⊆ spectralSetᶜ ∧ ∃ M : ℕ → ℝ, Summable M ∧
      ∀ n L, L ∈ U → ‖p L^(k n)*unscaledFullCoefficient (N n) L‖ ≤ M n := by
  obtain ⟨D,C,hD,hC,he⟩ := local_fullCoefficient_envelope hK
  let P : ℝ := ‖p K‖+2
  have hP : 1 ≤ P := by dsimp [P]; linarith [norm_nonneg (p K)]
  have hp : ∀ᶠ L in 𝓝 K, ‖p L‖ ≤ P := by
    apply ((p_analyticAt K).continuousAt.norm.eventually_lt continuousAt_const _).mono
    · intro L hL; exact hL.le
    · dsimp [P]; linarith
  have hevent : ∀ᶠ L in 𝓝 K, L ∈ spectralSetᶜ ∧
      ∀ n, ‖p L^(k n)*unscaledFullCoefficient (N n) L‖ ≤ D*hadamardEnvelope (C*P) (N n) := by
    filter_upwards [he,hp,spectralSet_isClosed.isOpen_compl.mem_nhds hK] with L hL hp hLc
    exact ⟨hLc, fun n => weighted_envelope hD.le hC.le hP (hk n) hp (hL (N n) (hN n))⟩
  obtain ⟨U,hUsub,hU,hKU⟩ := mem_nhds_iff.mp hevent
  exact ⟨U,hU.mem_nhds hKU,hU,fun L hL => (hUsub hL).1,
    fun n => D*hadamardEnvelope (C*P) (N n),
    (hs (C*P) (by positivity)).mul_left D,fun n L hL => (hUsub hL).2 n⟩
end
end IsingBulk.Joint.FormFactors
