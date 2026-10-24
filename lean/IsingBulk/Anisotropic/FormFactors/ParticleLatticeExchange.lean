import IsingBulk.Anisotropic.FormFactors.PhysicalLatticeSum
import IsingBulk.Anisotropic.FormFactors.LatticeNorm
import IsingBulk.Anisotropic.FormFactors.NormalConvergence

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.HT.Contour Filter
open scoped Topology

theorem physical_lattice_norm_envelope {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : realProduct lam x ≠ 1) :
    ∃ D C : ℝ, 0 ≤ D ∧ 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      (∑' v : LatticeSite, ‖latticeCoefficient N (realB lam x) (realC lam x) v‖) ≤
        D*hadamardEnvelope C N := by
  obtain ⟨r,hr,hr1,hm⟩ := physical_margin_radius (realB_pos hlam hx).le (real_dispersion_gap hlam hx hp)
  have ha := physical_margin_contourAnnulus hlam hx hr hr1 hm
  obtain ⟨M,hM,hlocal⟩ := local_inverse_dispersion_bound ha
  have hDz := hlocal.self_of_nhds
  let t := Real.sqrt (realProduct lam x)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hC := contourKernelBound_ge_one hr.le hr1
  have hK : 0 ≤ contourPairBound r := by unfold contourPairBound; positivity
  refine ⟨(2/(1-r))^2*contourKernelBound r,contourPairBound r*M*t,by positivity,by positivity,?_⟩
  intro N hN
  have hA (u v : Fin N → ℂ) (hu : ∀ i, ‖u i‖=r) (hv : ∀ i, ‖v i‖=r) :=
    circle_pairProduct_bound N hN hr hr1 u v hu hv
  have hsum := unscaledLatticeCoefficientAtRadius_norm_tsum_le N hN hr hr1 hM.le
    (by positivity : 0 ≤ contourKernelBound r*contourPairBound r^N*(N:ℝ)^(N-N/2)) hDz hA
  have hpow : r^N ≤ r := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    rw [pow_succ]
    exact mul_le_of_le_one_left hr.le (pow_le_one₀ hr.le hr1.le)
  have hratio : (1+r^N)/(1-r^N) ≤ 2/(1-r) := by
    apply div_le_div₀ (by norm_num) (by linarith) (by linarith) (by linarith)
  have hratio0 : 0 ≤ (1+r^N)/(1-r^N) := by
    apply div_nonneg (by positivity)
    linarith
  have hbound := hsum.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hratio0 hratio 2) (by positivity))
  have hpoint (v : LatticeSite) : ‖latticeCoefficient N (realB lam x) (realC lam x) v‖ =
      t^N*‖unscaledLatticeCoefficientAtRadius N r lam (x:ℂ) v‖ := by
    rw [physical_latticeCoefficient_eq_double_contour N hlam hx hp hr hr1 hm v,norm_mul]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg ht N)]
  simp_rw [hpoint]
  rw [tsum_mul_left]
  have hh := mul_le_mul_of_nonneg_left hbound (pow_nonneg ht N)
  convert hh using 1
  unfold hadamardEnvelope
  simp only [mul_pow]
  ring

/-- Joint absolute summability before interchanging particle number and
lattice site. The source is the literal angular coefficient at every site. -/
theorem selected_particle_lattice_norm_summable {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : realProduct lam x ≠ 1) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hs : ∀ C : ℝ, 0 ≤ C → Summable (fun n => hadamardEnvelope C (N n))) :
    Summable (fun p : ℕ × LatticeSite => ‖latticeCoefficient (N p.1) (realB lam x) (realC lam x) p.2‖) := by
  obtain ⟨D,C,hD,hC,hbound⟩ := physical_lattice_norm_envelope hlam hx hp
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  constructor
  · intro n
    exact (physical_lattice_summable_eq_full (N n) (hN n) hlam hx hp).1
  · exact ((hs C hC).mul_left D).of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
      (fun n => hbound (N n) (hN n))

set_option maxHeartbeats 1000000 in
theorem selected_particle_lattice_exchange {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : realProduct lam x ≠ 1) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hs : ∀ C : ℝ, 0 ≤ C → Summable (fun n => hadamardEnvelope C (N n))) :
    (∑' v : LatticeSite, ∑' n, latticeCoefficient (N n) (realB lam x) (realC lam x) v) =
      ∑' n, ((Real.sqrt (realProduct lam x))^(N n):ℝ)*unscaledFullCoefficient (N n) lam (x:ℂ) := by
  have habs := selected_particle_lattice_norm_summable hlam hx hp N hN hs
  calc
    _ = ∑' n, ∑' v : LatticeSite, latticeCoefficient (N n) (realB lam x) (realC lam x) v :=
      Summable.tsum_comm (f := fun n v => latticeCoefficient (N n) (realB lam x) (realC lam x) v) habs.of_norm
    _ = _ := by
      apply tsum_congr
      intro n
      exact (physical_lattice_summable_eq_full (N n) (hN n) hlam hx hp).2

end
end IsingBulk.Anisotropic.FormFactors
