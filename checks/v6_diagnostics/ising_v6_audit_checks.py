#!/usr/bin/env python3
"""Reproducible spot checks for ising_audit_manuscript_v6.

Requires Python 3.10+, numpy, mpmath.
Run: python ising_v6_audit_checks.py --output ising_v6_audit_checks.json

These are floating-point diagnostics, NOT certified interval bounds and NOT a
proof of any infinite-N or boundary-uniform estimate.  The amplitude comparison
explicitly fixes the angular-sign and principal-power conventions; it does not
establish an error in either source.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import mpmath as mp
import numpy as np


def interior_root(w: np.ndarray) -> np.ndarray:
    """Select the quadratic root of smaller modulus at the sampled points."""
    w = np.asarray(w, dtype=np.complex128)
    a = w - np.sqrt(w * w - 1)
    b = w + np.sqrt(w * w - 1)
    return np.where(np.abs(a) <= np.abs(b), a, b)


def complete_pairs(y: np.ndarray, z: np.ndarray) -> np.ndarray:
    yi, yj = y[:, None], y[None, :]
    zi, zj = z[:, None], z[None, :]
    return -(yi - yj) ** 2 * zi * zj / (yi * yj * (1 - zi * zj) ** 2)


def normalization(s: float, r: float, n: int = 384) -> dict[str, Any]:
    """Compare T_2, the onsite coefficient, and constrained full-site C_2."""
    if s <= 1 or not 0 < r < 1 or n < 32:
        raise ValueError('Need s>1, 0<r<1, and n>=32.')
    th = (np.arange(n) + 0.317) * 2 * np.pi / n
    y = r * np.exp(1j * th)
    z = interior_root(s + 1 / s - (y + 1 / y) / 2)
    if np.max(np.abs(z)) >= r:
        raise ValueError('The selected radius does not satisfy |z|<r.')
    residue = 2 * z * z / (1 - z * z)
    yp, zp = y[:, None] * y[None, :], z[:, None] * z[None, :]
    off = 0.5 * np.mean(
        (1 / zp + 1 / yp) / ((1 - zp) * (1 - yp))
        * complete_pairs(y, z)
        * (residue * y)[:, None] * (residue * y)[None, :]
    )
    # Independent unconstrained angular onsite formula.
    y = np.exp(1j * th)
    z = interior_root(s + 1 / s - (y + 1 / y) / 2)
    sinh_gamma = (1 / z - z) / 2
    onsite = 0.5 * np.mean(
        complete_pairs(y, z) / sinh_gamma[:, None] / sinh_gamma[None, :]
    )
    # Full-site formula imposes theta_2 = -theta_1.
    pp = -(y - 1 / y) ** 2 * z * z / (1 - z * z) ** 2
    full = 0.5 * np.mean(pp / sinh_gamma ** 2 * (1 + z * z) / (1 - z * z))
    return dict(s=s, r=r, grid=n, T2_real=float(off.real),
                T2_imag=float(off.imag), f00_real=float(onsite.real),
                Cstd_real=float(full.real),
                identity_residual=float(abs(full - onsite - 2 * off)))


def prime_family(pmax: int = 61) -> dict[str, Any]:
    """Finite floating-point search; the exact arithmetic proof is separate."""
    primes = [p for p in range(11, pmax + 1)
              if all(p % q for q in range(2, int(p ** 0.5) + 1))]
    count, failures, tol = 0, [], 2e-12
    for p in primes:
        for a in range(1, (p - 1) // 4 + 1):
            for b in range(a + 1, (p - 1) // 4 + 1):
                sstar_sum = np.cos(2 * np.pi * a / p) + np.cos(2 * np.pi * b / p)
                n0, hits = 2 * p, []
                for n in range(2, n0 + 1, 2):
                    cc = np.cos(2 * np.pi * np.arange(n // 2 + 1) / n)
                    wh = np.argwhere(np.abs(cc[:, None] + cc[None, :] - sstar_sum) < tol)
                    if len(wh):
                        hits.append((n, wh))
                if not hits or hits[0][0] != n0:
                    failures.append([p, a, b, 'first order'])
                cc = np.cos(2 * np.pi * np.arange(n0 // 2 + 1) / n0)
                if hits and hits[-1][0] == n0:
                    uniq = {tuple(sorted((round(float(cc[i]), 10), round(float(cc[j]), 10))))
                            for i, j in hits[-1][1]}
                    if len(uniq) != 1:
                        failures.append([p, a, b, 'cosine-pair uniqueness'])
                else:
                    failures.append([p, a, b, 'no hit at 2p'])
                count += 1
    return dict(families=count, pmax=pmax, failures=failures, tolerance=tol)


def branch_field_checks(p: int = 11, a: int = 1, b: int = 2) -> dict[str, Any]:
    """Test the selected-pair field with N=N0+2 and near-branch samples."""
    alpha, beta = 2 * np.pi * a / p, 2 * np.pi * b / p
    ss = np.cos(alpha) + np.cos(beta)
    theta, theta_b = np.arccos(ss / 2), np.arccos(ss - 1)
    star, n = np.exp(1j * theta), 2 * p + 2
    c0, logs = 0.1 * np.sin(theta), []
    for eps in (1e-4, 1e-7, 1e-10):
        s = (1 + eps) * star
        sp = 1 - 1 / s ** 2
        u = np.linspace(-1e-3, 2e-3, n)
        u[n // 2 - 1:n // 2 + 1] = [-0.5 * eps, eps]
        y = np.exp(-c0 * eps + 1j * (-theta_b + u))
        w = s + 1 / s - (y + 1 / y) / 2
        z = interior_root(w)
        sin_phi = (1 / z - z) / (2j)
        wu = -0.5j * (y - 1 / y)
        ai, bi, phi_s = sp / wu, -wu / sin_phi, -sp / sin_phi
        aa, ip, iq = np.sum(ai), 0, n - 1
        v = ai.copy()
        v[ip] += aa * bi[iq] / (bi[ip] - bi[iq])
        v[iq] -= aa * bi[ip] / (bi[ip] - bi[iq])
        residual = phi_s - bi * v
        nonselected = np.delete(residual, [ip, iq])
        denom = max(1.0, float(np.sum(np.abs(phi_s))), float(np.sum(np.abs(bi * v))))
        logs.append(dict(eps=eps, sum_V=float(abs(np.sum(v))),
                         Z_freeze_absolute=float(abs(np.sum(phi_s) - np.sum(bi * v))),
                         Z_freeze_scaled=float(abs(np.sum(phi_s) - np.sum(bi * v))) / denom,
                         max_unselected_residual=float(np.max(abs(nonselected))),
                         B_pair_sum=float(abs(residual[ip] + residual[iq]))))
    return dict(parameters=dict(p=p, a=a, b=b, N=n, theta=float(theta),
                                thetaB=float(theta_b), Sstar=float(ss)), tests=logs)


def amplitude_convention_checks() -> list[dict[str, Any]]:
    """Compare the manuscript's one-chart coefficient with review eq. (69).

    Gaussian Vandermonde identity evaluates C_N; all noninteger powers use
    mpmath principal powers. Both signs of the review's theta are recorded.
    The expected ratios are -i for +theta and 1 for -theta (even N).
    """
    mp.mp.dps = 90
    records = []
    for p in (11, 13, 17):
        n = 2 * p
        alpha, beta = 2 * mp.pi / p, 4 * mp.pi / p
        ss = mp.cos(alpha) + mp.cos(beta)
        theta = mp.acos(ss / 2)
        a0, k = (mp.mpf(n) ** 2 - 1) / 2, n * n // 2 - 1
        nu = a0 - 1
        q = 2 * n * mp.sin(theta) / mp.sin(beta)
        d = ss * (1 - mp.cos(alpha) * mp.cos(beta)) / (2 * mp.sin(beta) ** 3)
        kk = (2 / mp.factorial(n) * mp.power(2, -n * (n - 1))
              * mp.power(2 * mp.pi, -n) * mp.sin(beta) ** (-n * n))
        cn = ((2 * mp.pi) ** ((mp.mpf(n) - 1) / 2)
              * mp.fprod(mp.factorial(j) for j in range(1, n + 1))
              / (mp.sqrt(n) * 2 ** (a0 - 1) * mp.gamma(a0)))
        chart = mp.pi ** 2 * kk * cn * ((-1) ** k) * q ** nu * mp.power(-1j * d, -a0)
        geom = mp.sin(alpha) ** 2 * mp.cos(beta) + mp.sin(beta) ** 2 * mp.cos(alpha)
        common = (mp.fprod(mp.factorial(j) / 2 ** j for j in range(1, n))
                  / (geom ** a0 * mp.pi ** ((mp.mpf(n) - 3) / 2)
                     * mp.sqrt(n) * mp.gamma(a0)))
        positive = mp.power(n * 1j * mp.sin(theta), nu) * common
        negative = mp.power(-n * 1j * mp.sin(theta), nu) * common
        records.append(dict(p=p, N=n, ratio_review_positive_theta=mp.nstr(chart / positive, 40),
                            ratio_review_negative_theta=mp.nstr(chart / negative, 40),
                            positive_theta_residual_from_minus_i=mp.nstr(abs(chart / positive + 1j), 12),
                            negative_theta_residual_from_one=mp.nstr(abs(chart / negative - 1), 12)))
    return records


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('ising_v6_audit_checks.json'))
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    hashes = {}
    for name in ('ising_audit_manuscript_v6.tex', 'ising_audit_manuscript_v6.pdf'):
        path = base / name
        if path.is_file():
            hashes[name] = hashlib.sha256(path.read_bytes()).hexdigest()
    out = dict(
        scope='Floating-point spot checks only; no certified error or infinite-tail claim.',
        source_sha256=hashes,
        normalization=[normalization(s, r) for s, r in ((1.5, .9), (2., .8), (4., .75))],
        arithmetic=prime_family(),
        two_phase_field=branch_field_checks(),
        amplitude_conventions=amplitude_convention_checks(),
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(f'Wrote {args.output.resolve()}')


if __name__ == '__main__':
    main()
