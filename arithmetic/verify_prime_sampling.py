#!/usr/bin/env python3
"""Exact model checks and explicitly numerical prime-sampling diagnostics."""
import hashlib
import json
import math
from pathlib import Path
import sys

import mpmath as mp
import numpy as np
import sympy as sp

HERE = Path(__file__).resolve().parent


def sieve(limit):
    flags = np.ones(limit + 1, dtype=bool)
    flags[:2] = False
    for p in range(2, math.isqrt(limit) + 1):
        if flags[p]:
            flags[p * p::p] = False
    return np.flatnonzero(flags)


def exact_checks():
    c, s, r, z, y, a = sp.symbols('c s r z y a', real=True)
    radius2 = (r * s * c) ** 2 + (r * s ** 2) ** 2 + (r * c) ** 2
    assert sp.rem(sp.expand(radius2 - r ** 2), sp.Poly(c ** 2 + s ** 2 - 1, c, s, r)) == 0
    assert sp.expand(r ** 2 - r ** 2 * s ** 2 - r ** 2 * c ** 2 - r ** 2 * (1 - c ** 2 - s ** 2)) == 0
    assert sp.expand((2 * r - y) ** 2 - (y ** 2 + 4 * z ** 2)) == 4 * (r ** 2 - r * y - z ** 2)
    t = sp.symbols('t', real=True)
    assert sp.trigsimp((sp.cos(2 * t) - 1) ** 2 + sp.sin(2 * t) ** 2 - 4 * sp.sin(t) ** 2) == 0
    assert sp.cancel(s ** 2 * (1 / (2 * s)) ** 2) == sp.Rational(1, 4)
    gradient_norm2 = 1 - a ** 2 + (1 + a) ** 2 / 4
    assert sp.expand(gradient_norm2 - (sp.Rational(4, 3) - sp.Rational(3, 4) * (a - sp.Rational(1, 3)) ** 2)) == 0
    eps = sp.symbols('eps', positive=True)
    cdf = 2 / sp.pi * sp.asin(sp.sqrt(eps))
    assert sp.simplify(sp.diff(cdf, eps) - 1 / (sp.pi * sp.sqrt(eps * (1 - eps)))) == 0
    assert sp.limit(cdf / sp.sqrt(eps), eps, 0, dir='+') == 2 / sp.pi
    threshold = sp.symbols('T', positive=True)
    tail = 2 / sp.pi * sp.asin(1 / (2 * threshold))
    assert sp.limit(threshold * tail, threshold, sp.oo) == 1 / sp.pi
    delta = sp.symbols('delta', positive=True)
    line_mass = 2 / sp.pi * sp.asin(delta / sp.sqrt(2))
    assert sp.limit(line_mass / delta, delta, 0, dir='+') == sp.sqrt(2) / sp.pi
    return 10


def phase_discrepancy(values):
    phases = np.sort(np.remainder(values / (2 * np.pi), 1.0))
    n = len(phases)
    right = np.arange(1, n + 1) / n
    left = np.arange(n) / n
    return float(max(np.max(right - phases), np.max(phases - left)))


def diagnostics(values, label, cutoff):
    values = values.astype(float)
    sn, cs = np.sin(values), np.cos(values)
    height = sn ** 2
    cost = 1 / (2 * np.abs(sn))
    star = phase_discrepancy(values)
    levels = [0.0001, 0.001, 0.01, 0.1, 0.25, 0.5, 0.9]
    fold = []
    for eps in levels:
        observed = float(np.mean(height <= eps))
        expected = 2 / np.pi * np.arcsin(np.sqrt(eps))
        assert abs(observed - expected) <= 4 * star + 1e-11
        fold.append({'epsilon': eps, 'observed': observed, 'limiting_mass': float(expected), 'error': float(observed - expected)})
    tube = []
    for delta in [0.01, 0.05, 0.1, 0.25]:
        observed = float(np.mean(np.sqrt(2) * np.abs(cs) <= delta))
        expected = 2 / np.pi * np.arcsin(delta / np.sqrt(2))
        assert abs(observed - expected) <= 4 * star + 1e-11
        tube.append({'delta': delta, 'observed': observed, 'limiting_mass': float(expected)})
    tails = []
    for threshold in [1, 2, 10, 100]:
        observed = float(np.mean(cost > threshold))
        expected = 2 / np.pi * np.arcsin(1 / (2 * threshold))
        assert abs(observed - expected) <= 4 * star + 1e-11
        tails.append({'threshold': threshold, 'observed': observed, 'limiting_tail': float(expected)})
    rec = (values * height + np.hypot(values * height, 2 * values * cs)) / 2
    max_recovery_error = float(np.max(np.abs(rec - values)))
    assert max_recovery_error < 1e-8
    assert np.max(np.abs(height * cost ** 2 - 0.25)) < 1e-14
    nearest = np.rint(values / np.pi)
    distance = np.abs(values / np.pi - nearest)
    rate = []
    for epsilon in [0.01, 0.05, 0.1]:
        tau = 1 / 3 - epsilon
        witness = distance < values ** (-tau)
        assert np.all(height[witness] < np.pi ** 2 * values[witness] ** (-2 * tau) + 1e-10)
        rate.append({'epsilon': epsilon, 'tau': tau, 'finite_witnesses': int(witness.sum())})
    return {
        'sample': label, 'cutoff': cutoff, 'sample_size': len(values),
        'numerical_star_discrepancy': star, 'fold_cdf': fold, 'double_line_tubes': tube,
        'filling_tail': tails, 'empirical_cost_mean': float(cost.mean()),
        'truncated_cost_means': {str(m): float(np.minimum(cost, m).mean()) for m in [2, 10, 100]},
        'max_radius_recovery_error': max_recovery_error,
        'finite_diophantine_witnesses': rate,
        'smallest_fold_height_index': int(values[np.argmin(height)]),
        'smallest_fold_height': float(height.min()),
    }


def high_precision(primes):
    mp.mp.dps = 80
    sn = np.sin(primes.astype(float))
    selected = set(map(int, primes[np.argsort(np.abs(sn))[:12]]))
    selected.update(map(int, primes[np.argsort(np.abs(np.cos(primes.astype(float))))[:12]]))
    selected.update([2, 3, 5, 7, int(primes[-1])])
    rows = []
    for p in sorted(selected):
        assert p >= 2 and all(p % d for d in range(2, math.isqrt(p) + 1))
        t = mp.mpf(p)
        s, c = mp.sin(t), mp.cos(t)
        y, z = t * s ** 2, t * c
        recovered = (y + mp.sqrt(y ** 2 + 4 * z ** 2)) / 2
        holonomy = mp.exp(2j * t) - 1
        cost = 1 / abs(holonomy)
        assert abs(recovered - t) < mp.mpf('1e-70')
        assert abs(abs(holonomy) - 2 * abs(s)) < mp.mpf('1e-70')
        assert abs(s ** 2 * cost ** 2 - mp.mpf('0.25')) < mp.mpf('1e-65')
        assert s != 0 and c != 0
        rows.append({'prime': p, 'fold_height_80dps': mp.nstr(s ** 2, 35),
                     'filling_cost_80dps': mp.nstr(cost, 35),
                     'radius_error_80dps': mp.nstr(abs(recovered - t), 5)})
    return rows


def main():
    if not __debug__ or sys.flags.optimize or sys.argv[1:]:
        raise RuntimeError('Run without -O and without arguments.')
    assert sys.version_info[:3] == (3, 14, 6), sys.version
    assert (np.__version__, sp.__version__, mp.__version__) == ('2.5.2', '1.14.0', '1.3.0')
    count = exact_checks()
    primes = sieve(1_000_000)
    assert len(primes) == 78_498 and primes[-1] == 999_983
    small = set(map(int, primes[primes <= 10_000]))
    for n in range(10_001):
        trial = n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))
        assert (n in small) == trial
    records = []
    for cutoff in [10_000, 100_000, 1_000_000]:
        subset = primes[primes <= cutoff]
        records.append(diagnostics(subset, 'primes', cutoff))
        records.append(diagnostics(np.arange(1, cutoff + 1), 'all_positive_integers_control', cutoff))
    high = high_precision(primes)
    result = {
        'scope': 'Exact symbolic model checks and numerical diagnostics; not a proof of prime equidistribution or infinite prime approximation.',
        'environment': {'python': sys.version, 'numpy': np.__version__, 'sympy': sp.__version__, 'mpmath': mp.__version__},
        'exact_symbolic_checks': count, 'independent_trial_division_checks': 10_001,
        'exact_sieve_cutoff': 1_000_000, 'exact_prime_count': len(primes),
        'diagnostics': records, 'high_precision_rows': high,
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    output = HERE / 'evidence' / 'NUMERICAL_RESULTS_FINAL.json'
    if output.exists():
        assert json.loads(output.read_text()) == result, 'Replay differs from the frozen result.'
    else:
        output.write_text(json.dumps(result, indent=2) + '\n')
    print(f'PASS: {count} exact symbolic identities, 10001 trial-division cross-checks, 78498 primes, {len(high)} high-precision diagnostics.')
    for row in records:
        value = next(x for x in row['fold_cdf'] if x['epsilon'] == 0.01)
        print(row['sample'], row['cutoff'], 'F(0.01)=', value['observed'], 'limit=', value['limiting_mass'], 'D*=', row['numerical_star_discrepancy'])


if __name__ == '__main__':
    main()
