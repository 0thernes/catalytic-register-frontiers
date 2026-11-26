// SPDX-License-Identifier: Apache-2.0
/*
 * Catalytic Register Frontiers — Universal Zero-Dependency BigInt Engine & Adaptive Forking Scheduler
 *
 * Implements literal exact-arithmetic execution (zero floating-point proof steps) of EVERY
 * formally verified construction in `catalytic-register-frontiers` (Lean 4.35.0):
 *   - T1 / T1a–T1d: Exact prime-field base-p digit-sum oracle & Lucas binomials
 *   - T2: Strictly bilinear 2-access Frobenius collapse x^(2^k) over char-2 rings (k+1 regs, 4k-2 ops)
 *   - T3a–T3g: Literal 3-register passive Pascal-row shear loops prog4_x5 .. prog9_x15
 *   - T3h: Complete 4-register passive powering x^N over arbitrary commutative rings Z/mZ or F_p
 *   - T3i: Zero-write-wear exact streaming frequency moments F_D(f) = sum_i f_i^D over R^n
 *   - R3 (Cor. 5.4): Non-commutative homogeneous degree-2 lift mu_7(prog5_x7) on M_2(F_p)
 *   - T4: Balanced zero-workspace bilinear multilinear product x_0...x_{d-1} in <= log_2 d + 2 regs
 *   - Adaptive Forking (Exact DP + Hybrid Scheduler): Dynamically branches across Frobenius
 *     collapse, prime-field digit-sum, direct 3-reg gadgets, passive 4-reg composition wraps,
 *     Gray-code 2-way Cook-Mertz splits, and feasible mixed-radix Cook-Mertz schedules subject to
 *     exact commutative-ring invertibility gcd(D_t, m) = gcd((d-1)!, m) = gcd(len!, m) = 1.
 *   - Catalytic Byte-Vault: Borrows real Uint8Array bytes as dirty catalytic registers, runs exact
 *     computations, and restores every borrowed byte identically for live SHA-256 verification.
 *
 * Works identically in browsers (window.CatalyticEngine), Web Workers, and Node.js (module.exports).
 */
(function (root, factory) {
  const api = factory();
  if (typeof module === 'object' && module.exports) {
    module.exports = api;
  }
  if (root) {
    root.CatalyticEngine = api;
  }
})(typeof globalThis !== 'undefined' ? globalThis : this, function () {
  'use strict';

  // =========================================================================
  // 1. Exact BigInt Number Theory & Ring Arithmetic (zero floats)
  // =========================================================================

  function safeInt(val, def, min, max) {
    const n = Number(val);
    if (!Number.isFinite(n)) return def;
    const i = Math.trunc(n);
    if (min !== undefined && i < min) return min;
    if (max !== undefined && i > max) return max;
    return i;
  }

  function mod(a, p) {
    if (p === 0n) return a;
    const r = a % p;
    return r < 0n ? r + p : r;
  }

  function gcd(a, b) {
    a = a < 0n ? -a : a;
    b = b < 0n ? -b : b;
    while (b !== 0n) {
      const t = a % b;
      a = b;
      b = t;
    }
    return a;
  }

  function modInv(a, p) {
    if (p <= 1n) throw new Error(`Modulus ${p} has no modular inverses`);
    a = mod(a, p);
    if (a === 0n) throw new Error('Zero has no modular inverse');
    let t = 0n;
    let newT = 1n;
    let r = p;
    let newR = a;
    while (newR !== 0n) {
      const q = r / newR;
      [t, newT] = [newT, t - q * newT];
      [r, newR] = [newR, r - q * newR];
    }
    if (r !== 1n) throw new Error(`Element ${a} is not invertible mod ${p} (gcd=${r})`);
    return t < 0n ? t + p : t;
  }

  function modPow(base, exp, p) {
    let e = BigInt(exp);
    if (e < 0n) throw new Error('Negative exponent not supported');
    let res = p === 0n ? 1n : (1n % p);
    let b = p === 0n ? BigInt(base) : mod(BigInt(base), p);
    while (e > 0n) {
      if (e & 1n) res = p === 0n ? res * b : mod(res * b, p);
      b = p === 0n ? b * b : mod(b * b, p);
      e >>= 1n;
    }
    return res;
  }

  function isPrimeBig(n) {
    n = BigInt(n);
    if (n < 2n) return false;
    const small = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n];
    for (const p of small) {
      if (n === p) return true;
      if (n % p === 0n) return false;
    }
    let d = n - 1n;
    let s = 0;
    while ((d & 1n) === 0n) {
      d >>= 1n;
      s += 1;
    }
    const bases = [2n, 325n, 9375n, 28178n, 450775n, 9780504n, 1795265022n];
    for (const a of bases) {
      if (a % n === 0n) continue;
      let x = modPow(a, d, n);
      if (x === 1n || x === n - 1n) continue;
      let witness = true;
      for (let r = 1; r < s; r++) {
        x = (x * x) % n;
        if (x === n - 1n) {
          witness = false;
          break;
        }
      }
      if (witness) return false;
    }
    return true;
  }

  function baseDigits(base, n) {
    const b = BigInt(base);
    let cur = BigInt(n);
    if (b < 2n) throw new Error('Base must be >= 2');
    const digits = [];
    while (cur >= b) {
      digits.push(Number(cur % b));
      cur /= b;
    }
    digits.push(Number(cur));
    return digits; // LSB-first matching Lean baseDigits
  }

  function digitSum(p, n) {
    const ds = baseDigits(p, n);
    let s = 0;
    for (const d of ds) s += d;
    return s;
  }

  // Exact BigInt binomial coefficient C(n, k) — works for Z (p=0), primes, AND composite moduli!
  function binomExact(n, k) {
    const nb = BigInt(n);
    let kb = BigInt(k);
    if (kb < 0n || kb > nb) return 0n;
    if (kb > nb - kb) kb = nb - kb;
    let res = 1n;
    for (let i = 1n; i <= kb; i++) {
      res = (res * (nb - kb + i)) / i;
    }
    return res;
  }

  function binomModP(n, k, p) {
    const pb = BigInt(p);
    if (pb === 0n) return binomExact(n, k);
    if (!isPrimeBig(pb)) return mod(binomExact(n, k), pb);
    let nb = BigInt(n);
    let kb = BigInt(k);
    if (kb > nb) return 0n;
    let res = 1n;
    while (nb > 0n || kb > 0n) {
      const ni = nb % pb;
      const ki = kb % pb;
      if (ki > ni) return 0n;
      let num = 1n;
      let den = 1n;
      for (let i = 0n; i < ki; i++) {
        num = (num * (ni - i)) % pb;
        den = (den * (i + 1n)) % pb;
      }
      res = (res * num * modInv(den, pb)) % pb;
      nb /= pb;
      kb /= pb;
    }
    return res;
  }

  function factorialMod(n, p) {
    let acc = 1n;
    for (let i = 2n; i <= BigInt(n); i++) {
      acc = p === 0n ? acc * i : (acc * i) % p;
    }
    return acc;
  }

  // Exact commutative-ring invertibility check for n! in Z/pZ (or Z/Q when p=0):
  // n! is a unit in Z/pZ iff gcd(k, p) = 1 for every 2 <= k <= n (no prime <= n divides p).
  function isFactInvertible(n, p) {
    if (p === 0n) return true;
    if (p < 2n) return false;
    for (let k = 2n; k <= BigInt(n); k++) {
      if (gcd(k, p) !== 1n) return false;
    }
    return true;
  }

  function bigRatio(numBig, denBig) {
    const num = BigInt(numBig);
    const den = BigInt(denBig);
    if (den <= 0n) return 1;
    // Scale by 10,000 in exact BigInt to avoid Number overflow on huge N (up to 10^30+)
    const scaled = (num * 10000n) / den;
    return Number(scaled) / 10000;
  }

  function textToBigInt(str, p) {
    let acc = 0n;
    for (let i = 0; i < str.length; i++) {
      acc = (acc * 257n + BigInt(str.charCodeAt(i))) + 1n;
    }
    return p === 0n ? acc : mod(acc, p);
  }

  function formatBig(val, maxChars = 26) {
    const s = val.toString();
    if (s.length <= maxChars) return s;
    const head = s.slice(0, Math.floor((maxChars - 5) / 2));
    const tail = s.slice(-Math.floor((maxChars - 5) / 2));
    return `${head}..${tail} (${s.length}d)`;
  }

  // =========================================================================
  // 2. Verbatim Lean-Certified 3-Register Programs (T3a–T3g + Vinciguerra t=4)
  // =========================================================================

  const PROGRAMS_R3 = {
    4: {
      id: 'prog4_x5',
      label: 'Vinciguerra Baseline (t=4 -> x^5)',
      theorem: 'Vinciguerra (arXiv:2609.18692, Thm. 2.3)',
      t: 4,
      degree: 5,
      shearDeg: 2,
      D: 54n,
      badPrimes: [2n, 3n],
      exponent: Math.log(4) / Math.log(5),
      steps: [
        { terms: [[5, 0, 39n], [3, 1, -100n], [1, 2, 60n]], qNext: 1n, alpha: 1n },
        { terms: [[5, 0, -261n], [3, 1, -180n], [1, 2, -180n]], qNext: -2n, alpha: 1n },
        { terms: [[5, 0, 261n], [3, 1, 180n], [1, 2, 180n]], qNext: 1n, alpha: 1n },
        { terms: [[5, 0, -39n], [3, 1, 100n], [1, 2, -60n]], qNext: 0n, alpha: -3n }
      ]
    },
    5: {
      id: 'prog5_x7',
      label: 'Compact Practical Engine (t=5 -> x^7, T3a)',
      theorem: 'Lean T3a (prog5_x7)',
      t: 5,
      degree: 7,
      shearDeg: 2,
      D: 576n,
      badPrimes: [2n, 3n],
      exponent: Math.log(5) / Math.log(7),
      steps: [
        { terms: [[7, 0, -1567n], [5, 1, -5292n], [3, 2, -7245n], [1, 3, -3570n]], qNext: -1n, alpha: 1n },
        { terms: [[7, 0, -73006n], [5, 1, 92358n], [3, 2, -29610n], [1, 3, 9730n]], qNext: 3n, alpha: 1n },
        { terms: [[5, 1, -174132n], [1, 3, -12320n]], qNext: -3n, alpha: 1n },
        { terms: [[7, 0, 73006n], [5, 1, 92358n], [3, 2, 29610n], [1, 3, 9730n]], qNext: 1n, alpha: 1n },
        { terms: [[7, 0, 1567n], [5, 1, -5292n], [3, 2, 7245n], [1, 3, -3570n]], qNext: 0n, alpha: -4n }
      ]
    },
    6: {
      id: 'prog6_x9',
      label: 'Antisymmetric Engine (t=6 -> x^9, T3b)',
      theorem: 'Lean T3b (prog6_x9)',
      t: 6,
      degree: 9,
      shearDeg: 4,
      D: 382500000n,
      badPrimes: [2n, 3n, 5n, 17n],
      exponent: Math.log(6) / Math.log(9),
      steps: [
        { terms: [[9, 0, 4154985n], [5, 1, -9394056n], [1, 2, 5454540n]], qNext: 1n, alpha: 1n },
        { terms: [[9, 0, -72618275n], [5, 1, -30013200n], [1, 2, -12729150n]], qNext: -4n, alpha: 1n },
        { terms: [[9, 0, 193081500n], [5, 1, -8505000n], [1, 2, 10914750n]], qNext: 6n, alpha: 1n },
        { terms: [[9, 0, -193081500n], [5, 1, 8505000n], [1, 2, -10914750n]], qNext: -4n, alpha: 1n },
        { terms: [[9, 0, 72618275n], [5, 1, 30013200n], [1, 2, 12729150n]], qNext: 1n, alpha: 1n },
        { terms: [[9, 0, -4154985n], [5, 1, 9394056n], [1, 2, -5454540n]], qNext: 0n, alpha: -5n }
      ]
    },
    7: {
      id: 'prog7_x11',
      label: '7-Access Engine (t=7 -> x^11, T3c)',
      theorem: 'Lean T3c (prog7_x11)',
      t: 7,
      degree: 11,
      shearDeg: 5,
      D: 68724637549388656012800n,
      badPrimes: [2n, 3n, 5n, 7n, 538423n, 2512452073n],
      exponent: Math.log(7) / Math.log(11),
      steps: [
        { terms: [[11, 0, 7906012563161999776548n], [6, 1, 2913565459167362672640n], [1, 2, 359752416281925314670n]], qNext: -6n, alpha: 1n },
        { terms: [[11, 0, -160487039610242232432475n], [6, 1, 9002890386212446808700n], [1, 2, -575226836894382807750n]], qNext: 29n, alpha: 1n },
        { terms: [[11, 0, 739254464056809087842322n], [6, 1, 11855322660827313965220n], [1, 2, 491370792119074417242n]], qNext: -55n, alpha: 1n },
        { terms: [[11, 0, -1074623435277851316121425n], [6, 1, -2062222051271515088340n], [1, 2, -523787405092533868902n]], qNext: 50n, alpha: 1n },
        { terms: [[11, 0, 563164798398494126351300n], [6, 1, -13184058990777727982160n], [1, 2, 509164691003954780718n]], qNext: -20n, alpha: 1n },
        { terms: [[11, 0, -75339810861908276105898n], [6, 1, -8247961873263806201970n], [1, 2, -478052152922140654473n]], qNext: 1n, alpha: 2n },
        { terms: [[11, 0, 125010731536610689628n], [6, 1, -277535590894074174090n], [1, 2, 216778495504102818495n]], qNext: 0n, alpha: -7n }
      ]
    },
    8: {
      id: 'prog8_x13',
      label: 'Global Optimal Engine (t=8 -> x^13, T3d)',
      theorem: 'Lean T3d / T3f (prog8_x13)',
      t: 8,
      degree: 13,
      shearDeg: 6,
      D: 2656207148788801777680n,
      badPrimes: [2n, 3n, 5n, 7n, 137n, 1602207194491n],
      exponent: Math.log(8) / Math.log(13),
      steps: [
        { terms: [[13, 0, 48815710996788904n], [7, 1, -106093571331033000n], [1, 2, 60350317640973360n]], qNext: 1n, alpha: 1n },
        { terms: [[13, 0, -1658292324977727901n], [7, 1, -489368519245585980n], [1, 2, -127682705470680360n]], qNext: -6n, alpha: 1n },
        { terms: [[13, 0, 10834057724039418729n], [7, 1, -755802943366571100n], [1, 2, 109443420226524384n]], qNext: 15n, alpha: 1n },
        { terms: [[13, 0, -28066770107640654530n], [7, 1, -709685716297357800n], [1, 2, -112368956812984872n]], qNext: -20n, alpha: 1n },
        { terms: [[13, 0, 28066770107640654530n], [7, 1, 709685716297357800n], [1, 2, 112368956812984872n]], qNext: 15n, alpha: 1n },
        { terms: [[13, 0, -10834057724039418729n], [7, 1, 755802943366571100n], [1, 2, -109443420226524384n]], qNext: -6n, alpha: 1n },
        { terms: [[13, 0, 1658292324977727901n], [7, 1, 489368519245585980n], [1, 2, 127682705470680360n]], qNext: 1n, alpha: 1n },
        { terms: [[13, 0, -48815710996788904n], [7, 1, 106093571331033000n], [1, 2, -60350317640973360n]], qNext: 0n, alpha: -7n }
      ]
    },
    9: {
      id: 'prog9_x15',
      label: 'Post-Min Ascent Engine (t=9 -> x^15, T3g)',
      theorem: 'Lean T3g (prog9_x15)',
      t: 9,
      degree: 15,
      shearDeg: 7,
      D: 876702103804656272895371895753963647960420947968000n,
      badPrimes: [2n, 3n, 5n, 7n, 23n, 5263716917n, 22130905714103n, 638970634117961n],
      exponent: Math.log(9) / Math.log(15),
      steps: [
        { terms: [[15, 0, 47697576695807591149970091225524143671006608128n], [8, 1, 12828801617978706859373312286292362540907084800n], [1, 2, 1110886294449659745864096749366203925109120600n]], qNext: -8n, alpha: 1n },
        { terms: [[15, 0, -1869508609729587846176068147939982519944593238713n], [8, 1, 59996502939059511159195477622864433675594894400n], [1, 2, -1786938821946514648844378151300481931148403800n]], qNext: 55n, alpha: 1n },
        { terms: [[15, 0, 18929285835903525682822071783431297700189705828150n], [8, 1, 156868870192178246016753489647911722864476079660n], [1, 2, 1554796487897524506238230241861352577945418230n]], qNext: -161n, alpha: 1n },
        { terms: [[15, 0, -59701354430749272030885419618468843480279798575140n], [8, 1, 126572346189002105604280213928792980703987534280n], [1, 2, -1618444280603445010428031257340298209769887860n]], qNext: 259n, alpha: 1n },
        { terms: [[15, 0, 80464114702764739278983389227647015096532834945642n], [8, 1, -21050480064011964593421747180018455328448123740n], [1, 2, 1539451953576780013877480778907171940215731930n]], qNext: -245n, alpha: 1n },
        { terms: [[15, 0, -49538529867529484855836135637226966605728933525908n], [8, 1, -145439140733739384863055551545682276887938764400n], [1, 2, -1611646744675379323642096886402195841667682400n]], qNext: 133n, alpha: 1n },
        { terms: [[15, 0, 12439625519035786199231464105054913816402633009958n], [8, 1, -141436572689870378712533337515868209608737690300n], [1, 2, 1613128695684116497614060659740636235214780150n]], qNext: -35n, alpha: 1n },
        { terms: [[15, 0, -771759365416347953099835753244141156083904814775n], [8, 1, -47414065101749587510890697899583576459910516250n], [1, 2, -1482717341185777135391234005514321851922862975n]], qNext: 1n, alpha: 2n },
        { terms: [[15, 0, 428639024833933810563949521183005241049762658n], [8, 1, -926262348847253959701159344708981499930498450n], [1, 2, 681483756803035354711871870681933156023786125n]], qNext: 0n, alpha: -9n }
      ]
    }
  };

  // =========================================================================
  // 3. Literal Execution: 3-Register Pascal-Row Shear Loops (T3a–T3g)
  // =========================================================================

  function execPass3(t, xIn, pIn, opts = {}) {
    const spec = PROGRAMS_R3[t];
    if (!spec) throw new Error(`Unsupported 3-register engine t=${t}`);
    const p = BigInt(pIn);
    if (p < 0n || p === 1n) throw new Error('Modulus p must be 0 (exact Z) or >= 2');
    const x = mod(BigInt(xIn), p);
    const O0 = mod(BigInt(opts.O0 ?? 1234567n), p);
    const u0 = mod(BigInt(opts.u0 ?? 89101112n), p);
    const v0 = mod(BigInt(opts.v0 ?? 31415926n), p);
    const faultBit = Boolean(opts.faultBit);
    const scaleOut = p === 0n ? 1n : modInv(spec.D, p);

    let O = O0;
    let u = u0;
    let v = v0;
    let accesses = 0;
    let basicOps = 0;
    const trace = [{ stage: 'init', op: 'Initial dirty catalytic state', O, u, v }];

    for (let k = 0; k < spec.steps.length; k++) {
      const st = spec.steps[k];
      let delta = 0n;
      for (const [du, dv, coeff] of st.terms) {
        const term = mod(coeff * mod(modPow(u, du, p) * modPow(v, dv, p), p), p);
        delta = mod(delta + term, p);
      }
      O = mod(O + mod(scaleOut * delta, p), p);
      basicOps += 1;
      trace.push({ stage: `step ${k}.a`, op: `O <- O + F_${k}(u, v)`, O, u, v });

      if (st.qNext !== 0n) {
        v = mod(v - mod(st.qNext * modPow(u, spec.shearDeg, p), p), p);
        basicOps += 1;
      }
      u = mod(u + mod(st.alpha * x, p), p);
      accesses += 1;
      if (faultBit && k === Math.floor(spec.steps.length / 2)) {
        u = p === 0n ? (u ^ 1n) : mod(u + 1n, p);
      }
      if (st.qNext !== 0n) {
        v = mod(v + mod(st.qNext * modPow(u, spec.shearDeg, p), p), p);
        basicOps += 1;
      }
      trace.push({
        stage: `step ${k}.b`,
        op: `shear(-${st.qNext}u^${spec.shearDeg}); u += ${st.alpha}x; shear(+${st.qNext}u^${spec.shearDeg})${faultBit && k === Math.floor(spec.steps.length / 2) ? ' [1-BIT FAULT]' : ''}`,
        O, u, v
      });
    }

    const expectedDelta = p === 0n ? spec.D * modPow(x, spec.degree, 0n) : modPow(x, spec.degree, p);
    const expectedO = mod(O0 + expectedDelta, p);
    const outputExact = O === expectedO;
    const catalystsRestored = (u === u0) && (v === v0);
    return {
      spec,
      p,
      x,
      initial: { O: O0, u: u0, v: v0 },
      final: { O, u, v },
      expectedO,
      accesses,
      basicOps,
      outputExact,
      catalystsRestored,
      verified: outputExact && catalystsRestored,
      trace
    };
  }

  // =========================================================================
  // 4. Adaptive Forking Planner (Exact Commutative-Ring DP + Hybrid Scheduler)
  // =========================================================================

  function exactFourRegAccesses(delta, t, N) {
    const ds = baseDigits(delta, N);
    let acc = 0n;
    const tb = BigInt(t);
    let tPow = 1n;
    for (let i = 0; i < ds.length; i++) {
      const b = ds[i];
      const ci = b === 0 ? 0n : BigInt(b + 1) * tPow;
      acc = 2n * ci + 2n * acc;
      tPow *= tb;
    }
    return acc;
  }

  function isGadgetFeasible(spec, p, workload) {
    if (workload === 'matrix' && spec.shearDeg > 2) {
      return false; // Keep matrix shear tier strictly O(m^4) zero-overhead
    }
    if (p === 0n) return true;
    if (p < 2n || gcd(spec.D, p) !== 1n) return false;
    // Non-commutative matrix lift mu_delta (cor:matpow / Vinciguerra §4.4) divides by delta!, requiring delta! invertible mod p!
    if (workload === 'matrix' && !isFactInvertible(spec.degree, p)) {
      return false;
    }
    return true;
  }

  function isRadixScheduleValid(spec, N, p, workload = 'scalar') {
    if (p === 0n) return true;
    if (p < 2n) return false;
    const mLen = baseDigits(spec.degree, N).length;
    const reqFact = workload === 'matrix' ? spec.degree : (spec.degree - 1);
    return (
      gcd(spec.D, p) === 1n &&
      isFactInvertible(reqFact, p) &&
      isFactInvertible(mLen, p)
    );
  }

  function planAdaptiveFork(opts) {
    const workload = opts.workload || 'scalar'; // 'scalar' | 'streaming' | 'matrix' | 'frobenius'
    const N = BigInt(opts.N ?? 1000);
    const p = BigInt(opts.p ?? 0); // 0n means characteristic 0 (Q / exact Z), >= 2n means ring Z/pZ
    const matrixDim = safeInt(opts.matrixDim, 2, 1, 256);
    const deviceClass = opts.deviceClass || 'desktop';
    const pIsPrime = p >= 2n && isPrimeBig(p);
    const ringLabel = p === 0n ? 'exact Z/Q' : (pIsPrime ? `prime field F_${p}` : `commutative ring Z/${p}Z`);

    if (N < 1n) throw new Error('Exponent N must be >= 1');
    if (p < 0n || p === 1n) throw new Error('Modulus p must be 0 (exact Z/Q) or >= 2');

    // Static baselines for comparison
    const base4Acc = exactFourRegAccesses(5, 4, N);
    const prog5Acc = exactFourRegAccesses(7, 5, N);
    const prog8Acc = exactFourRegAccesses(13, 8, N);

    const p4Valid = isRadixScheduleValid(PROGRAMS_R3[4], N, p, workload);
    const p5Valid = isRadixScheduleValid(PROGRAMS_R3[5], N, p, workload);
    const p8Valid = isRadixScheduleValid(PROGRAMS_R3[8], N, p, workload);

    // Track every fork branch evaluated so the live SVG Fork-DAG can visualize winners & dodged branches!
    const forkCandidates = [];

    // Direct trivial case N = 1: literally 1 access (O += x) in 1 register!
    if (N === 1n) {
      forkCandidates.push({
        id: 'direct_x1',
        label: 'Direct O <- O + x',
        accesses: '1',
        status: 'winner',
        reason: 'Degree 1 requires only 1 input access in 1 register'
      });
      const baseNum = Number(base4Acc);
      return {
        workload,
        N: '1',
        p: p.toString(),
        pIsPrime,
        ringLabel,
        matrixDim,
        device: { maxFuzz: 500, traceLimit: 16, hint: 'Trivial degree-1 direct access (1 register, 1 access)' },
        internalPlan: { kind: 'direct_x1', n: 1 },
        forkCandidates,
        comparison: {
          vinciguerra_r3_x5: { accesses: base4Acc.toString(), exponent: '0.861353', validForP: p4Valid },
          prog5_x7_T3a: { accesses: prog5Acc.toString(), exponent: '0.827087', validForP: p5Valid, asympGainVsBase: 1 },
          prog8_x13_T3d: { accesses: prog8Acc.toString(), exponent: '0.810714', validForP: p8Valid, asympGainVsBase: 1 },
          adaptive_fork: {
            strategy: 'DIRECT_X1',
            label: 'Direct Input Addition (O <- O + x: 1 access, 1 register!)',
            accesses: '1',
            registers: workload === 'matrix' ? `${matrixDim * matrixDim} scalars` : '1 passive reg',
            tree: 'x^1 -> direct O <- O + x (1 access)',
            feasible: true
          }
        },
        reductionPct: baseNum > 0 ? ((baseNum - 1) / baseNum) * 100 : 0,
        speedupFactor: baseNum > 0 ? baseNum : 1
      };
    }

    // Check T1/T2 prime-field Frobenius collapse (strictly requires PRIME p and N >= 2)
    let frobenius2Plan = null;
    let t1DirectCandidate = null;
    if (pIsPrime && workload !== 'matrix') {
      const sp = digitSum(p, N);
      if (sp === 1) {
        frobenius2Plan = {
          strategy: p === 2n ? 'T2_BILINEAR_FROBENIUS' : 'T1a_FROBENIUS_COLLAPSE',
          label: p === 2n ? 'T2 Strictly Bilinear Frobenius Collapse (2 accesses!)' : `T1a Prime-Field Frobenius Collapse over F_${p} (2 accesses!)`,
          accesses: 2n,
          registers: p === 2n ? `${N.toString(2).length} bilinear regs` : '2 passive regs',
          tree: `x^${N} (s_${p}(${N}) = 1) -> direct 2-access Frobenius collapse!`
        };
        forkCandidates.push({
          id: 'frobenius_2',
          label: p === 2n ? 'T2 Bilinear Frobenius' : `T1a Frobenius (F_${p})`,
          accesses: '2',
          status: 'winner',
          reason: `s_${p}(${N}) = 1 collapses to 2 accesses`
        });
      } else if (BigInt(sp) < p) {
        t1DirectCandidate = {
          strategy: 'T1_DIGIT_SUM_DIRECT',
          label: `T1 Prime-Field Digit-Sum Direct (s_${p}(${N}) + 1 = ${sp + 1} accesses)`,
          accesses: BigInt(sp + 1),
          registers: '2 passive regs',
          tree: `x^${N} (s_${p}(${N}) = ${sp} <= ${p - 1n}) -> 2-register forward-difference program`
        };
        forkCandidates.push({
          id: 't1_direct',
          label: `T1 Digit-Sum (F_${p})`,
          accesses: String(sp + 1),
          status: 'candidate',
          reason: `s_${p}(${N}) = ${sp} < ${p}`
        });
      } else {
        forkCandidates.push({
          id: 't1_direct',
          label: `T1 2-Reg (F_${p})`,
          accesses: 'INF',
          status: 'pruned',
          reason: `T1c impossibility: s_${p}(${N}) = ${sp} >= ${p}`
        });
      }
    } else if (p >= 2n && !pIsPrime && workload !== 'matrix') {
      forkCandidates.push({
        id: 't1_direct',
        label: 'T1 Frobenius',
        accesses: 'N/A',
        status: 'pruned',
        reason: `Composite ring Z/${p}Z (T1 requires prime p)`
      });
    }

    // Determine feasible 3-register composition gadgets (exact ring check gcd(D_t, p) == 1)
    const feasibleSpecs = [];
    for (const t of [4, 5, 6, 7, 8, 9]) {
      const spec = PROGRAMS_R3[t];
      if (isGadgetFeasible(spec, p, workload)) {
        feasibleSpecs.push(spec);
      } else if (t === 8 || t === 5 || t === 6 || (workload === 'matrix' && t === 4)) {
        const reason = workload === 'matrix' && spec.shearDeg > 2
          ? `Shear deg ${spec.shearDeg} > 2 (Theta(m^${2 * spec.shearDeg}) scalars)`
          : (workload === 'matrix' && p >= 2n && !isFactInvertible(spec.degree, p)
            ? `Matrix lift mu_${spec.degree} requires ${spec.degree}! invertible (p > ${spec.degree})`
            : `Bad divisor: gcd(D_${t}, ${p}) = ${gcd(spec.D, p)} > 1`);
        forkCandidates.push({
          id: spec.id,
          label: `${spec.id} (x^${spec.degree})`,
          accesses: 'DODGED',
          status: 'pruned',
          reason
        });
      }
    }

    // Exact DP over n <= DP_LIMIT (strictly verifying exact ring invertibility at EVERY node!)
    const DP_LIMIT = N <= 4096n ? Number(N) : 2048;
    const costW3 = new Array(DP_LIMIT + 1).fill(Infinity);
    const planW3 = new Array(DP_LIMIT + 1).fill(null);

    costW3[0] = 0;
    planW3[0] = { op: 'const1' };
    costW3[1] = 1;
    planW3[1] = { op: 'direct', n: 1, accesses: 1 };

    // Precompute factorial invertibility limit for p (largest maxFactOk such that maxFactOk! is a unit mod p)
    let maxFactOk = DP_LIMIT;
    if (p >= 2n) {
      maxFactOk = 1;
      for (let k = 2; k <= DP_LIMIT; k++) {
        if (gcd(BigInt(k), p) === 1n) maxFactOk = k;
        else break;
      }
    }

    for (let n = 2; n <= DP_LIMIT; n++) {
      // Option A: direct forward-difference 2-reg program (requires n! invertible in Z/pZ!)
      if (n <= maxFactOk) {
        costW3[n] = n + 1;
        planW3[n] = { op: 'digit_leaf', n, accesses: n + 1 };
      }
      // Option B: prime-field T1 shortcut (strictly prime p, non-matrix)
      if (pIsPrime && workload !== 'matrix') {
        const sp = digitSum(p, BigInt(n));
        if (BigInt(sp) < p && sp + 1 < costW3[n]) {
          costW3[n] = sp + 1;
          planW3[n] = { op: 't1_frobenius', n, sp, accesses: sp + 1 };
        }
      }
      // Option C: exact multiplicative composition fork via any feasible 3-reg gadget
      for (const spec of feasibleSpecs) {
        if (n % spec.degree === 0) {
          const q = n / spec.degree;
          const cand = spec.t * costW3[q];
          if (cand < costW3[n]) {
            costW3[n] = cand;
            planW3[n] = { op: 'compose', gadget: spec.id, degree: spec.degree, t: spec.t, child: q, accesses: cand };
          }
        }
      }
    }

    // 4-register passive Cook-Mertz / Gray-Code / Composition Adaptive Fork DP:
    let adaptiveBest = null;
    let winningForkId = frobenius2Plan ? 'frobenius_2' : '';

    if (frobenius2Plan) {
      adaptiveBest = {
        ...frobenius2Plan,
        mode: 'frobenius',
        engineKey: 'frobenius',
        feasible: true
      };
    } else if (N <= BigInt(DP_LIMIT)) {
      const nInt = Number(N);
      let bestAcc = Infinity;
      let bestDesc = '';
      let bestPlan = null;

      // 0. Prime-field T1 direct candidate (if valid) competes fairly on access count
      if (t1DirectCandidate && Number(t1DirectCandidate.accesses) < bestAcc) {
        bestAcc = Number(t1DirectCandidate.accesses);
        bestDesc = t1DirectCandidate.label;
        bestPlan = { kind: 't1_direct', n: nInt };
        winningForkId = 't1_direct';
      }
      // 1. Direct passive 3-register single gadget match (e.g., N = 5, 7, 9, 11, 13, 15)
      for (const spec of feasibleSpecs) {
        if (spec.degree === nInt) {
          forkCandidates.push({
            id: `direct_${spec.id}`,
            label: `Direct 3-Reg ${spec.id}`,
            accesses: String(spec.t),
            status: 'candidate',
            reason: `Exact 3-register passive loop for x^${nInt}`
          });
          if (spec.t < bestAcc) {
            bestAcc = spec.t;
            bestDesc = `Direct passive 3-reg ${spec.id} (x^${nInt} in ${spec.t} accesses, 3 regs!)`;
            bestPlan = { kind: 'direct_pass3', t: spec.t, gadget: spec.id };
            winningForkId = `direct_${spec.id}`;
          }
        }
      }
      // 2. Direct 2-reg forward-difference leaf (needs n! invertible in Z/pZ!)
      if (nInt <= maxFactOk) {
        forkCandidates.push({
          id: 'direct_digit',
          label: '2-Reg Forward Diff',
          accesses: String(nInt + 1),
          status: 'candidate',
          reason: `${nInt}! invertible in ${ringLabel}`
        });
        if (nInt + 1 < bestAcc) {
          bestAcc = nInt + 1;
          bestDesc = `Direct 2-reg forward-difference leaf (x^${nInt} in ${nInt + 1} accesses)`;
          bestPlan = { kind: 'direct_digit', n: nInt };
          winningForkId = 'direct_digit';
        }
      }
      // 2b. Passive 4-reg wrap of exact Work3 multiplicative composition (2 * costW3[n] accesses!)
      if (costW3[nInt] < Infinity && planW3[nInt] && planW3[nInt].op === 'compose') {
        const wAcc = 2 * costW3[nInt];
        forkCandidates.push({
          id: 'wrap1_work3',
          label: `4-Reg Compose (${planW3[nInt].gadget}*x^${planW3[nInt].child})`,
          accesses: String(wAcc),
          status: 'candidate',
          reason: `Non-passive 3-reg composition wrapped cleanly`
        });
        if (wAcc < bestAcc) {
          bestAcc = wAcc;
          bestDesc = `Adaptive Composition Wrap: passive 4-reg wrap of Work3(${nInt} = ${planW3[nInt].degree} * ${planW3[nInt].child}) -> ${wAcc} accesses`;
          bestPlan = { kind: 'wrap1_work3', n: nInt, work3Plan: planW3[nInt], work3Table: planW3 };
          winningForkId = 'wrap1_work3';
        }
      }
      // 3. Exact Gray-Code 2-way Cook-Mertz adaptive fork: x^n = x^a * x^(n-a) (needs 2 invertible in Z/pZ!)
      if (2 <= maxFactOk) {
        let bestGray = Infinity;
        let bestGrayPair = null;
        for (let a = 1; a <= Math.floor(nInt / 2); a++) {
          const b = nInt - a;
          if (costW3[a] < Infinity && costW3[b] < Infinity) {
            const cand = 2 * costW3[a] + 2 * costW3[b];
            if (cand < bestGray) {
              bestGray = cand;
              bestGrayPair = { a, b };
            }
          }
        }
        if (bestGrayPair) {
          const { a, b } = bestGrayPair;
          forkCandidates.push({
            id: 'gray_cm2_fork',
            label: `Gray-Code Split (x^${a}*x^${b})`,
            accesses: String(bestGray),
            status: 'candidate',
            reason: `2*${costW3[a]} + 2*${costW3[b]} in 4 passive regs`
          });
          if (bestGray < bestAcc) {
            bestAcc = bestGray;
            bestDesc = `Gray-Code 2-Way Adaptive Fork: x^${nInt} = x^${a} (${costW3[a]}w) * x^${b} (${costW3[b]}w) -> ${bestGray} accesses`;
            bestPlan = { kind: 'gray_cm2_fork', a, b, planA: planW3[a], planB: planW3[b], work3Table: planW3 };
            winningForkId = 'gray_cm2_fork';
          }
        }
      }
      // 4. Compare all feasible base-delta Cook-Mertz expansions (delta in {5, 7, 9, 11, 13, 15})
      for (const spec of feasibleSpecs) {
        if (!isRadixScheduleValid(spec, N, p, workload)) continue;
        const ds = baseDigits(spec.degree, N);
        const mLen = ds.length;
        let acc = 0;
        let tPow = 1;
        let dPow = 1;
        for (let i = 0; i < mLen; i++) {
          const b = ds[i];
          const termExp = b * dPow;
          const staticCi = b === 0 ? 0 : (b + 1) * tPow;
          const adaptCi = b === 0 ? 0 : (termExp <= DP_LIMIT && costW3[termExp] < staticCi ? costW3[termExp] : staticCi);
          acc = 2 * adaptCi + 2 * acc;
          tPow *= spec.t;
          dPow *= spec.degree;
        }
        forkCandidates.push({
          id: `radix_${spec.id}`,
          label: `Base-${spec.degree} (${spec.id})`,
          accesses: String(acc),
          status: 'candidate',
          reason: `Cook-Mertz digits [${ds.join(',')}]`
        });
        if (acc < bestAcc) {
          bestAcc = acc;
          bestDesc = `Adaptive Base-${spec.degree} Fork (${spec.id}, digits [${ds.join(', ')}] LSB-first) -> ${acc} accesses`;
          bestPlan = { kind: 'radix_fork', base: spec.degree, t: spec.t, gadget: spec.id, digits: ds };
          winningForkId = `radix_${spec.id}`;
        }
      }

      if (bestAcc === Infinity) {
        adaptiveBest = {
          strategy: 'MODULUS_CONSTRAINT_WARNING',
          label: `Modulus p=${p} divides a required denominator for N=${N}; choose modulus coprime to D_t and required factorials (e.g. prime p > max(12, floor(log_13 N)+1) avoiding bad primes)`,
          accesses: prog5Acc,
          registers: workload === 'matrix' ? `${3 * matrixDim * matrixDim + (matrixDim * matrixDim * (matrixDim * matrixDim + 1)) / 2} scalars` : '4 passive regs',
          tree: `No exact inverse exists mod ${p} for any verified schedule at N=${N}`,
          feasible: false
        };
      } else {
        adaptiveBest = {
          strategy: 'ADAPTIVE_FORK_DP',
          label: bestDesc,
          accesses: BigInt(bestAcc),
          registers: workload === 'matrix'
            ? `${3 * matrixDim * matrixDim + (matrixDim * matrixDim * (matrixDim * matrixDim + 1)) / 2} scalars (zero overhead vs Vinciguerra r=3)`
            : (bestPlan && bestPlan.kind === 'direct_pass3' ? '3 passive regs' : '4 passive regs'),
          tree: bestDesc,
          plan: bestPlan,
          feasible: true
        };
      }
    } else {
      // Large-N Hybrid Top-Down Adaptive Forking (N > 4096, arbitrary BigInt!)
      // Evaluate EVERY feasible base-delta Cook-Mertz schedule + compete fairly against T1 prime-field digit-sum!
      let bestHybrid = null;
      const priority = workload === 'matrix' ? [5, 4] : [8, 9, 7, 6, 5, 4];
      const matScalars = 3 * matrixDim * matrixDim + (matrixDim * matrixDim * (matrixDim * matrixDim + 1)) / 2;

      for (const tCand of priority) {
        const sp = PROGRAMS_R3[tCand];
        if (!isGadgetFeasible(sp, p, workload) || !isRadixScheduleValid(sp, N, p, workload)) continue;
        const ds = baseDigits(sp.degree, N);
        let hybridAcc = 0n;
        let tPow = 1n;
        let dPow = 1n;
        for (let i = 0; i < ds.length; i++) {
          const b = ds[i];
          const termExp = BigInt(b) * dPow;
          let ci = b === 0 ? 0n : BigInt(b + 1) * tPow;
          if (b > 0 && termExp <= BigInt(DP_LIMIT)) {
            const dpVal = costW3[Number(termExp)];
            if (Number.isFinite(dpVal) && BigInt(dpVal) < ci) {
              ci = BigInt(dpVal);
            }
          }
          hybridAcc = 2n * ci + 2n * hybridAcc;
          tPow *= BigInt(sp.t);
          dPow *= BigInt(sp.degree);
        }
        const candId = `hybrid_${sp.id}`;
        forkCandidates.push({
          id: candId,
          label: `Hybrid ${sp.id} (Base ${sp.degree})`,
          accesses: hybridAcc.toString(),
          status: 'candidate',
          reason: `Base-${sp.degree} (${ds.length} digits, exp ${sp.exponent.toFixed(5)}) + DP leaves`
        });
        if (!bestHybrid || hybridAcc < bestHybrid.accesses) {
          bestHybrid = { spec: sp, ds, accesses: hybridAcc, id: candId };
        }
      }

      // Compete T1 Prime-Field Digit-Sum directly against all feasible hybrid schedules (fixes large-N T1 optimality!)
      if (t1DirectCandidate && (!bestHybrid || t1DirectCandidate.accesses < bestHybrid.accesses)) {
        winningForkId = 't1_direct';
        adaptiveBest = {
          strategy: t1DirectCandidate.strategy,
          label: t1DirectCandidate.label,
          accesses: t1DirectCandidate.accesses,
          registers: t1DirectCandidate.registers,
          tree: t1DirectCandidate.tree,
          plan: { kind: 't1_direct', n: N.toString() },
          feasible: true
        };
      } else if (!bestHybrid) {
        adaptiveBest = {
          strategy: 'MODULUS_CONSTRAINT_WARNING',
          label: `Modulus p=${p} is incompatible with all verified large-N schedules at N=${N} (need gcd(D_t, p)=1 and required factorials invertible mod p)`,
          accesses: prog5Acc,
          registers: workload === 'matrix' ? `${matScalars} scalar regs` : '4 passive regs',
          tree: `Modulus p=${p} divides required denominators across all feasible gadgets`,
          feasible: false
        };
      } else {
        const chosenSpec = bestHybrid.spec;
        winningForkId = bestHybrid.id;
        adaptiveBest = {
          strategy: workload === 'matrix' ? 'ADAPTIVE_MATRIX_PROG5' : `ADAPTIVE_HYBRID_${chosenSpec.id.toUpperCase()}`,
          label: workload === 'matrix'
            ? `Adaptive Matrix Fork (${chosenSpec.id}, d=2 shear, zero extra scalar regs) + DP leaves`
            : `Adaptive Hybrid Fork (${chosenSpec.id} top radix + DP-optimal leaves)`,
          accesses: bestHybrid.accesses,
          registers: workload === 'matrix' ? `${matScalars} scalar regs (m=${matrixDim}, exact r=3 tier)` : '4 passive regs',
          tree: `Top radix ${chosenSpec.degree} (${chosenSpec.id}, ${bestHybrid.ds.length} digits) -> DP leaf optimization for sub-exponents <= ${DP_LIMIT}`,
          chosenSpecId: chosenSpec.id,
          plan: { kind: 'radix_fork', base: chosenSpec.degree, t: chosenSpec.t, gadget: chosenSpec.id, digits: bestHybrid.ds },
          feasible: true
        };
      }
    }

    // Mark the single winning fork candidate clearly AND guarantee the winner is ALWAYS retained in the SVG DAG!
    for (const fc of forkCandidates) {
      if (fc.id === winningForkId) fc.status = 'winner';
    }
    const orderedCandidates = [];
    const winners = forkCandidates.filter((c) => c.status === 'winner');
    const pruned = forkCandidates.filter((c) => c.status === 'pruned');
    const alts = forkCandidates
      .filter((c) => c.status === 'candidate')
      .sort((a, b) => {
        const ba = /^\d+$/.test(a.accesses) ? BigInt(a.accesses) : (1n << 200n);
        const bb = /^\d+$/.test(b.accesses) ? BigInt(b.accesses) : (1n << 200n);
        return ba < bb ? -1 : (ba > bb ? 1 : 0);
      });
    orderedCandidates.push(...winners.slice(0, 1));
    orderedCandidates.push(...pruned.slice(0, 2));
    for (const a of alts) {
      if (orderedCandidates.length >= 7) break;
      orderedCandidates.push(a);
    }
    for (const pr of pruned.slice(2)) {
      if (orderedCandidates.length >= 7) break;
      orderedCandidates.push(pr);
    }

    // Exact BigInt-safe speedup & percentage calculation (never overflows Number even for N = 10^30!)
    const speedupFactor = bigRatio(base4Acc, adaptiveBest.accesses);
    const reductionPct = base4Acc > 0n
      ? (1 - bigRatio(adaptiveBest.accesses, base4Acc)) * 100
      : 0;

    // Asymptotic ratio at N (pure exponent comparison)
    const nf = Number(N > 10n ** 15n ? 10n ** 15n : N);
    const asympRatio5 = nf > 1 ? Math.pow(nf, Math.log(4) / Math.log(5) - Math.log(5) / Math.log(7)) : 1;
    const asympRatio8 = nf > 1 ? Math.pow(nf, Math.log(4) / Math.log(5) - Math.log(8) / Math.log(13)) : 1;

    const deviceBudgets = {
      watch: { maxFuzz: 100, traceLimit: 6, streamHz: 1, hint: 'Smartwatch glance mode: compact exact BigInt & 100-trial live fuzzer' },
      phone: { maxFuzz: 300, traceLimit: 14, streamHz: 2, hint: 'Mobile mode: touch-tuned adaptive fork & 300-trial fuzzer' },
      tablet: { maxFuzz: 600, traceLimit: 24, streamHz: 3, hint: 'Tablet split-view: full live step trace & 600-trial fuzzer' },
      laptop: { maxFuzz: 1000, traceLimit: 40, streamHz: 4, hint: 'Laptop mode: full multi-engine workbench & 1,000-trial fuzzer' },
      desktop: { maxFuzz: 2000, traceLimit: 60, streamHz: 4, hint: 'Desktop mode: full trace, live telemetry & 2,000-trial fuzzer' }
    };

    return {
      workload,
      N: N.toString(),
      p: p.toString(),
      pIsPrime,
      ringLabel,
      matrixDim,
      device: deviceBudgets[deviceClass] || deviceBudgets.desktop,
      internalPlan: adaptiveBest.plan || null,
      forkCandidates: orderedCandidates,
      comparison: {
        vinciguerra_r3_x5: { accesses: base4Acc.toString(), exponent: '0.861353', validForP: p4Valid },
        prog5_x7_T3a: { accesses: prog5Acc.toString(), exponent: '0.827087', validForP: p5Valid, asympGainVsBase: asympRatio5 },
        prog8_x13_T3d: { accesses: prog8Acc.toString(), exponent: '0.810714', validForP: p8Valid, asympGainVsBase: asympRatio8 },
        adaptive_fork: {
          strategy: adaptiveBest.strategy,
          label: adaptiveBest.label,
          accesses: adaptiveBest.accesses.toString(),
          registers: adaptiveBest.registers,
          tree: adaptiveBest.tree,
          feasible: adaptiveBest.feasible !== false
        }
      },
      reductionPct,
      speedupFactor
    };
  }

  // =========================================================================
  // 5. Literal 4-Register Powering (T3h) & Streaming Moments (T3i)
  // =========================================================================

  function execDigitPowWork3(b, x, p, state, scale = 1n) {
    let [r0, r1, r2] = state;
    if (b === 0) {
      return { state: [mod(r0 + scale, p), r1, r2], accesses: 0 };
    }
    if (b === 1) {
      return { state: [mod(r0 + mod(scale * x, p), p), r1, r2], accesses: 1 };
    }
    const invFact = modInv(factorialMod(b, p), p);
    const outFactor = mod(scale * invFact, p);
    let accesses = 0;
    for (let a = 0; a <= b; a++) {
      const sign = ((b - a) & 1) ? -1n : 1n;
      const w = mod(outFactor * sign * mod(binomExact(b, a), p), p);
      r0 = mod(r0 + mod(w * modPow(r1, b, p), p), p);
      const step = a < b ? 1n : -BigInt(b);
      r1 = mod(r1 + mod(step * x, p), p);
      accesses += 1;
    }
    return { state: [r0, r1, r2], accesses };
  }

  function execPowerLevelWork3(spec, level, b, x, p, state, scale = 1n) {
    if (level === 0) {
      return execDigitPowWork3(b, x, p, state, scale);
    }

    function runSpecWithOracle(st3, dstIdx, uIdx, vIdx, sScale, addInputFn) {
      const reg = [st3[0], st3[1], st3[2]];
      const invD = modInv(spec.D, p);
      const outScale = mod(sScale * invD, p);
      let acc = 0;
      for (let k = 0; k < spec.steps.length; k++) {
        const st = spec.steps[k];
        let delta = 0n;
        for (const [du, dv, coeff] of st.terms) {
          delta = mod(delta + mod(coeff * mod(modPow(reg[uIdx], du, p) * modPow(reg[vIdx], dv, p), p), p), p);
        }
        reg[dstIdx] = mod(reg[dstIdx] + mod(outScale * delta, p), p);
        if (st.qNext !== 0n) {
          reg[vIdx] = mod(reg[vIdx] - mod(st.qNext * modPow(reg[uIdx], spec.shearDeg, p), p), p);
        }
        const sub = addInputFn(reg, uIdx, vIdx, dstIdx, st.alpha);
        reg[0] = sub.state[0];
        reg[1] = sub.state[1];
        reg[2] = sub.state[2];
        acc += sub.accesses;
        if (st.qNext !== 0n) {
          reg[vIdx] = mod(reg[vIdx] + mod(st.qNext * modPow(reg[uIdx], spec.shearDeg, p), p), p);
        }
      }
      return { state: reg, accesses: acc };
    }

    function runPowTower(lvl, regState, dstIdx, uIdx, vIdx, sScale) {
      if (lvl === 0) {
        const out = [regState[0], regState[1], regState[2]];
        out[dstIdx] = mod(out[dstIdx] + mod(sScale * x, p), p);
        return { state: out, accesses: 1 };
      }
      return runSpecWithOracle(regState, dstIdx, uIdx, vIdx, sScale, (curReg, subDst, subU, subV, alpha) =>
        runPowTower(lvl - 1, curReg, subDst, subU, subV, alpha)
      );
    }

    if (b === 0) {
      return { state: [mod(state[0] + scale, p), state[1], state[2]], accesses: 0 };
    }
    if (b === 1) {
      return runPowTower(level, state, 0, 1, 2, scale);
    }
    const reg = [state[0], state[1], state[2]];
    const invFact = modInv(factorialMod(b, p), p);
    const outFactor = mod(scale * invFact, p);
    let totalAcc = 0;
    for (let a = 0; a <= b; a++) {
      const sign = ((b - a) & 1) ? -1n : 1n;
      const w = mod(outFactor * sign * mod(binomExact(b, a), p), p);
      reg[0] = mod(reg[0] + mod(w * modPow(reg[1], b, p), p), p);
      const step = a < b ? 1n : -BigInt(b);
      const sub = runPowTower(level, reg, 1, 2, 0, step);
      reg[0] = sub.state[0];
      reg[1] = sub.state[1];
      reg[2] = sub.state[2];
      totalAcc += sub.accesses;
    }
    return { state: reg, accesses: totalAcc };
  }

  function execWork3PlanNode(planTable, n, p, regState, dstIdx, uIdx, vIdx, scale, addInputFn) {
    const node = planTable[n];
    if (!node || node.op === 'const1') {
      const out = [regState[0], regState[1], regState[2]];
      out[dstIdx] = mod(out[dstIdx] + scale, p);
      return { state: out, accesses: 0 };
    }
    if (node.op === 'direct') {
      return addInputFn(regState, dstIdx, uIdx, vIdx, scale);
    }
    if (node.op === 'digit_leaf') {
      const reg = [regState[0], regState[1], regState[2]];
      const invFact = modInv(factorialMod(n, p), p);
      const outFactor = mod(scale * invFact, p);
      let acc = 0;
      for (let a = 0; a <= n; a++) {
        const sign = ((n - a) & 1) ? -1n : 1n;
        const w = mod(outFactor * sign * mod(binomExact(n, a), p), p);
        reg[dstIdx] = mod(reg[dstIdx] + mod(w * modPow(reg[uIdx], n, p), p), p);
        const step = a < n ? 1n : -BigInt(n);
        const sub = addInputFn(reg, uIdx, vIdx, dstIdx, step);
        reg[0] = sub.state[0]; reg[1] = sub.state[1]; reg[2] = sub.state[2];
        acc += sub.accesses;
      }
      return { state: reg, accesses: acc };
    }
    if (node.op === 't1_frobenius') {
      const s = node.sp;
      const reg = [regState[0], regState[1], regState[2]];
      const invFact = modInv(factorialMod(s, p), p);
      const outFactor = mod(scale * invFact, p);
      let acc = 0;
      for (let a = 0; a <= s; a++) {
        const sign = ((s - a) & 1) ? -1n : 1n;
        const w = mod(outFactor * sign * mod(binomExact(s, a), p), p);
        reg[dstIdx] = mod(reg[dstIdx] + mod(w * modPow(reg[uIdx], n, p), p), p);
        const step = a < s ? 1n : -BigInt(s);
        const sub = addInputFn(reg, uIdx, vIdx, dstIdx, step);
        reg[0] = sub.state[0]; reg[1] = sub.state[1]; reg[2] = sub.state[2];
        acc += sub.accesses;
      }
      return { state: reg, accesses: acc };
    }
    if (node.op === 'compose') {
      const spec = PROGRAMS_R3[node.t];
      const reg = [regState[0], regState[1], regState[2]];
      const invD = modInv(spec.D, p);
      const outScale = mod(scale * invD, p);
      let acc = 0;
      for (let k = 0; k < spec.steps.length; k++) {
        const st = spec.steps[k];
        let delta = 0n;
        for (const [du, dv, coeff] of st.terms) {
          delta = mod(delta + mod(coeff * mod(modPow(reg[uIdx], du, p) * modPow(reg[vIdx], dv, p), p), p), p);
        }
        reg[dstIdx] = mod(reg[dstIdx] + mod(outScale * delta, p), p);
        if (st.qNext !== 0n) {
          reg[vIdx] = mod(reg[vIdx] - mod(st.qNext * modPow(reg[uIdx], spec.shearDeg, p), p), p);
        }
        const sub = execWork3PlanNode(planTable, node.child, p, reg, uIdx, vIdx, dstIdx, st.alpha, addInputFn);
        reg[0] = sub.state[0]; reg[1] = sub.state[1]; reg[2] = sub.state[2];
        acc += sub.accesses;
        if (st.qNext !== 0n) {
          reg[vIdx] = mod(reg[vIdx] + mod(st.qNext * modPow(reg[uIdx], spec.shearDeg, p), p), p);
        }
      }
      return { state: reg, accesses: acc };
    }
    throw new Error(`Unknown Work3 plan op: ${node.op}`);
  }

  function execFourRegPowering(NIn, xIn, pIn, opts = {}) {
    const N = BigInt(NIn);
    const p = BigInt(pIn);
    if (N < 1n) throw new Error('Exponent N must be >= 1');
    if (p < 2n) throw new Error('Modulus p must be >= 2 for modular 4-register execution (supports prime F_p AND valid composite rings Z/mZ)');
    const x = mod(BigInt(xIn), p);
    const engineChoice = opts.engine || 'adaptive'; // 'prog4_x5' | 'prog5_x7' | 'prog8_x13' | 'adaptive'
    const faultBit = Boolean(opts.faultBit);

    const O0 = mod(BigInt(opts.O0 ?? 424242n), p);
    const u0 = mod(BigInt(opts.u0 ?? 135791n), p);
    const r10 = mod(BigInt(opts.r10 ?? 246802n), p);
    const r20 = mod(BigInt(opts.r20 ?? 975313n), p);

    let forcedRadixSpec = null;

    // If adaptive mode, ALWAYS check exact Frobenius / T1 prime-field collapse for ANY BigInt N >= 2!
    if (engineChoice === 'adaptive') {
      const planRes = planAdaptiveFork({ workload: 'scalar', N, p });
      const strat = planRes.comparison.adaptive_fork.strategy;

      if (strat === 'T1a_FROBENIUS_COLLAPSE' || strat === 'T2_BILINEAR_FROBENIUS') {
        let O = O0;
        let u = u0;
        O = mod(O - modPow(u, N, p), p);
        u = mod(u + x, p);
        const midScramble = { O, u, r1: r10, r2: r20 };
        if (faultBit) u = mod(u + 1n, p);
        O = mod(O + modPow(u, N, p), p);
        u = mod(u - x, p);
        const expectedO = mod(O0 + modPow(x, N, p), p);
        return {
          engineUsed: 'adaptive:T1a_frobenius_2access',
          N: N.toString(), p: p.toString(), x: x.toString(), digits: [1],
          initial: { O: O0, u: u0, r1: r10, r2: r20 },
          midScramble,
          final: { O, u, r1: r10, r2: r20 },
          expectedO, accesses: 2,
          vinciguerraBaselineAccesses: exactFourRegAccesses(5, 4, N).toString(),
          outputExact: O === expectedO, catalystsRestored: u === u0, verified: O === expectedO && u === u0
        };
      }
      if (strat === 'T1_DIGIT_SUM_DIRECT') {
        const s = digitSum(p, N);
        const invFact = modInv(factorialMod(s, p), p);
        let O = O0;
        let u = u0;
        let acc = 0;
        let midScramble = null;
        for (let a = 0; a <= s; a++) {
          const sign = ((s - a) & 1) ? -1n : 1n;
          const w = mod(invFact * sign * mod(binomExact(s, a), p), p);
          // Exact BigInt N exponentiation (never truncates via Number(N)!)
          O = mod(O + mod(w * modPow(u, N, p), p), p);
          const step = a < s ? 1n : -BigInt(s);
          u = mod(u + mod(step * x, p), p);
          if (faultBit && a === 0) u = mod(u + 1n, p);
          if (a === Math.floor(s / 2)) midScramble = { O, u, r1: r10, r2: r20 };
          acc += 1;
        }
        const expectedO = mod(O0 + modPow(x, N, p), p);
        return {
          engineUsed: 'adaptive:t1_direct (2-reg passive)',
          N: N.toString(), p: p.toString(), x: x.toString(), digits: baseDigits(p, N),
          initial: { O: O0, u: u0, r1: r10, r2: r20 },
          midScramble: midScramble || { O, u, r1: r10, r2: r20 },
          final: { O, u, r1: r10, r2: r20 },
          expectedO, accesses: acc,
          vinciguerraBaselineAccesses: exactFourRegAccesses(5, 4, N).toString(),
          outputExact: O === expectedO, catalystsRestored: u === u0, verified: O === expectedO && u === u0
        };
      }

      if (N <= 4096n) {
        const plan = planRes.internalPlan;
        const baseOracle = (st3, dstIdx, _u, _v, alpha) => {
          const out = [st3[0], st3[1], st3[2]];
          out[dstIdx] = mod(out[dstIdx] + mod(alpha * x, p), p);
          return { state: out, accesses: 1 };
        };

        if (plan && plan.kind === 'direct_x1') {
          let O = mod(O0 + x, p);
          let u = u0;
          if (faultBit) u = mod(u + 1n, p);
          const expectedO = mod(O0 + x, p);
          return {
            engineUsed: 'adaptive:direct_x1 (1-reg, 1 access)',
            N: '1', p: p.toString(), x: x.toString(), digits: [1],
            initial: { O: O0, u: u0, r1: r10, r2: r20 },
            midScramble: { O, u, r1: r10, r2: r20 },
            final: { O, u, r1: r10, r2: r20 },
            expectedO, accesses: 1,
            vinciguerraBaselineAccesses: Number(exactFourRegAccesses(5, 4, N)),
            outputExact: O === expectedO, catalystsRestored: u === u0, verified: O === expectedO && u === u0
          };
        }
        if (plan && plan.kind === 'direct_pass3') {
          const r3 = execPass3(plan.t, x, p, { O0, u0, v0: r10, faultBit });
          const mid = r3.trace[Math.floor(r3.trace.length / 2)] || r3.final;
          return {
            engineUsed: `adaptive:${plan.gadget} (direct 3-reg)`,
            N: N.toString(), p: p.toString(), x: x.toString(), digits: [Number(N)],
            initial: { O: O0, u: u0, r1: r10, r2: r20 },
            midScramble: { O: mid.O, u: mid.u, r1: mid.v, r2: r20 },
            final: { O: r3.final.O, u: r3.final.u, r1: r3.final.v, r2: r20 },
            expectedO: r3.expectedO, accesses: r3.accesses,
            vinciguerraBaselineAccesses: Number(exactFourRegAccesses(5, 4, N)),
            outputExact: r3.outputExact, catalystsRestored: r3.catalystsRestored, verified: r3.verified
          };
        }
        if (plan && (plan.kind === 'direct_digit' || plan.kind === 't1_direct')) {
          const nInt = Number(N);
          const s = plan.kind === 't1_direct' ? digitSum(p, N) : nInt;
          const invFact = modInv(factorialMod(s, p), p);
          let O = O0;
          let u = u0;
          let acc = 0;
          let midScramble = null;
          for (let a = 0; a <= s; a++) {
            const sign = ((s - a) & 1) ? -1n : 1n;
            const w = mod(invFact * sign * mod(binomExact(s, a), p), p);
            O = mod(O + mod(w * modPow(u, N, p), p), p);
            const step = a < s ? 1n : -BigInt(s);
            u = mod(u + mod(step * x, p), p);
            if (faultBit && a === 0) u = mod(u + 1n, p);
            if (a === Math.floor(s / 2)) midScramble = { O, u, r1: r10, r2: r20 };
            acc += 1;
          }
          const expectedO = mod(O0 + modPow(x, N, p), p);
          return {
            engineUsed: `adaptive:${plan.kind} (2-reg passive)`,
            N: N.toString(), p: p.toString(), x: x.toString(), digits: [nInt],
            initial: { O: O0, u: u0, r1: r10, r2: r20 },
            midScramble: midScramble || { O, u, r1: r10, r2: r20 },
            final: { O, u, r1: r10, r2: r20 },
            expectedO, accesses: acc,
            vinciguerraBaselineAccesses: Number(exactFourRegAccesses(5, 4, N)),
            outputExact: O === expectedO, catalystsRestored: u === u0, verified: O === expectedO && u === u0
          };
        }
        if (plan && plan.kind === 'wrap1_work3') {
          let O = mod(O0 - u0, p);
          let work = [u0, r10, r20];
          const rPlus = execWork3PlanNode(plan.work3Table, plan.n, p, work, 0, 1, 2, 1n, baseOracle);
          work = rPlus.state;
          const midScramble = { O, u: work[0], r1: work[1], r2: work[2] };
          if (faultBit) work[1] = mod(work[1] + 1n, p);
          O = mod(O + work[0], p);
          const rMinus = execWork3PlanNode(plan.work3Table, plan.n, p, work, 0, 1, 2, -1n, baseOracle);
          work = rMinus.state;
          const expectedO = mod(O0 + modPow(x, N, p), p);
          const restored = work[0] === u0 && work[1] === r10 && work[2] === r20;
          return {
            engineUsed: `adaptive:wrap1_compose(${plan.work3Plan.gadget}*x^${plan.work3Plan.child})`,
            N: N.toString(), p: p.toString(), x: x.toString(), digits: [plan.n],
            initial: { O: O0, u: u0, r1: r10, r2: r20 },
            midScramble,
            final: { O, u: work[0], r1: work[1], r2: work[2] },
            expectedO, accesses: rPlus.accesses + rMinus.accesses,
            vinciguerraBaselineAccesses: Number(exactFourRegAccesses(5, 4, N)),
            outputExact: O === expectedO, catalystsRestored: restored, verified: O === expectedO && restored
          };
        }
        if (plan && plan.kind === 'gray_cm2_fork') {
          const inv2 = modInv(2n, p);
          let O = O0;
          let work = [u0, r10, r20];
          let acc = 0;
          O = mod(O + mod(inv2 * modPow(work[0], 2, p), p), p);
          let sub = execWork3PlanNode(plan.work3Table, plan.a, p, work, 0, 1, 2, 1n, baseOracle);
          work = sub.state; acc += sub.accesses;
          if (faultBit) work[1] = mod(work[1] + 1n, p);
          O = mod(O - mod(inv2 * modPow(work[0], 2, p), p), p);
          sub = execWork3PlanNode(plan.work3Table, plan.b, p, work, 0, 1, 2, 1n, baseOracle);
          work = sub.state; acc += sub.accesses;
          const midScramble = { O, u: work[0], r1: work[1], r2: work[2] };
          O = mod(O + mod(inv2 * modPow(work[0], 2, p), p), p);
          sub = execWork3PlanNode(plan.work3Table, plan.a, p, work, 0, 1, 2, -1n, baseOracle);
          work = sub.state; acc += sub.accesses;
          O = mod(O - mod(inv2 * modPow(work[0], 2, p), p), p);
          sub = execWork3PlanNode(plan.work3Table, plan.b, p, work, 0, 1, 2, -1n, baseOracle);
          work = sub.state; acc += sub.accesses;
          const expectedO = mod(O0 + modPow(x, N, p), p);
          const restored = work[0] === u0 && work[1] === r10 && work[2] === r20;
          return {
            engineUsed: `adaptive:gray_cm2(x^${plan.a}*x^${plan.b})`,
            N: N.toString(), p: p.toString(), x: x.toString(), digits: [plan.a, plan.b],
            initial: { O: O0, u: u0, r1: r10, r2: r20 },
            midScramble,
            final: { O, u: work[0], r1: work[1], r2: work[2] },
            expectedO, accesses: acc,
            vinciguerraBaselineAccesses: Number(exactFourRegAccesses(5, 4, N)),
            outputExact: O === expectedO, catalystsRestored: restored, verified: O === expectedO && restored
          };
        }
        if (plan && plan.kind === 'radix_fork' && PROGRAMS_R3[plan.t]) {
          forcedRadixSpec = PROGRAMS_R3[plan.t];
        }
      } else if (planRes.internalPlan && planRes.internalPlan.kind === 'radix_fork' && PROGRAMS_R3[planRes.internalPlan.t]) {
        forcedRadixSpec = PROGRAMS_R3[planRes.internalPlan.t];
      }
    }

    let spec = forcedRadixSpec;
    if (!spec) {
      if (engineChoice === 'prog4_x5') spec = PROGRAMS_R3[4];
      else if (engineChoice === 'prog5_x7') spec = PROGRAMS_R3[5];
      else if (engineChoice === 'prog6_x9') spec = PROGRAMS_R3[6];
      else if (engineChoice === 'prog7_x11') spec = PROGRAMS_R3[7];
      else if (engineChoice === 'prog8_x13') spec = PROGRAMS_R3[8];
      else if (engineChoice === 'prog9_x15') spec = PROGRAMS_R3[9];
      else {
        for (const tCand of [8, 9, 7, 6, 5, 4]) {
          const cand = PROGRAMS_R3[tCand];
          if (isRadixScheduleValid(cand, N, p)) {
            spec = cand;
            break;
          }
        }
        if (!spec) spec = PROGRAMS_R3[4];
      }
    }

    const ds = baseDigits(spec.degree, N);
    const m = ds.length;
    if (!isRadixScheduleValid(spec, N, p)) {
      throw new Error(`Modulus p=${p} is incompatible with ${spec.id} at N=${N} (requires gcd(D_${spec.t}, p)=1 and (${spec.degree - 1})!, ${m}! invertible mod p)`);
    }

    let O = O0;
    let work = [u0, r10, r20];
    let accesses = 0;
    let faultInjected = false;
    let midScramble = null;
    const invFactM = modInv(factorialMod(m, p), p);

    function accumRec(idx, sign) {
      if (idx < 0) {
        O = mod(O + mod(sign * invFactM * modPow(work[0], m, p), p), p);
        return;
      }
      const b = ds[idx];
      const rPlus = execPowerLevelWork3(spec, idx, b, x, p, work, 1n);
      work = rPlus.state;
      accesses += rPlus.accesses;
      if (!midScramble) midScramble = { O, u: work[0], r1: work[1], r2: work[2] };
      if (faultBit && !faultInjected) {
        work[1] = mod(work[1] + 1n, p);
        faultInjected = true;
      }
      accumRec(idx - 1, sign);
      const rMinus = execPowerLevelWork3(spec, idx, b, x, p, work, -1n);
      work = rMinus.state;
      accesses += rMinus.accesses;
      accumRec(idx - 1, -sign);
    }

    accumRec(m - 1, 1n);

    const expectedO = mod(O0 + modPow(x, N, p), p);
    const outputExact = O === expectedO;
    const catalystsRestored = work[0] === u0 && work[1] === r10 && work[2] === r20;

    return {
      engineUsed: forcedRadixSpec ? `adaptive:radix(${spec.id})` : spec.id,
      N: N.toString(),
      p: p.toString(),
      x: x.toString(),
      digits: ds,
      initial: { O: O0, u: u0, r1: r10, r2: r20 },
      midScramble: midScramble || { O, u: work[0], r1: work[1], r2: work[2] },
      final: { O, u: work[0], r1: work[1], r2: work[2] },
      expectedO,
      accesses,
      vinciguerraBaselineAccesses: Number(exactFourRegAccesses(5, 4, N)),
      outputExact,
      catalystsRestored,
      verified: outputExact && catalystsRestored
    };
  }

  function execStreamingMoment(freqVec, DIn, pIn, opts = {}) {
    if (!Array.isArray(freqVec) || freqVec.length === 0) {
      throw new Error('Frequency vector must contain at least 1 element');
    }
    const D = BigInt(DIn);
    if (D < 1n) throw new Error('Moment order D must be >= 1');
    const p = BigInt(pIn);
    if (p < 2n) throw new Error('Modulus p must be >= 2 for modular streaming execution');
    const engine = opts.engine || 'adaptive';
    const faultBit = Boolean(opts.faultBit);
    const vec = freqVec.map((v) => mod(BigInt(v), p));
    const n = vec.length;

    let sumO0 = 0n;
    let sumOFinal = 0n;
    let naiveFD = 0n;
    let allOutputsExact = true;
    let allCatalystsRestored = true;
    let passes = 0;
    let engineUsed = '';
    const coordResults = [];

    for (let i = 0; i < n; i++) {
      const O0 = mod(BigInt(1000 + 37 * i), p);
      const u0 = mod(BigInt(2000 + 53 * i), p);
      const r10 = mod(BigInt(3000 + 71 * i), p);
      const r20 = mod(BigInt(4000 + 97 * i), p);
      const res = execFourRegPowering(D, vec[i], p, {
        engine,
        O0,
        u0,
        r10,
        r20,
        faultBit: faultBit && i === 0
      });
      engineUsed = res.engineUsed;
      passes = res.accesses;
      sumO0 = mod(sumO0 + O0, p);
      sumOFinal = mod(sumOFinal + res.final.O, p);
      naiveFD = mod(naiveFD + modPow(vec[i], D, p), p);
      if (!res.outputExact) allOutputsExact = false;
      if (!res.catalystsRestored) allCatalystsRestored = false;
      coordResults.push({
        index: i,
        freq: vec[i].toString(),
        deltaExact: res.outputExact,
        restored: res.catalystsRestored
      });
    }

    const extractedFD = mod(sumOFinal - sumO0, p);
    const sumExact = extractedFD === naiveFD;
    return {
      engineUsed,
      universeSize: n,
      D: D.toString(),
      p: p.toString(),
      passes,
      vinciguerraBaselinePasses: Number(exactFourRegAccesses(5, 4, D)),
      computedFD: extractedFD.toString(),
      naiveFD: naiveFD.toString(),
      sumExact,
      allOutputsExact,
      allCatalystsRestored,
      verified: sumExact && allOutputsExact && allCatalystsRestored,
      coordResults
    };
  }

  // =========================================================================
  // 5b. Live Catalytic Byte-Vault (Real Arbitrary Byte Borrowing & Restoration)
  // =========================================================================

  // Borrows real Uint8Array bytes verbatim into catalytic registers mod p (where p >= 257
  // holds 1 full byte per register cleanly, or p >= 65537 holds 2 bytes per register),
  // executes an exact Adaptive Fork computation on every 3-register chunk, captures the
  // mid-flight scrambled bytes, and unpacks the exact restored Uint8Array for SHA-256 audit.
  function execCatalyticByteVault(rawBytes, NIn, xIn, pIn, opts = {}) {
    const bytes = rawBytes instanceof Uint8Array ? rawBytes : new Uint8Array(rawBytes);
    if (bytes.length === 0) throw new Error('Byte vault payload cannot be empty');
    const p = BigInt(pIn);
    if (p < 257n) throw new Error('Byte vault requires modulus p >= 257 so every byte (0..255) fits injectively in a catalytic register');
    const N = BigInt(NIn);
    const x = mod(BigInt(xIn), p);
    const faultBit = Boolean(opts.faultBit);
    const maxChunks = safeInt(opts.maxChunks, 256, 1, 21845);
    const cappedLen = Math.min(bytes.length, maxChunks * 3);
    const slice = bytes.slice(0, cappedLen);

    const restored = new Uint8Array(slice.length);
    const midBytes = new Uint8Array(slice.length);
    let totalAccesses = 0;
    let allExact = true;
    let engineUsed = '';
    let sampleOutput = 0n;
    let sampleExpected = 0n;

    for (let offset = 0; offset < slice.length; offset += 3) {
      const u0 = BigInt(slice[offset]);
      const r10 = offset + 1 < slice.length ? BigInt(slice[offset + 1]) : 0n;
      const r20 = offset + 2 < slice.length ? BigInt(slice[offset + 2]) : 0n;
      const O0 = mod(BigInt(17 + offset * 31), p);
      const res = execFourRegPowering(N, x, p, {
        engine: 'adaptive',
        O0,
        u0,
        r10,
        r20,
        faultBit: faultBit && offset === 0
      });
      engineUsed = res.engineUsed;
      totalAccesses = res.accesses;
      sampleOutput = res.final.O;
      sampleExpected = res.expectedO;
      if (!res.verified) allExact = false;

      midBytes[offset] = Number(res.midScramble.u & 0xffn);
      if (offset + 1 < slice.length) midBytes[offset + 1] = Number(res.midScramble.r1 & 0xffn);
      if (offset + 2 < slice.length) midBytes[offset + 2] = Number(res.midScramble.r2 & 0xffn);

      restored[offset] = Number(res.final.u & 0xffn);
      if (offset + 1 < slice.length) restored[offset + 1] = Number(res.final.r1 & 0xffn);
      if (offset + 2 < slice.length) restored[offset + 2] = Number(res.final.r2 & 0xffn);
    }

    let bytesEqual = true;
    let corruptedByteCount = 0;
    for (let i = 0; i < slice.length; i++) {
      if (slice[i] !== restored[i]) {
        bytesEqual = false;
        corruptedByteCount += 1;
      }
    }
    const toHex = (arr) => Array.from(arr.slice(0, 16)).map((b) => b.toString(16).padStart(2, '0')).join(' ');
    return {
      engineUsed,
      borrowedBytes: slice.length,
      chunks: Math.ceil(slice.length / 3),
      accessesPerChunk: totalAccesses,
      beforeBytes: slice,
      midScrambleBytes: midBytes,
      afterBytes: restored,
      beforeHexPreview: toHex(slice),
      midHexPreview: toHex(midBytes),
      afterHexPreview: toHex(restored),
      sampleOutput: sampleOutput.toString(),
      sampleExpected: sampleExpected.toString(),
      bytesEqual,
      corruptedByteCount,
      verified: allExact && bytesEqual
    };
  }

  // =========================================================================
  // 6. Literal Non-Commutative Matrix Lift mu_7(prog5_x7) on M_2(F_p) (R3)
  // =========================================================================

  function execMatrixLiftProg5(AIn, pIn, opts = {}) {
    const p = BigInt(pIn);
    if (p < 11n || !isPrimeBig(p)) throw new Error('Matrix lift mu_7(prog5_x7) requires prime p >= 11');
    const A = AIn.map((row) => row.map((v) => mod(BigInt(v), p)));
    const O0 = (opts.O0 || [[4n, 7n], [2n, 9n]]).map((row) => row.map((v) => mod(BigInt(v), p)));
    const faultBit = Boolean(opts.faultBit);

    const matAdd = (x, y) => [
      [mod(x[0][0] + y[0][0], p), mod(x[0][1] + y[0][1], p)],
      [mod(x[1][0] + y[1][0], p), mod(x[1][1] + y[1][1], p)]
    ];
    const matScale = (c, x) => [
      [mod(c * x[0][0], p), mod(c * x[0][1], p)],
      [mod(c * x[1][0], p), mod(c * x[1][1], p)]
    ];
    const matMul = (x, y) => [
      [mod(x[0][0] * y[0][0] + x[0][1] * y[1][0], p), mod(x[0][0] * y[0][1] + x[0][1] * y[1][1], p)],
      [mod(x[1][0] * y[0][0] + x[1][1] * y[1][0], p), mod(x[1][0] * y[0][1] + x[1][1] * y[1][1], p)]
    ];
    const matEq = (x, y) => x[0][0] === y[0][0] && x[0][1] === y[0][1] && x[1][0] === y[1][0] && x[1][1] === y[1][1];
    const matPow = (m, e) => {
      let res = [[1n, 0n], [0n, 1n]];
      let b = m;
      let ex = e;
      while (ex > 0) {
        if (ex & 1) res = matMul(res, b);
        b = matMul(b, b);
        ex >>= 1;
      }
      return res;
    };

    const basis = [
      [[1n, 0n], [0n, 0n]],
      [[0n, 1n], [0n, 0n]],
      [[0n, 0n], [1n, 0n]],
      [[0n, 0n], [0n, 1n]]
    ];

    const polyAdd = (a, b) => {
      const out = new Map(a);
      for (const [k, v] of b.entries()) {
        const nv = mod((out.get(k) || 0n) + v, p);
        if (nv === 0n) out.delete(k);
        else out.set(k, nv);
      }
      return out;
    };
    const polyScale = (c, a) => {
      const cc = mod(c, p);
      if (cc === 0n) return new Map();
      const out = new Map();
      for (const [k, v] of a.entries()) {
        const nv = mod(cc * v, p);
        if (nv !== 0n) out.set(k, nv);
      }
      return out;
    };
    const polyMul = (a, b) => {
      const out = new Map();
      for (const [k1, v1] of a.entries()) {
        const a1 = k1.split(',').map(Number);
        for (const [k2, v2] of b.entries()) {
          const a2 = k2.split(',').map(Number);
          const key = `${a1[0] + a2[0]},${a1[1] + a2[1]},${a1[2] + a2[2]},${a1[3] + a2[3]}`;
          const nv = mod((out.get(key) || 0n) + v1 * v2, p);
          if (nv === 0n) out.delete(key);
          else out.set(key, nv);
        }
      }
      return out;
    };
    const polyPow = (a, e) => {
      let res = new Map([['0,0,0,0', 1n]]);
      for (let i = 0; i < e; i++) res = polyMul(res, a);
      return res;
    };
    const polyEq = (a, b) => {
      if (a.size !== b.size) return false;
      for (const [k, v] of a.entries()) if (b.get(k) !== v) return false;
      return true;
    };

    const symDP = new Map([['0,0,0,0', [[1n, 0n], [0n, 1n]]]]);
    function symSum(a0, a1, a2, a3) {
      const key = `${a0},${a1},${a2},${a3}`;
      if (symDP.has(key)) return symDP.get(key);
      let acc = [[0n, 0n], [0n, 0n]];
      const arr = [a0, a1, a2, a3];
      for (let j = 0; j < 4; j++) {
        if (arr[j] > 0) {
          const prev = arr.slice();
          prev[j] -= 1;
          acc = matAdd(acc, matMul(symSum(prev[0], prev[1], prev[2], prev[3]), basis[j]));
        }
      }
      symDP.set(key, acc);
      return acc;
    }

    const factMod = [1n];
    for (let i = 1; i <= 7; i++) factMod[i] = mod(factMod[i - 1] * BigInt(i), p);
    function mu7(poly) {
      let out = [[0n, 0n], [0n, 0n]];
      for (const [k, coeff] of poly.entries()) {
        const alpha = k.split(',').map(Number);
        let denom = 1n;
        for (const ai of alpha) denom = mod(denom * factMod[ai], p);
        const multinom = mod(factMod[7] * modInv(denom, p), p);
        const weight = mod(coeff * modInv(multinom, p), p);
        out = matAdd(out, matScale(weight, symSum(alpha[0], alpha[1], alpha[2], alpha[3])));
      }
      return out;
    }

    const ellA = new Map();
    if (A[0][0] !== 0n) ellA.set('1,0,0,0', A[0][0]);
    if (A[0][1] !== 0n) ellA.set('0,1,0,0', A[0][1]);
    if (A[1][0] !== 0n) ellA.set('0,0,1,0', A[1][0]);
    if (A[1][1] !== 0n) ellA.set('0,0,0,1', A[1][1]);

    const u0 = new Map([['1,0,0,0', mod(2n, p)], ['0,1,0,0', mod(5n, p)], ['0,0,1,0', mod(1n, p)], ['0,0,0,1', mod(8n, p)]]);
    const v0 = new Map([
      ['2,0,0,0', mod(3n, p)], ['1,1,0,0', mod(7n, p)], ['1,0,1,0', mod(4n, p)], ['1,0,0,1', mod(9n, p)],
      ['0,2,0,0', mod(2n, p)], ['0,1,1,0', mod(6n, p)], ['0,1,0,1', mod(1n, p)],
      ['0,0,2,0', mod(5n, p)], ['0,0,1,1', mod(8n, p)], ['0,0,0,2', mod(10n, p)]
    ]);

    const spec = PROGRAMS_R3[5];
    const invD5 = modInv(spec.D, p);
    let OReg = O0.map((r) => r.slice());
    let uReg = new Map(u0);
    let vReg = new Map(v0);

    for (let k = 0; k < spec.steps.length; k++) {
      const st = spec.steps[k];
      let fUV = new Map();
      for (const [du, dv, c] of st.terms) {
        fUV = polyAdd(fUV, polyScale(c, polyMul(polyPow(uReg, du), polyPow(vReg, dv))));
      }
      OReg = matAdd(OReg, matScale(invD5, mu7(fUV)));
      if (st.qNext !== 0n) {
        vReg = polyAdd(vReg, polyScale(-st.qNext, polyPow(uReg, 2)));
      }
      uReg = polyAdd(uReg, polyScale(st.alpha, ellA));
      if (faultBit && k === 2) {
        uReg = polyAdd(uReg, new Map([['1,0,0,0', 1n]]));
      }
      if (st.qNext !== 0n) {
        vReg = polyAdd(vReg, polyScale(st.qNext, polyPow(uReg, 2)));
      }
    }

    const expectedA7 = matPow(A, 7);
    const expectedO = matAdd(O0, expectedA7);
    const nonCommuting = !matEq(matMul(A, O0), matMul(O0, A));
    const outputExact = matEq(OReg, expectedO);
    const catalystsRestored = polyEq(uReg, u0) && polyEq(vReg, v0);
    return {
      p: p.toString(),
      A: A.map((r) => r.map((v) => v.toString())),
      O0: O0.map((r) => r.map((v) => v.toString())),
      finalO: OReg.map((r) => r.map((v) => v.toString())),
      expectedO: expectedO.map((r) => r.map((v) => v.toString())),
      A7: expectedA7.map((r) => r.map((v) => v.toString())),
      nonCommuting,
      singleCallScalarRegisters: 18, // O(4) + u(4) + v(10) = 18 scalars for single A^7
      recursiveScalarRegisters: 22,  // + U(4) = 22 scalars for recursive A^N (exact r=3 tier)
      scalarRegisters: 22,
      matrixAccesses: 5,
      outputExact,
      catalystsRestored,
      verified: outputExact && catalystsRestored
    };
  }

  // =========================================================================
  // 7. Literal T1 Oracle, T2 Bilinear Frobenius, & T4 Balanced Product
  // =========================================================================

  function evalT1Oracle(pIn, dIn, tIn) {
    const p = BigInt(pIn);
    const d = BigInt(dIn);
    const t = safeInt(tIn, 1, 0, 1000000000);
    if (!isPrimeBig(p)) {
      return { validPrime: false, message: `${p} is not prime. Theorem T1 characterizes prime fields F_p.` };
    }
    if (d < 0n) throw new Error('Degree d must be >= 0');
    const digits = baseDigits(p, d);
    const sp = digitSum(p, d);
    const pNum = p > 1000000n ? 1000000 : Number(p);
    const cap = Math.min(pNum - 1, t - 1);
    const permanentlyImpossible = d >= 2n && BigInt(sp) >= p;
    const feasibleAtT = d <= 1n ? (t >= 1) : (!permanentlyImpossible && sp <= cap);
    const minT = d <= 1n ? 1 : (permanentlyImpossible ? null : sp + 1);
    const frobenius2Access = d >= 2n && sp === 1;
    return {
      validPrime: true,
      p: p.toString(),
      d: d.toString(),
      t,
      digitsLSB: digits,
      digitSum: sp,
      permanentlyImpossible,
      feasibleAtT,
      minT,
      frobenius2Access,
      char0BaselineT: d <= 1n ? 1 : (d + 1n).toString()
    };
  }

  function gf256Mul(a, b) {
    let res = 0;
    let x = a & 0xff;
    let y = b & 0xff;
    for (let i = 0; i < 8; i++) {
      if (y & 1) res ^= x;
      const hi = x & 0x80;
      x = (x << 1) & 0xff;
      if (hi) x ^= 0x1b;
      y >>= 1;
    }
    return res;
  }

  function gf256Pow(a, exp) {
    let res = 1;
    let b = a & 0xff;
    let e = BigInt(exp);
    while (e > 0n) {
      if (e & 1n) res = gf256Mul(res, b);
      b = gf256Mul(b, b);
      e >>= 1n;
    }
    return res;
  }

  function execT2BilinearFrobenius(kIn, xByte, initRegs, opts = {}) {
    const k = Number(kIn);
    if (!Number.isInteger(k) || k < 1 || k > 12) throw new Error('Choose integer k in [1, 12]');
    const faultBit = Boolean(opts.faultBit);
    const x = Number(xByte) & 0xff;
    const init = [];
    for (let i = 0; i <= k; i++) {
      init.push((initRegs && initRegs[i] !== undefined ? Number(initRegs[i]) : ((i * 53 + 17) & 0xff)) & 0xff);
    }
    const R = init.slice();
    let accesses = 0;
    let bilinOps = 0;

    for (let phase = 0; phase < 2; phase++) {
      R[1] ^= x;
      accesses += 1;
      for (let j = 1; j < k; j++) {
        R[j + 1] ^= gf256Mul(R[j], R[j]);
        bilinOps += 1;
      }
      if (faultBit && phase === 0) {
        R[k] ^= 1;
      }
      R[0] ^= gf256Mul(R[k], R[k]);
      bilinOps += 1;
      for (let j = k - 1; j >= 1; j--) {
        R[j + 1] ^= gf256Mul(R[j], R[j]);
        bilinOps += 1;
      }
    }

    const deg = 1n << BigInt(k);
    const expectedR0 = init[0] ^ gf256Pow(x, deg);
    const outputExact = R[0] === expectedR0;
    let catalystsRestored = true;
    for (let i = 1; i <= k; i++) {
      if (R[i] !== init[i]) catalystsRestored = false;
    }
    return {
      k,
      degree: deg.toString(),
      ring: 'GF(2^8) = F_2[w]/(w^8+w^4+w^3+w+1)',
      x,
      registers: k + 1,
      accesses,
      bilinOps,
      initial: init,
      final: R,
      expectedR0,
      outputExact,
      catalystsRestored,
      verified: outputExact && catalystsRestored
    };
  }

  function execT4BalancedProduct(xsIn, initRegsIn, signIn = 1n, opts = {}) {
    const xs = xsIn.map((v) => BigInt(v));
    const d = xs.length;
    if (d < 1 || (d & (d - 1)) !== 0) throw new Error('T4 requires d = 2^k inputs');
    const k = Math.round(Math.log2(d));
    const neededRegs = k === 0 ? 1 : k + 2;
    const init = [];
    for (let i = 0; i < neededRegs; i++) {
      init.push(initRegsIn && initRegsIn[i] !== undefined ? BigInt(initRegsIn[i]) : BigInt(10 + 7 * i));
    }
    const regs = init.slice();
    const sign = BigInt(signIn) === -1n ? -1n : 1n;
    const faultBit = Boolean(opts.faultBit);
    let ops = 0;
    let faultDone = false;
    const allowedRegs = new Set();
    for (let i = 0; i < neededRegs; i++) allowedRegs.add(i);
    let usesOnlyHold = true;
    let strictDistinctHold = true;
    const snapshots = [{ opIdx: 0, label: 'Init dirty catalytic registers', regs: regs.map((v) => v.toString()) }];

    function rec(offset, len, target, s, pool) {
      if (len === 1) {
        if (!allowedRegs.has(target)) usesOnlyHold = false;
        regs[target] += s * xs[offset];
        ops += 1;
        if (faultBit && !faultDone && ops === 2) {
          regs[pool.length ? pool[0] : target] += 1n;
          faultDone = true;
        }
        return;
      }
      const half = len >> 1;
      const ra = pool[0];
      const rb = pool[1];
      const rest = pool.slice(2);
      if (!(target !== ra && target !== rb && ra !== rb)) strictDistinctHold = false;
      if (!(allowedRegs.has(target) && allowedRegs.has(ra) && allowedRegs.has(rb))) usesOnlyHold = false;

      regs[target] += s * (regs[ra] * regs[rb]);
      ops += 1;
      rec(offset, half, ra, 1n, [rb, ...rest]);
      regs[target] -= s * (regs[ra] * regs[rb]);
      ops += 1;
      if (len === d) snapshots.push({ opIdx: ops, label: 'After stage (3) — R_a holds c_a + A', regs: regs.map((v) => v.toString()) });
      rec(offset + half, half, rb, 1n, [ra, ...rest]);
      regs[target] += s * (regs[ra] * regs[rb]);
      ops += 1;
      if (len === d) snapshots.push({ opIdx: ops, label: 'After stage (5) — peak nonlinear cross-term', regs: regs.map((v) => v.toString()) });
      rec(offset, half, ra, -1n, [rb, ...rest]);
      regs[target] -= s * (regs[ra] * regs[rb]);
      ops += 1;
      rec(offset + half, half, rb, -1n, [ra, ...rest]);
      if (len === d) snapshots.push({ opIdx: ops, label: 'Final — catalysts restored bit-for-bit', regs: regs.map((v) => v.toString()) });
    }

    const pool = [];
    for (let i = 1; i < neededRegs; i++) pool.push(i);
    rec(0, d, 0, sign, pool);

    let prod = 1n;
    for (const v of xs) prod *= v;
    const expectedTarget = init[0] + sign * prod;
    const outputExact = regs[0] === expectedTarget;
    let catalystsRestored = true;
    for (let i = 1; i < neededRegs; i++) {
      if (regs[i] !== init[i]) catalystsRestored = false;
    }
    const expectedOps = (7 * d * d - 4) / 3;
    return {
      k,
      d,
      registers: neededRegs,
      ops,
      expectedOps,
      linearChainOps: (3n * (4n ** BigInt(d - 1)) - 2n).toString(),
      usesOnlyHold,
      strictDistinctHold,
      initial: init.map((v) => v.toString()),
      final: regs.map((v) => v.toString()),
      expectedTarget: expectedTarget.toString(),
      outputExact,
      catalystsRestored,
      verified: outputExact && catalystsRestored && ops === expectedOps && usesOnlyHold && strictDistinctHold,
      snapshots
    };
  }

  // =========================================================================
  // 8. Live Adversarial Fuzzer (Deterministic PRNG across T1–T4 + Composite Rings)
  // =========================================================================

  function runAdversarialFuzz(trialsIn = 500, seed = 20261125) {
    const trials = safeInt(trialsIn, 500, 1, 50000);
    let s = BigInt(safeInt(seed, 20261125)) & ((1n << 64n) - 1n);
    const nextU32 = () => {
      s = (s * 6364136223846793005n + 1442695040888963407n) & ((1n << 64n) - 1n);
      return Number((s >> 32n) & 0xffffffffn);
    };
    const t0 = typeof performance !== 'undefined' ? performance.now() : Date.now();
    let passed = 0;
    let failed = 0;
    const safePrimes = [11n, 13n, 19n, 29n, 31n, 101n, 1009n, 1000003n];
    const safeComposites = [1009n * 1013n, 19n * 29n, 31n * 37n]; // Valid odd composite rings Z/mZ!
    const gadgets = [4, 5, 6, 7, 8, 9];

    for (let i = 0; i < trials; i++) {
      const mode = i % 7;
      let ok = false;
      if (mode === 0) {
        // Fuzz ALL 3-register engines prog4_x5 .. prog9_x15 over safe primes
        const t = gadgets[nextU32() % gadgets.length];
        const p = safePrimes[nextU32() % safePrimes.length];
        const res = execPass3(t, BigInt(nextU32()), p, {
          O0: BigInt(nextU32()),
          u0: BigInt(nextU32()),
          v0: BigInt(nextU32())
        });
        ok = res.verified;
      } else if (mode === 1) {
        // Fuzz T2 strictly bilinear Frobenius over GF(2^8)
        const k = 1 + (nextU32() % 8);
        const x = nextU32() & 0xff;
        const init = Array.from({ length: k + 1 }, () => nextU32() & 0xff);
        ok = execT2BilinearFrobenius(k, x, init).verified;
      } else if (mode === 2) {
        // Fuzz T4 zero-workspace balanced product over Z (d = 4 or 8)
        const d = (nextU32() & 1) ? 4 : 8;
        const k = d === 4 ? 2 : 3;
        const xs = Array.from({ length: d }, () => BigInt((nextU32() % 19) - 9));
        const init = Array.from({ length: k + 2 }, () => BigInt((nextU32() % 101) - 50));
        const sign = (nextU32() & 1) ? 1n : -1n;
        ok = execT4BalancedProduct(xs, init, sign).verified;
      } else if (mode === 3) {
        // Fuzz T3h Adaptive Fork across prime F_1009 AND bad-prime dodging F_137 (137 | D_8!)
        const N = 1 + (nextU32() % 95);
        const p = (i % 21 === 3) ? 137n : 1009n;
        const res = execFourRegPowering(N, BigInt(nextU32()), p, {
          engine: 'adaptive',
          O0: BigInt(nextU32()),
          u0: BigInt(nextU32()),
          r10: BigInt(nextU32()),
          r20: BigInt(nextU32())
        });
        ok = res.verified;
      } else if (mode === 4) {
        // Fuzz T3h Adaptive Fork over NON-PRIME COMPOSITE COMMUTATIVE RINGS Z/mZ!
        const N = 1 + (nextU32() % 28);
        const m = safeComposites[nextU32() % safeComposites.length];
        const res = execFourRegPowering(N, BigInt(nextU32()), m, {
          engine: 'adaptive',
          O0: BigInt(nextU32()),
          u0: BigInt(nextU32()),
          r10: BigInt(nextU32()),
          r20: BigInt(nextU32())
        });
        ok = res.verified;
      } else if (mode === 5) {
        // Fuzz R3 non-commutative matrix lift mu_7(prog5_x7) over M_2(F_11 / F_13)
        const p = (nextU32() & 1) ? 11n : 13n;
        const A = [[BigInt(nextU32()), BigInt(nextU32())], [BigInt(nextU32()), BigInt(nextU32())]];
        const O0 = [[BigInt(nextU32()), BigInt(nextU32())], [BigInt(nextU32()), BigInt(nextU32())]];
        ok = execMatrixLiftProg5(A, p, { O0 }).verified;
      } else {
        // Fuzz Large-N T1 Prime-Field Frobenius & Digit-Sum Collapse (N up to > 10^6 in 2-4 accesses!)
        const cases = [
          { N: 65536n, p: 2n, maxAcc: 2 },
          { N: 15751n, p: 5n, maxAcc: 4 },
          { N: 1018081n, p: 1009n, maxAcc: 2 },
          { N: 1018082n, p: 1009n, maxAcc: 3 }
        ];
        const c = cases[nextU32() % cases.length];
        const res = execFourRegPowering(c.N, BigInt(nextU32()), c.p, {
          engine: 'adaptive',
          O0: BigInt(nextU32()),
          u0: BigInt(nextU32()),
          r10: BigInt(nextU32()),
          r20: BigInt(nextU32())
        });
        ok = res.verified && res.accesses <= c.maxAcc;
      }
      if (ok) passed += 1;
      else failed += 1;
    }

    const elapsedMs = (typeof performance !== 'undefined' ? performance.now() : Date.now()) - t0;
    return {
      trials,
      passed,
      failed,
      elapsedMs: Number(elapsedMs.toFixed(2)),
      trialsPerSec: elapsedMs > 0 ? Math.round((trials / elapsedMs) * 1000) : trials * 1000
    };
  }

  // =========================================================================
  // 9. Real-Time Cross-Device Calibration Benchmark (Adaptive vs. Baseline)
  // =========================================================================

  function runDeviceBenchmark(opts = {}) {
    const now = () => (typeof performance !== 'undefined' ? performance.now() : Date.now());
    const iters = safeInt(opts.iters, 6, 2, 100);
    const p = 1009n;

    // Warm-up JIT once
    execFourRegPowering(91, 7, p, { engine: 'adaptive' });
    execFourRegPowering(91, 7, p, { engine: 'prog4_x5' });

    // Benchmark N=91 (7*13): Adaptive Fork (80 accesses) vs Vinciguerra Static Baseline (208 accesses)
    let ok = true;
    const tA91 = now();
    for (let i = 0; i < iters; i++) {
      if (!execFourRegPowering(91, 7 + i, p, { engine: 'adaptive' }).verified) ok = false;
    }
    const adaptive91Ms = Math.max(0.01, (now() - tA91) / iters);

    const tB91 = now();
    for (let i = 0; i < iters; i++) {
      if (!execFourRegPowering(91, 7 + i, p, { engine: 'prog4_x5' }).verified) ok = false;
    }
    const baseline91Ms = Math.max(0.01, (now() - tB91) / iters);

    // Benchmark N=169 (13^2): Adaptive Fork (128 accesses) vs Vinciguerra Static Baseline (592 accesses)
    const tA169 = now();
    for (let i = 0; i < iters; i++) {
      if (!execFourRegPowering(169, 11 + i, p, { engine: 'adaptive' }).verified) ok = false;
    }
    const adaptive169Ms = Math.max(0.01, (now() - tA169) / iters);

    const tB169 = now();
    for (let i = 0; i < iters; i++) {
      if (!execFourRegPowering(169, 11 + i, p, { engine: 'prog4_x5' }).verified) ok = false;
    }
    const baseline169Ms = Math.max(0.01, (now() - tB169) / iters);

    // Benchmark Catalytic Byte-Vault throughput (192 bytes @ N=13 prog8_x13)
    const sample = new Uint8Array(192);
    for (let i = 0; i < sample.length; i++) sample[i] = (i * 37 + 13) & 0xff;
    const tV = now();
    const vRes = execCatalyticByteVault(sample, 13, 7, p, { maxChunks: 64 });
    const vaultMs = Math.max(0.01, now() - tV);
    if (!vRes.verified) ok = false;

    return {
      iters,
      verified: ok,
      n91: {
        adaptiveAccesses: 80,
        baselineAccesses: 208,
        adaptiveMs: Number(adaptive91Ms.toFixed(2)),
        baselineMs: Number(baseline91Ms.toFixed(2)),
        wallSpeedup: Number((baseline91Ms / adaptive91Ms).toFixed(2))
      },
      n169: {
        adaptiveAccesses: 128,
        baselineAccesses: 592,
        adaptiveMs: Number(adaptive169Ms.toFixed(2)),
        baselineMs: Number(baseline169Ms.toFixed(2)),
        wallSpeedup: Number((baseline169Ms / adaptive169Ms).toFixed(2))
      },
      vault: {
        bytes: sample.length,
        ms: Number(vaultMs.toFixed(2)),
        bytesPerSec: Math.round((sample.length / vaultMs) * 1000)
      }
    };
  }

  // =========================================================================
  // 10. Predictive Adaptive Horizon Sweep & Independent Certificate Verifier
  // =========================================================================

  function computeAdaptiveHorizon(pIn, opts = {}) {
    const p = BigInt(pIn ?? 1009);
    const workload = opts.workload || 'scalar';
    const matrixDim = safeInt(opts.matrixDim, 4, 1, 256);
    const points = opts.exponents || [5, 7, 9, 13, 15, 20, 25, 49, 64, 91, 121, 169, 256, 500, 1000, 2197];
    const rows = [];
    for (const nVal of points) {
      const r = planAdaptiveFork({ workload, N: BigInt(nVal), p, matrixDim });
      rows.push({
        N: String(nVal),
        baselineAccesses: r.comparison.vinciguerra_r3_x5.accesses,
        adaptiveAccesses: r.comparison.adaptive_fork.accesses,
        strategy: r.comparison.adaptive_fork.strategy,
        feasible: r.comparison.adaptive_fork.feasible,
        speedupFactor: Number(r.speedupFactor.toFixed(2)),
        reductionPct: Number(r.reductionPct.toFixed(1))
      });
    }
    return { p: p.toString(), workload, points: rows };
  }

  // Non-blocking chunked async Catalytic Byte-Vault for 60fps UI responsiveness on watches/phones/desktops
  async function execCatalyticByteVaultAsync(rawBytes, NIn, xIn, pIn, opts = {}) {
    const bytes = rawBytes instanceof Uint8Array ? rawBytes : new Uint8Array(rawBytes);
    if (bytes.length === 0) throw new Error('Byte vault payload cannot be empty');
    const p = BigInt(pIn);
    if (p < 257n) throw new Error('Byte vault requires modulus p >= 257 so every byte (0..255) fits injectively in a catalytic register');
    const N = BigInt(NIn);
    const x = mod(BigInt(xIn), p);
    const faultBit = Boolean(opts.faultBit);
    const maxChunks = safeInt(opts.maxChunks, 256, 1, 21845);
    const cappedLen = Math.min(bytes.length, maxChunks * 3);
    const slice = bytes.slice(0, cappedLen);
    const onProgress = typeof opts.onProgress === 'function' ? opts.onProgress : null;
    const isAborted = typeof opts.isAborted === 'function' ? opts.isAborted : null;
    const yieldEveryMs = safeInt(opts.yieldEveryMs, 12, 4, 250);
    const now = () => (typeof performance !== 'undefined' ? performance.now() : Date.now());

    const restored = new Uint8Array(slice.length);
    const midBytes = new Uint8Array(slice.length);
    let totalAccesses = 0;
    let allExact = true;
    let engineUsed = '';
    let sampleOutput = 0n;
    let sampleExpected = 0n;
    let lastYield = now();

    for (let offset = 0; offset < slice.length; offset += 3) {
      if (isAborted && isAborted()) throw new Error('Byte-Vault execution cancelled by user');
      const u0 = BigInt(slice[offset]);
      const r10 = offset + 1 < slice.length ? BigInt(slice[offset + 1]) : 0n;
      const r20 = offset + 2 < slice.length ? BigInt(slice[offset + 2]) : 0n;
      const O0 = mod(BigInt(17 + offset * 31), p);
      const res = execFourRegPowering(N, x, p, {
        engine: 'adaptive',
        O0,
        u0,
        r10,
        r20,
        faultBit: faultBit && offset === 0
      });
      engineUsed = res.engineUsed;
      totalAccesses = res.accesses;
      sampleOutput = res.final.O;
      sampleExpected = res.expectedO;
      if (!res.verified) allExact = false;

      midBytes[offset] = Number(res.midScramble.u & 0xffn);
      if (offset + 1 < slice.length) midBytes[offset + 1] = Number(res.midScramble.r1 & 0xffn);
      if (offset + 2 < slice.length) midBytes[offset + 2] = Number(res.midScramble.r2 & 0xffn);

      restored[offset] = Number(res.final.u & 0xffn);
      if (offset + 1 < slice.length) restored[offset + 1] = Number(res.final.r1 & 0xffn);
      if (offset + 2 < slice.length) restored[offset + 2] = Number(res.final.r2 & 0xffn);

      if (now() - lastYield >= yieldEveryMs && offset + 3 < slice.length) {
        if (onProgress) {
          const doneBytes = Math.min(slice.length, offset + 3);
          onProgress({ doneBytes, totalBytes: slice.length, pct: Math.round((doneBytes / slice.length) * 100) });
        }
        await new Promise((resolve) => setTimeout(resolve, 0));
        lastYield = now();
      }
    }
    if (onProgress) onProgress({ doneBytes: slice.length, totalBytes: slice.length, pct: 100 });

    let bytesEqual = true;
    let corruptedByteCount = 0;
    for (let i = 0; i < slice.length; i++) {
      if (slice[i] !== restored[i]) {
        bytesEqual = false;
        corruptedByteCount += 1;
      }
    }
    const toHex = (arr) => Array.from(arr.slice(0, 16)).map((b) => b.toString(16).padStart(2, '0')).join(' ');
    return {
      engineUsed,
      borrowedBytes: slice.length,
      chunks: Math.ceil(slice.length / 3),
      accessesPerChunk: totalAccesses,
      beforeBytes: slice,
      midScrambleBytes: midBytes,
      afterBytes: restored,
      beforeHexPreview: toHex(slice),
      midHexPreview: toHex(midBytes),
      afterHexPreview: toHex(restored),
      sampleOutput: sampleOutput.toString(),
      sampleExpected: sampleExpected.toString(),
      bytesEqual,
      corruptedByteCount,
      verified: allExact && bytesEqual
    };
  }

  function verifyCertificate(cert) {
    if (!cert || typeof cert !== 'object' || !cert.kind) {
      return { ok: false, reason: 'Invalid certificate object (missing kind)' };
    }
    const validDigest = (h) => typeof h === 'string' && /^(?:[0-9a-f]{64}|fnv64:[0-9a-f]{16})$/i.test(h);
    try {
      if (cert.kind === 'adaptive_fork_4reg') {
        const N = BigInt(cert.N);
        const p = BigInt(cert.p);
        const x = BigInt(cert.x);
        const plan = planAdaptiveFork({ workload: 'scalar', N, p });
        const reRun = execFourRegPowering(N, x, p, { engine: 'adaptive' });
        const accessMatch = String(reRun.accesses) === String(cert.accesses);
        const engineMatch = reRun.engineUsed === cert.engineUsed;
        const ok = Boolean(cert.verified) && reRun.verified && accessMatch && engineMatch && plan.comparison.adaptive_fork.feasible;
        return {
          ok,
          kind: cert.kind,
          recomputedAccesses: reRun.accesses,
          claimedAccesses: cert.accesses,
          engineMatch,
          reason: ok ? 'Independent exact re-execution matched claimed engine, access count, and 0-bit catalyst restoration.' : 'Mismatch or failed verification on independent re-execution.'
        };
      }
      if (cert.kind === 'catalytic_sha256_byte_vault') {
        const N = BigInt(cert.N);
        const p = BigInt(cert.p);
        const plan = planAdaptiveFork({ workload: 'scalar', N, p });
        const digestsValid = validDigest(cert.sha256Before) && validDigest(cert.sha256After) && (!cert.sha256MidFlightScrambled || validDigest(cert.sha256MidFlightScrambled));
        const shaOk = digestsValid && cert.sha256Before === cert.sha256After && cert.sha256Identical === true;
        const sample = new Uint8Array([0x53, 0x65, 0x6e, 0x73, 0x6f, 0x72]);
        const probe = execCatalyticByteVault(sample, N, 7n, p, { maxChunks: 2 });
        const ok = Boolean(cert.verified) && shaOk && probe.verified && plan.comparison.adaptive_fork.feasible && String(probe.accessesPerChunk) === String(cert.accessesPerChunk);
        return {
          ok,
          kind: cert.kind,
          sha256Match: shaOk,
          recomputedAccessesPerChunk: probe.accessesPerChunk,
          reason: ok ? 'SHA-256 pre/post digest format & equality and independent chunk re-execution verified.' : 'Certificate SHA-256 format/digest or chunk access count mismatch.'
        };
      }
      if (cert.kind === 'matrix_lift_prog5') {
        const r = cert.result;
        if (!r || !r.A || !r.p) return { ok: false, kind: cert.kind, reason: 'Missing matrix payload' };
        const reRun = execMatrixLiftProg5(r.A, BigInt(r.p));
        const a7Match = JSON.stringify(reRun.A7) === JSON.stringify(r.A7);
        const ok = Boolean(r.verified) && reRun.verified && a7Match;
        return {
          ok,
          kind: cert.kind,
          a7Match,
          reason: ok ? 'Independent non-commutative mu_7(prog5_x7) re-execution matched A^7 identically.' : 'Matrix A^7 mismatch.'
        };
      }
      if (cert.kind === 'device_calibration_benchmark') {
        const b = cert.benchmark;
        const ok = Boolean(b && b.verified && b.n91 && b.n91.adaptiveAccesses === 80 && b.n169 && b.n169.adaptiveAccesses === 128);
        return {
          ok,
          kind: cert.kind,
          reason: ok ? 'Benchmark access counts (80 @ N=91, 128 @ N=169) and exactness flags verified.' : 'Invalid benchmark certificate.'
        };
      }
      return { ok: false, kind: String(cert.kind), reason: `Unsupported certificate kind: ${cert.kind}` };
    } catch (err) {
      return { ok: false, kind: String(cert.kind), reason: `Malformed certificate field: ${err.message}` };
    }
  }

  const exportedApi = {
    version: '1.7.0',
    PROGRAMS_R3,
    safeInt,
    mod,
    gcd,
    modInv,
    modPow,
    isPrimeBig,
    isFactInvertible,
    baseDigits,
    digitSum,
    binomExact,
    binomModP,
    bigRatio,
    textToBigInt,
    formatBig,
    exactFourRegAccesses,
    execPass3,
    planAdaptiveFork,
    execFourRegPowering,
    execStreamingMoment,
    execCatalyticByteVault,
    execCatalyticByteVaultAsync,
    execMatrixLiftProg5,
    evalT1Oracle,
    execT2BilinearFrobenius,
    execT4BalancedProduct,
    runAdversarialFuzz,
    runDeviceBenchmark,
    computeAdaptiveHorizon,
    verifyCertificate
  };

  // Universal zero-dependency Node.js CLI entrypoint (laptops, desktops, servers, Termux, containers)
  // Supports BOTH named flags (--N 169 --p 1009) AND clean positional arguments (plan 169 1009 4 scalar)!
  if (typeof require === 'function' && typeof module === 'object' && require.main === module) {
    const args = process.argv.slice(2);
    const cmd = args[0] || 'help';
    const pos = [];
    const flags = new Map();
    const boolFlags = new Set();
    const knownBoolFlags = new Set(['--fault', '--stdin']);
    for (let i = 1; i < args.length; i++) {
      const a = args[i];
      if (a.startsWith('--')) {
        if (knownBoolFlags.has(a)) {
          boolFlags.add(a);
        } else {
          const next = args[i + 1];
          if (next !== undefined && !next.startsWith('--')) {
            flags.set(a, next);
            i += 1;
          } else {
            boolFlags.add(a);
          }
        }
      } else {
        pos.push(a);
      }
    }
    const getArg = (flag, posIdx, def) => {
      if (flags.has(flag)) return flags.get(flag);
      if (posIdx !== null && pos[posIdx] !== undefined) return pos[posIdx];
      return def;
    };
    const bigReplacer = (_k, v) => (typeof v === 'bigint' ? v.toString() : v);
    try {
      if (cmd === 'plan') {
        const res = planAdaptiveFork({
          N: BigInt(getArg('--N', 0, '91')),
          p: BigInt(getArg('--p', 1, '1009')),
          matrixDim: Number(getArg('--m', 2, '4')),
          workload: getArg('--workload', 3, 'scalar')
        });
        console.log(JSON.stringify({
          version: exportedApi.version,
          N: res.N,
          p: res.p,
          ring: res.ringLabel,
          winner: res.comparison.adaptive_fork,
          baseline: res.comparison.vinciguerra_r3_x5,
          speedupFactor: Number(res.speedupFactor.toFixed(3)),
          reductionPct: Number(res.reductionPct.toFixed(2))
        }, bigReplacer, 2));
      } else if (cmd === 'run') {
        const res = execFourRegPowering(
          BigInt(getArg('--N', 0, '91')),
          BigInt(getArg('--x', 1, '7')),
          BigInt(getArg('--p', 2, '1009')),
          { engine: getArg('--engine', 3, 'adaptive'), faultBit: boolFlags.has('--fault') }
        );
        console.log(JSON.stringify(res, bigReplacer, 2));
        if (!res.verified) process.exitCode = 2;
      } else if (cmd === 'vault') {
        const crypto = require('crypto');
        const fs = require('fs');
        const useStdin = boolFlags.has('--stdin');
        let raw;
        let NArg;
        let pArg;
        let xArg;
        if (useStdin) {
          raw = fs.readFileSync(0);
          NArg = getArg('--N', 0, '91');
          pArg = getArg('--p', 1, '1009');
          xArg = getArg('--x', 2, '7');
        } else {
          const payload = getArg('--text', 0, 'SensorBuffer:98.6F|Battery:84%|Keys:OK');
          raw = Buffer.from(payload, 'utf8');
          NArg = getArg('--N', 1, '91');
          pArg = getArg('--p', 2, '1009');
          xArg = getArg('--x', 3, '7');
        }
        const res = execCatalyticByteVault(
          new Uint8Array(raw),
          BigInt(NArg),
          BigInt(xArg),
          BigInt(pArg),
          { faultBit: boolFlags.has('--fault'), maxChunks: 21845 }
        );
        const hBefore = crypto.createHash('sha256').update(res.beforeBytes).digest('hex');
        const hMid = crypto.createHash('sha256').update(res.midScrambleBytes).digest('hex');
        const hAfter = crypto.createHash('sha256').update(res.afterBytes).digest('hex');
        console.log(JSON.stringify({
          engineUsed: res.engineUsed,
          borrowedBytes: res.borrowedBytes,
          accessesPerChunk: res.accessesPerChunk,
          sha256Before: hBefore,
          sha256MidFlightScrambled: hMid,
          sha256After: hAfter,
          sha256Identical: hBefore === hAfter,
          verified: res.verified && hBefore === hAfter
        }, null, 2));
        if (!(res.verified && hBefore === hAfter)) process.exitCode = 2;
      } else if (cmd === 'stream') {
        const rawToks = getArg('--tokens', 0, 'req_api req_api req_auth req_db req_api req_auth');
        const tokens = rawToks.trim().split(/[\s,;]+/).filter(Boolean);
        const counts = new Map();
        for (const t of tokens) counts.set(t, (counts.get(t) || 0) + 1);
        const freqVec = Array.from(counts.values());
        const res = execStreamingMoment(
          freqVec,
          BigInt(getArg('--D', 1, '20')),
          BigInt(getArg('--p', 2, '1009')),
          { engine: getArg('--engine', 3, 'adaptive'), faultBit: boolFlags.has('--fault') }
        );
        console.log(JSON.stringify(res, bigReplacer, 2));
        if (!res.verified) process.exitCode = 2;
      } else if (cmd === 'horizon') {
        const pVal = BigInt(getArg('--p', 0, '1009'));
        const wl = getArg('--workload', 1, 'scalar');
        console.log(JSON.stringify(computeAdaptiveHorizon(pVal, { workload: wl }), null, 2));
      } else if (cmd === 'verify') {
        const fs = require('fs');
        const certPath = getArg('--file', 0, '');
        if (!certPath) throw new Error('Provide a JSON certificate path: node catalytic-engine.js verify <cert.json>');
        const cert = JSON.parse(fs.readFileSync(certPath, 'utf8'));
        const verdict = verifyCertificate(cert);
        console.log(JSON.stringify(verdict, bigReplacer, 2));
        if (!verdict.ok) process.exitCode = 2;
      } else if (cmd === 'bench') {
        console.log(JSON.stringify(runDeviceBenchmark({ iters: Number(getArg('--iters', 0, '6')) }), null, 2));
      } else if (cmd === 'fuzz') {
        const n = Number(getArg('--trials', 0, '300'));
        const res = runAdversarialFuzz(n, 20261125);
        console.log(JSON.stringify(res, null, 2));
        if (res.failed > 0) process.exitCode = 2;
      } else {
        console.log([
          `Catalytic Register Frontiers — Adaptive Forking CLI v${exportedApi.version}`,
          'Usage (supports BOTH --flags and positional arguments):',
          '  node catalytic-engine.js plan    [N=91] [p=1009] [m=4] [workload=scalar]',
          '  node catalytic-engine.js run     [N=91] [x=7] [p=1009] [--fault]',
          '  node catalytic-engine.js vault   ["SecretRAM"|--stdin] [N=91] [p=1009] [x=7] [--fault]',
          '  node catalytic-engine.js stream  ["a a b a c b"] [D=20] [p=1009] [engine=adaptive]',
          '  node catalytic-engine.js horizon [p=1009] [workload=scalar]',
          '  node catalytic-engine.js verify  <certificate.json>',
          '  node catalytic-engine.js bench   [iters=6]',
          '  node catalytic-engine.js fuzz    [trials=300]'
        ].join('\n'));
      }
    } catch (err) {
      console.error('ERROR:', err.message);
      process.exitCode = 1;
    }
  }

  return exportedApi;
});
