// SPDX-License-Identifier: Apache-2.0
/*
 * Catalytic Register Frontiers — Universal Zero-Dependency BigInt Engine & Adaptive Forking Scheduler
 *
 * Implements literal exact-arithmetic execution (zero floating-point proof steps) of EVERY
 * formally verified construction in `catalytic-register-frontiers` (Lean 4.35.0):
 *   - T1 / T1a–T1d: Exact prime-field base-p digit-sum oracle & Lucas binomials
 *   - T2: Strictly bilinear 2-access Frobenius collapse x^(2^k) over char-2 rings (k+1 regs, 4k-2 ops)
 *   - T3a–T3g: Literal 3-register passive Pascal-row shear loops prog4_x5 .. prog9_x15
 *   - T3h: Complete 4-register passive powering x^N (Cook-Mertz + non-passive 3-reg composition)
 *   - T3i: Zero-write-wear exact streaming frequency moments F_D(f) = sum_i f_i^D over F_p^n
 *   - R3 (Cor. 5.4): Non-commutative homogeneous degree-2 lift mu_7(prog5_x7) on M_2(F_p)
 *   - T4: Balanced zero-workspace bilinear multilinear product x_0...x_{d-1} in <= log_2 d + 2 regs
 *   - Adaptive Forking (DP + Hybrid Scheduler): Dynamically selects optimal verified fork at each
 *     recursion level across Frobenius, direct digit leaves, multiplicative composition, and
 *     mixed-radix Cook-Mertz splits subject to modulus p, bad-prime constraints, matrix dimension,
 *     and device profile (watch / phone / tablet / laptop / desktop).
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
  // 1. Exact BigInt Number Theory & Modular Arithmetic (zero floats)
  // =========================================================================

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

  function binomModP(n, k, p) {
    const pb = BigInt(p);
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
  // 4. Adaptive Forking Planner (Exact DP + Hybrid Asymptotic Scheduler)
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
      return false; // Keep matrix shear tier strictly O(m^4) zero-overhead unless forced
    }
    if (p === 0n) return true;
    return gcd(spec.D, p) === 1n;
  }

  function planAdaptiveFork(opts) {
    const workload = opts.workload || 'scalar'; // 'scalar' | 'streaming' | 'matrix' | 'frobenius'
    const N = BigInt(opts.N ?? 1000);
    const p = BigInt(opts.p ?? 0); // 0n means characteristic 0 (Q / exact Z)
    const matrixDim = Math.max(1, Number(opts.matrixDim ?? 2));
    const deviceClass = opts.deviceClass || 'desktop';
    const pIsPrime = p >= 2n && isPrimeBig(p);

    if (N < 1n) throw new Error('Exponent N must be >= 1');

    // Static baselines for comparison
    const base4Acc = exactFourRegAccesses(5, 4, N);
    const prog5Acc = exactFourRegAccesses(7, 5, N);
    const prog8Acc = exactFourRegAccesses(13, 8, N);
    const ell5 = baseDigits(5, N).length - 1;
    const ell7 = baseDigits(7, N).length - 1;
    const ell13 = baseDigits(13, N).length - 1;

    const p5Valid = p === 0n || (p > BigInt(Math.max(6, ell7 + 1)) && gcd(576n, p) === 1n);
    const p8Valid = p === 0n || (p > BigInt(Math.max(12, ell13 + 1)) && gcd(PROGRAMS_R3[8].D, p) === 1n);
    const p4Valid = p === 0n || (p > BigInt(Math.max(4, ell5 + 1)) && gcd(54n, p) === 1n);

    // Check T1/T2 prime-field Frobenius collapse (exact 2-access) and T1 digit-sum candidate
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
      } else if (BigInt(sp) < p) {
        t1DirectCandidate = {
          strategy: 'T1_DIGIT_SUM_DIRECT',
          label: `T1 Prime-Field Digit-Sum Direct (s_${p}(${N}) + 1 = ${sp + 1} accesses)`,
          accesses: BigInt(sp + 1),
          registers: '2 passive regs',
          tree: `x^${N} (s_${p}(${N}) = ${sp} <= ${p - 1n}) -> 2-register forward-difference program`
        };
      }
    }

    // Determine feasible 3-register composition gadgets
    const feasibleSpecs = [4, 5, 6, 7, 8]
      .map((t) => PROGRAMS_R3[t])
      .filter((spec) => isGadgetFeasible(spec, p, workload));

    // Exact DP over n <= DP_LIMIT (for small/medium N, gives provably optimal adaptive fork tree!)
    const DP_LIMIT = N <= 4096n ? Number(N) : 2048;
    const costW3 = new Array(DP_LIMIT + 1).fill(Infinity);
    const planW3 = new Array(DP_LIMIT + 1).fill(null);

    // 3-work-register non-passive composition DP (Alekseev et al. Lem. 8):
    //   - Direct 2-reg digit leaf: n + 1 accesses (valid when p == 0 or p > n)
    //   - Prime-field T1 digit-sum leaf: s_p(n) + 1 (when p prime, s_p(n) < p, non-matrix)
    //   - Multiplicative composition fork: if d_k | n, compose(P_{n/d_k}, prog_k) costs t_k * costW3[n/d_k]
    costW3[0] = 0;
    planW3[0] = { op: 'const1' };
    costW3[1] = 1;
    planW3[1] = { op: 'direct', n: 1, accesses: 1 };

    for (let n = 2; n <= DP_LIMIT; n++) {
      // Option A: direct forward-difference 2-reg program (needs n! invertible mod p)
      if (p === 0n || p > BigInt(n)) {
        costW3[n] = n + 1;
        planW3[n] = { op: 'digit_leaf', n, accesses: n + 1 };
      }
      // Option B: prime-field T1 shortcut (strictly non-matrix)
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

    // 4-register passive Cook-Mertz / Gray-Code Adaptive Fork DP:
    let adaptiveBest = null;

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
      }
      // 1. Direct passive 3-register single gadget match (e.g., N = 5, 7, 9, 11, 13)
      for (const spec of feasibleSpecs) {
        if (spec.degree === nInt && spec.t < bestAcc) {
          bestAcc = spec.t;
          bestDesc = `Direct passive 3-reg ${spec.id} (x^${nInt} in ${spec.t} accesses, 3 regs!)`;
          bestPlan = { kind: 'direct_pass3', t: spec.t, gadget: spec.id };
        }
      }
      // 2. Direct 2-reg forward-difference leaf (needs n! invertible)
      if ((p === 0n || p > BigInt(nInt)) && nInt + 1 < bestAcc) {
        bestAcc = nInt + 1;
        bestDesc = `Direct 2-reg forward-difference leaf (x^${nInt} in ${nInt + 1} accesses)`;
        bestPlan = { kind: 'direct_digit', n: nInt };
      }
      // 2b. Passive 4-reg wrap of exact Work3 multiplicative composition (O -= U; U += x^n; O += U; U -= x^n -> 2 * costW3[n] accesses!)
      if (costW3[nInt] < Infinity && planW3[nInt] && planW3[nInt].op === 'compose' && 2 * costW3[nInt] < bestAcc) {
        bestAcc = 2 * costW3[nInt];
        bestDesc = `Adaptive Composition Wrap: passive 4-reg wrap of Work3(${nInt} = ${planW3[nInt].degree} * ${planW3[nInt].child}) -> ${bestAcc} accesses`;
        bestPlan = { kind: 'wrap1_work3', n: nInt, work3Plan: planW3[nInt], work3Table: planW3 };
      }
      // 3. Exact Gray-Code 2-way Cook-Mertz adaptive fork: x^n = x^a * x^(n-a) -> exact 2*costW3[a] + 2*costW3[b] accesses!
      if (p === 0n || p > 2n) {
        for (let a = 1; a <= Math.floor(nInt / 2); a++) {
          const b = nInt - a;
          if (costW3[a] < Infinity && costW3[b] < Infinity) {
            const cand = 2 * costW3[a] + 2 * costW3[b];
            if (cand < bestAcc) {
              bestAcc = cand;
              bestDesc = `Gray-Code 2-Way Adaptive Fork: x^${nInt} = x^${a} (${costW3[a]}w) * x^${b} (${costW3[b]}w) -> ${cand} accesses`;
              bestPlan = { kind: 'gray_cm2_fork', a, b, planA: planW3[a], planB: planW3[b], work3Table: planW3 };
            }
          }
        }
      }
      // 4. Compare all feasible base-delta Cook-Mertz expansions (delta in {5, 7, 9, 11, 13})
      for (const spec of feasibleSpecs) {
        const ds = baseDigits(spec.degree, N);
        const mLen = ds.length;
        const okMod = p === 0n || (p > BigInt(Math.max(spec.degree - 1, mLen)) && gcd(spec.D, p) === 1n);
        if (!okMod) continue;
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
        if (acc < bestAcc) {
          bestAcc = acc;
          bestDesc = `Adaptive Base-${spec.degree} Fork (${spec.id}, digits [${ds.join(', ')}] LSB-first) -> ${acc} accesses`;
          bestPlan = { kind: 'radix_fork', base: spec.degree, t: spec.t, gadget: spec.id, digits: ds };
        }
      }

      if (bestAcc === Infinity) {
        // Fallback when modulus p is tiny composite or divides required factorials
        adaptiveBest = {
          strategy: 'MODULUS_CONSTRAINT_WARNING',
          label: `Modulus p=${p} divides a required denominator; use prime p > max(12, floor(log_13 N)+1) avoiding bad primes`,
          accesses: prog5Acc,
          registers: workload === 'matrix' ? `${3 * matrixDim * matrixDim + (matrixDim * matrixDim * (matrixDim * matrixDim + 1)) / 2} scalars` : '4 passive regs',
          tree: `Modulus p=${p} is incompatible with exact inverse requirements for N=${N}`,
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
      // Large-N Hybrid Top-Down Adaptive Forking (N > 4096, up to 10^12+!)
      // Picks the asymptotically optimal feasible engine across all constraints
      let chosenSpec = null;
      for (const tCand of (workload === 'matrix' ? [5, 4] : [8, 7, 6, 5, 4])) {
        const sp = PROGRAMS_R3[tCand];
        const ell = baseDigits(sp.degree, N).length - 1;
        const okMod = p === 0n || (p > BigInt(Math.max(sp.degree - 1, ell + 1)) && gcd(sp.D, p) === 1n);
        if (isGadgetFeasible(sp, p, workload) && okMod) {
          chosenSpec = sp;
          break;
        }
      }
      if (!chosenSpec) {
        chosenSpec = PROGRAMS_R3[5];
      }
      // Compute hybrid adaptive accesses: replace low-order digit subtrees <= DP_LIMIT by exact DP costW3!
      const ds = baseDigits(chosenSpec.degree, N);
      let hybridAcc = 0n;
      let tPow = 1n;
      let dPow = 1n;
      for (let i = 0; i < ds.length; i++) {
        const b = ds[i];
        const termExp = BigInt(b) * dPow;
        let ci = b === 0 ? 0n : BigInt(b + 1) * tPow;
        if (b > 0 && termExp <= BigInt(DP_LIMIT) && costW3[Number(termExp)] < Number(ci)) {
          ci = BigInt(costW3[Number(termExp)]);
        }
        hybridAcc = 2n * ci + 2n * hybridAcc;
        tPow *= BigInt(chosenSpec.t);
        dPow *= BigInt(chosenSpec.degree);
      }
      const matScalars = 3 * matrixDim * matrixDim + (matrixDim * matrixDim * (matrixDim * matrixDim + 1)) / 2;
      adaptiveBest = {
        strategy: workload === 'matrix' ? 'ADAPTIVE_MATRIX_PROG5' : `ADAPTIVE_HYBRID_${chosenSpec.id.toUpperCase()}`,
        label: workload === 'matrix'
          ? `Adaptive Matrix Fork (${chosenSpec.id}, d=2 shear, zero extra scalar regs) + DP leaves`
          : `Adaptive Hybrid Fork (${chosenSpec.id} top radix + DP-optimal leaves)`,
        accesses: hybridAcc,
        registers: workload === 'matrix' ? `${matScalars} scalar regs (m=${matrixDim}, exact r=3 tier)` : '4 passive regs',
        tree: `Top radix ${chosenSpec.degree} (${chosenSpec.id}, ${ds.length} digits) -> DP leaf optimization for sub-exponents <= ${DP_LIMIT}`,
        chosenSpecId: chosenSpec.id,
        feasible: true
      };
    }

    const baseNum = Number(base4Acc);
    const adaptNum = Number(adaptiveBest.accesses);
    const reductionPct = baseNum > 0 ? ((baseNum - adaptNum) / baseNum) * 100 : 0;
    const speedupFactor = adaptNum > 0 ? baseNum / adaptNum : 1;

    // Asymptotic ratio at N (pure exponent comparison)
    const nf = Number(N > 10n ** 15n ? 10n ** 15n : N);
    const asympRatio5 = nf > 1 ? Math.pow(nf, Math.log(4) / Math.log(5) - Math.log(5) / Math.log(7)) : 1;
    const asympRatio8 = nf > 1 ? Math.pow(nf, Math.log(4) / Math.log(5) - Math.log(8) / Math.log(13)) : 1;

    const deviceBudgets = {
      watch: { maxFuzz: 100, traceLimit: 8, hint: 'Smartwatch glance mode: compact exact BigInt & 100-trial live fuzzer' },
      phone: { maxFuzz: 300, traceLimit: 16, hint: 'Mobile mode: touch-tuned adaptive fork & 300-trial fuzzer' },
      tablet: { maxFuzz: 600, traceLimit: 24, hint: 'Tablet split-view: full live step trace & 600-trial fuzzer' },
      laptop: { maxFuzz: 1000, traceLimit: 40, hint: 'Laptop mode: full multi-engine workbench & 1,000-trial fuzzer' },
      desktop: { maxFuzz: 2000, traceLimit: 60, hint: 'Desktop mode: full trace, streaming telemetry & 2,000-trial fuzzer' }
    };

    return {
      workload,
      N: N.toString(),
      p: p.toString(),
      matrixDim,
      device: deviceBudgets[deviceClass] || deviceBudgets.desktop,
      internalPlan: adaptiveBest.plan || null,
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

  // Execute a clean 3-work-register subprogram computing r0 <- r0 + x^(b * delta^i)
  // by literal instruction replay of 2-reg forward differences composed with prog_delta!
  function execDigitPowWork3(b, x, p, state, scale = 1n) {
    // Cleanly computes r0 <- r0 + scale * x^b on (r0, r1, r2), restoring r1, r2.
    let [r0, r1, r2] = state;
    if (b === 0) {
      return { state: [mod(r0 + scale, p), r1, r2], accesses: 0 };
    }
    if (b === 1) {
      return { state: [mod(r0 + mod(scale * x, p), p), r1, r2], accesses: 1 };
    }
    // Forward finite difference: sum_{a=0}^b (-1)^(b-a) C(b, a) (r1 + a*x)^b = b! * x^b
    const invFact = modInv(factorialMod(b, p), p);
    const outFactor = mod(scale * invFact, p);
    let accesses = 0;
    for (let a = 0; a <= b; a++) {
      const sign = ((b - a) & 1) ? -1n : 1n;
      const w = mod(outFactor * sign * binomModP(b, a, p), p);
      r0 = mod(r0 + mod(w * modPow(r1, b, p), p), p);
      const step = a < b ? 1n : -BigInt(b);
      r1 = mod(r1 + mod(step * x, p), p);
      accesses += 1;
    }
    return { state: [r0, r1, r2], accesses };
  }

  // Clean non-passive composition on 3 work registers (Alekseev et al. MFCS 2025, Lem. 8):
  // Executes P with input x replaced by g(x) = x^(delta^i), rotating registers cleanly.
  function execPowerLevelWork3(spec, level, b, x, p, state, scale = 1n) {
    if (level === 0) {
      return execDigitPowWork3(b, x, p, state, scale);
    }
    // Non-passive recursive substitution: replace each input access `u += alpha * y`
    // in the outer level with a rotated call to level - 1 computing `u += alpha * x^(delta^(level-1))`.
    const outer = execPowerLevelWork3_outer(spec, level, b, x, p, state, scale);
    return outer;
  }

  function execPowerLevelWork3_outer(spec, level, b, x, p, state, scale) {
    // Build the exact recursive evaluation of x^(b * delta^level) by substituting spec
    // into every input access of digitPow(b) using cyclic register rotation!
    // Base call: if level == 1 and b == 1, literally runs Pass3(spec) on (r0, r1, r2).
    if (level === 0) {
      return execDigitPowWork3(b, x, p, state, scale);
    }
    // Helper: execute spec on registers (dst, uReg, vReg) with input oracle `addInput(uVal, alpha)`
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
        // Input access on uIdx using the other two registers catalytically!
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

    // Now wrap digitPow(b) around runPowTower(level):
    if (b === 0) {
      return { state: [mod(state[0] + scale, p), state[1], state[2]], accesses: 0 };
    }
    if (b === 1) {
      return runPowTower(level, state, 0, 1, 2, scale);
    }
    // Forward finite difference on (r0, r1, r2) with each step `r1 += step * x^(delta^level)`
    // executed via runPowTower(level) targeting r1 and using (r2, r0) catalytically!
    const reg = [state[0], state[1], state[2]];
    const invFact = modInv(factorialMod(b, p), p);
    const outFactor = mod(scale * invFact, p);
    let totalAcc = 0;
    for (let a = 0; a <= b; a++) {
      const sign = ((b - a) & 1) ? -1n : 1n;
      const w = mod(outFactor * sign * binomModP(b, a, p), p);
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

  // Execute a DP Work3 plan recursively on registers (reg[dstIdx], reg[uIdx], reg[vIdx])
  // with input oracle addInputFn(regState, subDst, subU, subV, alpha), restoring non-target regs!
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
        const w = mod(outFactor * sign * binomModP(n, a, p), p);
        reg[dstIdx] = mod(reg[dstIdx] + mod(w * modPow(reg[uIdx], n, p), p), p);
        const step = a < n ? 1n : -BigInt(n);
        const sub = addInputFn(reg, uIdx, vIdx, dstIdx, step);
        reg[0] = sub.state[0]; reg[1] = sub.state[1]; reg[2] = sub.state[2];
        acc += sub.accesses;
      }
      return { state: reg, accesses: acc };
    }
    if (node.op === 't1_frobenius') {
      // Exact T1 forward finite difference on A = {0..s_p(n)} over F_p!
      const s = node.sp;
      const reg = [regState[0], regState[1], regState[2]];
      const invFact = modInv(factorialMod(s, p), p);
      const outFactor = mod(scale * invFact, p);
      let acc = 0;
      for (let a = 0; a <= s; a++) {
        const sign = ((s - a) & 1) ? -1n : 1n;
        const w = mod(outFactor * sign * binomModP(s, a, p), p);
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
        // Substitute child composition cleanly into uIdx using (vIdx, dstIdx) catalytically!
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
    if (p < 2n || !isPrimeBig(p)) throw new Error('Modulus p must be prime for modular 4-register execution');
    const x = mod(BigInt(xIn), p);
    const engineChoice = opts.engine || 'adaptive'; // 'prog4_x5' | 'prog5_x7' | 'prog8_x13' | 'adaptive'
    const faultBit = Boolean(opts.faultBit);

    const O0 = mod(BigInt(opts.O0 ?? 424242n), p);
    const u0 = mod(BigInt(opts.u0 ?? 135791n), p);
    const r10 = mod(BigInt(opts.r10 ?? 246802n), p);
    const r20 = mod(BigInt(opts.r20 ?? 975313n), p);

    // If adaptive mode AND N <= 4096, execute the LITERAL DP-optimal Adaptive Fork plan!
    if (engineChoice === 'adaptive' && N <= 4096n) {
      const planRes = planAdaptiveFork({ workload: 'scalar', N, p });
      const plan = planRes.internalPlan;
      const baseOracle = (st3, dstIdx, _u, _v, alpha) => {
        const out = [st3[0], st3[1], st3[2]];
        out[dstIdx] = mod(out[dstIdx] + mod(alpha * x, p), p);
        return { state: out, accesses: 1 };
      };

      if (plan && plan.kind === 'direct_pass3') {
        const r3 = execPass3(plan.t, x, p, { O0, u0, v0: r10, faultBit });
        return {
          engineUsed: `adaptive:${plan.gadget} (direct 3-reg)`,
          N: N.toString(), p: p.toString(), x: x.toString(), digits: [Number(N)],
          initial: { O: O0, u: u0, r1: r10, r2: r20 },
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
        for (let a = 0; a <= s; a++) {
          const sign = ((s - a) & 1) ? -1n : 1n;
          const w = mod(invFact * sign * binomModP(s, a, p), p);
          O = mod(O + mod(w * modPow(u, nInt, p), p), p);
          const step = a < s ? 1n : -BigInt(s);
          u = mod(u + mod(step * x, p), p);
          if (faultBit && a === 0) u = mod(u + 1n, p);
          acc += 1;
        }
        const expectedO = mod(O0 + modPow(x, N, p), p);
        return {
          engineUsed: `adaptive:${plan.kind} (2-reg passive)`,
          N: N.toString(), p: p.toString(), x: x.toString(), digits: [nInt],
          initial: { O: O0, u: u0, r1: r10, r2: r20 },
          final: { O, u, r1: r10, r2: r20 },
          expectedO, accesses: acc,
          vinciguerraBaselineAccesses: Number(exactFourRegAccesses(5, 4, N)),
          outputExact: O === expectedO, catalystsRestored: u === u0, verified: O === expectedO && u === u0
        };
      }
      if (plan && plan.kind === 'wrap1_work3') {
        // Passive 4-register wrap: O -= U; U += x^N; O += U; U -= x^N -> 2 * costW3[N] accesses!
        let O = mod(O0 - u0, p);
        let work = [u0, r10, r20];
        const rPlus = execWork3PlanNode(plan.work3Table, plan.n, p, work, 0, 1, 2, 1n, baseOracle);
        work = rPlus.state;
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
          final: { O, u: work[0], r1: work[1], r2: work[2] },
          expectedO, accesses: rPlus.accesses + rMinus.accesses,
          vinciguerraBaselineAccesses: Number(exactFourRegAccesses(5, 4, N)),
          outputExact: O === expectedO, catalystsRestored: restored, verified: O === expectedO && restored
        };
      }
      if (plan && plan.kind === 'gray_cm2_fork') {
        // Exact Gray-code 2-way Cook-Mertz: (0,0) -> (1,0) -> (1,1) -> (0,1) -> (0,0)
        // Literally 2 * costW3[a] + 2 * costW3[b] accesses!
        const inv2 = modInv(2n, p);
        let O = O0;
        let work = [u0, r10, r20];
        let acc = 0;
        // (0,0): +inv2 * u^2
        O = mod(O + mod(inv2 * modPow(work[0], 2, p), p), p);
        // +A -> (1,0): -inv2 * (u+A)^2
        let sub = execWork3PlanNode(plan.work3Table, plan.a, p, work, 0, 1, 2, 1n, baseOracle);
        work = sub.state; acc += sub.accesses;
        if (faultBit) work[1] = mod(work[1] + 1n, p);
        O = mod(O - mod(inv2 * modPow(work[0], 2, p), p), p);
        // +B -> (1,1): +inv2 * (u+A+B)^2
        sub = execWork3PlanNode(plan.work3Table, plan.b, p, work, 0, 1, 2, 1n, baseOracle);
        work = sub.state; acc += sub.accesses;
        O = mod(O + mod(inv2 * modPow(work[0], 2, p), p), p);
        // -A -> (0,1): -inv2 * (u+B)^2
        sub = execWork3PlanNode(plan.work3Table, plan.a, p, work, 0, 1, 2, -1n, baseOracle);
        work = sub.state; acc += sub.accesses;
        O = mod(O - mod(inv2 * modPow(work[0], 2, p), p), p);
        // -B -> (0,0) restored!
        sub = execWork3PlanNode(plan.work3Table, plan.b, p, work, 0, 1, 2, -1n, baseOracle);
        work = sub.state; acc += sub.accesses;
        const expectedO = mod(O0 + modPow(x, N, p), p);
        const restored = work[0] === u0 && work[1] === r10 && work[2] === r20;
        return {
          engineUsed: `adaptive:gray_cm2(x^${plan.a}*x^${plan.b})`,
          N: N.toString(), p: p.toString(), x: x.toString(), digits: [plan.a, plan.b],
          initial: { O: O0, u: u0, r1: r10, r2: r20 },
          final: { O, u: work[0], r1: work[1], r2: work[2] },
          expectedO, accesses: acc,
          vinciguerraBaselineAccesses: Number(exactFourRegAccesses(5, 4, N)),
          outputExact: O === expectedO, catalystsRestored: restored, verified: O === expectedO && restored
        };
      }
      if (planRes.comparison.adaptive_fork.strategy === 'T1a_FROBENIUS_COLLAPSE' ||
          planRes.comparison.adaptive_fork.strategy === 'T2_BILINEAR_FROBENIUS') {
        // Exact 2-access Frobenius collapse: O += (u+x)^N - u^N (2 input accesses: u += x; u -= x)
        let O = O0;
        let u = u0;
        O = mod(O - modPow(u, N, p), p);
        u = mod(u + x, p);
        if (faultBit) u = mod(u + 1n, p);
        O = mod(O + modPow(u, N, p), p);
        u = mod(u - x, p);
        const expectedO = mod(O0 + modPow(x, N, p), p);
        return {
          engineUsed: 'adaptive:T1a_frobenius_2access',
          N: N.toString(), p: p.toString(), x: x.toString(), digits: [Number(N)],
          initial: { O: O0, u: u0, r1: r10, r2: r20 },
          final: { O, u, r1: r10, r2: r20 },
          expectedO, accesses: 2,
          vinciguerraBaselineAccesses: Number(exactFourRegAccesses(5, 4, N)),
          outputExact: O === expectedO, catalystsRestored: u === u0, verified: O === expectedO && u === u0
        };
      }
    }

    let spec = PROGRAMS_R3[8];
    if (engineChoice === 'prog4_x5') spec = PROGRAMS_R3[4];
    else if (engineChoice === 'prog5_x7') spec = PROGRAMS_R3[5];
    else if (engineChoice === 'prog8_x13') spec = PROGRAMS_R3[8];
    else {
      const ds13 = baseDigits(13, N);
      const ds7 = baseDigits(7, N);
      if (p > BigInt(Math.max(12, ds13.length)) && gcd(PROGRAMS_R3[8].D, p) === 1n && N >= 13n) {
        spec = PROGRAMS_R3[8];
      } else if (p > BigInt(Math.max(6, ds7.length)) && gcd(PROGRAMS_R3[5].D, p) === 1n) {
        spec = PROGRAMS_R3[5];
      } else {
        spec = PROGRAMS_R3[4];
      }
    }

    const ds = baseDigits(spec.degree, N);
    const m = ds.length;
    if (p <= BigInt(Math.max(spec.degree - 1, m)) || gcd(spec.D, p) !== 1n) {
      throw new Error(`Prime p=${p} is incompatible with ${spec.id} at N=${N} (need p > ${Math.max(spec.degree - 1, m)} and p not dividing D_${spec.t})`);
    }

    let O = O0;
    let work = [u0, r10, r20];
    let accesses = 0;
    let faultInjected = false;
    const invFactM = modInv(factorialMod(m, p), p);

    // Literal Cook-Mertz recursive accumulation matching FourRegisterPowering.accumProg:
    // Recurses over digits MSB-first (index idx from m-1 down to 0)
    function accumRec(idx, sign) {
      if (idx < 0) {
        O = mod(O + mod(sign * invFactM * modPow(work[0], m, p), p), p);
        return;
      }
      const b = ds[idx];
      // Branch 1: U <- U + x^(b * delta^idx)
      const rPlus = execPowerLevelWork3(spec, idx, b, x, p, work, 1n);
      work = rPlus.state;
      accesses += rPlus.accesses;
      if (faultBit && !faultInjected) {
        work[1] = mod(work[1] + 1n, p);
        faultInjected = true;
      }
      accumRec(idx - 1, sign);
      // Uncompute: U <- U - x^(b * delta^idx)
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
      engineUsed: spec.id,
      N: N.toString(),
      p: p.toString(),
      x: x.toString(),
      digits: ds,
      initial: { O: O0, u: u0, r1: r10, r2: r20 },
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
    const D = BigInt(DIn);
    const p = BigInt(pIn);
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
      passes = res.accesses; // Vectorized product ring R^n performs the exact same pass schedule in parallel!
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
      scalarRegisters: 22, // 3*4 + C(5,2) = 12 + 10 = 22 (exact r=3 Vinciguerra tier)
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
    const t = Number(tIn);
    if (!isPrimeBig(p)) {
      return { validPrime: false, message: `${p} is not prime. Theorem T1 characterizes prime fields F_p.` };
    }
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

  // Execute T2 strictly bilinear 2-access Frobenius x^(2^k) over F_{2^8} (AES/Rijndael field x^8+x^4+x^3+x+1)!
  // Using F_{2^8} makes x^(2^k) genuinely non-trivial (unlike F_2 where x^2 = x)!
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

  function execT2BilinearFrobenius(k, xByte, initRegs, opts = {}) {
    if (k < 1 || k > 12) throw new Error('Choose k in [1, 12]');
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
  // 8. Live Adversarial Fuzzer (Deterministic PRNG across T1–T4)
  // =========================================================================

  function runAdversarialFuzz(trials = 500, seed = 20261125) {
    let s = BigInt(seed) & ((1n << 64n) - 1n);
    const nextU32 = () => {
      s = (s * 6364136223846793005n + 1442695040888963407n) & ((1n << 64n) - 1n);
      return Number((s >> 32n) & 0xffffffffn);
    };
    const t0 = typeof performance !== 'undefined' ? performance.now() : Date.now();
    let passed = 0;
    let failed = 0;
    const goodPrimes = [11n, 13n, 19n, 23n, 29n, 31n, 101n, 1009n, 1000003n];
    const gadgets = [4, 5, 6, 7, 8];

    for (let i = 0; i < trials; i++) {
      const mode = i % 5;
      let ok = false;
      if (mode === 0) {
        // Fuzz 3-register prog4..prog8 over good prime with random dirty catalysts
        const t = gadgets[nextU32() % gadgets.length];
        const p = goodPrimes[nextU32() % goodPrimes.length];
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
        // Fuzz T3h 4-register passive powering with random dirty catalysts
        const N = 1 + (nextU32() % 45);
        const p = 1009n;
        const res = execFourRegPowering(N, BigInt(nextU32()), p, {
          engine: 'adaptive',
          O0: BigInt(nextU32()),
          u0: BigInt(nextU32()),
          r10: BigInt(nextU32()),
          r20: BigInt(nextU32())
        });
        ok = res.verified;
      } else {
        // Fuzz R3 non-commutative matrix lift mu_7(prog5_x7) over M_2(F_11 / F_13)
        const p = (nextU32() & 1) ? 11n : 13n;
        const A = [[BigInt(nextU32()), BigInt(nextU32())], [BigInt(nextU32()), BigInt(nextU32())]];
        const O0 = [[BigInt(nextU32()), BigInt(nextU32())], [BigInt(nextU32()), BigInt(nextU32())]];
        ok = execMatrixLiftProg5(A, p, { O0 }).verified;
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

  return {
    version: '1.0.1',
    PROGRAMS_R3,
    mod,
    gcd,
    modInv,
    modPow,
    isPrimeBig,
    baseDigits,
    digitSum,
    binomModP,
    textToBigInt,
    formatBig,
    exactFourRegAccesses,
    execPass3,
    planAdaptiveFork,
    execFourRegPowering,
    execStreamingMoment,
    execMatrixLiftProg5,
    evalT1Oracle,
    execT2BilinearFrobenius,
    execT4BalancedProduct,
    runAdversarialFuzz
  };
});
