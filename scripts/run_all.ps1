# SPDX-License-Identifier: Apache-2.0
<#
.SYNOPSIS
  End-to-end reproducible verification orchestrator for catalytic-register-frontiers.
.PARAMETER Task
  One of: all, lean, experiments, tests, figures, paper, audit.
#>
param(
    [ValidateSet("all", "lean", "experiments", "tests", "figures", "paper", "audit")]
    [string]$Task = "all"
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$Repo = Split-Path -Parent $PSScriptRoot
$VenvPy = Join-Path $Repo ".venv\Scripts\python.exe"
if (Test-Path -LiteralPath $VenvPy) {
    $Py = $VenvPy
} else {
    $PyCmd = Get-Command python,python3,py -ErrorAction SilentlyContinue | Select-Object -First 1
    if (-not $PyCmd) { throw "Python interpreter not found (.venv\Scripts\python.exe or PATH)." }
    $Py = $PyCmd.Source
}
$VenvPytest = Join-Path $Repo ".venv\Scripts\pytest.exe"
$Pytest = if (Test-Path -LiteralPath $VenvPytest) { $VenvPytest } else { $null }
$TectonicCmd = Get-Command tectonic -ErrorAction SilentlyContinue
if ($TectonicCmd) {
    $Tectonic = $TectonicCmd.Source
} else {
    $Tectonic = Join-Path $env:USERPROFILE ".local\bin\tectonic.exe"
}
$ElanBin  = Join-Path $env:USERPROFILE ".elan\bin"
$LeanBin  = Join-Path $env:USERPROFILE ".elan\toolchains\leanprover--lean4---v4.35.0\bin"

if (Test-Path -LiteralPath $ElanBin) {
    $env:PATH = "$ElanBin;$LeanBin;$env:PATH"
}

function Run-Step([string]$Label, [scriptblock]$Body) {
    Write-Host "`n=== [$Label] ===" -ForegroundColor Cyan
    & $Body
    if ($LASTEXITCODE -ne 0) {
        throw "Step '$Label' failed with exit code $LASTEXITCODE"
    }
}

function Invoke-Lean {
    Run-Step "Lean 4.35 lake build + VerifyAxioms + leanchecker-paranoid + con-leche/con-ron" {
        Push-Location -LiteralPath (Join-Path $Repo "lean")
        try {
            & lake build
            if ($LASTEXITCODE -ne 0) { return }
            & $Py -c @"
import pathlib, subprocess, sys
r = subprocess.run(['lake', 'env', 'lean', 'VerifyAxioms.lean'], capture_output=True, text=True)
if r.returncode != 0:
    print(r.stdout, r.stderr, file=sys.stderr)
    sys.exit(r.returncode)
actual = r.stdout.replace('\r\n', '\n').strip()
print(actual)
expected = pathlib.Path('../results/lean_axioms.txt').read_text(encoding='utf-8').replace('\r\n', '\n').strip()
if actual != expected:
    print('AXIOM DRIFT DETECTED vs results/lean_axioms.txt!', file=sys.stderr)
    sys.exit(1)
import re
if re.search(r'sorryAx|_native|Lean\.ofReduceBool|Lean\.trustCompiler', actual):
    print('UNPERMITTED AXIOM DETECTED!', file=sys.stderr)
    sys.exit(1)
"@
            if ($LASTEXITCODE -ne 0) { return }
            & lake env leanchecker --fresh Solution
            if ($LASTEXITCODE -ne 0) { return }
            & lake env leanchecker-paranoid Solution
            if ($LASTEXITCODE -ne 0) { return }
            # Export raw UTF-8 stream via Python (avoiding PowerShell Out-File Unicode mangling)
            & $Py -c @"
import pathlib, subprocess, sys
exp = pathlib.Path('.lake/build/catalytic_export.txt')
with exp.open('wb') as f:
    p = subprocess.run(['lake', 'env', 'leanexport', 'Solution', '--',
        'Catalytic.Solution.prove_all_catalytic_theorems',
        'Catalytic.NonVacuity.nonvac_all_hypotheses'], stdout=f)
if p.returncode != 0:
    sys.exit(p.returncode)
for tool in ('con-leche', 'con-ron'):
    r = subprocess.run(['lake', 'env', tool, '--verified', str(exp)])
    if r.returncode != 0:
        sys.exit(r.returncode)
"@
        } finally {
            Pop-Location
        }
    }
}

function Invoke-Experiments {
    $scripts = @(
        "experiments/exp1_digit_sum_dichotomy.py",
        "experiments/exp2_three_register_breakthrough.py",
        "experiments/exp3_bilinear_and_balanced.py",
        "experiments/exp4_boolean_mc_companion.py"
    )
    Push-Location -LiteralPath $Repo
    try {
        foreach ($s in $scripts) {
            Run-Step "Experiment $s" { & $Py $s }
        }
    } finally {
        Pop-Location
    }
}

function Invoke-Tests {
    Run-Step "Pytest verification suite (repo-relative for bracket safety)" {
        Push-Location -LiteralPath $Repo
        try {
            if ($Pytest) { & $Pytest -v tests/test_all.py } else { & $Py -m pytest -v tests/test_all.py }
        } finally {
            Pop-Location
        }
    }
}

function Invoke-Figures {
    Run-Step "Generate 3 deterministic vector PDF figures" {
        Push-Location -LiteralPath $Repo
        try {
            & $Py scripts/make_figures.py
        } finally {
            Pop-Location
        }
    }
}

function Invoke-Paper {
    Run-Step "Compile AMS-LaTeX white paper with Tectonic" {
        $paperDir = Join-Path $Repo "paper"
        $buildDir = Join-Path $paperDir "build"
        if (-not (Test-Path -LiteralPath $buildDir)) {
            [System.IO.Directory]::CreateDirectory($buildDir) | Out-Null
        }
        Push-Location -LiteralPath $paperDir
        try {
            & $Tectonic -X compile main.tex --outdir build --keep-intermediates
        } finally {
            Pop-Location
        }
    }
}

function Invoke-Audit {
    Run-Step "Verify LRAT UNSAT proofs, REUSE/SPDX coverage, and offline citations" {
        Push-Location -LiteralPath $Repo
        try {
            & $Py scripts/verify_lrat.py
            if ($LASTEXITCODE -ne 0) { return }
            & $Py scripts/check_reuse.py
            if ($LASTEXITCODE -ne 0) { return }
            & $Py scripts/check_citations.py --offline
        } finally {
            Pop-Location
        }
    }
    Run-Step "Verify SHA-256 provenance manifest (MANIFEST.sha256)" {
        Push-Location -LiteralPath $Repo
        try {
            & $Py -c @"
import hashlib, pathlib, sys
manifest = pathlib.Path('MANIFEST.sha256')
if not manifest.exists():
    print('MISSING MANIFEST.sha256', file=sys.stderr)
    sys.exit(1)
ok = 0
for raw in manifest.read_text(encoding='utf-8').splitlines():
    line = raw.strip()
    if not line or line.startswith('#'):
        continue
    expected, rel = line.split('  ', 1)
    p = pathlib.Path(rel)
    if not p.exists():
        print(f'MISSING FILE: {rel}', file=sys.stderr)
        sys.exit(1)
    actual = hashlib.sha256(p.read_bytes()).hexdigest().lower()
    if actual != expected.lower():
        print(f'SHA256 MISMATCH: {rel} expected={expected} actual={actual}', file=sys.stderr)
        sys.exit(1)
    ok += 1
print(f'MANIFEST_SHA256_VERIFIED: {ok}/{ok} files match exact checksums.')
"@
        } finally {
            Pop-Location
        }
    }
    Run-Step "Verify DigiCert RFC 3161 trusted timestamp (provenance/MANIFEST.sha256.tsr)" {
        Push-Location -LiteralPath $Repo
        try {
            $gitOpenSSL = "C:\Program Files\Git\usr\bin\openssl.exe"
            if (Test-Path -LiteralPath $gitOpenSSL) {
                & $gitOpenSSL ts -verify -data MANIFEST.sha256 -in provenance/MANIFEST.sha256.tsr -CAfile /usr/ssl/certs/ca-bundle.crt
            } elseif (Get-Command openssl -ErrorAction SilentlyContinue) {
                & openssl ts -verify -data MANIFEST.sha256 -in provenance/MANIFEST.sha256.tsr
            } else {
                Write-Host "NOTE: openssl not found on PATH; skipping RFC 3161 cryptographic verification."
            }
        } finally {
            Pop-Location
        }
    }
}

switch ($Task) {
    "lean"        { Invoke-Lean }
    "experiments" { Invoke-Experiments }
    "tests"       { Invoke-Tests }
    "figures"     { Invoke-Figures }
    "paper"       { Invoke-Paper }
    "audit"       { Invoke-Audit }
    "all"         {
        Invoke-Lean
        Invoke-Tests
        Invoke-Audit
        Invoke-Figures
        Invoke-Paper
    }
}

Write-Host "`nALL REQUESTED TASKS COMPLETED SUCCESSFULLY ($Task)." -ForegroundColor Green
