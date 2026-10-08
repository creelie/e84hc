# verify.ps1 -- run the whole verification on Windows (PowerShell 5 or 7).
#
#   powershell -ExecutionPolicy Bypass -File .\verify.ps1                 # Python, then Lean
#   powershell -ExecutionPolicy Bypass -File .\verify.ps1 -Part python
#   powershell -ExecutionPolicy Bypass -File .\verify.ps1 -Part lean
#
# Python 3 with sympy, numpy and python-flint must be on the path as `python`
# or `python3`:
#
#   python -m pip install sympy numpy python-flint
#
# The Python suite (code\verify_all.py) takes about an hour and writes its
# output to verify_python.log.  The Lean step needs elan
# (https://github.com/leanprover/elan) with the toolchain named in
# lean\lean-toolchain; it elaborates lean\HodgeObstruction.lean once, which
# takes about one hundred minutes and about 7 GB of memory, and writes the
# axiom report to lean\axioms.txt.  If `lean` is not on the path the step is
# skipped and reported.

param([ValidateSet("all", "python", "lean")][string]$Part = "all")

$root = Split-Path -Parent $MyInvocation.MyCommand.Path
$env:PYTHONUTF8 = "1"
$env:PYTHONIOENCODING = "utf-8"

if ($Part -ne "lean") {
  $py = Get-Command python -ErrorAction SilentlyContinue
  if (-not $py) { $py = Get-Command python3 -ErrorAction SilentlyContinue }
  if (-not $py) { Write-Host "Python 3 was not found on the path."; exit 1 }

  Write-Host "== Python suite (code\verify_all.py) =="
  $log = Join-Path $root "verify_python.log"
  Push-Location (Join-Path $root "code")
  & $py.Source "verify_all.py" 2>&1 | ForEach-Object { "$_" } | Tee-Object -FilePath $log
  $pyStatus = $LASTEXITCODE
  Pop-Location
  if ($pyStatus -ne 0) { Write-Host "verify_all.py reported a failure (exit $pyStatus); see $log."; exit $pyStatus }
  Write-Host ""
}

if ($Part -ne "python") {
  Write-Host "== Lean check (lean\HodgeObstruction.lean) =="
  $lean = Get-Command lean -ErrorAction SilentlyContinue
  if (-not $lean) {
    Write-Host "lean is not on the path; skipping.  Install elan and run:"
    Write-Host "    cd lean; lean HodgeObstruction.lean"
    exit 0
  }
  $leanDir = Join-Path $root "lean"
  $source = Join-Path $leanDir "HodgeObstruction.lean"
  $expected = @(Select-String -Path $source -Pattern "^#print axioms").Count
  Push-Location $leanDir
  $out = & $lean.Source "HodgeObstruction.lean" 2>&1 | ForEach-Object { "$_" }
  $leanStatus = $LASTEXITCODE
  $out | Out-File -Encoding ascii "axioms.txt"
  Pop-Location
  if ($leanStatus -ne 0) { Write-Host "lean exited with status $leanStatus; see lean\axioms.txt."; exit $leanStatus }

  $lines = @($out | Where-Object { $_ -match "axioms" }).Count
  $free  = @($out | Where-Object { $_ -match "does not depend on any axioms" }).Count
  $prop  = @($out | Where-Object { $_ -match "depends on axioms: \[propext\]\s*$" }).Count
  $sorry = @($out | Where-Object { $_ -match "sorryAx" }).Count
  Write-Host ("theorems: {0}  axiom-free: {1}  propext only: {2}  sorryAx: {3}" -f $lines, $free, $prop, $sorry)
  if ($lines -ne $expected -or ($free + $prop) -ne $expected -or $sorry -ne 0) {
    Write-Host "the Lean report does not match the $expected theorems of the file."; exit 1
  }
}
Write-Host "overall: PASS"
