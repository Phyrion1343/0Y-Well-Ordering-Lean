param(
  [ValidateRange(1, 32)] [int]$Threads = 1,
  [switch]$AuditOnly
)

$ErrorActionPreference = 'Stop'
$taskLake = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../.tools/lean-4.33.1-windows/bin/lake.exe'))
if (-not (Test-Path -LiteralPath $taskLake -PathType Leaf)) { throw "Missing Lean runtime: $taskLake" }
$taskVersion = & $taskLake --version
if ($LASTEXITCODE -ne 0 -or $taskVersion -notmatch 'Lean version 4\.33\.1\)') {
  throw "Unexpected toolchain: $taskVersion"
}
$taskPreviousThreads = $env:LEAN_NUM_THREADS
Push-Location -LiteralPath $PSScriptRoot
try {
  $env:LEAN_NUM_THREADS = [string]$Threads
  if (-not $AuditOnly) {
    # The pinned upstream bridge emits existing linter warnings; kernel errors still fail.
    & $taskLake --keep-toolchain --no-cache build NoLiftConcrete 2>&1 |
      Tee-Object -FilePath '.lake/nolift-build.log'
    if ($LASTEXITCODE -ne 0) { throw 'NoLiftConcrete build failed.' }
  }
  & $taskLake env lean NoLiftAudit.lean 2>&1 | Tee-Object -FilePath 'nolift-audit-output.txt'
  if ($LASTEXITCODE -ne 0) { throw 'No-lift axiom audit failed to run.' }
  $taskExpected = @(Get-Content -LiteralPath 'NoLiftAudit.lean' | ForEach-Object {
    if ($_ -match '^#print axioms (\S+)\s*$') { $Matches[1] }
  })
  $taskAuditText = Get-Content -LiteralPath 'nolift-audit-output.txt' -Raw
  $taskAudits = [regex]::Matches($taskAuditText,
    "'(?<name>[^']+)' depends on axioms:\s*\[(?<axioms>[^\]]*)\]")
  if ($taskExpected.Count -ne 38 -or $taskAudits.Count -ne $taskExpected.Count) {
    throw 'No-lift audit declaration count mismatch.'
  }
  $taskSeen = @{}
  foreach ($taskAudit in $taskAudits) {
    $taskName = $taskAudit.Groups['name'].Value
    if ($taskName -notin $taskExpected -or $taskSeen.ContainsKey($taskName)) {
      throw "Unknown or duplicated audited declaration: $taskName"
    }
    $taskSeen[$taskName] = $true
    foreach ($taskAxiom in ($taskAudit.Groups['axioms'].Value -split ',')) {
      $taskAxiom = $taskAxiom.Trim()
      if ($taskAxiom -and $taskAxiom -notin @('propext', 'Classical.choice', 'Quot.sound')) {
        throw "Unexpected axiom for ${taskName}: $taskAxiom"
      }
    }
  }
  Write-Output 'All 38 no-lift axiom audits passed.'
}
finally {
  Pop-Location
  $env:LEAN_NUM_THREADS = $taskPreviousThreads
}
