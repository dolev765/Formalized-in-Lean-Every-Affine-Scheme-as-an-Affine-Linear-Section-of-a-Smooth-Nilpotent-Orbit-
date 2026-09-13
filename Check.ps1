param(
  [string]$File = '',
  [switch]$Build,
  [string]$DependencyCache = $env:UNIVERSALITY_PACKAGE_CACHE,
  [string]$OutputRoot = '',
  [ValidateRange(1, 64)][int]$Jobs = 2,
  [ValidateRange(512, 65536)][int]$MemoryMB = 4096
)
$ErrorActionPreference = 'Stop'
$workspacePath = $PSScriptRoot
if (-not $DependencyCache) {
  $DependencyCache = Join-Path $workspacePath '.lake/packages'
}
if (-not (Test-Path -LiteralPath $DependencyCache -PathType Container)) {
  throw 'Dependency cache not found. Run lake exe cache get, or pass -DependencyCache <existing .lake/packages>.'
}
if (-not $OutputRoot) {
  $OutputRoot = Join-Path ([IO.Path]::GetTempPath()) 'lean-ssrn-7199240'
}
$toolchain = (Get-Content -LiteralPath (Join-Path $workspacePath 'lean-toolchain') -Raw).Trim()
$libraryPaths = @(Get-ChildItem -LiteralPath $DependencyCache -Directory |
  ForEach-Object { Join-Path $_.FullName '.lake/build/lib/lean' } |
  Where-Object { Test-Path -LiteralPath $_ -PathType Container })
if (-not $libraryPaths.Count) {
  throw 'No compiled dependencies found. Run lake exe cache get first.'
}
$previousLeanPath = $env:LEAN_PATH
$env:LEAN_PATH = ((@($OutputRoot) + $libraryPaths + @($workspacePath)) -join [IO.Path]::PathSeparator)
$sources = if ($File) { @($File) } else {
  @('Universality/MatrixOrbit.lean', 'Universality/Circuit.lean',
    'Universality/Scheme.lean', 'Universality/Symplectic.lean',
    'Universality/Construction.lean', 'Universality/Main.lean',
    'Universality/Statements.lean', 'Universality.lean', 'Universality/Audit.lean')
}
try {
  foreach ($source in $sources) {
    $sourcePath = Join-Path $workspacePath $source
    if (-not (Test-Path -LiteralPath $sourcePath -PathType Leaf)) {
      throw "Lean source not found: $source"
    }
    $checkArgs = @("+$toolchain", "-j$Jobs", "-M$MemoryMB", "--root=$workspacePath")
    if ($Build -or -not $File) {
      # This optional helper can reuse compiled dependencies without changing Lake's git pins.
      $outputFile = [IO.Path]::ChangeExtension((Join-Path $OutputRoot $source), '.olean')
      New-Item -ItemType Directory -Path ([IO.Path]::GetDirectoryName($outputFile)) -Force | Out-Null
      $checkArgs += @('-o', $outputFile)
    }
    $checkArgs += $sourcePath
    & lean @checkArgs
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
  }
} finally {
  $env:LEAN_PATH = $previousLeanPath
}
exit 0
