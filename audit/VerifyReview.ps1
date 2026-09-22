$ErrorActionPreference = 'Stop'
$reviewDirectory = $PSScriptRoot
$reviewProjectRoot = Split-Path -Parent $reviewDirectory
$reviewCompiler = 'C:/Users/lzysh/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lean.exe'
$reviewDependencies = 'C:/Users/lzysh/Documents/Codex/lean32/packages'
$reviewOutput = Join-Path $reviewDirectory 'reviewer-build'
New-Item -ItemType Directory -Force -Path $reviewOutput | Out-Null

$reviewLibraryPaths = @($reviewOutput, $reviewProjectRoot)
foreach ($reviewPackage in Get-ChildItem -LiteralPath $reviewDependencies -Directory) {
    $reviewLibrary = Join-Path $reviewPackage.FullName '.lake/build/lib/lean'
    if (Test-Path -LiteralPath $reviewLibrary) { $reviewLibraryPaths += $reviewLibrary }
}
$env:LEAN_PATH = $reviewLibraryPaths -join [IO.Path]::PathSeparator

$reviewModules = @(
    'MoireSection2', 'MoireSection3', 'MoireLatticeWords', 'MoireEisenstein',
    'MoireGeometry', 'MoireCounting', 'MoireEndpoint', 'MoireFibre', 'MoireConcrete'
)
$reviewBuildLog = Join-Path $reviewDirectory 'reviewer-build.txt'
$reviewAxiomLog = Join-Path $reviewDirectory 'reviewer-axioms.txt'
Set-Content -LiteralPath $reviewBuildLog -Value ('Independent review build: ' + (Get-Date -Format o))

Push-Location $reviewProjectRoot
try {
    foreach ($reviewModule in $reviewModules) {
        $reviewCompilerOutput = & $reviewCompiler -o (Join-Path $reviewOutput ($reviewModule + '.olean')) ($reviewModule + '.lean') 2>&1
        $reviewExitCode = $LASTEXITCODE
        $reviewCompilerOutput | Add-Content -LiteralPath $reviewBuildLog
        if ($reviewExitCode -ne 0) {
            $reviewCompilerOutput | Write-Output
            throw ('Independent compiler rejected ' + $reviewModule)
        }
        $reviewMessage = 'CHECKED ' + $reviewModule
        Add-Content -LiteralPath $reviewBuildLog -Value $reviewMessage
        Write-Output $reviewMessage
    }
    $reviewAxiomOutput = & $reviewCompiler -o (Join-Path $reviewOutput 'ReviewAxioms.olean') 'audit/ReviewAxioms.lean' 2>&1
    $reviewAxiomExitCode = $LASTEXITCODE
    $reviewAxiomOutput | Set-Content -LiteralPath $reviewAxiomLog
    $reviewAxiomOutput | Write-Output
    if ($reviewAxiomExitCode -ne 0) { throw 'Independent axiom audit failed' }
    Add-Content -LiteralPath $reviewBuildLog -Value 'CHECKED ReviewAxioms'
    Write-Output 'CHECKED ReviewAxioms'
} finally {
    Pop-Location
}
