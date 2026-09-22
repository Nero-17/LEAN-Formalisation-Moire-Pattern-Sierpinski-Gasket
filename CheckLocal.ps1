param(
    [Parameter(Mandatory=$true)][string]$LeanExecutable,
    [Parameter(Mandatory=$true)][string]$DependencyRoot,
    [string[]]$Modules = @('MoireSection2', 'MoireSection3', 'MoireLatticeWords',
        'MoireEisenstein', 'MoireGeometry', 'MoireCounting', 'MoireEndpoint',
        'MoireFibre', 'MoireConcrete')
)
$ErrorActionPreference = 'Stop'
$projectRoot = $PSScriptRoot
$outputDirectory = Join-Path $projectRoot '.lake/build/lib/lean'
New-Item -ItemType Directory -Force -Path $outputDirectory | Out-Null
$libraryPaths = @($outputDirectory, $projectRoot)
foreach ($package in Get-ChildItem -LiteralPath $DependencyRoot -Directory) {
    $library = Join-Path $package.FullName '.lake/build/lib/lean'
    if (Test-Path -LiteralPath $library) { $libraryPaths += $library }
}
$env:LEAN_PATH = $libraryPaths -join [IO.Path]::PathSeparator
Push-Location $projectRoot
try {
    foreach ($module in $Modules) {
        & $LeanExecutable -o (Join-Path $outputDirectory "$module.olean") "$module.lean"
        if ($LASTEXITCODE -ne 0) { throw "Lean rejected $module" }
        Write-Output "CHECKED $module"
    }
} finally { Pop-Location }
