param(
    [Parameter(Mandatory=$true)][string]$LeanExecutable,
    [Parameter(Mandatory=$true)][string]$DependencyRoot,
    [string[]]$Modules = @('MoireSection2', 'MoireSection3', 'MoireLatticeWords',
        'MoireEisenstein', 'MoireGeometry', 'MoireCounting', 'MoireEndpoint',
        'MoireFibre', 'MoireConcrete', 'MoireAngles', 'MoireDimension',
        'MoireFiniteType', 'MoireDeterminization', 'MoireSection2Results',
        'MoireDensity', 'MoireNonempty', 'MoireCharacterisation',
        'MoirePiThirdSpectrum', 'MoireTriangle', 'MoireTriangleBounds',
        'MoirePiThirdGeometry', 'MoirePiThirdTable', 'MoireGraphGeometry',
        'MoireSpectralWeights', 'MoirePathMeasure', 'MoireGraphCoding',
        'MoireGraphCovers', 'MoireSpectralGrowth', 'MoireHausdorffUpper', 'MoireActualUpper', 'MoirePathCylinders', 'MoirePathSupport', 'MoireLabelledMeasure', 'MoirePrefixGeometry', 'MoireWordPacking', 'MoireDeterministicPaths', 'MoireSmallBalls', 'MoireGeometricMeasure', 'MoireSpectralMass', 'MoireMassDistribution', 'MoireHausdorffLower', 'MoireHausdorffEquality', 'MoireBoxDimension', 'MoireBoxBounds', 'MoireBoxSimilarity', 'MoireBoxEquality', 'MoireSection2Complete', 'MoireDifferenceMeasure', 'MoireDifferenceLaw', 'MoireIntersectionCounting', 'MoireIntersectionUpper', 'MoireDyadicConcentration', 'MoireLqDimension', 'MoireUpperFromLq', 'MoireSeparationGeometry', 'MoireProjectionSeparation', 'MoireAngularSublevel', 'MoireDeterminantSublevel', 'MoireAlmostEveryProjection', 'MoireAlmostEverySeparation', 'MoireSeparationPeriodicity', 'MoireGasketDimension', 'MoireSection3GeometricResults')
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
        $moduleOutput = Join-Path $outputDirectory "$module.olean"
        New-Item -ItemType Directory -Force -Path (Split-Path -Parent $moduleOutput) | Out-Null
        & $LeanExecutable -o $moduleOutput "$module.lean"
        if ($LASTEXITCODE -ne 0) { throw "Lean rejected $module" }
        Write-Output "CHECKED $module"
    }
} finally { Pop-Location }
