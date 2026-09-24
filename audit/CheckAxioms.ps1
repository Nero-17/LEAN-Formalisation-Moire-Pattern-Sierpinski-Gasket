param([string]$Log = (Join-Path $PSScriptRoot 'section3-literature-axioms-2026-09-24.txt'))
$ErrorActionPreference = 'Stop'
$contents = Get-Content -LiteralPath $Log -Raw
if ($contents -match 'sorryAx|(?m)^.*error:|Lean rejected') { throw 'Failed Lean axiom audit.' }
$standard = @('propext', 'Classical.choice', 'Quot.sound')
$literature = @('MoireLiterature.planar_ambient_bound', 'MoireLiterature.line_ambient_bound',
    'MoireLiterature.line_convolution_bound', 'MoireLiterature.corso_shmerkin_line',
    'MoireLiterature.corso_shmerkin_plane')
$expected = @{
    'MoireLiterature.inputs' = $literature
    'MoireSection3Complete.projected_difference_full' = $literature
    'MoireSection3Complete.difference_full' = $literature
    'MoireSection3Complete.ae_full_lq_dimension' = $literature
    'MoireSection3Complete.ae_upper_box_dimension' = $literature
}
$seen = @{}
$declarations = [regex]::Matches($contents, "'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
foreach ($declaration in $declarations) {
    $name = $declaration.Groups[1].Value
    $custom = @($declaration.Groups[2].Value -split ',' |
        ForEach-Object { $_.Trim() } | Where-Object { $_ -and $_ -notin $standard })
    $allowed = if ($expected.ContainsKey($name)) { @($expected[$name]) } else { @() }
    if (@($custom | Where-Object { $_ -notin $allowed }).Count -or
        @($allowed | Where-Object { $_ -notin $custom }).Count) {
        throw "Unexpected dependency set for ${name}: $($custom -join ', ')"
    }
    $seen[$name] = $true
}
foreach ($name in $expected.Keys) {
    if (-not $seen.ContainsKey($name)) { throw "Missing audited entry point: $name" }
}
if (-not $seen.ContainsKey('MoireSection2Complete.resonant_dimensions')) {
    throw 'Missing Section 2 regression audit.'
}
if ($contents -notmatch 'CHECKED audit/ReviewAxioms') { throw 'Incomplete compiler audit log.' }
Write-Output "PASS: $($declarations.Count) declarations; exactly five cited axioms at the final Section 3 entry point; Section 2 remains standard-only."
